import Mathlib

/-!
# Formalising Mathematics Project 3

06020618

In this project, I picked up from my first project on conformal prediction.

## Done

- Definition of conformal quantile (`quantile`)
- Definition of sample realisation (`sample`)
- Statement and partial proof of the marginal coverage guarantee (`scp_fki`)
- Statement of exchangeability (`Exch`)
- Definition of beta distribution density (`betaPDFReal`)

## Attempted, but not finished

- Measurability of conformal quantile on sample realisation
- Exchangeability implies uniform rank
- Uniform rank implies conformal bound
-/

set_option trace.aesop true -- for debugging `measurability` tactic

/-!
## Probability space

Define a probability space (Ω, 𝓕, ℙ) that will model some experiment.
Some sigma-algebra 𝓕  is implied by MeasureSpace, but I don't use it directly.
-/

open MeasureTheory ProbabilityTheory NNReal
open scoped ENNReal

variable
  -- {Ω} from https://github.com/RemyDegenne/CLT/blob/7b3ea058749421805d88c4e95a796a52e2f37d67/Clt/CLT.lean#L46
  -- could lead to typeclass issues, so added Type*, thanks BM
  {Ω : Type*}
  [MeasureSpace Ω] -- ambient space of experiment outcomes, no structure assumed
  [IsProbabilityMeasure (ℙ : Measure Ω)] -- this was P, leaving ℙ to mean volume, thanks BM

-- if ℙ is not defined, it's notation for volume, and might mess with typeclass inference
example : Measure Ω := volume (α := Ω)
noncomputable example : Measure ℝ := volume (α := ℝ)

-- using ω without Ω breaks on classes, must specify Ω (this tripped me up elsewhere)
example : ℙ { ω : Ω | false } = 0 := by simp

/-
Helper lemma about complements. Surprisingly hard to prove due to ENNReal arithmetic.
I tried many lemmas in ENNReal, got a bit lost along the way, eventually found "sub_sub_cancel".
-/

-- first attempt, got lost here, calc and integrals are completely unnecessary
lemma one_sub_compl (A : Set Ω) (hA : MeasurableSet A) : ℙ A = 1 - ℙ Aᶜ := by
  rw [prob_compl_eq_one_sub]
  · calc
      ℙ A = 1 - 1 + ℙ A := by simp
      1 - 1 + ℙ A = 1 - (1 - ℙ A) := by
        refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).mp ?_
        · simp
        · simp
        · simp only [tsub_self, zero_add]
          rw [← integral_indicator_one hA]
          rw [ENNReal.sub_sub_cancel]
          · exact integral_indicator_one hA
          · simp
          · exact prob_le_one
  · exact hA

-- second attempt, distilled from `one_sub_compl`
lemma one_sub_compl' (A : Set Ω) (hA : MeasurableSet A) : ℙ A = 1 - ℙ Aᶜ := by
  rw [prob_compl_eq_one_sub]
  · refine Eq.symm (ENNReal.sub_sub_cancel ?_ ?_)
    · simp
    · exact prob_le_one
  · exact hA

lemma one_sub_prob_eq_compl (A : Set Ω) (hA : MeasurableSet A) : 1 - ℙ A = ℙ Aᶜ := by
  rw [prob_compl_eq_one_sub]
  · exact hA

/-!
## Random variables

Define a family of IID random variables.
In practice, ω ∈ Ω is not actually observable,
only the result of this function at ω is observed.
-/

variable
  {X : ℕ → Ω → ℝ}
  (hX : ∀ i, Measurable (X i))

  -- identically distributed
  (hXident : ∀ i, IdentDistrib (X i) (X 0))

  -- independent
  (hXindep : iIndepFun inferInstance X)

#check ℙ (X 0 ⁻¹' Set.Iic (10 : ℝ))
#check ℙ {ω : Ω | X 0 ω > 0}

/-!
## Sample realisation

Define a sample at some ω (which can be thought of as "outcome of an experiment"
or "unbiased sample run of a reproducible algorithm that generates some data").
Previously, all of this was in terms of Finset ℝ, thanks BM for suggestion to use List ℝ instead.
-/

/-- Sample of first `n` random variables at some `ω ∈ Ω` -/
def sample (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : List ℝ :=
  (List.range n).map (fun i => X i ω)

/-
Prove that `n` and `n+1` samples are non-empty, since `n` is positive.
TODO: just prove `X` is size `n` or `n+1`, this is slightly ridiculous, I'm sorry.
-/

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
-- NB: sorry for the linter exception, it proposes "omit" but that makes instance problem stuck
-- it may be related to https://github.com/leanprover/lean4/issues/5595
lemma sample_nonempty (n : ℕ) (hn : n > 0) (ω : Ω) : (sample X n ω).length > 0 := by
    simp only [sample, List.length_map, List.length_range, gt_iff_lt]
    exact hn

lemma sample_nonempty_one (n : ℕ) (hn : n > 0) (ω : Ω) : (sample X (n + 1) ω).length > 0 := by
    apply sample_nonempty
    exact Nat.add_pos_left hn 1

/-!
## Conformal quantile

Define the conformal quantile, used to construct prediction sets in SCP,
as list of reals representing some realisation of a finite list of random variables.
Initially, I tried to define it directly for finsets of random variables,
but this has proven complicated, and I found the "deterministic" version much nicer.
-/

open Finset

/-- Conformal quantile -/
noncomputable
def quantile (X : List ℝ) (hX : X.length > 0) (α : ℝ) (hα : α < 1 ∧ 0 < α) : ℝ :=
  let n := X.length;
  let ranks := X.mergeSort (· ≤ ·);
  let k := ⌈(n + 1) * (1 - α)⌉.toNat;
  (ranks.take k).reverse.head (by
    simp only [ne_eq, List.reverse_eq_nil_iff, List.take_eq_nil_iff, not_or]
    constructor
    · simp only [k, Int.toNat_eq_zero, not_le, Int.ceil_pos]
      apply mul_pos
      · exact Nat.cast_add_one_pos n
      · norm_num
        exact hα.1
    · simp only [ranks, sort_range, List.range_eq_nil]
      refine List.ne_nil_of_length_pos ?_
      simp only [List.length_mergeSort]
      exact hX
    )

noncomputable example (X : List ℝ) := X.mergeSort

#check List.sorted_mergeSort
#check List.mergeSort_perm
#check List.map_mergeSort
#eval 1 :: 1 :: [1,2] ++ [3,4]
#check [].mergeSort_cons

example (xs ys : List ℝ) : xs.mergeSort (· > ·) = ys ↔ ys.mergeSort (· > ·) = xs := by
  have : (?x :: xs).mergeSort (· > ·) = [] := by
    sorry
  use 1
  sorry

#check List.measurable_prod

-- curious find: replacing mergeSort with a faster version at runtime using @[csimp]
-- https://github.com/leanprover/lean4/blob/149b6423f8a3f3cf840bd65b92a89ed4e18ac888/src/Init/Data/List/Sort/Impl.lean

/-!
## Measurability

I extracted a few measurability lemmas along the way, but unfortunately I did not get very far.
Definitions added new abstract things to learn, so it was a bit of a minefield at times.
-/

-- started by gathering some potentially useful results in documentation, loogle and leansearch
#check measurable_iUnionLift -- for constructions?
#check measurable_sum -- maybe I can covert something to sums
#check Measurable.ite -- quantile as conditionals?
#check measurable_find -- instead of mergeSort?
#check measurable_set_iff -- convert back to sets
#check measurable_coe_nnreal_ennreal_iff -- finishing

set_option maxHeartbeats 9999 in -- increase memory quota or else `apply?` does not finish
include hX in
@[measurability] -- to use in `measurability` in other lemmas
lemma sample_measurable
  [MeasurableSpace (List ℝ)] -- NB: fixes some sigma algebra on lists of reals
  (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  Measurable fun (ω : Ω) => sample X n ω := by
  simp only [sample]
  apply Measurable.eval
  apply Measurable.comp
  · exact Measurable.of_comap_le fun s a ↦ a
  · -- the goal here seems easy: Measurable fun x i => X i x
    #check measurable_pi_iff
    #check measurable_pi_apply
    -- these don't unify as is, but promising, thanks metahumor on discord
    -- NB: it would be very nice to make search tactics prioritise `#check`s nearby
    -- as a way to nudge the search towards something useful
    sorry

include hX in
@[measurability]
lemma quantile_measurable
  [MeasurableSpace (Set ℝ)] -- NB: fixes some sigma algebra on reals
  (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  Measurable fun ω => quantile (sample X n ω) (by exact sample_nonempty n hn ω) α hα := by
    unfold quantile
    simp only [List.head_reverse, List.head]
    intro t ht
    rw [← MeasurableSpace.map_def]
    sorry
    /- apply measurable_generateFrom -/
    /- #check OpensMeasurableSpace -/
    /- simp only [quantile, sample] -/
    /- simp only [List.length_map, List.length_range, List.head_reverse] -/
    /- unfold List.mergeSort -/
    /- simp only [List.length_cons, List.splitInTwo_fst, List.splitInTwo_snd] -/

set_option maxHeartbeats 9999 in
@[measurability]
lemma sample_quantile_measurable (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  Measurable fun ω : Ω => quantile (sample X n ω) (by exact sample_nonempty n hn ω) α hα := by
    #check measurable_const
    apply measurable_generateFrom
    simp only [Set.mem_setOf_eq]
    intro t ht
    rw [← measurable_mem]
    simp only [Set.mem_preimage]
    sorry -- need to combine `quantile_measurable` and `sample_measurable`

@[measurability]
lemma sample_quantile_one_measurable (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  Measurable fun ω : Ω => quantile (sample X (n+1) ω)
    (by exact sample_nonempty_one n hn ω) α hα := by
    refine sample_quantile_measurable α hα (n + 1) ?_
    simp

-- idea: monotonicity
-- this required more structure on Ω, but I did not want to assume anything,
-- as it was was supposed to be some unknown ambient space modelling an experiment
#check Monotone.measurable

variable
  {Ω' : Type*} [MeasurableSpace Ω'] [TopologicalSpace Ω']
  [BorelSpace Ω'] [LinearOrder Ω'] [OrderClosedTopology Ω']

-- idea: something with Chernoff bound
#check measure_ge_le_exp_mul_mgf

/-
More helper lemmas for SCP proof(s), unfortunately did not finish proving those.
-/

set_option linter.unusedSectionVars false in -- sorry, not sure how to unassume ℙ
-- being strictly larger than itself is impossible
lemma prob_x_gt_x_zero (n : ℕ) : ℙ {ω : Ω | X (n + 1) ω > X (n + 1) ω} = 0 := by simp

-- TODO: remove `1 - ·` part, it's not relevant
lemma sample_ext (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  1 - ℙ {ω | X (n + 1) ω > quantile (sample X n ω) (by exact sample_nonempty n hn ω) α hα} =
  1 - ℙ {ω | X (n + 1) ω > quantile (sample X (n+1) ω)
    (by exact sample_nonempty_one n hn ω) α hα} := by
  sorry -- this should be just `prob_x_gt_x_zero`, but I don't know how to split it out

-- first attempt, felt "almost done" until I tried it
include hX in
lemma complement_trick (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  1 - ℙ {ω | X (n + 1) ω > quantile (sample X (n + 1) ω)
        (by exact sample_nonempty_one n hn ω) α hα} =
      ℙ {ω | X (n + 1) ω ≤ quantile (sample X (n + 1) ω)
        (by exact sample_nonempty_one n hn ω) α hα} := by
    rw [one_sub_compl]
    · sorry -- dead end
    · apply MeasurableSet.of_compl
      rw [Set.compl_setOf]
      simp only [not_lt]
      apply measurableSet_le
      · simp only [hX]
      · refine sample_quantile_measurable α hα (n + 1) (by simp)

-- second attempt
include hX in
lemma complement_trick' (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  1 - ℙ {ω : Ω | X (n + 1) ω > quantile (sample X (n + 1) ω)
    (by exact sample_nonempty_one n hn ω) α hα} =
  ℙ {ω : Ω | X (n + 1) ω ≤ quantile (sample X (n + 1) ω)
      (by exact sample_nonempty_one n hn ω) α hα} := by
    rw [one_sub_prob_eq_compl]
    · rw [Set.compl_setOf]
      simp
    · simp only [measurableSet_setOf]
      -- should be exact sample_quantile_one_measurable
      -- typeclasses stuck on ℙ, added all Ω I could think of, ran out of time
      sorry

/-
In the first project, I proved a very simple lemma about ceiling of some numbers.
I rework it here into a more useful format to compute conformal bound.
-/

lemma ceil_one_α_mul_n_one_le_n_one (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) :
  ⌈(1-α)*(n+1)⌉ ≤ n+1 := by
    obtain ⟨α_lt_1, α_gt_0⟩ := hα
    rw [Int.ceil_le]
    apply mul_le_of_le_one_of_le_of_nonneg
    · exact le_of_lt (by exact sub_lt_self 1 α_gt_0)
    · simp
    · norm_cast
      simp

lemma conformal_bound (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  ℙ {ω | X (n + 1) ω ≤ quantile (sample X (n + 1) ω) (by exact sample_nonempty_one n hn ω) α hα}
  ≥ ENNReal.ofReal (1 - α) := by
    sorry

/-!
## Marginal coverage guarantee

Also known as "first key idea of conformal prediction" in the main reference.

1. Take the complement to work with strict inequality
2. Extend to statement from `n` to `n+1` because P(X > X) = 0
3. Take the complement again
4. Compute bound, arguing by uniform rank, which comes from exchangeability
-/

-- TODO: use dummy values instead of bookkeeping hypotheses
include hX in
theorem scp_fki (α : ℝ) (hα : α < 1 ∧ 0 < α) (n : ℕ) (hn : n > 0) :
  ℙ {ω : Ω | X (n + 1) ω ≤ quantile (sample X n ω) (sample_nonempty n hn ω) α hα}
  ≥ ENNReal.ofReal (1 - α) := by
    calc
      -- take complement to have a strict inequality
      _ = 1 - ℙ {ω | X (n + 1) ω > quantile (sample X n ω)
        (sample_nonempty n hn ω) α hα} := by
        simp only [not_le, gt_iff_lt]
        rw [one_sub_compl]
        rw [Set.compl_setOf]
        simp only [not_le]
        · apply measurableSet_le
          · simp only [hX]
          · exact sample_quantile_measurable α hα n hn

      -- extend to a statement about X (n+1)
      _ = 1 - ℙ {ω | X (n + 1) ω > quantile (sample X (n + 1) ω)
        (sample_nonempty_one n hn ω) α hα} := by
        exact sample_ext α hα n hn

      -- take complement again back to original form
      _ = ℙ {ω | X (n + 1) ω ≤ quantile (sample X (n + 1) ω)
        (sample_nonempty_one n hn ω) α hα} := by
        exact complement_trick' hX α hα n hn

      -- compute the bound by uniform rank of the sample
      _ ≥ ENNReal.ofReal (1 - α) := by exact conformal_bound α hα n hn

/-!
## Exchangeability

Independence is not actually needed for conformal prediction,
it works with a weaker condition of exchangeability (symmetry of joint pdf).
I would prefer this, though IID is a standard assumption in statistics.
-/

-- how do I construct permutations on lists? identity would be one of course
example : Equiv.Perm (List ℝ) := by
  use id
  · exact fun a ↦ a
  · exact congrFun rfl
  · exact congrFun rfl

/-- Permute list given a permutation -/
def permute_list (z : List ℝ) (σ : Equiv.Perm (List ℝ)) := σ z
#check permute_list [1, 2, 3] _ -- how can I construct this permutation? this might be wrong

-- perfect, List.Perm was exactly what I need
#check List.Perm [0, 1, 2]
#eval [0, 1, 2].Perm [1, 2, 0]

variable
  (sample' : List ℝ)
  (pdf' : List ℝ → ℝ)
  -- first attempt, permutations on the set of all possible lists, thanks BM
  (exch' : ∀ σ : Equiv.Perm (List ℝ), pdf' sample' = pdf' (σ sample'))
  -- second attempt at permutations, fixed one List, but same issue as before
  (exch'' : ∀ X : List ℝ, ∀ σ : Equiv.Perm (List ℝ), pdf' (σ X) = pdf' X)

/-- Exchangeability structure -/
class Exch where
  /-- Observed sample -/
  sample : List ℝ

  /-- Joint density -/
  pdf : List ℝ → ℝ

  /-- Symmetry of density -/
  -- third attempt, fixing both lists and using List.Perm
  symm : ∀ X : List ℝ, ∀ Y : List ℝ, X.Perm Y → pdf X = pdf Y

/-- Independence implies exchangeability -/
-- TODO: need to tie it to X via `sample`
def Exch.ofIndep (sample : List ℝ) : Exch where
  sample := sample
  pdf := sorry
  symm := sorry

#check pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf -- this should be useful

/-!
## Cumulative distribution function

Quantile is a kind of inverse of CDF, but it's not actually invertible in general.
That said, since SCP can be expressed in terms of empirical CDF, I spent some time exploring.
Before switching to quantile as a function of realised sample, I tried to use this instead.
-/

noncomputable example : ℝ := cdf ℙ 0.5

variable (Y : Ω → ℝ) (hY : Measurable Y)

/-- Alternative CDF -/
def cdf' (x : ℝ) : ℝ := ( ℙ { ω : Ω | Y ω ≤ x } ).toReal
example := cdf' Y 42

/-
An attempt at the "second key idea" in the reference.
Extends marginal coverage property to conformity scores,
which is how conformal prediction is used in practice.
-/

-- define "dataset" as (Z₁, ..., Zₙ) where Zᵢ = Xᵢ × Yᵢ ≃ (ℝ × ℝ) × ℝ
-- for some known vector Xᵢ (input) and unknown value Yᵢ (output).
variable
  (Z : Ω → (ℝ × ℝ) × ℝ)
  (hZm : Measurable Z)

/-- Unit interval -/
def unitInterval' : Set ℝ := Set.Icc 0 1
example : unitInterval = unitInterval' := by rfl

-- interestingly, `×` and `×ˢ` are not associative, (ℝ × ℝ) × ℝ is not the same type as ℝ × ℝ × ℝ
-- product measure idea from https://github.com/leanprover-community/mathlib4/blob/16a1c5cebbf76fcbea57a380669e60224207be98/Archive/Wiedijk100Theorems/BuffonsNeedle.lean#L91
/-- Product space for data and response -/
def space := (unitInterval ×ˢ unitInterval) ×ˢ unitInterval

variable (hZd : pdf.IsUniform Z space ℙ)

/-!
## Beta distribution

It comes up when there are no ties in realised sample.
It's not in Mathlib, so I started adding it here, following the Gaussian example.
-/

-- NB: ℙ.map doesn't work like P.map, but Measure.map does
example := Measure.map (X 0) ℙ = gaussianReal 0 1

open Real

example : Gamma 4 = 6 := by
  simp only [Gamma_ofNat_eq_factorial]
  unfold Nat.factorial
  simp

/-- Beta function -/
noncomputable
def Beta (α : ℝ) (β : ℝ) : ℝ := Gamma α * Gamma β

example : Beta 0 0 = 0 := by
  unfold Beta
  simp

/-- Beta density -/
noncomputable
def betaPDFReal (α : ℝ) (β : ℝ) (x : ℝ) : ℝ :=
  (x^(α-1) * (1-x)^(β-1)) / Beta α β -- https://en.wikipedia.org/wiki/Beta_distribution

-- the only linter failures left are due to some typeclass instances treated as unused variables
-- see https://github.com/leanprover/lean4/issues/2830 and https://github.com/leanprover/lean4/issues/2920
/- #lint -/

