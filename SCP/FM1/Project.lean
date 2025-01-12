import Mathlib

/- set_option autoImplicit false -/
/- set_option relaxedAutoImplicit false -/

/-!
# Formalising Mathematics Project 1

06020618

## Split conformal prediction

Let X = ℝⁿ be feature space
and Y = ℝ be response space.
Let X x Y have law P,
and (Xᵢ, Yᵢ) ∼ P for all i.
Let 0 < α < 1 be "nominal error level"
Define "prediction band" as

C : X → subsets of Y

such that for new i.i.d. pair (Xnew, Ynew) ∼ P
we have that P(Ynew ∈ C(Xnew)) ≥ 1 - α.
There exists a trivial example:
let C(Xnew) = Y with prob 1-α and ∅ otherwise.
We want a "better" C, and this is the want of CP.
-/

/-!
## Simpler setting
-/

/-!
### Intermediate result for induction functions
-/

open Finset Classical Nat

noncomputable section

variable
  (n : ℕ)
  (s : ℕ → ℝ)

/-- indicator I{Sn > Sk} -/
def ind (s : ℕ → ℝ) (n : ℕ) (k : ℕ) : ℝ :=
  if s n > s k then 1 else 0

example
  -- assume partial order without loss of generality
  (h_non_inc : ∀ x, s x ≥ s (x + 1))
  : ∑ k in range (n-1), ind s n k = ∑ k in range n, ind s n k := by
  -- induction example from Section 8 Sheet 1
  induction' n with d hd
  · rfl -- base case
  · rw [sum_range_succ] -- pop last element
    -- simp can "expand" defs, from Section 2 Sheet 5
    simp [ind] -- simplify by defn
    apply h_non_inc -- apply assumption
    -- didn't need hd, so induction is not a good fit

-- attempt 2 (Iio and Iic)

lemma ind_at_nn_is_0 : ∀ n, ind s n n = 0 := by
  simp [ind] -- needed to extract simplification into a lemma

example : ∑ k < n, ind s n k = ∑ k ≤ n, ind s n k := by
  rw [← sum_Iio_add_eq_sum_Iic] -- pop last element in the goal
  rw [self_eq_add_right] -- a=a+b iff b=0
  rw [ind_at_nn_is_0] -- simplify

-- attempt 3 (special notation)

/-- notation for indicator I{Sₙ > Sₖ} -/
notation l " ⟩ " r => (if l > r then 1 else 0)

lemma lt_sum_eq_le_sum : ∑ k < n, (s n ⟩ s k) = ∑ k ≤ n, (s n ⟩ s k) := by
  -- same as before, but cleaner
  rw [← sum_Iio_add_eq_sum_Iic]
  rw [self_eq_add_right]
  simp

-- additional assumptions
variable
  { i j x : ℕ }
  {h_distinct : s i ≠ s j} -- i and j are inferred from s args
  (h_non_inc : s x ≥ s (x + 1))


/-!
### Intermediate result about quantile inequality

⌈(n+1)(1-α)⌉ ≤ n+1
-/

lemma
  α_mul_n_lt_n
  {α : ℝ}
  (α_le_1 : α < 1)
  : Nat.ceil (α * n) ≤ n := by
  -- get rid of ceiling using `ceil y ≤ x → y ≤ x`
  rw [Nat.ceil_le]
  -- here we spawn three assumptions to prove end goal
  apply mul_le_of_le_one_of_le_of_nonneg -- thanks Bhavik Mehta

  -- 1. α ≤ 1
  -- via `exact?`
  · exact le_of_lt α_le_1

  -- 2. n ≤ n
  -- `exact?` fails at first because it expands to `↑n`
  -- but this can be fixed with a gap, thanks Bhavik Mehta
  · exact Preorder.le_refl _

  -- 3. n ≥ 0
  -- `aesop?` instead finds simp_all
  -- simp_all only [gt_iff_lt, le_refl]
  · exact Nat.cast_nonneg' n -- via `exact?`


/-!
## Measure-theoretic probability
-/

/-!
### Random variables
-/

open MeasureTheory ProbabilityTheory NNReal

variable
  {Ω : Type}
  [MeasureSpace Ω]
  {P : Measure Ω}
  [IsProbabilityMeasure P]

  -- family {Xᵢ : i ∈ ℝ} of i.i.d. real-valued random variables
  {i j : ℕ}
  {X : ℝ → Ω → ℝ}
  (h_meas : Measurable (X i))
  (h_ident : ∀ i j, IdentDistrib (X i) (X j))
  (h_indep : ∀ i ≠ j, IndepFun (X i) (X j))

#check pdf (X 0) P (P.map (X 10)) 0
#check uniformOn {1,2,3}
#check P[X 0.3211]
#check moment (X pi) 10
#check ∂P/∂P
#check X 0

example : ∀ x, pdf (X 0) P x ≥ 0 := by
  intro x
  -- found with `exact?`
  exact _root_.zero_le (pdf (X 0) P x)

/-!
### Exchangeability

We used i.i.d., but we need less.
Let Z = (Z_1, ..., Z_n) ∈ ℝⁿ
with joint density f.
Z is exchangeable iff
for a.e. z_1, ..., z_n ∈ Z
f(z_1, ..., z_n) = f(z_1', ..., z_n')
where ' is any permutation in Sₙ.
-/

variable
  -- default bind rule would say { fᵢ : ℝ → ℝ | i ≤ n }
  -- using parentheses to instead say f : ℝⁿ → ℝ (thanks Bhavik Mehta)
  {α : ℝ}
  {f : (Fin n → ℝ) → ℝ}

  -- finite permutation to define exchangeability, thanks Bhavik Mehta
  {σ : Equiv.Perm (Fin n)}
  ( f_symm : ∀ x, f (λ y ↦ x (σ y)) = f x )

  -- how does this work?
  -- `Fin n` is an index set for the vector
  -- `x` is the vector in ℝⁿ (maps each index to some real)
  -- `f x` is the final output in ℝ
  -- since `f` takes a mapping from indices to reals,
  -- we can give it a different function instead
  -- and we give it `λ y → x (σ y)` instead of `x`
  -- which is also a mapping, but from some index `y`
  -- to some permutation `σ y` of that index
  -- perhaps `x` and `y` were not good choice of names,
  -- because `x` is a vector and `y` is an index!

/-!
### Distributions

Example of push-forward measure
to define a normal distribution.
-/

variable
  -- X₀ ∼ N(μ, σ)
  {μ : ℝ}
  {σ : ℝ≥0}
  {h_normal : P.map (X 0) = gaussianReal 0 1}

example : P.map (X 0) = gaussianReal 0 1 := by
  exact h_normal

#min_imports -- doesn't find probability sources :(



#lint

