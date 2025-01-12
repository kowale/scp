import Mathlib

/-!
# Formalising Mathematics Project 2

06020618
-/

/-!
## Matrix operations

In applications (see e.g. Hartley-Zisserman book)
multi-view geometry is mostly implemented in homogeneous coordinates
using real-valued matrices of concrete shapes (3x4, 4x1, 3x1).
I would like to work with these expressions symbolically,
so I implement a few custom matrix operations in this section.
In hindsight, I probably should have used the existing Matrix API.
-/

section MatrixOperations

/-- 2-dimensional homogeneous coordinates -/
structure P3 where
  /-- Entries of P3 -/
  (x y z : ℝ)

/-- 3-dimensional homogeneous coordinates -/
structure P4 where
  /-- Entries of P4 -/
  (x y z w : ℝ)

/-- Camera projection matrix (row-major) -/
structure P34 where
  /-- Entries of P34 -/
  (p11 p12 p13 p14
   p21 p22 p23 p24
   p31 p32 p33 p34 : ℝ)

-- NB: redundant "entries" above because #lint wants docstrings on all constructors

/-- Matrix-vector multiplication -/
def matmulvec (m : P34) (v : P4) : P3 :=
  P3.mk
    (m.p11 * v.x + m.p12 * v.y + m.p13 * v.z + m.p14 * v.w)
    (m.p21 * v.x + m.p22 * v.y + m.p23 * v.z + m.p24 * v.w)
    (m.p31 * v.x + m.p32 * v.y + m.p33 * v.z + m.p34 * v.w)

/-- 2D origin -/
def P3.o := mk
  0 0 1

/-- 3D origin -/
def P4.o := mk
  0 0 0 1

/-- 3x4 identity -/
def P34.id := mk
  1 0 0 0
  0 1 0 0
  0 0 1 0

example : (matmulvec P34.id (P4.mk 4 5 0 1)).x = 4 := by
  simp only [matmulvec, P34.id]
  norm_num

/-- Normalise 2D point in homogeneous coordinates (id if at ∞) -/
noncomputable
def P3.normalise (v : P3) : P3 :=
  if v.z = 0 then v
  else P3.mk (v.x/v.z) (v.y/v.z) 1

/-- Normalise 3D point in homogeneous coordinates (id at ∞) -/
noncomputable
def P4.normalise (v : P4) : P4 :=
  if v.w = 0 then v
  else P4.mk (v.x/v.w) (v.y/v.w) (v.z/v.w) 1

end MatrixOperations

/-!
## Homogeneous coordinates

If V is finite dimensional, if it is e.g. ℝ⁴, element of projectivization
ℙ K V can be expressed in homogenous coordinates [x₀:x₁:x₂:x₃]
which obey by the same equivalence relation, and are usually normalised so x₃ = 1.

Vectors in ℝⁿ in Mathlib are often expected to be functions from fintype indices,
so I also try to prove equivalence with my custom matrix API.
-/

section HomCoord

/-- ℝ⁴ as a function -/
abbrev F4 := Fin 4 → ℝ

/-- ℝ³ as a function -/
abbrev F3 := Fin 3 → ℝ

-- NB: `def` doesn't work with ℙ, but `abbrev` does

-- ![] notation can be used to get a term of function from indices
example : (Fin 3 → ℝ) := ![0, 0, 0]

/-- Equivalence between vectors and finite functions -/
def vecFinEquiv : (P4 ≃ F4) where
  toFun p := ![p.x, p.y, p.z, p.w]
  invFun f := P4.mk (f 0) (f 1) (f 2) (f 3)
  left_inv p := by simp
  right_inv p := by
    exact List.ofFn_inj.mp rfl

/-- Homogeneous vectors on R4 -/
structure H4 where
  /-- ℝ⁴ vector as a function -/
  (v : F4)

  /-- Scalar multiplication doesn't matter -/
  (hv : ∀ a : ℝ, a ≠ 0 → a • v = v) -- `=` makes this nonsense

/-- Equivalence between homogeneous vectors and finite functions -/
noncomputable
def homFinEquiv : (H4 ≃ F4) where
  toFun h := h.v
  invFun v := H4.mk v (by sorry) -- also nonsense
  left_inv v := by simp
  right_inv h := by simp

end HomCoord

/-!
## Projective spaces

Let V be vector space over field K e.g. ℝ⁴ written as Fin 4 → ℝ.
Let ∼ be equivalence relation on V defined as λ • x ∼ y, ∀ λ ∈ K, λ ≠ 0.
Then projectivization ℙ K V is the quotient set of ∼ such that
for all p ∈ ℙ K V then p = {x ∈ V | x ∼ p}.
Equivalently, ℙ K V is the set of lines in V through the origin
or the set of 1-dimensional subspaces of V.

<https://github.com/leanprover-community/mathlib4/blob/6be2b2250d96f10b6fc57511db99f74adefb6b40/Mathlib/LinearAlgebra/Projectivization/Basic.lean>
-/

section ProjectiveSpaces

open Function LinearAlgebra Projectivization

/-- Lift a linear map from vector spaces to projective spaces -/
def lift (f : F4 →ₗ[ℝ] F3) : ℙ ℝ F4 → ℙ ℝ F3 := by
  intro p
  refine Projectivization.lift (fun u : {v : F4 // v ≠ 0} => sorry) ?_ p
  simp

/-- Equivalence between projectivization and finite functions -/
noncomputable
def projFinEquiv : (ℙ ℝ F4 ≃ {f : F4 // f ≠ 0}) where
  toFun p := by
    use p.rep
    exact rep_nonzero p -- from `exact?`
  invFun v :=  by
    apply Projectivization.mk -- not sure what is `?v` here
    · exact ne_zero_of_eq_one rfl -- from `exact?`
  left_inv p := by sorry
  right_inv p := by sorry

/-- Equivalence between vectors and projectivization -/
noncomputable
def vecProjEquiv : (ℙ ℝ F4 ≃ P4) := by
  sorry -- TODO: compose from vecFinEquiv and projFinEquiv

#check mk_eq_mk_iff -- proj iff invariant to scalar multiplication
#check equivSubmodule -- equivalence to 1-dim subspaces (lines)

end ProjectiveSpaces

/-!
### Setoid sidenote

In this sidenote, I explore how quotients are used for this.
-/

section SetoidSidenote

-- borrowed from https://github.com/leanprover-community/mathlib4/blob/abeb840f4a76fa4764d076825b201238d83a20f7/Mathlib/AlgebraicGeometry/EllipticCurve/Projective.lean#L152
instance setoidF4 : Setoid F4 := MulAction.orbitRel ℝˣ F4

-- `≈` notation requires setoid instance on F4 defined above
variable (v : F4) (hv : ∀ a : ℝ, v ≈ a • v)

/-- Equivalence class type for scalar multiplication quotient -/
def classF4 := MulAction.orbitRel.Quotient ℝˣ F4

-- NB: quotient can be made like this, but ≈ works without it

#check MulAction.orbitRel.Quotient ℝˣ F4

end SetoidSidenote

/-!
## Pinhole camera

Full-rank 3x4 matrix can model a pinhole camera
in the sense that it implements a surjective mapping from ℙ³ to ℙ².
For a single camera, such mapping is not injective,
that is, many points in world ℙ³ can map to the same point in image plane ℙ².
For ≥2 cameras, rays intersect so it becomes injective.

Note that no "clipping" is performed so there is no notion
of width/height of the image plane or camera front/behind.
The cameras defined only with an arbitrary full-rank 3x4 matrix
"see" all of the space in all directions, which isn't realistic.

In practice, these projection matrices have get structure from
intrinsic 3x3 matrices modelling focal length `fx`, `fy`,
skew `s` and offset `cx`, `cy`.
Extrinsic 4x4 matrices involve some rotation and translation,
as otherwise any camera we define would be in the same world location.
-/

section PinholeCamera

open Function

/-- Project world point to a pinhole camera -/
noncomputable
def project (camera : P34) (world : P4) : P3 :=
  let image := matmulvec camera world;
  P3.normalise image

-- project cannot be injective because depth is ambiguous
-- so many points in 3D (on a line) map to the same point in 2D
lemma project_once_not_injective : ¬Injective project := by
  refine not_injective_iff.mpr ?_
  constructor
  · sorry
  · exact P34.id

-- intersection of back-projected lines makes a pair injective
-- this needs pseudo-inverse to get 2nd point to make a line,
-- and a variant of project that uses both cameras
lemma project_twice_injective (c1 : P34) (c2 : P34) (h : c1 ≠ c2) : Injective project := by
  sorry

end PinholeCamera

/-!
## Scratchpad

* Matrix API
* Ideals
-/

variable
  (M : Matrix (Fin 3) (Fin 4) ℝ)
  (hM : M.rank = 3)
  (v : Fin 4 → ℝ)
  (f : M.mulVec v 0 = M 0 0 * v 0)

/-- Normalise fintype index function directly -/
noncomputable
def normalise' (u : {v : Fin 4 → ℝ // v ≠ 0}) :=
  if u.1 3 = 0
  then u.1
  else (u.1 3)⁻¹ • u.1


#check ProjectiveSpectrum.vanishingIdeal_closure

#lint

