import Mathlib
import Submission.Work.HP.Defs

/-!
# Definitions for the second-moment estimates `D^mix` and `D^loc` (node N09)

This file collects the objects that the proof of `Work.HP.moment_mix_loc` (Lemma D mixed and
Lemma D loc of Browning--Le Boudec--Sawin) needs, in a `sorry`-free module so that the lemmas
proved in parallel can be stated against them.

* `Sstar k Λ R`, `Sk k Λ R` : the sums `𝓢*_k(Λ;R)`, `𝓢_k(Λ;R)` of the paper.
* `GamMix x y Q`, `GamLoc x y Q` : the lattices `Γ^{mix}_{x,y}(Q)`, `Γ^{loc}_{x,y}(Q)`.
* `TmixSet y A α`, `TlocSet x y A α` : the regions `𝒯^{mix}_y(A,α)`, `𝒯^{loc}_{x,y}(A,α)`.
* `IcVol w z`, `JcVol w z` : the volumes `𝓘(w,z)` and `𝓙(w,z)`.
-/

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

/-! ## Volumes in Euclidean space -/

section volumes
variable {ι : Type*} [Fintype ι]

/-- The linear functional `t ↦ ⟪w,t⟫` on Euclidean space. -/
def innerLin (w : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ where
  toFun t := inner ℝ w t
  map_add' t s := by simp [inner_add_right]
  map_smul' c t := by simp [real_inner_smul_right]

/-- The `dim V`-dimensional Lebesgue volume of `S ∩ V`, for `V` a subspace of Euclidean space.
This is the canonical Lebesgue measure of a finite-dimensional real inner product space, i.e. the
one giving volume `1` to the parallelepiped spanned by an orthonormal basis. -/
def subVol (V : Submodule ℝ (EuclideanSpace ℝ ι)) (S : Set (EuclideanSpace ℝ ι)) : ℝ :=
  (volume {t : V | (t : EuclideanSpace ℝ ι) ∈ S}).toReal

/-- `𝓘(w,z) = vol {t ∈ (ℝw)^⊥ : |⟪z,t⟫| ≤ ‖t‖ ≤ 1}`, an `(N-1)`-dimensional volume. -/
def IcVol (w z : EuclideanSpace ℝ ι) : ℝ :=
  subVol (LinearMap.ker (innerLin w)) {t | |inner ℝ z t| ≤ ‖t‖ ∧ ‖t‖ ≤ 1}

/-- `𝓙(w,z) = vol {t : |⟪w,t⟫|,|⟪z,t⟫| ≤ ‖t‖ ≤ 1}`, an `N`-dimensional volume. -/
def JcVol (w z : EuclideanSpace ℝ ι) : ℝ :=
  (volume {t : EuclideanSpace ℝ ι |
    |inner ℝ w t| ≤ ‖t‖ ∧ |inner ℝ z t| ≤ ‖t‖ ∧ ‖t‖ ≤ 1}).toReal

/-- `δ_{w,z} = ‖w‖²‖z‖² - ⟪w,z⟫²`. -/
def deltaV (w z : EuclideanSpace ℝ ι) : ℝ := ‖w‖ ^ 2 * ‖z‖ ^ 2 - inner ℝ w z ^ 2

end volumes

/-! ## The sums `𝓢*_k` and `𝓢_k`, the lattices `Γ` and the regions `𝒯` -/

section sums
variable (d n : ℕ) [DecidableEq (Mon d n)]

/-- `𝓢*_k(Λ;R) = Σ_{a ∈ Λ, a prim, a ∈ R} ‖a‖^{-k}`. -/
def Sstar (k : ℕ) (L : Submodule ℤ (Mon d n → ℤ)) (R : Set (Mon d n → ℤ)) : ℝ :=
  ∑ᶠ a ∈ {a | a ∈ L ∧ IsPrim a ∧ a ∈ R}, 1 / eNorm a ^ k

/-- `𝓢_k(Λ;R) = Σ_{a ∈ Λ∖0, a ∈ R} ‖a‖^{-k}`. -/
def Sk (k : ℕ) (L : Submodule ℤ (Mon d n → ℤ)) (R : Set (Mon d n → ℤ)) : ℝ :=
  ∑ᶠ a ∈ {a | a ∈ L ∧ a ≠ 0 ∧ a ∈ R}, 1 / eNorm a ^ k

/-- `Γ^{mix}_{x,y}(Q) = Λ_{ν(x)} ∩ Λ^{(Q)}_{ν(y)}`. -/
def GamMix (x y : Fin (n + 1) → ℤ) (Q : ℕ) : Submodule ℤ (Mon d n → ℤ) :=
  latOrth (veronese d n x) ⊓ latMod (veronese d n y) Q

/-- `Γ^{loc}_{x,y}(Q) = Λ^{(Q)}_{ν(x)} ∩ Λ^{(Q)}_{ν(y)}`. -/
def GamLoc (x y : Fin (n + 1) → ℤ) (Q : ℕ) : Submodule ℤ (Mon d n → ℤ) :=
  latMod (veronese d n x) Q ⊓ latMod (veronese d n y) Q

/-- `𝒯^{mix}_y(A,α) = B_N(A) ∩ 𝒞_{ν(y)}^{(α)}`. -/
def TmixSet (y : Fin (n + 1) → ℤ) (A α : ℝ) : Set (Mon d n → ℤ) :=
  {a | eNorm a ≤ A ∧ toR a ∈ Cgam (toR (veronese d n y)) α}

/-- `𝒯^{loc}_{x,y}(A,α) = B_N(A) ∩ 𝒞_{ν(x)}^{(α)} ∩ 𝒞_{ν(y)}^{(α)}`. -/
def TlocSet (x y : Fin (n + 1) → ℤ) (A α : ℝ) : Set (Mon d n → ℤ) :=
  {a | eNorm a ≤ A ∧ toR a ∈ Cgam (toR (veronese d n x)) α ∧
      toR a ∈ Cgam (toR (veronese d n y)) α}

/-- `α = log B`. -/
def alphaOf (B : ℝ) : ℝ := Real.log B

/-- The point of Euclidean space with the same coordinates as `v`. -/
def toE {ι : Type*} (v : ι → ℝ) : EuclideanSpace ℝ ι := WithLp.toLp 2 v

/-- The point of Euclidean space attached to an integer vector. -/
def toEr {ι : Type*} (v : ι → ℤ) : EuclideanSpace ℝ ι := toE (toR v)

/-- The real span of an integral lattice, as a subspace of Euclidean space. -/
def spanE {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) :
    Submodule ℝ (EuclideanSpace ℝ ι) :=
  Submodule.span ℝ (toEr '' (L : Set (ι → ℤ)))

/-- The volume of `span(L) ∩ B(1) ∩ 𝒞_v^{(γ)} ∩ 𝒞_w^{(γ)}`. -/
def coneSliceVol {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ)
    (γ : ℝ) : ℝ :=
  subVol (spanE L) {t : EuclideanSpace ℝ ι |
    |inner ℝ (toE v) t| ≤ ‖toE v‖ * ‖t‖ / (2 * γ) ∧
    |inner ℝ (toE w) t| ≤ ‖toE w‖ * ‖t‖ / (2 * γ) ∧ ‖t‖ ≤ 1}

end sums

/-! ## Elementary properties of `eNorm` -/

section enorm
variable {ι : Type*} [Fintype ι]

lemma eNorm_nonneg (v : ι → ℤ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

lemma eNorm_neg (v : ι → ℤ) : eNorm (-v) = eNorm v := by
  simp [eNorm]

end enorm

/-! ## Basic monotonicity facts -/

section basic
variable {d n : ℕ}

lemma Sk_nonneg (k : ℕ) (L : Submodule ℤ (Mon d n → ℤ)) (R : Set (Mon d n → ℤ)) :
    0 ≤ Sk d n k L R := by
  rw [Sk, finsum_mem_def]
  exact finsum_nonneg fun a => by
    by_cases h : a ∈ {a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ a ∈ R}
    · simp only [Set.indicator_of_mem h]
      exact div_nonneg zero_le_one (pow_nonneg (eNorm_nonneg _) k)
    · simp only [Set.indicator_of_notMem h, le_refl]

lemma TmixSet_mono (y : Fin (n + 1) → ℤ) {A A' α : ℝ} (h : A ≤ A') :
    TmixSet d n y A α ⊆ TmixSet d n y A' α :=
  fun _ ha => ⟨le_trans ha.1 h, ha.2⟩

lemma TlocSet_mono (x y : Fin (n + 1) → ℤ) {A A' α : ℝ} (h : A ≤ A') :
    TlocSet d n x y A α ⊆ TlocSet d n x y A' α :=
  fun _ ha => ⟨le_trans ha.1 h, ha.2.1, ha.2.2⟩

end basic

end Work.HP
