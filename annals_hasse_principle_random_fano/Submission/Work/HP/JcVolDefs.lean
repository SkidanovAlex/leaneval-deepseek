import Mathlib
import Submission.Work.HP.MMDefs

/-!
# Definitions for the volume asymptotics `𝓙(w,z)` (Lemma 4.3 of Browning--Le Boudec--Sawin)

This file sets up the geometry of the volume
`𝓙(w,z) = vol {t : |⟪w,t⟫| ≤ ‖t‖ ∧ |⟪z,t⟫| ≤ ‖t‖ ∧ ‖t‖ ≤ 1}`
for linearly independent `w z` in a finite-dimensional Euclidean space.

The plan of the proof of `Work.HP.JcVolAsymp`:

* `P = ℝw ⊕ ℝz` is the plane spanned by `w,z` (dimension two) and `Q = Pᗮ` its orthogonal
  complement (dimension `N-2`), where `N = card ι ≥ 3`.
* The linear functional `Λ : P → ℝ²`, `a ↦ (⟪w,a⟫, ⟪z,a⟫)`, is a linear isomorphism, and
  `Λ.symm u = u₀ c₁ + u₁ c₂` where
  `c₁ = (‖z‖²w - ⟪w,z⟫z)/δ`, `c₂ = (-⟪w,z⟫ w + ‖w‖² z)/δ`, `δ = ‖w‖²‖z‖² - ⟪w,z⟫²`.
* Fubini over the orthogonal decomposition `E = P ⊕ Q` writes the volume as an integral over `P`
  of the `(N-2)`-dimensional volume of the fibre, which is an annulus in `Q`; the substitution
  `a = Λ.symm u` (volume factor `δ^{-1/2}`) then gives the explicit two-dimensional integral.

The definitions below are exactly the objects these steps need.
-/

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

variable {ι : Type*} [Fintype ι]

/-- The plane `P = ℝw ⊕ ℝz` spanned by `w` and `z`. -/
def planeP (w z : EuclideanSpace ℝ ι) : Submodule ℝ (EuclideanSpace ℝ ι) :=
  Submodule.span ℝ {w, z}

/-- The orthogonal complement `Q = Pᗮ` of the plane spanned by `w` and `z`. -/
abbrev perpQ (w z : EuclideanSpace ℝ ι) : Submodule ℝ (EuclideanSpace ℝ ι) := (planeP w z)ᗮ

/-- The vector `c₁ = (‖z‖²w - ⟪w,z⟫z)/δ` of the paper's Lemma 4.3. -/
def c1V (w z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (deltaV w z)⁻¹ • ((‖z‖ ^ 2) • w - (inner ℝ w z) • z)

/-- The vector `c₂ = (-⟪w,z⟫w + ‖w‖²z)/δ` of the paper's Lemma 4.3. -/
def c2V (w z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (deltaV w z)⁻¹ • (-(inner ℝ w z) • w + (‖w‖ ^ 2) • z)

/-- The linear map `Λ : P → ℝ²`, `a ↦ (⟪w,a⟫, ⟪z,a⟫)`. -/
def lamP (w z : EuclideanSpace ℝ ι) : ↥(planeP w z) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun a := WithLp.toLp 2 ![inner ℝ w (a : EuclideanSpace ℝ ι), inner ℝ z (a : EuclideanSpace ℝ ι)]
  map_add' a b := by
    ext i
    fin_cases i <;> simp [inner_add_right]
  map_smul' c a := by
    ext i
    fin_cases i <;> simp [real_inner_smul_right]

/-- The quadratic form `q(u) = ‖u₀ z - u₁ w‖²/δ`; for `u = Λ a` it equals `‖a‖²`. -/
def qform (w z : EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖(u 0) • z - (u 1) • w‖ ^ 2 / deltaV w z

/-- The function `u ↦ max(u₀², u₁²)`. -/
def qbar (u : EuclideanSpace ℝ (Fin 2)) : ℝ := max ((u 0) ^ 2) ((u 1) ^ 2)

/-- `V_Q`: the volume of the unit ball of `Q = Pᗮ`, an `(N-2)`-dimensional volume. -/
def VQ (w z : EuclideanSpace ℝ ι) : ℝ :=
  (volume (Metric.closedBall 0 1 : Set ↥(perpQ w z))).toReal

/-- The integrand of the explicit two-dimensional integral: the `(N-2)`-dimensional volume of the
annulus `{s ∈ Q : q(u) + ‖s‖² ∈ [max(u₀²,u₁²), 1]}` (zero when `max(u₀²,u₁²) > 1`, where the
annulus is empty). -/
def hfun (w z : EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if qbar u ≤ 1 then
    VQ w z * ((Real.sqrt (max (1 - qform w z u) 0)) ^ (Fintype.card ι - 2) -
      (Real.sqrt (max (qbar u - qform w z u) 0)) ^ (Fintype.card ι - 2))
  else 0

/-- The model integrand `4‖v‖²` integrated over the unit ball of `Q`, i.e. the main term
`4 (N-2)/N · ballVol (N-2)` up to the factor `δ^{-1/2}`. -/
def mainTermJ (w z : EuclideanSpace ℝ ι) : ℝ :=
  4 * ((Fintype.card ι : ℝ) - 2) / (Fintype.card ι : ℝ) *
    ballVol (Fintype.card ι - 2) / Real.sqrt (deltaV w z)

/-- `w` and `z` are linearly independent, the hypothesis of the theorem. -/
def IsIndep (w z : EuclideanSpace ℝ ι) : Prop := LinearIndependent ℝ ![w, z]

/-- The region whose volume is `𝓙(w,z)`. -/
def Jset (w z : EuclideanSpace ℝ ι) : Set (EuclideanSpace ℝ ι) :=
  {t | |inner ℝ w t| ≤ ‖t‖ ∧ |inner ℝ z t| ≤ ‖t‖ ∧ ‖t‖ ≤ 1}

/-- The dimension `N - 2` of `Q = Pᗮ`, as a natural number. -/
def dimQ (ι : Type*) [Fintype ι] : ℕ := Fintype.card ι - 2

section basic
variable (w z : EuclideanSpace ℝ ι)

lemma c1V_mem : c1V w z ∈ planeP w z := by
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

lemma c2V_mem : c2V w z ∈ planeP w z := by
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ ?_)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

@[simp] lemma lamP_apply_zero (a : ↥(planeP w z)) : (lamP w z a) 0 = inner ℝ w (a : EuclideanSpace ℝ ι) := rfl

@[simp] lemma lamP_apply_one (a : ↥(planeP w z)) : (lamP w z a) 1 = inner ℝ z (a : EuclideanSpace ℝ ι) := rfl

/-- The element of `P` with coordinates `u`. -/
def cComb (w z : EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ ι :=
  (u 0) • c1V w z + (u 1) • c2V w z

lemma cComb_mem (u : EuclideanSpace ℝ (Fin 2)) : cComb w z u ∈ planeP w z :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (c1V_mem w z)) (Submodule.smul_mem _ _ (c2V_mem w z))

end basic

section split
variable (w z : EuclideanSpace ℝ ι)

/-- The measurable equivalence `E ≃ᵐ P × Q` coming from the orthogonal decomposition
`E = P ⊕ Pᗮ`. -/
def splitP : EuclideanSpace ℝ ι ≃ᵐ ↥(planeP w z) × ↥(perpQ w z) :=
  (planeP w z).measurableEquivProd (0 : EuclideanSpace ℝ ι)

lemma splitP_symm_apply (a : ↥(planeP w z)) (s : ↥(perpQ w z)) :
    ((splitP w z).symm (a, s) : EuclideanSpace ℝ ι) =
      (a : EuclideanSpace ℝ ι) + (s : EuclideanSpace ℝ ι) := by
  rw [splitP, Submodule.measurableEquivProd_symm_apply, vadd_eq_add, add_zero]

lemma measurePreserving_splitP :
    MeasurePreserving (splitP w z) (volume : Measure (EuclideanSpace ℝ ι))
      (volume : Measure (↥(planeP w z) × ↥(perpQ w z))) := by
  have h := Submodule.measurePreserving_measurableEquivProd (planeP w z) (0 : EuclideanSpace ℝ ι)
  rwa [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h

end split

/-- The region `𝓙` is closed, hence measurable. -/
lemma isClosed_Jset (w z : EuclideanSpace ℝ ι) : IsClosed (Jset w z) := by
  unfold Jset
  refine (isClosed_le ?_ continuous_norm).inter ((isClosed_le ?_ continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  · exact continuous_abs.comp (continuous_const.inner continuous_id)
  · exact continuous_abs.comp (continuous_const.inner continuous_id)

section fibres
variable (w z : EuclideanSpace ℝ ι)

/-- The fibre of `𝓙(w,z)` over `a ∈ P`: `{s ∈ Q | a + s ∈ 𝓙(w,z)}`. -/
def fibreSet (a : ↥(planeP w z)) : Set ↥(perpQ w z) :=
  {s : ↥(perpQ w z) | (a : EuclideanSpace ℝ ι) + (s : EuclideanSpace ℝ ι) ∈ Jset w z}

/-- The annulus in `Q` over `a ∈ P` cut out by the two cone conditions. -/
def annSet (a : ↥(planeP w z)) : Set ↥(perpQ w z) :=
  {s : ↥(perpQ w z) |
    qbar (lamP w z a) ≤ ‖(a : EuclideanSpace ℝ ι)‖ ^ 2 + ‖s‖ ^ 2 ∧
      ‖(a : EuclideanSpace ℝ ι)‖ ^ 2 + ‖s‖ ^ 2 ≤ 1}

end fibres

/-- The normalized integrand `nu = hfun / VQ` (unguarded). -/
def nu (w z : EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (Real.sqrt (max (1 - qform w z u) 0)) ^ (Fintype.card ι - 2) -
    (Real.sqrt (max (qbar u - qform w z u) 0)) ^ (Fintype.card ι - 2)

/-- The normalized integrand of `hfun` (zero when `qbar u > 1`). -/
def mu (w z : EuclideanSpace ℝ ι) (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if qbar u ≤ 1 then nu w z u else 0

/-- The model integrand: `1 - (√qbar)^d` on `{qbar ≤ 1}`. -/
def m0 (d : ℕ) (u : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  if qbar u ≤ 1 then 1 - (Real.sqrt (qbar u)) ^ d else 0

end Work.HP
