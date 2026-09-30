import Mathlib
import Submission.Work.HypModel.mobius_contDiffOn
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Smoothness of a locally Möbius map on `{q : q 3 ≠ 0}`

`Work.HypModel.mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)` is the action of a Lorentz matrix `A` on
the upper half space model of hyperbolic 4-space.  The library already knows
(`Work.HypModel.mobius_contDiffOn`) that `mobius A` is `C^∞` (indeed analytic) on the upper half
space `{q : 0 < q 3}` — the image of the upper sheet of the hyperboloid under `A`, on which the
height `(A *ᵥ hypOfUHS q) 4 - (A *ᵥ hypOfUHS q) 3` cannot vanish.

Here we extend that to the full set `{q : q 3 ≠ 0}`, i.e. to the whole complement of the boundary
hyperplane `q 3 = 0`.  The point is that the upper half space model `E4` carries an *involution*
`neg3 q = (q₀,q₁,q₂,−q₃)`, the reflection in the hyperplane `q 3 = 0`, which on the hyperboloid is
the antipodal map `P ↦ −P`: because `hypOfUHS (neg3 q) = - hypOfUHS q` (and `A` is linear, and
`uhsOfHyp (-P) = neg3 (uhsOfHyp P)`), the maps commute,

`mobius A (neg3 q) = neg3 (mobius A q)`   (`Work.RTOwed.mobius_neg3`),

so `mobius A = neg3 ∘ mobius A ∘ neg3` and smoothness on the lower half space `{q 3 < 0}` follows
from smoothness on the upper half space `{q 3 > 0}` transported by the linear (hence smooth)
involution `neg3`.

The main theorem `Work.RTOwed.contDiffOn_of_localMobius` is then immediate: a map which agrees
locally with Möbius transformations on an open neighbourhood of every point of a set `T` whose
points all have `z 3 ≠ 0` is `C^∞` on `T`, because `ContDiffOn` is a local condition
(`contDiffOn_of_locally_contDiffOn`).
-/

namespace Work.RTOwed

open scoped Matrix InnerProductSpace
open Work.HypModel

/-! ### The reflection `q ↦ (q₀,q₁,q₂,−q₃)` of the upper half space coordinates -/

/-- `neg3 q = (q₀,q₁,q₂,−q₃)`: the reflection of the upper half space coordinates in the
hyperplane `q 3 = 0`.  On the hyperboloid it is the antipodal map `P ↦ -P`; hence it commutes with
the Möbius action of every matrix (`Work.RTOwed.mobius_neg3`), while not itself being a Möbius
transformation. -/
def neg3 (q : E4) : E4 := !₂[q 0, q 1, q 2, - q 3]

@[simp] theorem neg3_apply_zero (q : E4) : neg3 q 0 = q 0 := rfl
@[simp] theorem neg3_apply_one (q : E4) : neg3 q 1 = q 1 := rfl
@[simp] theorem neg3_apply_two (q : E4) : neg3 q 2 = q 2 := rfl
@[simp] theorem neg3_apply_three (q : E4) : neg3 q 3 = - q 3 := rfl

/-- `neg3` is an involution. -/
theorem neg3_invol (q : E4) : neg3 (neg3 q) = q := by
  ext i; fin_cases i <;> simp

/-- `neg3` preserves the Euclidean norm: it is a linear isometry of `E4`. -/
theorem norm_sq_neg3 (q : E4) : ‖neg3 q‖ ^ 2 = ‖q‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [neg3, Fin.sum_univ_four, PiLp.toLp_apply]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Real.norm_eq_abs, sq_abs]

/-- On the hyperboloid, `neg3` is the antipodal map: `hypOfUHS (neg3 q) = - hypOfUHS q`. -/
theorem hypOfUHS_neg3 (q : E4) : hypOfUHS (neg3 q) = - hypOfUHS q := by
  ext i
  fin_cases i <;> simp [hypOfUHS, norm_sq_neg3, div_neg]

/-- The inverse chart `uhsOfHyp` is compatible with the antipodal map:
`uhsOfHyp (-P) = neg3 (uhsOfHyp P)`. -/
theorem uhsOfHyp_neg (P : V5) : uhsOfHyp (-P) = neg3 (uhsOfHyp P) := by
  have h : -P 4 + P 3 = -(P 4 - P 3) := by ring
  have h2 : (P 3 - P 4)⁻¹ = -(P 4 - P 3)⁻¹ := by
    rw [show P 3 - P 4 = -(P 4 - P 3) by ring, inv_neg]
  ext i
  fin_cases i <;> simp [uhsOfHyp, h, h2, Pi.neg_apply]

/-- **The Möbius action commutes with the reflection `neg3`** (for *every* matrix `A`, Lorentz or
not): `mobius A (neg3 q) = neg3 (mobius A q)`. -/
theorem mobius_neg3 (A : Matrix (Fin 5) (Fin 5) ℝ) (q : E4) :
    mobius A (neg3 q) = neg3 (mobius A q) := by
  rw [mobius, hypOfUHS_neg3, Matrix.mulVec_neg, uhsOfHyp_neg]
  rfl

/-- `neg3` is linear, hence smooth. -/
theorem contDiff_neg3 : ContDiff ℝ ⊤ neg3 := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ ⊤ (fun q : E4 => q 0)
    exact (EuclideanSpace.proj (0 : Fin 4) : E4 →L[ℝ] ℝ).contDiff
  · change ContDiff ℝ ⊤ (fun q : E4 => q 1)
    exact (EuclideanSpace.proj (1 : Fin 4) : E4 →L[ℝ] ℝ).contDiff
  · change ContDiff ℝ ⊤ (fun q : E4 => q 2)
    exact (EuclideanSpace.proj (2 : Fin 4) : E4 →L[ℝ] ℝ).contDiff
  · change ContDiff ℝ ⊤ (fun q : E4 => - q 3)
    exact ((EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).contDiff).neg

/-! ### Smoothness of `mobius A` on `{q : q 3 ≠ 0}` -/

/-- **A Möbius transformation is smooth on the complement of the boundary hyperplane**, i.e. on
both half spaces `q 3 > 0` and `q 3 < 0`.  This strengthens `Work.HypModel.mobius_contDiffOn`
(which covers only `q 3 > 0`); the two halves are exchanged by the involution `neg3`, and
`mobius A ∘ neg3 = neg3 ∘ mobius A`. -/
theorem contDiffOn_mobius_height_ne {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    ContDiffOn ℝ ⊤ (mobius A) {q : E4 | q 3 ≠ 0} := by
  refine contDiffOn_of_locally_contDiffOn (fun z hz => ?_)
  have hproj : Continuous fun q : E4 => q 3 :=
    (EuclideanSpace.proj (3 : Fin 4) : E4 →L[ℝ] ℝ).continuous
  rcases lt_or_gt_of_ne hz with hlt | hgt
  · -- the lower half space: transport the known case by the reflection `neg3`
    have hsub : {q : E4 | q 3 < 0} ⊆ {q : E4 | q 3 ≠ 0} := fun q hq => ne_of_lt hq
    refine ⟨{q : E4 | q 3 < 0}, isOpen_lt hproj continuous_const, hlt, ?_⟩
    rw [Set.inter_eq_right.mpr hsub]
    have hcomp : ContDiffOn ℝ ⊤ (mobius A ∘ neg3) {q : E4 | q 3 < 0} :=
      (mobius_contDiffOn hA).comp contDiff_neg3.contDiffOn
        (fun q hq => by show 0 < (neg3 q) 3; rw [neg3_apply_three]; exact neg_pos.mpr hq)
    have hstep : ContDiffOn ℝ ⊤ (neg3 ∘ mobius A) {q : E4 | q 3 < 0} :=
      hcomp.congr (fun q _ => by simp [Function.comp_apply, mobius_neg3])
    have hpeel := (contDiff_neg3.contDiffOn (s := Set.univ)).comp hstep (fun q _ => trivial)
    exact hpeel.congr (fun q _ => by simp [Function.comp_apply, neg3_invol])
  · -- the upper half space: this is `HypModel.mobius_contDiffOn`
    have hsub : {q : E4 | 0 < q 3} ⊆ {q : E4 | q 3 ≠ 0} := fun q hq => ne_of_gt hq
    refine ⟨{q : E4 | 0 < q 3}, isOpen_lt continuous_const hproj, hgt, ?_⟩
    rw [Set.inter_eq_right.mpr hsub]
    exact mobius_contDiffOn hA

/-! ### The main theorem -/

theorem contDiffOn_of_localMobius {w : Work.Cusp.E4 → Work.Cusp.E4} {T : Set Work.Cusp.E4}
    (hT : ∀ z ∈ T, z 3 ≠ 0)
    (h : ∀ z ∈ T, ∃ (V : Set Work.Cusp.E4) (B : Matrix (Fin 5) (Fin 5) ℝ),
      IsOpen V ∧ z ∈ V ∧ Work.HypModel.IsLorentzMat B ∧
      ∀ z' ∈ V, w z' = Work.HypModel.mobius B z') :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w T := by
  -- `ContDiffOn` is a local condition on the domain, so it suffices to prove it near each point.
  refine contDiffOn_of_locally_contDiffOn (fun z hz => ?_)
  obtain ⟨V, B, hVopen, hzV, hB, hw⟩ := h z hz
  refine ⟨V, hVopen, hzV, ?_⟩
  -- on `T ∩ V` the map `w` is the Möbius transformation of `B`, and `T ⊆ {q | q 3 ≠ 0}`.
  have hsub : T ∩ V ⊆ {q : Work.Cusp.E4 | q 3 ≠ 0} := fun q hq => hT q hq.1
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.HypModel.mobius B) (T ∩ V) :=
    ((contDiffOn_mobius_height_ne hB).mono hsub).of_le le_top
  exact hsm.congr (fun q hq => hw q hq.2)

end Work.RTOwed
