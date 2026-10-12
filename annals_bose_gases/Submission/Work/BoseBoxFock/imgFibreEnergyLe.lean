import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.imgFibreC_fderiv_normSq_le
import Submission.Work.BoseBoxFock.imgFibreDG_integral
import Submission.Work.BoseBoxFock.imgFibreMF_integral
import Submission.Work.BoseBoxFock.imgFibreMG_integral
import Submission.Work.BoseBoxFock.imgFibre_boxSmooth
import Submission.Work.BoseBoxFock.stripImages_cost_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreEnergyLe` — the χ-weighted Dirichlet energy of the images fibre

The position-space fibre of the `χχ`-images words is

    imgFibre ℓ p F₁ G u v = ℓ⁻³ ∫_{x'}∫_{s∈boxL} F₁(insertCoord2 p s v x')·G(insertCoord2 p u v x')

(`Work.BoseBoxFock.imagesFibre`).  This module bounds its **χ-weighted Dirichlet energy**

    pairEnergy ℓ (imgFibreC ℓ p F₁ G)
      = ∫_{box}∫_{box} (Σ_j‖∂_{w_j}(χ_ℓ(w)·fibre w y)‖² + ℓ⁻²‖χ_ℓ(w)·fibre w y‖²)

by the two states' box contents:

    pairEnergy ≤ max (2·Kg + ℓ⁻²·Kc) 2 · (N(F₁)·(N(G) + Dχ(G))/ℓ⁶).

**Route.**  Split off `ℓ⁻³` and Cauchy–Schwarz the `(x', s)`-integral of the *value* and of each
`u`-derivative.  Since `F₁`'s inserted argument `insertCoord2 p s v x'` does not see `u`, while the
hypothesis `hGind` makes `G` invariant under writes to the slot `p.2`, the two factors of the
Cauchy–Schwarz separate:

* value:    `‖fibre u v‖² ≤ ℓ⁻⁶·MF(v)·MG(u)`,
* `u`-grad: `Σ_j‖∂_{u,j}fibre u v‖² ≤ ℓ⁻⁶·MF(v)·DG(u)`,

with the three densities of `imgFibreEnergyDefs`.  Their box integrals are `N(F₁)`, `N(G)` and
`Dχ(G)` by the measure-preserving insertions `splitEquiv` (`imgFibreMF_integral`,
`imgFibreMG_integral`, `imgFibreDG_integral`), and the two dominators

    P z = ℓ⁻⁶·MG(z.1)·MF(z.2),   Q z = ℓ⁻⁶·DG(z.1)·MF(z.2)

are then fed to `pairEnergy_le_of_integral_bounds_chi_param`, whose extra factor `‖χ_ℓ(u)‖²` on the
`Q`-row is exactly what picks out the χ-weighted Dirichlet content.

**Why `Dχ` and not the unweighted `D₁`.**  The sibling statement `imgFibre_pairEnergy_le` (with
`imgFibreD₁` and the power `ℓ⁻³`) is **FALSE** (`FINDING_imgFibre_pairEnergy_le_FALSE.md`): the
window's *concentration* `Kc = sup χ_ℓ²`, not its mean, multiplies the Dirichlet row.  The present
statement uses the `χ²`-weighted content `imgFibreDχ` together with the power `ℓ⁻⁶`, and the
missing factor is supplied automatically: the `χ_ℓ(u)²` in the `Q`-row is a `Kc`-sized weight.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-! ## 1. The window data in the `chiS` spelling -/

/-- The gradient data `hKg` of the real window transfers to the complexified window `chiS ℓ`. -/
theorem hKg_chiS {ℓ Kg : ℝ} (hℓ : 0 < ℓ)
    (hKg : ∀ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ Kg) :
    ∀ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg := by
  intro w
  have h2 : ∀ j : Fin 3,
      ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
        = ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w
            (EuclideanSpace.single j (1 : ℝ))‖ := by
    intro j
    rw [show chiS ℓ = fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) from
      funext (chiS_eq ℓ)]
    rw [ofReal_fderiv (Submission.BoseGases.chiScale ℓ)
      ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).differentiable (by simp))
      w (EuclideanSpace.single j (1 : ℝ))]
    exact RCLike.norm_ofReal _
  calc ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      = ∑ j : Fin 3, ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => by rw [h2 j]
    _ ≤ Kg := hKg w

/-- The mass data `hKc` of the real window transfers to the complexified window `chiS ℓ`. -/
theorem hKc_chiS {ℓ Kc : ℝ}
    (hKc : ∀ w : E3, (Submission.BoseGases.chiScale ℓ w) ^ 2 ≤ Kc) :
    ∀ w : E3, ‖chiS ℓ w‖ ^ 2 ≤ Kc := by
  intro w
  rw [chiS_sq]
  exact hKc w

/-! ## 2. Measurability and bounds of the three densities -/

theorem stronglyMeasurable_imgFibreMF {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    {F : Xn n → ℝ} (hF : Continuous F) :
    StronglyMeasurable (imgFibreMF ℓ p F) := by
  have hjoint : StronglyMeasurable (fun q : (E3 × (pairFib23 n p → E3)) × E3 =>
      (F (insertCoord2 p q.2 q.1.1 q.1.2)) ^ 2) :=
    ((hF.comp (contDiff_insertCoord2_comp p contDiff_snd
      (contDiff_fst.comp contDiff_fst) (contDiff_snd.comp contDiff_fst)).continuous).pow 2
        ).stronglyMeasurable
  have h := stronglyMeasurable_integral_boxPiSet_boxL (ℓ := ℓ)
    (g := fun (v : E3) (x' : pairFib23 n p → E3) (s : E3) =>
      (F (insertCoord2 p s v x')) ^ 2) hjoint
  change StronglyMeasurable (fun v : E3 =>
    ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ, (F (insertCoord2 p s v x')) ^ 2)
  exact h

theorem stronglyMeasurable_imgFibreMG {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    {G : Xn n → ℝ} (hG : Continuous G) :
    StronglyMeasurable (imgFibreMG ℓ p G) := by
  have hjoint : StronglyMeasurable (fun q : (E3 × (pairFib23 n p → E3)) × E3 =>
      (G (insertCoord2 p q.1.1 q.2 q.1.2)) ^ 2) :=
    ((hG.comp (contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst) contDiff_snd
      (contDiff_snd.comp contDiff_fst)).continuous).pow 2).stronglyMeasurable
  have h := stronglyMeasurable_integral_boxPiSet_boxL (ℓ := ℓ)
    (g := fun (u : E3) (x' : pairFib23 n p → E3) (s : E3) =>
      (G (insertCoord2 p u s x')) ^ 2) hjoint
  change StronglyMeasurable (fun u : E3 =>
    ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ, (G (insertCoord2 p u s x')) ^ 2)
  exact h

theorem stronglyMeasurable_imgFibreDG {n : ℕ} (ℓ : ℝ) (p : Fin n × Fin n)
    {G : Xn n → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    StronglyMeasurable (imgFibreDG ℓ p G) := by
  have hd : Continuous (fun q : (E3 × (pairFib23 n p → E3)) × E3 =>
      fderiv ℝ G (insertCoord2 p q.1.1 q.2 q.1.2)) :=
    (hG.continuous_fderiv (by simp)).comp
      (contDiff_insertCoord2_comp p (contDiff_fst.comp contDiff_fst) contDiff_snd
        (contDiff_snd.comp contDiff_fst)).continuous
  have hjoint : StronglyMeasurable (fun q : (E3 × (pairFib23 n p → E3)) × E3 =>
      ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p q.1.1 q.2 q.1.2) (slotDirVec p.1 j)) ^ 2) :=
    (continuous_finset_sum _ fun j _ => (hd.clm_apply continuous_const).pow 2).stronglyMeasurable
  have h := stronglyMeasurable_integral_boxPiSet_boxL (ℓ := ℓ)
    (g := fun (u : E3) (x' : pairFib23 n p → E3) (s : E3) =>
      ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j)) ^ 2) hjoint
  change StronglyMeasurable (fun u : E3 =>
    ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
      ∑ j : Fin 3, (fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j)) ^ 2)
  exact h

/-- A uniform bound for `imgFibreMF` on the box. -/
theorem exists_bound_imgFibreMF {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {F : Xn n → ℝ} (hF : Continuous F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ boxL ℓ, imgFibreMF ℓ p F v ≤ C := by
  obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨M ^ 2 * ((volume (boxPiSet (pairFib23 n p) ℓ)).toReal
    * (volume (boxL ℓ)).toReal), by positivity, fun v hv => ?_⟩
  rw [imgFibreMF]
  have hinner : ∀ x' ∈ boxPiSet (pairFib23 n p) ℓ,
      (∫ s in boxL ℓ, (F (insertCoord2 p s v x')) ^ 2) ≤ M ^ 2 * (volume (boxL ℓ)).toReal := by
    intro x' hx'
    refine setIntegral_boxL_le_const hℓ (fun s _ => by positivity) fun s hs => ?_
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hM _ ((insertCoord2_mem_abox_iff hℓ hs hv x').mpr hx')) 2
  calc (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ, (F (insertCoord2 p s v x')) ^ 2)
      ≤ (M ^ 2 * (volume (boxL ℓ)).toReal) * (volume (boxPiSet (pairFib23 n p) ℓ)).toReal :=
        setIntegral_boxPiSet_le_const hℓ (fun _ _ => integral_nonneg fun _ => by positivity) hinner
    _ = M ^ 2 * ((volume (boxPiSet (pairFib23 n p) ℓ)).toReal
          * (volume (boxL ℓ)).toReal) := by ring

/-- A uniform bound for `imgFibreMG` on the box. -/
theorem exists_bound_imgFibreMG {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {G : Xn n → ℝ} (hG : Continuous G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ boxL ℓ, imgFibreMG ℓ p G u ≤ C := by
  obtain ⟨M, hM⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hG.continuousOn
  refine ⟨M ^ 2 * ((volume (boxPiSet (pairFib23 n p) ℓ)).toReal
    * (volume (boxL ℓ)).toReal), by positivity, fun u hu => ?_⟩
  rw [imgFibreMG]
  have hinner : ∀ x' ∈ boxPiSet (pairFib23 n p) ℓ,
      (∫ s in boxL ℓ, (G (insertCoord2 p u s x')) ^ 2) ≤ M ^ 2 * (volume (boxL ℓ)).toReal := by
    intro x' hx'
    refine setIntegral_boxL_le_const hℓ (fun s _ => by positivity) fun s hs => ?_
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hM _ ((insertCoord2_mem_abox_iff hℓ hu hs x').mpr hx')) 2
  calc (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ, (G (insertCoord2 p u s x')) ^ 2)
      ≤ (M ^ 2 * (volume (boxL ℓ)).toReal) * (volume (boxPiSet (pairFib23 n p) ℓ)).toReal :=
        setIntegral_boxPiSet_le_const hℓ (fun _ _ => integral_nonneg fun _ => by positivity) hinner
    _ = M ^ 2 * ((volume (boxPiSet (pairFib23 n p) ℓ)).toReal
          * (volume (boxL ℓ)).toReal) := by ring

/-- A uniform bound for `imgFibreDG` on the box. -/
theorem exists_bound_imgFibreDG {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n)
    {G : Xn n → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ boxL ℓ, imgFibreDG ℓ p G u ≤ C := by
  choose M hM using fun j : Fin 3 =>
    (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
      ((hG.continuous_fderiv (by simp)).clm_apply continuous_const).continuousOn
  refine ⟨(∑ j : Fin 3, M j ^ 2) * ((volume (boxPiSet (pairFib23 n p) ℓ)).toReal
    * (volume (boxL ℓ)).toReal), by positivity, fun u hu => ?_⟩
  rw [imgFibreDG]
  have hinner : ∀ x' ∈ boxPiSet (pairFib23 n p) ℓ,
      (∫ s in boxL ℓ, ∑ j : Fin 3,
        (fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j)) ^ 2)
      ≤ (∑ j : Fin 3, M j ^ 2) * (volume (boxL ℓ)).toReal := by
    intro x' hx'
    refine setIntegral_boxL_le_const hℓ (fun s _ =>
      Finset.sum_nonneg fun j _ => by positivity) fun s hs => ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← sq_abs, ← Real.norm_eq_abs]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hM j _ ((insertCoord2_mem_abox_iff hℓ hu hs x').mpr hx')) 2
  calc (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ, ∑ j : Fin 3,
          (fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j)) ^ 2)
      ≤ ((∑ j : Fin 3, M j ^ 2) * (volume (boxL ℓ)).toReal)
          * (volume (boxPiSet (pairFib23 n p) ℓ)).toReal :=
        setIntegral_boxPiSet_le_const hℓ (fun _ _ =>
          integral_nonneg fun _ => Finset.sum_nonneg fun j _ => by positivity) hinner
    _ = (∑ j : Fin 3, M j ^ 2) * ((volume (boxPiSet (pairFib23 n p) ℓ)).toReal
          * (volume (boxL ℓ)).toReal) := by ring

/-! ## 3. Continuity and differentiability of the fibre -/

theorem continuous_uncurry_imgFibreC {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Continuous (Function.uncurry (imgFibreC ℓ p F₁ G)) := by
  have hce := imgFibreCore_eq ℓ p F₁ G
  rw [← hce]
  exact (contDiff_imgFibreCore hℓ hF₁ hG).continuous

theorem differentiableAt_imgFibreC {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (z : E3 × E3) :
    DifferentiableAt ℝ (fun w' => imgFibreC ℓ p F₁ G w' z.2) z.1 := by
  have hd : Differentiable ℝ (Function.uncurry (imgFibreC ℓ p F₁ G)) := by
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (imgFibreCore ℓ p F₁ G)) :=
      contDiff_imgFibreCore hℓ hF₁ hG
    rw [imgFibreCore_eq ℓ p F₁ G] at hcd
    exact hcd.differentiable (by simp)
  have h2 : DifferentiableAt ℝ
      (Function.uncurry (imgFibreC ℓ p F₁ G) ∘ fun w' : E3 => (w', z.2)) z.1 :=
    (hd.differentiableAt (x := (z.1, z.2))).comp z.1 (by fun_prop)
  exact h2

/-! ## 4. The `p.2`-independence of the inserted slot -/

/-- Inserting `v` in the slot `p.2` of `insertCoord2 p u s x'` gives `insertCoord2 p u v x'`. -/
theorem insertCoord2_update_p2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) (u v s : E3)
    (x' : pairFib23 n p → E3) :
    insertCoord2 p u v x' = Function.update (insertCoord2 p u s x') p.2 v := by
  funext k
  rw [insertCoord2_eq, insertCoord2_eq, Function.update_apply]
  dsimp only
  by_cases hk2 : k = p.2
  · rw [dif_neg (fun h : k = p.1 => hp (h.symm.trans hk2)), dif_pos hk2, if_pos hk2]
  · rw [if_neg hk2]
    by_cases hk1 : k = p.1
    · rw [dif_pos hk1, dif_pos hk1]
    · rw [dif_neg hk1, dif_neg hk2, dif_neg hk1, dif_neg hk2]

/-- The values of `G` at the two inserted configurations agree, by `p.2`-invariance. -/
theorem imgFibre_G_congr {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {G : Xn n → ℝ}
    (hGind : ∀ (x : Xn n) (t : E3), G (Function.update x p.2 t) = G x)
    (u v s : E3) (x' : pairFib23 n p → E3) :
    G (insertCoord2 p u v x') = G (insertCoord2 p u s x') := by
  rw [insertCoord2_update_p2 p hp u v s x']
  exact hGind (insertCoord2 p u s x') v

/-- The `p.1`-slot derivative of `G` at the two inserted configurations agrees, by
`p.2`-invariance. -/
theorem imgFibre_fderiv_G_update_p2 {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {G : Xn n → ℝ} (hGd : Differentiable ℝ G)
    (hGind : ∀ (x : Xn n) (t : E3), G (Function.update x p.2 t) = G x)
    (u v s : E3) (x' : pairFib23 n p → E3) (j : Fin 3) :
    fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)
      = fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j) := by
  rw [insertCoord2_update_p2 p hp u v s x']
  exact fderiv_update_p2_eq hp hGd hGind _ _ j

/-- The norm of the complexification of a real number. -/
theorem norm_ofReal_C (y : ℝ) : ‖((y : ℝ) : ℂ)‖ = |y| := RCLike.norm_ofReal y

/-- **The mass row of the fibre's Cauchy–Schwarz bound.** -/
theorem imgFibreC_normSq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {F₁ G : Xn n → ℝ} (hF₁ : Continuous F₁) (hG : Continuous G)
    (hGind : ∀ (x : Xn n) (t : E3), G (Function.update x p.2 t) = G x) (u v : E3) :
    ‖imgFibreC ℓ p F₁ G u v‖ ^ 2
      ≤ (ℓ ^ 6)⁻¹ * (imgFibreMF ℓ p F₁ v * imgFibreMG ℓ p G u) := by
  have hF' : Continuous (fun z : (pairFib23 n p → E3) × E3 =>
      F₁ (insertCoord2 p z.2 v z.1)) :=
    hF₁.comp (contDiff_insertCoord2_comp p contDiff_snd contDiff_const contDiff_fst).continuous
  have hG' : Continuous (fun z : (pairFib23 n p → E3) × E3 =>
      G (insertCoord2 p u v z.1)) :=
    hG.comp (contDiff_insertCoord2_comp p contDiff_const contDiff_const contDiff_fst).continuous
  have hcs := sq_integral_boxPiSet_boxL_le (ι := pairFib23 n p) hℓ hF' hG'
  simp only [] at hcs
  have hMF : (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
      (F₁ (insertCoord2 p s v x')) ^ 2) = imgFibreMF ℓ p F₁ v := rfl
  have hMG : (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
      (G (insertCoord2 p u v x')) ^ 2) = imgFibreMG ℓ p G u := by
    rw [imgFibreMG]
    refine integral_congr_ae (Eventually.of_forall fun x' => ?_)
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    rw [imgFibre_G_congr p hp hGind u v s x']
  rw [hMF, hMG] at hcs
  have hnorm : ‖imgFibreC ℓ p F₁ G u v‖ ^ 2 = (imgFibre ℓ p F₁ G u v) ^ 2 := by
    show ‖((imgFibre ℓ p F₁ G u v : ℝ) : ℂ)‖ ^ 2 = (imgFibre ℓ p F₁ G u v) ^ 2
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  rw [hnorm, imgFibre]
  have hc : ((ℓ ^ 3)⁻¹ : ℝ) ^ 2 = (ℓ ^ 6)⁻¹ := by
    rw [inv_pow]
    congr 1
    ring
  rw [mul_pow, hc]
  exact mul_le_mul_of_nonneg_left hcs (by positivity)

/-! ## 5. The assembly -/

/-- **The fibre-energy bound from the two pointwise Cauchy–Schwarz inequalities and the three
box-integral identities.**  This is the whole analytic content of `imgFibreEnergyLe`; the five
inputs are proved in the sibling modules of this directory. -/
theorem imgFibreEnergyLe_of_inputs {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {F₁ G : Xn n → ℝ} (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    {Kg Kc : ℝ} (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc)
    (hKg : ∀ w : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ Kg)
    (hKc : ∀ w : E3, (Submission.BoseGases.chiScale ℓ w) ^ 2 ≤ Kc)
    (hval : ∀ u v : E3, ‖imgFibreC ℓ p F₁ G u v‖ ^ 2
      ≤ (ℓ ^ 6)⁻¹ * (imgFibreMF ℓ p F₁ v * imgFibreMG ℓ p G u))
    (hdb : ∀ u v : E3, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => imgFibreC ℓ p F₁ G w' v) u
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ (ℓ ^ 6)⁻¹ * (imgFibreMF ℓ p F₁ v * imgFibreDG ℓ p G u))
    (hMFint : (∫ v in boxL ℓ, imgFibreMF ℓ p F₁ v) = imgFibreN ℓ F₁)
    (hMGint : (∫ u in boxL ℓ, imgFibreMG ℓ p G u) = imgFibreN ℓ G)
    (hDGint : (∫ u in boxL ℓ, (Submission.BoseGases.chiScale ℓ u) ^ 2 * imgFibreDG ℓ p G u)
      = imgFibreDχ ℓ p G) :
    L1Tails.pairEnergy ℓ (imgFibreC ℓ p F₁ G)
      ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
        * (imgFibreN ℓ F₁ * (imgFibreN ℓ G + imgFibreDχ ℓ p G) / ℓ ^ 6) := by
  obtain ⟨CF, hCF0, hCF⟩ := exists_bound_imgFibreMF hℓ p hF₁.continuous
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_imgFibreMG hℓ p hG.continuous
  obtain ⟨CD, hCD0, hCD⟩ := exists_bound_imgFibreDG hℓ p hG
  have hMFsm : StronglyMeasurable (imgFibreMF ℓ p F₁) :=
    stronglyMeasurable_imgFibreMF ℓ p hF₁.continuous
  have hMGsm : StronglyMeasurable (imgFibreMG ℓ p G) :=
    stronglyMeasurable_imgFibreMG ℓ p hG.continuous
  have hDGsm : StronglyMeasurable (imgFibreDG ℓ p G) :=
    stronglyMeasurable_imgFibreDG ℓ p hG
  have hbox : MeasurableSet (boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hℓ6 : 0 < ℓ ^ 6 := by positivity
  have hinv6 : 0 ≤ (ℓ ^ 6)⁻¹ := by positivity
  set P : E3 × E3 → ℝ :=
    fun z => (ℓ ^ 6)⁻¹ * (imgFibreMG ℓ p G z.1 * imgFibreMF ℓ p F₁ z.2) with hPdef
  set Q : E3 × E3 → ℝ :=
    fun z => (ℓ ^ 6)⁻¹ * (imgFibreDG ℓ p G z.1 * imgFibreMF ℓ p F₁ z.2) with hQdef
  have hP0 : ∀ z, 0 ≤ P z := fun z => by
    rw [hPdef]
    exact mul_nonneg hinv6 (mul_nonneg (imgFibreMG_nonneg ℓ p G z.1)
      (imgFibreMF_nonneg ℓ p F₁ z.2))
  have hQ0 : ∀ z, 0 ≤ Q z := fun z => by
    rw [hQdef]
    exact mul_nonneg hinv6 (mul_nonneg (imgFibreDG_nonneg ℓ p G z.1)
      (imgFibreMF_nonneg ℓ p F₁ z.2))
  have hval' : ∀ z : E3 × E3, ‖imgFibreC ℓ p F₁ G z.1 z.2‖ ^ 2 ≤ P z := by
    intro z
    calc ‖imgFibreC ℓ p F₁ G z.1 z.2‖ ^ 2
        ≤ (ℓ ^ 6)⁻¹ * (imgFibreMF ℓ p F₁ z.2 * imgFibreMG ℓ p G z.1) := hval z.1 z.2
      _ = P z := by rw [hPdef]; ring
  have hdb' : ∀ z : E3 × E3, ∑ j : Fin 3,
      ‖fderiv ℝ (fun w' => imgFibreC ℓ p F₁ G w' z.2) z.1
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Q z := by
    intro z
    calc ∑ j : Fin 3, ‖fderiv ℝ (fun w' => imgFibreC ℓ p F₁ G w' z.2) z.1
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ (ℓ ^ 6)⁻¹ * (imgFibreMF ℓ p F₁ z.2 * imgFibreDG ℓ p G z.1) := hdb z.1 z.2
      _ = Q z := by rw [hQdef]; ring
  have hPint : IntegrableOn P (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound (C := (ℓ ^ 6)⁻¹ * (CG * CF)) ?_ ?_
    · rw [hPdef]
      exact (((hMGsm.comp_measurable measurable_fst).mul
        (hMFsm.comp_measurable measurable_snd)).const_mul ((ℓ ^ 6)⁻¹)
          ).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (hP0 z), hPdef]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hCG z.1 hz.1) (hCF z.2 hz.2)
          (imgFibreMF_nonneg ℓ p F₁ z.2) hCG0) hinv6
  have hWQint : IntegrableOn (fun z : E3 × E3 => ‖chiS ℓ z.1‖ ^ 2 * Q z)
      (boxL ℓ ×ˢ boxL ℓ) := by
    refine integrableOn_boxL_prod_of_aeBound (C := Kc * ((ℓ ^ 6)⁻¹ * (CD * CF))) ?_ ?_
    · refine AEStronglyMeasurable.mul
        ((((continuous_chiS ℓ).comp continuous_fst).norm.pow 2).stronglyMeasurable
          |>.aestronglyMeasurable) ?_
      rw [hQdef]
      exact (((hDGsm.comp_measurable measurable_fst).mul
        (hMFsm.comp_measurable measurable_snd)).const_mul ((ℓ ^ 6)⁻¹)
          ).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict (hbox.prod hbox)] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hQ0 z)), hQdef, chiS_sq]
      exact mul_le_mul (hKc z.1)
        (mul_le_mul_of_nonneg_left (mul_le_mul (hCD z.1 hz.1) (hCF z.2 hz.2)
          (imgFibreMF_nonneg ℓ p F₁ z.2) hCD0) hinv6)
        (mul_nonneg hinv6 (mul_nonneg (imgFibreDG_nonneg ℓ p G z.1)
          (imgFibreMF_nonneg ℓ p F₁ z.2))) hKc0
  have hPintEq : (∫ z in boxL ℓ ×ˢ boxL ℓ, P z)
      = (ℓ ^ 6)⁻¹ * (imgFibreN ℓ G * imgFibreN ℓ F₁) := by
    rw [hPdef]
    change (∫ z in boxL ℓ ×ˢ boxL ℓ,
        (ℓ ^ 6)⁻¹ * (imgFibreMG ℓ p G z.1 * imgFibreMF ℓ p F₁ z.2))
      = (ℓ ^ 6)⁻¹ * (imgFibreN ℓ G * imgFibreN ℓ F₁)
    rw [MeasureTheory.integral_const_mul]
    congr 1
    show (∫ z in boxL ℓ ×ˢ boxL ℓ, imgFibreMG ℓ p G z.1 * imgFibreMF ℓ p F₁ z.2
        ∂((volume : Measure E3).prod (volume : Measure E3))) = imgFibreN ℓ G * imgFibreN ℓ F₁
    rw [MeasureTheory.setIntegral_prod_mul (μ := (volume : Measure E3))
      (ν := (volume : Measure E3))
      (f := fun u : E3 => imgFibreMG ℓ p G u)
      (g := fun v : E3 => imgFibreMF ℓ p F₁ v) (s := boxL ℓ) (t := boxL ℓ),
      hMGint, hMFint]
  have hWQintEq : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * Q z)
      = (ℓ ^ 6)⁻¹ * (imgFibreDχ ℓ p G * imgFibreN ℓ F₁) := by
    have hpt : ∀ z : E3 × E3, ‖chiS ℓ z.1‖ ^ 2 * Q z
        = (ℓ ^ 6)⁻¹ * (((Submission.BoseGases.chiScale ℓ z.1) ^ 2
            * imgFibreDG ℓ p G z.1) * imgFibreMF ℓ p F₁ z.2) := by
      intro z
      rw [hQdef, chiS_sq]; ring
    rw [MeasureTheory.integral_congr_ae (Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul]
    congr 1
    show (∫ z in boxL ℓ ×ˢ boxL ℓ,
        ((Submission.BoseGases.chiScale ℓ z.1) ^ 2 * imgFibreDG ℓ p G z.1)
          * imgFibreMF ℓ p F₁ z.2 ∂((volume : Measure E3).prod (volume : Measure E3)))
      = imgFibreDχ ℓ p G * imgFibreN ℓ F₁
    rw [MeasureTheory.setIntegral_prod_mul (μ := (volume : Measure E3))
      (ν := (volume : Measure E3))
      (f := fun u : E3 => (Submission.BoseGases.chiScale ℓ u) ^ 2 * imgFibreDG ℓ p G u)
      (g := fun v : E3 => imgFibreMF ℓ p F₁ v) (s := boxL ℓ) (t := boxL ℓ),
      hDGint, hMFint]
  have hA0 : 0 ≤ imgFibreN ℓ F₁ * imgFibreN ℓ G / ℓ ^ 6 :=
    div_nonneg (mul_nonneg (imgFibreN_nonneg ℓ F₁) (imgFibreN_nonneg ℓ G)) hℓ6.le
  have hB0 : 0 ≤ imgFibreN ℓ F₁ * imgFibreDχ ℓ p G / ℓ ^ 6 :=
    div_nonneg (mul_nonneg (imgFibreN_nonneg ℓ F₁) (imgFibreDχ_nonneg ℓ p G)) hℓ6.le
  have hPleA : (∫ z in boxL ℓ ×ˢ boxL ℓ, P z) ≤ imgFibreN ℓ F₁ * imgFibreN ℓ G / ℓ ^ 6 := by
    rw [hPintEq, div_eq_mul_inv]
    exact le_of_eq (by ring)
  have hWQleB : (∫ z in boxL ℓ ×ˢ boxL ℓ, ‖chiS ℓ z.1‖ ^ 2 * Q z)
      ≤ imgFibreN ℓ F₁ * imgFibreDχ ℓ p G / ℓ ^ 6 := by
    rw [hWQintEq, div_eq_mul_inv]
    exact le_of_eq (by ring)
  have hmain := pairEnergy_le_of_integral_bounds_chi_param (ℓ := ℓ) (Kg := Kg) (Kc := Kc)
    hℓ hKg0 hKc0 (hKg_chiS hℓ hKg) (hKc_chiS hKc)
    hA0 hB0 hP0 hQ0 hval' hdb' (fun z => differentiableAt_imgFibreC hℓ hF₁ hG z)
    (continuous_uncurry_imgFibreC hℓ hF₁ hG) hPint hWQint hPleA hWQleB
  have harith : imgFibreN ℓ F₁ * imgFibreN ℓ G / ℓ ^ 6
      + imgFibreN ℓ F₁ * imgFibreDχ ℓ p G / ℓ ^ 6
      = imgFibreN ℓ F₁ * (imgFibreN ℓ G + imgFibreDχ ℓ p G) / ℓ ^ 6 := by ring
  rw [harith] at hmain
  exact hmain

/-! ## 6. The target -/

theorem imgFibreEnergyLe {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {F₁ G : Submission.BoseGases.X n → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGind : ∀ (x : Submission.BoseGases.X n) (t : EuclideanSpace ℝ (Fin 3)),
      G (Function.update x p.2 t) = G x)
    {Kg Kc : ℝ} (hKg0 : 0 ≤ Kg) (hKc0 : 0 ≤ Kc)
    (hKg : ∀ w : EuclideanSpace ℝ (Fin 3),
      ∑ j : Fin 3,
        ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Kg)
    (hKc : ∀ w : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chiScale ℓ w) ^ 2 ≤ Kc) :
    Work.BoseBoxFock.L1Tails.pairEnergy ℓ (Work.BoseBoxFock.imgFibreC ℓ p F₁ G)
      ≤ max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2
        * (Work.BoseBoxFock.imgFibreN ℓ F₁
            * (Work.BoseBoxFock.imgFibreN ℓ G + Work.BoseBoxFock.imgFibreDχ ℓ p G) / ℓ ^ 6) :=
  imgFibreEnergyLe_of_inputs hℓ hp hF₁ hG hKg0 hKc0 hKg hKc
    (fun u v => imgFibreC_normSq_le hℓ hp hF₁.continuous hG.continuous hGind u v)
    (fun u v => imgFibreC_fderiv_normSq_le hℓ hp hF₁ hG hGind u v)
    (imgFibreMF_integral hℓ hp hF₁.continuous)
    (imgFibreMG_integral hℓ hp hG.continuous)
    (imgFibreDG_integral hℓ hp hG)

end Work.BoseBoxFock
