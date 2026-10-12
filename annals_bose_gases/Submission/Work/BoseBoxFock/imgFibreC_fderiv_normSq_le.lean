import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.fderiv_update_p2_eq
import Submission.Work.BoseBoxFock.imgFibreC_fderiv_slot
import Submission.Work.BoseBoxFock.sq_integral_boxPiSet_boxL_le
import Submission.Work.BoseBoxFock.sum_integral_boxPiSet_boxL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imgFibreC_fderiv_normSq_le` — the gradient row of the fibre's
Cauchy–Schwarz bound

The position-space fibre of the `χχ`-images words is

    imgFibre ℓ p F₁ G u v = ℓ⁻³ ∫_{x'} ∫_{s ∈ boxL} F₁ (ins p s v x') · G (ins p u v x')
    (ins = `insertCoord2`),

and its complexification is `imgFibreC`.  This module bounds the **`u`-gradient** of `imgFibreC`
by the two box *densities* of `imgFibreEnergyDefs`:

    ∑_{j<3} ‖∂_{u,j} imgFibreC ℓ p F₁ G u v‖²
      ≤ ℓ⁻⁶ · (imgFibreMF ℓ p F₁ v · imgFibreDG ℓ p G u) ,

where

* `imgFibreMF ℓ p F₁ v = ∫_{x'}∫_{s∈boxL} F₁ (ins p s v x')²` is the (u-free) `L²`-content of `F₁`,
* `imgFibreDG ℓ p G u = ∫_{x'}∫_{s∈boxL} Σ_j (∂_{p.1,j}G)(ins p u s x')²` is the `p.1`-slot
  Dirichlet density of `G`.

This is the `hdb` input of `Work.BoseBoxFock.imgFibreEnergyLe_of_inputs`; its value-row companion
is `Work.BoseBoxFock.imgFibreC_normSq_le` (in `imgFibreEnergyLe.lean`).

## The proof

The `u`-dependence of the fibre sits only in the `G`-factor, whose derivative is computed by the
proved `imgFibreC_fderiv_slot`:

    ∂_{u,j} imgFibreC u v = ℓ⁻³ ∫_{x'}∫_s F₁ (ins p s v x') · (∂_{p.1,j}G) (ins p u v x') ,

and the complex integral of a product of real factors is the complexification of the real integral
(`imgFibreSlotReal_eq_cplx`).  Hence, with

    A_j := ∫_{x'}∫_s F₁ (ins p s v x') · (∂_{p.1,j}G) (ins p u v x') ,

one has `∑_j ‖∂_{u,j} imgFibreC‖² = (ℓ⁻³)² ∑_j A_j²`, and the *pointwise-in-`j`*
Cauchy–Schwarz inequality for the iterated integral over the product of the two compact boxes
(`sq_integral_boxPiSet_boxL_le`) gives `A_j² ≤ imgFibreMF ℓ p F₁ v · B_j` with
`B_j = ∫∫ (∂_{p.1,j}G)(ins p u v x')²`.  Summing and using the linearity of the iterated integral
in the finite index `j` (`sum_integral_boxPiSet_boxL`) gives `∑_j B_j = imgFibreDG ℓ p G u`: the
density `imgFibreDG` fills the **dummy** `p.2`-slot with the integration variable `s`, and the
hypothesis `hGind` (invariance of `G` under writes to the slot `p.2`) is exactly what makes the
`p.1`-slot derivative insensitive to that slot (`fderiv_update_p2_eq`), so the `v`-version `B_j`
equals the `s`-version.  Finally `(ℓ⁻³)² = ℓ⁻⁶`.

`sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "boxL" => Work.BoseK15.corpusBox.boxL

/-- **The `p.1`-slot derivative of `G` is insensitive to the value in the slot `p.2`**, given the
`p.2`-invariance hypothesis `hGind`.  This is the identity that makes the density `imgFibreDG`
(whose `p.2`-slot carries the integration dummy `s`) compute the same quantity as the frozen-`v`
version occurring in `imgFibreC_fderiv_slot`. -/
theorem fderiv_slotDirVec_insertCoord2_update {n : ℕ} {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {G : Submission.BoseGases.X n → ℝ} (hGd : Differentiable ℝ G)
    (hGind : ∀ (x : Submission.BoseGases.X n) (t : E3), G (Function.update x p.2 t) = G x)
    (u v s : E3) (x' : pairFib23 n p → E3) (j : Fin 3) :
    fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)
      = fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j) := by
  have hupd : insertCoord2 p u v x' = Function.update (insertCoord2 p u s x') p.2 v := by
    funext k
    rw [insertCoord2_eq, insertCoord2_eq, Function.update_apply]
    dsimp only
    by_cases hk2 : k = p.2
    · rw [dif_neg (fun h : k = p.1 => hp (h.symm.trans hk2)), dif_pos hk2, if_pos hk2]
    · rw [if_neg hk2]
      by_cases hk1 : k = p.1
      · rw [dif_pos hk1, dif_pos hk1]
      · rw [dif_neg hk1, dif_neg hk2, dif_neg hk1, dif_neg hk2]
  rw [hupd]
  exact fderiv_update_p2_eq hp hGd hGind _ _ j

theorem imgFibreC_fderiv_normSq_le {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n}
    (hp : p.1 ≠ p.2) {F₁ G : Submission.BoseGases.X n → ℝ}
    (hF₁ : ContDiff ℝ (⊤ : ℕ∞) F₁) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGind : ∀ (x : Submission.BoseGases.X n) (t : EuclideanSpace ℝ (Fin 3)),
      G (Function.update x p.2 t) = G x)
    (u v : EuclideanSpace ℝ (Fin 3)) :
    ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => Work.BoseBoxFock.imgFibreC ℓ p F₁ G w' v) u
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      ≤ (ℓ ^ 6)⁻¹ * (Work.BoseBoxFock.imgFibreMF ℓ p F₁ v
          * Work.BoseBoxFock.imgFibreDG ℓ p G u) := by
  classical
  -- **(1)** Each directional derivative is the complexification of a real double integral.
  have hnorm : ∀ j : Fin 3,
      ‖fderiv ℝ (fun w' => imgFibreC ℓ p F₁ G w' v) u
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        = ((ℓ ^ 3)⁻¹) ^ 2
          * (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
              F₁ (insertCoord2 p s v x')
                * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2 := by
    intro j
    have hderiv : fderiv ℝ (fun w' => imgFibreC ℓ p F₁ G w' v) u
        (EuclideanSpace.single j (1 : ℝ))
        = ((((ℓ ^ 3)⁻¹) * (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
              F₁ (insertCoord2 p s v x')
                * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) : ℝ) : ℂ) := by
      rw [imgFibreC_fderiv_slot hℓ hp hF₁ hG u v j,
        ← imgFibreSlotReal_eq_cplx ℓ p F₁ G u v j]
      rw [Complex.ofReal_mul]
    rw [hderiv, Complex.sq_norm, Complex.normSq_ofReal]
    ring
  -- **(2)** Cauchy–Schwarz in the `(x', s)`-variables, for each `j`.
  have hCS : ∀ j : Fin 3,
      (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
          F₁ (insertCoord2 p s v x')
            * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2
        ≤ imgFibreMF ℓ p F₁ v
          * (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
              (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2) := by
    intro j
    have hf : Continuous (fun z : (pairFib23 n p → E3) × E3 =>
        F₁ (insertCoord2 p z.2 v z.1)) :=
      hF₁.continuous.comp
        ((contDiff_insertCoord2_comp p contDiff_snd contDiff_const contDiff_fst).continuous)
    have hg1 : Continuous (fun z : (pairFib23 n p → E3) × E3 =>
        insertCoord2 p u v z.1) :=
      (contDiff_insertCoord2_comp p contDiff_const contDiff_const contDiff_fst).continuous
    have hg2 : Continuous (fun y : Submission.BoseGases.X n =>
        fderiv ℝ G y (slotDirVec p.1 j)) :=
      (hG.continuous_fderiv (by simp)).clm_apply continuous_const
    have hcs := sq_integral_boxPiSet_boxL_le
      (ι := pairFib23 n p) hℓ hf (hg2.comp hg1)
    have hMF : (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
        (F₁ (insertCoord2 p s v x')) ^ 2) = imgFibreMF ℓ p F₁ v := rfl
    simp only [] at hcs
    rw [hMF] at hcs
    exact hcs
  -- **(3)** Linearising the finite sum over `j` under the two box integrals; the `p.2`-slot of
  -- `imgFibreDG` carries the dummy `s`, which the `p.2`-invariance of `G` permits.
  have hBeq : (∑ j : Fin 3, ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
        (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
      = imgFibreDG ℓ p G u := by
    have hGd : Differentiable ℝ G := hG.differentiable (by simp)
    have hpoint : ∀ j : Fin 3,
        (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
            (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
        = (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
            (fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j)) ^ 2) := by
      intro j
      refine integral_congr_ae (Filter.Eventually.of_forall fun x' => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
      rw [fderiv_slotDirVec_insertCoord2_update hp hGd hGind u v s x' j]
    have hsum_eq : (∑ j : Fin 3, ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
          (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
        = ∑ j : Fin 3, ∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
            (fderiv ℝ G (insertCoord2 p u s x') (slotDirVec p.1 j)) ^ 2 :=
      Finset.sum_congr rfl fun j _ => hpoint j
    rw [hsum_eq]
    have hcont : ∀ j : Fin 3, Continuous (fun z : (pairFib23 n p → E3) × E3 =>
        (fderiv ℝ G (insertCoord2 p u z.2 z.1) (slotDirVec p.1 j)) ^ 2) := by
      intro j
      have hg1 : Continuous (fun z : (pairFib23 n p → E3) × E3 =>
          insertCoord2 p u z.2 z.1) :=
        (contDiff_insertCoord2_comp p contDiff_const contDiff_snd contDiff_fst).continuous
      have hg2 : Continuous (fun y : Submission.BoseGases.X n =>
          fderiv ℝ G y (slotDirVec p.1 j)) :=
        (hG.continuous_fderiv (by simp)).clm_apply continuous_const
      exact ((hg2.comp hg1).pow 2)
    have h := sum_integral_boxPiSet_boxL (ι := pairFib23 n p) hℓ hcont
    simpa only [imgFibreDG] using h
  have hsum : (∑ j : Fin 3, (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
        F₁ (insertCoord2 p s v x')
          * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
      ≤ imgFibreMF ℓ p F₁ v * imgFibreDG ℓ p G u := by
    calc (∑ j : Fin 3, (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
          F₁ (insertCoord2 p s v x')
            * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2)
        ≤ ∑ j : Fin 3, imgFibreMF ℓ p F₁ v
            * (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
                (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2) :=
          Finset.sum_le_sum fun j _ => hCS j
      _ = imgFibreMF ℓ p F₁ v
            * ∑ j : Fin 3, (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
                (fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2) :=
          (Finset.mul_sum Finset.univ _ _).symm
      _ = imgFibreMF ℓ p F₁ v * imgFibreDG ℓ p G u := by rw [hBeq]
  -- **(4)** The scalar bookkeeping `(ℓ⁻³)² = ℓ⁻⁶`.
  have hc : ((ℓ ^ 3)⁻¹) ^ 2 = (ℓ ^ 6)⁻¹ := by
    rw [inv_pow]
    congr 1
    ring
  calc ∑ j : Fin 3, ‖fderiv ℝ (fun w' => imgFibreC ℓ p F₁ G w' v) u
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
      = ∑ j : Fin 3, ((ℓ ^ 3)⁻¹) ^ 2
          * (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
              F₁ (insertCoord2 p s v x')
                * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2 :=
        Finset.sum_congr rfl fun j _ => hnorm j
    _ = ((ℓ ^ 3)⁻¹) ^ 2
          * ∑ j : Fin 3, (∫ x' in boxPiSet (pairFib23 n p) ℓ, ∫ s in boxL ℓ,
              F₁ (insertCoord2 p s v x')
                * fderiv ℝ G (insertCoord2 p u v x') (slotDirVec p.1 j)) ^ 2 :=
        (Finset.mul_sum Finset.univ _ _).symm
    _ ≤ ((ℓ ^ 3)⁻¹) ^ 2 * (imgFibreMF ℓ p F₁ v * imgFibreDG ℓ p G u) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (ℓ ^ 6)⁻¹ * (imgFibreMF ℓ p F₁ v * imgFibreDG ℓ p G u) := by rw [hc]

end Work.BoseBoxFock
