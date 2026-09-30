import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.foldTheta_injOn
import Submission.Work.FoldInst.foldPsi_continuousOn
import Submission.Work.FoldInst.Qbar_geometry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chart height is bounded below, uniformly over the Voronoi pieces

The fold chart of the class `i` is `foldTheta i r = coordPerm i ∘ mobiusKlein (N_F D_r)`; its
coordinate `3` is the *height* coordinate of the upper half space model (`coordPerm` fixes the
height).  We prove that there is a single `δ > 0` such that every point of every Voronoi piece
`Dvor i r` has chart height at least `δ`.

The proof has two ingredients.

* The height of `foldTheta i r y` is *independent of `r`*: because the developing matrix `D_r`
  only differs from `N_F` by the sign matrix `R_{ε_r}`, which fixes the height coefficients,
  one has `(foldTheta i r y) 3 = (mobiusKlein (N_F) (act k_r y)) 3` (`foldTheta_three_eq`).
* For each matrix `N_F` (`i : Fin 98`) the function `z ↦ (mobiusKlein (N_F) z) 3` is continuous
  and strictly positive on the compact set `Q̄`
  (`continuousOn_mobiusKlein`, `mobiusKlein_mem`), hence bounded below by a positive constant on
  `Q̄`; taking the minimum over the finitely many `i` gives the uniform `δ`.
-/

namespace Work.FoldInst

open Matrix
open scoped Matrix

/-- The coordinate permutation `coordPerm` fixes the height coordinate: `foldTau i` fixes `3` and
is bijective. -/
theorem coordPerm_three (i : Fin 98) (y : E4) : coordPerm i y 3 = y 3 := by
  have : Function.invFun (foldTau i) 3 = 3 := by
    have h := Function.leftInverse_invFun (foldTau_bijective i).1 3
    rwa [foldTau_three] at h
  rw [coordPerm_apply, this]

/-- The height coordinate of `mobiusKlein M y` is `√(1−‖y‖²)` divided by the height difference
`(M·(y,1))₄ − (M·(y,1))₃` of the image ray.  This is the general form of `mobiusKlein_height`. -/
theorem mobiusKlein_three_eq (M : Matrix (Fin 5) (Fin 5) ℝ) (y : E4) :
    (Work.HypModel.mobiusKlein M y) 3 =
      Real.sqrt (1 - ‖y‖ ^ 2) *
        ((M *ᵥ Work.HypModel.ray y) 4 - (M *ᵥ Work.HypModel.ray y) 3)⁻¹ := by
  simp only [Work.HypModel.mobiusKlein, Work.HypModel.hypOfKlein, Matrix.mulVec_smul]
  rw [Work.HypModel.uhsOfHyp_apply_three]
  rw [show ((Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • (M *ᵥ Work.HypModel.ray y)) 4
        - ((Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • (M *ᵥ Work.HypModel.ray y)) 3
        = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ *
          ((M *ᵥ Work.HypModel.ray y) 4 - (M *ᵥ Work.HypModel.ray y) 3) from by
      simp only [Pi.smul_apply, smul_eq_mul]; ring]
  rw [mul_inv, inv_inv]

/-- **The height of the fold chart does not depend on the representative `r`.**  The chart height
`(foldTheta i r y) 3` equals `(mobiusKlein N_F (act k_r y)) 3`: the developing matrix `D_r` and
`N_F` differ by the sign matrix `R_{ε_r}`, which fixes the coefficients `3` and `4` entering the
height. -/
theorem foldTheta_three_eq (i : Fin 98) (r : Fin (foldCodim i) → Bool) (y : E4) :
    (foldTheta i r y) 3 =
      (Work.HypModel.mobiusKlein (foldNr i) (act (toG (foldKr i r)) y)) 3 := by
  rw [show (foldTheta i r y) 3 =
      (Work.HypModel.mobiusKlein (foldNr i * foldDrR i r) y) 3 from by
    simp only [foldTheta]; rw [coordPerm_three]]
  rw [mobiusKlein_three_eq (foldNr i * foldDrR i r) y, mobiusKlein_height i r y]
  have hV : (foldNr i * foldDrR i r) *ᵥ Work.HypModel.ray y
      = reflEr (foldEr i r) *ᵥ
        (foldNr i *ᵥ Work.HypModel.ray (act (toG (foldKr i r)) y)) := by
    rw [← foldKrR_mulVec_ray_act i r y, Matrix.mulVec_mulVec, foldNr_mul_D_mul_K i r,
      ← Matrix.mulVec_mulVec]
  have hkey : ((foldNr i * foldDrR i r) *ᵥ Work.HypModel.ray y) 4
        - ((foldNr i * foldDrR i r) *ᵥ Work.HypModel.ray y) 3
      = (foldNr i *ᵥ Work.HypModel.ray (act (toG (foldKr i r)) y)) 4
        - (foldNr i *ᵥ Work.HypModel.ray (act (toG (foldKr i r)) y)) 3 := by
    rw [hV, reflEr_mulVec_four, reflEr_mulVec_three]
  rw [hkey]

/-- **A uniform lower bound for the Klein height of the normalisations `N_F`.**  For the finitely
many classes `i`, the continuous function `z ↦ (mobiusKlein (foldNr i) z) 3` is strictly positive
on the compact `Q̄`, hence has a positive minimum there; the minimum over the finitely many `i` is
the announced `δ`. -/
theorem exists_pos_le_foldtheta_height_aux :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (i : Fin 98) (z : E4), z ∈ Qbar →
      δ ≤ (Work.HypModel.mobiusKlein (foldNr i) z) 3 := by
  have hper : ∀ i : Fin 98, ∃ d : ℝ, 0 < d ∧
      ∀ z ∈ Qbar, d ≤ (Work.HypModel.mobiusKlein (foldNr i) z) 3 := by
    intro i
    have hcont : ContinuousOn (fun z : E4 => (Work.HypModel.mobiusKlein (foldNr i) z) 3) Qbar :=
      ((PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3).comp_continuousOn
        (continuousOn_mobiusKlein (FoldThetaOrthantAux.foldNr_isLorentz i))).mono
        Qbar_subset_ball
    obtain ⟨x0, hx0, hmin⟩ := IsCompact.exists_isMinOn Qbar_geometry.1 Qbar_nonempty hcont
    refine ⟨(Work.HypModel.mobiusKlein (foldNr i) x0) 3, ?_, ?_⟩
    · exact Work.HypModel.mobiusKlein_mem (FoldThetaOrthantAux.foldNr_isLorentz i)
        (Qbar_subset_ball hx0)
    · intro z hz
      exact (isMinOn_iff.mp hmin) z hz
  choose d hd using hper
  have hne : (Finset.univ : Finset (Fin 98)).Nonempty := Finset.univ_nonempty
  refine ⟨(Finset.univ : Finset (Fin 98)).inf' hne d, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro i _
    exact (hd i).1
  · intro i z hz
    exact le_trans (Finset.inf'_le d (Finset.mem_univ i)) ((hd i).2 z hz)

theorem exists_pos_le_foldTheta_height :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (i : Fin 98) (r : Fin (foldCodim i) → Bool) (x : Xbar),
      x ∈ Dvor i r → δ ≤ (foldTheta i r x.2.1) 3 := by
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_foldtheta_height_aux
  refine ⟨δ, hδpos, ?_⟩
  intro i r x _
  rw [foldTheta_three_eq i r x.2.1]
  exact hδle i (act (toG (foldKr i r)) x.2.1)
    ((Qbar_act (toG (foldKr i r)) x.2.1).mpr x.2.2)

end Work.FoldInst
