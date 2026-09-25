import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.norm_fderiv_le_of_CVBound
import Submission.Work.NN.Newton.Defect.norm_fderiv_sub_le_of_CVBound

namespace Work.NN.Newton.Defect

open Set

/-!
# `C^{0,α}` bound for the field `z ↦ λ_l((DA_z X_z) Y)` with `X` only `C^{0,α}`

Given a `C^{1,α}`-small perturbation `A` (`CVBound A α a P`, i.e. every coefficient
`z ↦ A z w j` (`‖w‖ ≤ 1`, `j : Fin n`) has `holderNorm 1 α ≤ ofReal a` on the polydisc
`P = polydiscR n r`) and a *vector field* `X` which is only `C^{0,α}`-small
(`VecHolder X α a P`), the function

  `z ↦ λ_l((DA_z X_z) Y)`

is `C^{0,α}(P)` of norm at most `4 a²` for every fixed `‖Y‖ ≤ 1`.

The proof has three ingredients, all of them elementary:

* `holderNorm 0 α f P = sup_P ‖f‖ + [f]_{0,α;P}`, so it suffices to bound the two pieces
  (`holderNorm_zero_le_of_pointwise`);
* `‖fderiv ℝ A z‖ ≤ a` and `‖fderiv ℝ A z - fderiv ℝ A z'‖ ≤ a ‖z - z'‖^α` on `P`, which
  `CVBound` gives coordinate by coordinate (`norm_fderiv_le_of_CVBound`,
  `norm_fderiv_sub_le_of_CVBound`), using that the polydisc is open so that the `within`
  derivatives of `holderNorm` are the genuine ones;
* the bilinear splitting
  `(DA_z X_z)Y - (DA_{z'} X_{z'})Y = ((DA_z - DA_{z'}) X_z)Y + (DA_{z'}(X_z - X_{z'}))Y`,
  bounded by `a·a·‖Y‖·‖z-z'‖^α` and `a·a·‖z-z'‖^α·‖Y‖` respectively.
-/

/-- `holderNorm 0 α f Ω ≤ ofReal A + ofReal B` from a sup bound `A` and an `α`-seminorm bound `B`.

(The two terms of `holderNorm 0 α` are the sup of `‖f‖` and the `α`-Hölder seminorm of `f`.) -/
lemma holderNorm_zero_le_of_pointwise {n : ℕ} {α : ℝ} {Ω : Set (Work.NN.Core.Cn n)}
    {f : Work.NN.Core.Cn n → ℂ} {A B : ℝ} (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (h1 : ∀ z ∈ Ω, ‖f z‖ ≤ A) (h2 : ∀ z ∈ Ω, ∀ z' ∈ Ω, ‖f z - f z'‖ ≤ B * ‖z - z'‖ ^ α) :
    Work.CR.Flat.holderNorm 0 α f Ω ≤ ENNReal.ofReal A + ENNReal.ofReal B := by
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
  refine add_le_add ?_ ?_
  · refine iSup₂_le fun z hz => ?_
    exact ENNReal.ofReal_le_ofReal (by simpa using h1 z hz)
  · refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hne => ?_
    rw [show ‖iteratedFDerivWithin ℝ 0 f Ω z - iteratedFDerivWithin ℝ 0 f Ω z'‖
        = ‖f z - f z'‖ from by
      simpa [dist_eq_norm] using dist_iteratedFDerivWithin_zero (𝕜 := ℝ) f Ω z f Ω z']
    by_cases h0 : z = z'
    · subst h0; simp
    · have hpos : 0 < ‖z - z'‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h0)) α
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_iff₀ hpos]
      exact h2 z hz z' hz'

theorem holderNorm_LD_field_fixed {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hAc : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r))
    {X : Work.NN.Core.Cn n → Work.NN.Core.Cn n}
    (hX : Work.NN.Final.VecHolder X α a (Work.NN.Newton.polydiscR n r))
    {Y : Work.NN.Core.Cn n} (hY : ‖Y‖ ≤ 1) (l : Fin n) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y))
        (Work.NN.Newton.polydiscR n r)
      ≤ ENNReal.ofReal (4 * a ^ 2) := by
  have ha2 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  have h2a2 : (0 : ℝ) ≤ 2 * a ^ 2 := by positivity
  obtain ⟨hXsup, hXhol⟩ := hX
  have hB1 : ∀ z ∈ Work.NN.Newton.polydiscR n r, ‖fderiv ℝ A z‖ ≤ a :=
    norm_fderiv_le_of_CVBound A ha0 hAc hA
  have hB2 : ∀ z ∈ Work.NN.Newton.polydiscR n r, ∀ z' ∈ Work.NN.Newton.polydiscR n r,
      ‖fderiv ℝ A z - fderiv ℝ A z'‖ ≤ a * ‖z - z'‖ ^ α :=
    norm_fderiv_sub_le_of_CVBound A ha0 hAc hA
  -- the sup bound `a ^ 2`
  have h1 : ∀ z ∈ Work.NN.Newton.polydiscR n r,
      ‖Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y)‖ ≤ a ^ 2 := by
    intro z hz
    have hz1 : ‖fderiv ℝ A z‖ ≤ a := hB1 z hz
    have hzX : ‖X z‖ ≤ a := hXsup z hz
    have hle3 : ‖Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y)‖
        ≤ ‖(fderiv ℝ A z (X z)) Y‖ := by
      simpa [Work.NN.Newton.lamC_apply] using norm_le_pi_norm ((fderiv ℝ A z (X z)) Y) l
    calc ‖Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y)‖
        ≤ ‖(fderiv ℝ A z (X z)) Y‖ := hle3
      _ ≤ ‖fderiv ℝ A z (X z)‖ * ‖Y‖ := (fderiv ℝ A z (X z)).le_opNorm Y
      _ ≤ (‖fderiv ℝ A z‖ * ‖X z‖) * ‖Y‖ :=
            mul_le_mul_of_nonneg_right ((fderiv ℝ A z).le_opNorm (X z)) (norm_nonneg _)
      _ ≤ (a * a) * 1 := by
            refine mul_le_mul ?_ hY (norm_nonneg _) ?_
            · exact mul_le_mul hz1 hzX (norm_nonneg _) ha0
            · exact mul_nonneg ha0 ha0
      _ = a ^ 2 := by ring
  -- the `α`-seminorm bound `2 a ^ 2`
  have h2 : ∀ z ∈ Work.NN.Newton.polydiscR n r, ∀ z' ∈ Work.NN.Newton.polydiscR n r,
      ‖Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y)
        - Work.NN.Newton.lamC l ((fderiv ℝ A z' (X z')) Y)‖ ≤ 2 * a ^ 2 * ‖z - z'‖ ^ α := by
    intro z hz z' hz'
    have hz1' : ‖fderiv ℝ A z'‖ ≤ a := hB1 z' hz'
    have hC : ‖fderiv ℝ A z - fderiv ℝ A z'‖ ≤ a * ‖z - z'‖ ^ α := hB2 z hz z' hz'
    have hXz : ‖X z‖ ≤ a := hXsup z hz
    have hXzz' : ‖X z - X z'‖ ≤ a * ‖z - z'‖ ^ α := hXhol z hz z' hz'
    have hD : (0 : ℝ) ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hF : Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y)
        - Work.NN.Newton.lamC l ((fderiv ℝ A z' (X z')) Y)
        = Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y - (fderiv ℝ A z' (X z')) Y) :=
      (map_sub (Work.NN.Newton.lamC l) _ _).symm
    have hid : (fderiv ℝ A z (X z)) Y - (fderiv ℝ A z' (X z')) Y
        = ((fderiv ℝ A z - fderiv ℝ A z') (X z)) Y
          + (fderiv ℝ A z' (X z - X z')) Y := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]
      abel
    have hb1 : ‖((fderiv ℝ A z - fderiv ℝ A z') (X z)) Y‖ ≤ (a * ‖z - z'‖ ^ α) * a := by
      calc ‖((fderiv ℝ A z - fderiv ℝ A z') (X z)) Y‖
          ≤ ‖(fderiv ℝ A z - fderiv ℝ A z') (X z)‖ * ‖Y‖ :=
              ((fderiv ℝ A z - fderiv ℝ A z') (X z)).le_opNorm Y
        _ ≤ (‖fderiv ℝ A z - fderiv ℝ A z'‖ * ‖X z‖) * ‖Y‖ :=
              mul_le_mul_of_nonneg_right ((fderiv ℝ A z - fderiv ℝ A z').le_opNorm (X z))
                (norm_nonneg _)
        _ ≤ ((a * ‖z - z'‖ ^ α) * a) * 1 := by
              refine mul_le_mul ?_ hY (norm_nonneg _) ?_
              · exact mul_le_mul hC hXz (norm_nonneg _) (mul_nonneg ha0 hD)
              · exact mul_nonneg (mul_nonneg ha0 hD) ha0
        _ = (a * ‖z - z'‖ ^ α) * a := by ring
    have hb2 : ‖(fderiv ℝ A z' (X z - X z')) Y‖ ≤ a * (a * ‖z - z'‖ ^ α) := by
      calc ‖(fderiv ℝ A z' (X z - X z')) Y‖
          ≤ ‖fderiv ℝ A z' (X z - X z')‖ * ‖Y‖ := (fderiv ℝ A z' (X z - X z')).le_opNorm Y
        _ ≤ (‖fderiv ℝ A z'‖ * ‖X z - X z'‖) * ‖Y‖ :=
              mul_le_mul_of_nonneg_right ((fderiv ℝ A z').le_opNorm (X z - X z'))
                (norm_nonneg _)
        _ ≤ (a * (a * ‖z - z'‖ ^ α)) * 1 := by
              refine mul_le_mul ?_ hY (norm_nonneg _) ?_
              · exact mul_le_mul hz1' hXzz' (norm_nonneg _) ha0
              · exact mul_nonneg ha0 (mul_nonneg ha0 hD)
        _ = a * (a * ‖z - z'‖ ^ α) := by ring
    have hmain : ‖(fderiv ℝ A z (X z)) Y - (fderiv ℝ A z' (X z')) Y‖
        ≤ (a * ‖z - z'‖ ^ α) * a + a * (a * ‖z - z'‖ ^ α) := by
      rw [hid]
      exact le_trans (norm_add_le _ _) (add_le_add hb1 hb2)
    calc ‖Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y)
          - Work.NN.Newton.lamC l ((fderiv ℝ A z' (X z')) Y)‖
        = ‖Work.NN.Newton.lamC l ((fderiv ℝ A z (X z)) Y - (fderiv ℝ A z' (X z')) Y)‖ := by
            rw [hF]
      _ ≤ ‖(fderiv ℝ A z (X z)) Y - (fderiv ℝ A z' (X z')) Y‖ := by
            simpa [Work.NN.Newton.lamC_apply] using
              norm_le_pi_norm ((fderiv ℝ A z (X z)) Y - (fderiv ℝ A z' (X z')) Y) l
      _ ≤ (a * ‖z - z'‖ ^ α) * a + a * (a * ‖z - z'‖ ^ α) := hmain
      _ = 2 * a ^ 2 * ‖z - z'‖ ^ α := by ring
  refine le_trans (holderNorm_zero_le_of_pointwise ha2 h2a2 h1 h2) ?_
  rw [← ENNReal.ofReal_add ha2 h2a2]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

end Work.NN.Newton.Defect
