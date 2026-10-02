import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.cutoff_props
import Submission.Work.FBif.antipoly_wirtinger
import Submission.Work.FBif.norm_deriv_glueMap

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FBif.badSet_locallyFinite`

The glued map `F = glueMap c q ε (cutoff c)` of `Submission/Work/FBif/Glue.lean` is `C¹` and
satisfies, at every point `z`,

* `‖∂F z‖ ≤ ε · ‖q z‖ · Kχ`   (`glue_wirtinger`, `hKχ`),
* `‖∂̄F z‖ ≥ 2‖z‖ - ε · (‖q z‖ · Kχ + ‖∂̄q z‖)`   (`norm_deriv_glueMap`).

The second bound is strictly positive on the annulus `‖z‖ ≥ innerRad c`, and strictly larger
than the first one there precisely under the smallness assumption
`ε · (Q' + 2 · Q · Kχ) < 2 · innerRad c`: indeed on `innerRad c ≤ ‖z‖ ≤ cutRad c` we have
`‖q z‖ ≤ Q` and `‖∂̄q z‖ ≤ Q'`, so that

`‖∂F z‖ ≤ ε·Q·Kχ < 2·innerRad c - ε·(Q·Kχ + Q') ≤ ‖∂̄F z‖`.

Outside the cut ball `F` coincides with `T_c`, where `∂F = 0` and `∂̄F = 2 z̄ ≠ 0`.  Inside the
inner ball `F` coincides with the perturbation `perturb c q ε`, for which `∂F = 0` (an
antipolynomial is antiholomorphic) and

`∂̄F z = 2 z̄ + ε · P'(z̄)`.

Consequently the exceptional set `badSet F`, where `F` fails to be orientation reversing
(`‖∂F z‖ ≥ ‖∂̄F z‖`), is contained in the zero set of the *nonzero* polynomial
`2X + ε·P'` (nonvanishing is exactly the hypothesis `hQ0`), hence is **finite**.  A finite set
has an empty punctured neighbourhood at every point, which is the statement below. -/

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The Wirtinger derivatives of the perturbation -/

/-- The perturbation `perturb c q ε = T_c + ε·q` of an antipolynomial is antiholomorphic:
`∂(perturb) = 0`. -/
theorem dz_perturb (c : ℂ) {q : ℂ → ℂ} {P : Polynomial ℂ}
    (hP : ∀ z : ℂ, q z = P.eval (star z)) (ε : ℝ) (z : ℂ) :
    Work.MRMT.dz (perturb c q ε) z = 0 := by
  obtain ⟨hqc, hdzq, -⟩ := antipoly_wirtinger hP
  obtain ⟨hTc, hdzT, -⟩ := tantibar_wirtinger c
  have hTd : DifferentiableAt ℝ (Tantibar c) z :=
    (hTc.differentiable (by norm_num)).differentiableAt
  have hqd : DifferentiableAt ℝ q z := (hqc.differentiable (by norm_num)).differentiableAt
  have hg : DifferentiableAt ℝ (fun w : ℂ => (ε : ℂ) * q w) z := hqd.const_mul _
  have heq : perturb c q ε = fun w : ℂ => Tantibar c w + (ε : ℂ) * q w := rfl
  rw [heq, Work.MRMT.QC.dz_add_of_diff hTd hg, hdzT z, dz_const_mul_of_diff hqd, hdzq z]
  ring

/-- `∂̄(perturb c q ε) z = 2 z̄ + ε · P'(z̄)`. -/
theorem dzbar_perturb (c : ℂ) {q : ℂ → ℂ} {P : Polynomial ℂ}
    (hP : ∀ z : ℂ, q z = P.eval (star z)) (ε : ℝ) (z : ℂ) :
    Work.MRMT.dzbar (perturb c q ε) z = 2 * star z + (ε : ℂ) * P.derivative.eval (star z) := by
  obtain ⟨hqc, -, hdzbarq⟩ := antipoly_wirtinger hP
  obtain ⟨hTc, -, hdzbarT⟩ := tantibar_wirtinger c
  have hTd : DifferentiableAt ℝ (Tantibar c) z :=
    (hTc.differentiable (by norm_num)).differentiableAt
  have hqd : DifferentiableAt ℝ q z := (hqc.differentiable (by norm_num)).differentiableAt
  have hg : DifferentiableAt ℝ (fun w : ℂ => (ε : ℂ) * q w) z := hqd.const_mul _
  have heq : perturb c q ε = fun w : ℂ => Tantibar c w + (ε : ℂ) * q w := rfl
  rw [heq, Work.MRMT.QC.dzbar_add_of_diff hTd hg, hdzbarT z,
    dzbar_const_mul_of_diff hqd, hdzbarq z]

/-! ## The exceptional set of the glued map is finite -/

theorem badSet_locallyFinite (c : ℂ) {q : ℂ → ℂ} {P : Polynomial ℂ}
    (hP : ∀ z : ℂ, q z = P.eval (star z)) {ε : ℝ} (hε : 0 < ε)
    (hQ0 : ¬ (Polynomial.C 2 * Polynomial.X + Polynomial.C (ε : ℂ) * P.derivative = 0))
    {Q Kχ Q' : ℝ} (hQ : ∀ z : ℂ, ‖z‖ ≤ Work.FBif.cutRad c → ‖q z‖ ≤ Q)
    (hKχ : ∀ z : ℂ, ‖Work.MRMT.dz (Work.FBif.realCoe (Work.FBif.cutoff c)) z‖ ≤ Kχ)
    (hQ' : ∀ z : ℂ, ‖z‖ ≤ Work.FBif.cutRad c → ‖Work.MRMT.dzbar q z‖ ≤ Q')
    (hsmall : ε * (Q' + 2 * Q * Kχ) < 2 * Work.FBif.innerRad c) :
    ∀ z : ℂ, Filter.Eventually (fun w : ℂ =>
      w ∉ Work.FBif.badSet (Work.FBif.glueMap c q ε (Work.FBif.cutoff c)))
      (nhdsWithin z {z}ᶜ) := by
  have hq : Antipoly q := ⟨P, hP⟩
  have hχ : ContDiff ℝ 1 (cutoff c) := (cutoff_props c).1
  have hχrange : ∀ z : ℂ, 0 ≤ cutoff c z ∧ cutoff c z ≤ 1 := (cutoff_props c).2.2.2.1
  have hcutpos : 0 < cutRad c := cutoffAux.cutRad_pos c
  have hQ0' : 0 ≤ Q := le_trans (norm_nonneg _) (hQ 0 (le_trans (by simp) (le_of_lt hcutpos)))
  have hQ'0 : 0 ≤ Q' := le_trans (norm_nonneg _) (hQ' 0 (le_trans (by simp) (le_of_lt hcutpos)))
  have hKχ0 : 0 ≤ Kχ := le_trans (norm_nonneg _) (hKχ 0)
  have heps : ‖(ε : ℂ)‖ = ε := by
    have h : ‖(ε : ℂ)‖ = |ε| := RCLike.norm_ofReal ε
    rw [h, abs_of_pos hε]
  -- There, the glued map is the model `T_c`, so `∂F = 0` and `∂̄F = 2 z̄ ≠ 0`.
  have houter : ∀ w : ℂ, cutRad c < ‖w‖ → w ∉ badSet (glueMap c q ε (cutoff c)) := by
    intro w hw
    have hev : glueMap c q ε (cutoff c) =ᶠ[𝓝 w] Tantibar c := by
      filter_upwards [cutoffAux.eventually_cutoff_eq_zero c hw] with u hu
      rw [glueMap_apply, hu]
      norm_num
    have hfd : fderiv ℝ (glueMap c q ε (cutoff c)) w = fderiv ℝ (Tantibar c) w := hev.fderiv_eq
    obtain ⟨-, hdzT, hdzbarT⟩ := tantibar_wirtinger c
    have hdz : Work.MRMT.dz (glueMap c q ε (cutoff c)) w = 0 := by
      rw [show Work.MRMT.dz (glueMap c q ε (cutoff c)) w = Work.MRMT.dz (Tantibar c) w from by
        simp only [Work.MRMT.dz, hfd], hdzT w]
    have hdzb : Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w = 2 * star w := by
      rw [show Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w = Work.MRMT.dzbar (Tantibar c) w from by
        simp only [Work.MRMT.dzbar, hfd], hdzbarT w]
    have hlt : ‖Work.MRMT.dz (glueMap c q ε (cutoff c)) w‖ <
        ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w‖ := by
      rw [hdz, hdzb, norm_zero, norm_mul, norm_star, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have : 0 < ‖w‖ := lt_trans hcutpos hw
      linarith
    intro hmem
    exact not_le.mpr hlt hmem
  -- The annulus `innerRad c ≤ ‖z‖ ≤ cutRad c`: the explicit estimate.
  have hmiddle : ∀ w : ℂ, innerRad c ≤ ‖w‖ → ‖w‖ ≤ cutRad c →
      w ∉ badSet (glueMap c q ε (cutoff c)) := by
    intro w hw1 hw2
    have hcw : ‖((cutoff c w : ℝ) : ℂ)‖ = cutoff c w := by
      have h : ‖((cutoff c w : ℝ) : ℂ)‖ = |cutoff c w| := RCLike.norm_ofReal (cutoff c w)
      rw [h, abs_of_nonneg (hχrange w).1]
    have hwirt := glue_wirtinger c hq ε hχ w
    have hA : ‖Work.MRMT.dz (glueMap c q ε (cutoff c)) w‖ ≤ ε * Q * Kχ := by
      rw [hwirt.1, norm_mul, norm_mul, heps]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hQ w hw2) (le_of_lt hε)) (hKχ w)
        (norm_nonneg _) (mul_nonneg (le_of_lt hε) hQ0')
    have hB : 2 * innerRad c - ε * Q * Kχ - ε * Q' ≤
        ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w‖ := by
      rw [hwirt.2]
      have h1 : ‖(2 : ℂ) * star w‖ = 2 * ‖w‖ := by
        rw [norm_mul, norm_star, show ‖(2 : ℂ)‖ = 2 by norm_num]
      have h2 : ‖(ε : ℂ) * ((cutoff c w : ℝ) : ℂ) * Work.MRMT.dzbar q w‖ ≤ ε * Q' := by
        rw [norm_mul, norm_mul, hcw, heps]
        calc ε * cutoff c w * ‖Work.MRMT.dzbar q w‖ ≤ ε * 1 * Q' := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left (hχrange w).2 (le_of_lt hε)
              · exact hQ' w hw2
              · exact norm_nonneg _
              · exact mul_nonneg (le_of_lt hε) (by norm_num)
          _ = ε * Q' := by ring
      have h3 : ‖(ε : ℂ) * q w * Work.MRMT.dzbar (realCoe (cutoff c)) w‖ ≤ ε * Q * Kχ := by
        rw [norm_mul, norm_mul, norm_dzbar_realCoe_eq hχ w, heps]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hQ w hw2) (le_of_lt hε)) (hKχ w)
          (norm_nonneg _) (mul_nonneg (le_of_lt hε) hQ0')
      have htri := norm_three_bound ((2 : ℂ) * star w)
        ((ε : ℂ) * ((cutoff c w : ℝ) : ℂ) * Work.MRMT.dzbar q w)
        ((ε : ℂ) * q w * Work.MRMT.dzbar (realCoe (cutoff c)) w)
      rw [h1] at htri
      linarith [htri, h2, h3, hw1]
    have hlt : ‖Work.MRMT.dz (glueMap c q ε (cutoff c)) w‖ <
        ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w‖ := by
      have key : ε * Q * Kχ < 2 * innerRad c - ε * Q * Kχ - ε * Q' := by
        have hexp : ε * (Q' + 2 * Q * Kχ) = ε * Q' + ε * Q * Kχ + ε * Q * Kχ := by ring
        linarith [hsmall, hexp]
      linarith [hA, hB]
    intro hmem
    exact not_le.mpr hlt hmem
  have hfar : ∀ w : ℂ, innerRad c ≤ ‖w‖ → w ∉ badSet (glueMap c q ε (cutoff c)) := by
    intro w hw
    by_cases h : ‖w‖ ≤ cutRad c
    · exact hmiddle w hw h
    · exact houter w (not_le.mp h)
  -- Inside the inner ball the glued map is the perturbation; there `‖∂F‖ = 0`, so membership in
  -- `badSet` forces `∂̄F = 2 z̄ + ε P'(z̄)` to vanish.
  have hzeros : ∀ w : ℂ, w ∈ badSet (glueMap c q ε (cutoff c)) →
      2 * star w + (ε : ℂ) * P.derivative.eval (star w) = 0 := by
    intro w hmem
    by_cases hw : ‖w‖ < innerRad c
    · have hev : glueMap c q ε (cutoff c) =ᶠ[𝓝 w] perturb c q ε := by
        filter_upwards [cutoffAux.eventually_cutoff_eq_one c hw] with u hu
        rw [glueMap_apply, perturb_apply, hu]
        norm_num
      have hfd : fderiv ℝ (glueMap c q ε (cutoff c)) w = fderiv ℝ (perturb c q ε) w :=
        hev.fderiv_eq
      have hdz : Work.MRMT.dz (glueMap c q ε (cutoff c)) w = 0 := by
        rw [show Work.MRMT.dz (glueMap c q ε (cutoff c)) w = Work.MRMT.dz (perturb c q ε) w from by
          simp only [Work.MRMT.dz, hfd], dz_perturb c hP ε w]
      have hdzb : Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w =
          2 * star w + (ε : ℂ) * P.derivative.eval (star w) := by
        rw [show Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w =
            Work.MRMT.dzbar (perturb c q ε) w from by
          simp only [Work.MRMT.dzbar, hfd], dzbar_perturb c hP ε w]
      have hge : ‖Work.MRMT.dz (glueMap c q ε (cutoff c)) w‖ ≥
          ‖Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w‖ := hmem
      rw [hdz, norm_zero] at hge
      have hz : Work.MRMT.dzbar (glueMap c q ε (cutoff c)) w = 0 := norm_le_zero_iff.mp hge
      rw [hdzb] at hz
      exact hz
    · exact absurd hmem (hfar w (not_lt.mp hw))
  -- The zero set of `2X + ε P'` is finite because that polynomial is not the zero polynomial.
  have hSfin : ({w : ℂ | 2 * star w + (ε : ℂ) * P.derivative.eval (star w) = 0}).Finite := by
    have hG0 : Polynomial.C 2 * Polynomial.X + Polynomial.C (ε : ℂ) * P.derivative ≠ 0 := hQ0
    have hT : {u : ℂ |
        (Polynomial.C 2 * Polynomial.X + Polynomial.C (ε : ℂ) * P.derivative).IsRoot u}.Finite :=
      Polynomial.finite_setOfPred_isRoot hG0
    have hpre : (star ⁻¹' {u : ℂ |
        (Polynomial.C 2 * Polynomial.X + Polynomial.C (ε : ℂ) * P.derivative).IsRoot u}).Finite :=
      hT.preimage (star_injective.injOn)
    convert hpre using 1
    ext w
    simp [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul]
  have hbadfin : (badSet (glueMap c q ε (cutoff c))).Finite :=
    hSfin.subset (fun w hw => hzeros w hw)
  -- A finite set has empty punctured neighbourhoods.
  intro z
  have hBfin : (badSet (glueMap c q ε (cutoff c)) \ {z}).Finite :=
    hbadfin.subset Set.sdiff_subset
  have hBclosed : IsClosed (badSet (glueMap c q ε (cutoff c)) \ {z}) := hBfin.isClosed
  have hz : z ∈ (badSet (glueMap c q ε (cutoff c)) \ {z})ᶜ := by simp
  have hmem : (badSet (glueMap c q ε (cutoff c)) \ {z})ᶜ ∈ 𝓝 z :=
    hBclosed.isOpen_compl.mem_nhds hz
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hmem] with w hw hwz
  exact fun hwS => hw ⟨hwS, hwz⟩

end Work.FBif

end
