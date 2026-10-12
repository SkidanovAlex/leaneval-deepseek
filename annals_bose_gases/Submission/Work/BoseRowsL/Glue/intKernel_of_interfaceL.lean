import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.honest_IntKernel_uncond
import Submission.Work.BoseRowsL.Glue.sumDiff_of_interfaceL
import Submission.Work.BoseRowsL.Row2.omegaLatticeRow_of_interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Glue.intKernel_of_interfaceL`

The honest `IntKernel` of FS `lem:EstimateIntegral` at the honest data, **assuming only the
decay-free interface `Work.BoseRowsL.HonestInterfaceL`**.

This is the analogue of `Work.BoseRowsFS.honest_IntKernel_uncond`, with the two decay rows
`|Ŵ₁(p)|(1+‖p‖)² ≤ Cw·a`, `|ĝ(p)|(1+‖p‖)² ≤ Cw·a` replaced by the interface's sup / Lipschitz
rows.  The proof has exactly the shape of `Work.BoseRowsFS.honest_IntKernel`'s body; the rows are

* `Ŵ₁ω(0)` (row 2) — `Work.BoseRowsL.Row2.omegaLatticeRow_of_interface` (heat-kernel torus/free
  comparison, using `H.bndW` and `H.tailL`);
* `W₁ − g₀` (the `sum_diff` row) — `Work.BoseRowsL.Glue.sumDiff_of_interfaceL`
  (the lattice comparison `honest_lattice_sum_diff` plus the cut tail `H.tailL`);
* the four lattice rows — `Work.BoseRowsFS.honest_lattice_rows` (decay-free);
* the `P_H^q` row — `Work.BoseRowsFS.RowSumW1sq_regime` (decay-free);

while the `A`/`B` mode rows come from `Work.BoseRowsFS.honest_A_ge_AB_regime` (at its own
diluteness threshold `t₀`, folded into `ε₀ = min t₀ hthr.εg`), the `τ̃` row from
`honest_tauSm_rows`, and the two sup rows `|Ŵ₁| ≤ 16π a`, `|ĝ| ≤ 8π a` from `H.bndW` /
`chat_g0_abs_le`.  The final assembly is `Work.BoseRowsFS.intKernel_kzEnvAt`.
-/

namespace Work.BoseRowsL.Glue

open scoped Real BigOperators Topology
open MeasureTheory Metric

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem intKernel_of_interfaceL {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hthr : Work.BoseGateFS.GateThresholds v h fc fu R)
    (H : Work.BoseRowsL.HonestInterfaceL R hthr) :
    ∃ ε₀ K₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ hthr.εg ∧ 128 * Real.pi ≤ K₀ ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ), (∀ μ, H.Ng' μ ≤ (HM μ).N) →
      ∀ (μ ρ : ℝ),
        (hvK : Work.BoseB7.FSParamsView
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) →
        0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε₀ → 0 ≤ ρ →
        (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16 →
        Work.BoseB7A.IntKernel K₀ R (Work.BoseRowsFS.honF v h fc fu HM μ)
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
          (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)) := by
  -- ## the rows, each with an absolute constant
  obtain ⟨Cω, hCω, hωrow⟩ := Work.BoseRowsL.Row2.omegaLatticeRow_of_interface (v := v) (h := h)
    (fc := fc) (fu := fu) R hR hav hv_nonneg hvrad hv_supp hthr H
  obtain ⟨Cδ, hCδ, hδrow⟩ := Work.BoseRowsL.Glue.sumDiff_of_interfaceL (v := v) (h := h)
    (fc := fc) (fu := fu) R hR hav hv_nonneg hvrad hv_supp hthr H
  obtain ⟨Kl, hKl, hlrows⟩ := Work.BoseRowsFS.honest_lattice_rows (v := v) (h := h)
    (fc := fc) (fu := fu)
  -- ## the `HM`-independent régime rows, extracted from `hthr.dil` at a mode family that is
  --     large enough for `hthr.Ng`
  let HM0 : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ :=
    fun μ => Classical.choose (Work.BoseBoxFock.exists_honestModes v μ (hthr.Ng μ))
  have hHM0 : ∀ μ : ℝ, (HM0 μ).N = hthr.Ng μ :=
    fun μ => Classical.choose_spec (Work.BoseBoxFock.exists_honestModes v μ (hthr.Ng μ))
  have hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := by
    intro μ hμ hε
    have hd := hthr.dil HM0 (fun μ' => le_of_eq (hHM0 μ').symm) μ hμ hε
    exact ⟨hd.1, hd.2.2.1⟩
  obtain ⟨Cq, hCq, hqrow⟩ := Work.BoseRowsFS.RowSumW1sq_regime (v := v) (h := h)
    (fc := fc) (fu := fu) (R := R) hR hav hv_nonneg hvrad hv_supp hthr.εg hrég
  -- ## the `P_H` rows of `A`, `B`, at their own diluteness threshold `t₀`
  obtain ⟨t₀, ht₀pos, hAreg⟩ := Work.BoseRowsFS.honest_A_ge_AB_regime (v := v) (h := h)
    (fc := fc) (fu := fu) R hR hav hv_nonneg hvrad hv_supp
  -- ## the common threshold and one absolute constant dominating all of them
  set ε₀ : ℝ := min t₀ hthr.εg with hε₀def
  have hε₀pos : 0 < ε₀ := lt_min ht₀pos hthr.pos
  have hε₀g : ε₀ ≤ hthr.εg := min_le_right _ _
  have hε₀t : ε₀ ≤ t₀ := by rw [hε₀def]; exact min_le_left _ _
  set K₀ : ℝ := 128 * Real.pi + H.Cw + Cω + Cδ + Kl + Cq with hK₀def
  have hK128 : 128 * Real.pi ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, H.Cw_nonneg, hCω, hCδ, hKl, hCq]
  have hK16 : 16 * Real.pi ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, H.Cw_nonneg, hCω, hCδ, hKl, hCq]
  have hK8 : 8 * Real.pi ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, H.Cw_nonneg, hCω, hCδ, hKl, hCq]
  have hKωCw : H.Cw ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, hCω, hCδ, hKl, hCq]
  have hKω : Cω ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, H.Cw_nonneg, hCδ, hKl, hCq]
  have hKδ : Cδ ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, H.Cw_nonneg, hCω, hKl, hCq]
  have hKql : Kl ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, H.Cw_nonneg, hCω, hCδ, hCq]
  have hKq : Cq ≤ K₀ := by
    rw [hK₀def]; linarith [Real.pi_pos, H.Cw_nonneg, hCω, hCδ, hKl]
  refine ⟨ε₀, K₀, hε₀pos, hε₀g, hK128, ?_⟩
  intro HM hN μ ρ hvK hμ hε hρ hsc
  -- the honest environment / Fock data of this point
  set F : FockData (Lab (HM μ).N) := Work.BoseRowsFS.honF v h fc fu HM μ with hFdef
  set E : Q3Env (Lab (HM μ).N) := Work.BoseRowsFS.honE v h fc fu HM μ with hEdef
  have hεg : μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg := le_trans hε hε₀g
  have hεt : μ * _root_.BoseGases.a v ^ 3 ≤ t₀ := le_trans hε hε₀t
  have hng' : ∀ μ' : ℝ, hthr.Ng μ' ≤ (HM μ').N := fun μ' => le_trans (H.Ng'_ge μ') (hN μ')
  obtain ⟨h1ℓ, _hR2KH, hRchi, _hdil323, _hKL, _hKH32⟩ := hthr.dil HM hng' μ hμ hεg
  have hview : FSParamsView E := H.fsp HM μ hμ hεg
  have hellpos : 0 < E.ell := by
    rw [hEdef]
    rw [Work.BoseRowsFS.honE_ell v h fc fu HM μ hμ hav]
    exact Work.BoseBoxFock.ellH_pos v μ
  have hKHpos : 0 < E.KH := lt_of_lt_of_le one_pos hview.one_le_KH
  have hX : 0 < E.KH * E.aScat := mul_pos hKHpos hview.a_pos
  -- ### the `Ŵ₁` row, from the interface's sup bound
  have rowW1 : ∀ k : Lab (HM μ).N, |E.W1 k| ≤ K₀ * E.aScat := by
    intro k
    have happ : E.W1 k = uvCut fu (uvRad (ellH v μ) (HM μ).N) (F.kmom k)
        * chat (W1fun v h (ellH v μ)) (F.kmom k) := by
      rw [hEdef, hFdef]
      exact Work.BoseRowsFS.honE_W1_apply v h fc fu HM μ hμ hav k
    rw [happ]
    have hζ : |uvCut fu (uvRad (ellH v μ) (HM μ).N) (F.kmom k)| ≤ 1 := by
      have h0 : 0 ≤ uvCut fu (uvRad (ellH v μ) (HM μ).N) (F.kmom k) :=
        Work.BoseBoxFix.LowCut.nonneg fu _
      have h1 : uvCut fu (uvRad (ellH v μ) (HM μ).N) (F.kmom k) ≤ 1 :=
        Work.BoseBoxFix.LowCut.le_one fu _
      rw [abs_le]
      exact ⟨by linarith, h1⟩
    have hb := H.bndW (ellH v μ) h1ℓ hRchi (F.kmom k)
    calc |uvCut fu (uvRad (ellH v μ) (HM μ).N) (F.kmom k)
          * chat (W1fun v h (ellH v μ)) (F.kmom k)|
        = |uvCut fu (uvRad (ellH v μ) (HM μ).N) (F.kmom k)|
            * |chat (W1fun v h (ellH v μ)) (F.kmom k)| := abs_mul _ _
      _ ≤ 1 * (H.Cw * a v) := mul_le_mul hζ hb (abs_nonneg _) (by norm_num)
      _ = H.Cw * a v := one_mul _
      _ ≤ K₀ * a v := mul_le_mul_of_nonneg_right hKωCw hav.le
      _ = K₀ * E.aScat := by rw [hEdef]; rfl
  -- ### the `ĝ` row (proved, constant `8π`)
  have rowg : ∀ k : Lab (HM μ).N, |chat (g0 v h) (F.kmom k)| ≤ K₀ * E.aScat := by
    intro k
    have hb := Work.BoseRowsFS.chat_g0_abs_le (v := v) (R := R) hR hv_nonneg hvrad hv_supp h
      (F.kmom k)
    calc |chat (g0 v h) (F.kmom k)| ≤ 8 * Real.pi * a v := hb
      _ ≤ K₀ * a v := mul_le_mul_of_nonneg_right hK8 hav.le
      _ = K₀ * E.aScat := by rw [hEdef]; rfl
  -- ### the `A`, `B` rows, from the régime branch of `honest_A_ge_AB`
  have hABrows := hAreg HM μ ρ hvK hμ hRchi hρ
    (by rw [Work.BoseRowsFS.view_t_eq_mu_a3 hvK]; exact hεt) hsc
  have rowA : ∀ k : Lab (HM μ).N, F.PH E.KH E.aScat k → 0 < (KzEnvAt E ρ).A k :=
    hABrows.1
  have rowAB : ∀ k : Lab (HM μ).N, F.PH E.KH E.aScat k →
      2 * |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k := hABrows.2
  -- ### `kmom ≠ 0` on the excited modes
  have rowne : ∀ k ∈ excited (Lab (HM μ).N), F.kmom k ≠ 0 := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hinj := Work.BoseBoxFock.GramLab.kmomLab_injective (ellH v μ)
      (Work.BoseBoxFock.ellH_pos v μ) (HM μ).N
    have hz : kmomLab (ellH v μ) (HM μ).N (0 : Lab (HM μ).N) = 0 := by
      rw [Work.BoseRowsFS.kmomLab_eq, Work.BoseRowsFS.labVec_zero,
        Work.BoseRowsFS.vecZ_zero, smul_zero]
    exact fun hkzero => hk0 (hinj (hkzero.trans hz.symm))
  -- ### the `τ̃` row
  have rowtau : ∀ k : Lab (HM μ).N,
      0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k
        ∧ ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell) :=
    fun k => Work.BoseRowsFS.honest_tauSm_rows (v := v) (h := h) (fc := fc) (fu := fu)
      HM μ hμ hview k
  -- ### the `Ŵ₁ω(0)` row (row 2 of FS §11, from the interface)
  have rowω : |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ excited (Lab (HM μ).N),
          E.W1 k * chat (g0 v h) (F.kmom k) / (2 * ‖F.kmom k‖ ^ 2)|
      ≤ K₀ * E.aScat ^ 2 / E.ell := by
    refine le_trans (hωrow HM hN μ hμ hεg) ?_
    have hX2 : (0 : ℝ) ≤ E.aScat ^ 2 / E.ell := div_nonneg (sq_nonneg _) hellpos.le
    calc Cω * E.aScat ^ 2 / E.ell = Cω * (E.aScat ^ 2 / E.ell) := by ring
      _ ≤ K₀ * (E.aScat ^ 2 / E.ell) := mul_le_mul_of_nonneg_right hKω hX2
      _ = K₀ * E.aScat ^ 2 / E.ell := by ring
  -- ### the four lattice rows
  obtain ⟨rl, r4, r6, r3⟩ := hlrows HM μ hμ hview h1ℓ
  have hfl : (excited (Lab (HM μ).N)).filter (fun k => ¬ F.PH E.KH E.aScat k)
      = (excited (Lab (HM μ).N)).filter
        (fun k => ¬ (1 / (2 * E.KH * E.aScat) ≤ ‖Work.BoseRowsFS.honKmom v HM μ k‖)) := by
    refine Finset.filter_congr (fun k hk => ?_)
    simp only [hFdef, Work.BoseB7.FockData.PH, Work.BoseRowsFS.honF_kmom]
  have hfp : F.PHset E
      = (excited (Lab (HM μ).N)).filter
        (fun k => 1 / (2 * E.KH * E.aScat) ≤ ‖Work.BoseRowsFS.honKmom v HM μ k‖) := by
    rw [Work.BoseB7.FockData.PHset]
    refine Finset.filter_congr (fun k hk => ?_)
    simp only [hFdef, Work.BoseB7.FockData.PH, Work.BoseRowsFS.honF_kmom]
  have hf3 : (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat)
      = (((excited (Lab (HM μ).N)).filter
          (fun k => 1 / (2 * E.KH * E.aScat) ≤ ‖Work.BoseRowsFS.honKmom v HM μ k‖)).filter
          (fun k => ‖Work.BoseRowsFS.honKmom v HM μ k‖ ≤ 1 / E.aScat)) := by
    rw [hfp]
    refine Finset.filter_congr (fun k hk => ?_)
    simp only [hFdef, Work.BoseRowsFS.honF_kmom]
  have rowlow : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (excited (Lab (HM μ).N)).filter (fun k => ¬ F.PH E.KH E.aScat k),
          1 / ‖F.kmom k‖ ^ 2
      ≤ K₀ / (E.KH * E.aScat) := by
    rw [hfl]
    exact le_trans rl (div_le_div_of_nonneg_right hKql hX.le)
  have row4 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 4
      ≤ K₀ * E.KH * E.aScat := by
    rw [hfp]
    rw [show K₀ * E.KH * E.aScat = K₀ * (E.KH * E.aScat) from by ring]
    exact le_trans r4 (mul_le_mul_of_nonneg_right hKql hX.le)
  have row6 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 6
      ≤ K₀ * (E.KH * E.aScat) ^ 3 := by
    rw [hfp]
    exact le_trans r6 (mul_le_mul_of_nonneg_right hKql (by positivity))
  have row3 : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat), 1 / ‖F.kmom k‖ ^ 3
      ≤ K₀ * (1 + Real.log E.KH) := by
    rw [hf3]
    exact le_trans r3 (mul_le_mul_of_nonneg_right hKql
      (by linarith [Real.log_nonneg hview.one_le_KH]))
  -- ### the `P_H^q` row 1
  have rowq : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (excited (Lab (HM μ).N)).filter (F.PHq E.KH E.aScat),
          E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ K₀ * E.aScat :=
    le_trans (hqrow HM μ hμ hεg) (mul_le_mul_of_nonneg_right hKq hview.a_pos.le)
  -- ### the `Ŵ₁ − ĝ` row (the `sum_diff` row, from the interface)
  have rowδ : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ F.PHset E,
          (chat (g0 v h) (F.kmom k) - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ K₀ * E.aScat * (R / E.ell) ^ 4 :=
    le_trans (hδrow HM hN μ hμ hεg) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKδ hview.a_pos.le) (by positivity))
  exact Work.BoseRowsFS.intKernel_kzEnvAt F E (fun k => chat (g0 v h) (F.kmom k)) R ρ K₀
    hρ hellpos hX rowW1 rowg rowA rowAB rowne rowtau rowω rowlow row4 row6 row3 rowq rowδ

end

end Work.BoseRowsL.Glue
