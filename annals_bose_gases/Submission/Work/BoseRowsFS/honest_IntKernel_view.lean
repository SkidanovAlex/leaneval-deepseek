import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.honest_IntKernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseRowsFS/honest_IntKernel_view.lean`

**The honest `IntKernel` with the two `P_H` rows supplied *at the view*.**

`Work.BoseRowsFS.honest_IntKernel` (this area, session 3) reduces `IntKernel` at
the honest model to fifteen derived rows plus the two mode-level rows
`A_pos`/`AB_kernel`.  The latter two are proved in
`Work.BoseRowsFS.honest_A_ge_AB` **from the view** `FSParamsView (KzEnvAt (honE …) ρ)`
of the datum: the proof needs the density bound `|ρ − μ| ≤ μ/2` which is a field
of that view.  `honest_IntKernel`'s signature, however, demands `A_pos`/`AB_kernel`
for *every* `ρ ≥ 0`, and for large `ρ` they are false
(`𝒜 k = τ k + ρŴ₁ k`, `ℬ k = ρŴ₁ k`: `2|ℬ| ≤ 𝒜` would force `ρŴ₁ k ≤ τ k` for
arbitrarily large `ρ`).  So `honest_IntKernel` is not applicable at the honest
data, and the unconditional statement `Work.BoseRowsFS.honest_IntKernel_uncond`
must instead assemble `IntKernel` directly from the row-collecting step of
`honest_IntKernel`'s proof, with the two `P_H` rows taken *from the view*.

This module does exactly that:

* `view_t_eq_mu_a3` — `hvK.t = μa³` at any view of `KzEnvAt (honE …) ρ`
  (`KzEnvAt` changes neither `μ` nor `aScat`);
* `honest_IntKernel_view` — for an effective diluteness threshold `ε ≤ εg` and a
  `P_H`-row package `hArows` indexed by the view of the datum, the honest
  `IntKernel` holds at every admissible `(μ, ρ)` with the *same* constant `K₀`,
  `128π ≤ K₀`, as `honest_IntKernel`.

The body is the row-collecting half of `honest_IntKernel`'s proof verbatim (the
rows are all functions of the fixed environment `honE …`, not of `ρ`); only the
final `intro` and the two rows `rowA`/`rowAB` differ.
-/

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- `hvK.t = μ·(a v)³` for every view of the `KzEnvAt` datum: `KzEnvAt` keeps
the chemical potential `μ` and the scattering length `a` of `honE … μ`, which are
`μ` and `a v`. -/
lemma view_t_eq_mu_a3 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ ρ : ℝ}
    (hvK : Work.BoseB7.FSParamsView
      (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) :
    hvK.t = μ * _root_.BoseGases.a v ^ 3 := by
  have hh := hvK.mu_eq
  have hE : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).mu = μ := rfl
  have hA : (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).aScat
      = _root_.BoseGases.a v := rfl
  rw [hE, hA] at hh
  exact hh.symm

/-- **The honest `IntKernel`, with the two `P_H` rows taken from the view.**

Identical to `Work.BoseRowsFS.honest_IntKernel` except that

* the threshold is an effective `ε ≤ εg` (the row hypotheses `hrég`, `hcut`,
  `htail`, `hFSP` are still those of the caller's `εg`, used through `hε ≤ εg`);
* the fields `A_pos`/`AB_kernel` are not hypotheses but come from `hArows`, which
  is indexed by the view `hvK` of the datum `KzEnvAt (honE … μ) ρ` — the form in
  which `Work.BoseRowsFS.honest_A_ge_AB` (and its régime-restricted variant
  `Work.BoseRowsFS.honest_A_ge_AB_regime`) proves them. -/
theorem honest_IntKernel_view {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (havm : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hdecayW : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (hdecayg : ∀ ℓ : ℝ, 1 ≤ ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 2
          ≤ Cw * _root_.BoseGases.a v)
    (Ng : ℝ → ℕ) (εg : ℝ) (hεg : 0 < εg)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0)
    (hcut : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 / R ≤ 2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (Ng μ)
        ∧ Cw ^ 2 * Work.BoseBoxFock.ellH v μ
            ≤ (2 * Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (Ng μ)) ^ 3)
    (htail : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ),
      (∀ μ, Ng μ ≤ (HM μ).N) → ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
        (Work.BoseRowsFS.honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
            ∑ k ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
                (fun k => Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) (HM μ).N
                  < ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖),
              (Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
                  ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2
                + Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k) ^ 2)
                / ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
          ≤ Cw ^ 2 * _root_.BoseGases.a v
              * (R / Work.BoseBoxFock.ellH v μ) ^ 4)
    (hFSP : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ))
    (ε : ℝ) (hεpos : 0 < ε) (hεεg : ε ≤ εg)
    (hArows : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ)
        (hvK : Work.BoseB7.FSParamsView
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)),
        0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε → 0 ≤ ρ →
        (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16 →
        (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseRowsFS.honF v h fc fu HM μ).PH
              (Work.BoseRowsFS.honE v h fc fu HM μ).KH
              (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
            0 < (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k)
        ∧ (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseRowsFS.honF v h fc fu HM μ).PH
              (Work.BoseRowsFS.honE v h fc fu HM μ).KH
              (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
            2 * |(Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).B k|
              ≤ (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k)) :
    ∃ K₀ : ℝ, 128 * Real.pi ≤ K₀ ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ ρ : ℝ),
        (hvK : Work.BoseB7.FSParamsView
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)) →
        0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ ε → 0 ≤ ρ →
        (Work.BoseRowsFS.honE v h fc fu HM μ).aScat
            * (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            / ((Work.BoseRowsFS.honE v h fc fu HM μ).s
              * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) ≤ 1 / 16 →
        Work.BoseB7A.IntKernel K₀ R (Work.BoseRowsFS.honF v h fc fu HM μ)
          (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ)
          (fun k => Work.BoseFixR.chat (Submission.BoseGases.g0 v h)
            ((Work.BoseRowsFS.honF v h fc fu HM μ).kmom k)) := by
  -- the four honest rows, each with an absolute constant
  obtain ⟨Cω, hCω, hωrow⟩ := omega_lattice_honest_decay (v := v) (h := h) (fc := fc) (fu := fu)
    R hR havm hv_nonneg hvrad hv_supp Cw hCw hdecayW hdecayg Ng εg hεg hrég hcut
  obtain ⟨Cδ, hCδ, hδrow⟩ := honest_sum_diff (v := v) (h := h) (fc := fc) (fu := fu)
    R hR havm hv_nonneg hvrad hv_supp Cw hCw hdecayW hdecayg Ng εg hεg hrég htail
  obtain ⟨Kl, hKl, hlrows⟩ := honest_lattice_rows (v := v) (h := h) (fc := fc) (fu := fu)
  obtain ⟨Cq, hCq, hqrow⟩ := RowSumW1sq_regime (v := v) (h := h) (fc := fc) (fu := fu)
    (R := R) hR havm hv_nonneg hvrad hv_supp εg hrég
  -- one absolute constant dominating all of them
  set K₀ : ℝ := 128 * Real.pi + Cω + Cδ + Kl + Cq with hK₀
  have hK128 : 128 * Real.pi ≤ K₀ := by rw [hK₀]; linarith [Real.pi_pos, hCω, hCδ, hKl, hCq]
  have hK16 : 16 * Real.pi ≤ K₀ := by rw [hK₀]; linarith [Real.pi_pos, hCω, hCδ, hKl, hCq]
  have hK8 : 8 * Real.pi ≤ K₀ := by rw [hK₀]; linarith [Real.pi_pos, hCω, hCδ, hKl, hCq]
  have hKω : Cω ≤ K₀ := by rw [hK₀]; linarith [Real.pi_pos, hCδ, hKl, hCq]
  have hKδ : Cδ ≤ K₀ := by rw [hK₀]; linarith [Real.pi_pos, hCω, hKl, hCq]
  have hKql : Kl ≤ K₀ := by rw [hK₀]; linarith [Real.pi_pos, hCω, hCδ, hCq]
  have hKq : Cq ≤ K₀ := by rw [hK₀]; linarith [Real.pi_pos, hCω, hCδ, hKl]
  refine ⟨K₀, hK128, ?_⟩
  intro HM hN μ ρ hvK hμ hεμ hρ hsc
  have hε : μ * _root_.BoseGases.a v ^ 3 ≤ εg := le_trans hεμ hεεg
  have hview := hFSP HM μ hμ hε
  obtain ⟨h1ℓ, hRchi⟩ := hrég μ hμ hε
  have hellpos : 0 < (honE v h fc fu HM μ).ell := by
    rw [honE_ell v h fc fu HM μ hμ havm]
    linarith
  have hKHpos : 0 < (honE v h fc fu HM μ).KH := lt_of_lt_of_le one_pos hview.one_le_KH
  have hX : 0 < (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat :=
    mul_pos hKHpos hview.a_pos
  -- ### `Ŵ₁` row
  have rowW1 : ∀ k : Lab (HM μ).N,
      |(honE v h fc fu HM μ).W1 k| ≤ K₀ * (honE v h fc fu HM μ).aScat := by
    intro k
    rw [honE_W1_apply v h fc fu HM μ hμ havm k]
    have hb := Work.BoseB7AK.W1rows.W1hat_abs_le (v := v) (R := R) (ℓ := ellH v μ)
      hR (ellH_pos v μ) hv_nonneg hvrad hv_supp h hRchi ((honF v h fc fu HM μ).kmom k)
    have hζ : |uvCut fu (uvRad (ellH v μ) (HM μ).N)
        ((honF v h fc fu HM μ).kmom k)| ≤ 1 := by
      have h0 : 0 ≤ uvCut fu (uvRad (ellH v μ) (HM μ).N) ((honF v h fc fu HM μ).kmom k) :=
        Work.BoseBoxFix.LowCut.nonneg fu _
      have h1 : uvCut fu (uvRad (ellH v μ) (HM μ).N) ((honF v h fc fu HM μ).kmom k) ≤ 1 :=
        Work.BoseBoxFix.LowCut.le_one fu _
      rw [abs_le]
      exact ⟨by linarith, h1⟩
    calc |uvCut fu (uvRad (ellH v μ) (HM μ).N) ((honF v h fc fu HM μ).kmom k)
          * chat (W1fun v h (ellH v μ)) ((honF v h fc fu HM μ).kmom k)|
        = |uvCut fu (uvRad (ellH v μ) (HM μ).N) ((honF v h fc fu HM μ).kmom k)|
            * |chat (W1fun v h (ellH v μ)) ((honF v h fc fu HM μ).kmom k)| := abs_mul _ _
      _ ≤ 1 * (16 * Real.pi * a v) := mul_le_mul hζ hb (abs_nonneg _) (by norm_num)
      _ = 16 * Real.pi * a v := one_mul _
      _ ≤ K₀ * a v := mul_le_mul_of_nonneg_right hK16 havm.le
      _ = K₀ * (honE v h fc fu HM μ).aScat := rfl
  -- ### `ĝ` row
  have rowg : ∀ k : Lab (HM μ).N,
      |chat (g0 v h) ((honF v h fc fu HM μ).kmom k)| ≤ K₀ * (honE v h fc fu HM μ).aScat := by
    intro k
    have hb := chat_g0_abs_le (v := v) (R := R) hR hv_nonneg hvrad hv_supp h
      ((honF v h fc fu HM μ).kmom k)
    calc |chat (g0 v h) ((honF v h fc fu HM μ).kmom k)| ≤ 8 * Real.pi * a v := hb
      _ ≤ K₀ * a v := mul_le_mul_of_nonneg_right hK8 havm.le
      _ = K₀ * (honE v h fc fu HM μ).aScat := rfl
  -- ### `A`, `B` rows (from the view) and `kmom ≠ 0`
  have hrows := hArows HM μ ρ hvK hμ hεμ hρ hsc
  have rowA := hrows.1
  have rowAB := hrows.2
  have rowne : ∀ k ∈ excited (Lab (HM μ).N), (honF v h fc fu HM μ).kmom k ≠ 0 := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hinj := Work.BoseBoxFock.GramLab.kmomLab_injective (ellH v μ) (ellH_pos v μ) (HM μ).N
    have hz : kmomLab (ellH v μ) (HM μ).N (0 : Lab (HM μ).N) = 0 := by
      rw [kmomLab_eq, labVec_zero, vecZ_zero, smul_zero]
    exact fun hkzero => hk0 (hinj (hkzero.trans hz.symm))
  -- ### the τ̃ row
  have rowtau : ∀ k : Lab (HM μ).N,
      0 ≤ ‖(honF v h fc fu HM μ).kmom k‖ ^ 2 - (honE v h fc fu HM μ).tau k
        ∧ ‖(honF v h fc fu HM μ).kmom k‖ ^ 2 - (honE v h fc fu HM μ).tau k
          ≤ 2 * ‖(honF v h fc fu HM μ).kmom k‖
              / ((honE v h fc fu HM μ).d * (honE v h fc fu HM μ).s
                  * (honE v h fc fu HM μ).ell) :=
    fun k => honest_tauSm_rows (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hview k
  -- ### the `Ŵ₁ω(0)` row
  have rowω : |(honE v h fc fu HM μ).W1omega0
        - (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ excited (Lab (HM μ).N),
            (honE v h fc fu HM μ).W1 k * chat (g0 v h) ((honF v h fc fu HM μ).kmom k)
              / (2 * ‖(honF v h fc fu HM μ).kmom k‖ ^ 2)|
      ≤ K₀ * (honE v h fc fu HM μ).aScat ^ 2 / (honE v h fc fu HM μ).ell := by
    refine le_trans (hωrow HM hN μ hμ hε) ?_
    have hX2 : (0 : ℝ) ≤ (honE v h fc fu HM μ).aScat ^ 2 / (honE v h fc fu HM μ).ell :=
      div_nonneg (sq_nonneg _) hellpos.le
    calc Cω * (honE v h fc fu HM μ).aScat ^ 2 / (honE v h fc fu HM μ).ell
        = Cω * ((honE v h fc fu HM μ).aScat ^ 2 / (honE v h fc fu HM μ).ell) := by ring
      _ ≤ K₀ * ((honE v h fc fu HM μ).aScat ^ 2 / (honE v h fc fu HM μ).ell) :=
          mul_le_mul_of_nonneg_right hKω hX2
      _ = K₀ * (honE v h fc fu HM μ).aScat ^ 2 / (honE v h fc fu HM μ).ell := by ring
  -- ### the four lattice rows
  obtain ⟨rl, r4, r6, r3⟩ := hlrows HM μ hμ hview h1ℓ
  have hfl : (excited (Lab (HM μ).N)).filter
        (fun k => ¬ (honF v h fc fu HM μ).PH (honE v h fc fu HM μ).KH
          (honE v h fc fu HM μ).aScat k)
      = (excited (Lab (HM μ).N)).filter
        (fun k => ¬ (1 / (2 * (honE v h fc fu HM μ).KH
          * (honE v h fc fu HM μ).aScat) ≤ ‖honKmom v HM μ k‖)) := by
    refine Finset.filter_congr (fun k hk => ?_)
    simp only [Work.BoseB7.FockData.PH, honF_kmom]
  have hfp : (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ)
      = (excited (Lab (HM μ).N)).filter
        (fun k => 1 / (2 * (honE v h fc fu HM μ).KH
          * (honE v h fc fu HM μ).aScat) ≤ ‖honKmom v HM μ k‖) := by
    rw [Work.BoseB7.FockData.PHset]
    refine Finset.filter_congr (fun k hk => ?_)
    simp only [Work.BoseB7.FockData.PH, honF_kmom]
  have hf3 : ((honF v h fc fu HM μ).PHset (honE v h fc fu HM μ)).filter
        (fun k => ‖(honF v h fc fu HM μ).kmom k‖ ≤ 1 / (honE v h fc fu HM μ).aScat)
      = (((excited (Lab (HM μ).N)).filter
          (fun k => 1 / (2 * (honE v h fc fu HM μ).KH
            * (honE v h fc fu HM μ).aScat) ≤ ‖honKmom v HM μ k‖)).filter
          (fun k => ‖honKmom v HM μ k‖ ≤ 1 / (honE v h fc fu HM μ).aScat)) := by
    rw [hfp]
    refine Finset.filter_congr (fun k hk => ?_)
    simp only [honF_kmom]
  have rowlow : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (excited (Lab (HM μ).N)).filter
            (fun k => ¬ (honF v h fc fu HM μ).PH
              (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat k),
          1 / ‖(honF v h fc fu HM μ).kmom k‖ ^ 2
      ≤ K₀ / ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) := by
    rw [hfl]
    exact le_trans rl (div_le_div_of_nonneg_right hKql hX.le)
  have row4 : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
          1 / ‖(honF v h fc fu HM μ).kmom k‖ ^ 4
      ≤ K₀ * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat := by
    rw [hfp]
    rw [show K₀ * (honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat
        = K₀ * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) from by ring]
    exact le_trans r4 (mul_le_mul_of_nonneg_right hKql hX.le)
  have row6 : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
          1 / ‖(honF v h fc fu HM μ).kmom k‖ ^ 6
      ≤ K₀ * ((honE v h fc fu HM μ).KH * (honE v h fc fu HM μ).aScat) ^ 3 := by
    rw [hfp]
    exact le_trans r6 (mul_le_mul_of_nonneg_right hKql (by positivity))
  have row3 : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ ((honF v h fc fu HM μ).PHset (honE v h fc fu HM μ)).filter
            (fun k => ‖(honF v h fc fu HM μ).kmom k‖ ≤ 1 / (honE v h fc fu HM μ).aScat),
          1 / ‖(honF v h fc fu HM μ).kmom k‖ ^ 3
      ≤ K₀ * (1 + Real.log (honE v h fc fu HM μ).KH) := by
    rw [hf3]
    exact le_trans r3 (mul_le_mul_of_nonneg_right hKql
      (by linarith [Real.log_nonneg hview.one_le_KH]))
  -- ### the `P_H^q` row 1
  have rowq : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (excited (Lab (HM μ).N)).filter
            ((honF v h fc fu HM μ).PHq
              (honE v h fc fu HM μ).KH (honE v h fc fu HM μ).aScat),
          (honE v h fc fu HM μ).W1 k ^ 2 / ‖(honF v h fc fu HM μ).kmom k‖ ^ 2
      ≤ K₀ * (honE v h fc fu HM μ).aScat :=
    le_trans (hqrow HM μ hμ hε) (mul_le_mul_of_nonneg_right hKq hview.a_pos.le)
  -- ### the `Ŵ₁ − ĝ` row
  have rowδ : (honE v h fc fu HM μ).ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (honF v h fc fu HM μ).PHset (honE v h fc fu HM μ),
          (chat (g0 v h) ((honF v h fc fu HM μ).kmom k) - (honE v h fc fu HM μ).W1 k) ^ 2
            / ‖(honF v h fc fu HM μ).kmom k‖ ^ 2
      ≤ K₀ * (honE v h fc fu HM μ).aScat * (R / (honE v h fc fu HM μ).ell) ^ 4 :=
    le_trans (hδrow HM hN μ hμ hε) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKδ hview.a_pos.le) (by positivity))
  exact intKernel_kzEnvAt (honF v h fc fu HM μ) (honE v h fc fu HM μ)
    (fun k => chat (g0 v h) ((honF v h fc fu HM μ).kmom k)) R ρ K₀ hρ hellpos hX
    rowW1 rowg rowA rowAB rowne rowtau rowω rowlow row4 row6 row3 rowq rowδ

end

end Work.BoseRowsFS
