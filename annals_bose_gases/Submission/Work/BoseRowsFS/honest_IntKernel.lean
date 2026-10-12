import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.RowSumW1sq_regime
import Submission.Work.BoseRowsFS.honest_lattice_rows
import Submission.Work.BoseRowsFS.honest_sum_diff
import Submission.Work.BoseRowsFS.honest_tauSm_rows
import Submission.Work.BoseRowsFS.omega_lattice_honest_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowsFS

open scoped Real BigOperators Topology
open MeasureTheory Metric

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

noncomputable section

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## The generic assembly of `IntKernel` at a `KzEnvAt` datum -/

/-- `ρ_z = ρ` at the `KzEnvAt` datum, for `ρ ≥ 0`. -/
lemma rho_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Q3Env Mode) {ρ : ℝ} (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) :
    (KzEnvAt E ρ).rho = ρ := by
  rw [Q3Env.rho, KzEnvAt, Work.BoseB7.rhoZ]
  simp only []
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- **Generic assembly of `IntKernel` at the `KzEnvAt` datum.**

`KzEnvAt E ρ` changes only the `c`-number `z`, the `A`- and the `B`-kernels of `E`
(`z ↦ √(ρℓ³)`, `A ↦ τ + ρŴ₁`, `B ↦ ρŴ₁`); the scalars `ℓ`, `K_H`, `a`, the kernels
`τ`, `Ŵ₁`, `Ŵ₁ω(0)` and the mode sets `PHset`, `excited` are untouched, so every row
of `Work.BoseB7A.IntKernel` other than `A_eq`, `B_eq` transfers verbatim.  The two
exceptions are

* `A_eq`/`B_eq`, which use `ρ_z = ρ` (`rho_KzEnvAt`);
* `sum_W1sq`, whose `P_H`-sum is bounded by the wider `P_H^q`-sum
  (`1/(4K_H a) ≤ 1/(2K_H a) ≤ ‖k‖`). -/
lemma intKernel_kzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (E : Q3Env Mode) (gHat : Mode → ℝ) (R ρ K : ℝ)
    (hρ : 0 ≤ ρ) (hℓ : 0 < E.ell) (hX : 0 < E.KH * E.aScat)
    (hW1 : ∀ k, |E.W1 k| ≤ K * E.aScat)
    (hg : ∀ k, |gHat k| ≤ K * E.aScat)
    (hA : ∀ k, F.PH E.KH E.aScat k → 0 < (KzEnvAt E ρ).A k)
    (hAB : ∀ k, F.PH E.KH E.aScat k → 2 * |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k)
    (hne : ∀ k ∈ Work.BoseB7.excited Mode, F.kmom k ≠ 0)
    (htau : ∀ k, 0 ≤ ‖F.kmom k‖ ^ 2 - E.tau k ∧
      ‖F.kmom k‖ ^ 2 - E.tau k ≤ 2 * ‖F.kmom k‖ / (E.d * E.s * E.ell))
    (hω : |E.W1omega0 - E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖F.kmom k‖ ^ 2)|
      ≤ K * E.aScat ^ 2 / E.ell)
    (hlow : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (fun k => ¬ F.PH E.KH E.aScat k),
          1 / ‖F.kmom k‖ ^ 2 ≤ K / (E.KH * E.aScat))
    (hi4 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 4
      ≤ K * E.KH * E.aScat)
    (hi6 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, 1 / ‖F.kmom k‖ ^ 6
      ≤ K * (E.KH * E.aScat) ^ 3)
    (hi3 : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (F.PHset E).filter (fun k => ‖F.kmom k‖ ≤ 1 / E.aScat), 1 / ‖F.kmom k‖ ^ 3
      ≤ K * (1 + Real.log E.KH))
    (hK1 : E.ell ^ (-(3 : ℝ)) *
        ∑ k ∈ (Work.BoseB7.excited Mode).filter (Work.BoseB7.FockData.PHq F E.KH E.aScat),
          E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 ≤ K * E.aScat)
    (hK2 : E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ K * E.aScat * (R / E.ell) ^ 4) :
    IntKernel K R F (KzEnvAt E ρ) gHat := by
  have hrho : (KzEnvAt E ρ).rho = ρ := rho_KzEnvAt E hρ hℓ
  have hPHsub : F.PHset E ⊆
      (Work.BoseB7.excited Mode).filter (Work.BoseB7.FockData.PHq F E.KH E.aScat) := by
    intro k hk
    simp only [Work.BoseB7.FockData.PHset, Work.BoseB7.FockData.PH,
      Work.BoseB7.FockData.PHq, Finset.mem_filter] at hk ⊢
    refine ⟨hk.1, ?_⟩
    have h2 : (2 : ℝ) * E.KH * E.aScat ≤ 4 * E.KH * E.aScat := by linarith [hX]
    have h3 : 1 / (4 * E.KH * E.aScat) ≤ 1 / (2 * E.KH * E.aScat) :=
      one_div_le_one_div_of_le (by linarith [hX]) h2
    exact le_trans h3 hk.2
  refine ⟨hW1, hg, ?_, ?_, hA, hAB, hne, fun k _ => htau k, hω, hlow, hi4, hi6, hi3, ?_, hK2⟩
  · intro k
    rw [hrho]
    rfl
  · intro k
    rw [hrho]
    rfl
  · have hle : (∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2)
        ≤ ∑ k ∈ (Work.BoseB7.excited Mode).filter
            (Work.BoseB7.FockData.PHq F E.KH E.aScat),
            E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hPHsub (fun k _ _ => by positivity)
    have hnn : (0 : ℝ) ≤ E.ell ^ (-(3 : ℝ)) := Real.rpow_nonneg hℓ.le _
    calc (KzEnvAt E ρ).ell ^ (-(3 : ℝ)) *
          ∑ k ∈ F.PHset (KzEnvAt E ρ), (KzEnvAt E ρ).W1 k ^ 2 / ‖F.kmom k‖ ^ 2
        = E.ell ^ (-(3 : ℝ)) * ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := rfl
      _ ≤ E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (Work.BoseB7.excited Mode).filter
            (Work.BoseB7.FockData.PHq F E.KH E.aScat),
            E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := mul_le_mul_of_nonneg_left hle hnn
      _ ≤ K * E.aScat := hK1
      _ = K * (KzEnvAt E ρ).aScat := rfl

end

theorem honest_IntKernel {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
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
    (hApos : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg → 0 ≤ ρ →
      ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honF v h fc fu HM μ).PH
            (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
          0 < (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k)
    (hAB : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ ρ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ εg → 0 ≤ ρ →
      ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        (Work.BoseRowsFS.honF v h fc fu HM μ).PH
            (Work.BoseRowsFS.honE v h fc fu HM μ).KH
            (Work.BoseRowsFS.honE v h fc fu HM μ).aScat k →
          2 * |(Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).B k|
            ≤ (Work.BoseFixR.KzEnvAt (Work.BoseRowsFS.honE v h fc fu HM μ) ρ).A k) :
    ∃ K₀ : ℝ, 128 * Real.pi ≤ K₀ ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ), (∀ μ, Ng μ ≤ (HM μ).N) →
      ∀ (μ : ℝ), 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      ∀ ρ : ℝ, 0 ≤ ρ →
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
  intro HM hN μ hμ hε ρ hρ
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
  -- ### `A`, `B` rows (given) and `kmom ≠ 0`
  have rowA := hApos HM μ ρ hμ hε hρ
  have rowAB := hAB HM μ ρ hμ hε hρ
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

end Work.BoseRowsFS
