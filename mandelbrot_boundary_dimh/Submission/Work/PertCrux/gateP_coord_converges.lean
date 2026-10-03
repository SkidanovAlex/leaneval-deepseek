import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.tools
import Submission.Work.Pert.Gates
import Submission.Work.Pert.eventually_subset_gates
import Submission.Work.Pert.limitCoord_plus_exists
import Submission.Work.Pert.nearTranslation_F0
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.u_close_of_nearOn
import Submission.Work.Pert.rotOf_bound_of_nearOn_compact
import Submission.Work.Pert.qadm
import Submission.Work.Pert.tauC_gate_sub_closedBall
import Submission.Work.Pert.tauC_add_inv_le
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.Pert.hF_lipschitz_on_ball
import Submission.Work.Pert.liftF_sub_model_le
import Submission.Work.PertCrux.gate_tauC_lower
import Submission.Work.PertCrux.liftF_tendsto_seq_simple
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Parabolic

namespace Work.PertCrux

open MandelDim Filter Metric
open scoped Topology

noncomputable section

/-! ## Auxiliary lemmas -/

/-- The sequential pigeonhole: if every sequence of counterexamples with tolerance `δ n → 0` is
impossible, then one positive tolerance works. -/
theorem exists_pos_forall_of_forall_seq_aux {P : ℝ → Prop}
    (h : ∀ (δ : ℕ → ℝ), (∀ n, 0 < δ n) → Tendsto δ atTop (𝓝 0) → (∀ n, ¬ P (δ n)) → False) :
    ∃ δ₀, 0 < δ₀ ∧ P δ₀ := by
  by_contra hc
  push Not at hc
  exact h (fun n => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => hc _ (by positivity))

/-- `NearTranslationOn` restricts to subsets. -/
lemma NearTranslationOn_mono {F : ℂ → ℂ} {Q Q' : Set ℂ} (h : MandelDim.NearTranslationOn F Q)
    (hsub : Q' ⊆ Q) : MandelDim.NearTranslationOn F Q' :=
  ⟨h.1.mono hsub, fun z hz => h.2 z (hsub hz)⟩

/-- The normalisation `1 - σ u 0 = exp (2πiα)`, `1/2 ≤ ‖u 0‖ ≤ 2` and smallness of `α` give
`π‖α‖/2 ≤ ‖σ‖`. -/
lemma pi_mul_norm_div_two_le_norm_sigma {u : ℂ → ℂ} {σ α : ℂ}
    (h2π : 2 * Real.pi * ‖α‖ ≤ 1 / 2) (hu0 : 1 / 2 ≤ ‖u 0‖) (hu2 : ‖u 0‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α)) :
    Real.pi * ‖α‖ / 2 ≤ ‖σ‖ := by
  have hz : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ = 2 * Real.pi * ‖α‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, Real.norm_of_nonneg (le_of_lt Real.pi_pos)]
  have hz2 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ ≤ 1 / 2 := by rw [hz]; exact h2π
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    rw [← hnorm]; ring
  have hkey : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ / 2 ≤
      ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
    have h3 : ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1
        - (2 * Real.pi * Complex.I * α : ℂ)‖
        ≤ ‖(2 * Real.pi * Complex.I * α : ℂ)‖ ^ 2 :=
      Complex.norm_exp_sub_one_sub_id_le (le_trans hz2 (by norm_num))
    have h4 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖
        ≤ ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖
          + ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1 - (2 * Real.pi * Complex.I * α)‖ := by
      have h := norm_sub_le (Complex.exp (2 * Real.pi * Complex.I * α) - 1)
        (Complex.exp (2 * Real.pi * Complex.I * α) - 1 - (2 * Real.pi * Complex.I * α))
      have he : (Complex.exp (2 * Real.pi * Complex.I * α) - 1)
          - (Complex.exp (2 * Real.pi * Complex.I * α) - 1 - (2 * Real.pi * Complex.I * α))
          = (2 * Real.pi * Complex.I * α : ℂ) := by ring
      rwa [he] at h
    have h5 : ‖Complex.exp (2 * Real.pi * Complex.I * α) - 1‖
        = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by rw [norm_sub_rev]
    have h6 : ‖(2 * Real.pi * Complex.I * α : ℂ)‖ ^ 2
        ≤ ‖(2 * Real.pi * Complex.I * α : ℂ)‖ / 2 := by
      nlinarith [hz2, norm_nonneg (2 * Real.pi * Complex.I * α : ℂ)]
    linarith [h4, h3, h5, h6]
  have hmain : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
    rw [← norm_mul, hσu]
  have hle : Real.pi * ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
    have h := hkey
    rw [hz] at h
    linarith
  have h2 : Real.pi * ‖α‖ ≤ ‖σ‖ * ‖u 0‖ := by rw [hmain]; exact hle
  have h3 : ‖σ‖ * ‖u 0‖ ≤ ‖σ‖ * 2 := mul_le_mul_of_nonneg_left hu2 (norm_nonneg σ)
  have h4 : Real.pi * ‖α‖ * 2 ≤ ‖σ‖ * 2 * 2 := by nlinarith [h2, h3]
  linarith [h4]

/-- `‖α n‖ → 0` inside the class `𝓕₁` makes `Re (1/α n) → +∞`. -/
lemma eventually_le_inv_re {α : ℕ → ℂ} (h0 : Tendsto (fun n => ‖α n‖) atTop (𝓝 0))
    (hinf : ∀ n, MandelDim.InF1 (α n)) :
    ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, R ≤ (1 / α n).re := by
  have hpos : ∀ n : ℕ, 0 < ‖α n‖ := fun n => by
    have hre : 0 < (α n).re := lt_of_le_of_lt (abs_nonneg _) (hinf n)
    exact norm_pos_iff.mpr (fun h => by rw [h] at hre; simp at hre)
  intro R
  rcases lt_or_ge (0 : ℝ) R with hR | hR
  · have h2 : (0 : ℝ) < 1 / (2 * R) := by positivity
    filter_upwards [h0.eventually (isOpen_Iio.mem_nhds h2)] with n hn
    have hn' : ‖α n‖ < 1 / (2 * R) := hn
    have h1 := Work.Pert.inv_re_lower (hinf n)
    have h3 : R < 1 / (2 * ‖α n‖) := by
      have hp := hpos n
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * ‖α n‖)]
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * R)] at hn'
      linarith
    linarith
  · refine Filter.Eventually.of_forall (fun n => ?_)
    have h1 := Work.Pert.inv_re_lower (hinf n)
    have h2 : 0 < 1 / (2 * ‖α n‖) := by
      have hp := hpos n
      positivity
    linarith

/-- **The gate `Qp Ξ' α` swallows a fixed compact of the cone** once `Re (1/α)` is large. -/
lemma eventually_subset_Qp {Ξ' : ℝ} {K : Set ℂ} (hKc : IsCompact K)
    (hK : K ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none) {ι : Type*} {l : Filter ι} {α : ι → ℂ}
    (hre : ∀ R : ℝ, ∀ᶠ n in l, R ≤ (1 / α n).re) :
    ∀ᶠ n in l, K ⊆ Work.Pert.Qp Ξ' (α n) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z ∈ K, z.re ≤ C := by
    obtain ⟨a, ha⟩ := hKc.image Complex.continuous_re |>.bddAbove
    exact ⟨a, fun z hz => ha ⟨z, hz, rfl⟩⟩
  filter_upwards [hre (C + Ξ' + 1)] with n hn z hz
  rw [Work.Pert.Qp_mem_iff]
  have hcone : Ξ' - |z.im| < z.re := by
    have h1 := hK hz
    rw [Work.Pert.mem_Qreg_cone] at h1
    linarith
  exact ⟨hcone, by linarith [hC z hz, hn, abs_nonneg (z.im - (1 / α n).im)]⟩

/-! ## The main theorem -/

theorem gateP_coord_converges {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
    ∀ {K : Set ℂ}, IsCompact K → K ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none →
    ∀ ε : ℝ, 0 < ε → ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧
      Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ') ⊆ L ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) →
        MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) →
        ∃ Φp : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φp (Work.Pert.Qp Ξ' α) ∧
          ∀ ζ ∈ K, MandelDim.tau0 ζ ∈ MandelDim.ParabolicBasin f₀ D₀ →
            ‖Φp ζ - d.Φ (MandelDim.tau0 ζ)‖ < ε := by
  classical
  obtain ⟨ξL, hξLpos, hLim⟩ := Work.Pert.limitCoord_plus_exists d hd
  obtain ⟨ξN, hξNpos, hNT0, -, -, -⟩ := Work.Pert.nearTranslation_F0 hd
  obtain ⟨r₀, hr₀pos, hr₀sub, C₀, hC₀pos, hsmall⟩ := Work.Pert.small_of_nearOn hd
  obtain ⟨r₁, hr₁pos, Cα, hCαpos, hrot⟩ := Work.Pert.rotOf_bound_of_nearOn_compact hd
  obtain ⟨ξS, hξSpos, hSeq⟩ : ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
      ∀ K : Set ℂ, IsCompact K → K ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none →
      ∀ (δ : ℕ → ℝ), (∀ n, 0 < δ n) → Tendsto δ atTop (𝓝 0) →
      ∀ (f : ℕ → ℂ → ℂ) (Df : ℕ → Set ℂ) (rr : ℕ → ℝ) (u : ℕ → ℂ → ℂ) (σ α : ℕ → ℂ),
        (∀ n, MandelDim.NearOn f₀ (f n) (Df n) (Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ'))
          (δ n)) →
        (∀ n, f n 0 = 0) →
        (∀ n, MandelDim.InF1 (MandelDim.rotOf (f n))) →
        (∀ n, α n = MandelDim.rotOf (f n)) →
        (∀ n, 0 < rr n) →
        (∀ n, 1 / (4 * (Ξ' + 1)) ≤ rr n) →
        (∀ n, ‖α n‖ ≤ 1 / 64) →
        (∀ n, DifferentiableOn ℂ (u n) (Metric.ball 0 (rr n))) →
        (∀ n z, z ∈ Metric.ball 0 (rr n) → 1 / 2 ≤ ‖u n z‖ ∧ ‖u n z‖ ≤ 2) →
        (∀ n z, z ∈ Metric.ball 0 (rr n) → f n z = z + z * (z - σ n) * u n z) →
        (∀ n, 1 - σ n * u n 0 = Complex.exp (2 * Real.pi * Complex.I * α n)) →
        (∀ n, MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α n))) →
        (∀ n, ∀ z ∈ Work.Pert.Qp Ξ' (α n), Work.Pert.tauC (σ n) (α n) z ∈ Metric.ball 0 (rr n)) →
        TendstoUniformlyOn
          (fun n : ℕ => fun w : ℂ => Work.Pert.liftF (u n) (σ n) (α n) w)
          (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Filter.atTop K :=
    Work.PertCrux.liftF_tendsto_seq_simple (D₀ := D₀) hd
  refine ⟨max (max ξL ξN) (max ξS (max (16 * Real.pi / r₀) 64)), ?_, ?_⟩
  · exact lt_of_lt_of_le (lt_max_of_lt_left hξLpos) (le_max_left _ _)
  · intro Ξ' hΞ' K hKc hKcone ε hε
    have h1 : max ξL ξN ≤ Ξ' := le_trans (le_max_left _ _) hΞ'
    have h2 : max ξS (max (16 * Real.pi / r₀) 64) ≤ Ξ' := le_trans (le_max_right _ _) hΞ'
    have h3 : max (16 * Real.pi / r₀) 64 ≤ Ξ' := le_trans (le_max_right _ _) h2
    have hξLΞ : ξL ≤ Ξ' := le_trans (le_max_left _ _) h1
    have hξNΞ : ξN ≤ Ξ' := le_trans (le_max_right _ _) h1
    have hξSΞ : ξS ≤ Ξ' := le_trans (le_max_left _ _) h2
    have h16r₀Ξ : 16 * Real.pi / r₀ ≤ Ξ' := le_trans (le_max_left _ _) h3
    have h64Ξ : (64 : ℝ) ≤ Ξ' := le_trans (le_max_right _ _) h3
    have hΞ'pos : 0 < Ξ' := lt_of_lt_of_le hξLpos hξLΞ
    have h16r₀ : 16 * Real.pi / Ξ' ≤ r₀ := by
      rw [div_le_iff₀ hr₀pos] at h16r₀Ξ
      rw [div_le_iff₀ hΞ'pos]
      linarith
    refine ⟨Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ'),
      isCompact_closedBall (x := (0 : ℂ)) (r := 16 * Real.pi / Ξ'), ?_, subset_rfl, ?_⟩
    · exact fun z hz => hr₀sub (Metric.closedBall_subset_closedBall h16r₀ hz)
    · refine exists_pos_forall_of_forall_seq_aux ?_
      intro δ hδpos hδlim hnotP
      have hseq : ∀ n : ℕ, ∃ (f : ℂ → ℂ) (Df : Set ℂ) (rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
          MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ')) (δ n) ∧
            f 0 = 0 ∧ MandelDim.InF1 (MandelDim.rotOf f) ∧ α = MandelDim.rotOf f ∧ 0 < rr ∧
            DifferentiableOn ℂ u (Metric.ball 0 rr) ∧
            (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) ∧
            (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) ∧
            1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) ∧
            (∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) ∧
            MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) ∧
            MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) ∧
            MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) ∧
          (∀ Φp : ℂ → ℂ, MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φp
            (Work.Pert.Qp Ξ' α) → ∃ ζ : ℂ, ζ ∈ K ∧
            MandelDim.tau0 ζ ∈ MandelDim.ParabolicBasin f₀ D₀ ∧
            ε ≤ ‖Φp ζ - d.Φ (MandelDim.tau0 ζ)‖) := by
        intro n
        have h := hnotP n
        push Not at h
        exact h
      choose f Df rr u σ α hH using hseq
      have hNear : ∀ n, MandelDim.NearOn f₀ (f n) (Df n)
          (Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ')) (δ n) := fun n => (hH n).1
      have hf0 : ∀ n, f n 0 = 0 := fun n => (hH n).2.1
      have hInF1 : ∀ n, MandelDim.InF1 (MandelDim.rotOf (f n)) := fun n => (hH n).2.2.1
      have hAeq : ∀ n, α n = MandelDim.rotOf (f n) := fun n => (hH n).2.2.2.1
      have hrrpos : ∀ n, 0 < rr n := fun n => (hH n).2.2.2.2.1
      have hudiff : ∀ n, DifferentiableOn ℂ (u n) (Metric.ball 0 (rr n)) :=
        fun n => (hH n).2.2.2.2.2.1
      have hubnd : ∀ n z, z ∈ Metric.ball 0 (rr n) → 1 / 2 ≤ ‖u n z‖ ∧ ‖u n z‖ ≤ 2 :=
        fun n => (hH n).2.2.2.2.2.2.1
      have hform : ∀ n z, z ∈ Metric.ball 0 (rr n) →
          f n z = z + z * (z - σ n) * u n z := fun n => (hH n).2.2.2.2.2.2.2.1
      have hnorm : ∀ n, 1 - σ n * u n 0 = Complex.exp (2 * Real.pi * Complex.I * (α n)) :=
        fun n => (hH n).2.2.2.2.2.2.2.2.1
      have hτC : ∀ n z, z ∈ Work.Pert.Qp Ξ' (α n) →
          Work.Pert.tauC (σ n) (α n) z ∈ Metric.ball 0 (rr n) :=
        fun n => (hH n).2.2.2.2.2.2.2.2.2.1
      have hqadm1 : ∀ n, MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / (α n))) :=
        fun n => (hH n).2.2.2.2.2.2.2.2.2.2.1
      have hqadm2 : ∀ n, MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / (α n))) (some (-(Ξ' : ℂ))) :=
        fun n => (hH n).2.2.2.2.2.2.2.2.2.2.2.1
      have hNTL : ∀ n, MandelDim.NearTranslationL1 (Work.Pert.liftF (u n) (σ n) (α n))
          (Work.Pert.Qp Ξ' (α n)) := fun n => (hH n).2.2.2.2.2.2.2.2.2.2.2.2.1
      have hbad : ∀ n, ∀ Φp : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF (u n) (σ n) (α n)) Φp
            (Work.Pert.Qp Ξ' (α n)) → ∃ ζ : ℂ, ζ ∈ K ∧
            MandelDim.tau0 ζ ∈ MandelDim.ParabolicBasin f₀ D₀ ∧
            ε ≤ ‖Φp ζ - d.Φ (MandelDim.tau0 ζ)‖ := fun n => (hH n).2.2.2.2.2.2.2.2.2.2.2.2.2
      have hInF1α : ∀ n, MandelDim.InF1 (α n) := fun n => by rw [hAeq n]; exact hInF1 n
      -- the lower gate is admissible, hence `‖α n‖ Ξ' ≤ 1`
      have hα64 : ∀ n, ‖α n‖ ≤ 1 / 64 := by
        intro n
        have hs := Work.Pert.norm_alpha_mul_le_one_of_InF1_QAdm hΞ'pos (hInF1α n) (hqadm2 n)
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 64)]
        have hmono : ‖α n‖ * 64 ≤ ‖α n‖ * Ξ' := mul_le_mul_of_nonneg_left h64Ξ (norm_nonneg _)
        linarith
      have hαne : ∀ n, α n ≠ 0 := fun n => by
        have hre : 0 < (α n).re := lt_of_le_of_lt (abs_nonneg _) (hInF1α n)
        intro h
        rw [h] at hre
        simp at hre
      -- the gate has a waist: `rr n` is bounded below
      have hrrlo : ∀ n, 1 / (4 * (Ξ' + 1)) ≤ rr n := by
        intro n
        have hm : (0 : ℂ) ∈ Metric.ball 0 (rr n) := Metric.mem_ball_self (hrrpos n)
        have hu0 : 1 / 2 ≤ ‖u n 0‖ := (hubnd n 0 hm).1
        have hu2 : ‖u n 0‖ ≤ 2 := (hubnd n 0 hm).2
        have h2π : 2 * Real.pi * ‖α n‖ ≤ 1 / 2 := by
          have h3 := hα64 n
          nlinarith [Real.pi_pos, Real.pi_le_four, norm_nonneg (α n), h3]
        have hσ : Real.pi * ‖α n‖ / 2 ≤ ‖σ n‖ :=
          pi_mul_norm_div_two_le_norm_sigma h2π hu0 hu2 (hnorm n)
        obtain ⟨w, hw, hwlo⟩ :=
          gate_tauC_lower (Ξ' := Ξ') (σ := σ n) (α := α n) (by linarith [h64Ξ])
            (hαne n) (hInF1α n) (hqadm1 n) hσ
        have hmem := hτC n w hw
        rw [Metric.mem_ball, dist_zero_right] at hmem
        exact le_of_lt (lt_of_le_of_lt hwlo hmem)
      -- hence `‖α n‖ → 0`
      set ρ : ℝ := min (min (1 / (4 * (Ξ' + 1))) (16 * Real.pi / Ξ')) r₁ with hρdef
      have hρpos : 0 < ρ := by
        rw [hρdef]
        exact lt_min (lt_min (by positivity) (by positivity)) hr₁pos
      have hρlemin : ∀ n, ρ ≤ min (min (rr n) (16 * Real.pi / Ξ')) r₁ := by
        intro n
        rw [hρdef]
        refine le_min ?_ (min_le_right _ _)
        refine le_min ?_ (le_trans (min_le_left _ _) (min_le_right _ _))
        calc min (min (1 / (4 * (Ξ' + 1))) (16 * Real.pi / Ξ')) r₁
            ≤ min (1 / (4 * (Ξ' + 1))) (16 * Real.pi / Ξ') := min_le_left _ _
          _ ≤ 1 / (4 * (Ξ' + 1)) := min_le_left _ _
          _ ≤ rr n := hrrlo n
      have hαbnd : ∀ᶠ n : ℕ in atTop, ‖α n‖ ≤ (Cα / ρ) * δ n := by
        filter_upwards [hδlim.eventually (isOpen_Iio.mem_nhds (by positivity : (0:ℝ) < ρ / 2))]
          with n hn
        have h2δ : 2 * δ n ≤ min (min (rr n) (16 * Real.pi / Ξ')) r₁ := by
          have hρn := hρlemin n
          linarith
        have hb := hrot (f := f n) (Df := Df n)
          (L := Metric.closedBall (0 : ℂ) (16 * Real.pi / Ξ'))
          (u := u n) (σ := σ n) (ρ := min (rr n) (16 * Real.pi / Ξ')) (δ₀ := δ n)
          (isCompact_closedBall (x := (0 : ℂ)) (r := 16 * Real.pi / Ξ'))
          (fun z hz => hr₀sub (Metric.closedBall_subset_closedBall h16r₀ hz))
          (lt_min (hrrpos n) (by positivity))
          (Metric.closedBall_subset_closedBall (min_le_right _ _))
          (hδpos n) h2δ (hNear n) (hf0 n)
          ((hudiff n).mono (Metric.ball_subset_ball (min_le_left _ _)))
          (fun z hz => hubnd n z (Metric.ball_subset_ball (min_le_left _ _) hz))
          (fun z hz => hform n z (Metric.ball_subset_ball (min_le_left _ _) hz))
        rw [hAeq n]
        refine le_trans hb ?_
        have h8 : δ n / min (min (rr n) (16 * Real.pi / Ξ')) r₁ ≤ δ n / ρ :=
          div_le_div_of_nonneg_left (hδpos n).le hρpos (hρlemin n)
        calc Cα * (δ n / min (min (rr n) (16 * Real.pi / Ξ')) r₁) ≤ Cα * (δ n / ρ) :=
              mul_le_mul_of_nonneg_left h8 hCαpos.le
          _ = (Cα / ρ) * δ n := by ring
      have hαtend : Tendsto (fun n : ℕ => ‖α n‖) atTop (𝓝 0) := by
        have htend : Tendsto (fun n : ℕ => (Cα / ρ) * δ n) atTop (𝓝 0) := by
          have h0 : Tendsto (fun n : ℕ => (Cα / ρ) * δ n) atTop (𝓝 ((Cα / ρ) * 0)) :=
            hδlim.const_mul (Cα / ρ)
          simpa using h0
        refine tendsto_order.2 ⟨?_, ?_⟩
        · intro b hb
          exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le hb (norm_nonneg _))
        · intro b hb
          have hb' : ∀ᶠ n : ℕ in atTop, (Cα / ρ) * δ n < b :=
            htend (isOpen_Iio.mem_nhds (by simpa using hb))
          filter_upwards [hαbnd, hb'] with n h1 h2
          linarith
      have hαzero : ∀ R : ℝ, ∀ᶠ n : ℕ in atTop, R ≤ (1 / α n).re :=
        eventually_le_inv_re hαtend hInF1α
      -- the limit coordinate on the cone
      obtain ⟨Φ₀, hΦ₀coord, hΦ₀v⟩ := hLim Ξ' hξLΞ
      have hNT0' : MandelDim.NearTranslationOn
          (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
          (MandelDim.Qreg (some (Ξ' : ℂ)) none) :=
        NearTranslationOn_mono hNT0 (Work.Pert.Qreg_cone_mono hξNΞ)
      set z₀ : ℂ := ((Ξ' + 1 : ℝ) : ℂ) with hz₀def
      have hz₀mem : z₀ ∈ MandelDim.Qreg (some (Ξ' : ℂ)) none := by
        rw [hz₀def, Work.Pert.mem_Qreg_cone]
        simp
      have hcoord : ∀ n, ∃ Φp : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF (u n) (σ n) (α n)) Φp
            (Work.Pert.Qp Ξ' (α n)) ∧ Φp z₀ = Φ₀ z₀ := by
        intro n
        obtain ⟨Ψ, hΨ1, -⟩ := hF.1 (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / (α n)))
          (Work.Pert.liftF (u n) (σ n) (α n)) (hqadm1 n) ((hNTL n).1)
        exact ⟨fun z => Ψ z + (-(Ψ z₀) + Φ₀ z₀), Work.Pert.MandelDim.IsFatouCoordOn.add_const hΨ1 _, by simp⟩
      choose Φ hΦ using hcoord
      have hmove : ∀ K' ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none, IsCompact K' →
          (∀ᶠ n : ℕ in atTop, K' ⊆ MandelDim.Qreg (some (Ξ' : ℂ))
            (some (-(Ξ' : ℂ) + 1 / (α n)))) ∧
          TendstoUniformlyOn
            (fun n : ℕ => fun w : ℂ => Work.Pert.liftF (u n) (σ n) (α n) w)
            (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Filter.atTop K' := by
        intro K' hK'cone hK'c
        refine ⟨eventually_subset_Qp hK'c hK'cone hαzero, ?_⟩
        exact hSeq Ξ' hξSΞ K' hK'c hK'cone δ hδpos hδlim f Df rr u σ α hNear hf0 hInF1
          hAeq hrrpos hrrlo hα64 hudiff hubnd hform hnorm hqadm1 hτC
      have hQAdmcone : MandelDim.QAdm (some (Ξ' : ℂ)) none := by
        intro a ha b hb
        simp at hb
      have hcont := hF.2.2.2.1
        (fun n : ℕ => some (Ξ' : ℂ)) (fun n : ℕ => some (-(Ξ' : ℂ) + 1 / (α n)))
        (some (Ξ' : ℂ)) none
        (fun n : ℕ => fun w : ℂ => Work.Pert.liftF (u n) (σ n) (α n) w)
        (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Φ Φ₀ z₀
        hqadm1 hQAdmcone (fun n => (hNTL n).1) hNT0' hmove
        (fun n => (hΦ n).1) hΦ₀coord hz₀mem (Filter.Eventually.of_forall (fun n => (hΦ n).2))
      have hKconv : TendstoUniformlyOn Φ Φ₀ Filter.atTop K := hcont K hKcone hKc
      rw [Metric.tendstoUniformlyOn_iff] at hKconv
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hKconv ε hε)
      obtain ⟨ζ, hζK, hζbasin, hζbad⟩ := hbad N (Φ N) (hΦ N).1
      have hclose : ‖Φ N ζ - d.Φ (MandelDim.tau0 ζ)‖ < ε := by
        have h1 : dist (Φ₀ ζ) (Φ N ζ) < ε := hN N le_rfl ζ hζK
        rw [dist_eq_norm] at h1
        rw [hΦ₀v ζ (hKcone hζK) hζbasin] at h1
        rwa [norm_sub_rev] at h1
      linarith

end

end Work.PertCrux
