import Mathlib
import Submission.Work.Pert.pert2v2.gate_coord_close_minus

/-!
# `Work.Pert.pert2v2.gate_coord_close_minus_gen`

The **general** form of `Work.Pert.pert2v2.gate_coord_close_minus`: the perturbed Fatou coordinate
on the lower gate `Qm Ξ' α` converges, as `f → f₀`, to *any* Fatou coordinate `Ψ` of the model map
`F₀ = τ₀ ∘ f₀ ∘ τ₀` on the left region `Qreg none (some (-(Ξ')))`, **up to its own value at a fixed
base point** `z₀` of that region:

  `‖(Φm ζ - Φm z₀) - (Ψ ζ - Ψ z₀)‖ < ε`   for `ζ ∈ K`.

The proof is *literally* the contradiction argument of `gate_coord_close_minus` with the model
coordinate `PhiMinus d` replaced by the arbitrary coordinate `Ψ`: shift every counterexample
coordinate by the constant `Ψ z₀ - Φm z₀` (so that it is pinned at `z₀` with the value `Ψ z₀`),
feed the sequence to `MandelDim.FatouContinuityL1` with limit coordinate `Ψ` (which is a Fatou
coordinate by hypothesis), and observe that the shift cancels in the base-point difference.
-/

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

theorem gate_coord_close_minus_gen {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
      ∀ Ψ : ℂ → ℂ,
      MandelDim.IsFatouCoordOn
        (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
        Ψ (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) →
      ∀ z₀ : ℂ, z₀ ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) →
      ∀ K : Set ℂ, IsCompact K → K ⊆ MandelDim.Qreg none (some (-(Ξ' : ℂ))) →
      ∀ ε : ℝ, 0 < ε →
        ∃ ρmin : ℝ, 0 < ρmin ∧
        ∀ L : Set ℂ, IsCompact L → L ⊆ D₀ →
        ∀ ρ : ℝ, ρmin ≤ ρ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
        ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (Φm : ℂ → ℂ),
          MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
          α = MandelDim.rotOf f →
          DifferentiableOn ℂ u (Metric.ball 0 ρ) →
          (∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
          (∀ z ∈ Metric.ball 0 ρ, f z = z + z * (z - σ) * u z) →
          1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
          (∀ z ∈ Work.Pert.Qm Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 ρ) →
          MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) →
          MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ' α) →
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ' α) →
          ∀ ζ ∈ K, ‖(Φm ζ - Φm z₀) - (Ψ ζ - Ψ z₀)‖ < ε := by
  classical
  -- the narrow (L¹) contract
  obtain ⟨-, -, -, hContL1, -, -⟩ := MandelDim.fatouL1_of_fatou hF
  -- `F₀ = τ₀ ∘ f₀ ∘ τ₀` is a near translation with integrable defect on the left cone
  obtain ⟨ξN, hξNpos, -, -, -, hNT0L⟩ := Work.Pert.nearTranslation_F0 hd
  -- the perturbed lifts converge to `F₀` on compacts of the left cone, with a uniform radius
  obtain ⟨ξC, hξCpos, r, hrpos, hClose⟩ :=
    Work.Pert.tendsto_uniformly_liftF_F0_left_uniform_r hd
  -- the rotation number is controlled by the closeness on a compact
  obtain ⟨r₀, hr₀pos, Cα, hCαpos, hRotB⟩ := Work.Pert.rotOf_bound_of_nearOn_compact hd
  refine ⟨max (max ξN ξC) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun Ξ' hΞ' => ?_⟩
  have hξNΞ : ξN ≤ Ξ' := le_trans (le_trans (le_max_left ξN ξC) (le_max_left _ _)) hΞ'
  have hξCΞ : ξC ≤ Ξ' := le_trans (le_trans (le_max_right ξN ξC) (le_max_left _ _)) hΞ'
  intro Ψ hΦ₀ z₀ hz₀Q K hKc hKQ ε hε
  -- `F₀` is an `L¹` near-translation on the left cone `Ξ'`
  have hNT0' : MandelDim.NearTranslationL1 (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
      (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) :=
    Work.Pert.NearTranslationL1.mono hNT0L (qreg_left_mono hξNΞ)
  have hqadm : MandelDim.QAdm (none : Option ℂ) (some (-(Ξ' : ℂ))) := by
    intro a ha
    simp at ha
  refine ⟨max r 1, lt_of_lt_of_le hrpos (le_max_left _ _), fun L hLc hLD0 ρ hρ hρball => ?_⟩
  have hρr : r ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρpos : 0 < ρ := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hρ
  -- it suffices to derive a contradiction from every sequence of counterexamples
  refine exists_pos_forall_of_forall_seq_coord' ?_
  intro δ hδpos hδlim F D U S A Pp hnotP
  -- unpack the hypotheses of the counterexamples
  have hH : ∀ n, MandelDim.NearOn f₀ (F n) (D n) L (δ n) ∧ (F n) 0 = 0 ∧
      MandelDim.InF1 (MandelDim.rotOf (F n)) ∧ A n = MandelDim.rotOf (F n) ∧
      DifferentiableOn ℂ (U n) (Metric.ball (0 : ℂ) ρ) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖U n z‖ ∧ ‖U n z‖ ≤ 2) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, F n z = z + z * (z - S n) * U n z) ∧
      1 - S n * U n 0 = Complex.exp (2 * Real.pi * Complex.I * (A n)) ∧
      (∀ z ∈ Work.Pert.Qm Ξ' (A n), Work.Pert.tauC (S n) (A n) z ∈ Metric.ball (0 : ℂ) ρ) ∧
      MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / (A n))) (some (-(Ξ' : ℂ))) ∧
      MandelDim.NearTranslationL1 (Work.Pert.liftF (U n) (S n) (A n)) (Work.Pert.Qm Ξ' (A n)) ∧
      MandelDim.IsFatouCoordOn (Work.Pert.liftF (U n) (S n) (A n)) (Pp n)
        (Work.Pert.Qm Ξ' (A n)) :=
    fun n => by
      by_contra hc
      exact hnotP n (fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
        absurd ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ hc)
  have hNear : ∀ n, MandelDim.NearOn f₀ (F n) (D n) L (δ n) := fun n => (hH n).1
  have hf0 : ∀ n, F n 0 = 0 := fun n => (hH n).2.1
  have hInF1 : ∀ n, MandelDim.InF1 (MandelDim.rotOf (F n)) := fun n => (hH n).2.2.1
  have hAeq : ∀ n, A n = MandelDim.rotOf (F n) := fun n => (hH n).2.2.2.1
  have hQAdm : ∀ n, MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / (A n))) (some (-(Ξ' : ℂ))) :=
    fun n => (hH n).2.2.2.2.2.2.2.2.2.1
  have hNT : ∀ n, MandelDim.NearTranslationL1 (Work.Pert.liftF (U n) (S n) (A n))
      (Work.Pert.Qm Ξ' (A n)) := fun n => (hH n).2.2.2.2.2.2.2.2.2.2.1
  have hΦmn : ∀ n, MandelDim.IsFatouCoordOn (Work.Pert.liftF (U n) (S n) (A n)) (Pp n)
      (Work.Pert.Qm Ξ' (A n)) := fun n => (hH n).2.2.2.2.2.2.2.2.2.2.2
  -- the badness of each counterexample, read at the base-point difference
  have hBad : ∀ n, ∃ ζ : ℂ, ζ ∈ K ∧
      ε ≤ ‖(Pp n ζ - Pp n z₀) - (Ψ ζ - Ψ z₀)‖ := by
    intro n
    by_contra hc
    push Not at hc
    exact hnotP n (fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      fun ζ hζK => hc ζ hζK)
  -- the sequence of rotation numbers tends to `0`
  have hδtend : ∀ᶠ n in atTop, 2 * δ n < min ρ r₀ := by
    have h2 : 0 < min ρ r₀ := lt_min hρpos hr₀pos
    have hlim2 : Tendsto (fun n : ℕ => 2 * δ n) atTop (𝓝 0) := by
      simpa using hδlim.const_mul 2
    exact hlim2.eventually (isOpen_Iio.mem_nhds h2)
  have hrotT : ∀ᶠ n in atTop, ‖MandelDim.rotOf (F n)‖ ≤ Cα * (δ n / min ρ r₀) := by
    filter_upwards [hδtend] with n hn
    exact hRotB hLc hLD0 hρpos hρball (hδpos n) hn.le (hNear n) (hf0 n)
      (hH n).2.2.2.2.1 (hH n).2.2.2.2.2.1 (hH n).2.2.2.2.2.2.1
  have hA_tend0 : Tendsto (fun n : ℕ => ‖A n‖) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => Cα * (δ n / min ρ r₀)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Cα * (δ n / min ρ r₀)) atTop
          (𝓝 (Cα * (0 / min ρ r₀))) :=
        (hδlim.div_const (min ρ r₀)).const_mul Cα
      simpa using h1
    have hrot0 : Tendsto (fun n : ℕ => MandelDim.rotOf (F n)) atTop (𝓝 0) :=
      squeeze_zero_norm' hrotT hlim
    have heq : (fun n : ℕ => MandelDim.rotOf (F n)) =ᶠ[atTop] (fun n : ℕ => A n) :=
      Filter.Eventually.of_forall fun n => (hAeq n).symm
    have h1 : Tendsto (fun n : ℕ => A n) atTop (𝓝 0) := hrot0.congr' heq
    simpa using h1.norm
  -- the counterexample coordinates, shifted so that they are pinned at `z₀` with the model value
  set Φ₀ : ℂ → ℂ := Ψ with hΦ₀def
  have hΦ₀c : MandelDim.IsFatouCoordOn (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Φ₀
      (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) := hΦ₀
  set Φs : ℕ → ℂ → ℂ := fun n z => Pp n z + (Φ₀ z₀ - Pp n z₀) with hΦsdef
  have hΦs : ∀ n, MandelDim.IsFatouCoordOn (Work.Pert.liftF (U n) (S n) (A n)) (Φs n)
      (Work.Pert.Qm Ξ' (A n)) := fun n =>
    MandelDim.IsFatouCoordOn.add_const (hΦmn n) (Φ₀ z₀ - Pp n z₀)
  have hΦs0 : ∀ᶠ n in atTop, Φs n z₀ = Φ₀ z₀ := by
    filter_upwards with n
    simp only [hΦsdef]
    ring
  -- the hypothesis of `FatouContinuityL1`: compacts of the left cone are eventually inside the
  -- gates `Qm Ξ' αₙ`, and the lifts converge uniformly on them
  have hconvH : ∀ K' ⊆ MandelDim.Qreg none (some (-(Ξ' : ℂ))), IsCompact K' →
      (∀ᶠ n in atTop, K' ⊆ MandelDim.Qreg (some ((Ξ' : ℂ) - 1 / (A n))) (some (-(Ξ' : ℂ)))) ∧
      TendstoUniformlyOn (fun n => Work.Pert.liftF (U n) (S n) (A n))
        (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) atTop K' := by
    intro K' hK'Q hK'c
    constructor
    · -- the gate `Qm Ξ' αₙ` swallows the compact `K'` once `Re (1/αₙ)` is large
      obtain ⟨R, hRpos, hRQm⟩ := subset_Qm_of_inv_re_ge hK'c hK'Q
      have hsmall : ∀ᶠ n in atTop, ‖A n‖ ≤ 1 / (2 * R) := by
        have hlt : ∀ᶠ n in atTop, ‖A n‖ < 1 / (2 * R) :=
          hA_tend0.eventually (isOpen_Iio.mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * R)))
        filter_upwards [hlt] with n hn
        exact hn.le
      filter_upwards [hsmall] with n hn
      have hInF1n : MandelDim.InF1 (A n) := by rw [hAeq n]; exact hInF1 n
      exact hRQm (A n) (Work.Pert.inv_re_ge_of_norm_le' hInF1n hRpos hn)
    · -- the lifts converge uniformly on `K'`
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε' hε'
      -- the limit theorem, with the uniform radius `r`
      obtain ⟨η, hηpos, hkey⟩ := hClose K' hK'c (fun z hz => qreg_left_mono hξCΞ (hK'Q hz)) ε' hε'
      -- the `C⁰`-closeness of `u` to `(f₀ - id)/z²`, with tolerance `η` at the radius `r`
      obtain ⟨δ₁, hδ₁pos, huc⟩ := Work.Pert.u_close_of_nearOn hd hrpos hηpos
      have hballrL : Metric.closedBall (0 : ℂ) r ⊆ L :=
        fun z hz => hρball (Metric.closedBall_subset_closedBall hρr hz)
      have hev1 : ∀ᶠ n in atTop, δ n < δ₁ := hδlim.eventually (isOpen_Iio.mem_nhds hδ₁pos)
      have hev2 : ∀ᶠ n in atTop, ‖A n‖ < η :=
        hA_tend0.eventually (isOpen_Iio.mem_nhds hηpos)
      filter_upwards [hev1, hev2] with n hn1 hn2 w hw
      have hαne : A n ≠ 0 := by
        have h1 : MandelDim.InF1 (A n) := by rw [hAeq n]; exact hInF1 n
        simp only [MandelDim.InF1] at h1
        intro h0
        rw [h0] at h1
        simp at h1
      have hudiff : DifferentiableOn ℂ (U n) (Metric.ball (0 : ℂ) r) :=
        (hH n).2.2.2.2.1.mono (Metric.ball_subset_ball hρr)
      have hcl := hkey (u := U n) (σ := S n) (α := A n) hαne hn2.le
        (hH n).2.2.2.2.2.2.2.1 hudiff
        (huc (F n) (D n) L (U n) (S n) hLc hballrL hLD0
          (Work.Pert.NearOn.mono_delta (hNear n) hn1.le) (hf0 n) hudiff
          (fun z hz => (hH n).2.2.2.2.2.1 z (Metric.ball_subset_ball hρr hz))
          (fun z hz => (hH n).2.2.2.2.2.2.1 z (Metric.ball_subset_ball hρr hz)))
        w hw
      simpa [dist_eq_norm, norm_sub_rev] using hcl
  -- `FatouContinuityL1` on the sequence of gates `Qm Ξ' αₙ → Qreg none (some (-Ξ'))`
  have hKconv : TendstoUniformlyOn Φs Φ₀ atTop K :=
    hContL1 (fun n => some ((Ξ' : ℂ) - 1 / (A n))) (fun n => some (-(Ξ' : ℂ)))
      none (some (-(Ξ' : ℂ))) (fun n => Work.Pert.liftF (U n) (S n) (A n))
      (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Φs Φ₀ z₀
      hQAdm hqadm hNT hNT0' hconvH hΦs hΦ₀c hz₀Q hΦs0 K hKQ hKc
  -- the contradiction
  rw [Metric.tendstoUniformlyOn_iff] at hKconv
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hKconv ε hε)
  obtain ⟨ζ, hζK, hζbad⟩ := hBad N
  have h1 : dist (Φ₀ ζ) (Φs N ζ) < ε := hN N le_rfl ζ hζK
  have h2 : Φs N ζ - Φ₀ ζ = (Pp N ζ - Pp N z₀) - (Φ₀ ζ - Φ₀ z₀) := by
    simp only [hΦsdef]
    ring
  have h3 : ‖(Pp N ζ - Pp N z₀) - (Φ₀ ζ - Φ₀ z₀)‖ < ε := by
    rw [← h2, norm_sub_rev, ← dist_eq_norm]
    exact h1
  have h3' : ε ≤ ‖(Pp N ζ - Pp N z₀) - (Φ₀ ζ - Φ₀ z₀)‖ := hζbad
  linarith

end

end Work.Pert.pert2v2
