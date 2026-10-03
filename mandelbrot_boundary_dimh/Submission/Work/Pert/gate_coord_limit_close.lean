import Mathlib
import Submission.Work.Pert.limitCoord_plus_exists
import Submission.Work.Pert.nearTranslation_F0
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.rotOf_bound_of_nearOn_compact
import Submission.Work.Pert.liftF_uniform_close_uniform_radius
import Submission.Work.Interfaces.FatouNarrow

/-!
# PERT · `Work.Pert.gate_coord_limit_close`

The perturbed Fatou coordinate on the upper gate `Qp Ξ' α` is `ε`-close to the datum's coordinate
`d.Φ ∘ τ₀` on any compact `K` of the limit cone `Qreg (some Ξ') none` whose `τ₀`-image lies in the
parabolic basin.

The argument is a compactness/continuity argument along the family `α → 0` (i.e. `Re (1/α) → ∞`),
in the shape prescribed by `MandelDim.FatouContinuityL1`:

* the *limit* region is the cone `Qreg (some Ξ') none`, where `F₀ = τ₀ ∘ f₀ ∘ τ₀` is a near
  translation with integrable defect (`Work.Pert.nearTranslation_F0`) and where the limit
  coordinate `Φ₀` with `Φ₀ u = d.Φ (τ₀ u)` on the basin part is supplied by
  `Work.Pert.limitCoord_plus_exists`;
* along a sequence of counterexamples, the perturbed lifts `liftF uₙ σₙ αₙ` converge to `F₀`
  uniformly on compact subsets of the cone (`Work.Pert.liftF_uniform_close_uniform_radius`), the
  gates `Qp Ξ' αₙ` swallow every fixed compact of the cone (because `Re (1/αₙ) → ∞`, which follows
  from `‖rotOf fₙ‖ → 0` via `Work.Pert.rotOf_bound_of_nearOn_compact`), and the moving Fatou
  coordinates, *pinned* at a fixed point `z₀` of the cone, converge to `Φ₀`
  (`MandelDim.FatouContinuityL1`).
-/

namespace Work.Pert

open _root_.MandelDim Complex Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! ## Elementary closure properties -/

/-- `NearOn` is monotone in the tolerance. -/
theorem NearOn.mono_delta {f₀ f : ℂ → ℂ} {Df L : Set ℂ} {δ δ' : ℝ}
    (h : MandelDim.NearOn f₀ f Df L δ) (hle : δ ≤ δ') : MandelDim.NearOn f₀ f Df L δ' :=
  ⟨h.1, h.2.1, h.2.2.1, fun z hz => lt_of_lt_of_le (h.2.2.2 z hz) hle⟩

/-- `NearTranslationOn` restricts to subsets. -/
theorem NearTranslationOn.mono {F : ℂ → ℂ} {Q Q' : Set ℂ} (h : MandelDim.NearTranslationOn F Q)
    (hsub : Q' ⊆ Q) : MandelDim.NearTranslationOn F Q' :=
  ⟨h.1.mono hsub, fun z hz => h.2 z (hsub hz)⟩

/-- `NearTranslationL1` restricts to subsets. -/
theorem NearTranslationL1.mono {F : ℂ → ℂ} {Q Q' : Set ℂ} (h : MandelDim.NearTranslationL1 F Q)
    (hsub : Q' ⊆ Q) : MandelDim.NearTranslationL1 F Q' :=
  ⟨NearTranslationOn.mono h.1 hsub, fun x hx => h.2 x (fun y => hsub (hx y))⟩

/-- **`Re (1/α)` is large when `α` is small in the class `𝓕₁`.**  For `|α.im| < α.re` and
`‖α‖ ≤ c` one has `1/(2c) ≤ Re (1/α)`. -/
theorem inv_re_ge_of_norm_le {α : ℂ} (hIn : MandelDim.InF1 α) {c : ℝ} (h : ‖α‖ ≤ c) :
    1 / (2 * c) ≤ (1 / α).re := by
  unfold MandelDim.InF1 at hIn
  have hre : 0 < α.re := by linarith [abs_nonneg α.im]
  have hne : α ≠ 0 := fun h0 => by rw [h0] at hre; simp at hre
  have hnpos : 0 < ‖α‖ := norm_pos_iff.mpr hne
  have h2c : 0 < 2 * c := by linarith
  have him2 : α.im ^ 2 < α.re ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hre]
    exact hIn
  have hsq : ‖α‖ ^ 2 = α.re ^ 2 + α.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hrec : α.re ≤ c := le_trans (Complex.re_le_norm α) h
  have hkey : ‖α‖ ^ 2 ≤ α.re * (2 * c) := by
    rw [hsq]; nlinarith [him2, hre, hrec]
  have hpos : 0 < ‖α‖ ^ 2 := pow_pos hnpos 2
  have h1 : (1 / α).re = α.re / ‖α‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.sq_norm]
  have hstep : ‖α‖ ^ 2 / (2 * c) ≤ α.re := by
    rw [div_le_iff₀ h2c]; linarith [hkey]
  rw [h1]
  calc 1 / (2 * c) = (‖α‖ ^ 2 / (2 * c)) / ‖α‖ ^ 2 := by field_simp
      _ ≤ α.re / ‖α‖ ^ 2 := div_le_div_of_nonneg_right hstep hpos.le

/-- The normalization of `inv_re_ge_of_norm_le` used below: `‖α‖ ≤ 1/(2R)` gives `Re (1/α) ≥ R`. -/
theorem inv_re_ge_of_norm_le' {α : ℂ} (hIn : MandelDim.InF1 α) {R : ℝ} (hR : 0 < R)
    (h : ‖α‖ ≤ 1 / (2 * R)) : R ≤ (1 / α).re := by
  have hc : 0 < 1 / (2 * R) := by positivity
  have h1 := inv_re_ge_of_norm_le hIn h
  have h2 : 1 / (2 * (1 / (2 * R))) = R := by field_simp
  rwa [h2] at h1

/-- **The gate `Qp ξ α` swallows a fixed compact of the cone once `Re (1/α)` is large.** -/
theorem subset_Qp_of_inv_re_ge {ξ : ℝ} {K : Set ℂ} (hKc : IsCompact K)
    (hK : K ⊆ MandelDim.Qreg (some (ξ : ℂ)) none) :
    ∃ R : ℝ, 0 < R ∧ ∀ α : ℂ, R ≤ (1 / α).re → K ⊆ Work.Pert.Qp ξ α := by
  obtain ⟨C, hC⟩ := hKc.isBounded.exists_norm_le
  refine ⟨max (C + ξ + 1) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun α hα z hz => ?_⟩
  rw [Work.Pert.Qp_mem_iff]
  have hzre : z.re ≤ C := le_trans (Complex.re_le_norm z) (hC z hz)
  have hcone : ξ - |z.im| < z.re := by
    have h : ξ < z.re + |z.im| := by
      have h1 := hK hz
      rwa [Work.Pert.mem_Qreg_cone] at h1
    linarith
  have hR : C + ξ + 1 ≤ (1 / α).re := le_trans (le_max_left _ _) hα
  exact ⟨hcone, by linarith [hR, hzre, abs_nonneg (z.im - (1 / α).im)]⟩

/-- **Sequential criterion.**  To produce a *neighbourhood* `δ₀` from a sequential statement, it
suffices to contradict every sequence with `δₙ → 0⁺`. -/
theorem exists_pos_forall_of_forall_seq {P : ℝ → (ℂ → ℂ) → Set ℂ → (ℂ → ℂ) → ℂ → ℂ → Prop}
    (h : ∀ (δ : ℕ → ℝ), (∀ n, 0 < δ n) → Tendsto δ atTop (𝓝 0) →
      ∀ (F : ℕ → ℂ → ℂ) (D : ℕ → Set ℂ) (U : ℕ → ℂ → ℂ) (S A : ℕ → ℂ),
        (∀ n, ¬ P (δ n) (F n) (D n) (U n) (S n) (A n)) → False) :
    ∃ δ₀, 0 < δ₀ ∧ ∀ F D U S A, P δ₀ F D U S A := by
  by_contra hc
  push Not at hc
  have hseq : ∀ n : ℕ, ∃ (F : ℂ → ℂ) (D : Set ℂ) (U : ℂ → ℂ) (S A : ℂ),
      ¬ P (1 / ((n : ℝ) + 1)) F D U S A :=
    fun n => hc (1 / ((n : ℝ) + 1)) (by positivity)
  choose F D U S A hspec using hseq
  exact h (fun n => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat F D U S A hspec

/-! ## The limit cone is nonempty and the limit data are legal -/

theorem base_point_mem {ξ : ℝ} : ((ξ + 1 : ℝ) : ℂ) ∈ MandelDim.Qreg (some (ξ : ℂ)) none := by
  rw [Work.Pert.mem_Qreg_cone]
  simp

theorem QAdm_cone_none {a : ℂ} : MandelDim.QAdm (some a) none := by
  intro b _ c hc
  simp at hc

/-! ## The main theorem -/

theorem gate_coord_limit_close {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
      ∀ K : Set ℂ, IsCompact K → K ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none →
      ∀ ε : ℝ, 0 < ε → ∃ ρmin : ℝ, 0 < ρmin ∧
      ∀ L : Set ℂ, IsCompact L → L ⊆ D₀ →
      ∀ ρ : ℝ, ρmin ≤ ρ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 →
        MandelDim.InF1 (MandelDim.rotOf f) → α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ) →
        (∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) ρ, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qp Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) ρ) →
        MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / α)) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qp Ξ' α) →
        ∃ Φp : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φp (Work.Pert.Qp Ξ' α) ∧
          ∀ ζ ∈ K, MandelDim.tau0 ζ ∈ MandelDim.ParabolicBasin f₀ D₀ →
            ‖Φp ζ - d.Φ (MandelDim.tau0 ζ)‖ < ε := by
  classical
  -- the narrow (L¹) contract
  obtain ⟨hExistsL1, -, -, hContL1, -, -⟩ := MandelDim.fatouL1_of_fatou hF
  -- the limit coordinate on the cone
  obtain ⟨ξL, hξLpos, hLim⟩ := Work.Pert.limitCoord_plus_exists d hd
  -- `F₀ = τ₀ ∘ f₀ ∘ τ₀` is a near translation with integrable defect on the cone
  obtain ⟨ξN, hξNpos, -, -, hNT0, -⟩ := Work.Pert.nearTranslation_F0 hd
  -- the perturbed lifts converge to `F₀` on compacts of the cone, with a uniform radius
  obtain ⟨ξC, hξCpos, ρ₀, hρ₀pos, hClose⟩ :=
    Work.Pert.liftF_uniform_close_uniform_radius hd
  -- the rotation number is controlled by the closeness on a compact
  obtain ⟨r₀, hr₀pos, Cα, hCαpos, hRotB⟩ := Work.Pert.rotOf_bound_of_nearOn_compact hd
  refine ⟨max (max ξL ξN) (max ξC 1),
    lt_of_lt_of_le hξLpos (le_trans (le_max_left _ _) (le_max_left _ _)), fun Ξ' hΞ' => ?_⟩
  have hξLΞ : ξL ≤ Ξ' := le_trans (le_trans (le_max_left ξL ξN) (le_max_left _ _)) hΞ'
  have hξNΞ : ξN ≤ Ξ' := le_trans (le_trans (le_max_right ξL ξN) (le_max_left _ _)) hΞ'
  have hξCΞ : ξC ≤ Ξ' := le_trans (le_trans (le_max_left ξC 1) (le_max_right _ _)) hΞ'
  -- the limit coordinate `Φ₀` and its identification with `d.Φ ∘ τ₀` on the basin
  obtain ⟨Φ₀, hΦ₀c, hΦ₀v⟩ := hLim Ξ' hξLΞ
  -- `F₀` is an L¹ near-translation on the cone `Ξ'`
  have hNT0' : MandelDim.NearTranslationL1 (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
      (MandelDim.Qreg (some (Ξ' : ℂ)) none) :=
    NearTranslationL1.mono hNT0 (Work.Pert.Qreg_cone_mono hξNΞ)
  intro K hKc hKQ ε hε
  refine ⟨max ρ₀ 1, lt_of_lt_of_le hρ₀pos (le_max_left _ _), fun L hLc hLD0 ρ hρ hρball => ?_⟩
  have hρρ₀ : ρ₀ ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρpos : 0 < ρ := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right _ _)) hρ
  -- it suffices to derive a contradiction from every sequence of counterexamples
  refine exists_pos_forall_of_forall_seq ?_
  intro δ hδpos hδlim F D U S A hnotP
  -- unpack the hypotheses of the counterexamples
  have hH : ∀ n, MandelDim.NearOn f₀ (F n) (D n) L (δ n) ∧ (F n) 0 = 0 ∧
      MandelDim.InF1 (MandelDim.rotOf (F n)) ∧ A n = MandelDim.rotOf (F n) ∧
      DifferentiableOn ℂ (U n) (Metric.ball (0 : ℂ) ρ) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖U n z‖ ∧ ‖U n z‖ ≤ 2) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, F n z = z + z * (z - S n) * U n z) ∧
      1 - S n * U n 0 = Complex.exp (2 * Real.pi * Complex.I * (A n)) ∧
      (∀ z ∈ Work.Pert.Qp Ξ' (A n), Work.Pert.tauC (S n) (A n) z ∈ Metric.ball (0 : ℂ) ρ) ∧
      MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / (A n))) ∧
      MandelDim.NearTranslationL1 (Work.Pert.liftF (U n) (S n) (A n)) (Work.Pert.Qp Ξ' (A n)) :=
    fun n => by
      by_contra hc
      exact hnotP n (fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
        absurd ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ hc)
  have hNear : ∀ n, MandelDim.NearOn f₀ (F n) (D n) L (δ n) := fun n => (hH n).1
  have hf0 : ∀ n, F n 0 = 0 := fun n => (hH n).2.1
  have hInF1 : ∀ n, MandelDim.InF1 (MandelDim.rotOf (F n)) := fun n => (hH n).2.2.1
  have hAeq : ∀ n, A n = MandelDim.rotOf (F n) := fun n => (hH n).2.2.2.1
  have hQAdm : ∀ n, MandelDim.QAdm (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / (A n))) :=
    fun n => (hH n).2.2.2.2.2.2.2.2.2.1
  have hNT : ∀ n, MandelDim.NearTranslationL1 (Work.Pert.liftF (U n) (S n) (A n))
      (Work.Pert.Qp Ξ' (A n)) := fun n => (hH n).2.2.2.2.2.2.2.2.2.2
  -- the badness of each counterexample
  have hBad : ∀ n, ∀ Φp : ℂ → ℂ,
      MandelDim.IsFatouCoordOn (Work.Pert.liftF (U n) (S n) (A n)) Φp (Work.Pert.Qp Ξ' (A n)) →
      ∃ ζ : ℂ, ζ ∈ K ∧ MandelDim.tau0 ζ ∈ MandelDim.ParabolicBasin f₀ D₀ ∧
        ε ≤ ‖Φp ζ - d.Φ (MandelDim.tau0 ζ)‖ := by
    intro n Φp hΦ
    by_contra hc
    push Not at hc
    exact hnotP n (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨Φp, hΦ, hc⟩)
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
  -- the moving coordinates, pinned at the fixed point `z₀` of the cone
  choose Ψ hΨspec using fun n => hExistsL1 (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / (A n)))
    (Work.Pert.liftF (U n) (S n) (A n)) (hQAdm n) (hNT n)
  have hΨ : ∀ n, MandelDim.IsFatouCoordOn (Work.Pert.liftF (U n) (S n) (A n)) (Ψ n)
      (Work.Pert.Qp Ξ' (A n)) := fun n => (hΨspec n).1
  set z₀ : ℂ := ((Ξ' + 1 : ℝ) : ℂ) with hz₀def
  have hz₀mem : z₀ ∈ MandelDim.Qreg (some (Ξ' : ℂ)) none := by
    rw [hz₀def]; exact base_point_mem
  set Φs : ℕ → ℂ → ℂ := fun n z => Ψ n z + (Φ₀ z₀ - Ψ n z₀) with hΦsdef
  have hΦs : ∀ n, MandelDim.IsFatouCoordOn (Work.Pert.liftF (U n) (S n) (A n)) (Φs n)
      (Work.Pert.Qp Ξ' (A n)) := fun n =>
    MandelDim.IsFatouCoordOn.add_const (hΨ n) (Φ₀ z₀ - Ψ n z₀)
  have hΦs0 : ∀ᶠ n in atTop, Φs n z₀ = Φ₀ z₀ := by
    filter_upwards with n
    simp only [hΦsdef]
    ring
  -- the hypothesis of `FatouContinuityL1`: compacts of the cone are eventually inside the gates,
  -- and the lifts converge uniformly on them
  have hconvH : ∀ K' ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) none, IsCompact K' →
      (∀ᶠ n in atTop, K' ⊆ MandelDim.Qreg (some (Ξ' : ℂ)) (some (-(Ξ' : ℂ) + 1 / (A n)))) ∧
      TendstoUniformlyOn (fun n => Work.Pert.liftF (U n) (S n) (A n))
        (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) atTop K' := by
    intro K' hK'Q hK'c
    constructor
    · -- the gate `Qp Ξ' αₙ` swallows the compact `K'` once `Re (1/αₙ)` is large
      obtain ⟨R, hRpos, hRQp⟩ := subset_Qp_of_inv_re_ge hK'c hK'Q
      have hsmall : ∀ᶠ n in atTop, ‖A n‖ ≤ 1 / (2 * R) := by
        have hlt : ∀ᶠ n in atTop, ‖A n‖ < 1 / (2 * R) :=
          hA_tend0.eventually (isOpen_Iio.mem_nhds (by positivity : (0:ℝ) < 1 / (2 * R)))
        filter_upwards [hlt] with n hn
        exact hn.le
      filter_upwards [hsmall] with n hn
      refine hRQp (A n) ?_
      rw [hAeq n]
      exact inv_re_ge_of_norm_le' (hInF1 n) hRpos (by rw [← hAeq n]; exact hn)
    · -- the lifts converge uniformly on `K'`
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε' hε'
      obtain ⟨δ₀', hδ₀'pos, hδ₀'⟩ :=
        hClose Ξ' hξCΞ K' hK'c hK'Q ε' hε' ρ hρρ₀ L hLc hLD0 hρball
      have hev : ∀ᶠ n in atTop, δ n < δ₀' :=
        hδlim.eventually (isOpen_Iio.mem_nhds hδ₀'pos)
      filter_upwards [hev] with n hn w hw
      have hcl := hδ₀' (F n) (D n) (U n) (S n) (A n)
        (NearOn.mono_delta (hNear n) hn.le) (hf0 n) (hInF1 n) (hAeq n)
        (hH n).2.2.2.2.1 (hH n).2.2.2.2.2.1 (hH n).2.2.2.2.2.2.1
        (hH n).2.2.2.2.2.2.2.1 w hw
      simpa [dist_eq_norm, norm_sub_rev] using hcl
  -- `FatouContinuityL1` on the sequence of gates `Qp Ξ' αₙ → Qreg (some Ξ') none`
  have hKconv : TendstoUniformlyOn Φs Φ₀ atTop K :=
    hContL1 (fun n => some (Ξ' : ℂ)) (fun n => some (-(Ξ' : ℂ) + 1 / (A n)))
      (some (Ξ' : ℂ)) none (fun n => Work.Pert.liftF (U n) (S n) (A n))
      (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w))) Φs Φ₀ z₀
      hQAdm QAdm_cone_none hNT hNT0' hconvH hΦs hΦ₀c hz₀mem hΦs0 K hKQ hKc
  -- the contradiction
  rw [Metric.tendstoUniformlyOn_iff] at hKconv
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hKconv ε hε)
  obtain ⟨ζ, hζK, hζbasin, hζbad⟩ := hBad N (Φs N) (hΦs N)
  have h1 : dist (Φ₀ ζ) (Φs N ζ) < ε := hN N le_rfl ζ hζK
  have h2 : Φ₀ ζ = d.Φ (MandelDim.tau0 ζ) := hΦ₀v ζ (hKQ hζK) hζbasin
  have h3 : ‖Φs N ζ - d.Φ (MandelDim.tau0 ζ)‖ < ε := by
    rw [← h2, norm_sub_rev, ← dist_eq_norm]
    exact h1
  linarith

end

end Work.Pert
