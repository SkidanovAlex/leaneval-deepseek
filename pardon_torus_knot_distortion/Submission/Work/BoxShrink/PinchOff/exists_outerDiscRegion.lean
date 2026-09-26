import Mathlib
import Submission.Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential
import Submission.Work.Smooth.Schoenflies.All
import Submission.Work.TorusCover.Main
import Submission.Work.SphereJordan.unboundedDisc
import Submission.Work.Smooth.SphereJordan.exists_outerDisc
import Submission.Work.SurgeryInvariance.DiscRegion.not_isEssential
import Submission.Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen
import Submission.Work.BoxShrink.PinchOff.lattice_separated_of_isCompact
import Submission.Work.BoxShrink.PinchOff.exists_annulus_close_to_circle
import Submission.Work.BoxShrink.PinchOff.exists_unc

open Set LeanEval.KnotTheory.PardonDistortion

namespace Work.BoxShrink.PinchOff

noncomputable section

private theorem circlePoint_norm (θ : ℝ) :
    ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

theorem exists_outerDiscRegion {P : Work.CoreTopology.ParamTorus}
    (D : Work.SurgeryInvariance.DiscRegion P)
    {N : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hN : Work.SurgeryInvariance.IsOpenInCarrier P N) (hsub : D.boundary ⊆ N) :
    ∃ D₂ : Work.SurgeryInvariance.DiscRegion P,
      D.carrier ⊆ D₂.interior ∧ D₂.boundary ⊆ N := by
  classical
  obtain ⟨Ξ, hΞ⟩ := Work.SurgeryInvariance.DiscRegion.exists_lift_disc D
  have hΞinj : Function.Injective Ξ := by
    intro a b hab
    apply D.inj
    rw [← hΞ a, ← hΞ b, hab]
  let F : C(Metric.closedBall (0 : ℂ) 1, ℂ) :=
    ⟨fun z => ofR2 (Ξ z), continuous_ofR2.comp Ξ.continuous⟩
  have hFinj : Function.Injective F := fun a b h => hΞinj (ofR2_injective h)
  obtain ⟨e, w₀, heinj, hebd, hwlt, hwe, hErange⟩ :=
    Work.Smooth.SphereJordan.exists_outerDisc F hFinj
  obtain ⟨unc, hunc_coe, hunc_cont⟩ := exists_unc
  let K : Set (ℝ × ℝ) := Set.range Ξ
  let J0 : Set (ℝ × ℝ) := Set.range (fun θ : ℝ => Ξ (Work.Smooth.Jordan.circlePoint θ))
  let hout : Metric.closedBall (0 : ℂ) 1 → ℝ × ℝ := fun z => toR2 (unc (e z))
  have hrangeF : Set.range ⇑F = ofR2 '' K := by
    have h1 : ⇑F = ofR2 ∘ ⇑Ξ := rfl
    rw [h1, Set.range_comp]
  let r : ℝ := (‖(w₀ : ℂ)‖ + 1) / 2
  have hrw : ‖(w₀ : ℂ)‖ < r := by simp only [r]; have := norm_nonneg (w₀ : ℂ); linarith
  have hr0 : 0 < r := by simp only [r]; have := norm_nonneg (w₀ : ℂ); linarith
  have hr1 : r < 1 := by simp only [r]; linarith [hwlt]
  have hzn : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ ≤ 1 := by
    intro z; have h := z.2; rwa [Metric.mem_closedBall, dist_zero_right] at h
  have he_ne_infty : ∀ z : Metric.closedBall (0 : ℂ) 1, r ≤ ‖(z : ℂ)‖ →
      e z ≠ OnePoint.infty := by
    intro z hz hze
    have hzw : z = w₀ := heinj (by rw [hze, hwe])
    rw [hzw] at hz
    exact absurd hz (not_le.mpr hrw)
  have hhout : ContinuousOn hout {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖} := by
    have hmaps : MapsTo e {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖}
        (({OnePoint.infty} : Set (OnePoint ℂ))ᶜ) := by
      intro z hz
      simpa using he_ne_infty z hz
    have h1 : ContinuousOn (fun z : Metric.closedBall (0 : ℂ) 1 => unc (e z))
        {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖} :=
      hunc_cont.comp e.continuous.continuousOn hmaps
    exact continuous_toR2.continuousOn.comp h1 (fun z _ => Set.mem_univ _)
  have hout_circle : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → hout z ∈ J0 := by
    intro z hz
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
    refine ⟨θ, ?_⟩
    rw [← hθ]
    show Ξ (Work.Smooth.Jordan.circlePoint θ)
        = toR2 (unc (e (Work.Smooth.Jordan.circlePoint θ)))
    rw [hebd θ, hunc_coe]
    have hFv : F (Work.Smooth.Jordan.circlePoint θ)
        = ofR2 (Ξ (Work.Smooth.Jordan.circlePoint θ)) := rfl
    rw [hFv, toR2_ofR2]
  have hJ0K : J0 ⊆ K := by rintro _ ⟨θ, rfl⟩; exact ⟨_, rfl⟩
  have hout_circle_K : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → hout z ∈ K :=
    fun z hz => hJ0K (hout_circle z hz)
  haveI hCpt : CompactSpace (Metric.closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  have hKcpt : IsCompact K := isCompact_range Ξ.continuous
  have hsphere_eq : (Set.range (fun θ : ℝ => Work.Smooth.Jordan.circlePoint θ))
      = {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} := by
    ext z
    constructor
    · rintro ⟨θ, rfl⟩
      exact circlePoint_norm θ
    · intro hz
      obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq z hz
      exact ⟨θ, hθ⟩
  have hJ0cpt : IsCompact J0 := by
    have hclosed : IsClosed {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} :=
      isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const
    have heq : J0 = Ξ '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ = 1} := by
      have h2 : J0 = Set.range (⇑Ξ ∘ (fun θ : ℝ => Work.Smooth.Jordan.circlePoint θ)) := rfl
      rw [h2, Set.range_comp, ← hsphere_eq]
    rw [heq]
    exact hclosed.isCompact.image Ξ.continuous
  let W : Set (ℝ × ℝ) := (Work.TorusCover.psiMap P.psi) ⁻¹' N
  have hWopen : IsOpen W := by
    have hcont : Continuous (Work.TorusCover.psiMapToRange P.psi) :=
      (Work.TorusCover.isCoveringMap_psiMapToRange_param P).continuous
    have h1 : IsOpen (Work.TorusCover.psiMapToRange P.psi ⁻¹' (Subtype.val ⁻¹' N)) :=
      hN.preimage hcont
    have hset : Work.TorusCover.psiMapToRange P.psi ⁻¹' (Subtype.val ⁻¹' N) = W := by
      rw [show W = (Work.TorusCover.psiMap P.psi) ⁻¹' N from rfl]
      ext p
      simp [Work.TorusCover.psiMapToRange_apply]
    rwa [hset] at h1
  have hJ0W : J0 ⊆ W := by
    rintro _ ⟨θ, rfl⟩
    show P.psi (Ξ (Work.Smooth.Jordan.circlePoint θ)).1
        (Ξ (Work.Smooth.Jordan.circlePoint θ)).2 ∈ N
    rw [hΞ (Work.Smooth.Jordan.circlePoint θ)]
    exact hsub ⟨Work.Smooth.Jordan.circlePoint θ, circlePoint_norm θ, rfl⟩
  obtain ⟨ρN, hρNpos, hρNsub⟩ :=
    IsCompact.exists_cthickening_subset_open hJ0cpt hWopen hJ0W
  have hKinj : ∀ p ∈ K, ∀ q ∈ K, p - q ∈ Work.TorusCover.lattice → p = q := by
    rintro p ⟨zp, rfl⟩ q ⟨zq, rfl⟩ hpq
    have hm : Work.TorusCover.psiMap P.psi (Ξ zp) = Work.TorusCover.psiMap P.psi (Ξ zq) :=
      (Work.TorusCover.psiMap_eq_iff_param P).mpr hpq
    have h1 : D.e zp = D.e zq := by
      rw [← hΞ zp, ← hΞ zq]
      exact hm
    have h2 : zp = zq := D.inj h1
    rw [h2]
  obtain ⟨δ, hδpos, hδ⟩ :=
    lattice_separated_of_isCompact hKcpt ⟨Ξ 0, ⟨0, rfl⟩⟩ hKinj
  obtain ⟨tK, htKr, htK1, htK⟩ :=
    exists_annulus_close_to_circle hout K r hr1 hhout hout_circle_K δ hδpos
  obtain ⟨tN, htNr, htN1, htN⟩ :=
    exists_annulus_close_to_circle hout J0 r hr1 hhout hout_circle ρN hρNpos
  let t : ℝ := (max tK tN + 1) / 2
  have htmaxK : tK ≤ max tK tN := le_max_left _ _
  have htmaxN : tN ≤ max tK tN := le_max_right _ _
  have htmax1 : max tK tN < 1 := max_lt htK1 htN1
  have htmax_lt_t : max tK tN < t := by simp only [t]; linarith
  have ht1 : t < 1 := by simp only [t]; linarith
  have ht0 : 0 < t := by
    have : 0 < max tK tN := lt_of_lt_of_le hr0 (le_trans htKr htmaxK)
    simp only [t]; linarith
  have htKt : tK ≤ t := le_of_lt (lt_of_le_of_lt htmaxK htmax_lt_t)
  have htNt : tN ≤ t := le_of_lt (lt_of_le_of_lt htmaxN htmax_lt_t)
  have hrt : r ≤ t := le_trans htKr htKt
  have hwt : ‖(w₀ : ℂ)‖ < t := lt_of_lt_of_le hrw hrt
  let σ : ℝ → ℝ := fun s => t + (1 - t) * ((1 - s) / (1 - r))
  have hσcont : Continuous σ := by simp only [σ]; fun_prop
  have hσr : σ r = 1 := by
    simp only [σ]
    rw [div_self (ne_of_gt (show (0 : ℝ) < 1 - r by linarith)), mul_one]
    ring
  have hσ1 : σ 1 = t := by simp only [σ]; ring
  have hσpos : ∀ s : ℝ, s ≤ 1 → 0 < σ s := by
    intro s hs
    have h2 : (0 : ℝ) < 1 - r := by linarith
    have h3 : (0 : ℝ) < 1 - t := by linarith
    have h1 : 0 ≤ (1 - s) / (1 - r) := div_nonneg (by linarith) (le_of_lt h2)
    have h4 : 0 ≤ (1 - t) * ((1 - s) / (1 - r)) := mul_nonneg (le_of_lt h3) h1
    simp only [σ]; linarith [ht0]
  have hσle1 : ∀ s : ℝ, r ≤ s → s ≤ 1 → σ s ≤ 1 := by
    intro s hrs hs
    have h2 : (0 : ℝ) < 1 - r := by linarith
    have h3 : (0 : ℝ) < 1 - t := by linarith
    have h4 : (1 - s) / (1 - r) ≤ 1 := by
      rw [div_le_one h2]; linarith
    have h5 : (1 - t) * ((1 - s) / (1 - r)) ≤ (1 - t) := by
      calc (1 - t) * ((1 - s) / (1 - r)) ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left h4 (le_of_lt h3)
        _ = 1 - t := by ring
    simp only [σ]; linarith
  have hσget : ∀ s : ℝ, s ≤ 1 → t ≤ σ s := by
    intro s hs
    have h2 : (0 : ℝ) < 1 - r := by linarith
    have h3 : (0 : ℝ) < 1 - t := by linarith
    have h1 : 0 ≤ (1 - s) / (1 - r) := div_nonneg (by linarith) (le_of_lt h2)
    have h4 : 0 ≤ (1 - t) * ((1 - s) / (1 - r)) := mul_nonneg (le_of_lt h3) h1
    simp only [σ]; linarith
  have hσlt1 : ∀ s : ℝ, r < s → s ≤ 1 → σ s < 1 := by
    intro s hrs hs
    have h2 : (0 : ℝ) < 1 - r := by linarith
    have h3 : (0 : ℝ) < 1 - t := by linarith
    have h4 : (1 - s) / (1 - r) < 1 := by rw [div_lt_one h2]; linarith
    have h5 : (1 - t) * ((1 - s) / (1 - r)) < (1 - t) := by
      calc (1 - t) * ((1 - s) / (1 - r)) < (1 - t) * 1 := mul_lt_mul_of_pos_left h4 h3
        _ = 1 - t := by ring
    simp only [σ]; linarith
  have hσ_inj : ∀ s₁ s₂ : ℝ, σ s₁ = σ s₂ → s₁ = s₂ := by
    intro s₁ s₂ heq
    simp only [σ] at heq
    have h2 : (0 : ℝ) < 1 - r := by linarith
    have h3 : (0 : ℝ) < 1 - t := by linarith
    have h5 : (1 - s₁) / (1 - r) = (1 - s₂) / (1 - r) := by
      have := add_left_cancel heq
      exact mul_left_cancel₀ (ne_of_gt h3) this
    have h6 : 1 - s₁ = 1 - s₂ := by
      have h7 := (div_eq_div_iff (ne_of_gt h2) (ne_of_gt h2)).mp h5
      exact mul_right_cancel₀ (ne_of_gt h2) h7
    linarith
  let dir : Metric.closedBall (0 : ℂ) 1 → ℂ := fun z => (max ‖(z : ℂ)‖ r)⁻¹ • (z : ℂ)
  have hmz : ∀ z : Metric.closedBall (0 : ℂ) 1, max ‖(z : ℂ)‖ r ≠ 0 :=
    fun z => ne_of_gt (lt_of_lt_of_le hr0 (le_max_right _ _))
  have hdircont : Continuous dir := by
    simp only [dir]
    exact (((continuous_norm.comp continuous_subtype_val).max continuous_const).inv₀ hmz).smul
      continuous_subtype_val
  have hdir_le : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖dir z‖ ≤ 1 := by
    intro z
    have hm : 0 < max ‖(z : ℂ)‖ r := lt_of_lt_of_le hr0 (le_max_right _ _)
    simp only [dir]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hm, inv_mul_le_one₀ hm]
    exact le_max_left _ _
  have hdir_eq : ∀ z : Metric.closedBall (0 : ℂ) 1, r ≤ ‖(z : ℂ)‖ → ‖dir z‖ = 1 := by
    intro z hz
    have hzpos : 0 < ‖(z : ℂ)‖ := lt_of_lt_of_le hr0 hz
    simp only [dir]
    rw [max_eq_left hz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hzpos,
      inv_mul_cancel₀ (ne_of_gt hzpos)]
  have hdir_value : ∀ z : Metric.closedBall (0 : ℂ) 1, r ≤ ‖(z : ℂ)‖ →
      dir z = (‖(z : ℂ)‖)⁻¹ • (z : ℂ) := by
    intro z hz
    simp only [dir]
    rw [max_eq_left hz]
  let φ₁ : Metric.closedBall (0 : ℂ) 1 → Metric.closedBall (0 : ℂ) 1 :=
    fun z => ⟨dir z, by rw [Metric.mem_closedBall, dist_zero_right]; exact hdir_le z⟩
  have hφ₁cont : Continuous φ₁ := by
    simp only [φ₁]; exact hdircont.subtype_mk _
  have hφ₁coe : ∀ z, (φ₁ z : ℂ) = dir z := fun z => rfl
  let f : Metric.closedBall (0 : ℂ) 1 → ℝ × ℝ := fun z => Ξ (φ₁ z)
  have hfcont : Continuous f := Ξ.continuous.comp hφ₁cont
  have hmin_mem : ∀ z : Metric.closedBall (0 : ℂ) 1,
      min (σ ‖(z : ℂ)‖) 1 • dir z ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro z
    rw [Metric.mem_closedBall, dist_zero_right]
    have hpos : 0 < min (σ ‖(z : ℂ)‖) 1 := lt_min (hσpos _ (hzn z)) one_pos
    have hle : min (σ ‖(z : ℂ)‖) 1 ≤ 1 := min_le_right _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    nlinarith [hdir_le z, norm_nonneg (dir z)]
  let φ₂ : Metric.closedBall (0 : ℂ) 1 → Metric.closedBall (0 : ℂ) 1 :=
    fun z => ⟨min (σ ‖(z : ℂ)‖) 1 • dir z, hmin_mem z⟩
  have hφ₂cont : Continuous φ₂ := by
    simp only [φ₂]
    exact (((hσcont.comp (continuous_norm.comp continuous_subtype_val)).min continuous_const).smul
      hdircont).subtype_mk _
  have hφ₂coe : ∀ z, (φ₂ z : ℂ) = min (σ ‖(z : ℂ)‖) 1 • dir z := fun z => rfl
  let g : Metric.closedBall (0 : ℂ) 1 → ℝ × ℝ := fun z => hout (φ₂ z)
  have hφ₂norm : ∀ z : Metric.closedBall (0 : ℂ) 1, r ≤ ‖(z : ℂ)‖ →
      ‖(φ₂ z : ℂ)‖ = σ ‖(z : ℂ)‖ := by
    intro z hz
    rw [hφ₂coe, norm_smul, Real.norm_eq_abs, abs_of_pos (lt_min (hσpos _ (hzn z)) one_pos),
      hdir_eq z hz, min_eq_left (hσle1 _ hz (hzn z)), mul_one]
  have hφ₂ne : ∀ z : Metric.closedBall (0 : ℂ) 1, r ≤ ‖(z : ℂ)‖ → φ₂ z ≠ w₀ := by
    intro z hz hc
    have h1 : ‖(φ₂ z : ℂ)‖ = ‖(w₀ : ℂ)‖ := by rw [hc]
    rw [hφ₂norm z hz] at h1
    have h2 : t ≤ σ ‖(z : ℂ)‖ := hσget _ (hzn z)
    linarith [hwt]
  have hgcont : ContinuousOn g {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖} := by
    have hmaps : MapsTo (fun z => e (φ₂ z)) {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖}
        (({OnePoint.infty} : Set (OnePoint ℂ))ᶜ) := by
      intro z hz
      have hnorm : ‖(φ₂ z : ℂ)‖ = σ ‖(z : ℂ)‖ := hφ₂norm z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro heq
      have hzw : φ₂ z = w₀ := heinj (by rw [heq, hwe])
      have h1 : ‖(w₀ : ℂ)‖ = σ ‖(z : ℂ)‖ := by rw [← hzw, hnorm]
      have h2 : t ≤ σ ‖(z : ℂ)‖ := hσget _ (hzn z)
      linarith [hwt]
    have h0 : ContinuousOn (fun z => e (φ₂ z)) {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖} :=
      (e.continuous.comp hφ₂cont).continuousOn
    have h1 : ContinuousOn (fun z => unc (e (φ₂ z)))
        {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖} :=
      hunc_cont.comp h0 hmaps
    exact continuous_toR2.continuousOn.comp h1 (fun z _ => Set.mem_univ _)
  have hcl_sub : closure ({z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r}ᶜ)
      ⊆ {z : Metric.closedBall (0 : ℂ) 1 | r ≤ ‖(z : ℂ)‖} := by
    apply closure_minimal
    · intro z hz
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hz
      exact le_of_lt hz
    · exact isClosed_le continuous_const (continuous_norm.comp continuous_subtype_val)
  have hgcont' : ContinuousOn g (closure ({z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r}ᶜ)) :=
    hgcont.mono hcl_sub
  have hfront : ∀ z ∈ frontier {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r},
      f z = g z := by
    intro z hz
    have hzle : ‖(z : ℂ)‖ ≤ r := by
      have hcl : closure {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r}
          = {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r} :=
        (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const).closure_eq
      have h : z ∈ closure {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r} := hz.1
      rw [hcl] at h
      exact h
    have hzge : r ≤ ‖(z : ℂ)‖ := by
      by_contra hlt
      rw [not_le] at hlt
      apply hz.2
      have hballsub : Metric.ball (0 : Metric.closedBall (0 : ℂ) 1) r
          ⊆ {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r} := by
        intro y hy
        rw [Metric.mem_ball] at hy
        rw [Subtype.dist_eq] at hy
        have h2 : dist (y : ℂ) (0 : ℂ) < r := hy
        rw [dist_zero_right] at h2
        exact le_of_lt h2
      refine interior_maximal hballsub Metric.isOpen_ball ?_
      rw [Metric.mem_ball, Subtype.dist_eq]
      have h2 : dist (z : ℂ) (0 : ℂ) < r := by
        rw [dist_zero_right]; exact hlt
      exact h2
    have hzr : ‖(z : ℂ)‖ = r := le_antisymm hzle hzge
    have hsub1 : φ₂ z = φ₁ z := by
      apply Subtype.ext
      rw [hφ₂coe, hφ₁coe, hzr, hσr, min_eq_right le_rfl, one_smul]
    have hφ₁norm : ‖(φ₁ z : ℂ)‖ = 1 := by rw [hφ₁coe]; exact hdir_eq z hzge
    obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq (φ₁ z) hφ₁norm
    have hfz : f z = Ξ (φ₁ z) := rfl
    have hgz : g z = hout (φ₁ z) := by show hout (φ₂ z) = hout (φ₁ z); rw [hsub1]
    rw [hfz, hgz, ← hθ]
    show Ξ (Work.Smooth.Jordan.circlePoint θ)
        = toR2 (unc (e (Work.Smooth.Jordan.circlePoint θ)))
    rw [hebd θ, hunc_coe]
    have hFv : F (Work.Smooth.Jordan.circlePoint θ)
        = ofR2 (Ξ (Work.Smooth.Jordan.circlePoint θ)) := rfl
    rw [hFv, toR2_ofR2]
  let G : Metric.closedBall (0 : ℂ) 1 → ℝ × ℝ :=
    Set.piecewise {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r} f g
  have hGcont : Continuous G := by
    simp only [G]
    exact continuous_piecewise hfront hfcont.continuousOn hgcont'
  have hGf : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ ≤ r → G z = Ξ (φ₁ z) := by
    intro z hz
    show (if z ∈ {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r} then f z else g z)
        = Ξ (φ₁ z)
    rw [if_pos (show z ∈ {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r} from hz)]
  have hGg : ∀ z : Metric.closedBall (0 : ℂ) 1, ¬ ‖(z : ℂ)‖ ≤ r → G z = hout (φ₂ z) := by
    intro z hz
    show (if z ∈ {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r} then f z else g z)
        = hout (φ₂ z)
    rw [if_neg (show ¬ (z ∈ {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ ≤ r}) from hz)]
  have hGclose : ∀ z : Metric.closedBall (0 : ℂ) 1, ∃ p' ∈ K, dist (G z) p' < δ := by
    intro z
    by_cases hz : ‖(z : ℂ)‖ ≤ r
    · exact ⟨G z, ⟨φ₁ z, (hGf z hz).symm⟩, by simp [hδpos]⟩
    · have hz' : r ≤ ‖(z : ℂ)‖ := le_of_lt (not_le.mp hz)
      have h1 : tK ≤ ‖(φ₂ z : ℂ)‖ := by
        rw [hφ₂norm z hz']
        exact le_trans htKt (hσget _ (hzn z))
      have h2 : ‖(φ₂ z : ℂ)‖ ≤ 1 := by
        rw [hφ₂norm z hz']; exact hσle1 _ hz' (hzn z)
      obtain ⟨c, hc, hdist⟩ := htK (φ₂ z) h1 h2
      exact ⟨c, hc, by rw [hGg z hz]; exact hdist⟩
  have hψinj : Set.InjOn (Work.TorusCover.psiMap P.psi) (Set.range G) := by
    rintro p ⟨z, rfl⟩ q ⟨z', rfl⟩ hpq
    have hlat : G z - G z' ∈ Work.TorusCover.lattice :=
      (Work.TorusCover.psiMap_eq_iff_param P).mp hpq
    exact hδ (G z) (G z') (hGclose z) (hGclose z') hlat
  have he_subset : e '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}
      ⊆ ({OnePoint.infty} ∪ (fun c : ℂ => (c : OnePoint ℂ)) '' (Set.range ⇑F)ᶜ) := by
    rintro x ⟨z, hz, rfl⟩
    have hx : e z ∈ Set.range ⇑e := ⟨z, rfl⟩
    rw [hErange] at hx
    rcases hx with (hinf | hF) | hcirc
    · exact Or.inl hinf
    · exact Or.inr hF
    · exfalso
      obtain ⟨d, hd, hdz⟩ := hcirc
      obtain ⟨θ, hθ⟩ := hd
      have hze : e z = e (Work.Smooth.Jordan.circlePoint θ) := by
        rw [hebd θ]
        rw [show F (Work.Smooth.Jordan.circlePoint θ) = d from hθ]
        exact hdz.symm
      have hzc : z = Work.Smooth.Jordan.circlePoint θ := heinj hze
      have hzlt : ‖(z : ℂ)‖ < 1 := hz
      rw [hzc, circlePoint_norm θ] at hzlt
      exact absurd hzlt (lt_irrefl 1)
  have hnotK : ∀ w : Metric.closedBall (0 : ℂ) 1, ‖(w : ℂ)‖ < 1 → w ≠ w₀ →
      hout w ∉ K := by
    intro w hw hwne hmem
    have hene : e w ≠ OnePoint.infty := by
      intro heq; exact hwne (heinj (by rw [heq, hwe]))
    obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp hene
    have hcnotF : c ∉ Set.range ⇑F := by
      have hsub2 := he_subset ⟨w, hw, rfl⟩
      rw [← hc] at hsub2
      rcases hsub2 with h | h
      · exact absurd h (OnePoint.coe_ne_infty c)
      · obtain ⟨d, hd, hdc⟩ := h
        rw [← OnePoint.coe_injective hdc]; exact hd
    obtain ⟨y, hy⟩ := hmem
    have hval : toR2 c = Ξ y := by
      have h1 : hout w = toR2 c := by
        show toR2 (unc (e w)) = toR2 c
        rw [← hc, hunc_coe]
      rw [h1] at hy
      exact hy.symm
    refine hcnotF ?_
    rw [hrangeF]
    exact ⟨Ξ y, ⟨y, rfl⟩, (by rw [← hval, ofR2_toR2] : c = ofR2 (Ξ y)).symm⟩
  have hout_inj : ∀ w w' : Metric.closedBall (0 : ℂ) 1, ‖(w : ℂ)‖ < 1 → w ≠ w₀ →
      ‖(w' : ℂ)‖ < 1 → w' ≠ w₀ → hout w = hout w' → w = w' := by
    intro w w' hw hwne hw' hw'ne h
    have hene : e w ≠ OnePoint.infty := by
      intro heq; exact hwne (heinj (by rw [heq, hwe]))
    have hene' : e w' ≠ OnePoint.infty := by
      intro heq; exact hw'ne (heinj (by rw [heq, hwe]))
    obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp hene
    obtain ⟨c', hc'⟩ := OnePoint.ne_infty_iff_exists.mp hene'
    have h2 : hout w = toR2 c := by
      show toR2 (unc (e w)) = toR2 c
      rw [← hc, hunc_coe]
    have h3 : hout w' = toR2 c' := by
      show toR2 (unc (e w')) = toR2 c'
      rw [← hc', hunc_coe]
    rw [h2, h3] at h
    have hcc' : c = c' := toR2_injective h
    exact heinj (by rw [← hc, ← hc', hcc'])
  have hKsub : K ⊆ G '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1} := by
    rintro p ⟨y, rfl⟩
    have hzmem : r • (y : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [hzn y]
    have hznorm : ‖((⟨r • (y : ℂ), hzmem⟩ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [hzn y, hr1]
    refine ⟨⟨r • (y : ℂ), hzmem⟩, hznorm, ?_⟩
    have hle : ‖((⟨r • (y : ℂ), hzmem⟩ : Metric.closedBall (0 : ℂ) 1) : ℂ)‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [hzn y, hr0]
    rw [hGf _ hle]
    show Ξ (φ₁ ⟨r • (y : ℂ), hzmem⟩) = Ξ y
    congr 1
    apply Subtype.ext
    rw [hφ₁coe]
    simp only [dir]
    rw [max_eq_right hle, smul_smul, inv_mul_cancel₀ (ne_of_gt hr0), one_smul]
  have hGinj : Function.Injective G := by
    intro z z' hzz
    by_cases hz : ‖(z : ℂ)‖ ≤ r
    · by_cases hz' : ‖(z' : ℂ)‖ ≤ r
      · have h1 : φ₁ z = φ₁ z' := by
          apply hΞinj
          rw [← hGf z hz, ← hGf z' hz']
          exact hzz
        have h3 : (max ‖(z : ℂ)‖ r)⁻¹ • (z : ℂ) = (max ‖(z' : ℂ)‖ r)⁻¹ • (z' : ℂ) :=
          congrArg Subtype.val h1
        rw [max_eq_right hz, max_eq_right hz'] at h3
        have h4 : (z : ℂ) = (z' : ℂ) :=
          (smul_right_injective ℂ (inv_ne_zero (ne_of_gt hr0))) h3
        exact Subtype.ext h4
      · have hz'2 : r ≤ ‖(z' : ℂ)‖ := le_of_lt (not_le.mp hz')
        have hKz : G z ∈ K := ⟨φ₁ z, (hGf z hz).symm⟩
        have hmem : G z' ∈ K := by rw [← hzz]; exact hKz
        rw [hGg z' hz'] at hmem
        exact absurd hmem (hnotK (φ₂ z') (by
            rw [hφ₂norm z' hz'2]; exact hσlt1 _ (not_le.mp hz') (hzn z'))
          (hφ₂ne z' hz'2))
    · have hz2 : r ≤ ‖(z : ℂ)‖ := le_of_lt (not_le.mp hz)
      by_cases hz' : ‖(z' : ℂ)‖ ≤ r
      · have hKz' : G z' ∈ K := ⟨φ₁ z', (hGf z' hz').symm⟩
        have hmem : G z ∈ K := by rw [hzz]; exact hKz'
        rw [hGg z hz] at hmem
        exact absurd hmem (hnotK (φ₂ z) (by
            rw [hφ₂norm z hz2]; exact hσlt1 _ (not_le.mp hz) (hzn z))
          (hφ₂ne z hz2))
      · have hz'2 : r ≤ ‖(z' : ℂ)‖ := le_of_lt (not_le.mp hz')
        have h1 : φ₂ z = φ₂ z' := by
          rw [hGg z hz, hGg z' hz'] at hzz
          exact hout_inj (φ₂ z) (φ₂ z') (by
              rw [hφ₂norm z hz2]; exact hσlt1 _ (not_le.mp hz) (hzn z))
            (hφ₂ne z hz2) (by
              rw [hφ₂norm z' hz'2]; exact hσlt1 _ (not_le.mp hz') (hzn z'))
            (hφ₂ne z' hz'2) hzz
        have hnorm : ‖(z : ℂ)‖ = ‖(z' : ℂ)‖ := by
          have h2 : σ ‖(z : ℂ)‖ = σ ‖(z' : ℂ)‖ := by
            rw [← hφ₂norm z hz2, ← hφ₂norm z' hz'2, h1]
          exact hσ_inj _ _ h2
        have h2 : (z : ℂ) = (z' : ℂ) := by
          have h3 : (φ₂ z : ℂ) = (φ₂ z' : ℂ) := congrArg Subtype.val h1
          rw [hφ₂coe, hφ₂coe, min_eq_left (hσle1 _ hz2 (hzn z)),
            min_eq_left (hσle1 _ hz'2 (hzn z'))] at h3
          have h3' : σ ‖(z : ℂ)‖ • dir z = σ ‖(z : ℂ)‖ • dir z' := by
            have h3'' : σ ‖(z : ℂ)‖ • dir z = σ ‖(z' : ℂ)‖ • dir z' := h3
            rwa [← hnorm] at h3''
          have h4 : dir z = dir z' :=
            (smul_right_injective ℂ (ne_of_gt (hσpos _ (hzn z)))) h3'
          have h4' : (‖(z : ℂ)‖)⁻¹ • (z : ℂ) = (‖(z : ℂ)‖)⁻¹ • (z' : ℂ) := by
            have hz1 : dir z = (‖(z : ℂ)‖)⁻¹ • (z : ℂ) := hdir_value z hz2
            have hz2' : dir z' = (‖(z : ℂ)‖)⁻¹ • (z' : ℂ) := by
              rw [hdir_value z' hz'2, ← hnorm]
            rw [← hz1, ← hz2']
            exact h4
          exact (smul_right_injective ℂ
            (inv_ne_zero (ne_of_gt (lt_of_lt_of_le hr0 hz2)))) h4'
        exact Subtype.ext h2
  have hGopen : IsOpen (G '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) := by
    have hc : Continuous (ofR2 ∘ G) := continuous_ofR2.comp hGcont
    have hinj : Function.Injective (ofR2 ∘ G) := ofR2_injective.comp hGinj
    have hopen : IsOpen ((ofR2 ∘ G) '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) :=
      Work.Smooth.SphereJordan.openImage_isOpen_of_injective ⟨ofR2 ∘ G, hc⟩ hinj
    have heq : G '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}
        = ofR2 ⁻¹' ((ofR2 ∘ G) '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, hzp⟩
        exact ⟨z, hz, ofR2_injective hzp⟩
    rw [heq]
    exact hopen.preimage continuous_ofR2
  have hboundaryW : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ = 1 → G z ∈ W := by
    intro z hz
    have hzr : ¬ ‖(z : ℂ)‖ ≤ r := by rw [hz]; exact not_le.mpr hr1
    rw [hGg z hzr]
    have h1 : tN ≤ ‖(φ₂ z : ℂ)‖ := by
      rw [hφ₂norm z (le_of_lt (not_le.mp hzr)), hz, hσ1]
      exact htNt
    have h2 : ‖(φ₂ z : ℂ)‖ ≤ 1 := by
      rw [hφ₂norm z (le_of_lt (not_le.mp hzr)), hz, hσ1]
      exact le_of_lt ht1
    obtain ⟨c, hc, hdist⟩ := htN (φ₂ z) h1 h2
    exact hρNsub (Metric.thickening_subset_cthickening ρN J0
      (Metric.mem_thickening_iff.mpr ⟨c, hc, hdist⟩))
  let e₂ : Metric.closedBall (0 : ℂ) 1 → R3 := fun z => Work.TorusCover.psiMap P.psi (G z)
  have he₂cont : Continuous e₂ := by
    show Continuous fun z => P.psi (G z).1 (G z).2
    exact P.cont.comp hGcont
  have he₂inj : Function.Injective e₂ := by
    intro z z' h
    exact hGinj (hδ (G z) (G z') (hGclose z) (hGclose z')
      ((Work.TorusCover.psiMap_eq_iff_param P).mp (show Work.TorusCover.psiMap P.psi (G z)
        = Work.TorusCover.psiMap P.psi (G z') from h)))
  refine ⟨{ e := ⟨e₂, he₂cont⟩, inj := he₂inj,
            mem := fun z => P.psi_mem_carrier _ _,
            open_interior := ?_ }, ?_, ?_⟩
  · have hfun : (⟨e₂, he₂cont⟩ : C(Metric.closedBall (0 : ℂ) 1, R3))
        = (Work.TorusCover.psiMap P.psi) ∘ G := by ext z; rfl
    show Work.SurgeryInvariance.IsOpenInCarrier P
      ((⟨e₂, he₂cont⟩ : C(Metric.closedBall (0 : ℂ) 1, R3))
        '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1})
    rw [hfun, Set.image_comp]
    exact Work.Smooth.Morse.Surface.isOpenInCarrier_psiMap_image P hGopen
  · intro x hx
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨p, hp, hGp⟩ := hKsub (Set.mem_range_self z)
    refine ⟨p, hp, ?_⟩
    show e₂ p = D.e z
    rw [show e₂ p = Work.TorusCover.psiMap P.psi (G p) from rfl, hGp]
    simpa using hΞ z
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    show e₂ z ∈ N
    exact hboundaryW z hz

end

end Work.BoxShrink.PinchOff
