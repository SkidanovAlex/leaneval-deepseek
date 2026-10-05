import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Geometry
import Submission.Work.RPB1a.isOpen_image_of_differentiableOn_of_injOn
import Submission.Work.RPB1a.isOpen_annulus
import Submission.Work.RPB1a.differentiableOn_of_compl_sphere
import Submission.Work.RPB1a.deriv_ne_zero_of_injOn
import Submission.Work.RPB1a.differentiableOn_invFunOn
import Submission.Work.RPB1a.contDiff_arg_lift_circle
import Submission.Work.RPB.B1.argument_lift_aux
import Submission.Work.RPB.B2.paramIntegral_contDiff_inf
import Submission.Work.RPB.Defs
import Submission.Work.RPA3.contDiff_param_intervalIntegral

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff Real Topology ComplexConjugate
open Work.RPB1a

noncomputable section

/-! ## Auxiliary facts about conjugation and the unit circle -/

lemma conj_one_div (w : ℂ) : conj (1 / w) = 1 / conj w := by
  rw [one_div, one_div, map_inv₀]

lemma conj_eq_zero_iff' {z : ℂ} : conj z = 0 ↔ z = 0 := by
  constructor <;> intro h
  · simpa using congrArg conj h
  · rw [h, map_zero]

lemma inv_conj_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : (conj z)⁻¹ = z := by
  rw [← Complex.conj_inv, Complex.inv_eq_conj hz, conj_conj]

lemma div_conj_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : 1 / conj z = z := by
  rw [one_div, inv_conj_of_norm_eq_one hz]

/-! ## Reflection in the unit circle -/

/-- Reflection of `h` in the unit circle: `h` inside the closed unit disc and
`z ↦ 1 / conj (h (1 / conj z))` outside it. -/
def reflShell (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ 1 then h z else 1 / conj (h (1 / conj z))

@[simp]
lemma reflShell_of_le_one {h : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ ≤ 1) : reflShell h z = h z :=
  if_pos hz

lemma reflShell_of_one_lt {h : ℂ → ℂ} {z : ℂ} (hz : 1 < ‖z‖) :
    reflShell h z = 1 / conj (h (1 / conj z)) :=
  if_neg (not_le.mpr hz)

lemma reflShell_of_one_le {h : ℂ → ℂ} (hsph : ∀ z : ℂ, ‖z‖ = 1 → ‖h z‖ = 1) {z : ℂ}
    (hz : 1 ≤ ‖z‖) : reflShell h z = 1 / conj (h (1 / conj z)) := by
  rcases lt_or_eq_of_le hz with hlt | heq
  · exact reflShell_of_one_lt hlt
  · rw [reflShell_of_le_one heq.ge, div_conj_of_norm_eq_one heq.symm]
    have h1 : (conj (h z))⁻¹ = h z := by
      rw [← Complex.conj_inv, Complex.inv_eq_conj (hsph z heq.symm), conj_conj]
    rw [one_div, h1]

/-- Continuity of the reflection of `h` on the annulus `1-η < ‖z‖ < (1-η)⁻¹`, assuming `h` is
continuous and nonvanishing on the closed shell `1-η ≤ ‖z‖ ≤ 1` and unimodular on the circle. -/
lemma continuousOn_reflShell {h : ℂ → ℂ} {η : ℝ} (hη1 : η < 1)
    (hc : ContinuousOn h {z : ℂ | 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1})
    (hne : ∀ z : ℂ, 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1 → h z ≠ 0)
    (hsph : ∀ z : ℂ, ‖z‖ = 1 → ‖h z‖ = 1) :
    ContinuousOn (reflShell h) (annulus (1 - η)) := by
  have hsplit : annulus (1 - η) =
      (annulus (1 - η) ∩ closedBall 0 1) ∪ (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) := by
    ext z
    simp only [annulus, Set.mem_ofPred_eq, mem_union, mem_inter_iff, mem_closedBall,
      dist_zero_right]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_ge ‖z‖ 1 with h | h
      · exact Or.inl ⟨⟨h1, h2⟩, le_of_lt h⟩
      · exact Or.inr ⟨⟨h1, h2⟩, h⟩
    · rintro (⟨⟨h1, h2⟩, _⟩ | ⟨⟨h1, h2⟩, _⟩) <;> exact ⟨h1, h2⟩
  -- The closed inner part: the reflection agrees with `h` there.
  have hinner : ContinuousOn (reflShell h) (annulus (1 - η) ∩ closedBall 0 1) := by
    refine (hc.mono ?_).congr ?_
    · rintro z hz
      have hz1 : 1 - η < ‖z‖ := hz.1.1
      have hz2 : z ∈ closedBall (0 : ℂ) 1 := hz.2
      have hz3 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz2
      exact ⟨le_of_lt hz1, hz3⟩
    · rintro z hz
      have hz2 : z ∈ closedBall (0 : ℂ) 1 := hz.2
      have hz3 : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz2
      exact reflShell_of_le_one hz3
  -- The closed outer part: the reflection is the reflected formula there.
  have houter : ContinuousOn (reflShell h) (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) := by
    have hmap : MapsTo (fun w : ℂ => (1 : ℂ) / conj w)
        (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) {z : ℂ | 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1} := by
      rintro w ⟨hw, hw1⟩
      have hwpos : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw1
      have hnorm : ‖(1 : ℂ) / conj w‖ = ‖w‖⁻¹ := by
        rw [norm_div, norm_one, norm_conj, one_div]
      refine ⟨?_, ?_⟩
      · rw [hnorm]
        have hpos : 0 < 1 - η := by linarith
        have hstep : ((1 - η)⁻¹)⁻¹ < ‖w‖⁻¹ :=
          (inv_lt_inv₀ (inv_pos.mpr hpos) hwpos).mpr hw.2
        rw [inv_inv] at hstep
        exact le_of_lt hstep
      · rw [hnorm, inv_le_one₀ hwpos]
        exact hw1
    have hspan : ContinuousOn (fun w : ℂ => (1 : ℂ) / conj w)
        (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
      continuousOn_const.div continuous_conj.continuousOn (fun w hw => by
        have h1 : 1 ≤ ‖w‖ := hw.2
        intro h0
        rw [conj_eq_zero_iff'] at h0
        rw [h0] at h1
        norm_num at h1)
    have hcomp : ContinuousOn (fun w : ℂ => h ((1 : ℂ) / conj w))
        (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) := hc.comp hspan hmap
    have hconj : ContinuousOn (fun w : ℂ => conj (h ((1 : ℂ) / conj w)))
        (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
      continuous_conj.continuousOn.comp (t := Set.univ) hcomp fun _ _ => trivial
    have hformula : ContinuousOn (fun w : ℂ => (1 : ℂ) / conj (h ((1 : ℂ) / conj w)))
        (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) :=
      continuousOn_const.div hconj (fun w hw => by
        intro h0
        rw [conj_eq_zero_iff'] at h0
        exact hne _ (hmap hw) h0)
    exact hformula.congr (fun w hw => reflShell_of_one_le hsph hw.2)
  intro z hz
  rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
  · have hs : (annulus (1 - η) ∩ closedBall 0 1) ∈ 𝓝 z :=
      Filter.mem_of_superset
        (Filter.inter_mem ((isOpen_annulus (1 - η)).mem_nhds hz)
          ((isOpen_lt continuous_norm continuous_const).mem_nhds hlt))
        (fun w hw => ⟨hw.1, by
          rw [mem_closedBall, dist_zero_right]
          exact le_of_lt (by simpa using hw.2)⟩)
    exact (hinner.continuousAt hs).continuousWithinAt
  · have hzu : ContinuousWithinAt (reflShell h)
        ((annulus (1 - η) ∩ closedBall 0 1) ∪ (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖})) z :=
      ContinuousWithinAt.union
        (hinner.continuousWithinAt ⟨hz, by rw [mem_closedBall, dist_zero_right]; exact heq.le⟩)
        (houter.continuousWithinAt ⟨hz, heq.ge⟩)
    exact hsplit ▸ hzu
  · have hs : (annulus (1 - η) ∩ {z : ℂ | 1 ≤ ‖z‖}) ∈ 𝓝 z :=
      Filter.mem_of_superset
        (Filter.inter_mem ((isOpen_annulus (1 - η)).mem_nhds hz)
          ((isOpen_lt continuous_const continuous_norm).mem_nhds hgt))
        (fun w hw => ⟨hw.1, le_of_lt (by simpa using hw.2)⟩)
    exact (houter.continuousAt hs).continuousWithinAt

/-! ## Differentiability of the reflection off the circle -/

/-- Off the unit circle the reflection is holomorphic (it is `h` inside, and a composition of
holomorphic maps outside). -/
lemma differentiableOn_reflShell_off_sphere {h : ℂ → ℂ} {η : ℝ} (hη1 : η < 1)
    (hd : DifferentiableOn ℂ h {z : ℂ | 1 - η < ‖z‖ ∧ ‖z‖ < 1})
    (hne : ∀ z : ℂ, 1 - η < ‖z‖ ∧ ‖z‖ < 1 → h z ≠ 0) :
    DifferentiableOn ℂ (reflShell h) (annulus (1 - η) \ sphere 0 1) := by
  intro z hz
  have hzA : z ∈ annulus (1 - η) := hz.1
  have hzA' : 1 - η < ‖z‖ ∧ ‖z‖ < (1 - η)⁻¹ := hzA
  have hzsph : z ∉ sphere (0 : ℂ) 1 := hz.2
  have hnorm1 : ‖z‖ ≠ 1 := fun h1 => hzsph (by rw [mem_sphere, dist_zero_right]; exact h1)
  have hopen : IsOpen {z : ℂ | 1 - η < ‖z‖ ∧ ‖z‖ < 1} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  rcases lt_or_gt_of_ne hnorm1 with hlt | hgt
  · -- ‖z‖ < 1 : the reflection agrees with `h` near `z`
    have hmem : {w : ℂ | ‖w‖ ≤ 1} ∈ 𝓝 z :=
      Filter.mem_of_superset
        ((isOpen_lt continuous_norm continuous_const).mem_nhds hlt)
        (fun w hw => show ‖w‖ ≤ 1 from le_of_lt (show ‖w‖ < 1 from hw))
    have hev : reflShell h =ᶠ[𝓝 z] h := by
      filter_upwards [hmem] with w hw
      exact reflShell_of_le_one hw
    exact ((hd.differentiableAt (hopen.mem_nhds ⟨hzA'.1, hlt⟩)).congr_of_eventuallyEq
      hev).differentiableWithinAt
  · -- 1 < ‖z‖ : the reflection is the reflected formula near `z`
    have hzpos : 0 < ‖z‖ := lt_trans zero_lt_one hgt
    have hz0 : z ≠ 0 := fun h0 => by rw [h0] at hgt; norm_num at hgt
    have hinner : conj (1 / z) ∈ {z : ℂ | 1 - η < ‖z‖ ∧ ‖z‖ < 1} := by
      have hnorm : ‖conj (1 / z)‖ = ‖z‖⁻¹ := by
        rw [norm_conj, norm_div, norm_one, one_div]
      refine ⟨?_, ?_⟩ <;> rw [hnorm]
      · have hpos : 0 < 1 - η := by linarith [hzA'.1]
        have hstep : ((1 - η)⁻¹)⁻¹ < ‖z‖⁻¹ :=
          (inv_lt_inv₀ (inv_pos.mpr hpos) hzpos).mpr hzA'.2
        rw [inv_inv] at hstep
        exact hstep
      · exact (inv_lt_one₀ hzpos).mpr hgt
    have hd1 : DifferentiableAt ℂ h (conj (1 / z)) :=
      hd.differentiableAt (hopen.mem_nhds hinner)
    have hdrefl : DifferentiableAt ℂ (fun u : ℂ => conj (h (conj u))) ((1 : ℂ) / z) := by
      have h := hd1.conj_conj
      have h3 : (starRingEnd ℂ) (conj (1 / z)) = ((1 : ℂ) / z) := by simp [conj_conj]
      rw [h3] at h
      exact h
    have hinv : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) / w) z :=
      (differentiableAt_const (1 : ℂ)).div differentiableAt_id hz0
    have hcomp : DifferentiableAt ℂ (fun w : ℂ => conj (h (conj (1 / w)))) z :=
      hdrefl.comp z hinv
    have hrefl_ne : conj (h (conj (1 / z))) ≠ 0 := by
      have h0 : h (conj (1 / z)) ≠ 0 := hne _ hinner
      intro h1
      rw [conj_eq_zero_iff'] at h1
      exact h0 h1
    have hdiv : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) / conj (h (conj (1 / w)))) z :=
      (differentiableAt_const (1 : ℂ)).div hcomp hrefl_ne
    have hev : reflShell h =ᶠ[𝓝 z]
        (fun w : ℂ => (1 : ℂ) / conj (h (conj (1 / w)))) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hgt] with w hw
      rw [reflShell_of_one_lt hw, conj_one_div]
    exact (hdiv.congr_of_eventuallyEq hev).differentiableWithinAt


/-- The reflection of `h` is holomorphic on the whole annulus `1-η < ‖z‖ < (1-η)⁻¹`. -/
lemma differentiableOn_reflShell {h : ℂ → ℂ} {η : ℝ} (hη1 : η < 1)
    (hc : ContinuousOn h {z : ℂ | 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1})
    (hd : DifferentiableOn ℂ h {z : ℂ | 1 - η < ‖z‖ ∧ ‖z‖ < 1})
    (hne : ∀ z : ℂ, 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1 → h z ≠ 0)
    (hsph : ∀ z : ℂ, ‖z‖ = 1 → ‖h z‖ = 1) :
    DifferentiableOn ℂ (reflShell h) (annulus (1 - η)) :=
  differentiableOn_of_compl_sphere (isOpen_annulus (1 - η))
    (continuousOn_reflShell hη1 hc hne hsph)
    (differentiableOn_reflShell_off_sphere hη1 hd
      (fun z hz => hne z ⟨le_of_lt hz.1, le_of_lt hz.2⟩))


/-! ## The shell on which the collar map is defined -/

lemma one_div_conj_mem_annulus {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : w ∈ annulus ρ) :
    1 / conj w ∈ annulus ρ := by
  obtain ⟨hw1, hw2⟩ := hw
  have hwpos : 0 < ‖w‖ := lt_trans hρ hw1
  refine ⟨?_, ?_⟩
  · rw [norm_div, norm_one, norm_conj, one_div]
    have h := (inv_lt_inv₀ (inv_pos.mpr hρ) hwpos).mpr hw2
    rwa [inv_inv] at h
  · rw [norm_div, norm_one, norm_conj, one_div]
    exact (inv_lt_inv₀ hwpos hρ).mpr hw1

/-- If `Φ` maps the unit circle into an open set `W` and is continuous on the closed unit disc, then
it maps a closed shell `1 - η ≤ ‖z‖ ≤ 1` around the circle into `W` for some `η > 0`. -/
lemma exists_shell_mapsTo {Φ : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hc : ContinuousOn Φ (closedBall (0 : ℂ) 1)) (hsub : Φ '' sphere (0 : ℂ) 1 ⊆ W) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ Φ '' {z : ℂ | 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1} ⊆ W := by
  -- `V := Φ ⁻¹' W ∪ (closedBall 0 1)ᶜ` is open and contains the circle.
  have hVopen : IsOpen (Φ ⁻¹' W ∪ (closedBall (0 : ℂ) 1)ᶜ) := by
    rw [isOpen_iff_mem_nhds]
    rintro z hz
    rcases hz with hzW | hzc
    · by_cases hzK : z ∈ closedBall (0 : ℂ) 1
      · have hcont : ContinuousWithinAt Φ (closedBall (0 : ℂ) 1) z := hc.continuousWithinAt hzK
        have hmem : Φ ⁻¹' W ∈ 𝓝[closedBall (0 : ℂ) 1] z := hcont (hW.mem_nhds hzW)
        obtain ⟨ε, hε, hεK⟩ := mem_nhdsWithin_iff.mp hmem
        refine Filter.mem_of_superset (Metric.ball_mem_nhds z hε) ?_
        intro w hw
        by_cases hwK : w ∈ closedBall (0 : ℂ) 1
        · exact Or.inl (hεK ⟨hw, hwK⟩)
        · exact Or.inr hwK
      · exact Filter.mem_of_superset (isClosed_closedBall.isOpen_compl.mem_nhds hzK)
          (fun w hw => Or.inr hw)
    · exact Filter.mem_of_superset (isClosed_closedBall.isOpen_compl.mem_nhds hzc)
        (fun w hw => Or.inr hw)
  have hsubV : sphere (0 : ℂ) 1 ⊆ Φ ⁻¹' W ∪ (closedBall (0 : ℂ) 1)ᶜ :=
    fun z hz => Or.inl (hsub ⟨z, hz, rfl⟩)
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hVopen hsubV
  refine ⟨min δ 1 / 2, by positivity, by linarith [min_le_right δ 1], ?_⟩
  rintro y ⟨z, hz, rfl⟩
  have hz2 : ‖z‖ ≤ 1 := hz.2
  have hzpos : 0 < ‖z‖ := by linarith [min_le_right δ 1, hz.1]
  have hzK : z ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right]; exact hz2
  have hzsphere : (‖z‖ : ℂ)⁻¹ * z ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere, dist_zero_right, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hzpos]
    field_simp
  have hzdist : dist z ((‖z‖ : ℂ)⁻¹ * z) < δ := by
    have h1 : dist z ((‖z‖ : ℂ)⁻¹ * z) = |‖z‖ - 1| := by
      have h2 : dist z ((‖z‖ : ℂ)⁻¹ * z) = ‖(1 - (‖z‖ : ℂ)⁻¹) * z‖ := by
        rw [dist_eq_norm]; congr 1; ring
      rw [h2, norm_mul]
      have h3 : ‖(1 : ℂ) - (‖z‖ : ℂ)⁻¹‖ = |1 - (‖z‖)⁻¹| := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
      rw [h3]
      have hinv : 1 ≤ (‖z‖)⁻¹ := (one_le_inv₀ hzpos).mpr hz2
      rw [abs_of_nonpos (by linarith : 1 - (‖z‖)⁻¹ ≤ 0),
        abs_of_nonpos (by linarith : ‖z‖ - 1 ≤ 0)]
      field_simp
    rw [h1, abs_of_nonpos (by linarith : ‖z‖ - 1 ≤ 0)]
    have hz1 : 1 - min δ 1 / 2 ≤ ‖z‖ := hz.1
    linarith [min_le_left δ 1, hz1]
  have hzthick : z ∈ Metric.thickening δ (sphere (0 : ℂ) 1) := by
    rw [Metric.mem_thickening_iff]
    exact ⟨_, hzsphere, hzdist⟩
  rcases hδV hzthick with h | h
  · exact h
  · exact absurd hzK h






/-- N7: analytic continuation of the Riemann map across an analytic boundary (circle Schwarz
reflection). -/

theorem analytic_extension_of_collar (v : ℝ → ℂ) (hv : IsSmoothLoop v) (D : Set ℂ)
    (hDo : IsOpen D) (hDfr : frontier D = range v) (hDdisj : Disjoint D (range v))
    (Γ : ℂ → ℂ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hΓd : DifferentiableOn ℂ Γ (annulus ρ)) (hΓi : InjOn Γ (annulus ρ))
    (hΓd' : ∀ w ∈ annulus ρ, deriv Γ w ≠ 0)
    (hΓcirc : ∀ t : ℝ, Γ (Complex.exp (t * I)) = v t)
    (hin : Γ '' (annulus ρ ∩ ball 0 1) ⊆ D)
    (hout : Disjoint (Γ '' (annulus ρ \ closedBall 0 1)) D)
    (Φ : ℂ → ℂ) (hΦc : ContinuousOn Φ (closedBall 0 1)) (hΦd : DifferentiableOn ℂ Φ (ball 0 1))
    (hΦi : InjOn Φ (closedBall 0 1)) (hΦim : Φ '' ball 0 1 = D)
    (hΦs : MapsTo Φ (sphere 0 1) (range v)) :
    ∃ R : ℝ, 1 < R ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 R) ∧ InjOn F (ball 0 R) ∧
      (∀ z ∈ ball 0 R, deriv F z ≠ 0) ∧ EqOn F Φ (closedBall 0 1) ∧
      ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ ∀ t : ℝ, F (Complex.exp (t * I)) = v (σ t) := by
  -- ### The collar image is open, and contains the boundary
  have hWopen : IsOpen (Γ '' annulus ρ) :=
    isOpen_image_of_differentiableOn_of_injOn (isOpen_annulus ρ) hΓd hΓi
  have hexp_norm : ∀ t : ℝ, ‖Complex.exp (t * I)‖ = 1 := by
    intro t; rw [Complex.norm_exp]; simp
  have hexp_ann : ∀ t : ℝ, Complex.exp (t * I) ∈ annulus ρ := by
    intro t
    rw [annulus]
    exact ⟨by rw [hexp_norm t]; exact hρ1, by rw [hexp_norm t]; exact (one_lt_inv₀ hρ0).mpr hρ1⟩
  have hrvW : range v ⊆ Γ '' annulus ρ := by
    rintro y ⟨t, rfl⟩
    exact ⟨Complex.exp (t * I), hexp_ann t, hΓcirc t⟩
  have hPhiSW : Φ '' sphere (0 : ℂ) 1 ⊆ Γ '' annulus ρ := by
    rintro y ⟨z, hz, rfl⟩
    exact hrvW (hΦs hz)
  obtain ⟨η, hη0, hη1, hηmap⟩ := exists_shell_mapsTo hWopen hΦc hPhiSW
  -- ### The inverse of the collar map
  set Ψ : ℂ → ℂ := Function.invFunOn Γ (annulus ρ) with hΨ
  have hΨd : DifferentiableOn ℂ Ψ (Γ '' annulus ρ) :=
    differentiableOn_invFunOn (isOpen_annulus ρ) hΓd hΓi hΓd'
  have hΨmem : ∀ y ∈ Γ '' annulus ρ, Ψ y ∈ annulus ρ := fun y hy => Function.invFunOn_mem hy
  have hΨΓ : ∀ y ∈ Γ '' annulus ρ, Γ (Ψ y) = y := fun y hy => Function.invFunOn_eq hy
  -- ### The map `ψ = Ψ ∘ Φ` on the shell
  set ψ : ℂ → ℂ := fun z => Ψ (Φ z) with hψ
  have hψmap : ∀ z : ℂ, 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1 → ψ z ∈ annulus ρ :=
    fun z hz => hΨmem (Φ z) (hηmap ⟨z, hz, rfl⟩)
  have hψd : DifferentiableOn ℂ ψ {z : ℂ | 1 - η < ‖z‖ ∧ ‖z‖ < 1} :=
    DifferentiableOn.comp hΨd
      (hΦd.mono fun z hz => by rw [mem_ball, dist_zero_right]; exact hz.2)
      (fun z hz => hηmap ⟨z, ⟨le_of_lt hz.1, le_of_lt hz.2⟩, rfl⟩)
  have hψc : ContinuousOn ψ {z : ℂ | 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1} :=
    ContinuousOn.comp hΨd.continuousOn
      (hΦc.mono fun z hz => by rw [mem_closedBall, dist_zero_right]; exact hz.2)
      (fun z hz => hηmap ⟨z, hz, rfl⟩)
  have hψne : ∀ z : ℂ, 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1 → ψ z ≠ 0 := by
    intro z hz h0
    have h := (hψmap z hz).1
    rw [h0] at h
    simp at h
    linarith
  have hψsph : ∀ z : ℂ, ‖z‖ = 1 → ‖ψ z‖ = 1 := by
    intro z hz
    have hzsh : z ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere, dist_zero_right]; exact hz
    have hshell : 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1 := ⟨by linarith, by linarith⟩
    have hzW : ψ z ∈ annulus ρ := hψmap z hshell
    have hΓψ : Γ (ψ z) = Φ z := hΨΓ (Φ z) (hηmap ⟨z, hshell, rfl⟩)
    obtain ⟨t, ht⟩ := hΦs hzsh
    have hexp : Γ (ψ z) = Γ (Complex.exp (t * I)) := by rw [hΓψ, ← ht, hΓcirc]
    rw [hΓi hzW (hexp_ann t) hexp, hexp_norm t]
  have hψlt : ∀ z : ℂ, 1 - η < ‖z‖ ∧ ‖z‖ < 1 → ‖ψ z‖ < 1 := by
    intro z hz
    have hshell : 1 - η ≤ ‖z‖ ∧ ‖z‖ ≤ 1 := ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    have hzW : ψ z ∈ annulus ρ := hψmap z hshell
    have hΓψ : Γ (ψ z) = Φ z := hΨΓ (Φ z) (hηmap ⟨z, hshell, rfl⟩)
    have hzD : Φ z ∈ D := by
      rw [← hΦim]; exact ⟨z, by rw [mem_ball, dist_zero_right]; exact hz.2, rfl⟩
    have hnot : ψ z ∉ annulus ρ \ closedBall (0 : ℂ) 1 := by
      intro hmem
      have hD' : Γ (ψ z) ∈ D := hΓψ ▸ hzD
      exact (Set.disjoint_left.mp hout ⟨ψ z, hmem, rfl⟩) hD'
    have hle : ‖ψ z‖ ≤ 1 := by
      by_contra h
      rw [not_le] at h
      exact hnot ⟨hzW, by rw [mem_closedBall, dist_zero_right, not_le]; exact h⟩
    rcases lt_or_eq_of_le hle with h' | h'
    · exact h'
    · exfalso
      have hψne0 : ψ z ≠ 0 := by
        intro h0; rw [h0] at h'; simp at h'
      have hlog : Γ (ψ z) ∈ range v := by
        refine ⟨(Complex.log (ψ z)).im, ?_⟩
        have h1 : Complex.exp (Complex.log (ψ z)) = ψ z := Complex.exp_log hψne0
        have h2 : (Complex.log (ψ z)).re = 0 := by rw [Complex.log_re, h']; simp
        have h3 : Complex.log (ψ z) = ((Complex.log (ψ z)).im : ℂ) * I := by
          conv_lhs => rw [← Complex.re_add_im (Complex.log (ψ z))]
          rw [h2]; simp
        have h4 := hΓcirc ((Complex.log (ψ z)).im)
        rw [← h3] at h4
        rw [h1] at h4
        exact h4.symm
      have hD' : Γ (ψ z) ∈ D := hΓψ ▸ hzD
      exact (Set.disjoint_left.mp hDdisj hD') hlog
  -- ### Reflection across the unit circle
  have hrefl_d : DifferentiableOn ℂ (reflShell ψ) (annulus (1 - η)) :=
    differentiableOn_reflShell hη1 hψc hψd hψne hψsph
  -- ### The extension `F`
  set F : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then Φ z else Γ (reflShell ψ z) with hF
  have hFapp : ∀ z : ℂ, F z = if ‖z‖ ≤ 1 then Φ z else Γ (reflShell ψ z) := fun z => rfl
  have hOne : (1 : ℝ) < (1 - η)⁻¹ :=
    (one_lt_inv₀ (by linarith : (0 : ℝ) < 1 - η)).mpr (by linarith)
  have hshell_inv : ∀ u : ℂ, 1 < ‖u‖ → ‖u‖ < (1 - η)⁻¹ →
      1 - η < ‖1 / conj u‖ ∧ ‖1 / conj u‖ < 1 := by
    intro u hu hu'
    have hupos : 0 < ‖u‖ := lt_trans zero_lt_one hu
    have hnorm : ‖1 / conj u‖ = ‖u‖⁻¹ := by rw [norm_div, norm_one, norm_conj, one_div]
    rw [hnorm]
    refine ⟨?_, (inv_lt_one₀ hupos).mpr hu⟩
    have hpos : 0 < 1 - η := by linarith
    have hstep : ((1 - η)⁻¹)⁻¹ < ‖u‖⁻¹ := (inv_lt_inv₀ (inv_pos.mpr hpos) hupos).mpr hu'
    rwa [inv_inv] at hstep
  have hout_mem : ∀ u : ℂ, 1 < ‖u‖ → ‖u‖ < (1 - η)⁻¹ →
      reflShell ψ u ∈ annulus ρ \ closedBall (0 : ℂ) 1 := by
    intro u hu hu'
    have hshell := hshell_inv u hu hu'
    have hψmem : ψ (1 / conj u) ∈ annulus ρ := hψmap _ ⟨le_of_lt hshell.1, le_of_lt hshell.2⟩
    have hlt : ‖ψ (1 / conj u)‖ < 1 := hψlt _ hshell
    refine ⟨?_, ?_⟩
    · rw [reflShell_of_one_lt hu]
      exact one_div_conj_mem_annulus hρ0 hψmem
    · rw [mem_closedBall, dist_zero_right, not_le, reflShell_of_one_lt hu, norm_div, norm_one,
        norm_conj, one_div]
      exact (one_lt_inv₀ (hρ0.trans hψmem.1)).mpr hlt
  have hψ_inj : Set.InjOn ψ {z : ℂ | 1 - η < ‖z‖ ∧ ‖z‖ < 1} := by
    intro u hu v hv huv
    have huK : u ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]; exact le_of_lt hu.2
    have hvK : v ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]; exact le_of_lt hv.2
    have hΦuv : Φ u = Φ v := by
      have h2 : Γ (ψ u) = Γ (ψ v) := by rw [huv]
      rw [hΨΓ (Φ u) (hηmap ⟨u, ⟨le_of_lt hu.1, le_of_lt hu.2⟩, rfl⟩),
        hΨΓ (Φ v) (hηmap ⟨v, ⟨le_of_lt hv.1, le_of_lt hv.2⟩, rfl⟩)] at h2
      exact h2
    exact hΦi huK hvK hΦuv
  have hFd : DifferentiableOn ℂ F (ball 0 ((1 - η)⁻¹)) := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · have hmem : {w : ℂ | ‖w‖ ≤ 1} ∈ 𝓝 z :=
        Filter.mem_of_superset ((isOpen_lt continuous_norm continuous_const).mem_nhds hlt)
          (fun w hw => show ‖w‖ ≤ 1 from le_of_lt hw)
      have hev : F =ᶠ[𝓝 z] Φ := by
        filter_upwards [hmem] with w hw
        rw [hFapp, if_pos hw]
      have hzball : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; exact hlt
      exact ((hΦd.differentiableAt (isOpen_ball.mem_nhds hzball)).congr_of_eventuallyEq
        hev).differentiableWithinAt
    · have hzA : z ∈ annulus (1 - η) := by
        have h1 : 1 - η < ‖z‖ := by rw [heq]; linarith
        have h2 : ‖z‖ < (1 - η)⁻¹ := by rw [heq]; exact hOne
        simpa [annulus] using ⟨h1, h2⟩
      have hzψ : reflShell ψ z ∈ annulus ρ := by
        rw [reflShell_of_le_one heq.le]
        exact hψmap z ⟨by linarith [heq], heq.le⟩
      have hd1 : DifferentiableAt ℂ (reflShell ψ) z :=
        hrefl_d.differentiableAt ((isOpen_annulus (1 - η)).mem_nhds hzA)
      have hd2 : DifferentiableAt ℂ Γ (reflShell ψ z) :=
        hΓd.differentiableAt ((isOpen_annulus ρ).mem_nhds hzψ)
      have hev : F =ᶠ[𝓝 z] (Γ ∘ reflShell ψ) := by
        have hnbh : {w : ℂ | 1 - η < ‖w‖} ∈ 𝓝 z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds
            (show 1 - η < ‖z‖ from by rw [heq]; linarith)
        filter_upwards [hnbh] with w hw
        rw [hFapp]
        by_cases hw1 : ‖w‖ ≤ 1
        · rw [if_pos hw1, Function.comp_apply, reflShell_of_le_one hw1]
          exact (hΨΓ (Φ w) (hηmap ⟨w, ⟨le_of_lt hw, hw1⟩, rfl⟩)).symm
        · rw [if_neg hw1, Function.comp_apply]
      exact ((hd2.comp z hd1).congr_of_eventuallyEq hev).differentiableWithinAt
    · have hzA : z ∈ annulus (1 - η) := by
        have h1 : 1 - η < ‖z‖ := by linarith
        have h2 : ‖z‖ < (1 - η)⁻¹ := hz
        simpa [annulus] using ⟨h1, h2⟩
      have hzψ : reflShell ψ z ∈ annulus ρ := (hout_mem z hgt hz).1
      have hd1 : DifferentiableAt ℂ (reflShell ψ) z :=
        hrefl_d.differentiableAt ((isOpen_annulus (1 - η)).mem_nhds hzA)
      have hd2 : DifferentiableAt ℂ Γ (reflShell ψ z) :=
        hΓd.differentiableAt ((isOpen_annulus ρ).mem_nhds hzψ)
      have hev : F =ᶠ[𝓝 z] (Γ ∘ reflShell ψ) := by
        have hnbh : {w : ℂ | 1 < ‖w‖} ∈ 𝓝 z :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds (show 1 < ‖z‖ from hgt)
        filter_upwards [hnbh] with w hw
        rw [hFapp, if_neg (not_le.mpr hw), Function.comp_apply]
      exact ((hd2.comp z hd1).congr_of_eventuallyEq hev).differentiableWithinAt
  have hFi : InjOn F (ball 0 ((1 - η)⁻¹)) := by
    have hF_in : ∀ u : ℂ, ‖u‖ ≤ 1 → F u = Φ u := fun u hu => by rw [hFapp, if_pos hu]
    have hF_out : ∀ u : ℂ, 1 < ‖u‖ → ‖u‖ < (1 - η)⁻¹ → F u = Γ (reflShell ψ u) :=
      fun u hu _ => by rw [hFapp, if_neg (not_le.mpr hu)]
    intro z hz w hw hzw
    rw [mem_ball, dist_zero_right] at hz hw
    by_cases hz1 : ‖z‖ ≤ 1 <;> by_cases hw1 : ‖w‖ ≤ 1
    · exact hΦi (by rw [mem_closedBall, dist_zero_right]; exact hz1)
        (by rw [mem_closedBall, dist_zero_right]; exact hw1)
        (by rw [← hF_in z hz1, ← hF_in w hw1]; exact hzw)
    · have hwmem := hout_mem w (not_le.mp hw1) hw
      have hwout : F w ∈ Γ '' (annulus ρ \ closedBall (0 : ℂ) 1) := by
        rw [hF_out w (not_le.mp hw1) hw]
        exact ⟨reflShell ψ w, hwmem, rfl⟩
      have hnotD : F w ∉ D := Set.disjoint_left.mp hout hwout
      rcases lt_or_eq_of_le hz1 with hlt | heq
      · have hzD : Φ z ∈ D := by
          rw [← hΦim]; exact ⟨z, by rw [mem_ball, dist_zero_right]; exact hlt, rfl⟩
        exfalso
        exact hnotD (by rw [← hzw, hF_in z hz1]; exact hzD)
      · have hzsh : z ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere, dist_zero_right]; exact heq
        obtain ⟨t, ht⟩ := hΦs hzsh
        have hΓeq : Γ (reflShell ψ w) = Γ (Complex.exp (t * I)) := by
          rw [← hF_out w (not_le.mp hw1) hw, ← hzw, hF_in z hz1, ← ht, hΓcirc]
        have heqrw := hΓi hwmem.1 (hexp_ann t) hΓeq
        exfalso
        exact hwmem.2 (by rw [heqrw, mem_closedBall, dist_zero_right, hexp_norm t])
    · have hzmem := hout_mem z (not_le.mp hz1) hz
      have hzout : F z ∈ Γ '' (annulus ρ \ closedBall (0 : ℂ) 1) := by
        rw [hF_out z (not_le.mp hz1) hz]
        exact ⟨reflShell ψ z, hzmem, rfl⟩
      have hnotD : F z ∉ D := Set.disjoint_left.mp hout hzout
      rcases lt_or_eq_of_le hw1 with hlt | heq
      · have hwD : Φ w ∈ D := by
          rw [← hΦim]; exact ⟨w, by rw [mem_ball, dist_zero_right]; exact hlt, rfl⟩
        exfalso
        exact hnotD (by rw [hzw, hF_in w hw1]; exact hwD)
      · have hwsh : w ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere, dist_zero_right]; exact heq
        obtain ⟨t, ht⟩ := hΦs hwsh
        have hΓeq : Γ (reflShell ψ z) = Γ (Complex.exp (t * I)) := by
          rw [← hF_out z (not_le.mp hz1) hz, hzw, hF_in w hw1, ← ht, hΓcirc]
        have heqrw := hΓi hzmem.1 (hexp_ann t) hΓeq
        exfalso
        exact hzmem.2 (by rw [heqrw, mem_closedBall, dist_zero_right, hexp_norm t])
    · have hΓeq : Γ (reflShell ψ z) = Γ (reflShell ψ w) := by
        rw [← hF_out z (not_le.mp hz1) hz, ← hF_out w (not_le.mp hw1) hw]
        exact hzw
      have heq2 : reflShell ψ z = reflShell ψ w :=
        hΓi (hout_mem z (not_le.mp hz1) hz).1 (hout_mem w (not_le.mp hw1) hw).1 hΓeq
      rw [reflShell_of_one_lt (not_le.mp hz1), reflShell_of_one_lt (not_le.mp hw1)] at heq2
      have h3 : conj (ψ (1 / conj z)) = conj (ψ (1 / conj w)) := by
        have hh := congrArg (fun v : ℂ => v⁻¹) heq2
        simpa using hh
      have h1 : ψ (1 / conj z) = ψ (1 / conj w) := by
        have hh := congrArg conj h3
        rwa [conj_conj, conj_conj] at hh
      have h2 : 1 / conj z = 1 / conj w :=
        hψ_inj (hshell_inv z (not_le.mp hz1) hz) (hshell_inv w (not_le.mp hw1) hw) h1
      have h3' : conj z = conj w := by
        have hh := congrArg (fun v : ℂ => v⁻¹) h2
        simpa using hh
      have hh := congrArg conj h3'
      rwa [conj_conj, conj_conj] at hh
  have hFeq : EqOn F Φ (closedBall 0 1) := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    rw [hFapp, if_pos hz]
  have hσ : ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧
      ∀ t : ℝ, F (Complex.exp (t * I)) = v (σ t) := by
    have hcircle : ∀ t : ℝ, Complex.exp (t * I) ∈ annulus (1 - η) := by
      intro t
      rw [annulus]
      refine ⟨?_, ?_⟩
      · rw [hexp_norm t]; linarith
      · rw [hexp_norm t]; exact hOne
    have hC : ContDiff ℝ ∞ fun t : ℝ => Complex.exp (t * I) := by
      have h1 : ContDiff ℝ ∞ fun t : ℝ => (t : ℂ) := Complex.ofRealCLM.contDiff
      have h2 : ContDiff ℝ ∞ fun t : ℝ => (t : ℂ) * I := h1.mul contDiff_const
      have h3 : ContDiff ℝ ∞ (Complex.exp : ℂ → ℂ) := Complex.contDiff_exp
      exact h3.comp h2
    have hcont : ContDiffOn ℝ ∞ (reflShell ψ) (annulus (1 - η)) :=
      (hrefl_d.contDiffOn (isOpen_annulus (1 - η))).restrict_scalars ℝ
    have hsmooth : ContDiff ℝ ∞ fun t : ℝ => reflShell ψ (Complex.exp (t * I)) :=
      hcont.comp_contDiff hC fun t => hcircle t
    have hnorm1 : ∀ t : ℝ, ‖reflShell ψ (Complex.exp (t * I))‖ = 1 := by
      intro t
      rw [reflShell_of_le_one (h := ψ) (le_of_eq (hexp_norm t))]
      exact hψsph _ (hexp_norm t)
    obtain ⟨σ, hσd, hσeq⟩ := contDiff_arg_lift_circle hsmooth hnorm1
    refine ⟨σ, hσd, fun t => ?_⟩
    rw [hFapp, if_pos (le_of_eq (hexp_norm t))]
    have h1 : Φ (Complex.exp (t * I)) = Γ (ψ (Complex.exp (t * I))) :=
      (hΨΓ _ (hηmap ⟨_, ⟨by rw [hexp_norm t]; linarith, by rw [hexp_norm t]⟩, rfl⟩)).symm
    rw [h1, ← reflShell_of_le_one (h := ψ) (z := Complex.exp (t * I)) (le_of_eq (hexp_norm t)),
      hσeq t, hΓcirc]
  exact ⟨(1 - η)⁻¹, hOne, F, hFd, hFi, fun z hz => deriv_ne_zero_of_injOn isOpen_ball hFd hFi z hz,
    hFeq, hσ⟩


end

end Work.RPB1a
