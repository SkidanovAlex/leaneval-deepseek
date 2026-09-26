import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Order.LeftRightNhds

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Set Metric
open scoped Topology

namespace Commons.Topology.Jordan

noncomputable section

private def pbOf (v w : ℂ) : ℂ →L[ℝ] ℝ :=
  (1/(w/v).im) • (Complex.imCLM.comp (ContinuousLinearMap.mul ℝ ℂ (1/v)))
private def paOf (v w : ℂ) : ℂ →L[ℝ] ℝ :=
  (Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (1/v))) - (w/v).re • pbOf v w
private lemma pbOf_apply (v w z : ℂ) :
    pbOf v w z = (z / v).im / (w/v).im := by
  have hμ : (ContinuousLinearMap.mul ℝ ℂ (1/v)) z = z / v := by
    rw [ContinuousLinearMap.mul_apply', one_div, div_eq_mul_inv]; ring
  simp only [pbOf, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hμ]
  rw [one_div, div_eq_mul_inv, Complex.imCLM_apply, div_eq_mul_inv]
  rw [div_eq_mul_inv, smul_eq_mul, mul_comm]
private lemma paOf_apply (v w z : ℂ) :
    paOf v w z = (z / v).re - (z/v).im / (w/v).im * (w/v).re := by
  have hμ : (ContinuousLinearMap.mul ℝ ℂ (1/v)) z = z / v := by
    rw [ContinuousLinearMap.mul_apply', one_div, div_eq_mul_inv]; ring
  simp only [paOf, pbOf_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, hμ]
  rw [Complex.reCLM_apply]
  simp only [smul_eq_mul]
  ring
private lemma paOf_v {v w : ℂ} (hv : v ≠ 0) : paOf v w v = 1 := by
  rw [paOf_apply, div_self hv]
  have : (1:ℂ).im = 0 := rfl
  simp
private lemma pbOf_v {v w : ℂ} (hv : v ≠ 0) : pbOf v w v = 0 := by
  rw [pbOf_apply, div_self hv]
  simp
private lemma paOf_w {v w : ℂ} (hw : (w/v).im ≠ 0) : paOf v w w = 0 := by
  rw [paOf_apply]
  have him : (w / v).im ≠ 0 := hw
  field_simp
  ring
private lemma pbOf_w {v w : ℂ} (hw : (w/v).im ≠ 0) : pbOf v w w = 1 := by
  rw [pbOf_apply]
  have him : (w / v).im ≠ 0 := hw
  field_simp
private lemma coord_id (v w : ℂ) (hv : v ≠ 0) (hw : (w/v).im ≠ 0) (c₀ z : ℂ) :
    z - c₀ = (paOf v w (z - c₀)) • v + (pbOf v w (z - c₀)) • w := by
  set s := z - c₀ with hs
  have key : (paOf v w s : ℂ) + (pbOf v w s : ℂ) * (w / v) = s / v := by
    rw [paOf_apply, pbOf_apply]
    rw [Complex.ofReal_sub, Complex.ofReal_mul]
    apply Complex.ext <;>
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        mul_zero, sub_zero, zero_sub, neg_zero]
    · field_simp; ring
    · field_simp; ring
  have hsv : s = (paOf v w s : ℂ) * v + (pbOf v w s : ℂ) * w := by
    calc s = s / v * v := (div_mul_cancel₀ s hv).symm
      _ = ((paOf v w s : ℂ) + (pbOf v w s : ℂ) * (w / v)) * v := by rw [key]
      _ = (paOf v w s : ℂ) * v + (pbOf v w s : ℂ) * w := by
            rw [add_mul, mul_assoc, div_mul_cancel₀ w hv]
  show s = (paOf v w s) • v + (pbOf v w s) • w
  conv_lhs => rw [hsv]
  simp [smul_eq_mul]

/-- Periods of the parametrisation: `γ t = γ t₀` iff `t - t₀ ∈ ℤ`. -/
private lemma gamma_eq_iff_exists_int (γ : ℝ → ℂ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1)) (t₀ t : ℝ) :
    γ t = γ t₀ ↔ ∃ k : ℤ, t = t₀ + k := by
  constructor
  · intro h
    have hft : γ t = γ (Int.fract t) := by
      have hh := (hper.int_mul ⌊t⌋) (Int.fract t)
      simp only [mul_one] at hh
      rw [Int.fract_add_floor] at hh
      exact hh
    have hf0 : γ t₀ = γ (Int.fract t₀) := by
      have hh := (hper.int_mul ⌊t₀⌋) (Int.fract t₀)
      simp only [mul_one] at hh
      rw [Int.fract_add_floor] at hh
      exact hh
    have hfract : Int.fract t = Int.fract t₀ := by
      refine hinj ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩
        ⟨Int.fract_nonneg t₀, Int.fract_lt_one t₀⟩ ?_
      rw [← hft, ← hf0]; exact h
    refine ⟨⌊t⌋ - ⌊t₀⌋, ?_⟩
    have h1 := Int.fract_add_floor t
    have h2 := Int.fract_add_floor t₀
    push_cast
    linarith
  · rintro ⟨k, rfl⟩
    have hh := (hper.int_mul k) t₀
    simp only [mul_one] at hh
    exact hh

/-- If `z` is a point of the curve within distance `d` of `γ t₀`, where `d` bounds the curve
away on the complement of `[t₀-r, t₀+r]`, then `z` is attained by a parameter in `[t₀-r, t₀+r]`. -/
private lemma exists_local_param_of_mem_ball
    (γ : ℝ → ℂ) (hper : Function.Periodic γ 1) (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1))
    (t₀ : ℝ) {r d : ℝ} (hr : 0 < r) (hr1 : r < 1/2)
    (hd : ∀ y ∈ γ '' Set.Icc (t₀ + r) (t₀ + 1 - r), d ≤ dist (γ t₀) y)
    {z : ℂ} (hz : z ∈ Set.range γ) (hzd : dist z (γ t₀) < d) :
    ∃ t ∈ Set.Icc (t₀ - r) (t₀ + r), γ t = z := by
  obtain ⟨t, rfl⟩ := hz
  set s : ℝ := (t₀ - r) + Int.fract (t - (t₀ - r)) with hs
  have hlow : t₀ - r ≤ s := by rw [hs]; linarith [Int.fract_nonneg (t - (t₀ - r))]
  have hhigh : s < t₀ + 1 - r := by rw [hs]; linarith [Int.fract_lt_one (t - (t₀ - r))]
  have hst : ∃ k : ℤ, t = s + k := by
    refine ⟨⌊t - (t₀ - r)⌋, ?_⟩
    have h := Int.fract_add_floor (t - (t₀ - r))
    rw [hs]; push_cast; linarith
  have hγs : γ s = γ t := by
    obtain ⟨k, hk⟩ := hst
    rw [hk]
    have h := (hper.int_mul k) s
    simp only [mul_one] at h
    exact h.symm
  rcases le_or_gt s (t₀ + r) with hle | hlt
  · exact ⟨s, ⟨hlow, hle⟩, hγs⟩
  · exfalso
    have hmem : γ t ∈ γ '' Set.Icc (t₀ + r) (t₀ + 1 - r) :=
      ⟨s, ⟨le_of_lt hlt, le_of_lt hhigh⟩, hγs⟩
    have h1 := hd (γ t) hmem
    rw [dist_comm] at h1
    linarith [hzd]

/-- The region above a continuous graph in a strip is preconnected. -/
private lemma isPreconnected_strip_above {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (φ : ℝ → ℝ)
    (hφ : ∀ α ∈ Ioo (-δ) δ, φ α < ρ/2) :
    IsPreconnected {p : ℝ × ℝ | p.1 ∈ Ioo (-δ) δ ∧ φ p.1 < p.2 ∧ p.2 < ρ} := by
  set σ : Set ℝ := Ioo (-δ) δ with hσ
  have hσ0 : (0:ℝ) ∈ σ := by rw [hσ]; exact ⟨by linarith, by linarith⟩
  have hpc : ∀ α : σ, IsPreconnected
      (({α.1} : Set ℝ) ×ˢ Ioo (φ α.1) ρ ∪ σ ×ˢ ({ρ/2} : Set ℝ)) := by
    intro α
    have hm : (α.1, ρ/2) ∈ ({α.1} : Set ℝ) ×ˢ Ioo (φ α.1) ρ :=
      ⟨rfl, hφ α.1 α.2, by linarith⟩
    have hm2 : (α.1, ρ/2) ∈ σ ×ˢ ({ρ/2} : Set ℝ) := ⟨α.2, rfl⟩
    exact IsPreconnected.union (α.1, ρ/2) hm hm2
      (isPreconnected_singleton.prod isPreconnected_Ioo)
      (isPreconnected_Ioo.prod isPreconnected_singleton)
  have hunion : (⋃ α : σ, (({α.1} : Set ℝ) ×ˢ Ioo (φ α.1) ρ ∪ σ ×ˢ ({ρ/2} : Set ℝ)))
      = {p : ℝ × ℝ | p.1 ∈ Ioo (-δ) δ ∧ φ p.1 < p.2 ∧ p.2 < ρ} := by
    ext p; constructor
    · intro hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨α, h⟩ := hp
      rcases h with h | h
      · simp only [Set.mem_prod, Set.mem_singleton_iff] at h
        exact ⟨h.1 ▸ α.2, h.1 ▸ h.2.1, h.2.2⟩
      · simp only [Set.mem_prod, Set.mem_singleton_iff] at h
        exact ⟨h.1, lt_of_lt_of_le (hφ p.1 h.1) (le_of_eq h.2.symm), by rw [h.2]; linarith⟩
    · rintro ⟨h1, h2, h3⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨p.1, h1⟩, Or.inl ⟨rfl, h2, h3⟩⟩
  rw [← hunion]
  refine isPreconnected_iUnion
    (s := fun α : σ => (({α.1} : Set ℝ) ×ˢ Ioo (φ α.1) ρ ∪ σ ×ˢ ({ρ/2} : Set ℝ)))
    ⟨(0, ρ/2), ?_⟩ hpc
  rw [Set.mem_iInter]
  intro α
  exact Or.inr ⟨hσ0, rfl⟩

/-- The region below a continuous graph in a strip is preconnected. -/
private lemma isPreconnected_strip_below {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (φ : ℝ → ℝ)
    (hφ : ∀ α ∈ Ioo (-δ) δ, -ρ/2 < φ α) :
    IsPreconnected {p : ℝ × ℝ | p.1 ∈ Ioo (-δ) δ ∧ -ρ < p.2 ∧ p.2 < φ p.1} := by
  set σ : Set ℝ := Ioo (-δ) δ with hσ
  have hσ0 : (0:ℝ) ∈ σ := by rw [hσ]; exact ⟨by linarith, by linarith⟩
  have hpc : ∀ α : σ, IsPreconnected
      (({α.1} : Set ℝ) ×ˢ Ioo (-ρ) (φ α.1) ∪ σ ×ˢ ({-ρ/2} : Set ℝ)) := by
    intro α
    have hm : (α.1, -ρ/2) ∈ ({α.1} : Set ℝ) ×ˢ Ioo (-ρ) (φ α.1) :=
      ⟨rfl, by linarith, hφ α.1 α.2⟩
    have hm2 : (α.1, -ρ/2) ∈ σ ×ˢ ({-ρ/2} : Set ℝ) := ⟨α.2, rfl⟩
    exact IsPreconnected.union (α.1, -ρ/2) hm hm2
      (isPreconnected_singleton.prod isPreconnected_Ioo)
      (isPreconnected_Ioo.prod isPreconnected_singleton)
  have hunion : (⋃ α : σ, (({α.1} : Set ℝ) ×ˢ Ioo (-ρ) (φ α.1) ∪ σ ×ˢ ({-ρ/2} : Set ℝ)))
      = {p : ℝ × ℝ | p.1 ∈ Ioo (-δ) δ ∧ -ρ < p.2 ∧ p.2 < φ p.1} := by
    ext p; constructor
    · intro hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨α, h⟩ := hp
      rcases h with h | h
      · simp only [Set.mem_prod, Set.mem_singleton_iff] at h
        exact ⟨h.1 ▸ α.2, h.2.1, h.1 ▸ h.2.2⟩
      · simp only [Set.mem_prod, Set.mem_singleton_iff] at h
        exact ⟨h.1, by rw [h.2]; linarith, lt_of_le_of_lt (le_of_eq h.2) (hφ p.1 h.1)⟩
    · rintro ⟨h1, h2, h3⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨p.1, h1⟩, Or.inl ⟨rfl, h2, h3⟩⟩
  rw [← hunion]
  refine isPreconnected_iUnion
    (s := fun α : σ => (({α.1} : Set ℝ) ×ˢ Ioo (-ρ) (φ α.1) ∪ σ ×ˢ ({-ρ/2} : Set ℝ)))
    ⟨(0, -ρ/2), ?_⟩ hpc
  rw [Set.mem_iInter]
  intro α
  exact Or.inr ⟨hσ0, rfl⟩

/-- **Local splitting of a neighbourhood of a regular point, transverse to a crossing curve.**

Given a continuous `1`-periodic injection `γ` that is `C¹` at `t₀` with non-zero derivative `v`,
and a curve `η` with `η 0 = γ t₀` whose derivative `w` at `0` is transverse to `v`
(`(w / v).im ≠ 0`), there is an open neighbourhood `W` of `γ t₀` split as
`W \ range γ = U ∪ V` into two preconnected open pieces such that `η s ∈ U` for every small
`s > 0` and `η (-s) ∈ V` for every small `s > 0`. -/
theorem local_split_transverse
    (γ : ℝ → ℂ) (hcont : Continuous γ) (hper : Function.Periodic γ 1)
    (hinj : Set.InjOn γ (Set.Ico (0:ℝ) 1))
    (t₀ : ℝ) (v : ℂ) (hv : v ≠ 0) (hder : ContDiffAt ℝ 1 γ t₀) (hdv : deriv γ t₀ = v)
    (η : ℝ → ℂ) (hη0 : η 0 = γ t₀) (w : ℂ) (hη : HasDerivAt η w 0) (hw : (w / v).im ≠ 0) :
    ∃ W : Set ℂ, IsOpen W ∧ γ t₀ ∈ W ∧
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ W \ Set.range γ = U ∪ V ∧
      IsPreconnected U ∧ IsPreconnected V ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → η s ∈ U) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → η (-s) ∈ V) := by
  classical
  have hγder : HasDerivAt γ v t₀ := by
    have h := (hder.differentiableAt one_ne_zero).hasDerivAt
    rwa [hdv] at h
  let a : ℝ → ℝ := fun t => paOf v w (γ t - γ t₀)
  let b : ℝ → ℝ := fun t => pbOf v w (γ t - γ t₀)
  have hb_cont : Continuous b := (pbOf v w).continuous.comp (hcont.sub continuous_const)
  have ha_deriv : HasDerivAt a 1 t₀ := by
    have h1 : HasDerivAt (fun t => γ t - γ t₀) v t₀ := hγder.sub_const _
    have h2 := (paOf v w).hasFDerivAt.comp_hasDerivAt t₀ h1
    rw [paOf_v hv] at h2
    exact h2
  have ha_cd : ContDiffAt ℝ 1 a t₀ :=
    (paOf v w).contDiff.contDiffAt.comp t₀ (hder.sub contDiffAt_const)
  have ha_sd : HasStrictDerivAt a 1 t₀ := ha_cd.hasStrictDerivAt' ha_deriv one_ne_zero
  have ha_sfd := ha_sd.hasStrictFDerivAt_equiv one_ne_zero
  let Pd : OpenPartialHomeomorph ℝ ℝ := ha_sfd.toOpenPartialHomeomorph a
  have hcoe : (Pd : ℝ → ℝ) = a := ha_sfd.toOpenPartialHomeomorph_coe
  have htsrc : t₀ ∈ Pd.source := ha_sfd.mem_toOpenPartialHomeomorph_source
  have h0tgt : a t₀ ∈ Pd.target := ha_sfd.image_mem_toOpenPartialHomeomorph_target
  have hat0 : a t₀ = 0 := by simp [a]
  have hbt0 : b t₀ = 0 := by simp [b]
  have hPd0 : Pd.symm 0 = t₀ := by
    have h := Pd.left_inv htsrc
    rw [hcoe, hat0] at h
    exact h
  have h0tgt' : (0:ℝ) ∈ Pd.target := by rwa [hat0] at h0tgt
  have hsrc_open : IsOpen Pd.source := Pd.open_source
  -- radius for the source interval
  obtain ⟨εs, hεs_pos, hεs_sub⟩ := Metric.mem_nhds_iff.mp (hsrc_open.mem_nhds htsrc)
  set r : ℝ := min εs 1 / 4 with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hr1 : r < 1/2 := by
    rw [hr]; have := min_le_right εs 1; linarith
  have hrsub : Set.Icc (t₀ - r) (t₀ + r) ⊆ Pd.source := by
    intro t ht
    apply hεs_sub
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : |t - t₀| ≤ r := by rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    calc |t - t₀| ≤ r := h1
      _ < εs := by rw [hr]; have := min_le_left εs 1; linarith
  -- far part of the curve
  set F : Set ℂ := γ '' Set.Icc (t₀ + r) (t₀ + 1 - r) with hF
  have hFcompact : IsCompact F := isCompact_Icc.image hcont
  have hFne : F.Nonempty := ⟨γ (t₀ + r), t₀ + r, ⟨le_rfl, by linarith⟩, rfl⟩
  have hcontF : Continuous (fun y : ℂ => dist (γ t₀) y) := continuous_const.dist continuous_id
  obtain ⟨y₀, hy₀F, hy₀min⟩ := hFcompact.exists_isMinOn hFne hcontF.continuousOn
  set d : ℝ := dist (γ t₀) y₀ with hd
  have hdpos : 0 < d := by
    rw [hd, dist_pos]
    intro hcon
    obtain ⟨s, hsIcc, hsy⟩ := hy₀F
    rw [← hsy] at hcon
    obtain ⟨k, hk⟩ := (gamma_eq_iff_exists_int γ hper hinj t₀ s).mp hcon.symm
    have hk' : (k : ℝ) = s - t₀ := by linarith [hk]
    have hs1 : r ≤ (k:ℝ) := by rw [hk']; linarith [hsIcc.1]
    have hs2 : (k:ℝ) ≤ 1 - r := by rw [hk']; linarith [hsIcc.2]
    have hk0 : (0:ℤ) < k := by exact_mod_cast (by linarith : (0:ℝ) < (k:ℝ))
    have hk1 : k < 1 := by exact_mod_cast (by linarith : (k:ℝ) < 1)
    omega
  have hdmin : ∀ y ∈ F, d ≤ dist (γ t₀) y := hy₀min
  -- coordinate radii
  have hwne : w ≠ 0 := by
    intro h0; rw [h0, zero_div, Complex.zero_im] at hw; exact hw rfl
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set ρ : ℝ := d / (4 * ‖w‖) with hρ
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.mem_nhds_iff.mp (Pd.open_target.mem_nhds h0tgt')
  have hφ0cont : ContinuousAt (fun α => b (Pd.symm α)) 0 :=
    hb_cont.continuousAt.comp (Pd.continuousAt_symm h0tgt')
  have hφ0val : b (Pd.symm 0) = 0 := by rw [hPd0]; exact hbt0
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.continuousAt_iff.mp hφ0cont (ρ/2) (by positivity)
  have hε₂' : ∀ x : ℝ, |x| < ε₂ → |b (Pd.symm x)| < ρ/2 := by
    intro x hx
    have h := hε₂ (by simpa [Real.dist_eq] using hx)
    simpa [Real.dist_eq, hφ0val] using h
  set δ : ℝ := min (min (ε₁/2) (ε₂/2)) (d / (4 * ‖v‖)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact lt_min (lt_min (by linarith) (by linarith)) (by positivity)
  have hδle1 : 2 * δ ≤ ε₁ := by
    rw [hδ]
    have h1 : min (min (ε₁/2) (ε₂/2)) (d/(4*‖v‖)) ≤ ε₁/2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hδtgt : Set.Ioo (-(2*δ)) (2*δ) ⊆ Pd.target := by
    intro t ht
    apply hε₁sub
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have h1 : |t| < 2 * δ := by rw [abs_lt]; exact ⟨by linarith [ht.1], ht.2⟩
    linarith
  have hδbox : δ * ‖v‖ + ρ * ‖w‖ < d := by
    have h1 : δ ≤ d / (4 * ‖v‖) := by
      rw [hδ]; exact min_le_right _ _
    have h2 : δ * ‖v‖ ≤ d / 4 := by
      calc δ * ‖v‖ ≤ (d / (4 * ‖v‖)) * ‖v‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
        _ = d / 4 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hvnorm.ne']
    have h3 : ρ * ‖w‖ = d / 4 := by rw [hρ]; field_simp
    linarith
  -- the clamp and the graph function
  let cl : ℝ → ℝ := fun α => max (-δ) (min α δ)
  have hcl_self : ∀ α ∈ Set.Icc (-δ) δ, cl α = α := by
    intro α hα; simp only [cl, min_eq_left hα.2, max_eq_right hα.1]
  have hcl_mem : ∀ α, cl α ∈ Set.Icc (-δ) δ := by
    intro α
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hcl_cont : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  let φ : ℝ → ℝ := fun α => b (Pd.symm (cl α))
  have hφ_cont : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro α
    have hmem : cl α ∈ Pd.target := hδtgt ⟨by have := (hcl_mem α).1; linarith,
      by have := (hcl_mem α).2; linarith⟩
    exact hb_cont.continuousAt.comp ((Pd.continuousAt_symm hmem).comp hcl_cont.continuousAt)
  have hφ0 : φ 0 = 0 := by
    show b (Pd.symm (cl 0)) = 0
    have hcl0 : cl 0 = 0 := by simp only [cl, min_eq_left (by linarith : (0:ℝ) ≤ δ),
      max_eq_right (by linarith : -δ ≤ 0)]
    rw [hcl0, hPd0, hbt0]
  have hδε₂ : δ ≤ ε₂ / 2 := by
    rw [hδ]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hφ_abs : ∀ α ∈ Set.Ioo (-δ) δ, |φ α| < ρ/2 := by
    intro α hα
    have hclα : cl α = α := hcl_self α ⟨le_of_lt hα.1, le_of_lt hα.2⟩
    have h2 : |α| < ε₂ := by
      rw [abs_lt]; exact ⟨by linarith [hα.1, hδε₂], by linarith [hα.2, hδε₂]⟩
    have hb := hε₂' α h2
    rwa [show φ α = b (Pd.symm α) from by simp only [φ, hclα]]
  have hφ_small : ∀ α ∈ Set.Ioo (-δ) δ, φ α < ρ/2 := by
    intro α hα; linarith [abs_lt.mp (hφ_abs α hα)]
  have hφ_big : ∀ α ∈ Set.Ioo (-δ) δ, -ρ/2 < φ α := by
    intro α hα; linarith [abs_lt.mp (hφ_abs α hα)]
  -- the three sets
  let W : Set ℂ := {z | paOf v w (z - γ t₀) ∈ Set.Ioo (-δ) δ ∧ pbOf v w (z - γ t₀) ∈ Set.Ioo (-ρ) ρ}
  let U : Set ℂ := {z | paOf v w (z - γ t₀) ∈ Set.Ioo (-δ) δ ∧
      pbOf v w (z - γ t₀) ∈ Set.Ioo (-ρ) ρ ∧ φ (paOf v w (z - γ t₀)) < pbOf v w (z - γ t₀)}
  let V : Set ℂ := {z | paOf v w (z - γ t₀) ∈ Set.Ioo (-δ) δ ∧
      pbOf v w (z - γ t₀) ∈ Set.Ioo (-ρ) ρ ∧ pbOf v w (z - γ t₀) < φ (paOf v w (z - γ t₀))}
  have hpa_cont : Continuous (fun z : ℂ => paOf v w (z - γ t₀)) :=
    (paOf v w).continuous.comp (continuous_id.sub continuous_const)
  have hpb_cont : Continuous (fun z : ℂ => pbOf v w (z - γ t₀)) :=
    (pbOf v w).continuous.comp (continuous_id.sub continuous_const)
  have hWo : IsOpen W := by
    have h1 : IsOpen {z : ℂ | paOf v w (z - γ t₀) ∈ Set.Ioo (-δ) δ} :=
      isOpen_Ioo.preimage hpa_cont
    have h2 : IsOpen {z : ℂ | pbOf v w (z - γ t₀) ∈ Set.Ioo (-ρ) ρ} :=
      isOpen_Ioo.preimage hpb_cont
    have heq : W = {z : ℂ | paOf v w (z - γ t₀) ∈ Set.Ioo (-δ) δ} ∩
        {z : ℂ | pbOf v w (z - γ t₀) ∈ Set.Ioo (-ρ) ρ} := by
      ext z; simp only [W, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [heq]; exact h1.inter h2
  have hWmem : γ t₀ ∈ W := by
    simp only [W, Set.mem_setOf_eq]
    constructor
    · rw [show γ t₀ - γ t₀ = 0 from sub_self _]; simp [hδpos, hρpos]
    · rw [show γ t₀ - γ t₀ = 0 from sub_self _]; simp [hδpos, hρpos]
  have hUo : IsOpen U := by
    have hcont : Continuous (fun z : ℂ => pbOf v w (z - γ t₀) - φ (paOf v w (z - γ t₀))) :=
      hpb_cont.sub (hφ_cont.comp hpa_cont)
    have h3 : IsOpen {z : ℂ | φ (paOf v w (z - γ t₀)) < pbOf v w (z - γ t₀)} := by
      have heq : {z : ℂ | φ (paOf v w (z - γ t₀)) < pbOf v w (z - γ t₀)}
          = (fun z : ℂ => pbOf v w (z - γ t₀) - φ (paOf v w (z - γ t₀))) ⁻¹' Set.Ioi 0 := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ioi, sub_pos]
      rw [heq]; exact isOpen_Ioi.preimage hcont
    have heq : U = W ∩ {z : ℂ | φ (paOf v w (z - γ t₀)) < pbOf v w (z - γ t₀)} := by
      ext z; simp only [U, W, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [heq]; exact hWo.inter h3
  have hVo : IsOpen V := by
    have hcont : Continuous (fun z : ℂ => pbOf v w (z - γ t₀) - φ (paOf v w (z - γ t₀))) :=
      hpb_cont.sub (hφ_cont.comp hpa_cont)
    have h3 : IsOpen {z : ℂ | pbOf v w (z - γ t₀) < φ (paOf v w (z - γ t₀))} := by
      have heq : {z : ℂ | pbOf v w (z - γ t₀) < φ (paOf v w (z - γ t₀))}
          = (fun z : ℂ => pbOf v w (z - γ t₀) - φ (paOf v w (z - γ t₀))) ⁻¹' Set.Iio 0 := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio, sub_neg]
      rw [heq]; exact isOpen_Iio.preimage hcont
    have heq : V = W ∩ {z : ℂ | pbOf v w (z - γ t₀) < φ (paOf v w (z - γ t₀))} := by
      ext z; simp only [V, W, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [heq]; exact hWo.inter h3
  -- the coordinate identity in the ambient plane
  have hcoord : ∀ z : ℂ, z - γ t₀ = (paOf v w (z - γ t₀)) • v + (pbOf v w (z - γ t₀)) • w :=
    coord_id v w hv hw (γ t₀)
  -- the graph property
  have hgraph : ∀ z ∈ W, (z ∈ Set.range γ ↔ pbOf v w (z - γ t₀) = φ (paOf v w (z - γ t₀))) := by
    intro z hzW
    obtain ⟨hzA, hzB⟩ := hzW
    have hαtgt : paOf v w (z - γ t₀) ∈ Pd.target :=
      hδtgt ⟨by linarith [hzA.1], by linarith [hzA.2]⟩
    constructor
    · intro hzr
      have hzd : dist z (γ t₀) < d := by
        rw [dist_eq_norm, hcoord z]
        calc ‖(paOf v w (z - γ t₀)) • v + (pbOf v w (z - γ t₀)) • w‖
            ≤ ‖(paOf v w (z - γ t₀)) • v‖ + ‖(pbOf v w (z - γ t₀)) • w‖ := norm_add_le _ _
          _ = |paOf v w (z - γ t₀)| * ‖v‖ + |pbOf v w (z - γ t₀)| * ‖w‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
          _ < δ * ‖v‖ + ρ * ‖w‖ := by
              have h1 : |paOf v w (z - γ t₀)| < δ := by rw [abs_lt]; exact ⟨hzA.1, hzA.2⟩
              have h2 : |pbOf v w (z - γ t₀)| < ρ := by rw [abs_lt]; exact ⟨hzB.1, hzB.2⟩
              nlinarith [norm_nonneg v, norm_nonneg w]
          _ < d := hδbox
      obtain ⟨t, htIcc, htγ⟩ := exists_local_param_of_mem_ball γ hper hinj t₀ hrpos hr1
        (fun y hy => hdmin y hy) hzr hzd
      have hPdt : Pd t = paOf v w (z - γ t₀) := by
        change a t = paOf v w (z - γ t₀)
        show paOf v w (γ t - γ t₀) = paOf v w (z - γ t₀)
        rw [htγ]
      have hsmm : Pd.symm (paOf v w (z - γ t₀)) = t := by
        have hs : Pd.symm (paOf v w (z - γ t₀)) ∈ Pd.source := Pd.map_target hαtgt
        exact Pd.injOn hs (hrsub htIcc) (by rw [Pd.right_inv hαtgt, hPdt])
      have hclα : cl (paOf v w (z - γ t₀)) = paOf v w (z - γ t₀) :=
        hcl_self _ ⟨le_of_lt hzA.1, le_of_lt hzA.2⟩
      have hφval : φ (paOf v w (z - γ t₀)) = b t := by
        change b (Pd.symm (cl (paOf v w (z - γ t₀)))) = b t
        rw [hclα, hsmm]
      rw [hφval]
      change pbOf v w (z - γ t₀) = pbOf v w (γ t - γ t₀)
      rw [htγ]
    · intro herr
      let s : ℝ := Pd.symm (paOf v w (z - γ t₀))
      have hsat : a s = paOf v w (z - γ t₀) := Pd.right_inv hαtgt
      have hclα : cl (paOf v w (z - γ t₀)) = paOf v w (z - γ t₀) :=
        hcl_self _ ⟨le_of_lt hzA.1, le_of_lt hzA.2⟩
      have hφval : φ (paOf v w (z - γ t₀)) = b s := by
        change b (Pd.symm (cl (paOf v w (z - γ t₀)))) = b (Pd.symm (paOf v w (z - γ t₀)))
        rw [hclα]
      have hbs : b s = pbOf v w (z - γ t₀) := hφval.symm.trans herr.symm
      refine ⟨s, ?_⟩
      have hsid : γ s - γ t₀ = (a s) • v + (b s) • w := coord_id v w hv hw (γ t₀) (γ s)
      have hzid : z - γ t₀ = (paOf v w (z - γ t₀)) • v + (pbOf v w (z - γ t₀)) • w := hcoord z
      have key : γ s - γ t₀ = z - γ t₀ := by
        rw [hsid, hsat, hbs]
        conv_rhs => rw [hzid]
      have key2 : γ s = z := by
        have := congrArg (fun w => w + γ t₀) key
        simpa using this
      exact key2
  -- W \ range γ = U ∪ V
  have hWUV : W \ Set.range γ = U ∪ V := by
    ext z
    have hiff := hgraph z
    constructor
    · rintro ⟨hzW, hzr⟩
      simp only [W, Set.mem_setOf_eq] at hzW
      obtain ⟨hzA, hzB⟩ := hzW
      have hne : pbOf v w (z - γ t₀) ≠ φ (paOf v w (z - γ t₀)) :=
        fun h => hzr ((hiff ⟨hzA, hzB⟩).mpr h)
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inr ⟨hzA, hzB, h⟩
      · exact Or.inl ⟨hzA, hzB, h⟩
    · rintro (⟨hzA, hzB, h⟩ | ⟨hzA, hzB, h⟩)
      · exact ⟨⟨hzA, hzB⟩, fun hzr => absurd ((hiff ⟨hzA, hzB⟩).mp hzr) (ne_of_gt h)⟩
      · exact ⟨⟨hzA, hzB⟩, fun hzr => absurd ((hiff ⟨hzA, hzB⟩).mp hzr) (ne_of_lt h)⟩
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    rintro z ⟨_, _, h1⟩ ⟨_, _, h2⟩
    exact absurd (lt_asymm h1 h2) (by simp)
  -- preconnectedness
  have hmap_cont : Continuous (fun p : ℝ × ℝ => γ t₀ + p.1 • v + p.2 • w) := by fun_prop
  have hUpc : IsPreconnected U := by
    have hR : IsPreconnected {p : ℝ × ℝ | p.1 ∈ Set.Ioo (-δ) δ ∧ φ p.1 < p.2 ∧ p.2 < ρ} :=
      isPreconnected_strip_above hδpos hρpos φ hφ_small
    have himg : (fun p : ℝ × ℝ => γ t₀ + p.1 • v + p.2 • w) ''
        {p : ℝ × ℝ | p.1 ∈ Set.Ioo (-δ) δ ∧ φ p.1 < p.2 ∧ p.2 < ρ} = U := by
      ext z; constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨hp1, hp2, hp3⟩ := hp
        have hφb : -ρ < φ p.1 := by linarith [(abs_lt.mp (hφ_abs p.1 hp1)).1]
        have e1 : paOf v w (γ t₀ + p.1 • v + p.2 • w - γ t₀) = p.1 := by
          rw [show γ t₀ + p.1 • v + p.2 • w - γ t₀ = p.1 • v + p.2 • w from by ring]
          rw [map_add, map_smul, map_smul, paOf_v hv, paOf_w hw]
          simp
        have e2 : pbOf v w (γ t₀ + p.1 • v + p.2 • w - γ t₀) = p.2 := by
          rw [show γ t₀ + p.1 • v + p.2 • w - γ t₀ = p.1 • v + p.2 • w from by ring]
          rw [map_add, map_smul, map_smul, pbOf_v hv, pbOf_w hw]
          simp
        simp only [U, Set.mem_setOf_eq, e1, e2]
        exact ⟨hp1, ⟨⟨hφb.trans hp2, hp3⟩, hp2⟩⟩
      · intro hz
        simp only [U, Set.mem_setOf_eq] at hz
        refine ⟨(paOf v w (z - γ t₀), pbOf v w (z - γ t₀)),
          ⟨hz.1, hz.2.2, hz.2.1.2⟩, ?_⟩
        show γ t₀ + (paOf v w (z - γ t₀)) • v + (pbOf v w (z - γ t₀)) • w = z
        have hz' : z = γ t₀ + (paOf v w (z - γ t₀)) • v + (pbOf v w (z - γ t₀)) • w := by
          conv_lhs => rw [show z = γ t₀ + (z - γ t₀) from by abel]
          conv_lhs => rw [hcoord z]
          abel
        conv_rhs => rw [hz']
    rw [← himg]
    exact hR.image _ hmap_cont.continuousOn
  have hVpc : IsPreconnected V := by
    have hR : IsPreconnected {p : ℝ × ℝ | p.1 ∈ Set.Ioo (-δ) δ ∧ -ρ < p.2 ∧ p.2 < φ p.1} :=
      isPreconnected_strip_below hδpos hρpos φ hφ_big
    have himg : (fun p : ℝ × ℝ => γ t₀ + p.1 • v + p.2 • w) ''
        {p : ℝ × ℝ | p.1 ∈ Set.Ioo (-δ) δ ∧ -ρ < p.2 ∧ p.2 < φ p.1} = V := by
      ext z; constructor
      · rintro ⟨p, hp, rfl⟩
        obtain ⟨hp1, hp2, hp3⟩ := hp
        have hφt : φ p.1 < ρ := by linarith [(abs_lt.mp (hφ_abs p.1 hp1)).2]
        have e1 : paOf v w (γ t₀ + p.1 • v + p.2 • w - γ t₀) = p.1 := by
          rw [show γ t₀ + p.1 • v + p.2 • w - γ t₀ = p.1 • v + p.2 • w from by ring]
          rw [map_add, map_smul, map_smul, paOf_v hv, paOf_w hw]
          simp
        have e2 : pbOf v w (γ t₀ + p.1 • v + p.2 • w - γ t₀) = p.2 := by
          rw [show γ t₀ + p.1 • v + p.2 • w - γ t₀ = p.1 • v + p.2 • w from by ring]
          rw [map_add, map_smul, map_smul, pbOf_v hv, pbOf_w hw]
          simp
        simp only [V, Set.mem_setOf_eq, e1, e2]
        exact ⟨hp1, ⟨hp2, hp3.trans hφt⟩, hp3⟩
      · intro hz
        simp only [V, Set.mem_setOf_eq] at hz
        refine ⟨(paOf v w (z - γ t₀), pbOf v w (z - γ t₀)),
          ⟨hz.1, hz.2.1.1, hz.2.2⟩, ?_⟩
        show γ t₀ + (paOf v w (z - γ t₀)) • v + (pbOf v w (z - γ t₀)) • w = z
        have hz' : z = γ t₀ + (paOf v w (z - γ t₀)) • v + (pbOf v w (z - γ t₀)) • w := by
          conv_lhs => rw [show z = γ t₀ + (z - γ t₀) from by abel]
          conv_lhs => rw [hcoord z]
          abel
        conv_rhs => rw [hz']
    rw [← himg]
    exact hR.image _ hmap_cont.continuousOn

  -- ### The crossing curve `η`
  -- the transverse coordinate `b` of the curve is differentiable with derivative `0` at `t₀`
  have hb_deriv : HasDerivAt b 0 t₀ := by
    have h1 : HasDerivAt (fun t => γ t - γ t₀) v t₀ := hγder.sub_const _
    have h := (pbOf v w).hasFDerivAt.comp_hasDerivAt t₀ h1
    rw [show (pbOf v w) v = 0 from pbOf_v hv] at h
    exact h
  -- the inverse of the tangential coordinate `a` has derivative `1` at `0`
  have hPd_symm : HasStrictDerivAt Pd.symm 1 0 := by
    have h := Pd.hasStrictDerivAt_symm (a := 0) (f' := 1) h0tgt' one_ne_zero
      (by rw [hcoe, hPd0]; exact ha_sd)
    simpa using h
  -- the (unclamped) graph function is differentiable at `0`
  have hψ : HasDerivAt (fun α => b (Pd.symm α)) 0 0 := by
    have hb' : HasDerivAt b 0 (Pd.symm 0) := by rw [hPd0]; exact hb_deriv
    have h := hb'.comp 0 hPd_symm.hasDerivAt
    simpa [Function.comp_def] using h
  have hcl_eq : cl =ᶠ[𝓝 (0:ℝ)] id := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδpos] with α hα
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] at hα
    exact hcl_self α ⟨hα.1.le, hα.2.le⟩
  have hcl_deriv : HasDerivAt cl 1 0 :=
    (hcl_eq.hasDerivAt_iff).mpr (hasDerivAt_id 0)
  have hcl0 : cl 0 = 0 := by
    simp only [cl, min_eq_left (by linarith : (0:ℝ) ≤ δ), max_eq_right (by linarith : -δ ≤ 0)]
  have hφ_deriv : HasDerivAt φ 0 0 := by
    have hψ' : HasDerivAt (fun α => b (Pd.symm α)) 0 (cl 0) := by rw [hcl0]; exact hψ
    have h := hψ'.comp 0 hcl_deriv
    have h' : HasDerivAt (fun α => b (Pd.symm (cl α))) 0 0 := by simpa [Function.comp_def] using h
    show HasDerivAt (fun α => b (Pd.symm (cl α))) 0 0
    exact h'
  -- derivatives of the two coordinates of `η` at `0`
  have hηderiv : HasDerivAt (fun s => η s - γ t₀) w 0 := hη.sub_const _
  have hP : HasDerivAt (fun s => paOf v w (η s - γ t₀)) 0 0 := by
    have h := (paOf v w).hasFDerivAt.comp_hasDerivAt 0 hηderiv
    rw [show (paOf v w) w = 0 from paOf_w hw] at h
    exact h
  have hQ : HasDerivAt (fun s => pbOf v w (η s - γ t₀)) 1 0 := by
    have h := (pbOf v w).hasFDerivAt.comp_hasDerivAt 0 hηderiv
    rw [show (pbOf v w) w = 1 from pbOf_w hw] at h
    exact h
  have hφP : HasDerivAt (fun s => φ (paOf v w (η s - γ t₀))) 0 0 := by
    have hφ0' : HasDerivAt φ 0 (paOf v w (η 0 - γ t₀)) := by
      rw [hη0, sub_self, map_zero]; exact hφ_deriv
    have h := hφ0'.comp 0 hP
    simpa [Function.comp_def] using h
  let G : ℝ → ℝ := fun s => pbOf v w (η s - γ t₀) - φ (paOf v w (η s - γ t₀))
  have hG : HasDerivAt G 1 0 := by
    have h := hQ.sub hφP
    have h2 : HasDerivAt (fun s => pbOf v w (η s - γ t₀) - φ (paOf v w (η s - γ t₀)))
        (1 - 0) 0 := h
    rw [sub_zero] at h2
    show HasDerivAt (fun s => pbOf v w (η s - γ t₀) - φ (paOf v w (η s - γ t₀))) 1 0
    exact h2
  have hG0 : G 0 = 0 := by
    show pbOf v w (η 0 - γ t₀) - φ (paOf v w (η 0 - γ t₀)) = 0
    rw [hη0, sub_self, map_zero, map_zero, hφ0, sub_zero]
  -- `G > 0` just to the right of `0` and `G < 0` just to its left
  have hGright : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → 0 < G s := by
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), (1/2 : ℝ) < t⁻¹ * G t := by
      have h := hG.tendsto_slope_zero_right.eventually
        (isOpen_Ioi.mem_nhds (by norm_num : (1/2:ℝ) < 1))
      filter_upwards [h] with t ht
      simpa [hG0, zero_add, smul_eq_mul] using ht
    obtain ⟨b, hbpos, hb⟩ := (nhdsGT_basis (0:ℝ)).mem_iff.mp hev
    refine ⟨b, hbpos, fun s hs hlt => ?_⟩
    have h1 : (1/2:ℝ) < s⁻¹ * G s := hb ⟨hs, hlt⟩
    have h2 : G s = s * (s⁻¹ * G s) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
    rw [h2]; nlinarith [h1, hs]
  have hGleft : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → G (-s) < 0 := by
    have hev : ∀ᶠ t in 𝓝[<] (0:ℝ), (1/2 : ℝ) < t⁻¹ * G t := by
      have h := hG.tendsto_slope_zero_left.eventually
        (isOpen_Ioi.mem_nhds (by norm_num : (1/2:ℝ) < 1))
      filter_upwards [h] with t ht
      simpa [hG0, zero_add, smul_eq_mul] using ht
    obtain ⟨b, hbneg, hb⟩ := (nhdsLT_basis (0:ℝ)).mem_iff.mp hev
    refine ⟨-b, by linarith, fun s hs hlt => ?_⟩
    have ht : -s ∈ Set.Ioo b 0 := ⟨by linarith, by linarith⟩
    have h1 : (1/2:ℝ) < (-s)⁻¹ * G (-s) := hb ht
    rw [inv_neg] at h1
    have h2 : G (-s) = s * (s⁻¹ * G (-s)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
    have h3 : s⁻¹ * G (-s) < -(1/2:ℝ) := by linarith
    rw [h2]; nlinarith [h3, hs]
  obtain ⟨ε₃, hε₃pos, hε₃⟩ := hGright
  obtain ⟨ε₅, hε₅pos, hε₅⟩ := hGleft
  -- the coordinates of `η` lie in the box for small parameters
  have hPcont : ContinuousAt (fun s => paOf v w (η s - γ t₀)) 0 :=
    ((paOf v w).continuous.continuousAt).comp (hη.continuousAt.sub_const (γ t₀))
  have hQcont : ContinuousAt (fun s => pbOf v w (η s - γ t₀)) 0 :=
    ((pbOf v w).continuous.continuousAt).comp (hη.continuousAt.sub_const (γ t₀))
  have hPbox : ∀ᶠ s in 𝓝 (0:ℝ), paOf v w (η s - γ t₀) ∈ Set.Ioo (-δ) δ := by
    have hnhds : Set.Ioo (-δ) δ ∈ 𝓝 ((fun s : ℝ => paOf v w (η s - γ t₀)) 0) := by
      have h0 : ((fun s : ℝ => paOf v w (η s - γ t₀)) 0) = (0:ℝ) := by
        show paOf v w (η 0 - γ t₀) = 0
        rw [hη0, sub_self, map_zero]
      rw [h0]
      exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    exact hPcont.eventually hnhds
  have hQbox : ∀ᶠ s in 𝓝 (0:ℝ), pbOf v w (η s - γ t₀) ∈ Set.Ioo (-ρ) ρ := by
    have hnhds : Set.Ioo (-ρ) ρ ∈ 𝓝 ((fun s : ℝ => pbOf v w (η s - γ t₀)) 0) := by
      have h0 : ((fun s : ℝ => pbOf v w (η s - γ t₀)) 0) = (0:ℝ) := by
        show pbOf v w (η 0 - γ t₀) = 0
        rw [hη0, sub_self, map_zero]
      rw [h0]
      exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    exact hQcont.eventually hnhds
  obtain ⟨ε₄, hε₄pos, hε₄⟩ := Metric.eventually_nhds_iff.mp (hPbox.and hQbox)
  refine ⟨W, hWo, hWmem, U, V, hUo, hVo, hdisj, hWUV, hUpc, hVpc, ?_, ?_⟩
  · refine ⟨min ε₃ ε₄, lt_min hε₃pos hε₄pos, ?_⟩
    intro s hs hlt
    have hs3 : s < ε₃ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hs4 : s < ε₄ := lt_of_lt_of_le hlt (min_le_right _ _)
    have hbox := hε₄ (y := s) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; exact hs4)
    have hg := hε₃ s hs hs3
    show paOf v w (η s - γ t₀) ∈ Set.Ioo (-δ) δ ∧
      pbOf v w (η s - γ t₀) ∈ Set.Ioo (-ρ) ρ ∧
      φ (paOf v w (η s - γ t₀)) < pbOf v w (η s - γ t₀)
    exact ⟨hbox.1, hbox.2, by linarith [hg]⟩
  · refine ⟨min ε₅ ε₄, lt_min hε₅pos hε₄pos, ?_⟩
    intro s hs hlt
    have hs5 : s < ε₅ := lt_of_lt_of_le hlt (min_le_left _ _)
    have hs4 : s < ε₄ := lt_of_lt_of_le hlt (min_le_right _ _)
    have hbox := hε₄ (y := -s) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hs]; exact hs4)
    have hg := hε₅ s hs hs5
    show paOf v w (η (-s) - γ t₀) ∈ Set.Ioo (-δ) δ ∧
      pbOf v w (η (-s) - γ t₀) ∈ Set.Ioo (-ρ) ρ ∧
      pbOf v w (η (-s) - γ t₀) < φ (paOf v w (η (-s) - γ t₀))
    exact ⟨hbox.1, hbox.2, by linarith [hg]⟩


end

end Commons.Topology.Jordan
