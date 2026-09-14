import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology

open Filter Metric
open scoped Topology

namespace Commons.Analysis.Calculus

/-- If `g : ℝ → ℝ` is continuous at `0` and has a local minimum at `0`, then the second
derivative of `g` at `0` is nonnegative (in the junk case where `deriv g` is not differentiable
at `0`, `deriv (deriv g) 0` is `0` and the claim is trivial). -/
lemma deriv_deriv_nonneg_of_isLocalMin {g : ℝ → ℝ} (hcont : ContinuousAt g 0)
    (hmin : IsLocalMin g 0) : 0 ≤ deriv (deriv g) 0 := by
  by_contra hneg
  rw [not_le] at hneg
  by_cases hd : DifferentiableAt ℝ (deriv g) 0
  · have hder : HasDerivAt (deriv g) (deriv (deriv g) 0) 0 := hd.hasDerivAt
    have hg0 : deriv g 0 = 0 := by
      by_cases hgd : DifferentiableAt ℝ g 0
      · exact hmin.deriv_eq_zero
      · exact deriv_zero_of_not_differentiableAt hgd
    have hslope : Tendsto (slope (deriv g) 0) (𝓝[{0}ᶜ] (0:ℝ)) (𝓝 (deriv (deriv g) 0)) :=
      hder.tendsto_slope
    have hev : ∀ᶠ s in 𝓝[{0}ᶜ] (0:ℝ), slope (deriv g) 0 s < deriv (deriv g) 0 / 2 :=
      Filter.Tendsto.eventually_lt_const (by linarith) hslope
    rw [eventually_nhdsWithin_iff] at hev
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hev
    have hmn : ∀ᶠ s in 𝓝 (0:ℝ), g 0 ≤ g s := hmin
    rw [Metric.eventually_nhds_iff] at hmn
    obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hmn
    set δ := min δ₁ δ₂ with hδdef
    have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
    have hδle₁ : δ ≤ δ₁ := min_le_left _ _
    have hδle₂ : δ ≤ δ₂ := min_le_right _ _
    have hderneg : ∀ s, 0 < s → s < δ → deriv g s < 0 := by
      intro s hs hs2
      have hsne : s ∈ ({0}ᶜ : Set ℝ) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith
      have hdist : dist s 0 < δ₁ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hs]; linarith
      have h1 := hδ₁ hdist hsne
      rw [slope_def_field] at h1
      simp only [sub_zero, hg0] at h1
      have hL2 : deriv (deriv g) 0 / 2 < 0 := by linarith
      have h1neg : deriv g s / s < 0 := h1.trans hL2
      by_contra hcon
      rw [not_lt] at hcon
      have hpos : 0 ≤ deriv g s / s := div_nonneg hcon (le_of_lt hs)
      linarith
    have hdiffAt : ∀ s ∈ Set.Ioo (0:ℝ) δ, DifferentiableAt ℝ g s := by
      intro s hs
      by_contra hnd
      have hz : deriv g s = 0 := deriv_zero_of_not_differentiableAt hnd
      have := hderneg s hs.1 hs.2
      linarith
    have hcontOn : ContinuousOn g (Set.Icc (0:ℝ) (δ/2)) := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · rw [← hx0]
        exact hcont.continuousWithinAt
      · have hxlt : x < δ := lt_of_le_of_lt hx.2 (by linarith)
        exact ((hdiffAt x ⟨hx0, hxlt⟩).continuousAt).continuousWithinAt
    have hdiffOn : DifferentiableOn ℝ g (Set.Ioo (0:ℝ) (δ/2)) := by
      intro x hx
      exact (hdiffAt x ⟨hx.1, lt_trans hx.2 (by linarith)⟩).differentiableWithinAt
    have hδhalfpos : (0:ℝ) < δ/2 := by linarith
    obtain ⟨c, hc, hcder⟩ := exists_deriv_eq_slope g hδhalfpos hcontOn hdiffOn
    have hcneg : deriv g c < 0 := hderneg c hc.1 (lt_trans hc.2 (by linarith))
    rw [sub_zero] at hcder
    have hquot : (g (δ/2) - g 0) / (δ/2) < 0 := by rw [← hcder]; exact hcneg
    have hlt : g (δ/2) < g 0 := by
      have h2 := mul_neg_of_neg_of_pos hquot hδhalfpos
      rw [div_mul_cancel₀ _ (ne_of_gt hδhalfpos)] at h2
      linarith
    have hge : g 0 ≤ g (δ/2) := by
      apply hδ₂
      rw [Real.dist_eq, sub_zero, abs_of_pos hδhalfpos]
      linarith
    linarith
  · have hz : deriv (deriv g) 0 = 0 := deriv_zero_of_not_differentiableAt hd
    rw [hz] at hneg
    exact lt_irrefl _ hneg

theorem parabolic_min_principle_diagonal
    (V : ℝ × ℝ × ℝ → ℝ)
    (hcont : ContinuousOn V {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2})
    (h0 : ∀ x y : ℝ, 0 ≤ V (x, y, 0))
    (hinf : ∀ δ > 0, ∀ T > 0, ∃ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x y : ℝ,
      R ≤ |x| + |y| → -δ ≤ V (x, y, t))
    (hderivt : ∀ x y t : ℝ, 0 < t → HasDerivAt (fun u : ℝ => V (x, y, u))
      (deriv (fun u : ℝ => V (x, y, u)) t) t)
    (hhill : ∀ t x y : ℝ, 0 < t →
      IsLocalMin (fun p : ℝ × ℝ => V (p.1, p.2, t)) (x, y) →
      deriv (deriv (fun s : ℝ => V (x + s, y + s, t))) 0
        ≤ 4 * Real.pi * deriv (fun u : ℝ => V (x, y, u)) t) :
    ∀ x y t : ℝ, 0 ≤ t → 0 ≤ V (x, y, t) := by
  intro x y t ht
  by_contra hneg
  rw [not_le] at hneg
  have htpos : 0 < t := by
    rcases lt_or_eq_of_le ht with h | h
    · exact h
    · exfalso
      have ht0 : t = 0 := h.symm
      rw [ht0] at hneg
      have := h0 x y
      linarith
  set a : ℝ := - V (x, y, t) with hadef
  have hapos : 0 < a := by rw [hadef]; exact neg_pos.mpr hneg
  have hVeq : V (x, y, t) = -a := by rw [hadef, neg_neg]
  set lam : ℝ := a / (4 * t) with hlamdef
  have hlampos : 0 < lam := by
    rw [hlamdef]; exact div_pos hapos (by positivity)
  have hlamt : lam * t = a / 4 := by
    rw [hlamdef]; field_simp
  set W : ℝ × ℝ × ℝ → ℝ := fun p => V p + lam * p.2.2 with hWdef
  have hWxy : W (x, y, t) = -(3*a/4) := by
    simp only [hWdef]; rw [hVeq, hlamt]; ring
  set T' : ℝ := t + 1 with hT'def
  have hT'pos : 0 < T' := by rw [hT'def]; linarith
  have ht_lt_T' : t < T' := by rw [hT'def]; linarith
  obtain ⟨R₁, hR₁⟩ := hinf (a/2) (by linarith) T' hT'pos
  have hR₁pos : 0 < R₁ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hxy : R₁ ≤ |x| + |y| := le_trans hcon (by positivity)
    have := hR₁ t ⟨le_of_lt htpos, le_of_lt ht_lt_T'⟩ x y hxy
    rw [hVeq] at this
    linarith
  set B : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (-R₁) R₁ ×ˢ (Set.Icc (-R₁) R₁ ×ˢ Set.Icc (0:ℝ) T') with hBdef
  have hxy_lt : |x| + |y| < R₁ := by
    by_contra hcon; rw [not_lt] at hcon
    have := hR₁ t ⟨le_of_lt htpos, le_of_lt ht_lt_T'⟩ x y hcon
    rw [hVeq] at this; linarith
  have hxR : |x| ≤ R₁ := le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (abs_nonneg y)) hxy_lt)
  have hyR : |y| ≤ R₁ := le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_left (abs_nonneg x)) hxy_lt)
  have hmemB : (x, y, t) ∈ B := by
    rw [hBdef, Set.mem_prod, Set.mem_prod, Set.mem_Icc, Set.mem_Icc, Set.mem_Icc]
    exact ⟨abs_le.mp hxR, abs_le.mp hyR, le_of_lt htpos, le_of_lt ht_lt_T'⟩
  have hBcompact : IsCompact B := by
    rw [hBdef]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hBne : B.Nonempty := ⟨_, hmemB⟩
  have hWcontOn : ContinuousOn W B := by
    rw [hWdef]
    have hsub : B ⊆ {p : ℝ × ℝ × ℝ | 0 ≤ p.2.2} := by
      intro p hp
      rw [hBdef] at hp
      simp only [Set.mem_prod, Set.mem_Icc] at hp
      exact hp.2.2.1
    refine ContinuousOn.add ?_ ?_
    · exact hcont.mono hsub
    · exact ((continuous_const.mul ((continuous_snd.comp continuous_snd))).continuousOn)
  obtain ⟨p₀, hp₀B, hp₀min⟩ := hBcompact.exists_isMinOn hBne hWcontOn
  obtain ⟨x₀, y₀, t₀⟩ := p₀
  have hp₀mem := hp₀B
  rw [hBdef] at hp₀mem
  simp only [Set.mem_prod, Set.mem_Icc] at hp₀mem
  have hx₀R : |x₀| ≤ R₁ := abs_le.mpr ⟨hp₀mem.1.1, hp₀mem.1.2⟩
  have hy₀R : |y₀| ≤ R₁ := abs_le.mpr ⟨hp₀mem.2.1.1, hp₀mem.2.1.2⟩
  have ht₀ge : 0 ≤ t₀ := hp₀mem.2.2.1
  have ht₀le : t₀ ≤ T' := hp₀mem.2.2.2
  have hmin' := isMinOn_iff.mp hp₀min
  have hμ : W (x₀, y₀, t₀) ≤ W (x, y, t) := hmin' (x,y,t) hmemB
  have hμlt : W (x₀, y₀, t₀) < -a/2 := by rw [hWxy] at hμ; linarith
  have ht₀pos : 0 < t₀ := by
    by_contra hcon
    rw [not_lt] at hcon
    have ht₀0 : t₀ = 0 := le_antisymm hcon ht₀ge
    have hW0 : W (x₀, y₀, t₀) = V (x₀, y₀, 0) := by
      rw [ht₀0]; simp only [hWdef, mul_zero, add_zero]
    rw [hW0] at hμlt
    have := h0 x₀ y₀
    linarith
  have hx₀lt : |x₀| < R₁ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hsum : R₁ ≤ |x₀| + |y₀| := le_trans hcon (le_add_of_nonneg_right (abs_nonneg y₀))
    have hVge : -(a/2) ≤ V (x₀, y₀, t₀) := hR₁ t₀ ⟨ht₀ge, ht₀le⟩ x₀ y₀ hsum
    have hWge : -(a/2) ≤ W (x₀, y₀, t₀) := by
      have hWeq : W (x₀, y₀, t₀) = V (x₀, y₀, t₀) + lam * t₀ := by simp only [hWdef]
      rw [hWeq]
      have : 0 ≤ lam * t₀ := mul_nonneg (le_of_lt hlampos) ht₀ge
      linarith
    linarith
  have hy₀lt : |y₀| < R₁ := by
    by_contra hcon
    rw [not_lt] at hcon
    have hsum : R₁ ≤ |x₀| + |y₀| := le_trans hcon (le_add_of_nonneg_left (abs_nonneg x₀))
    have hVge : -(a/2) ≤ V (x₀, y₀, t₀) := hR₁ t₀ ⟨ht₀ge, ht₀le⟩ x₀ y₀ hsum
    have hWge : -(a/2) ≤ W (x₀, y₀, t₀) := by
      have hWeq : W (x₀, y₀, t₀) = V (x₀, y₀, t₀) + lam * t₀ := by simp only [hWdef]
      rw [hWeq]
      have : 0 ≤ lam * t₀ := mul_nonneg (le_of_lt hlampos) ht₀ge
      linarith
    linarith
  have hminspatial : IsMinOn (fun p : ℝ × ℝ => V (p.1, p.2, t₀))
      (Set.Icc (-R₁) R₁ ×ˢ Set.Icc (-R₁) R₁) (x₀, y₀) := by
    rw [isMinOn_iff]
    intro u hu
    rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc] at hu
    have huinB : (u.1, u.2, t₀) ∈ B := by
      rw [hBdef, Set.mem_prod, Set.mem_prod, Set.mem_Icc, Set.mem_Icc, Set.mem_Icc]
      exact ⟨hu.1, hu.2, ht₀ge, ht₀le⟩
    have := hmin' (u.1,u.2,t₀) huinB
    simp only [hWdef] at this
    linarith
  have hminV : IsLocalMin (fun p : ℝ × ℝ => V (p.1, p.2, t₀)) (x₀, y₀) :=
    hminspatial.isLocalMin (by
      have hopen : IsOpen (Set.Ioo (-R₁) R₁ ×ˢ Set.Ioo (-R₁) R₁) := isOpen_Ioo.prod isOpen_Ioo
      have hmem : (x₀,y₀) ∈ Set.Ioo (-R₁) R₁ ×ˢ Set.Ioo (-R₁) R₁ := by
        rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
        exact ⟨abs_lt.mp hx₀lt, abs_lt.mp hy₀lt⟩
      refine mem_of_superset (hopen.mem_nhds hmem) ?_
      intro p hp
      rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo] at hp
      rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
      exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩⟩)
  have hcontV0 : ContinuousAt V (x₀, y₀, t₀) := by
    apply hcont.continuousAt
    have hopen : IsOpen {p : ℝ × ℝ × ℝ | 0 < p.2.2} :=
      isOpen_lt continuous_const (continuous_snd.comp continuous_snd)
    have hmem : (x₀, y₀, t₀) ∈ {p : ℝ × ℝ × ℝ | 0 < p.2.2} := ht₀pos
    refine mem_of_superset (hopen.mem_nhds hmem) ?_
    intro p hp
    exact le_of_lt (by simpa using hp)
  have hg : ContinuousAt (fun s : ℝ => V (x₀ + s, y₀ + s, t₀)) 0 := by
    have hφ : ContinuousAt (fun s : ℝ => (x₀ + s, y₀ + s, t₀)) 0 := by fun_prop
    exact ContinuousAt.comp (f := fun s : ℝ => (x₀ + s, y₀ + s, t₀)) (g := V) (x := 0)
      (by simpa using hcontV0) hφ
  have hmin_g : IsLocalMin (fun s : ℝ => V (x₀ + s, y₀ + s, t₀)) 0 := by
    have hψ : ContinuousAt (fun s : ℝ => (x₀ + s, y₀ + s)) 0 := by fun_prop
    exact IsLocalMin.comp_continuous (f := fun p : ℝ × ℝ => V (p.1, p.2, t₀))
      (g := fun s : ℝ => (x₀ + s, y₀ + s)) (b := 0) (by simpa using hminV) hψ
  have hLHSnn : 0 ≤ deriv (deriv (fun s : ℝ => V (x₀ + s, y₀ + s, t₀))) 0 :=
    deriv_deriv_nonneg_of_isLocalMin hg hmin_g
  have hhillapp := hhill t₀ x₀ y₀ ht₀pos hminV
  have hdtnn : 0 ≤ deriv (fun u : ℝ => V (x₀, y₀, u)) t₀ := by
    nlinarith [hLHSnn, hhillapp, Real.pi_pos]
  have hderW : HasDerivAt (fun s : ℝ => W (x₀, y₀, s))
      (deriv (fun u : ℝ => V (x₀, y₀, u)) t₀ + lam) t₀ := by
    have h1 : HasDerivAt (fun s : ℝ => V (x₀, y₀, s)) (deriv (fun u : ℝ => V (x₀,y₀,u)) t₀) t₀ :=
      hderivt x₀ y₀ t₀ ht₀pos
    have h2 : HasDerivAt (fun s : ℝ => lam * s) lam t₀ := by
      simpa using (hasDerivAt_id t₀).const_mul lam
    have h3 := h1.add h2
    have hfun : (fun s : ℝ => V (x₀, y₀, s)) + (fun s : ℝ => lam * s) = (fun s : ℝ => W (x₀, y₀, s)) := by
      ext s; simp only [Pi.add_apply, hWdef]
    rw [hfun] at h3
    exact h3
  have hDle : deriv (fun u : ℝ => V (x₀, y₀, u)) t₀ + lam ≤ 0 := by
    have hslope := hderW.tendsto_slope
    have hle : 𝓝[<] t₀ ≤ 𝓝[{t₀}ᶜ] t₀ :=
      nhdsWithin_mono t₀ (by intro s hs; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_lt hs)
    have hslope' : Tendsto (slope (fun s : ℝ => W (x₀, y₀, s)) t₀) (𝓝[<] t₀)
        (𝓝 (deriv (fun u : ℝ => V (x₀, y₀, u)) t₀ + lam)) := hslope.mono_left hle
    apply le_of_tendsto hslope'
    have hge : ∀ᶠ s in 𝓝[<] t₀, 0 ≤ s := by
      have h0lt : ∀ᶠ s in 𝓝 t₀, (0:ℝ) < s := eventually_gt_nhds ht₀pos
      filter_upwards [h0lt.filter_mono nhdsWithin_le_nhds] with s hs
      exact le_of_lt hs
    have hlt : ∀ᶠ s in 𝓝[<] t₀, s < t₀ := self_mem_nhdsWithin
    filter_upwards [hge, hlt] with s hs0 hst
    rw [slope_def_field]
    apply div_nonpos_of_nonneg_of_nonpos
    · have hsB : (x₀, y₀, s) ∈ B := by
        rw [hBdef, Set.mem_prod, Set.mem_prod, Set.mem_Icc, Set.mem_Icc, Set.mem_Icc]
        exact ⟨abs_le.mp hx₀R, abs_le.mp hy₀R, hs0, le_trans (le_of_lt hst) ht₀le⟩
      have := hmin' (x₀,y₀,s) hsB
      linarith
    · linarith
  have hdtpos : 0 < deriv (fun u : ℝ => V (x₀, y₀, u)) t₀ + lam := by linarith
  linarith

end Commons.Analysis.Calculus