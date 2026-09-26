import Mathlib

namespace Work.Analysis.DiscreteValues

private lemma norm_two_pi_I : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
  have h2pi : (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [h2pi, norm_mul, Complex.norm_I, mul_one, Complex.norm_def, Complex.normSq_ofReal,
    Real.sqrt_mul_self (by positivity)]

private lemma dist_lattice (n n₀ : ℤ) :
    dist (n * (2 * Real.pi * Complex.I)) (n₀ * (2 * Real.pi * Complex.I))
      = 2 * Real.pi * |((n - n₀ : ℤ) : ℝ)| := by
  have h1 : (n : ℂ) * (2 * Real.pi * Complex.I) - (n₀ : ℂ) * (2 * Real.pi * Complex.I)
      = ((n : ℂ) - (n₀ : ℂ)) * (2 * Real.pi * Complex.I) := by ring
  have hcast : (n : ℂ) - (n₀ : ℂ) = ((n - n₀ : ℤ) : ℂ) := by push_cast; ring
  rw [dist_eq_norm, h1, hcast, norm_mul, Complex.norm_intCast, norm_two_pi_I]
  ring

private lemma lattice_eq_of_dist_lt (n n₀ : ℤ)
    (h : dist (n * (2 * Real.pi * Complex.I)) (n₀ * (2 * Real.pi * Complex.I)) < Real.pi) :
    n = n₀ := by
  rw [dist_lattice] at h
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : 2 * |((n - n₀ : ℤ) : ℝ)| < 1 := by
    have h' : Real.pi * (2 * |((n - n₀ : ℤ) : ℝ)|) < Real.pi * 1 := by
      rw [mul_one]
      rwa [show 2 * Real.pi * |((n - n₀ : ℤ) : ℝ)|
            = Real.pi * (2 * |((n - n₀ : ℤ) : ℝ)|) by ring] at h
    exact lt_of_mul_lt_mul_left h' (le_of_lt hpi)
  have h2 : ((|n - n₀| : ℤ) : ℝ) < 1 := by
    rw [Int.cast_abs]; linarith
  have h3 : |n - n₀| < (1:ℤ) := by exact_mod_cast h2
  have h4 : n - n₀ = 0 := Int.abs_lt_one_iff.mp h3
  omega

private lemma dist_gt_of_ne (n n₀ : ℤ) (h : n ≠ n₀) :
    Real.pi < dist (n * (2 * Real.pi * Complex.I)) (n₀ * (2 * Real.pi * Complex.I)) := by
  rw [dist_lattice]
  have hk : (1:ℤ) ≤ |n - n₀| := Int.one_le_abs (sub_ne_zero.mpr h)
  have hk' : (1:ℝ) ≤ ((|n - n₀| : ℤ) : ℝ) := by exact_mod_cast hk
  rw [Int.cast_abs] at hk'
  have hmono : 2 * Real.pi * 1 ≤ 2 * Real.pi * |((n - n₀ : ℤ) : ℝ)| :=
    mul_le_mul_of_nonneg_left hk' (by positivity)
  linarith [hmono, Real.pi_pos]

theorem eq_const_of_isPreconnected {h : ℂ → ℂ} {V : Set ℂ} (hV : IsPreconnected V)
    (hc : ContinuousOn h V) (hval : ∀ z ∈ V, ∃ n : ℤ, h z = n * (2 * Real.pi * Complex.I))
    {z₀ : ℂ} (hz₀ : z₀ ∈ V) : ∀ z ∈ V, h z = h z₀ := by
  obtain ⟨n₀, hn₀⟩ := hval z₀ hz₀
  have himg : IsPreconnected (h '' V) := hV.image h hc
  have hneπ : ∀ z ∈ V, dist (h z) (h z₀) ≠ Real.pi := by
    intro z hz
    obtain ⟨n, hn⟩ := hval z hz
    rcases eq_or_ne n n₀ with heq | hne
    · subst heq
      rw [hn, hn₀, dist_self]
      exact (Real.pi_pos.ne').symm
    · rw [hn, hn₀]
      exact (dist_gt_of_ne n n₀ hne).ne'
  have hclose : ∀ w ∈ h '' V, dist w (h z₀) < Real.pi := by
    intro w hw
    by_contra hcon
    rw [not_lt] at hcon
    obtain ⟨z, hz, rfl⟩ := hw
    have hgt : Real.pi < dist (h z) (h z₀) := lt_of_le_of_ne hcon (Ne.symm (hneπ z hz))
    have hU : IsOpen (Metric.ball (h z₀) Real.pi) := Metric.isOpen_ball
    have hW : IsOpen {u : ℂ | Real.pi < dist u (h z₀)} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    have hcover : h '' V ⊆ Metric.ball (h z₀) Real.pi ∪ {u : ℂ | Real.pi < dist u (h z₀)} := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := hy
      rcases lt_trichotomy (dist (h y') (h z₀)) Real.pi with h1 | h2 | h3
      · exact Or.inl h1
      · exact absurd h2 (hneπ y' hy')
      · exact Or.inr h3
    have hne1 : (h '' V ∩ Metric.ball (h z₀) Real.pi).Nonempty :=
      ⟨h z₀, ⟨z₀, hz₀, rfl⟩, by rw [Metric.mem_ball, dist_self]; exact Real.pi_pos⟩
    have hne2 : (h '' V ∩ {u : ℂ | Real.pi < dist u (h z₀)}).Nonempty :=
      ⟨h z, ⟨z, hz, rfl⟩, hgt⟩
    obtain ⟨u', -, hu1, hu2⟩ :=
      himg (Metric.ball (h z₀) Real.pi) {u : ℂ | Real.pi < dist u (h z₀)} hU hW hcover hne1 hne2
    rw [Metric.mem_ball] at hu1
    exact absurd hu1 (not_lt.mpr (le_of_lt hu2))
  intro z hz
  obtain ⟨n, hn⟩ := hval z hz
  have hd : dist (h z) (h z₀) < Real.pi := hclose (h z) ⟨z, hz, rfl⟩
  have hd' : dist (n * (2 * Real.pi * Complex.I)) (n₀ * (2 * Real.pi * Complex.I)) < Real.pi := by
    rw [← hn, ← hn₀]; exact hd
  have hn_eq : n = n₀ := lattice_eq_of_dist_lt n n₀ hd'
  rw [hn, hn₀, hn_eq]

end Work.Analysis.DiscreteValues
