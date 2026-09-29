import Mathlib

namespace Work.TMComp.RedProj

/-- Uniform margin lemma.  From the coupled covering hypothesis on `[c,d] × [0,1]`
(one index `i` must work simultaneously for the `E`- and `x`-coordinate) one extracts a
single positive `β` such that at every point of the rectangle some index has both
coordinate margins at least `β`.  This is a compactness statement: the pointwise
maximum of the finitely many continuous margin functions is positive on the compact
rectangle, hence bounded below by a positive constant, and at an arg-max the two
coordinate margins are both at least that constant. -/
lemma exists_uniform_margin_aux {ι : Type*} [Fintype ι] (c d : ℝ) (hcd : c ≤ d)
    (E X s t : ι → ℝ)
    (hcover : ∀ E₀ ∈ Set.Icc c d, ∀ x₀ ∈ Set.Icc (0:ℝ) 1, ∃ i, |E₀ - E i| < s i ∧ |x₀ - X i| < t i) :
    ∃ β : ℝ, 0 < β ∧ ∀ E₀ ∈ Set.Icc c d, ∀ x₀ ∈ Set.Icc (0:ℝ) 1,
      ∃ i, s i - |E₀ - E i| ≥ β ∧ t i - |x₀ - X i| ≥ β := by
  haveI hne : Nonempty ι := by
    obtain ⟨i, _⟩ := hcover c (Set.left_mem_Icc.mpr hcd) 0 (Set.left_mem_Icc.mpr zero_le_one)
    exact ⟨i⟩
  let Φ : ι → ℝ × ℝ → ℝ := fun i p => min (s i - |p.1 - E i|) (t i - |p.2 - X i|)
  have hΦc : ∀ i, Continuous (Φ i) := by
    intro i
    change Continuous (fun p : ℝ × ℝ => min (s i - |p.1 - E i|) (t i - |p.2 - X i|))
    exact Continuous.min (continuous_const.sub ((continuous_fst.sub continuous_const).abs))
      (continuous_const.sub ((continuous_snd.sub continuous_const).abs))
  let g : ℝ × ℝ → ℝ := fun p => Finset.univ.sup' Finset.univ_nonempty (fun i => Φ i p)
  have hgfun : g = Finset.univ.sup' Finset.univ_nonempty (fun i => Φ i) := by
    funext p
    exact (Finset.sup'_apply Finset.univ_nonempty (fun i => Φ i) p).symm
  have hgc : Continuous g := by
    rw [hgfun]
    exact Continuous.finset_sup' Finset.univ_nonempty (fun i _ => hΦc i)
  have hKne : (Set.Icc c d ×ˢ (Set.Icc (0:ℝ) 1)).Nonempty :=
    ⟨(c, 0), by rw [Set.mem_prod]; exact ⟨Set.left_mem_Icc.mpr hcd, Set.left_mem_Icc.mpr zero_le_one⟩⟩
  obtain ⟨p₀, hp₀K, hp₀min⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_isMinOn hKne hgc.continuousOn
  have hp₀mem := Set.mem_prod.mp hp₀K
  have hgpos : 0 < g p₀ := by
    obtain ⟨i, hi1, hi2⟩ := hcover p₀.1 hp₀mem.1 p₀.2 hp₀mem.2
    have hΦpos : 0 < Φ i p₀ := by
      change 0 < min (s i - |p₀.1 - E i|) (t i - |p₀.2 - X i|)
      exact lt_min (sub_pos.mpr hi1) (sub_pos.mpr hi2)
    have hle : Φ i p₀ ≤ g p₀ := Finset.le_sup' (fun j => Φ j p₀) (Finset.mem_univ i)
    linarith
  refine ⟨g p₀, hgpos, ?_⟩
  intro E₀ hE₀ x₀ hx₀
  have hmem : (E₀, x₀) ∈ Set.Icc c d ×ˢ (Set.Icc (0:ℝ) 1) := by
    rw [Set.mem_prod]; exact ⟨hE₀, hx₀⟩
  have hle : g p₀ ≤ g (E₀, x₀) := (isMinOn_iff.mp hp₀min) (E₀, x₀) hmem
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => Φ i (E₀, x₀))
  have hgi : g (E₀, x₀) = min (s i - |E₀ - E i|) (t i - |x₀ - X i|) :=
    calc g (E₀, x₀)
        = Finset.univ.sup' Finset.univ_nonempty (fun j => Φ j (E₀, x₀)) := rfl
      _ = Φ i (E₀, x₀) := hi
      _ = min (s i - |E₀ - E i|) (t i - |x₀ - X i|) := rfl
  have hβle : g p₀ ≤ min (s i - |E₀ - E i|) (t i - |x₀ - X i|) := le_trans hle (le_of_eq hgi)
  exact ⟨i, le_trans hβle (min_le_left _ _), le_trans hβle (min_le_right _ _)⟩

theorem exists_tube_subset_union_polydiscs {ι : Type*} [Fintype ι] (c d : ℝ) (hcd : c ≤ d)
    (E X s t : ι → ℝ) (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i)
    (hcover : ∀ E₀ ∈ Set.Icc c d, ∀ x₀ ∈ Set.Icc (0:ℝ) 1, ∃ i, |E₀ - E i| < s i ∧ |x₀ - X i| < t i) :
    ∃ Δ : Set ℂ, IsOpen Δ ∧ (Set.Icc c d : Set ℝ) ⊆ {E | (E : ℂ) ∈ Δ} ∧
      ∃ ρ : ℝ, 0 < ρ ∧ (Δ ×ˢ {w : ℂ | |w.im| < ρ}) ⊆
        ⋃ i, ⋃ n : ℤ, (Metric.ball (E i : ℂ) (s i) ×ˢ Metric.ball (((X i + n : ℝ) : ℂ)) (t i)) := by
  obtain ⟨β, hβpos, hβ⟩ := exists_uniform_margin_aux c d hcd E X s t hcover
  set Δ : Set ℂ := {w : ℂ | ∃ E₀ ∈ Set.Icc c d, ‖w - (E₀ : ℂ)‖ < β} with hΔdef
  have hΔopen : IsOpen Δ := by
    have hEq : Δ = ⋃ E₀ ∈ Set.Icc c d, Metric.ball (E₀ : ℂ) β := by
      rw [hΔdef]
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Metric.mem_ball, dist_eq_norm]
      constructor <;> rintro ⟨E₀, hE₀, h⟩ <;> exact ⟨E₀, hE₀, h⟩
    rw [hEq]
    exact isOpen_biUnion (fun E₀ _ => Metric.isOpen_ball)
  have hsub : (Set.Icc c d : Set ℝ) ⊆ {E | (E : ℂ) ∈ Δ} := by
    intro E hE
    rw [hΔdef, Set.mem_setOf_eq]
    exact ⟨E, hE, by simpa using hβpos⟩
  refine ⟨Δ, hΔopen, hsub, β, hβpos, ?_⟩
  intro p hp
  rw [Set.mem_prod] at hp
  obtain ⟨hpΔ, hpim⟩ := hp
  have hpim' : |p.2.im| < β := hpim
  rw [hΔdef, Set.mem_setOf_eq] at hpΔ
  obtain ⟨E₀, hE₀, hpE⟩ := hpΔ
  set x₀ : ℝ := p.2.re - (⌊p.2.re⌋ : ℝ) with hx₀
  have hx₀mem : x₀ ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · rw [hx₀]; linarith [Int.floor_le p.2.re]
    · rw [hx₀]; have h := Int.lt_floor_add_one p.2.re; linarith
  obtain ⟨i, hEi, hXi⟩ := hβ E₀ hE₀ x₀ hx₀mem
  refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨⌊p.2.re⌋, ?_⟩⟩
  simp only [Set.mem_prod, Metric.mem_ball, dist_eq_norm]
  refine ⟨?_, ?_⟩
  · have h2 : ‖(E₀ : ℂ) - (E i : ℂ)‖ = |E₀ - E i| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hsplit : p.1 - (E i : ℂ) = (p.1 - (E₀ : ℂ)) + ((E₀ : ℂ) - (E i : ℂ)) := by ring
    have hEin : ‖p.1 - (E i : ℂ)‖ ≤ ‖p.1 - (E₀ : ℂ)‖ + |E₀ - E i| := by
      calc ‖p.1 - (E i : ℂ)‖ = ‖(p.1 - (E₀ : ℂ)) + ((E₀ : ℂ) - (E i : ℂ))‖ := by rw [hsplit]
        _ ≤ ‖p.1 - (E₀ : ℂ)‖ + ‖(E₀ : ℂ) - (E i : ℂ)‖ := norm_add_le _ _
        _ = ‖p.1 - (E₀ : ℂ)‖ + |E₀ - E i| := by rw [h2]
    linarith
  · have hβt : β ≤ t i := by
      have h := abs_nonneg (x₀ - X i)
      linarith
    have hreal : (p.2.re - (X i + (⌊p.2.re⌋ : ℝ)))^2 ≤ (t i - β)^2 := by
      have habs : |p.2.re - (X i + (⌊p.2.re⌋ : ℝ))| ≤ t i - β := by
        rw [show p.2.re - (X i + (⌊p.2.re⌋ : ℝ)) = x₀ - X i by rw [hx₀]; ring]
        linarith
      nlinarith [sq_abs (p.2.re - (X i + (⌊p.2.re⌋ : ℝ))),
        abs_nonneg (p.2.re - (X i + (⌊p.2.re⌋ : ℝ))), habs, hβt]
    have him : (p.2.im)^2 < β^2 := by
      nlinarith [sq_abs p.2.im, abs_nonneg p.2.im, hβpos, hpim']
    have hnormsq : ∀ r : ℝ, ‖p.2 - (r : ℂ)‖^2 = (p.2.re - r)^2 + p.2.im^2 := by
      intro r
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im]
      ring
    refine (sq_lt_sq₀ (norm_nonneg _) (le_of_lt (ht i))).mp ?_
    rw [hnormsq (X i + (⌊p.2.re⌋ : ℝ))]
    nlinarith [hreal, him]

end Work.TMComp.RedProj
