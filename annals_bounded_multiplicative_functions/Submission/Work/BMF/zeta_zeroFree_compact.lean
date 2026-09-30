import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex

namespace Work.BMF

/-- The compact set `K = {s : ℂ | 1/2 ≤ Re s ≤ 2, 3 ≤ |Im s| ≤ T}`, written as the image of a
compact subset of `ℝ × ℝ` under `(x,y) ↦ x + y·i`. -/
private def Kset (T : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ (Set.Icc (3 : ℝ) T ∪ Set.Icc (-T) (-3)))

/-- Membership in `Kset T` in explicit coordinates. -/
private lemma mem_Kset_iff (T : ℝ) (hT : 3 ≤ T) (t σ : ℝ) :
    ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ Kset T ↔
      ((1 / 2 : ℝ) ≤ σ ∧ σ ≤ 2 ∧ 3 ≤ |t| ∧ |t| ≤ T) := by
  constructor
  · rintro ⟨p, hp, hpeq⟩
    have hre : σ = p.1 := by
      have := congrArg Complex.re hpeq
      simpa using this.symm
    have him : t = p.2 := by
      have := congrArg Complex.im hpeq
      simpa using this.symm
    refine ⟨by linarith [hp.1.1, hre], by linarith [hp.1.2, hre], ?_, ?_⟩
    · rcases hp.2 with ⟨h3, _⟩ | ⟨_, h3⟩
      · rw [him]
        exact le_trans (by linarith : (3 : ℝ) ≤ p.2) (le_abs_self p.2)
      · rw [him, abs_of_nonpos (by linarith : p.2 ≤ 0)]
        linarith
    · rcases hp.2 with ⟨_, hT'⟩ | ⟨hT', _⟩
      · rw [him]
        exact abs_le.mpr ⟨by linarith, hT'⟩
      · rw [him, abs_of_nonpos (by linarith : p.2 ≤ 0)]
        linarith
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(σ, t), ⟨⟨h1, h2⟩, ?_⟩, rfl⟩
    rcases le_abs.mp h3 with h | h
    · exact Or.inl ⟨h, (abs_le.mp h4).2⟩
    · exact Or.inr ⟨(abs_le.mp h4).1, by linarith⟩

/-- Zero-freeness in a compact horizontal strip away from the real axis: for every `T ≥ 3` there is
`ε > 0` with `ζ(σ + it) ≠ 0` whenever `3 ≤ |t| ≤ T` and `1 - ε ≤ σ ≤ 2`.

The set `K = {s : ℂ | 1/2 ≤ Re s ≤ 2, 3 ≤ |Im s| ≤ T}` is compact and avoids the pole `s = 1`; the
zeros of `ζ` inside `K` form a finite set `Z` (Mathlib: `IsCompact.inter_riemannZetaZeros_finite`),
each with `Re < 1` (Mathlib: `riemannZeta_ne_zero_of_one_le_re`, giving no zeros with `Re ≥ 1`).
If `Z` is empty take `ε = 1/2`; otherwise `ε = (1 - max{Re ρ : ρ ∈ Z})/2`. -/
theorem zeta_zeroFree_compact (T : ℝ) (hT : 3 ≤ T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t σ : ℝ, 3 ≤ |t| → |t| ≤ T → 1 - ε ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have hKcompact : IsCompact (Kset T) := by
    refine IsCompact.image ?_ ?_
    · exact IsCompact.prod isCompact_Icc (IsCompact.union isCompact_Icc isCompact_Icc)
    · fun_prop
  let Z : Set ℂ := Kset T ∩ riemannZetaZeros
  have hZfin : Z.Finite := hKcompact.inter_riemannZetaZeros_finite
  -- Real parts of the zeros in `K` lie in `[1/2, 1)`.
  have hZ_re_ge_half : ∀ z : ℂ, z ∈ Z → (1 / 2 : ℝ) ≤ z.re := by
    intro z hz
    have hzK : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) ∈ Kset T := by
      rw [Complex.re_add_im]
      exact hz.1
    exact ((mem_Kset_iff T hT z.im z.re).mp hzK).1
  have hZ_re_lt_one : ∀ z : ℂ, z ∈ Z → z.re < 1 := by
    intro z hz
    have hz0 : riemannZeta z = 0 := by simpa [riemannZetaZeros] using hz.2
    exact lt_of_not_ge (fun hge : (1 : ℝ) ≤ z.re =>
      riemannZeta_ne_zero_of_one_le_re hge hz0)
  by_cases hZempty : Z = ∅
  · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    intro t σ ht1 ht2 hσlo hσhi hz0
    have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ Z := by
      refine ⟨?_, ?_⟩
      · rw [mem_Kset_iff T hT t σ]
        exact ⟨by linarith, hσhi, ht1, ht2⟩
      · simpa [riemannZetaZeros] using hz0
    rw [hZempty] at hmem
    exact hmem
  · have hZn : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hZempty
    let fz : Finset ℂ := hZfin.toFinset
    have hfz : ∀ z : ℂ, z ∈ fz ↔ z ∈ Z := fun z => hZfin.mem_toFinset
    have hne : (fz.image (fun z : ℂ => 1 - z.re)).Nonempty := by
      rcases hZn with ⟨z, hz⟩
      exact ⟨1 - z.re, Finset.mem_image.mpr ⟨z, (hfz z).mpr hz, rfl⟩⟩
    let d : ℝ := (fz.image (fun z : ℂ => 1 - z.re)).min' hne
    have hd_mem : d ∈ fz.image (fun z : ℂ => 1 - z.re) := by
      dsimp [d]
      exact Finset.min'_mem _ hne
    rcases Finset.mem_image.mp hd_mem with ⟨z₀, hz₀f, hz₀eq⟩
    have hz₀Z : z₀ ∈ Z := (hfz z₀).mp hz₀f
    have hd_eq : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
    have hd_pos : 0 < d := by
      have := hZ_re_lt_one z₀ hz₀Z
      linarith
    have hd_le_half : d ≤ 1 / 2 := by
      have := hZ_re_ge_half z₀ hz₀Z
      linarith
    have hd_le : ∀ z : ℂ, z ∈ Z → d ≤ 1 - z.re := by
      intro z hz
      dsimp [d]
      exact Finset.min'_le (fz.image (fun z : ℂ => 1 - z.re)) (1 - z.re)
        (Finset.mem_image.mpr ⟨z, (hfz z).mpr hz, rfl⟩)
    refine ⟨d / 2, by linarith, ?_⟩
    intro t σ ht1 ht2 hσlo hσhi hz0
    have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ Z := by
      refine ⟨?_, ?_⟩
      · rw [mem_Kset_iff T hT t σ]
        exact ⟨by linarith, hσhi, ht1, ht2⟩
      · simpa [riemannZetaZeros] using hz0
    have h1 : d ≤ 1 - σ := by
      have h := hd_le ((σ : ℂ) + (t : ℂ) * Complex.I) hmem
      simpa using h
    have h2 : 1 - σ ≤ d / 2 := by linarith
    linarith

end Work.BMF
