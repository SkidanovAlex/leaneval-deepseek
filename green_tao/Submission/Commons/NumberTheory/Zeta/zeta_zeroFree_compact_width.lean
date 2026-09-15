import Mathlib.NumberTheory.LSeries.ZetaZeros

noncomputable section
open Complex Filter Metric Set
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

/-- **Zero-free region of ζ in a fixed strip for bounded imaginary part.**
For every `H ≥ 4` there is `ε > 0` such that `ζ(σ + i·t) ≠ 0` whenever
`|t| ≤ H` and `1 - ε ≤ σ ≤ 2`.

This is a compactness argument: ζ has no zeros on the closed half-plane
`re s ≥ 1`, and its zero set is discrete, so the compact rectangle
`[1/2, 2] × [-H, H]` contains only finitely many zeros — all of them with
`re s < 1`.  The minimal distance of those finitely many zeros from the line
`re s = 1` is positive, and half of it is the desired width. -/
theorem zeta_zeroFree_compact_width (H : ℝ) (hH : (4 : ℝ) ≤ H) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (t σ : ℝ), |t| ≤ H → 1 - ε ≤ σ → σ ≤ 2 →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  let S₀ : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-H) H)
  have hS₀compact : IsCompact S₀ := by
    dsimp [S₀]
    exact (IsCompact.prod isCompact_Icc isCompact_Icc).image
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)))
  let Z : Set ℂ := S₀ ∩ riemannZetaZeros
  have hZfin : Z.Finite := by
    dsimp [Z]
    exact hS₀compact.inter_riemannZetaZeros_finite
  have hZm : ∀ z : ℂ, z ∈ Z →
      (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ H ∧ riemannZeta z = 0 := by
    intro z hz
    rcases hz.1 with ⟨p, hp, hpeq⟩
    have hzre : z.re = p.1 := by rw [← hpeq]; simp
    have hzim : z.im = p.2 := by rw [← hpeq]; simp
    have hz0 : riemannZeta z = 0 := by simpa [riemannZetaZeros] using hz.2
    constructor
    · linarith [hp.1.1, hzre]
    constructor
    · linarith [hp.1.2, hzre]
    constructor
    · exact abs_le.mpr (by simpa [hzim] using hp.2)
    · exact hz0
  have hZ_re_lt_one : ∀ z : ℂ, z ∈ Z → z.re < 1 := by
    intro z hz
    have hz0 : riemannZeta z = 0 := (hZm z hz).2.2.2
    exact lt_of_not_ge (fun hge : (1 : ℝ) ≤ z.re =>
      riemannZeta_ne_zero_of_one_le_re (s := z) hge hz0)
  by_cases hZempty : Z = ∅
  · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    intro t σ ht hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ?_, rfl⟩
        constructor
        · constructor <;> linarith
        · exact abs_le.mp ht
      · simpa [Z, riemannZetaZeros, s] using hz0
    rw [hZempty] at hsZ
    exact hsZ
  · have hZn : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hZempty
    let fz : Finset ℂ := hZfin.toFinset
    have hfz_mem_iff : ∀ z : ℂ, z ∈ fz ↔ z ∈ Z := by
      intro z
      exact hZfin.mem_toFinset
    have hg_ne : (fz.image (fun z : ℂ => 1 - z.re)).Nonempty := by
      rcases hZn with ⟨z, hz⟩
      refine ⟨1 - z.re, Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩⟩
    let d : ℝ := (fz.image (fun z : ℂ => 1 - z.re)).min' hg_ne
    have hd_mem : d ∈ fz.image (fun z : ℂ => 1 - z.re) := by
      dsimp [d]
      exact Finset.min'_mem _ hg_ne
    rcases Finset.mem_image.mp hd_mem with ⟨z₀, hz₀f, hz₀eq⟩
    have hz₀Z : z₀ ∈ Z := (hfz_mem_iff z₀).1 hz₀f
    have hd0 : 0 < d := by
      have hz₀re : z₀.re < 1 := hZ_re_lt_one z₀ hz₀Z
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith
    have hd_le_half : d ≤ 1 / 2 := by
      have hz₀re_lo : (1 / 2 : ℝ) ≤ z₀.re := (hZm z₀ hz₀Z).1
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith
    have hd_le : ∀ z : ℂ, z ∈ Z → d ≤ 1 - z.re := by
      intro z hz
      dsimp [d]
      exact Finset.min'_le (fz.image (fun z : ℂ => 1 - z.re))
        (1 - z.re) (Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩)
    refine ⟨d / 2, by positivity, ?_⟩
    intro t σ ht hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ?_, rfl⟩
        constructor
        · constructor <;> linarith
        · exact abs_le.mp ht
      · simpa [Z, riemannZetaZeros, s] using hz0
    have hre : s.re = σ := by simp [s]
    have h1 : d ≤ 1 - σ := by
      have hd' := hd_le s hsZ
      rwa [hre] at hd'
    have h2 : 1 - σ ≤ d / 2 := by linarith
    linarith


end Commons.NumberTheory.Zeta