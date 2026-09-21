import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving

/-!
# Smoothness of the windowed centroid integral in the slope variable

`Work.OddVolterra.Window.contDiffOn_fixed_window` is the smoothness input needed to
differentiate the odd-case moment equations repeatedly in the slope variable: for a smooth
profile `h` and a slope window on which the radicand `1 - t² - (u t + h u)²` stays strictly
positive, the parametric integral

`u ↦ ∫ t in (-x₀(1))..(x₀(1)), (1 - t² - (u t + h u)²)^(n-1) √(1 - t² - (u t + h u)²) (t + h'(u))`

is `C^∞` in `u` on a neighbourhood of `s`.

The proof is in three steps.

* `contDiff_intervalIntegral_const_bounds`: a parametric interval integral with constant
  bounds and a *globally* smooth integrand is smooth (this is
  `Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving` with constant
  endpoints).
* `exists_pos_smooth_extension`: the radicand `Φ`, being strictly positive on the window
  `{|u - s| < ε} × [c,d]`, agrees on that window with a *globally* smooth and globally
  strictly positive function `Ψ`.  The construction is the standard bump interpolation
  `Ψ = 1 + χ (Φ - 1)` with `χ = β(u) γ(t)`, where the `t`-bump `γ` is supported in a
  thickening of `[c,d]` chosen small enough that `Φ` is still positive there.
* `contDiffOn_window_integral`: combine the two, using that replacing `Φ` by `Ψ` does not
  change the integral over `[c,d]` for `u` close to `s`.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- A parametric interval integral with constant bounds and a globally smooth integrand is
smooth in the parameter. -/
lemma contDiff_intervalIntegral_const_bounds {c d : ℝ} {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun u : ℝ => ∫ t in c..d, F (u, t)) := by
  have hF' : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F (p.1, p.2)) := by simpa only using hF
  have h := Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving
    (F := fun u t => F (u, t)) (a := fun _ : ℝ => c) (b := fun _ : ℝ => d)
    hF' contDiff_const contDiff_const
  simpa using h

/-- **Bump interpolation of a radicand.**  If `Φ : ℝ × ℝ → ℝ` is smooth and strictly positive
on the window `{|u - s| < ε} × [c,d]`, then there is a smooth `Ψ` which is strictly positive
everywhere and agrees with `Φ` on `{|u - s| ≤ ε/8} × [c,d]`. -/
lemma exists_pos_smooth_extension {Φ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {c d s ε : ℝ} (hcd : c ≤ d) (hε : 0 < ε)
    (hΦpos : ∀ u : ℝ, |u - s| < ε → ∀ t ∈ Set.Icc c d, 0 < Φ (u, t)) :
    ∃ Ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ (∀ q, 0 < Ψ q) ∧
      (∀ u : ℝ, |u - s| ≤ ε / 8 → ∀ t ∈ Set.Icc c d, Ψ (u, t) = Φ (u, t)) := by
  -- Step 1: positivity on a thickening of `[s - ε/2, s + ε/2] × [c,d]`.
  have hKsub : Set.Icc (s - ε / 2) (s + ε / 2) ×ˢ Set.Icc c d ⊆ {q : ℝ × ℝ | 0 < Φ q} := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    refine hΦpos u ?_ t ht
    have hu' : |u - s| ≤ ε / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    linarith
  have hUopen : IsOpen {q : ℝ × ℝ | 0 < Φ q} := isOpen_lt continuous_const hΦ.continuous
  obtain ⟨ρ, hρ, hρK⟩ :=
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Set.Icc (s - ε / 2) (s + ε / 2) ×ˢ Set.Icc c d)).exists_thickening_subset_open
        hUopen hKsub
  have hpos_ext : ∀ u : ℝ, |u - s| ≤ ε / 2 →
      ∀ t ∈ Set.Icc (c - ρ / 2) (d + ρ / 2), 0 < Φ (u, t) := by
    intro u hu t ht
    have ht' : max c (min t d) ∈ Set.Icc c d :=
      ⟨le_max_left _ _, max_le hcd (min_le_right _ _)⟩
    have hu' : u ∈ Set.Icc (s - ε / 2) (s + ε / 2) := by
      rw [abs_le] at hu
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hmem : (u, t) ∈
        Metric.thickening ρ (Set.Icc (s - ε / 2) (s + ε / 2) ×ˢ Set.Icc c d) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(u, max c (min t d)), ⟨hu', ht'⟩, ?_⟩
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]
      have hclamp : |t - max c (min t d)| ≤ ρ / 2 := by
        rcases le_total t d with htd | htd
        · rw [min_eq_left htd]
          rcases le_total c t with hct | hct
          · rw [max_eq_right hct, sub_self, abs_zero]; linarith [hρ]
          · rw [max_eq_left hct, abs_of_nonpos (by linarith)]
            linarith [ht.1]
        · rw [min_eq_right htd, max_eq_right hcd, abs_of_nonneg (by linarith)]
          linarith [ht.2]
      linarith [hclamp, hρ]
    exact hρK hmem
  -- Step 2: smooth bump glue.
  let β : ContDiffBump s := ⟨ε / 8, ε / 4, by linarith, by linarith⟩
  let γ : ContDiffBump ((c + d) / 2) :=
    ⟨(d - c) / 2 + ρ / 4, (d - c) / 2 + ρ / 2, by linarith, by linarith⟩
  let χ : ℝ × ℝ → ℝ := fun q => β q.1 * γ q.2
  let Ψ' : ℝ × ℝ → ℝ := fun q => 1 + χ q * (Φ q - 1)
  have hβsmooth : ContDiff ℝ ∞ (fun x : ℝ => β x) := β.contDiff
  have hγsmooth : ContDiff ℝ ∞ (fun x : ℝ => γ x) := γ.contDiff
  have hχsmooth : ContDiff ℝ ∞ χ := by
    show ContDiff ℝ ∞ (fun q : ℝ × ℝ => β q.1 * γ q.2)
    exact (hβsmooth.comp contDiff_fst).mul (hγsmooth.comp contDiff_snd)
  have hΨ'smooth : ContDiff ℝ ∞ Ψ' := by
    show ContDiff ℝ ∞ (fun q : ℝ × ℝ => 1 + χ q * (Φ q - 1))
    exact contDiff_const.add (hχsmooth.mul (hΦ.sub contDiff_const))
  have hχnn : ∀ q, 0 ≤ χ q := by
    intro q
    show 0 ≤ β q.1 * γ q.2
    exact mul_nonneg β.nonneg γ.nonneg
  have hχle : ∀ q, χ q ≤ 1 := by
    intro q
    show β q.1 * γ q.2 ≤ 1
    nlinarith [β.le_one (x := q.1), β.nonneg (x := q.1), γ.le_one (x := q.2),
      γ.nonneg (x := q.2)]
  have hχsupp : ∀ q, χ q ≠ 0 → β q.1 ≠ 0 ∧ γ q.2 ≠ 0 := by
    intro q hq
    constructor
    · intro h
      exact hq (by show β q.1 * γ q.2 = 0; rw [h, zero_mul])
    · intro h
      exact hq (by show β q.1 * γ q.2 = 0; rw [h, mul_zero])
  have hβmem : ∀ u : ℝ, |u - s| ≤ ε / 8 → β u = 1 := by
    intro u hu
    refine β.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, show β.rIn = ε / 8 from rfl]
    exact hu
  have hγmem : ∀ t ∈ Set.Icc c d, γ t = 1 := by
    intro t ht
    refine γ.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq,
      show γ.rIn = (d - c) / 2 + ρ / 4 from rfl]
    have h1 : c ≤ t := ht.1
    have h2 : t ≤ d := ht.2
    have : |t - (c + d) / 2| ≤ (d - c) / 2 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have hΨ'pos : ∀ q, 0 < Ψ' q := by
    intro q
    rcases le_total 1 (Φ q) with h1 | h1
    · show 0 < 1 + χ q * (Φ q - 1)
      nlinarith [hχnn q]
    · by_cases hχ : χ q = 0
      · show 0 < 1 + χ q * (Φ q - 1)
        rw [hχ, zero_mul, add_zero]
        norm_num
      · obtain ⟨hβne, hγne⟩ := hχsupp q hχ
        have hq1 : |q.1 - s| < ε / 4 := by
          have hmem : q.1 ∈ Metric.ball s β.rOut := by
            rw [← β.support_eq]; exact hβne
          rw [Metric.mem_ball, Real.dist_eq, show β.rOut = ε / 4 from rfl] at hmem
          exact hmem
        have hq2 : q.2 ∈ Set.Icc (c - ρ / 2) (d + ρ / 2) := by
          have hmem : q.2 ∈ Metric.ball ((c + d) / 2) γ.rOut := by
            rw [← γ.support_eq]; exact hγne
          rw [Metric.mem_ball, Real.dist_eq, abs_lt,
            show γ.rOut = (d - c) / 2 + ρ / 2 from rfl] at hmem
          constructor <;> linarith [hmem.1, hmem.2]
        have hΦq : 0 < Φ q :=
          hpos_ext q.1 (by linarith [hq1]) q.2 hq2
        have hχpos : 0 < χ q := lt_of_le_of_ne (hχnn q) (Ne.symm hχ)
        show 0 < 1 + χ q * (Φ q - 1)
        have hkey : 1 + χ q * (Φ q - 1) = (1 - χ q) + χ q * Φ q := by ring
        rw [hkey]
        have h1 : 0 < χ q * Φ q := mul_pos hχpos hΦq
        have h2 : 0 ≤ 1 - χ q := by linarith [hχle q]
        linarith
  have hΨ'eq : ∀ u : ℝ, |u - s| ≤ ε / 8 → ∀ t ∈ Set.Icc c d, Ψ' (u, t) = Φ (u, t) := by
    intro u hu t ht
    have h1 : β u = 1 := hβmem u hu
    have h2 : γ t = 1 := hγmem t ht
    show 1 + χ (u, t) * (Φ (u, t) - 1) = Φ (u, t)
    have hχ1 : χ (u, t) = 1 := by show β u * γ t = 1; rw [h1, h2, one_mul]
    rw [hχ1]; ring
  exact ⟨Ψ', hΨ'smooth, hΨ'pos, hΨ'eq⟩

/-- **Smoothness of the windowed parametric integral.**  If `Φ` and `Λ` are smooth on
`ℝ × ℝ` and `Φ` is strictly positive on a window `{|u - s| < ε} × [c,d]`, then for some
`δ > 0` the function
`u ↦ ∫ t in c..d, Φ(u,t)^n √(Φ(u,t)) Λ(u,t)`
is `C^∞` on `Ioo (s - δ) (s + δ)`. -/
lemma contDiffOn_window_integral (n : ℕ) {c d s : ℝ} (hcd : c ≤ d)
    {Φ Λ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΛ : ContDiff ℝ ∞ Λ)
    (hpos : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → ∀ t ∈ Set.Icc c d, 0 < Φ (u, t)) :
    ∃ δ > 0, ContDiffOn ℝ ∞
      (fun u : ℝ => ∫ t in c..d, Φ (u, t) ^ n * Real.sqrt (Φ (u, t)) * Λ (u, t))
      (Set.Ioo (s - δ) (s + δ)) := by
  obtain ⟨ε, hε, hΦpos⟩ := hpos
  obtain ⟨Ψ, hΨsm, hΨpos, hΨeq⟩ := exists_pos_smooth_extension hΦ hcd hε hΦpos
  have hGsm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => Ψ q ^ n * Real.sqrt (Ψ q) * Λ q) :=
    ((hΨsm.pow n).mul (hΨsm.sqrt fun q => (hΨpos q).ne')).mul hΛ
  have hmain : ContDiff ℝ ∞
      (fun u : ℝ => ∫ t in c..d, Ψ (u, t) ^ n * Real.sqrt (Ψ (u, t)) * Λ (u, t)) :=
    contDiff_intervalIntegral_const_bounds hGsm
  refine ⟨ε / 8, by linarith, ?_⟩
  refine hmain.contDiffOn.congr ?_
  intro u hu
  refine intervalIntegral.integral_congr fun t ht => ?_
  have hu' : |u - s| ≤ ε / 8 := by
    rw [abs_le]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have ht' : t ∈ Set.Icc c d := by simpa [Set.uIcc_of_le hcd] using ht
  show Φ (u, t) ^ n * Real.sqrt (Φ (u, t)) * Λ (u, t)
      = Ψ (u, t) ^ n * Real.sqrt (Ψ (u, t)) * Λ (u, t)
  rw [hΨeq u hu' t ht']

end

end Work.OddVolterra.Window

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

theorem contDiffOn_fixed_window (n : ℕ) (hn : 1 ≤ n) {s : ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hpos : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε →
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
        0 < 1 - t ^ 2 - line h u t ^ 2) :
    ∃ δ > 0, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun u : ℝ => ∫ t in (-(Commons.Geometry.Ulam.profileX 1))..(Commons.Geometry.Ulam.profileX 1),
        (1 - t ^ 2 - line h u t ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - line h u t ^ 2) *
          lineSlope h u t)
      (Set.Ioo (s - δ) (s + δ)) := by
  have hdpos : 0 < Commons.Geometry.Ulam.profileX 1 :=
    Commons.Geometry.Ulam.profileX_pos 1 (by norm_num)
  have hcd : -(Commons.Geometry.Ulam.profileX 1) ≤ Commons.Geometry.Ulam.profileX 1 := by
    linarith
  have hΦ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => 1 - q.2 ^ 2 - line h q.1 q.2 ^ 2) := by
    unfold line
    fun_prop
  have hΛ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => lineSlope h q.1 q.2) := by
    unfold lineSlope
    fun_prop
  obtain ⟨δ, hδ, hcont⟩ := contDiffOn_window_integral (n := n - 1)
    (c := -(Commons.Geometry.Ulam.profileX 1)) (d := Commons.Geometry.Ulam.profileX 1)
    (s := s) (Φ := fun q : ℝ × ℝ => 1 - q.2 ^ 2 - line h q.1 q.2 ^ 2)
    (Λ := fun q : ℝ × ℝ => lineSlope h q.1 q.2) hcd hΦ hΛ hpos
  exact ⟨δ, hδ, hcont⟩

end

end Work.OddVolterra.Window
