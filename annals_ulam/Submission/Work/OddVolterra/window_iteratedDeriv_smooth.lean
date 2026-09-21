import Mathlib
import Submission.Work.OddVolterra.window_iteratedDeriv_of_eventually_pos

/-!
# Differentiating under the integral sign through a positive window (smooth data)

`Work.OddVolterra.window_iteratedDeriv_smooth` is the same statement as
`Work.OddVolterra.window_iteratedDeriv_of_eventually_pos`, but with the weaker hypothesis
`ContDiff ℝ (⊤ : ℕ∞)` (i.e. `C^∞`) in place of the analytic `ContDiff ℝ ⊤ = ContDiff ℝ ω`.

Since `ContDiff ℝ (⊤ : ℕ∞)` is literally `ContDiff ℝ ∞`, the proof of the analytic version
goes through verbatim after replacing `hΨ.of_le le_top` by `hΨ`; the auxiliary lemmas of
`Submission.Work.OddVolterra.window_iteratedDeriv_of_eventually_pos` (`pderiv`,
`contDiff_pderiv`, `deriv_integral_of_contDiff`, `param_iteratedDeriv`, ...) are all stated for
`ContDiff ℝ ∞`, and are reused directly here.
-/

namespace Work.OddVolterra

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **Differentiating under the integral sign through a positive window, with smooth (not
analytic) data.**  Same statement as `Work.OddVolterra.window_iteratedDeriv_of_eventually_pos`
in the module `Submission.Work.OddVolterra.window_iteratedDeriv_of_eventually_pos`, except that
the smoothness hypothesis is the weaker `ContDiff ℝ (⊤ : ℕ∞)` (`C^∞`) instead of the analytic
`ContDiff ℝ ω` used there.

Concretely: for `Ψ : ℝ → ℝ → ℝ` which is `C^∞` on `ℝ × ℝ` and strictly positive on a window
`{|u - s| < ε} × [c,d]`, the `(n+1)`-st derivative at `s` of `u ↦ ∫_t∈[c,d] Ψ(u,t)^n √(Ψ(u,t))`
is the integral over `t` of the pointwise `(n+1)`-st derivatives. -/
theorem window_iteratedDeriv_smooth (n : ℕ) (hn : 1 ≤ n) {c d s : ℝ}
    (hcd : c ≤ d) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => Ψ q.1 q.2))
    (hpos : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → ∀ t ∈ Set.Icc c d, 0 < Ψ u t) :
    iteratedDeriv (n + 1)
        (fun u : ℝ => ∫ t in c..d, Ψ u t ^ n * Real.sqrt (Ψ u t)) s =
      ∫ t in c..d,
        iteratedDeriv (n + 1) (fun u : ℝ => Ψ u t ^ n * Real.sqrt (Ψ u t)) s := by
  obtain ⟨ε, hε, hΨpos⟩ := hpos
  let Φ : ℝ × ℝ → ℝ := fun q => Ψ q.1 q.2
  have hΦ : ContDiff ℝ ∞ Φ := hΨ
  -- Step 1: positivity on a product window around `{s} × [c,d]`.
  have hKsub : Set.Icc (s - ε / 2) (s + ε / 2) ×ˢ Set.Icc c d ⊆ {q : ℝ × ℝ | 0 < Φ q} := by
    rintro ⟨u, t⟩ ⟨hu, ht⟩
    refine hΨpos u ?_ t ht
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
  -- values of `β` and `γ`
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
  -- Step 3: apply the global theorem to `G'` and transfer.
  let G : ℝ × ℝ → ℝ := fun q => Φ q ^ n * Real.sqrt (Φ q)
  let G' : ℝ × ℝ → ℝ := fun q => Ψ' q ^ n * Real.sqrt (Ψ' q)
  have hG'smooth : ContDiff ℝ ∞ G' := by
    show ContDiff ℝ ∞ (fun q : ℝ × ℝ => Ψ' q ^ n * Real.sqrt (Ψ' q))
    exact (hΨ'smooth.pow n).mul (hΨ'smooth.sqrt fun q => (hΨ'pos q).ne')
  have hwin : ∀ u : ℝ, |u - s| < ε / 8 → ∀ t ∈ Set.Icc c d, G' (u, t) = G (u, t) := by
    intro u hu t ht
    have := hΨ'eq u hu.le t ht
    show Ψ' (u, t) ^ n * Real.sqrt (Ψ' (u, t)) = Φ (u, t) ^ n * Real.sqrt (Φ (u, t))
    rw [this]
  have hL : (fun u : ℝ => ∫ t in c..d, G' (u, t)) =ᶠ[𝓝 s]
      (fun u : ℝ => ∫ t in c..d, G (u, t)) := by
    filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < ε / 8)] with u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    exact intervalIntegral.integral_congr fun t ht =>
      hwin u hu t (by simpa [Set.uIcc_of_le hcd] using ht)
  have hR : (∫ t in c..d, iteratedDeriv (n + 1) (fun u : ℝ => G' (u, t)) s)
      = ∫ t in c..d, iteratedDeriv (n + 1) (fun u : ℝ => G (u, t)) s := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have hEq : (fun u : ℝ => G' (u, t)) =ᶠ[𝓝 s] (fun u : ℝ => G (u, t)) := by
      filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < ε / 8)] with u hu
      rw [Metric.mem_ball, Real.dist_eq] at hu
      exact hwin u hu t (by simpa [Set.uIcc_of_le hcd] using ht)
    exact (hEq.iteratedDeriv (n + 1)).eq_of_nhds
  have hmain := param_iteratedDeriv (n + 1) hcd hG'smooth s
  have hfinal : iteratedDeriv (n + 1) (fun u : ℝ => ∫ t in c..d, G (u, t)) s
      = ∫ t in c..d, iteratedDeriv (n + 1) (fun u : ℝ => G (u, t)) s := by
    rw [← (hL.iteratedDeriv (n + 1)).eq_of_nhds, hmain, hR]
  exact hfinal
end

end Work.OddVolterra
