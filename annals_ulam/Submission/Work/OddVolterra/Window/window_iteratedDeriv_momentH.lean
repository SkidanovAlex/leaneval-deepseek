import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.window_iteratedDeriv_of_eventually_pos

/-!
# Differentiating the centroid moment integrand under the integral sign

This file proves `Work.OddVolterra.Window.window_iteratedDeriv_momentH`: for a
slope window on which the radicand `1 - t² - (u t + h u)²` stays strictly
positive, the `n`-th derivative at `s` of the parametric centroid-moment
integral equals the integral of the `n`-th derivatives of the sections.

The proof reduces to the globally smooth case (`param_iteratedDeriv`) by gluing
the radicand `Φ` to the constant `1` outside a neighbourhood of the window with
a smooth bump; the extra factor `lineSlope h u t` is globally smooth and is
carried along unchanged.
-/

namespace Work.OddVolterra.Window

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- **Differentiation under the integral sign for `Φ ^ n * √Φ * Λ`.**

If `Φ` and `Λ` are globally smooth on `ℝ × ℝ` and `Φ` is strictly positive on a
window around `{s} × [c,d]`, then the `m`-th derivative at `s` of the
parametric integral `u ↦ ∫ t in c..d, Φ (u,t)^n √(Φ (u,t)) Λ (u,t)` is the
integral of the `m`-th derivatives of the sections.

The positivity hypothesis is used only to replace `Φ` by a globally smooth and
globally positive `Ψ'` which agrees with `Φ` on a neighbourhood of the window;
the resulting integrand is globally smooth, and `param_iteratedDeriv` applies. -/
theorem window_iteratedDeriv_of_smooth (n m : ℕ) {c d s : ℝ} (hcd : c ≤ d)
    {Φ Λ : ℝ × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΛ : ContDiff ℝ ∞ Λ)
    (hpos : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → ∀ t ∈ Set.Icc c d, 0 < Φ (u, t)) :
    iteratedDeriv m (fun u : ℝ => ∫ t in c..d,
        Φ (u, t) ^ n * Real.sqrt (Φ (u, t)) * Λ (u, t)) s =
      ∫ t in c..d, iteratedDeriv m (fun u : ℝ =>
        Φ (u, t) ^ n * Real.sqrt (Φ (u, t)) * Λ (u, t)) s := by
  obtain ⟨ε, hε, hΦpos⟩ := hpos
  -- Step 1: positivity on a product window around `{s} × [c,d]`.
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
  -- Step 3: apply the global theorem to the glued integrand and transfer.
  let G : ℝ × ℝ → ℝ := fun q => Φ q ^ n * Real.sqrt (Φ q) * Λ q
  let G' : ℝ × ℝ → ℝ := fun q => Ψ' q ^ n * Real.sqrt (Ψ' q) * Λ q
  have hG'smooth : ContDiff ℝ ∞ G' := by
    show ContDiff ℝ ∞ (fun q : ℝ × ℝ => Ψ' q ^ n * Real.sqrt (Ψ' q) * Λ q)
    exact ((hΨ'smooth.pow n).mul (hΨ'smooth.sqrt fun q => (hΨ'pos q).ne')).mul hΛ
  have hwin : ∀ u : ℝ, |u - s| < ε / 8 → ∀ t ∈ Set.Icc c d, G' (u, t) = G (u, t) := by
    intro u hu t ht
    have := hΨ'eq u hu.le t ht
    show Ψ' (u, t) ^ n * Real.sqrt (Ψ' (u, t)) * Λ (u, t)
      = Φ (u, t) ^ n * Real.sqrt (Φ (u, t)) * Λ (u, t)
    rw [this]
  have hL : (fun u : ℝ => ∫ t in c..d, G' (u, t)) =ᶠ[𝓝 s]
      (fun u : ℝ => ∫ t in c..d, G (u, t)) := by
    filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < ε / 8)] with u hu
    rw [Metric.mem_ball, Real.dist_eq] at hu
    exact intervalIntegral.integral_congr fun t ht =>
      hwin u hu t (by simpa [Set.uIcc_of_le hcd] using ht)
  have hR : (∫ t in c..d, iteratedDeriv m (fun u : ℝ => G' (u, t)) s)
      = ∫ t in c..d, iteratedDeriv m (fun u : ℝ => G (u, t)) s := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have hEq : (fun u : ℝ => G' (u, t)) =ᶠ[𝓝 s] (fun u : ℝ => G (u, t)) := by
      filter_upwards [Metric.ball_mem_nhds s (by linarith : (0 : ℝ) < ε / 8)] with u hu
      rw [Metric.mem_ball, Real.dist_eq] at hu
      exact hwin u hu t (by simpa [Set.uIcc_of_le hcd] using ht)
    exact (hEq.iteratedDeriv m).eq_of_nhds
  have hmain := param_iteratedDeriv m hcd hG'smooth s
  calc iteratedDeriv m (fun u : ℝ => ∫ t in c..d, G (u, t)) s
      = iteratedDeriv m (fun u : ℝ => ∫ t in c..d, G' (u, t)) s := by
        rw [(hL.iteratedDeriv m).eq_of_nhds]
    _ = ∫ t in c..d, iteratedDeriv m (fun u : ℝ => G' (u, t)) s := hmain
    _ = ∫ t in c..d, iteratedDeriv m (fun u : ℝ => G (u, t)) s := hR

/-- **The windowed centroid-moment differentiation identity.** -/
theorem window_iteratedDeriv_momentH (n : ℕ) (hn : 1 ≤ n) {c d s : ℝ} (hcd : c ≤ d)
    {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hpos : ∃ ε > 0, ∀ u : ℝ, |u - s| < ε → ∀ t ∈ Set.Icc c d, 0 < 1 - t ^ 2 - line h u t ^ 2) :
    iteratedDeriv n (fun u : ℝ => ∫ t in c..d,
        (1 - t ^ 2 - line h u t ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - line h u t ^ 2) *
          lineSlope h u t) s =
      ∫ t in c..d, iteratedDeriv n (fun u : ℝ =>
        (1 - t ^ 2 - line h u t ^ 2) ^ (n - 1) * Real.sqrt (1 - t ^ 2 - line h u t ^ 2) *
          lineSlope h u t) s := by
  have hΦ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => 1 - q.2 ^ 2 - line h q.1 q.2 ^ 2) := by
    unfold line
    fun_prop
  have hΛ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => lineSlope h q.1 q.2) := by
    unfold lineSlope
    fun_prop
  exact window_iteratedDeriv_of_smooth (n := n - 1) (m := n) hcd hΦ hΛ hpos

end

end Work.OddVolterra.Window
