import Mathlib
import Submission.Work.RPB.B2.PhaseDefs
import Submission.Work.RPB.B2.chordVec_eq_mul_chordW_inf
import Submission.Work.RPB.B2.chordW_ne_zero_nhds

/-!
# `chordW` is non-vanishing near the chord annulus, under mere smoothness

The divided chord `chordW c τ t r = ∫_{s ∈ [-1,1]} c'(t + s r) ds` is `chordVec / r`, where
`chordVec c τ t r = c τ (t+r) - c τ (t-r)`.  For an embedded closed curve with non-vanishing
derivative the chord vector does not vanish on the open strip `-π < r < π` (it vanishes only on
the diagonal `r = 0` mod `2π`), and at `r = 0` the divided chord equals `2 c'(t) ≠ 0`.  Hence
`chordW` is non-zero on `[0,1] × ℝ × [A,B]` for `[A,B] ⊂ (-π,π)`, and by joint continuity and
`2π`-periodicity in `t` this persists on a neighbourhood of the `τ`-interval.

The point of this file, compared with `Submission/Work/RPB/B2/chordW_ne_zero_nhds.lean`, is that
only *smoothness* (`C^∞`, i.e. the order `((⊤ : ℕ∞) : WithTop ℕ∞)` of the `ContDiff` scope) of the
curve family `c` is assumed, not analyticity (the order `ω = (⊤ : WithTop ℕ∞)`).  Indeed the only
step of the original argument that consumed the extra strength of the hypothesis was the identity
`chordVec = r * chordW`, whose smooth version `Work.RPB.B2.chordVec_eq_mul_chordW_inf` is already
available; the remaining ingredients (continuity of `chordW`, `2π`-periodicity in `t`, the value at
`r = 0`, non-vanishing of the chord vector for `-π < r < π`, reduction of `t` mod `2π`) use no
smoothness at all beyond continuity.  Accordingly we reprove here only the two continuity inputs
(`continuous_deriv_snd_inf`, `continuous_chordW_inf`) for a `C^∞` family and reuse the rest.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff
open MeasureTheory intervalIntegral

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

/-! ## Continuity of `chordW` for a `C^∞` family -/

/-- The derivative in the second variable of a smooth two-variable function is jointly
continuous: `(τ, u) ↦ ∂₂ c(τ, u)`.  (Smooth version of `continuous_deriv_snd`.) -/
theorem continuous_deriv_snd_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun p : ℝ × ℝ => deriv (fun v : ℝ => c p.1 v) p.2) := by
  have hslice : ∀ τ u : ℝ, deriv (fun v : ℝ => c τ v) u
      = (fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, u)) ((0 : ℝ), 1) := by
    intro τ u
    have h2 : HasFDerivAt (fun z : ℝ × ℝ => c z.1 z.2)
        (fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, u)) (τ, u) :=
      (hc.differentiable (by simp) (τ, u)).hasFDerivAt
    have h1 : HasFDerivAt (fun v : ℝ => (τ, v)) (ContinuousLinearMap.inr ℝ ℝ ℝ) u :=
      hasFDerivAt_prodMk_right τ u
    have h3 : HasFDerivAt ((fun z : ℝ × ℝ => c z.1 z.2) ∘ (fun v : ℝ => (τ, v)))
        ((fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, u))
          ∘SL (ContinuousLinearMap.inr ℝ ℝ ℝ)) u :=
      h2.comp u h1
    have h4 := h3.fderiv
    rw [show (fun v : ℝ => c τ v)
          = ((fun z : ℝ × ℝ => c z.1 z.2) ∘ (fun v : ℝ => (τ, v))) from rfl]
    rw [show deriv (((fun z : ℝ × ℝ => c z.1 z.2)) ∘ (fun v : ℝ => (τ, v))) u
          = (fderiv ℝ ((fun z : ℝ × ℝ => c z.1 z.2) ∘ (fun v : ℝ => (τ, v))) u) 1 from
        (fderiv_apply_one_eq_deriv).symm]
    rw [h4]
    simp [ContinuousLinearMap.inr_apply]
  have hcont : Continuous (fun z : ℝ × ℝ =>
      (fderiv ℝ (fun z : ℝ × ℝ => c z.1 z.2) z) ((0 : ℝ), (1 : ℝ))) :=
    (hc.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  simpa only [hslice] using hcont

/-- `chordW` is jointly continuous in `(τ, t, r)` for a `C^∞` family.
(Smooth version of `continuous_chordW`.) -/
theorem continuous_chordW_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => chordW c z.1 z.2.1 z.2.2) := by
  have hderiv := continuous_deriv_snd_inf c hc
  have hg : Continuous (fun p : (ℝ × (ℝ × ℝ)) × ℝ =>
      (p.1.1, p.1.2.1 + p.2 * p.1.2.2)) := by fun_prop
  have huncurry : Continuous (Function.uncurry (fun z : ℝ × (ℝ × ℝ) => fun s : ℝ =>
      deriv (fun v : ℝ => c z.1 v) (z.2.1 + s * z.2.2))) := hderiv.comp hg
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) huncurry (-1) 1
  simpa only [chordW, Function.uncurry] using this

/-! ## The main lemma -/

theorem chordW_ne_zero_nhds_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t)
    (hinj : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t t', c τ t = c τ t' → ∃ m : ℤ, t' = t + 2 * Real.pi * m)
    (himm : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, deriv (c τ) t ≠ 0)
    {A B : ℝ} (hA : -Real.pi < A) (hB : B < Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Set.Ioo (-δ) (1 + δ), ∀ t : ℝ, ∀ r ∈ Set.Icc A B,
      Work.RPB.B2.chordW c τ t r ≠ 0 := by
  have hFcont : Continuous (fun z : ℝ × (ℝ × ℝ) => chordW c z.1 z.2.1 z.2.2) :=
    continuous_chordW_inf c hc
  -- pointwise non-vanishing on the `τ`-interval `[0,1]`
  have hne : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t r, r ∈ Set.Icc A B → chordW c τ t r ≠ 0 := by
    intro τ hτ t r hr
    rcases eq_or_ne r 0 with h0 | hne0
    · subst h0
      intro h
      have h2 : (2 : ℂ) * deriv (fun u : ℝ => c τ u) t = 0 := by
        rw [← chordW_zero c τ t]; exact h
      exact himm τ hτ t ((mul_eq_zero.mp h2).resolve_left (by norm_num))
    · intro h
      have hv : Work.RPB.chordVec c τ t r = 0 := by
        rw [chordVec_eq_mul_chordW_inf c hc τ t r, h, mul_zero]
      exact chordVec_ne_zero_of c hinj hτ (lt_of_lt_of_le hA hr.1) (lt_of_le_of_lt hr.2 hB)
        hne0 hv
  -- a compact slab on which `chordW` is non-zero, thickened to a neighbourhood
  have hKcpt : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc A B)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hopen : IsOpen {p : ℝ × (ℝ × ℝ) | chordW c p.1 p.2.1 p.2.2 ≠ 0} :=
    (isClosed_singleton (x := (0 : ℂ))).isOpen_compl.preimage hFcont
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc A B)
      ⊆ {p : ℝ × (ℝ × ℝ) | chordW c p.1 p.2.1 p.2.2 ≠ 0} := by
    rintro ⟨τ0, t0, r0⟩ ⟨hτ0, _, hr0⟩
    exact hne τ0 hτ0 t0 r0 hr0
  obtain ⟨δ, hδpos, hδsub⟩ := hKcpt.exists_thickening_subset_open hopen hsub
  refine ⟨δ, hδpos, ?_⟩
  intro τ hτ t r hr
  obtain ⟨t1, ht1, m, hm⟩ := exists_mod_two_pi t
  have hperF : Function.Periodic (fun t : ℝ => chordW c τ t r) (2 * Real.pi) :=
    fun t => chordW_add_two_pi c hper τ t r
  have hperτ' : chordW c τ t r = chordW c τ t1 r := by
    have hh := (hperF.int_mul m) t1
    rw [mul_comm (↑m : ℝ) (2 * Real.pi)] at hh
    rw [← hm] at hh
    exact hh
  -- the translated point `(τ, t₁, r)` is within `δ` of the compact slab
  have hu_mem : max 0 (min τ 1) ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hdist_abs : |τ - max 0 (min τ 1)| < δ := by
    rcases le_or_gt τ 0 with h | h
    · have hmax : max 0 (min τ 1) = 0 := by
        rw [min_eq_left (by linarith : τ ≤ 1), max_eq_left h]
      rw [hmax, sub_zero, abs_of_nonpos h]
      linarith [hτ.1]
    · rcases le_or_gt τ 1 with h1 | h1
      · have hmax : max 0 (min τ 1) = τ := by rw [min_eq_left h1, max_eq_right h.le]
        rw [hmax, sub_self, abs_zero]; exact hδpos
      · have hmax : max 0 (min τ 1) = 1 := by
          rw [min_eq_right h1.le, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
        rw [hmax, abs_of_pos (by linarith : (0 : ℝ) < τ - 1)]
        linarith [hτ.2]
  have hdist : dist (τ, t1, r) (max 0 (min τ 1), t1, r) < δ := by
    have heq : dist (τ, t1, r) (max 0 (min τ 1), t1, r) = |τ - max 0 (min τ 1)| := by
      simp [Prod.dist_eq, Real.dist_eq]
    rw [heq]; exact hdist_abs
  have hmem : (τ, t1, r) ∈ Metric.thickening δ
      (Set.Icc (0 : ℝ) 1 ×ˢ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc A B)) := by
    rw [Metric.mem_thickening_iff]
    exact ⟨(max 0 (min τ 1), t1, r), ⟨hu_mem, ht1, hr⟩, hdist⟩
  have hne' : chordW c τ t1 r ≠ 0 := hδsub hmem
  rw [hperτ']
  exact hne'

end Work.RPB.B2
