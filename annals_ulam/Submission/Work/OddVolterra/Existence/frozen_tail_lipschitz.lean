import Mathlib
import Submission.Work.OddVolterra.WinData.thetaM_deriv_close_ext
import Submission.Work.Anchor.ThetaM_contDiffOn_wide
import Submission.Work.OddVolterra.WinData.smooth_upgrade

/-!
# The frozen tail of the odd transition-slope system is Lipschitz in the slope

`Work.OddVolterra.Existence.aw_frozen_tail_close` shows that the frozen tail

`∫_{19/20}^{1} Θ_M(s,σ, baseState σ) dσ`

is `O(δ)`-close to its unperturbed value, uniformly in `s`.  For the Volterra engine one needs
the *quantitative* form: the difference of the two tails (perturbed and unperturbed) at two
slopes `u`, `v` is Lipschitz in the slope with constant proportional to `δ`.  This is what the
present file proves: for `u, v ∈ [7/10, 19/20]`,

`‖(T_h(u) - T_h(v)) - (T_0(u) - T_0(v))‖ ≤ C δ |u - v|`,

where `T_g(s) = ∫_{19/20}^1 Θ_M(n, g, s, σ, baseState σ) dσ`.

The mathematical input is exactly `Work.OddVolterra.WinData.thetaM_deriv_close_ext`, which bounds
the `s`-derivative of the pointwise defect `Θ_M(n,h,s,σ,z) - Θ_M(n,0,s,σ,z)` by `C δ`
(an estimate that needs `n+3` derivatives of `h`).  The mean value theorem converts this into the
pointwise Lipschitz bound in `s`, and the `σ`-integral of length `1/20` is then estimated with
`intervalIntegral.norm_integral_le_of_norm_le_const`.  The differentiability in `s` on the window
comes from the smoothness of the manifest `Θ`-data (`Work.Anchor.ThetaM_contDiffOn_wide`), and the
interval integrability of the tail integrand from
`Work.OddVolterra.WinData.intervalIntegrable_thetaM_of_curve`.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra

noncomputable section

/-- The zero function has all its `C¹`-norms bounded by `1/100`. -/
private lemma ftl_small_zero :
    ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) x| ≤ 1 / 100 := by
  intro k hk x
  have h0 : iteratedDeriv k (0 : ℝ → ℝ) x = 0 := by
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split <;> simp
  rw [h0, abs_zero]; norm_num

/-- The support of the zero function is contained in the transition window. -/
private lemma ftl_support_zero :
    Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
  intro x hx
  rw [Function.mem_support] at hx
  exact absurd rfl hx

/-- **The frozen tail is Lipschitz in the slope.**  There is a constant `C` such that for every
smooth bump `h` supported in the transition window `[1 - 2τ, 1 - τ]` whose derivatives up to
order `n + 3` are bounded by `δ ≤ 1/100`, the difference of the frozen tails at two slopes
`u, v ∈ [7/10, 19/20]` is bounded by `C δ |u - v|`, both for the perturbation `h` and for the
unperturbed data. -/
theorem frozen_tail_lipschitz (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) →
      ∀ u ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), ∀ v ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        ‖((∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
              Work.OddVolterra.KernelExt.ThetaM n h u σ (Work.OddVolterra.baseState σ))
            - (∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
              Work.OddVolterra.KernelExt.ThetaM n h v σ (Work.OddVolterra.baseState σ)))
          - ((∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
              Work.OddVolterra.KernelExt.ThetaM n 0 u σ (Work.OddVolterra.baseState σ))
            - (∫ σ in Work.OddVolterra.WinData.wHi..(1 : ℝ),
              Work.OddVolterra.KernelExt.ThetaM n 0 v σ (Work.OddVolterra.baseState σ)))‖
          ≤ C * δ * |u - v| := by
  obtain ⟨C, L, hCpos, hLpos, hclose⟩ := WinData.thetaM_deriv_close_ext n hn
  refine ⟨C / 20, by linarith, ?_⟩
  intro h δ hh hδpos hδ100 hjet hsupp u hu v hv
  have hsmallh : ∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k h x| ≤ 1 / 100 :=
    fun k hk x => le_trans (hjet k (by omega) x) hδ100
  -- ## Step 1: differentiability of the `s`-slice of `Θ_M` on the window
  have hslice : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100) →
      ∀ σ ∈ Set.Ioc (19 / 20 : ℝ) 1, ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        DifferentiableAt ℝ (fun x : ℝ => KernelExt.ThetaM n g x σ (baseState σ)) s := by
    intro g hg hgs σ hσ s hs
    have hreg := Anchor.ThetaM_contDiffOn_wide (n := n) (h := g) hg hgs
    have hmap : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => (x, (σ, baseState σ)))
        (Set.Icc (69 / 100 : ℝ) (96 / 100)) := by fun_prop
    have hmaps : Set.MapsTo (fun x : ℝ => (x, (σ, baseState σ)))
        (Set.Icc (69 / 100 : ℝ) (96 / 100))
        {p : ℝ × ℝ × St | p.1 ∈ Set.Ioo (481 / 1000 : ℝ) (97 / 100) ∧
          p.2.1 ∈ Set.Ioo (481 / 1000 : ℝ) (102 / 100) ∧
          ‖p.2.2 - baseState p.2.1‖ < 9 / 20} := by
      intro x hx
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
        ⟨by linarith [hσ.1], by linarith [hσ.2]⟩,
        by rw [sub_self, norm_zero]; norm_num⟩
    have hslice' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x : ℝ => KernelExt.ThetaM n g x σ (baseState σ))
        (Set.Icc (69 / 100 : ℝ) (96 / 100)) := by
      simpa [Function.comp_def] using hreg.comp hmap hmaps
    exact (hslice'.contDiffAt (Icc_mem_nhds (by linarith [hs.1])
      (by linarith [hs.2]))).differentiableAt (by simp)
  -- ## Step 2: pointwise Lipschitz bound in the slope, by the mean value theorem
  have hpoint : ∀ σ ∈ Set.Ioc (19 / 20 : ℝ) 1,
      ‖(KernelExt.ThetaM n h u σ (baseState σ) - KernelExt.ThetaM n 0 u σ (baseState σ))
       - (KernelExt.ThetaM n h v σ (baseState σ) - KernelExt.ThetaM n 0 v σ (baseState σ))‖
      ≤ C * δ * |u - v| := by
    intro σ hσ
    have hdu : ∀ x ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), DifferentiableAt ℝ
        (fun x : ℝ => KernelExt.ThetaM n h x σ (baseState σ) -
          KernelExt.ThetaM n 0 x σ (baseState σ)) x :=
      fun x hx => (hslice h hh hsmallh σ hσ x hx).sub
        (hslice 0 contDiff_const ftl_small_zero σ hσ x hx)
    have hbnd : ∀ x ∈ Set.Icc (7 / 10 : ℝ) (19 / 20), ‖deriv
        (fun x : ℝ => KernelExt.ThetaM n h x σ (baseState σ) -
          KernelExt.ThetaM n 0 x σ (baseState σ)) x‖ ≤ C * δ := by
      intro x hx
      have hdd : deriv (fun x : ℝ => KernelExt.ThetaM n h x σ (baseState σ) -
            KernelExt.ThetaM n 0 x σ (baseState σ)) x
          = deriv (fun x : ℝ => KernelExt.ThetaM n h x σ (baseState σ)) x
            - deriv (fun x : ℝ => KernelExt.ThetaM n 0 x σ (baseState σ)) x :=
        deriv_sub (hslice h hh hsmallh σ hσ x hx)
          (hslice 0 contDiff_const ftl_small_zero σ hσ x hx)
      rw [hdd]
      exact (hclose h δ hh hδpos hδ100 hjet hsupp x ⟨by linarith [hx.1], hx.2⟩ σ
        ⟨by linarith [hσ.1], hσ.2⟩ (baseState σ)
        (by rw [Metric.mem_closedBall, dist_self]; norm_num) (baseState σ)
        (by rw [Metric.mem_closedBall, dist_self]; norm_num)).1
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun x : ℝ =>
        KernelExt.ThetaM n h x σ (baseState σ) - KernelExt.ThetaM n 0 x σ (baseState σ))
      (s := Set.Icc (7 / 10 : ℝ) (19 / 20)) (x := v) (y := u) (C := C * δ)
      hdu hbnd (convex_Icc _ _) hv hu
    rw [Real.norm_eq_abs] at hmvt
    exact hmvt
  -- ## Step 3: interval integrability of the tail integrands
  have hint : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g →
      Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      (∀ k : ℕ, k ≤ 1 → ∀ x : ℝ, |iteratedDeriv k g x| ≤ 1 / 100) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) (19 / 20),
        IntervalIntegrable (fun σ : ℝ => KernelExt.ThetaM n g s σ (baseState σ)) volume
          WinData.wHi 1 := by
    intro g hg hgs hgsm s hs
    refine WinData.intervalIntegrable_thetaM_of_curve (h := g) (c := baseState) (s := s)
      (a := WinData.wHi) (b := 1) n hg hgs hgsm ?_ ?_ ?_ ?_ ?_
    · linarith [hs.1]
    · linarith [hs.2]
    · rw [WinData.wHi]; norm_num
    · exact Anchor.contDiff_baseState_eng.continuous.continuousOn
    · intro σ hσ
      rw [WinData.wHi] at hσ
      obtain ⟨h1, h2⟩ := hσ
      exact ⟨by linarith, by linarith,
        WinData.one_fifth_lt_abs_coord (σ := σ) (by linarith) (by linarith)
          (z := baseState σ) (by simp) 0 (Or.inl rfl),
        WinData.one_fifth_lt_abs_coord (σ := σ) (by linarith) (by linarith)
          (z := baseState σ) (by simp) 1 (Or.inr rfl)⟩
  -- ## Step 4: assemble the four tails into a single integral of the pointwise defect
  have hIhu := hint h hh hsupp hsmallh u hu
  have hIhv := hint h hh hsupp hsmallh v hv
  have hI0u := hint 0 contDiff_const ftl_support_zero ftl_small_zero u hu
  have hI0v := hint 0 contDiff_const ftl_support_zero ftl_small_zero v hv
  have hG : ((∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n h u σ (baseState σ))
        - (∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n h v σ (baseState σ)))
      - ((∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n 0 u σ (baseState σ))
        - (∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n 0 v σ (baseState σ)))
      = ((∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n h u σ (baseState σ))
        - (∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n 0 u σ (baseState σ)))
      - ((∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n h v σ (baseState σ))
        - (∫ σ in WinData.wHi..(1 : ℝ), KernelExt.ThetaM n 0 v σ (baseState σ))) := by
    abel
  rw [hG, ← intervalIntegral.integral_sub hIhu hI0u,
    ← intervalIntegral.integral_sub hIhv hI0v,
    ← intervalIntegral.integral_sub (hIhu.sub hI0u) (hIhv.sub hI0v)]
  have hbound : ‖∫ σ in WinData.wHi..(1 : ℝ),
      (KernelExt.ThetaM n h u σ (baseState σ) - KernelExt.ThetaM n 0 u σ (baseState σ)
        - (KernelExt.ThetaM n h v σ (baseState σ) - KernelExt.ThetaM n 0 v σ (baseState σ)))‖
      ≤ (C * δ * |u - v|) * |1 - WinData.wHi| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro σ hσ
    rw [Set.uIoc_of_le (by rw [WinData.wHi]; norm_num)] at hσ
    rw [WinData.wHi] at hσ
    exact hpoint σ ⟨hσ.1, hσ.2⟩
  refine le_trans hbound (le_of_eq ?_)
  rw [show |1 - WinData.wHi| = 1 / 20 by rw [WinData.wHi]; norm_num]
  ring

end

end Work.OddVolterra.Existence
