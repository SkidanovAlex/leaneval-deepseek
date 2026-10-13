import Mathlib
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.Frame.eaEvalC_toC
import Submission.Work.WilE3.eaEval_analytic

namespace Work.WilE3.Taylor.Grad

open Filter Topology

/-- **The origin of a polar arc lies on the polar system.**

If an analytic arc `γ` through `y` satisfies the gradient-polar system of `Φ` with pivot `i₀`
along its values `γ t` for all small `t > 0` (i.e. `Φ ∘ γ` vanishes to order `m > 0` and all the
pivot minors `gpolMinor c Φ i₀ i`, `i ≠ i₀`, vanish along `γ`), then `y` itself satisfies the
system, so that the complex point `toC y` is a zero of the complexified system.

The pivot row (`i = i₀`) is `Φ` itself: the vanishing of `eaEval c Φ ∘ γ` to order `m > 0` at `0`
forces `eaEval c Φ (γ 0) = 0`.  For the remaining rows the hypothesis gives equality to `0`
eventually along `nhdsWithin 0 (Ioi 0)`; the analytic (hence continuous) germ
`t ↦ eaEval c (polarSys c Φ i₀ i) (γ t)` therefore has limit `0` along that filter and, being
continuous at `0`, equals `0` there as well.  Transferring back through
`Frame.eaEvalC_toC` turns the real vanishing into the complex one. -/
theorem polarSys_eval_toC_eq_zero {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (i₀ : Fin k)
    {m : ℕ}
    (hγ : AnalyticAt ℝ γ 0) (hγ0 : γ 0 = y) (hm : 0 < m)
    (hord : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m)
    (hminors : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
      WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t) = 0) :
    ∀ i : Fin k, Work.WilE3.eaEvalC c (Work.WilE3.Taylor.polarSys c Φ i₀ i)
      (Work.WilE3.Frame.toC y) = 0 := by
  intro i
  -- It suffices to show that the (real) polar system vanishes at `y`.
  have hy : WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) y = 0 := by
    by_cases hi : i = i₀
    · -- pivot row: `polarSys c Φ i₀ i₀ = Φ`, and `eaEval c Φ ∘ γ` vanishes to order `m > 0`.
      have hps : Work.WilE3.Taylor.polarSys c Φ i₀ i = Φ := by
        simp [Work.WilE3.Taylor.polarSys, hi]
      rw [hps]
      have h0 : (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = 0 :=
        apply_eq_zero_of_analyticOrderAt_ne_zero
          (f := fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) (z₀ := (0 : ℝ))
          (by rw [hord]; exact_mod_cast hm.ne')
      simpa [hγ0] using h0
    · -- remaining rows: analytic germ vanishing eventually on `nhdsWithin 0 (Ioi 0)`.
      have hgan : AnalyticAt ℝ
          (fun t : ℝ => WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t)) 0 :=
        (Work.WilE3.eaEval_analytic c _ (γ 0)).comp hγ
      have hmin : (fun t : ℝ =>
            WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t))
          =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun _ => (0 : ℝ)) :=
        hminors.mono (fun t ht => ht i hi)
      have hnb : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot le_rfl
      have h1 : Tendsto
          (fun t : ℝ => WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
        Filter.Tendsto.congr' hmin.symm tendsto_const_nhds
      have h2 : Tendsto
          (fun t : ℝ => WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (𝓝 ((fun t : ℝ =>
            WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t)) 0)) :=
        hgan.continuousAt.continuousWithinAt
      have hg0 : (fun t : ℝ =>
            WilkiesDesign.E.eaEval c (Work.WilE3.Taylor.polarSys c Φ i₀ i) (γ t)) 0 = 0 :=
        tendsto_nhds_unique' hnb h2 h1
      simpa [hγ0] using hg0
  simp only [Work.WilE3.Frame.eaEvalC_toC, hy, Complex.ofReal_zero]

end Work.WilE3.Taylor.Grad
