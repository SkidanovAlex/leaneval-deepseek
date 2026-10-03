import Mathlib
import Submission.Work.FatouCH.uniqueSetup
import Submission.Unif.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

/-!
# `psiOf` is entire

Given `Φ₀` holomorphic and injective on the open set `Q` and a second map `Φ` with the same fibres
modulo `ℤ` (the transfer hypothesis `htrans` of `Submission.Work.FatouCH.uniqueSetup`), the
`ℤ`-equivariant extension `ψ = psiOf Q Φ₀ Φ hex` of `Φ ∘ Φ₀⁻¹` is complex differentiable everywhere.

At a point `u₀ = Φ₀ z₀ + n₀` (`z₀ ∈ Q`), the holomorphic inverse function theorem gives a local
inverse `r` of `Φ₀` at `z₀`, and near `u₀` one has `ψ u = Φ (r (u - n₀)) + n₀`; this is a
composition of analytic maps.
-/

namespace Work.FatouCH

open Set Metric Complex Filter
open scoped Topology

/-- Shifting the argument by a constant does not change analyticity. -/
theorem analyticAt_comp_add_const_iff {ψ : ℂ → ℂ} {c x : ℂ} :
    AnalyticAt ℂ (fun w : ℂ => ψ (w + c)) (x - c) ↔ AnalyticAt ℂ ψ x := by
  have hf : AnalyticAt ℂ (fun w : ℂ => w + c) (x - c) := analyticAt_id.add analyticAt_const
  have hf' : deriv (fun w : ℂ => w + c) (x - c) ≠ 0 := by
    rw [deriv_add_const, deriv_id'']
    norm_num
  have h := analyticAt_comp_iff_of_deriv_ne_zero (g := ψ) hf hf'
  have h2 : x - c + c = x := sub_add_cancel x c
  rw [h2] at h
  simpa [Function.comp_def] using h

/-- `psiOf Q Φ₀ Φ hex` is entire. -/
theorem psiOf_entire {Q : Set ℂ} {Φ₀ Φ : ℂ → ℂ} (hex : FatouRepExists Q Φ₀)
    (hQ : IsOpen Q) (hΦ₀ : DifferentiableOn ℂ Φ₀ Q) (hinj : Set.InjOn Φ₀ Q)
    (hΦ : DifferentiableOn ℂ Φ Q)
    (htrans : ∀ z ∈ Q, ∀ z' ∈ Q, ∀ k : ℤ, Φ₀ z' = Φ₀ z + (k : ℂ) → Φ z' = Φ z + (k : ℂ)) :
    Differentiable ℂ (psiOf Q Φ₀ Φ hex) := by
  intro u₀
  set z₀ : ℂ := (psiRep hex u₀).1 with hz₀def
  set n₀ : ℤ := (psiRep hex u₀).2 with hn₀def
  have hz₀Q : z₀ ∈ Q := psiRep_fst_mem hex u₀
  have hspec : Φ₀ z₀ + (n₀ : ℂ) = u₀ := psiRep_spec hex u₀
  have hΦ₀an : AnalyticAt ℂ Φ₀ z₀ := hΦ₀.analyticAt (hQ.mem_nhds hz₀Q)
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hQ z₀ hz₀Q
  have hderiv : deriv Φ₀ z₀ ≠ 0 :=
    Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hρpos hΦ₀an (hinj.mono hρsub)
  set r : ℂ → ℂ :=
    HasStrictDerivAt.localInverse Φ₀ (deriv Φ₀ z₀) z₀ hΦ₀an.hasStrictDerivAt hderiv with hrdef
  have hran : AnalyticAt ℂ r (Φ₀ z₀) := hΦ₀an.analyticAt_localInverse hderiv
  have hleft : ∀ᶠ x in 𝓝 z₀, r (Φ₀ x) = x :=
    hΦ₀an.hasStrictDerivAt.eventually_left_inverse hderiv
  have hrz : r (Φ₀ z₀) = z₀ := hleft.self_of_nhds
  have hright : ∀ᶠ w in 𝓝 (Φ₀ z₀), Φ₀ (r w) = w :=
    hΦ₀an.hasStrictDerivAt.eventually_right_inverse hderiv
  have hrQ : ∀ᶠ w in 𝓝 (Φ₀ z₀), r w ∈ Q :=
    hran.continuousAt.eventually (hQ.mem_nhds (by rw [hrz]; exact hz₀Q))
  -- the formula for `ψ` near `Φ₀ z₀`
  have hev : ∀ᶠ w in 𝓝 (Φ₀ z₀),
      psiOf Q Φ₀ Φ hex (w + (n₀ : ℂ)) = Φ (r w) + (n₀ : ℂ) := by
    filter_upwards [hright, hrQ] with w hw hwQ
    exact psiOf_apply_rep hex htrans hwQ n₀ (by rw [hw])
  -- analyticity of the right-hand side at `Φ₀ z₀`
  have hΦr : AnalyticAt ℂ (fun v : ℂ => Φ (r v)) (Φ₀ z₀) := by
    have h1 : AnalyticAt ℂ Φ (r (Φ₀ z₀)) := by
      rw [hrz]
      exact hΦ.analyticAt (hQ.mem_nhds hz₀Q)
    exact h1.comp hran
  have han0 : AnalyticAt ℂ (fun w : ℂ => psiOf Q Φ₀ Φ hex (w + (n₀ : ℂ))) (Φ₀ z₀) :=
    (hΦr.add analyticAt_const).congr (Filter.EventuallyEq.symm hev)
  -- transport to `u₀ = Φ₀ z₀ + n₀`
  have h1 : AnalyticAt ℂ (fun w : ℂ => psiOf Q Φ₀ Φ hex (w + (n₀ : ℂ))) (u₀ - (n₀ : ℂ)) := by
    rw [show u₀ - (n₀ : ℂ) = Φ₀ z₀ from by rw [← hspec]; ring]
    exact han0
  exact ((analyticAt_comp_add_const_iff (ψ := psiOf Q Φ₀ Φ hex) (c := (n₀ : ℂ))
    (x := u₀)).mp h1).differentiableAt

end Work.FatouCH
