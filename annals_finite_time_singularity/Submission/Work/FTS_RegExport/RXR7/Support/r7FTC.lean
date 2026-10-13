/-
# `Work.FTS_RegExport.RXR7.Support.r7FTC` — the fundamental theorem of calculus for the profile

For fixed `(z,θ) ∈ Qd` and every horizon `0 < S`, the profile `s ↦ Prof α g z θ s` is a
primitive of `-K7 α Φs E g z θ ·` on `[0,S]`, where `K7` is the closed-form right-hand side
`Vz7ᵣ·D_z(Prof) + Vθ7ᵣ·∂_θ(Prof) + cs7ᵣ·Prof` of the transport equation.

## Route

`0 ≤ τ ≤ S` is split at `τ = 0` (trivial: both sides vanish).  For `τ > 0` we apply Mathlib's
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` with `f := fun s => Prof α g z θ s`,
`f' := fun s => -(K7 α Φs E g z θ s)`, `a = 0`, `b = τ`; it needs

* `ContinuousOn f (Icc 0 τ)` — on `Icc 0 τ ⊆ Ici 0` the profile agrees with the explicit
  `F_* z θ + g z θ s` (for `z > 0`, `τ ≥ 0` the right-Taylor extension `tauExt` and the
  sanitiser `gS` are both inert and `extG` is the identity), and `s ↦ g z θ s` is continuous
  on `Ici 0` by the `cont` field of the regularity package `RegPkgMin`, which is part of
  `DynOK'`.  This is the only endpoint (`τ = 0`) information needed, and it is exactly what
  the transport identity `hEq` (stated for `τ > 0` only) cannot supply by itself;
* the pointwise derivative on `Ioo 0 τ` — the hypothesis `hEq` (every point there satisfies
  `0 < s ≤ τ ≤ S`);
* `IntervalIntegrable f' volume 0 τ` — `hK7cont` restricts to continuity of the `τ`-slice
  `s ↦ K7 α Φs E g z θ s` on `Icc 0 τ = uIcc 0 τ`, hence interval integrability, and the
  negated version via `IntervalIntegrable.neg`.

`intervalIntegral.integral_neg` turns the resulting identity
`∫ s in 0..τ, -(K7 …) = Prof … τ - Prof … 0` into the stated form.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS_RegExport.RXR7.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR7.Support

open Set Filter MeasureTheory

theorem r7FTC {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hK7cont : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.FTS_RegExport.RXR7.K7 α Φs E g p.1 p.2.1 p.2.2) (Work.FTS_RegExport.RXR7.R7Slab S))
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (-(Work.FTS_RegExport.RXR7.K7 α Φs E g z θ τ)) τ) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ → τ ≤ S →
      Work.FTS_RegExport.RXR7.Prof α g z θ τ - Work.FTS_RegExport.RXR7.Prof α g z θ 0
        = -∫ s in (0:ℝ)..τ, Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s := by
  intro z θ τ hz hθ hθπ hτ0 hτS
  rcases eq_or_lt_of_le hτ0 with hτeq | hτpos
  · -- the case `τ = 0`: the integral over a point and the difference both vanish
    subst hτeq
    simp
  · -- the case `τ > 0`: the fundamental theorem of calculus on `[0,τ]`
    have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ, hθπ⟩
    -- on `Icc 0 τ` the profile is `F_* z θ + g z θ s` (the sanitiser and the right-Taylor
    -- extension are inert at `z > 0`, `0 ≤ θ ≤ π/2`, `s ≥ 0`)
    have hEqOn : Set.EqOn (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (fun s => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + g z θ s)
        (Set.Icc 0 τ) := by
      intro s hs
      have hs0 : 0 ≤ s := hs.1
      show Work.FTS.Regularity.profFull α
          (Work.FTS.RegPkgGal.extG (Work.FTS_RegExport.RXR7.GR α g)) z θ s = _
      rw [Work.FTS.Regularity.profFull_apply]
      congr 1
      rw [Work.FTS.RegPkgGal.extG_of_pos hz hs0]
      show Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s = g z θ s
      simp only [Work.FTS.FinalV2.gS, hz, hθ.le, hθπ.le, and_self, ↓reduceIte]
      exact Work.FTS.FinalV2.tauExt_of_nonneg g hs0
    -- continuity of the `τ`-slice, including the endpoint `τ = 0` (`RegPkgMin.cont`)
    have hcontg : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc 0 τ) :=
      (hOK.1.1.cont z θ hzθ).mono Set.Icc_subset_Ici_self
    have hcont2 : ContinuousOn (fun s : ℝ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ + g z θ s) (Set.Icc 0 τ) :=
      continuousOn_const.add hcontg
    have hcont : ContinuousOn (fun s : ℝ => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (Set.Icc 0 τ) :=
      hcont2.congr hEqOn
    -- the pointwise derivative, straight from `hEq`
    have hderiv : ∀ s ∈ Set.Ioo (0:ℝ) τ,
        HasDerivAt (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
          (-(Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s)) s := by
      intro s hs
      exact hEq z θ s hz hθ hθπ hs.1 (le_trans hs.2.le hτS)
    -- the `τ`-slice of `K7` is continuous on `[0,τ]`, hence interval integrable
    have hmaps : Set.MapsTo (fun s : ℝ => ((z, θ, s) : ℝ × ℝ × ℝ)) (Set.Icc 0 τ)
        (Work.FTS_RegExport.RXR7.R7Slab S) := by
      intro s hs
      refine ⟨hz, ⟨⟨hθ, hθπ⟩, hs.1, le_trans hs.2 hτS⟩⟩
    have hfuneq : ((fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.K7 α Φs E g p.1 p.2.1 p.2.2)
        ∘ fun x : ℝ => (z, θ, id x))
        = (fun s : ℝ => Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s) := by
      funext s; simp
    have hint : IntervalIntegrable (fun s => Work.FTS_RegExport.RXR7.K7 α Φs E g z θ s)
        MeasureTheory.volume 0 τ := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hτpos.le]
      have hK7c := hK7cont.comp
        ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn) hmaps
      rwa [hfuneq] at hK7c
    have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτpos.le hcont hderiv hint.neg
    rw [intervalIntegral.integral_neg] at hFTC
    exact hFTC.symm

end Work.FTS_RegExport.RXR7.Support
