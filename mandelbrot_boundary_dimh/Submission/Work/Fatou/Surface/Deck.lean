import Submission.Work.Fatou.Surface.Manifold
import Submission.Lib.Unif2.Packaging

/-!
# The deck transformation `ζ ↦ ζ+1` of `XF` and the shift it induces

The map `T : ζ ↦ ζ+1` is a biholomorphism of `XF D` (it is the identity in the charts
`chart n → chart (n+1)`), so for any biholomorphism `Ψ : XF D ≃ ℂ` the conjugate
`A := Ψ ∘ T ∘ Ψ⁻¹` is an entire injective fixed-point-free map, hence (by `InjEntireTranslation`)
a translation: `Ψ (ζ+1) = Ψ ζ + b` with `b ≠ 0`.
-/

namespace Work.Fatou

open MandelDim Filter Set Metric
open scoped Topology Manifold ContDiff
open LeanEval.Geometry

noncomputable section

namespace FatouData

/-- The deck transformation `ζ ↦ ζ+1` of the surface. -/
def T (D : FatouData) : D.XF → D.XF := fun u => D.ofℂ (D.toℂ u + 1)

/-- Its inverse. -/
def Tinv (D : FatouData) : D.XF → D.XF := fun u => D.ofℂ (D.toℂ u - 1)

@[simp] theorem toℂ_T (D : FatouData) (u : D.XF) : D.toℂ (D.T u) = D.toℂ u + 1 := rfl
@[simp] theorem toℂ_Tinv (D : FatouData) (u : D.XF) : D.toℂ (D.Tinv u) = D.toℂ u - 1 := rfl

theorem T_Tinv (D : FatouData) (u : D.XF) : D.T (D.Tinv u) = u := by
  show D.ofℂ (D.toℂ (D.Tinv u) + 1) = u
  rw [D.toℂ_Tinv]
  simp

theorem Tinv_T (D : FatouData) (u : D.XF) : D.Tinv (D.T u) = u := by
  show D.ofℂ (D.toℂ (D.T u) - 1) = u
  rw [D.toℂ_T]
  simp

theorem T_injective (D : FatouData) : Function.Injective D.T := by
  intro u v huv
  have h : D.Tinv (D.T u) = D.Tinv (D.T v) := by rw [huv]
  rwa [D.Tinv_T, D.Tinv_T] at h

theorem T_ne_self (D : FatouData) (u : D.XF) : D.T u ≠ u := by
  intro h
  have h2 : D.toℂ (D.T u) = D.toℂ u := by rw [h]
  rw [D.toℂ_T] at h2
  have h3 : (D.toℂ u + 1).re = (D.toℂ u).re := congrArg Complex.re h2
  rw [Complex.add_re, Complex.one_re] at h3
  linarith

theorem continuous_T (D : FatouData) : Continuous D.T :=
  D.continuous_ofℂ.comp (D.continuous_toℂ.add continuous_const)

theorem continuous_Tinv (D : FatouData) : Continuous D.Tinv :=
  D.continuous_ofℂ.comp (D.continuous_toℂ.sub continuous_const)

/-- `T` is the identity in the charts `chart n → chart (n+1)`. -/
theorem analyticAt_T (D : FatouData) (u : D.XF) :
    AnalyticAt ℂ ((chartAt ℂ (D.T u)) ∘ D.T ∘ (chartAt ℂ u).symm) ((chartAt ℂ u) u) := by
  set n : ℤ := ⌊(D.toℂ u).re⌋ with hn
  have hcu : chartAt ℂ u = D.chart n := rfl
  have hcv : chartAt ℂ (D.T u) = D.chart (n + 1) := by
    show D.chart ⌊(D.toℂ (D.T u)).re⌋ = D.chart (n + 1)
    rw [D.toℂ_T]
    have h1 : (D.toℂ u + 1).re = (D.toℂ u).re + 1 := by simp
    rw [h1, Int.floor_add_one, hn]
  rw [hcu, hcv]
  refine AnalyticAt.congr analyticAt_id ?_
  have hmem : (D.chart n) u ∈ (D.chart n).target := (D.chart n).map_source (mem_chart_source ℂ u)
  filter_upwards [(D.chart n).open_target.mem_nhds hmem] with w hw
  obtain ⟨ζ, hζ, hzw⟩ := hw
  have hwr : w ∈ Set.range D.devH := ⟨ζ, hzw⟩
  show w = D.chart (n + 1) (D.T ((D.chart n).symm w))
  rw [show (D.chart n).symm w = D.ofℂ (D.devHI w + (n : ℂ)) from rfl]
  have hval : D.chart (n + 1) (D.T (D.ofℂ (D.devHI w + (n : ℂ)))) = w := by
    rw [show D.T (D.ofℂ (D.devHI w + (n : ℂ))) =
        D.ofℂ (D.devHI w + (n : ℂ) + 1) from rfl, D.chart_apply_ofℂ]
    rw [show D.devHI w + (n : ℂ) + 1 - ((n + 1 : ℤ) : ℂ) = D.devHI w by push_cast; ring]
    exact D.devH_apply_devHI hwr
  exact hval.symm

theorem contMDiff_T (D : FatouData) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ D.T :=
  Submission.contMDiff_of_analyticAt_charts D.continuous_T D.analyticAt_T

end FatouData

open FatouData

/-- **The deck shift.**  For any biholomorphism `Ψ : XF D ≃ ℂ`, the conjugate of the deck
transformation `ζ ↦ ζ+1` is a translation: there is `b ≠ 0` with `Ψ (ζ+1) = Ψ ζ + b`. -/
theorem exists_deck_shift (hIET : MandelDim.InjEntireTranslation) (D : FatouData)
    (Ψ : D.XF ≃ₘ⟮modelWithCornersSelf ℂ ℂ, modelWithCornersSelf ℂ ℂ⟯ ℂ) :
    ∃ b : ℂ, b ≠ 0 ∧ ∀ u : D.XF, Ψ (D.T u) = Ψ u + b := by
  set A : ℂ → ℂ := fun w => Ψ (D.T (Ψ.symm w)) with hA
  have hcont : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ A :=
    (Ψ.contMDiff.comp D.contMDiff_T).comp Ψ.symm.contMDiff
  have hdiff : Differentiable ℂ A := by
    have h1 : ContDiff ℂ 1 A := ((contMDiff_iff_contDiff).1 hcont).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
    exact h1.differentiable one_ne_zero
  have hinj : Function.Injective A := by
    intro w w' hww'
    have h1 : D.T (Ψ.symm w) = D.T (Ψ.symm w') := Ψ.injective hww'
    have h2 : Ψ.symm w = Ψ.symm w' := D.T_injective h1
    exact Ψ.symm.injective h2
  have hnofix : ∀ w, A w ≠ w := by
    intro w hw
    have h1 : D.T (Ψ.symm w) = Ψ.symm w := by
      apply Ψ.injective
      change A w = Ψ (Ψ.symm w)
      rw [hw, Ψ.apply_symm_apply]
    exact D.T_ne_self (Ψ.symm w) h1
  obtain ⟨b, hb, hbw⟩ := hIET A hdiff hinj hnofix
  refine ⟨b, hb, fun u => ?_⟩
  have h : Ψ (D.T (Ψ.symm (Ψ u))) = Ψ u + b := hbw (Ψ u)
  rwa [Ψ.symm_apply_apply] at h

end

end Work.Fatou
