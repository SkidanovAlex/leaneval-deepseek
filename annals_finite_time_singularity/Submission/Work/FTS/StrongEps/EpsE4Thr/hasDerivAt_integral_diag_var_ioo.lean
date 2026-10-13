import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivAt_integral_diag_var

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace Work.FTS.StrongEps.EpsE4Thr

/-! ## The `L²`-route derivative with *interior* continuity only

`hasDerivAt_integral_diag_var` asks for the a.e. continuity of the time slices on the *closed*
interval `[0,T]`.  That hypothesis is **not** a consequence of the interior differentiability
(nothing controls the *values* of the slices at `0` and `T`: take `u s p = sin (log (1/s))` for
`s > 0`, which is differentiable on `(0,T)` with continuous derivative but has no limit at `0⁺`).
The difference-quotient argument, however, only uses a window `(τ-δ, τ+δ) ⊆ (0,T)` around the base
time, so the interior version is what the mathematics actually needs.

The reduction below is a *shift of the fake time*: put `s₀ = τ/2 > 0` and apply the `Icc`-version to
the family `(s, p) ↦ u (s + s₀) p` on the smaller interval `[0, T/2]`.  There the closed-interval
continuity *is* available (the shifted slices map a closed interval into the interior `(0,T)`), all
the other hypotheses transport because `s ↦ s + s₀` maps `[0,T/2]` into `[0,T]`, and the conclusion
is transported back by the chain rule with the inverse translation `s ↦ s - s₀`.

The two measure-theoretic inputs (translation is measure preserving for `volume.prod ν`, hence
preserves a.e.-strong measurability) are proved first. -/

/-- Translating the first coordinate is measure preserving for `volume.prod ν`. -/
theorem map_prod_add_fst {β : Type*} [MeasurableSpace β] {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite ν] (c : ℝ) :
    MeasureTheory.Measure.map (fun q : ℝ × β => (q.1 + c, q.2))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν)
      = (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν := by
  have h1 := MeasureTheory.Measure.map_prod_map
    (μa := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (μc := ν)
    (f := fun x : ℝ => x + c) (g := id) (measurable_id.add_const c) measurable_id
  rw [MeasureTheory.map_add_right_eq_self (MeasureTheory.volume : MeasureTheory.Measure ℝ) c,
    MeasureTheory.Measure.map_id] at h1
  exact h1.symm

/-- Shifting the first coordinate preserves a.e.-strong measurability. -/
theorem aestronglyMeasurable_comp_add_fst {β : Type*} [MeasurableSpace β]
    {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite ν] {c : ℝ} {Φ : ℝ × β → ℝ}
    (hΦ : MeasureTheory.AEStronglyMeasurable Φ
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν)) :
    MeasureTheory.AEStronglyMeasurable (fun q : ℝ × β => Φ (q.1 + c, q.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν) := by
  have hmp : MeasureTheory.MeasurePreserving (fun q : ℝ × β => (q.1 + c, q.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν) :=
    ⟨measurable_fst.add_const c |>.prodMk measurable_snd, map_prod_add_fst (ν := ν) c⟩
  exact hΦ.comp_measurePreserving hmp

/-- `HasDerivAt (fun s => P (s + s₀)) c (τ - s₀)` implies `HasDerivAt P c τ` (chain rule with the
inverse translation `s ↦ s - s₀`). -/
theorem hasDerivAt_comp_sub_const {P : ℝ → ℝ} {c s₀ τ : ℝ}
    (h : HasDerivAt (fun s : ℝ => P (s + s₀)) c (τ - s₀)) : HasDerivAt P c τ := by
  have hshift : HasDerivAt (fun s : ℝ => s - s₀) 1 τ := by
    simpa using (hasDerivAt_id τ).sub_const s₀
  have h2 := h.comp τ hshift
  have hfun : ((fun s : ℝ => P (s + s₀)) ∘ fun s : ℝ => s - s₀) = P := by
    funext s
    simp only [Function.comp_apply, sub_add_cancel]
  rw [hfun, mul_one] at h2
  exact h2

/-- A limit at `τ` transfers to a limit at `τ - s₀` precomposed with `σ ↦ σ + s₀`. -/
theorem tendsto_comp_add_const_sub {F : ℝ → ℝ} {τ s₀ : ℝ}
    (h : Filter.Tendsto F (nhds τ) (nhds 0)) :
    Filter.Tendsto (fun σ : ℝ => F (σ + s₀)) (nhds (τ - s₀)) (nhds 0) := by
  have h1 : Filter.Tendsto (fun x : ℝ => x + s₀) (nhds (τ - s₀)) (nhds ((τ - s₀) + s₀)) :=
    tendsto_id.add_const s₀
  rw [sub_add_cancel] at h1
  exact h.comp h1

theorem hasDerivAt_integral_diag_var_ioo {ρ : ℝ → ℝ → ℝ} {u udot : ℝ → Work.FTS.Galerkin.Fn}
    {τ T : ℝ} (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T)
    (hρmeas : AEMeasurable (Function.uncurry ρ)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hρnn : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)), 0 ≤ ρ p.1 p.2)
    (hdiag : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hdiagd : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hmeasd : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hderiv : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s)
    (hcont : ∀ᵐ p ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)),
      ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Ioo 0 T))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ≤ K)
    (hcontU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) (nhds τ) (nhds 0)) :
    HasDerivAt (fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      (2 * ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) τ := by
  have hτ0 : 0 < τ := hτ.1
  have hτT : τ < T := hτ.2
  -- the shift of the fake time, and the smaller interval it is applied on
  set s₀ : ℝ := τ / 2 with hs₀
  have hT' : (0 : ℝ) ≤ T / 2 := by linarith
  have hτ' : τ - s₀ ∈ Set.Ioo (0 : ℝ) (T / 2) := by
    simp only [Set.mem_Ioo, hs₀]
    constructor <;> linarith
  have hmem : ∀ s ∈ Set.Icc (0 : ℝ) (T / 2), s + s₀ ∈ Set.Icc (0 : ℝ) T := by
    intro s hs
    simp only [Set.mem_Icc] at hs ⊢
    rw [hs₀]
    constructor <;> linarith
  have hsmem : ∀ s ∈ Set.Ioo (0 : ℝ) (T / 2), s + s₀ ∈ Set.Ioo (0 : ℝ) T := by
    intro s hs
    simp only [Set.mem_Ioo] at hs ⊢
    rw [hs₀]
    constructor <;> linarith
  -- the hypotheses of the `Icc`-version, shifted
  have hdiag' : ∀ s ∈ Set.Icc (0 : ℝ) (T / 2), MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u (s + s₀) p.1 p.2) ^ 2 * ρ p.1 p.2) diaM :=
    fun s hs => hdiag (s + s₀) (hmem s hs)
  have hdiagd' : ∀ s ∈ Set.Icc (0 : ℝ) (T / 2), MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot (s + s₀) p.1 p.2) ^ 2 * ρ p.1 p.2) diaM :=
    fun s hs => hdiagd (s + s₀) (hmem s hs)
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u (q.1 + s₀) q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM) :=
    aestronglyMeasurable_comp_add_fst (ν := diaM) (c := s₀) hmeas
  have hmeasd' : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => udot (q.1 + s₀) q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM) :=
    aestronglyMeasurable_comp_add_fst (ν := diaM) (c := s₀) hmeasd
  have hderiv' : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) (T / 2),
      HasDerivAt (fun t : ℝ => u (t + s₀) p.1 p.2) (udot (s + s₀) p.1 p.2) s := by
    filter_upwards [hderiv] with p hp
    intro s hs
    have h1 : HasDerivAt (fun t : ℝ => t + s₀) 1 s := by
      simpa using (hasDerivAt_id s).add_const s₀
    have h2 := (hp (s + s₀) (hsmem s hs)).comp s h1
    rw [mul_one] at h2
    exact h2
  have hcont' : ∀ᵐ p ∂diaM,
      ContinuousOn (fun s : ℝ => u (s + s₀) p.1 p.2) (Set.Icc (0 : ℝ) (T / 2)) := by
    filter_upwards [hcont] with p hp
    have hmap : Set.MapsTo (fun s : ℝ => s + s₀) (Set.Icc (0 : ℝ) (T / 2))
        (Set.Ioo (0 : ℝ) T) := by
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ioo]
      rw [hs₀]
      constructor <;> linarith
    exact hp.comp (continuous_id.add continuous_const).continuousOn hmap
  have hK' : ∃ K' : ℝ, 0 ≤ K' ∧ ∀ σ ∈ Set.Icc (0 : ℝ) (T / 2),
      ∫ p : ℝ × ℝ, (udot (σ + s₀) p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K' := by
    obtain ⟨K, hK0, hKbd⟩ := hK
    exact ⟨K, hK0, fun σ hσ => hKbd (σ + s₀) (hmem σ hσ)⟩
  have hcontU' : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
      (udot (σ + s₀) p.1 p.2 - udot ((τ - s₀) + s₀) p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM)
      (nhds (τ - s₀)) (nhds 0) := by
    refine Tendsto.congr' ?_ (tendsto_comp_add_const_sub (s₀ := s₀) hcontU)
    refine Eventually.of_forall fun σ => ?_
    simp only [sub_add_cancel]
  -- the `Icc`-version for the shifted family, on `[0, T/2]`
  have hmain : HasDerivAt
      (fun s : ℝ => ∫ p : ℝ × ℝ,
        u (s + s₀) p.1 p.2 * u (s + s₀) p.1 p.2 * ρ p.1 p.2 ∂diaM)
      (2 * ∫ p : ℝ × ℝ,
        udot ((τ - s₀) + s₀) p.1 p.2 * u ((τ - s₀) + s₀) p.1 p.2 * ρ p.1 p.2 ∂diaM)
      (τ - s₀) :=
    hasDerivAt_integral_diag_var (ρ := ρ) (u := fun s => u (s + s₀))
      (udot := fun s => udot (s + s₀)) (τ := τ - s₀) (T := T / 2)
      hT' hτ' hρmeas hρnn hdiag' hdiagd' hmeas' hmeasd' hderiv' hcont' hK' hcontU'
  -- the two ends of the shifted statement are the original ones
  have hval : 2 * (∫ p : ℝ × ℝ,
        udot ((τ - s₀) + s₀) p.1 p.2 * u ((τ - s₀) + s₀) p.1 p.2 * ρ p.1 p.2 ∂diaM)
      = 2 * (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) := by
    have h1 : (∫ p : ℝ × ℝ,
          udot ((τ - s₀) + s₀) p.1 p.2 * u ((τ - s₀) + s₀) p.1 p.2
            * ρ p.1 p.2 ∂diaM)
        = (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      simp only [sub_add_cancel]
    rw [h1]
  rw [hval] at hmain
  -- transport back along the inverse shift
  refine hasDerivAt_comp_sub_const (P := fun s : ℝ => ∫ p : ℝ × ℝ,
    u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂diaM) (s₀ := s₀) ?_
  exact hmain

end Work.FTS.StrongEps.EpsE4Thr
