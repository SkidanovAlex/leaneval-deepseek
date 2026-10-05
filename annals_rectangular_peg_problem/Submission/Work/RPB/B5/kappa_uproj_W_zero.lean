import Mathlib
import Submission.Work.RPV.V
import Submission.Work.RPB.Defs

/-!
# `kappa_uproj_W_zero`: the chord chart on the blown-up diagonal `ρ = 0` (`C¹` version)

Let `CI` be a curve isotopy, `a` a chord-phase lift and `W` the `ρ = r²`-chart of the chord
annulus of `CI`, i.e. `W τ t (r²) = chordSurf CI.c a τ t r` for `0 < r ≤ π/2`, the chart being of
class `C¹` in `(τ,t,ρ)` on `[0,1] × ℝ × (-ρ₀,ρ₀)`.

This is the `C¹`-hypothesis version of `Work.RPB.B5.uproj_W_zero` (which assumes `C¹²`); only
continuity in `ρ` is used.

The hypothesis `hchord` constrains `W` only at the *positive* levels `ρ = r²`, but `W` is continuous
there (it is `C¹` on a set meeting the line `{(τ,t,ρ) : ρ ∈ (-ρ₀,ρ₀)}` in a neighbourhood of
`ρ = 0`), so its value on the diagonal `ρ = 0` is the limit `lim_{r→0⁺} W τ t (r²)`.

Since `uproj` of a chord `(z,w)` is `(z + w)/√2` (`Work.RPV.uproj_chordPS`), and the curve family is
continuous in `t`, that limit is `(c τ t + c τ t)/√2 = √2 · c τ t`:

`uproj (W τ t 0) = √2 · CI.c τ t`.
-/

open Complex Real
open scoped Topology ContDiff

namespace Work.RPB.B5

/-- The `ρ`-slices of a function `C¹` on `[0,1] ×ˢ univ ×ˢ (-ρ₀,ρ₀)` are continuous at `ρ = 0`,
for `τ ∈ [0,1]`.  (In the `ρ`-direction the domain is a neighbourhood of the point.) -/
private lemma contAt_slice_one {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {ρ₀ : ℝ}
    (hρ₀ : 0 < ρ₀) {f : ℝ × (ℝ × ℝ) → Y}
    (hf : ContDiffOn ℝ 1 f (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) 1) (t : ℝ) :
    ContinuousAt (fun ρ : ℝ => f (τ, (t, ρ))) 0 := by
  have hφ : ContDiffOn ℝ 1 (fun ρ : ℝ => (τ, (t, ρ))) (Set.Ioo (-ρ₀) ρ₀) :=
    (by fun_prop : ContDiff ℝ 1 (fun ρ : ℝ => (τ, (t, ρ)))).contDiffOn
  have hst : Set.MapsTo (fun ρ : ℝ => (τ, (t, ρ))) (Set.Ioo (-ρ₀) ρ₀)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀) := by
    intro ρ hρ; exact ⟨hτ, Set.mem_univ _, hρ⟩
  exact (hf.comp hφ hst).continuousOn.continuousAt (Ioo_mem_nhds (by linarith) hρ₀)

/-- `(x + x)/√2 = √2 · x` over `ℂ`. -/
private lemma two_div_sqrt_two (x : ℂ) :
    (x + x) / (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) * x := by
  have hs2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hs0 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hs2; norm_num at hs2
  rw [div_eq_iff hs0]
  rw [mul_comm (Real.sqrt 2 : ℂ) x, mul_assoc, hs2]
  ring

/-- The reduced coordinate `uproj` is continuous. -/
private lemma continuous_uproj_PS : Continuous Work.RPV.uproj := by
  show Continuous fun x : Work.RPV.PS => Complex.exp (x.1.2 * I) * (x.2.1 + x.1.1 * I)
  fun_prop

theorem kappa_uproj_W_zero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {W : ℝ → ℝ → ℝ → Work.RPV.PS}
    (hW : ContDiffOn ℝ 1 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      Work.RPV.uproj (W τ t 0) = (Real.sqrt 2 : ℂ) * CI.c τ t := by
  intro τ hτ t
  -- The chart is continuous in `ρ` at `ρ = 0`, for `τ ∈ [0,1]`.
  have hslice : ContinuousAt (fun ρ : ℝ => W τ t ρ) 0 := contAt_slice_one hρ₀ hW hτ t
  -- Hence `uproj (W τ t (r²)) → uproj (W τ t 0)` as `r → 0⁺`.
  have h1 : Filter.Tendsto (fun r : ℝ => Work.RPV.uproj (W τ t (r ^ 2))) (𝓝[>] 0)
      (𝓝 (Work.RPV.uproj (W τ t 0))) := by
    have hr2 : Filter.Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_pow 2).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    exact (continuous_uproj_PS.tendsto (W τ t 0)).comp (hslice.tendsto.comp hr2)
  -- The curve family is continuous in the parameter.
  have hcτ : Continuous (fun s : ℝ => CI.c τ s) :=
    CI.smooth.continuous.comp (continuous_const.prodMk continuous_id)
  have hgcont : ContinuousAt
      (fun r : ℝ => (CI.c τ (t + r) + CI.c τ (t - r)) / (Real.sqrt 2 : ℂ)) 0 :=
    (((hcτ.comp (continuous_const.add continuous_id)).add
      (hcτ.comp (continuous_const.sub continuous_id))).continuousAt).div_const _
  -- ... so `(c τ (t+r) + c τ (t-r))/√2 → (c τ t + c τ t)/√2 = √2 c τ t` as `r → 0⁺`.
  have hg : Filter.Tendsto (fun r : ℝ => (CI.c τ (t + r) + CI.c τ (t - r)) / (Real.sqrt 2 : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.sqrt 2 : ℂ) * CI.c τ t)) := by
    have h := hgcont.tendsto.mono_left (nhdsWithin_le_nhds : (𝓝[>] (0:ℝ)) ≤ 𝓝 (0:ℝ))
    simpa only [add_zero, sub_zero, two_div_sqrt_two] using h
  -- The chord identification holds for every `r ∈ (0, π/2]`, hence eventually near `0⁺`.
  have hmem : Set.Ioc (0:ℝ) (Real.pi / 2) ∈ 𝓝[>] (0:ℝ) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT (show (0:ℝ) < Real.pi/2 by positivity))
      (fun x hx => ⟨hx.1, hx.2.le⟩)
  have heq : (fun r : ℝ => Work.RPV.uproj (W τ t (r ^ 2))) =ᶠ[𝓝[>] 0]
      (fun r : ℝ => (CI.c τ (t + r) + CI.c τ (t - r)) / (Real.sqrt 2 : ℂ)) := by
    filter_upwards [hmem] with r hr
    obtain ⟨hr0, hrle⟩ := hr
    rw [hchord τ hτ t r ⟨hr0, hrle⟩, Work.RPB.chordSurf]
    exact Work.RPV.uproj_chordPS _ _ _
  have h2 : Filter.Tendsto (fun r : ℝ => Work.RPV.uproj (W τ t (r ^ 2))) (𝓝[>] 0)
      (𝓝 ((Real.sqrt 2 : ℂ) * CI.c τ t)) := Filter.Tendsto.congr' heq.symm hg
  -- Two limits of the same function along a nontrivial filter coincide.
  exact tendsto_nhds_unique h1 h2

end Work.RPB.B5
