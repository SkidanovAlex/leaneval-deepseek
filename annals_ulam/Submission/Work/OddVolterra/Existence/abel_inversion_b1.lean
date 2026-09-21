import Mathlib
import Submission.Commons.Analysis.Abel.volterra_double_integral
import Submission.Commons.Analysis.Abel.volterra_integral_hasDerivAt

/-!
# The Abel/Volterra equivalence, easy direction, at the right endpoint `b = 1`

This module isolates the direction of the Abel/Volterra equivalence that turns the *Abel*
equation `∫_s^1 K(s,σ)/√(σ-s) dσ = Q(s)` into the *differentiated* (Volterra) form

`-∫_0^1 K(s,s)/√(τ(1-τ)) dτ + ∫_s^1 ∂₁G(s,σ) dσ = (d/ds) ∫_s^1 Q(σ)/√(σ-s) dσ`,
where `G(s,σ) = ∫_0^1 K(s+τ(σ-s),σ)/√(τ(1-τ)) dτ`.

Its point is that it needs **no** regularity of `Q` (only the Abel equation itself, i.e. `K` and
`Q` are already linked by the Abel equation), so it applies with `b = 1`, where the Abel transform
of `Q` is only continuous.  (`Commons.Analysis.Abel.volterra_equivalence*` need `Q ∈ C²` on the
*closed* interval and `Q b = 0`, which fails at `b = 1` for the odd transition-slope data of
`Work.OddVolterra`: `E₁`, `E₂` are only `C^∞` on `[0,1)` and merely continuous at `1`.)

The proof uses the double-Abel-transform identity `volterra_double_integral` (which identifies the
iterated integral of `K` with the Abel transform of the Abel transform of `K`, hence — on the
hypothesis — with the Abel transform of `Q`) and `volterra_integral_hasDerivAt` (the derivative of
that iterated integral).

For the odd transition-slope kernel of `Work.OddVolterra` the hypothesis `ContDiffOn ℝ 2 K` on the
*box* has to be produced from the kernel defined on the *triangle* `s ≤ σ`; see the remark at the
end of the file.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace Work.OddVolterra.Existence

/-- **Abel ⟹ differentiated (Volterra) form, at the endpoint `b = 1`.**

If `∫_s^1 K(s,σ)/√(σ-s) dσ = Q(s)` holds on `(a,1)`, then the differentiated form holds there
too.  No regularity of `Q` is needed beyond the identity itself. -/
theorem dvi_of_abel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha1 : a < 1) {K : ℝ → ℝ → E} {Q : ℝ → E}
    (hK : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a 1 ×ˢ Set.Icc a 1))
    (habel : ∀ s ∈ Set.Ioo a 1, (∫ σ in s..1, (Real.sqrt (σ - s))⁻¹ • K s σ) = Q s) :
    ∀ s ∈ Set.Ioo a 1,
      - (∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s) +
        (∫ σ in s..1, deriv (fun u : ℝ =>
          ∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s)
        = deriv (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) s := by
  intro s hs
  have hKcont : ContinuousOn (fun p : ℝ × ℝ => K p.1 p.2) (Set.Icc a 1 ×ˢ Set.Icc a 1) :=
    hK.continuousOn
  have hEqOn : ∀ u ∈ Set.Ioo a 1,
      (∫ σ in u..1, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ)
      = (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) := by
    intro u hu
    have hd := Commons.Analysis.Abel.volterra_double_integral (E := E) (a := a) (b := 1) ha1
      hKcont u hu
    rw [hd]
    refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hu.2) (fun x hx => ?_)
    have hx' : x ∈ Set.Ioo a 1 := ⟨lt_trans hu.1 hx.1, hx.2⟩
    rw [habel x hx']
  have hev : (fun u : ℝ => ∫ σ in u..1, ∫ τ in (0 : ℝ)..(1 : ℝ),
        (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ)
      =ᶠ[𝓝 s] (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with u hu
    exact hEqOn u hu
  have hHderiv : HasDerivAt (fun u : ℝ => ∫ σ in u..1, ∫ τ in (0 : ℝ)..(1 : ℝ),
      (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) (
      - (∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K s s) +
        (∫ σ in s..1, deriv (fun u : ℝ =>
          ∫ τ in (0 : ℝ)..(1 : ℝ), (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ • K (u + τ * (σ - u)) σ) s)) s :=
    Commons.Analysis.Abel.volterra_integral_hasDerivAt (E := E) (a := a) (b := 1) ha1 hK s hs
  rw [← hHderiv.deriv, hev.deriv_eq]

/-!
### Remark: producing the hypothesis for the odd kernel

For the odd transition-slope kernel
`K s σ := Kvec n h s σ (x σ) (y σ) (x'σ) (y'σ)` (a `Fin 2 → ℝ`-valued function) the hypothesis
`ContDiffOn ℝ 2 (uncurry K) (Icc a 1 ×ˢ Icc a 1)` is *not* satisfiable by the `if σ = s then …`
definition of `Kvec` — for `s > σ` the `else` branch is `iteratedDeriv … * √ψ` with `ψ < 0`, so
`Kvec` jumps at the diagonal and is not even continuous across it.  Two ways out:

* show that `Kvec` agrees on the *triangle* `{s ≤ σ}` with an explicit smooth expression `m`
  (`m` is the Leibniz/`ks` expansion of the swept kernel: for the `y`-branch,
  `K1(s,σ,t) = √(σ-s) · ks A (n+1/2) (n+1) s σ` with `A u σ = Ey u σ ^ (n+1/2)`), and then apply
  `dvi_of_abel` to (any `C²` extension of) `m` — the terms of the conclusion only sample the
  *triangle*, so the extension agrees with the original kernel there;
* or prove a triangle version of `volterra_integral_hasDerivAt` (the swept paths
  `(s+τ(σ-s), σ)` stay in the triangle, so only triangle regularity is used).

Both are recorded here as the missing input; see `Work.OddVolterra.Existence.volterra_rows_of_moment_eqs`.
-/

end Work.OddVolterra.Existence
