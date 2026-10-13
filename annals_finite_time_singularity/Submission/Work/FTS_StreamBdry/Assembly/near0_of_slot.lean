import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.sb1_gauge_proved
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_DzLe
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_RegExport.RXT.Slots.v2_velPert
import Submission.Work.FTS_RegExport.RXT.Slots.v2_starUop
import Submission.Work.FTS_RegExport.RXT.starVop
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_StreamBdry.SB4.near0Core
import Submission.Work.FTS_StreamBdry.SB4.Epart_dz_bound
import Submission.Work.FTS_StreamBdry.SB4.Thetapart_dz_bound
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.Assembly.near0_of_slot` — the near-origin bound for the SB4 producer

For the canonical slice `Ψ = slice (PsiCan Φs E g) τ` of the strong route, the `U`-slot part
`psiP αG Ψ` of the stream function satisfies

`|D_z(psiP αG Ψ)(z,θ)| ≤ K · z · sin 2θ`   for `(z,θ)` in the open quadrant, `z ≤ 1`,

which is what `SB6.rates` needs (`sb6_rates` consumes exactly this `∃K` statement).

## The argument

Write `αG = pExp a = 3a ∈ (0,1]`, `f = slice g τ`.  By the *definitions*
`PhiTs αG Φs = Φs - Θ(F_*)` and `PhiTil αG f (E f) = E f - Θ(f)`, so the slice splits
*algebraically* as

`Ψ = Φ̃_* + Θ(F_*) + Φ̃_E + Θ(f)`,   `Φ̃_* = PhiTs αG Φs`,  `Φ̃_E = PhiTil αG f (E f)`.

The `U`-slot `U'(X) = Uop αG X / sin 2θ` is additive over this splitting, and each summand's
`U'` is Lipschitz in `z` on `(0,1]`, uniformly in `θ`:

* `Φ̃_*`: `((z+1)/z)·U'(Φ̃_*) ∈ 𝒲^{4,∞}` (`StarPkgo2.UszW` through `RXT.starUop`);
* `Θ(F_*)`: explicit, `U'(Θ(F_*)) = -3/(2(1+z)) + αG z/(2(1+z)²)`, Lipschitz constant `2`;
* `Φ̃_E`: from the `ℋ⁴`-slot of `E` on the class-`C` approximants of `LimApprox`;
* `Θ(f)`: from the `L₁₂`/`Qang` estimates of `RegPkg'` (the quotient is *radial*).

`psiP αG Ψ = -(s2θ/αG)∫₀¹ v^{3/αG-1}U'(Ψ)(zv,θ)dv` then inherits the Lipschitz constant
`s2θ·C/(3+αG)`, `abs_deriv_le_of_lipschitzOn_Ioc` bounds `|∂_z psiP|` by it, and the factor `z`
comes from `D_z = z·∂_z`.

## Where each piece lives

The pieces of this argument are worked out in `...SB4.near0Aux` (the fragmentary radial Lipschitz
bounds), `...SB4.Epart_dz_bound` / `...SB4.Thetapart_dz_bound` (the `D_z`-bounds of the elliptic
and `Θ(f)` summands), `...SB4.slice_L12_c2` (the `C²`-regularity of `z ↦ L₁₂(slice g τ)(z)`),
`...SB4.psiP_lipschitz` and `...SB4.abs_deriv_le_of_lipschitzOn_Ioc`; `...SB4.near0Core`
(`near0_core`) is their assembly into the statement of this theorem, and the three producers
below instantiate its remaining hypotheses.
-/

namespace Work.FTS_StreamBdry.Assembly

theorem near0_of_slot {a C₀ Ce Cs : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp a) u →
      Work.FTS.VocabO.EllPkgGo (Work.FTS.Regularity.pExp a) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp a) 6 Ce u (E u))
    (hEL : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp a) E)
    (hStar : Work.FTS.VocabO2.StarPkgo2 (Work.FTS.Regularity.pExp a) Cs Φs)
    {g G : Work.FTS.Galerkin.Fam} {A B : ℝ → ℝ}
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp a) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp a) C₀ Φs E g)
    (hreg : ∀ S : ℝ, 0 < S →
      Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP (Work.FTS.Regularity.pExp a)
        (Work.FTS.Galerkin.slice (Work.FTS.Nonlin.PsiCan Φs E g) τ)) z θ|
        ≤ K * z * Work.Construction.s2 θ := by
  intro τ hτ
  refine Work.FTS_StreamBdry.SB4.near0_core (Φs := Φs) (E := E) (g := g)
    ha ha13 hStar hEL hOK ?_ ?_ ?_ τ hτ
  · -- `C²`-regularity of the `L₁₂`-tail of the slice
    intro τ' hτ' z hz
    exact Work.FTS_StreamBdry.SB4.slice_L12_c2 ha ha13 hOK τ' hτ' z hz
  · -- the `D_z`-bound for the elliptic summand `PhiTil αG f (E f)`
    intro τ' hτ'
    obtain ⟨K, hK0, hKb⟩ := Work.FTS_StreamBdry.SB4.Epart_dz_bound (C₀ := C₀) (Ce := Ce)
      ha ha13 hEll hEL hOK τ' hτ'
    exact ⟨K, hK0, fun z θ hzθ hz1 => by
      simpa only [Work.FTS.StreamBdryIface.Uprime] using hKb z θ hzθ hz1⟩
  · -- the `D_z`-bound for the `Θ`-summand `Theta αG f`
    intro τ' hτ'
    obtain ⟨K, hK0, hKb⟩ := Work.FTS_StreamBdry.SB4.Thetapart_dz_bound (C₀ := C₀)
      ha ha13 hOK hreg hG τ' hτ'
    exact ⟨K, hK0, fun z θ hzθ hz1 => by
      simpa only [Work.FTS.StreamBdryIface.Uprime] using hKb z θ hzθ hz1⟩

end Work.FTS_StreamBdry.Assembly
