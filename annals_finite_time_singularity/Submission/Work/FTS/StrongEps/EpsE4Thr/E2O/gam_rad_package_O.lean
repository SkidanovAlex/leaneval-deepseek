/-
# `gam_rad_package_O` — the *open-class* package for the separated summand `Γ(θ)·radS α f z`

This is the version of `HkMem_gam_rad` (`Transfer/E2pkg/HkMemGam.lean`) that replaces the
`CoerAdm α f` hypothesis of the coercivity chapter by the two *open-class* inputs actually
available on the `E2O` route:

* `hA : ContDiffOn ℝ 4 (fun z => L₁₂ f z) (Ioi 0)` — only the radial analytic input of
  `radS_contDiffOn_three` is needed for the `C^n` half (`n ≤ 3`);
* `hint : IntegrableOn (∑_{j≤n} (D_z^j radS α f)² w²) Iz` — the radial integrability of the
  level-`n` density, which is all the `ℋ^n` half consumes.

Both halves are then assembled exactly as in `HkMem_gam_rad`:
* the regularity from `contDiffOn_Gam_Qd` (`Γ` as a function of `θ` is `C^∞` on the quadrant)
  times the radial factor `radS α f ∘ fst`, which is `C^n` by `radS_contDiffOn_three` +
  composition + `ContDiffOn.of_le`;
* the membership `HkMem` from `LocData.HkMem_of_majorant` with the majorant
  `4·10^10 · angMaj α θ · radMaj α f n z`: the pointwise domination is the public
  `HkIntegrand_gam_rad_le` of `HkMemGam.lean` (no hypothesis on `f`), the angular factor `angMaj`
  is integrable on `Iθ` by `Spaces.sin_two_rpow` (exponents `-η` and `2α/5 - γ`, both in `(-1,0]`),
  and the `z`-integrability of `∫_θ M` is exactly `hint` after the two constant pull-outs.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.HkMemGam

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GamRadAux

open Work.FTS.CoercivityFix.Transfer.E2pkg

/-- The angular majorant `angMaj α θ = sin(2θ)^{-η} + sin(2θ)^{2α/5-γ}` is integrable on `Iθ`.
(This is the local copy of the `private` lemma `integrableOn_angMaj` of `HkMemGam.lean`.) -/
lemma integrableOn_angMaj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    IntegrableOn (fun θ : ℝ => angMaj α θ) Work.Spaces.Iθ := by
  have h1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num)
      (by rw [Work.Spaces.eta]; norm_num)).1
  have h2 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))
      Work.Spaces.Iθ := by
    refine (Work.Spaces.sin_two_rpow (2 * α / 5 - Work.Spaces.gam α) ?_ ?_).1
    · rw [Work.Spaces.gam]; linarith
    · rw [Work.Spaces.gam]; linarith
  refine (h1.add h2).congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Pi.add_apply, angMaj, Work.FTS.Nonlinear.RadialProd.smE]

end GamRadAux

open Work.FTS.CoercivityFix.Transfer.E2pkg (angMaj radMaj Qd)

theorem gam_rad_package_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ} {n : ℕ}
    (hn : n ≤ 3)
    (hA : ContDiffOn ℝ 4 (fun z => Work.Coercivity.L12f f z) (Set.Ioi 0))
    (hint : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => Work.Spaces.Gam α θ
        * Work.FTS.CoercivityFix.Transfer.radS α f z)) Work.FTS.CoercivityFix.Transfer.E2pkg.Qd ∧
      Work.Spaces.HkMem α n (fun z θ => Work.Spaces.Gam α θ
        * Work.FTS.CoercivityFix.Transfer.radS α f z) := by
  have hR : ContDiffOn ℝ 3 (fun z : ℝ => Work.FTS.CoercivityFix.Transfer.radS α f z)
      (Set.Ioi 0) :=
    Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1 hA
  have hR' : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.FTS.CoercivityFix.Transfer.radS α f p.1)
      Qd :=
    (hR.comp contDiffOn_fst (fun p hp => hp.1)).of_le (by exact_mod_cast hn)
  have hG : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Qd :=
    Work.FTS.CoercivityFix.Transfer.contDiffOn_Gam_Qd α n
  have hfun : Function.uncurry
        (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)
      = fun p : ℝ × ℝ => Work.Spaces.Gam α p.2
          * Work.FTS.CoercivityFix.Transfer.radS α f p.1 := rfl
  have hsm : ContDiffOn ℝ n (Function.uncurry
      (fun z θ => Work.Spaces.Gam α θ * Work.FTS.CoercivityFix.Transfer.radS α f z)) Qd := by
    rw [hfun]
    exact hG.mul hR'
  refine ⟨hsm, ?_⟩
  -- ### The `ℋ^n` membership, via `HkMem_of_majorant` and the majorant `M`
  have hMslice : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ : ℝ => 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
        Work.Spaces.Iθ := by
    intro z hz
    have h := MeasureTheory.Integrable.mul_const
      (GamRadAux.integrableOn_angMaj α hα hα1) (radMaj α f n z)
    exact MeasureTheory.Integrable.const_mul h (4 * 10 ^ 10)
  have hMz : IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
      Work.Spaces.Iz := by
    have h0 : IntegrableOn (fun z : ℝ => radMaj α f n z) Work.Spaces.Iz := hint
    have hconst : IntegrableOn (fun z : ℝ =>
        (4 * 10 ^ 10 * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) * radMaj α f n z)
        Work.Spaces.Iz :=
      MeasureTheory.Integrable.const_mul h0 _
    refine MeasureTheory.IntegrableOn.congr_fun hconst (fun z hz => ?_) measurableSet_Ici
    have h1 : (∫ θ in Work.Spaces.Iθ, 4 * 10 ^ 10 * (angMaj α θ * radMaj α f n z))
        = 4 * 10 ^ 10 * (∫ θ in Work.Spaces.Iθ, angMaj α θ * radMaj α f n z) :=
      MeasureTheory.integral_const_mul _ _
    have h2 : (∫ θ in Work.Spaces.Iθ, angMaj α θ * radMaj α f n z)
        = (∫ θ in Work.Spaces.Iθ, angMaj α θ) * radMaj α f n z :=
      MeasureTheory.integral_mul_const _ _
    rw [h1, h2]
    ring
  refine Work.FTS.LocData.HkMem_of_majorant α n ?_ hMslice hMz ?_
  · exact Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont
      (Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hsm) α
  · intro z hz θ hθ
    exact Work.FTS.CoercivityFix.Transfer.E2pkg.HkIntegrand_gam_rad_le α hα hα1 hn f z hz θ hθ

end Work.FTS.StrongEps.EpsE4Thr.E2O
