import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.FTS_RegExport.RX0.sup2_extG_ext_hIS
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXT.omega_facts
import Submission.Work.R1G.DecayInZ_gA
-- ===== merged: Submission.Work.FTS_RegExport.RXR7.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false

variable {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
  {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}

/-- The sanitised right-Taylor family `gS α (tauExt g)`. -/
abbrev GR (α : ℝ) (g : Work.FTS.Galerkin.Fam) : Work.FTS.Galerkin.Fam :=
  Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)

/-- The stream function `psiR α Φs E (tauExt g)` fed to R7. -/
abbrev ΦR (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    Work.FTS.Galerkin.Fam :=
  Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)

/-- The clock `maxMu (pExp α) (PsiCan Φs E g) g` of the coefficients. -/
abbrev μR (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ :=
  Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g

/-- `Vz7` at the sanitised family (`= RXT.VR`). -/
abbrev Vz7R (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α) (μR α Φs E g) (GR α g)
    (ΦR α Φs E g)

/-- `Vθ7` at the sanitised family. -/
abbrev Vθ7R (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α) (ΦR α Φs E g)

/-- `cs7` at the sanitised family (`= RXT.cR`). -/
abbrev cs7R (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegExportIface.cs7 (Work.FTS.Regularity.pExp α) (μR α Φs E g) (GR α g)
    (ΦR α Φs E g)

/-- The full profile of the R7 block: `profFull α (extG (GR α g))`. -/
abbrev Prof (α : ℝ) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG (GR α g)) z θ τ

/-- The closed-form right-hand side `Vz7ᵣ·D_z(Prof) + Vθ7ᵣ·∂_θ(Prof) + cs7ᵣ·Prof` of the
transport form of the profile equation (negated in `R7Block.hEq`). -/
abbrev K7 (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) :
    ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ =>
    Vz7R α Φs E g z θ τ * Work.Spaces.Dz (fun z θ => Prof α g z θ τ) z θ
      + Vθ7R α Φs E g z θ τ * Work.Spaces.pth (fun z θ => Prof α g z θ τ) z θ
      + cs7R α Φs E g z θ τ * Prof α g z θ τ

/-- The slab `(0,∞) × (0,π/2) × [0,S]` of `R7Block.hFjoint`/`hVjoint`/`hcscont`. -/
abbrev R7Slab (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.prod (Set.Ioi (0 : ℝ))
    (Set.prod (Set.Ioo (0 : ℝ) (Real.pi / 2)) (Set.Icc (0 : ℝ) S))

end Work.FTS_RegExport.RXR7
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.C2Assemble =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.C2Assemble` — elementary smoothness of the transport coefficients

The pointwise (in `(z,θ) ∈ Q0`) assembly steps of S4 (`coeff_C2`): once the stream function
`slice (psiR α Φs E (tauExt g)) τ` is `C³` on the open quadrant and the two radial functions
`L₁₂(F(τ))`, `𝔽K(F(τ))` are `C²`/`C³` on `(0,∞)`, the three coefficients `Vz7`, `Vθ7`, `cs7`
of `(E)` are `C²` there.

Nothing here uses the elliptic theory: these are the `ContDiffOn`-calculus lemmas.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## `sin 2θ`, `cos θ` and `tan` on the open quadrant -/

theorem sin_two_pos_Q0 {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [h.2.1]) (by linarith [h.2.2, Real.pi_pos])

theorem cos_pos_Q0 {z θ : ℝ} (h : (z, θ) ∈ Work.FTS.EllipticEst.Q0) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.2.1, Real.pi_pos], by linarith [h.2.2, Real.pi_pos]⟩

theorem contDiffOn_tan_Q0 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.tan p.2)
    Work.FTS.EllipticEst.Q0 := by
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn
  have hcos : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn
  refine (hsin.div hcos (fun p hp => ne_of_gt (cos_pos_Q0 hp))).congr ?_
  intro p _
  exact Real.tan_eq_sin_div_cos p.2

/-! ## The partial derivatives lower the order -/

theorem contDiffOn_uncurry_pz {F : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz F)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pz_fin Work.FTS.EllipticEst.isOpen_Q0 h

theorem contDiffOn_uncurry_pth {F : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth F)) Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongEps.contDiffOn_uncurry_pth_fin Work.FTS.EllipticEst.isOpen_Q0 h

/-- `C³` is in particular `C²`. -/
theorem cd2_of_cd3 {F : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 3 (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0 :=
  h.of_le (by norm_num)

/-! ## The coefficients `Uop`, `Vop`, `Rop` of an open-quadrant-`C³` stream function -/

theorem contDiffOn_uncurry_Uop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Uop α Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pz hΨ
  have h2 := cd2_of_cd3 hΨ
  have h3 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => α * p.1 * Work.Spaces.pz Ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 :=
    ((contDiffOn_const (c := α)).mul contDiffOn_fst).mul hpz
  refine (((contDiffOn_const (c := (-3 : ℝ))).mul h2).sub h3).congr ?_
  intro p _
  simp only [Function.uncurry, Work.Construction.Uop]

theorem contDiffOn_uncurry_Vop {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Vop Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hpth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pth hΨ
  have h2 := cd2_of_cd3 hΨ
  exact hpth.sub (contDiffOn_tan_Q0.mul h2)

theorem contDiffOn_uncurry_Rop {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Construction.Rop α Ψ)) Work.FTS.EllipticEst.Q0 := by
  have hpz : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pz hΨ
  have hpth : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) Work.FTS.EllipticEst.Q0 :=
    contDiffOn_uncurry_pth hΨ
  have h2 := cd2_of_cd3 hΨ
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_sin.comp_contDiffOn contDiff_snd.contDiffOn
  have hcos : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.cos p.2) Work.FTS.EllipticEst.Q0 :=
    Real.contDiff_cos.comp_contDiffOn contDiff_snd.contDiffOn
  have hn : ContDiffOn ℝ 2 (fun p : ℝ × ℝ =>
      (2 * Real.sin p.2 * Ψ p.1 p.2 + α * Real.sin p.2 * p.1 * Work.Spaces.pz Ψ p.1 p.2
        + Real.cos p.2 * Work.Spaces.pth Ψ p.1 p.2)) Work.FTS.EllipticEst.Q0 :=
    ((((contDiffOn_const (c := (2 : ℝ))).mul hsin).mul h2).add
      ((((contDiffOn_const (c := α)).mul hsin).mul contDiffOn_fst).mul hpz)).add
        (hcos.mul hpth)
  refine (hn.div hcos (fun p hp => ne_of_gt (cos_pos_Q0 hp))).congr ?_
  intro p _
  simp only [Pi.div_apply, Function.uncurry, Work.Construction.Rop]

/-! ## Division by `sin (2θ)` and radial/angular products -/

theorem contDiffOn_uncurry_div_sin_two {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) Work.FTS.EllipticEst.Q0) :
    ContDiffOn ℝ 2 (Function.uncurry (fun z θ => F z θ / Real.sin (2 * θ)))
      Work.FTS.EllipticEst.Q0 := by
  have hsin : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hF.div hsin (fun p hp => ne_of_gt (sin_two_pos_Q0 hp))



end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.CoeffJetsDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.CoeffJets` — the *true* coefficient package of RX-VP

The frozen `RegExportIface.VelPkg` (and its split `Work.FTS_RegExport.VelPkgSup`) carry three
clauses whose angular quantifier is the **closed** interval `Iθ = Icc 0 (π/2)`:

* `bnd` (`|Vz7| ≤ M`, `|Vθ7| ≤ M sin 2θ`, `|cs7| ≤ M` for `θ ∈ Iθ`),
* `vz0` (`0 ≤ Vz7` for `θ ∈ Iθ`),
* `cont` (joint continuity on `Ioi 0 ×ˢ Icc 0 (π/2) ×ˢ Icc 0 S`),

and they are **false** for the constructed profile: `Vz7` is discontinuous at `θ = π/2`
(`RXVP2/NOTES_velPkgSup_FALSE.md`, machine-checked `not_continuousOn_Vz7`; the defect is
`Real.tan (π/2) = 0` inside `Vop`) and `vz0` fails there too for `α > 1/4`.  The clause `axis`
of `VelPkg` is false as well (`RXVP/NOTES_velPkgEnd_axis_FALSE.md`).

Every *consumer* on the RX-St1 path quantifies over the **open** interval `0 < θ < π/2`
(`R7Block.hVz0/hVza/hVθb/hcsc`, and the leaf statements S5b/S5c/S6 of
`RegExportIface/RXT/Leaves.lean`), and the open-θ clauses are not affected by the `tan (π/2)`
artefact.  This file therefore fixes the package in the only place that matters:

* `dbnd` — the order-≤2 mixed jets of the three coefficient slices (open `θ`), verbatim from
  the frozen `dbnd`;
* `cont` — τ-continuity of the three coefficient slices at a fixed point of the open quadrant.

`CoeffJets` is what S5b/S5c/S6 and the assembly of S8 (`weighted_system`) actually consume;
it is implied by any open-θ repair of `VelPkgSup`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7)

set_option autoImplicit false

/-- **The coefficient package actually consumed by the RX-St1 chain** (open angular interval):
the order-≤2 jet bounds `dbnd` of the frozen `VelPkg`, plus τ-continuity of the three coefficient
slices at each point of the open quadrant. -/
structure CoeffJets (αG : ℝ) (μ : ℝ → ℝ) (G Φ : Fam) (S : ℝ) : Prop where
  /-- order-≤2 mixed jets of `Vz7`, `Vθ7/sin 2θ`, `cs7` and of `∂_θVz7` (open `θ`) -/
  dbnd : ∃ M : ℝ, ∀ τ ∈ Icc (0:ℝ) S, ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ, 0 < z → 0 < θ →
    θ < π / 2 →
    |Work.Spaces.mixed j i (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => Vθ7 αG Φ z θ τ / Real.sin (2 * θ)) z θ| ≤ M ∧
    |Work.Spaces.mixed j i (fun z θ => cs7 αG μ G Φ z θ τ) z θ| ≤ M ∧
    |Work.Spaces.pth (fun z θ => Vz7 αG μ G Φ z θ τ) z θ| ≤ M
  /-- τ-continuity of the three coefficient slices at a fixed point of the open quadrant -/
  cont : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    ContinuousOn (fun τ => (Vz7 αG μ G Φ z θ τ, Vθ7 αG Φ z θ τ / Real.sin (2 * θ),
      cs7 αG μ G Φ z θ τ)) (Icc 0 S)

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.MixedUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.MixedUniform` — uniform interior bounds for the slices of `g`

The class-`C` interior `L^∞`–`ℋ⁴` trade-off of Elgindi's Corollary `SecondDerivativesBounded`
(`Work.FTS.StrongEps.SupPort.classC_mixed_sup_le`) applied to the approximating sequence of
`LimApprox` and passed to the limit: every mixed slot of order `≤ 2` of `slice g τ` is bounded
on the open quadrant by `10/√(γ-1) · (C₀ α²)`, uniformly in `τ ∈ [0,T]` and in `(z,θ) ∈ Q0`.

This is the `(b,a)`-uniform form of RX-A2 (`lim_mixed_bounds_proved`) that the domination
arguments for the angular parametric integrals of `coeff_C2` need.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.FinalV2 (LimApprox)

set_option autoImplicit false

/-- **Uniform mixed-slot bounds of the slices of `g`.**  From the `LimApprox` clause of
`DynOK'` (class-`C` approximants with `ℋ⁴`-bounds and jet convergence) and the class-`C`
interior trade-off `classC_mixed_sup_le`. -/
theorem mixed_uniform {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hA : LimApprox α C₀ Φs E g) (T : ℝ) (hT : 0 < T) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed b a (slice g τ) z θ|
        ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
  intro τ hτ b a hab z θ hzθ
  obtain ⟨gn, B, L, hC, -, hjet, -⟩ := hA T hT
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by
    rw [Work.Spaces.gam_sub_one]; linarith
  have hK : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have h1 : ∀ n : ℕ, |Work.Spaces.mixed b a (slice (gn n) τ) z θ|
      ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
    intro n
    refine le_trans (Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1
      (hC n τ hτ).1 b a hab hzθ) ?_
    exact mul_le_mul_of_nonneg_left (hC n τ hτ).2.1 hK
  have h2 : Tendsto (fun n : ℕ => |Work.Spaces.mixed b a (slice (gn n) τ) z θ|) atTop
      (𝓝 |Work.Spaces.mixed b a (slice g τ) z θ|) :=
    (hjet τ hτ b a (by omega) z θ hzθ).abs
  exact le_of_tendsto h2 (Eventually.of_forall h1)

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.abs_mixed_gdot_le_of_GdotLoc =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-- Pointwise (in `(z,θ)`) uniform-in-`σ` bound for a single mixed jet of `∂_τ g`, extracted from
the local bounds packaged in `GdotLoc S g`.  In `GdotLoc` the bounds are stated on compact boxes
`Icc a b × Icc c d` with `a > 0` and `d < π/2`; instantiating the box at the *single point*
`(z,θ)` (i.e. `a = b = z`, `c = d = θ`) gives the bound at that point, uniformly for
`σ ∈ Ioc 0 S`.  The constant is clamped to `≥ 0` (harmless: a bound on a nonempty range already
forces nonnegativity, and the vacuous case `Ioc 0 S = ∅` admits `C = 0`). -/
theorem abs_mixed_gdot_le_of_GdotLoc {S : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hG : Work.FTS.RegExportIface.RXT.GdotLoc S g) {j i : ℕ} (hji : j + i ≤ 2)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Ioc (0 : ℝ) S,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) z θ| ≤ C := by
  -- the degenerate box `[z,z] × [θ,θ]`: all side conditions of `GdotLoc` are immediate
  obtain ⟨C₀, hC₀⟩ := hG.2 z z θ θ hz le_rfl hθ0 le_rfl hθ1
  refine ⟨max 0 C₀, le_max_left 0 C₀, fun σ hσ => ?_⟩
  have hz' : z ∈ Set.Icc z z := Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  have hθ' : θ ∈ Set.Icc θ θ := Set.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  exact le_trans ((hC₀ σ hσ z hz' θ hθ').1 j i hji) (le_max_right 0 C₀)

end Work.FTS_RegExport.RXT.Sys
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.SysAux.muR_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

/-- `|a - b - c| ≤ |a| + |b| + |c|` (elementary, used to split the defining identity of `Vz7`). -/
private lemma abs_sub_sub_le (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 : |a - b - c| ≤ |a - b| + |c| := by
    have := abs_add_le (a - b) (-c)
    simpa [sub_eq_add_neg] using this
  have h2 : |a - b| ≤ |a| + |b| := by
    have := abs_add_le a (-b)
    simpa [sub_eq_add_neg] using this
  linarith [abs_nonneg c]

/-- `Vz7` is affine in the clock `μ`:  `Vz7 α μ G Φ z θ τ = (1 - μ τ) + L12(τ) z * c2m θ
+ 2α * Vop(Φ̃(τ)) z θ`.  Hence a uniform sup bound on `Vz7` together with the uniform bound on
`L12` and the `O(z)`-vanishing bound on `Vop` bounds `μ` on `[0, S]`: evaluate at `z = 1`,
`θ = π/4`, where every term other than `μ` is controlled by a constant that does not depend
on `τ`. -/
theorem muR_bound {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hVz : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.μR α Φs E g)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g)
        z θ σ| ≤ M)
    (hVop : ∃ M : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
        z θ| ≤ M * min z 1)
    (hL12b : ∃ C : ℝ, ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 < z →
      |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) z| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Set.Icc (0:ℝ) S,
      |Work.FTS.RegExportIface.RXT.μR α Φs E g σ| ≤ C := by
  obtain ⟨M, hM⟩ := hVz
  obtain ⟨M₂, hM₂⟩ := hVop
  obtain ⟨C₁, hC₁⟩ := hL12b
  refine ⟨|M| + |C₁| * |Work.Construction.c2m (Real.pi / 4)|
    + 2 * |Work.FTS.Regularity.pExp α| * |M₂| + 1, by positivity, ?_⟩
  intro σ hσ
  have hpi : 0 < Real.pi := Real.pi_pos
  have hz : (0 : ℝ) < 1 := one_pos
  have hθ0 : (0 : ℝ) < Real.pi / 4 := by linarith
  have hθ1 : Real.pi / 4 < Real.pi / 2 := by linarith
  have h1 := hM σ hσ 1 (Real.pi / 4) hz hθ0 hθ1
  have h2 := hM₂ σ hσ 1 (Real.pi / 4) hz hθ0 hθ1
  have h3 := hC₁ σ hσ 1 hz
  simp only [min_self, mul_one] at h2
  -- the defining identity of `Vz7` at `(z, θ) = (1, π/4)`
  have hdec : (1 : ℝ) - Work.FTS.RegExportIface.RXT.μR α Φs E g σ
      = Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.μR α Φs E g)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g)
          1 (Real.pi / 4) σ
        - (Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) σ) 1 * Work.Construction.c2m (Real.pi / 4))
        - (2 * Work.FTS.Regularity.pExp α
            * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
              (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
              1 (Real.pi / 4)) := by
    unfold Work.FTS.RegExportIface.Vz7
    ring
  have hmain : |1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ|
      ≤ |M| + |C₁| * |Work.Construction.c2m (Real.pi / 4)|
        + 2 * |Work.FTS.Regularity.pExp α| * |M₂| := by
    have hT : |Work.FTS.RegExportIface.Vz7 (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.μR α Φs E g)
        (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g)
        1 (Real.pi / 4) σ| ≤ |M| := le_trans h1 (le_abs_self M)
    have hL : |Work.Construction.L12 (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.RXT.GR α g) σ) 1 * Work.Construction.c2m (Real.pi / 4)|
        ≤ |C₁| * |Work.Construction.c2m (Real.pi / 4)| := by
      rw [abs_mul]
      exact le_trans (mul_le_mul_of_nonneg_right h3 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (le_abs_self C₁) (abs_nonneg _))
    have hV : |2 * Work.FTS.Regularity.pExp α
        * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) (Work.FTS.RegExportIface.RXT.ΦR α Φs E g) σ)
          1 (Real.pi / 4)| ≤ 2 * |Work.FTS.Regularity.pExp α| * |M₂| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (le_trans h2 (le_abs_self M₂)) (by positivity)
    rw [hdec]
    refine le_trans (abs_sub_sub_le _ _ _) ?_
    linarith
  have habs : |Work.FTS.RegExportIface.RXT.μR α Φs E g σ|
      ≤ |1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ| + 1 := by
    have hsplit : Work.FTS.RegExportIface.RXT.μR α Φs E g σ
        = (Work.FTS.RegExportIface.RXT.μR α Φs E g σ - 1) + 1 := by ring
    calc |Work.FTS.RegExportIface.RXT.μR α Φs E g σ|
        = |(Work.FTS.RegExportIface.RXT.μR α Φs E g σ - 1) + 1| :=
            congrArg (fun x : ℝ => |x|) hsplit
      _ ≤ |Work.FTS.RegExportIface.RXT.μR α Φs E g σ - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ = |1 - Work.FTS.RegExportIface.RXT.μR α Φs E g σ| + 1 := by
            rw [abs_sub_comm, abs_one]
  linarith

end Work.FTS_RegExport.RXT.SysAux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.loc_sup4 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.loc_sup4` — the local `C⁴` sup bound of the strong solution (S1)

For a family `g` satisfying `DynOK' (pExp α) C₀ Φs E g` and any box `[a,b] × [c,d]` with
`0 < a`, `0 < c`, `d < π/2` inside the open quadrant, the mixed derivatives
`D_z^jD_θ^i (slice g τ)` of order `j + i ≤ 4` are uniformly bounded on `[0,T] × [a,b] × [c,d]`.

The proof is the plan of `sources/ftsV2/fts_rxt_leafplans.md` (S1):

* `DynOK'` gives `DynOK` and `LimApprox`; evaluating the latter at the horizon `T + 1` produces the
  class-C approximants `gn`, the uniform `ℋ⁶`-bound `Xn6 α (slice (gn n) τ) ≤ B` and the
  convergence of every jet of order `≤ 4` on `Qd`;
* a class-`C` slice is `SmoothOpen` and `HkMem` at level `6`, so the interior `L^∞`–`ℋ⁶` trade-off
  `StrongEps.classC_mixed_sup_le_four` bounds each mixed slot of order `≤ 4` at a point of `Qd` by
  a constant (depending only on the box and on `γ - 1`) times `Xn6`;
* the box lies in `Qd`, so the limit is taken with `le_of_tendsto`.

Note the constant may depend on the box (the `L^∞`–`ℋ⁶` constant does), which is exactly what the
statement allows.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

theorem loc_sup4 {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (T : ℝ) (hT : 0 < T) {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (hd : d < π / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) T, ∀ j i : ℕ, j + i ≤ 4 →
      ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc c d,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice g τ) z θ| ≤ C := by
  -- the exponent `β = pExp α = 3α` is a positive exponent `≤ 1`
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  -- the class-`C` interior `L^∞`–`ℋ⁶` trade-off
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  have hC₁nn : 0 ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) :=
    div_nonneg hC₁pos.le (Real.sqrt_nonneg _)
  -- the approximating class-C families, the uniform `ℋ⁶`-bound `B`, and the jet convergence
  obtain ⟨gn, B, _L, h1, _h2, h3, _h4⟩ := hOK.2 (T + 1) (by linarith)
  have hBnn : 0 ≤ B := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨le_rfl, by linarith⟩
    have hx : 0 ≤ Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn 0) 0) := Work.Spaces.HkNorm_nonneg _ 6 _
    linarith [(h1 0 0 h0).2.2]
  refine ⟨C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B,
    mul_nonneg hC₁nn hBnn, ?_⟩
  intro τ hτ j i hji z hz θ hθ
  -- the box sits inside the open quadrant, and `τ` inside the horizon `T + 1`
  have hzpos : 0 < z := lt_of_lt_of_le ha hz.1
  have hθpos : 0 < θ := lt_of_lt_of_le hc hθ.1
  have hθlt : θ < π / 2 := lt_of_le_of_lt hθ.2 hd
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hzpos, hθpos, hθlt⟩
  have hτT : τ ∈ Set.Icc (0 : ℝ) (T + 1) := ⟨hτ.1, by linarith [hτ.2]⟩
  -- every approximant satisfies the class-C bound at `(z,θ)`
  have hbound : ∀ n : ℕ,
      |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B := by
    intro n
    have hcn : Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) := (h1 n τ hτT).1
    have hx6 : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
        (Work.FTS.Galerkin.slice (gn n) τ) ≤ B := (h1 n τ hτT).2.2
    have hb := hC₁ (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ hcn j i (by omega) hzθ
    calc |Work.Spaces.mixed j i (Work.FTS.Galerkin.slice (gn n) τ) z θ|
        ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
            * Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α)
              (Work.FTS.Galerkin.slice (gn n) τ) := hb
      _ ≤ C₁ / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * B :=
          mul_le_mul_of_nonneg_left hx6 hC₁nn
  -- pass to the limit along the jets of order `≤ 4`
  exact le_of_tendsto (h3 τ hτT j i hji z θ hzθ).abs (Filter.Eventually.of_forall hbound)

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.st1_prelim =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_RegExport.RXT

/-! ## §1 The exported family and its elementary properties -/

/-- The sanitised, right-Taylor-extended family `gS α (tauExt g)`, extended to `z ≤ 0` by `0`. -/
abbrev GG (α : ℝ) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ → ℝ → ℝ :=
  Work.FTS.RegPkgGal.extG (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))

/-- `GG` agrees with the slice of `g` on `z > 0`, `θ ∈ Iθ`, `τ ≥ 0`. -/
theorem GG_of_mem (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    GG α g z θ τ = Work.FTS.Galerkin.slice g τ z θ := by
  rw [GG, Work.FTS.FinalV2.extG_gS_of_mem α (Work.FTS.FinalV2.tauExt g) hθ.1 hθ.2,
    Work.FTS.RegPkgGal.extG_of_pos hz hτ]
  exact Work.FTS.FinalV2.tauExt_of_nonneg g hτ

/-- `GG` vanishes for `z ≤ 0`. -/
theorem GG_of_nonpos (α : ℝ) {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ} (hz : z ≤ 0) :
    GG α g z θ τ = 0 := by
  simp only [GG, Work.FTS.RegPkgGal.extG_of_nonpos hz]

/-- `deriv F 0 = 0` if `F` vanishes on `(-∞,0]`. -/
theorem deriv_eq_zero_of_eq_zero_of_nonpos {F : ℝ → ℝ} (h : ∀ x : ℝ, x ≤ 0 → F x = 0) :
    deriv F 0 = 0 := by
  by_cases hd : DifferentiableAt ℝ F 0
  · have h1 : Tendsto (fun t : ℝ => t⁻¹ * (F t - F 0)) (𝓝[≠] (0:ℝ)) (𝓝 (deriv F 0)) := by
      simpa only [zero_add, smul_eq_mul] using hd.hasDerivAt.tendsto_slope_zero
    have h2 : Tendsto (fun t : ℝ => t⁻¹ * (F t - F 0)) (𝓝[<] (0:ℝ)) (𝓝 (deriv F 0)) :=
      h1.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_lt hx))
    have h3 : (fun _ : ℝ => (0:ℝ)) =ᶠ[𝓝[<] (0:ℝ)]
        (fun t : ℝ => t⁻¹ * (F t - F 0)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [h t ht.le, h 0 le_rfl, sub_zero, mul_zero]
    have h5 : Tendsto (fun t : ℝ => t⁻¹ * (F t - F 0)) (𝓝[<] (0:ℝ)) (𝓝 (0:ℝ)) :=
      Tendsto.congr' h3 tendsto_const_nhds
    exact tendsto_nhds_unique h2 h5
  · exact deriv_zero_of_not_differentiableAt hd

/-! ## §2 The angular factor `Γ`, the weight `ω` -/

/-- `Γ(0) = 0` for `α > 0`. -/
theorem Gamma_zero_left {α : ℝ} (hα : 0 < α) : Work.FTS.Regularity.Gamma α 0 = 0 := by
  have h : Real.sin (0:ℝ) * Real.cos (0:ℝ) ^ 2 = 0 := by
    rw [Real.sin_zero, Real.cos_zero]; ring
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, h,
    Real.zero_rpow (ne_of_gt hα)]

/-- `Γ(π/2) = 0` for `α > 0`. -/
theorem Gamma_zero_right {α : ℝ} (hα : 0 < α) : Work.FTS.Regularity.Gamma α (π / 2) = 0 := by
  have h : Real.sin (π / 2) * Real.cos (π / 2) ^ 2 = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  rw [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, h,
    Real.zero_rpow (ne_of_gt hα)]

/-- `ω ≥ 0` on the closed quadrant. -/
theorem omega_nonneg_of (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.RegExportIface.ω α z θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  rw [Work.FTS.RegExportIface.ω]
  exact div_nonneg (mul_nonneg (sq_nonneg z) hG) (by positivity)

/-- `ω ≤ z²Γ`. -/
theorem omega_le_zsq_mul_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ ≤ z ^ 2 * Work.FTS.Regularity.Gamma α θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  have h1 : (1:ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  rw [Work.FTS.RegExportIface.ω, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  simpa using mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg z) hG)

/-- `ω ≤ Γ` (the `z²/(1+z)²` factor is `≤ 1`). -/
theorem omega_le_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ ≤ Work.FTS.Regularity.Gamma α θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  have h1 : z ^ 2 ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  rw [Work.FTS.RegExportIface.ω, div_le_iff₀ (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  calc z ^ 2 * Work.FTS.Regularity.Gamma α θ
      = Work.FTS.Regularity.Gamma α θ * z ^ 2 := by ring
    _ ≤ Work.FTS.Regularity.Gamma α θ * (1 + z) ^ 2 :=
        mul_le_mul_of_nonneg_left h1 hG

/-- `z/(1+z)² ≤ 1` for `z ≥ 0`. -/
theorem z_div_one_add_sq_le_one {z : ℝ} (hz : 0 ≤ z) : z / (1 + z) ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity : (0:ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg z]

/-- `ω α z θ / z ≤ Γ(θ)`, for `z ≥ 0` (the `z/(1+z)²` factor is `≤ 1`). -/
theorem omega_div_z_le_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ / z ≤ Work.FTS.Regularity.Gamma α θ := by
  have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · simp [Work.FTS.RegExportIface.ω, hG]
  · have hz0 : z ≠ 0 := ne_of_gt hzpos
    have hd0 : (1 + z) ^ 2 ≠ 0 := by positivity
    have e : Work.FTS.RegExportIface.ω α z θ / z
        = Work.FTS.Regularity.Gamma α θ * (z / (1 + z) ^ 2) := by
      rw [Work.FTS.RegExportIface.ω]
      field_simp
    rw [e]
    calc Work.FTS.Regularity.Gamma α θ * (z / (1 + z) ^ 2)
        ≤ Work.FTS.Regularity.Gamma α θ * 1 :=
          mul_le_mul_of_nonneg_left (z_div_one_add_sq_le_one hz) hG
      _ = Work.FTS.Regularity.Gamma α θ := mul_one _

/-- `ω α z θ / z ≤ z·Γ(θ)`, for `z ≥ 0` (the `1/(1+z)²` factor is `≤ 1`). -/
theorem omega_div_z_le_z_mul_Gamma (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.RegExportIface.ω α z θ / z ≤ z * Work.FTS.Regularity.Gamma α θ := by
  rcases eq_or_lt_of_le hz with rfl | hzpos
  · simp [Work.FTS.RegExportIface.ω]
  · have hG : 0 ≤ Work.FTS.Regularity.Gamma α θ := Work.ConstructionInstance.Gamma_nonneg hθ
    have h1 : (1:ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
    have hd0 : (1 + z) ^ 2 ≠ 0 := by positivity
    have e : Work.FTS.RegExportIface.ω α z θ / z
        = Work.FTS.Regularity.Gamma α θ * z * ((1 + z) ^ 2)⁻¹ := by
      rw [Work.FTS.RegExportIface.ω]
      field_simp
    rw [e]
    calc Work.FTS.Regularity.Gamma α θ * z * ((1 + z) ^ 2)⁻¹
        ≤ Work.FTS.Regularity.Gamma α θ * z * 1 :=
          mul_le_mul_of_nonneg_left
            (by rw [inv_le_one₀ (by positivity)]; exact h1) (mul_nonneg hG hz)
      _ = z * Work.FTS.Regularity.Gamma α θ := by ring

/-! ## §3 Congruences between `GG` and the slice of `g` -/

/-- `∂_z` of the `GG`-slice equals `∂_z` of the `g`-slice, for `z > 0`, `θ ∈ Iθ`. -/
theorem pz_GG_eq (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
      = Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z θ := by
  show deriv (fun z' => GG α g z' θ τ) z
    = deriv (fun z' => Work.FTS.Galerkin.slice g τ z' θ) z
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact GG_of_mem α hτ hz' hθ

/-- `∂_z²` of the `GG`-slice equals `∂_z²` of the `g`-slice, for `z > 0`, `θ ∈ Iθ`. -/
theorem pz_pz_GG_eq (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ)) z θ
      = Work.Spaces.pz (Work.Spaces.pz (Work.FTS.Galerkin.slice g τ)) z θ := by
  show deriv (fun z' => Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z' θ) z
    = deriv (fun z' => Work.Spaces.pz (Work.FTS.Galerkin.slice g τ) z' θ) z
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
  exact pz_GG_eq α hτ hz' hθ

/-- `D_θ` of the `GG`-slice equals `D_θ` of the `g`-slice, at interior angles. -/
theorem Dth_GG_eq (α : ℝ) {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) :
    Work.Spaces.Dth (Work.FTS.Regularity.gSlice (GG α g) τ) z θ
      = Work.Spaces.Dth (Work.FTS.Galerkin.slice g τ) z θ := by
  show Real.sin (2 * θ) * deriv (fun θ' => GG α g z θ' τ) θ
    = Real.sin (2 * θ) * deriv (fun θ' => Work.FTS.Galerkin.slice g τ z θ') θ
  congr 1
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩] with θ' hθ'
  exact GG_of_mem α hτ hz ⟨hθ'.1.le, hθ'.2.le⟩

section Vanish

variable {g : Work.FTS.Galerkin.Fam}

/-- `GG α g z 0 τ = 0` on the left angular boundary. -/
theorem GG_eq_zero_left (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    GG α g z 0 τ = 0 := by
  rw [GG_of_mem α hτ hz ⟨le_rfl, by linarith [Real.pi_pos]⟩]
  exact (hv τ hτ z hz.le).1

/-- `GG α g z (π/2) τ = 0` on the right angular boundary. -/
theorem GG_eq_zero_right (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    GG α g z (π / 2) τ = 0 := by
  rw [GG_of_mem α hτ hz ⟨by linarith [Real.pi_pos], le_rfl⟩]
  exact (hv τ hτ z hz.le).2

/-- `∂_z` of the `GG`-slice vanishes at `θ = 0` (for `z > 0`). -/
theorem pz_GG_eq_zero_left (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z 0 = 0 := by
  show deriv (fun z' => GG α g z' 0 τ) z = 0
  have hev : (fun z' : ℝ => GG α g z' 0 τ) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact GG_eq_zero_left α hτ hz' hv
  rw [hev.deriv_eq, deriv_const]

/-- `∂_z` of the `GG`-slice vanishes at `θ = π/2` (for `z > 0`). -/
theorem pz_GG_eq_zero_right (α : ℝ) {τ z : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z)
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    Work.Spaces.pz (Work.FTS.Regularity.gSlice (GG α g) τ) z (π / 2) = 0 := by
  show deriv (fun z' => GG α g z' (π / 2) τ) z = 0
  have hev : (fun z' : ℝ => GG α g z' (π / 2) τ) =ᶠ[𝓝 z] (fun _ => (0:ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact GG_eq_zero_right α hτ hz' hv
  rw [hev.deriv_eq, deriv_const]

end Vanish

/-- `D_zD_θ = z·sin(2θ)·∂_z∂_θ`. -/
theorem mixed_one_one_eq (Φ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 1 1 Φ z θ
      = z * (Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth Φ) z θ) := by
  show z * Work.Spaces.pz (Work.Spaces.Dth Φ) z θ = _
  congr 1
  show deriv (fun z' => Real.sin (2 * θ) * Work.Spaces.pth Φ z' θ) z = _
  rw [deriv_const_mul_field]
  rfl

/-! ## §4 `K ≥ 0` -/

/-- The weighted bound forces `0 ≤ K` (it is read at the interior point `(1, π/4)`, `τ = 0`). -/
theorem st1_K_nonneg {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam} {S K : ℝ}
    (hS : 0 < S)
    (hw : ∀ k : Fin 6, ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.Galerkin.slice g τ) z θ| ≤ K * Work.FTS.RegExportIface.ω α z θ) :
    0 ≤ K := by
  have hωpos : 0 < Work.FTS.RegExportIface.ω α 1 (π / 4) := by
    have hΓ : 0 < Work.FTS.Regularity.Gamma α (π / 4) :=
      Gamma_pos α (π / 4) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    rw [Work.FTS.RegExportIface.ω]
    positivity
  have hpt : |Work.Spaces.mixed 0 0 (Work.FTS.Galerkin.slice g 0) 1 (π / 4)|
      ≤ K * Work.FTS.RegExportIface.ω α 1 (π / 4) := by
    have h := hw (0 : Fin 6) 0 ⟨le_rfl, hS.le⟩ 1 (π / 4) one_pos
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    norm_num [Work.FTS.RegExportIface.RXT.idx] at h
    exact h
  exact nonneg_of_mul_nonneg_left (le_trans (abs_nonneg _) hpt) hωpos

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT0.RXJets.CJDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.CJHyps` — the hypothesis bundle of `coeffJetsJointCont`

`coeffJetsJointCont` has ten hypotheses (`hα`, `hα13`, `hEll`, `hEL3`, `hStar`, `hSol`, `hOK`,
`hμ`, `hL12`, `hSlot`).  The proof is split over several modules (the file-size guard of the
project forbids a single large module), so the ten are bundled here into one `Prop`-valued
structure; the statement of `coeffJetsJointCont` itself is *unchanged* and still takes the ten
hypotheses separately, constructing this structure at the top of its proof.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

/-- **The hypothesis bundle of `coeffJetsJointCont`**, verbatim. -/
structure CJHyps (α C₀ Ce Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) : Prop where
  hα : 0 < α
  hα13 : α ≤ 1 / 3
  hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
    Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
      Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u)
  hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E
  hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs
  hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g
  hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g
  hμ : Work.FTS.RegExportIface.ClockBd α Φs E g
  hL12 : ∀ S > 0, ∀ j : ℕ, j ≤ 2 →
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (fun z (_ : ℝ) => Work.Construction.L12
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
      (fun z (_ : ℝ) => Work.Construction.FK
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S)
  hSlot : ∀ S > 0, ∀ j i : ℕ, j + i ≤ 2 →
    (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
      (fun z θ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
      p.1 p.2.1)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
    (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
      (fun z θ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ)
      p.1 p.2.1)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))) ∧
    (ContinuousOn (fun p : ℝ × ℝ × ℝ => Work.Spaces.mixed j i
      (fun z θ => Work.Construction.Uop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.FTS.Galerkin.slice g p.2.2) (E (Work.FTS.Galerkin.slice g p.2.2))) z θ
        / Real.sin (2 * θ)) p.1 p.2.1)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))

end Work.FTS_RegExport.RXT0.RXJets
end
end
-- ===== merged: Submission.Work.FTS_RegExport.THL.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.THL

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false

/-- The Γ-weighted system (output of `RXT.weighted_system`, input of `RXT.st1_angle`). -/
def WSys (α S K : ℝ) (g : Fam) : Prop :=
  ∀ k : Fin 6, ∀ τ ∈ Icc (0:ℝ) S, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
    |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
      (Work.FTS.RegExportIface.RXT.idx k).2 (slice g τ) z θ| ≤ K * ω α z θ

/-- The two O1 families. -/
abbrev DzG (α : ℝ) (g : Fam) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  Work.Spaces.Dz (fun z θ => gS α (tauExt g) z θ τ) z θ
abbrev DthG (α : ℝ) (g : Fam) : ℝ → ℝ → ℝ → ℝ := fun z θ τ =>
  Work.Spaces.Dth (fun z θ => gS α (tauExt g) z θ τ) z θ

end Work.FTS_RegExport.THL
end
end
