import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.R5Parts
import Submission.Work.FTS.RegPkgGal.R7d.support_strip
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.Stability.CutFactorFderivZero
-- ===== merged: Submission.Work.FTS.RegExportIface.RXT.LeafDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! # `Work.FTS.RegExportIface.RXT.LeafDefs` — the definition block of `RXT/Leaves.lean`

Split out of `Submission/Work/FTS/RegExportIface/RXT/Leaves.lean` (same namespace, hence the same
fully-qualified names) so that leaf-proof modules can be written **without** importing `Leaves`:
`Leaves` imports this file, so every one of the ~130 consumers of `Leaves` is unaffected, while a
`LeafAux/<leaf>.lean` module (imported by `Leaves`) can import `LeafDefs` instead of `Leaves` and
the import cycle is broken.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS.RegExportIface.RXT

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp)
open Work.FTS.RegPkgGal (extG St1Class)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- The one-step backward inequality on compact boxes, with the coupling taken at the new time. -/
def ConeStep (n : ℕ) (φ : Fin n → ℝ → ℝ → ℝ → ℝ) (T A C F : ℝ) : Prop :=
  ∀ R ε : ℝ, 0 < ε → ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ τ ∈ Ico (0:ℝ) T, ∀ h : ℝ, 0 < h → h < h₀ →
    τ + h ≤ T → ∀ s ψ : ℝ, |s| ≤ R → |ψ| ≤ R →
      ∃ s' ψ' : ℝ, |s' - s| ≤ A * h ∧ |ψ' - ψ| ≤ A * h ∧
        ∀ M B : ℝ, (∀ j, |φ j s' ψ' τ| ≤ M) → (∀ j, |φ j s ψ (τ + h)| ≤ B) →
          ∀ k, |φ k s ψ (τ + h)| ≤ M + h * (C * B + F) + ε * h

/-- The six components `(j,i) = (#D_z, #D_θ)` of the system. -/
def idx : Fin 6 → ℕ × ℕ := ![(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]

/-- the sanitised family, its stream function and its clock -/
abbrev GR (α : ℝ) (g : Fam) : Fam := gS α (tauExt g)
abbrev ΦR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : Fam := psiR α Φs E (tauExt g)
abbrev μR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ :=
  Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g
/-- the three transport coefficients (closed form, `b = Vθ7/sin 2θ`) -/
abbrev VR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  Vz7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g)
abbrev bR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ / Real.sin (2 * θ)
abbrev cR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  cs7 (pExp α) (μR α Φs E g) (GR α g) (ΦR α Φs E g)
/-- the `F_*`-forcing `Σ = Vz·D_zF_* + Vθ·∂_θF_* + cs·F_*` (slice at `τ`) -/
def SigR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  VR α Φs E g z θ τ * Work.Spaces.Dz (Work.Construction.Fstar (pExp α)) z θ
    + Vθ7 (pExp α) (ΦR α Φs E g) z θ τ * Work.Spaces.pth (Work.Construction.Fstar (pExp α)) z θ
    + cR α Φs E g z θ τ * Work.Construction.Fstar (pExp α) z θ

/-- The local regularity of `∂_τg` that S5a consumes (output of S5c). -/
def GdotLoc (S : ℝ) (g : Fam) : Prop :=
  (∀ σ ∈ Ioc (0:ℝ) S,
    ContDiffOn ℝ 2 (Function.uncurry (Work.FTS.Galerkin.gdot g σ)) Work.FTS.EllipticEst.Q0) ∧
  ∀ a b c d : ℝ, 0 < a → a ≤ b → 0 < c → c ≤ d → d < π / 2 → ∃ C : ℝ,
    ∀ σ ∈ Ioc (0:ℝ) S, ∀ z ∈ Icc a b, ∀ θ ∈ Icc c d,
      (∀ j i : ℕ, j + i ≤ 2 → |Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ) z θ| ≤ C) ∧
      (∀ j i : ℕ, j + i ≤ 1 →
        |Work.Spaces.pz (Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ)) z θ| ≤ C ∧
        |Work.Spaces.pth (Work.Spaces.mixed j i (Work.FTS.Galerkin.gdot g σ)) z θ| ≤ C)

end Work.FTS.RegExportIface.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXDiag.closedFormOpen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXDiag

open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-!
# `Work.FTS_RegExport.RXDiag.closedFormOpen`

**The closed form of the transport coefficients `Vz7`, `cs7` on the open quadrant.**

`Vz7 = (1-μ) + L₁₂(F)·c2m + 2αG·V(Φ̃)` and `cs7 = (1+μ) - L₁₂(F)/αG + sin²θ·𝔽K(F) - 2·ℛ(Φ̃)`
are written with the `Θ`-part in closed form, so that they are continuous up to `θ = π/2`
(see the design notes of `RegExportIface/Defs`).  On the *open* quadrant, where the two
`Θ`-identities `2αG·V(Θ) = L₁₂(F)·c2m(θ)` and `-2·ℛ(Θ) = -L₁₂(F)/αG + sin²θ·𝔽K(F)` hold (the
second needs `z∂_zL₁₂(F) = -𝔽K(F)`, i.e. the density hypotheses `hint`, `hcont`), the `Θ`-parts
drop out and the coefficients reduce to their *literal* form `(1∓μ) ± 2αG·(V/R)(Φ)`.

The two ingredients are

* the closed forms of `V(Θ)`, `ℛ(Θ)` (`two_mul_Vop_Theta`, `neg_two_mul_Rop_Theta`), and
* the subtractivity of `V`, `ℛ` at a point where both slices (in `z` and in `θ`) of both data
  are differentiable (`Vop_sub_of_diffAt`, `Rop_sub_of_diffAt`) — the hypotheses `hdz`, `hdθ`
  of the statement.  (`Work.R1G6.annOp_sub` proves the sibling statement for *jointly*
  differentiable data.)
-/

/-! ## Subtracting the two partials slicewise -/





/-! ## The two closed forms of `Θ` -/

/-- `2αG·V(Θ αG F) = L₁₂(F)·c2m(θ)` on the open quadrant. -/
private theorem two_mul_Vop_Theta {αG : ℝ} (hαG : 0 < αG) {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    2 * αG * Work.Construction.Vop (Work.Construction.Theta αG F) z θ
      = Work.Construction.L12 F z * Work.Construction.c2m θ := by
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hα0 : αG ≠ 0 := ne_of_gt hαG
  have hpth : Work.Spaces.pth (Work.Construction.Theta αG F) z θ
      = (1 / (4 * αG)) * (2 * Real.cos (2 * θ)) * Work.Construction.L12 F z := by
    rw [Work.Construction.pth_Theta_eq (α := αG) hαG z θ]
    ring
  simp only [Work.Construction.Vop, hpth, Work.Construction.Theta, Work.Construction.s2,
    Work.Construction.c2m, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul, Real.cos_two_mul']
  field_simp
  rw [Real.sin_sq]
  ring


/-! ## The main statement -/


end Work.FTS_RegExport.RXDiag
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.HJ.HJDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

/-! ## Local vocabulary for `hj_cluster`

`Gs α g = gS α (tauExt g)` is the sanitised right-Taylor family on which the R1 block is read, and
`Ps α Φs E g = psiR α Φs E (tauExt g)` the stream function of the R5 package.  The remaining
abbreviations decompose the right-hand side of the fake-time equation at `τ = 0` into its five
elementary pieces, so that the `R5Parts` jet / `z`-derivative fields apply to them verbatim.  The
profile exponent of the dynamic equation is `pExp α = 3α`, which is what `R5Parts` itself uses. -/

/-- The sanitised right-Taylor family. -/
abbrev Gs (α : ℝ) (g : Work.FTS.Galerkin.Fam) : Work.FTS.Galerkin.Fam :=
  Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)

/-- The R5 stream function of the right-Taylor family. -/
abbrev Ps (α : ℝ) (Φs : Work.FTS.Galerkin.Fn) (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn)
    (g : Work.FTS.Galerkin.Fam) : Work.FTS.Galerkin.Fam :=
  Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)

/-- The within-filter of the cluster: `(z,τ) → (0,τ₀)` with `z > 0`. -/
abbrev Filt (τ₀ : ℝ) : Filter (ℝ × ℝ) :=
  nhdsWithin ((0 : ℝ), τ₀) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)

abbrev RP1 (α : ℝ) (G : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  -(Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α) (Work.FTS.Regularity.gSlice G 0) z θ)

abbrev RP2 (α : ℝ) (G : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.Construction.N0 (Work.FTS.Regularity.pExp α)
    (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice G 0) z θ

abbrev RP3 (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.Construction.N (Work.FTS.Regularity.pExp α)
    (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice Φ 0) z θ

abbrev RP4 (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.Construction.Nstar (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) Φ G 0)
    (Work.FTS.Galerkin.lamDyn (Work.FTS.Regularity.pExp α) Φ G 0)
    (Work.FTS.Regularity.gSlice G 0) z θ

abbrev mbar0 (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) : ℝ :=
  Work.Construction.mubar
    (Work.Construction.N0 (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice G 0))
    (Work.Construction.N (Work.FTS.Regularity.pExp α)
      (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) G 0) (Work.FTS.Regularity.gSlice Φ 0))

/-- The right-hand side of the fake-time equation at `τ = 0`. -/
abbrev RHSo (α : ℝ) (G Φ : Work.FTS.Galerkin.Fam) (z θ : ℝ) : ℝ :=
  Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) G 0 z θ
    + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ G 0 z θ

/-- `Galerkin.slice` and `Regularity.gSlice` are the same family slice (definitionally). -/
theorem slice_eq_gSlice (g : Work.FTS.Galerkin.Fam) (τ : ℝ) :
    Work.FTS.Galerkin.slice g τ = Work.FTS.Regularity.gSlice g τ := rfl

/-- The decomposition of the right-hand side into its five elementary pieces. -/
theorem RHSo_eq {α : ℝ} {G Φ : Work.FTS.Galerkin.Fam} (z θ : ℝ) :
    RHSo α G Φ z θ = RP1 α G z θ
      + (-(mbar0 α G Φ) * Work.Construction.AK (Work.FTS.Regularity.pExp α) z θ
        + RP2 α G z θ + RP3 α G Φ z θ + RP4 α G Φ z θ) := by
  simp only [RHSo, RP1, RP2, RP3, RP4, mbar0, Work.FTS.Galerkin.dynLin, Work.FTS.Galerkin.dynRHS,
    Work.Construction.gRHS, slice_eq_gSlice]

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.ftc_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS_RegExport.RXR1

theorem ftc_slice {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    {θ z k : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hz : 0 < z)
    (hk : k ∈ Set.Icc (0:ℝ) 1)
    (hsol : Work.FTS.Galerkin.IsDynEqOn (Work.FTS.Regularity.pExp α)
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hcont : ContinuousOn (fun s : ℝ => g z θ s) (Set.Ici 0))
    (hRcont : ContinuousOn (fun s : ℝ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) (Set.Icc (0:ℝ) 1)) :
    g z θ k - g z θ 0 = ∫ s in (0:ℝ)..k, (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) := by
  have hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := ⟨hθ0.le, hθ1.le⟩
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  -- the sanitiser and the right-Taylor extension are invisible on `τ ≥ 0`
  have hEq : ∀ s ∈ Set.Ici (0:ℝ), Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s
      = g z θ s := by
    intro s hs
    rw [Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hθ]
    exact Work.FTS.FinalV2.tauExt_of_nonneg g hs
  -- the one-sided equation of the datum, transferred to `g` itself
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) k,
      HasDerivAt (fun s => g z θ s)
        (Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) x z θ
          + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
            (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) x z θ) x := by
    intro x hx
    have hd := hsol z θ x hx.1.le hzθ
    exact (hd.congr (fun s hs => (hEq s hs).symm) ((hEq x hx.1.le).symm)).hasDerivAt
      (Ici_mem_nhds hx.1)
  have hcontI : ContinuousOn (fun s : ℝ => g z θ s) (Set.Icc (0:ℝ) k) :=
    hcont.mono (fun x hx => hx.1)
  have hRcontI : ContinuousOn (fun s : ℝ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) (Set.Icc (0:ℝ) k) :=
    hRcont.mono (fun x hx => ⟨hx.1, le_trans hx.2 hk.2⟩)
  have hint : IntervalIntegrable (fun s : ℝ => Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α)
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ
      + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α)
        (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))
        (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) s z θ) volume (0:ℝ) k := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hk.1]
    exact hRcontI
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hk.1 hcontI hderiv hint
  simpa using hFTC.symm

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.hd1z2_limit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.hd1z2_limit`

The `z`-weighted vanishing of the fake-time derivative `∂_τ g` at `τ = 0`, at the corner
`(z, θ) → (0, 0)`:

  `z⁻¹ · ∂_τ (gS α (tauExt g))(z, θ, 0) → 0` as `z → 0⁺`, for every `θ ∈ Iθ`.

The proof has three ingredients.

* **The one-sided slope bound** (`abs_deriv_zero_le_of_slope_bound`): if `|G s - G 0| ≤ M s`
  for `0 < s < 1` then `|deriv G 0| ≤ M`.  If `G` is differentiable at `0` the slope tends to
  `deriv G 0` along `(0,1]` and the bound is the limit of the bounds; if not, `deriv G 0 = 0`
  by the totalisation of `deriv`.

* **The endpoints** `θ = 0, π/2` (`deriv_gS_tauExt_eq_zero_at_boundary`): `RegPkgMin.vanish`
  makes `g z 0 τ = g z (π/2) τ = 0` for `τ ≥ 0`, hence the `τ`-slice of `tauExt g` is
  identically zero at those angles and the derivative at `0` vanishes.

* **The interior** `0 < θ < π/2`: the hypothesis `hw` bounds the `τ`-differences of the slices
  of `g` by `C z^{3/2}/(1+z)² |τ - τ'|`, which is exactly the slope bound for
  `s ↦ gS α (tauExt g) z θ s` on `(0,1)`; the slope bound yields
  `|∂_τ(gS α (tauExt g))(z,θ,0)| ≤ C z^{3/2}/(1+z)²`, and multiplication by `z⁻¹` gives
  `C z^{1/2}/(1+z)² ≤ C z^{1/2} → 0`.

* The final limit is taken along `𝓝[(0,0)] (Ioi 0 ×ˢ univ)`; since the function only depends on
  the first coordinate, the one-dimensional eventual bound is lifted by
  `eventually_nhdsWithin_fst` and closed with `Metric.tendsto_nhds`.
-/

noncomputable section

open scoped Topology
open Filter

namespace Work.FTS_RegExport.RXR1

set_option autoImplicit false

/-- **A one-sided slope bound bounds the derivative at `0`.**  If `|G s - G 0| ≤ M · s` for
`s ∈ (0,1)`, then `|deriv G 0| ≤ M`.  (No hypothesis on the left of `0` is needed: if `G` is not
differentiable at `0` then `deriv G 0 = 0`.) -/
lemma abs_deriv_zero_le_of_slope_bound {G : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ s ∈ Set.Ioo (0:ℝ) 1, |G s - G 0| ≤ M * s) : |deriv G 0| ≤ M := by
  by_cases hd : DifferentiableAt ℝ G 0
  · -- `G` is differentiable at `0`: the slope bound passes to the limit along `(0,1)`
    have hslope : Filter.Tendsto (slope G 0) (𝓝[>] (0:ℝ)) (𝓝 (deriv G 0)) :=
      (hd.hasDerivAt.tendsto_slope).mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
    have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), ‖slope G 0 s‖ ≤ M := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Ioo_mem_nhds (by norm_num : (-1:ℝ) < 0) (by norm_num : (0:ℝ) < 1))] with s hs hsI
      have hs0 : 0 < s := hs
      have h1 : slope G 0 s = (G s - G 0) / s := by rw [slope_def_field, sub_zero]
      rw [h1, div_eq_mul_inv, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs0)]
      calc |G s - G 0| * s⁻¹ ≤ (M * s) * s⁻¹ :=
            mul_le_mul_of_nonneg_right (h s ⟨hs0, hsI.2⟩) (le_of_lt (inv_pos.mpr hs0))
        _ = M := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hs0), mul_one]
    have hnorm : ‖deriv G 0‖ ≤ M := le_of_tendsto hslope.norm hev
    rwa [Real.norm_eq_abs] at hnorm
  · -- `G` is not differentiable at `0`: the derivative is the junk value `0`
    rw [deriv_zero_of_not_differentiableAt hd, abs_zero]
    exact hM

/-- **Lifting an eventual statement in `z` to the two-dimensional filter
`𝓝[(0,0)] (Ioi 0 ×ˢ univ)`**, using that `Prod.fst` is continuous. -/
lemma eventually_nhdsWithin_fst {P : ℝ → Prop}
    (h : ∀ᶠ z in nhdsWithin (0:ℝ) (Set.Ioi 0), P z) :
    ∀ᶠ p : ℝ × ℝ in nhdsWithin (0,0) (Set.Ioi (0:ℝ) ×ˢ Set.univ), P p.1 := by
  rw [nhdsWithin, Filter.eventually_inf_principal] at h
  rw [nhdsWithin, Filter.eventually_inf_principal]
  have h2 : ∀ᶠ p : ℝ × ℝ in 𝓝 ((0:ℝ),(0:ℝ)), (0 < p.1 → P p.1) :=
    (continuous_fst.tendsto ((0:ℝ),(0:ℝ))).eventually h
  filter_upwards [h2] with p hp hpS
  exact hp hpS.1

/-- **At the angular endpoints `θ = 0`, `π/2` the family `gS α (tauExt g)` is identically zero in
the fake time**, when the datum `g` vanishes on the two boundary rays `θ = 0`, `θ = π/2`
(the `vanish` clause of `RegPkgMin`).  Hence the `τ`-derivative at `0` vanishes. -/
lemma deriv_gS_tauExt_eq_zero_at_boundary {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hvanish : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    {θ : ℝ} (hθbd : θ = 0 ∨ θ = Real.pi / 2) :
    ∀ z : ℝ, 0 < z →
      deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0 = 0 := by
  have hθ0 : 0 ≤ θ := by rcases hθbd with h | h <;> rw [h] <;> linarith [Real.pi_pos]
  have hθπ : θ ≤ Real.pi / 2 := by rcases hθbd with h | h <;> rw [h] <;> linarith [Real.pi_pos]
  have hval : ∀ (s : ℝ) (z : ℝ), 0 ≤ s → 0 ≤ z → g z θ s = 0 := by
    intro s z hs hz
    rcases hθbd with h | h <;> rw [h]
    · exact (hvanish s hs z hz).1
    · exact (hvanish s hs z hz).2
  intro z hz
  have hfun : (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s)
      = fun _ => (0:ℝ) := by
    have hEq : Set.EqOn (fun s => g z θ s) (fun _ => (0:ℝ)) (Set.Ici 0) :=
      fun s hs => hval s z hs hz.le
    have hd0 : derivWithin (fun s => g z θ s) (Set.Ici 0) 0 = 0 := by
      rw [derivWithin_congr hEq (by simpa using hval 0 z le_rfl hz.le)]
      exact congrFun (derivWithin_const (Set.Ici (0:ℝ)) (0:ℝ)) 0
    funext s
    have hgs : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s
        = Work.FTS.FinalV2.tauExt g z θ s := by
      simp [Work.FTS.FinalV2.gS, hz, hθ0, hθπ]
    rw [hgs]
    by_cases hs : s < 0
    · -- the left branch of `tauExt` is the affine extension with slope `derivWithin … = 0`
      rw [Work.FTS.FinalV2.tauExt_of_neg g hs, hd0, hval 0 z le_rfl hz.le]
      ring
    · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hs)]
      exact hval s z (not_lt.mp hs) hz.le
  rw [hfun, deriv_const]

theorem hd1z2_limit {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)))
    (hw : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ τ' ∈ Set.Icc (0:ℝ) 1,
      ∀ b a : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'|) :
    ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto
      (fun p : ℝ × ℝ => p.1⁻¹ * deriv
        (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) 0)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) Set.univ)) (nhds 0) := by
  intro θ hθ
  have hθ0 : 0 ≤ θ := hθ.1
  have hθπ : θ ≤ Real.pi / 2 := hθ.2
  have hreg : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g := hOK.1.1
  have hvan : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0 :=
    fun τ hτ z hz => hreg.vanish τ hτ z hz
  -- on the quadrant `gS α (tauExt g)` agrees with `tauExt g`
  have hGval : ∀ z s : ℝ, 0 < z →
      Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s
        = Work.FTS.FinalV2.tauExt g z θ s := by
    intro z s hz
    simp [Work.FTS.FinalV2.gS, hz, hθ0, hθπ]
  rcases eq_or_lt_of_le hθ0 with hθeq | hθpos
  · -- `θ = 0`
    subst hθeq
    have hkey := deriv_gS_tauExt_eq_zero_at_boundary (α := α) (g := g) hvan (Or.inl rfl)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    rw [hkey p.1 hp.1, mul_zero]
  rcases eq_or_lt_of_le hθπ with hθeq2 | hθlt
  · -- `θ = π/2`
    subst hθeq2
    have hkey := deriv_gS_tauExt_eq_zero_at_boundary (α := α) (g := g) hvan (Or.inr rfl)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with p hp
    rw [hkey p.1 hp.1, mul_zero]
  · -- `0 < θ < π/2`: the slope hypothesis `hw`
    obtain ⟨C, hC0, hC⟩ := hw
    have hident : ∀ z : ℝ, 0 < z →
        z⁻¹ * (C * (z ^ ((3:ℝ)/2) / (1+z)^2)) = C * (Real.sqrt z / (1+z)^2) := by
      intro z hz
      have h3 : z ^ ((3:ℝ)/2) = z * Real.sqrt z := by
        rw [show (3:ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add hz, Real.rpow_one,
          ← Real.sqrt_eq_rpow]
      rw [h3]
      field_simp
    -- the `τ`-derivative at `0` obeys the `3/2`-weight
    have hderiv : ∀ z : ℝ, 0 < z →
        |deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0|
          ≤ C * (z ^ ((3:ℝ)/2) / (1+z)^2) := by
      intro z hz
      refine abs_deriv_zero_le_of_slope_bound
        (mul_nonneg hC0 (div_nonneg (Real.rpow_nonneg hz.le _) (sq_nonneg _))) ?_
      intro s hs
      have hs0 : 0 < s := hs.1
      have hsle : 0 ≤ s := hs0.le
      have hGs : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s = g z θ s := by
        rw [hGval z s hz, Work.FTS.FinalV2.tauExt_of_nonneg g hsle]
      have hG0 : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ 0 = g z θ 0 := by
        rw [hGval z 0 hz, Work.FTS.FinalV2.tauExt_of_nonneg g le_rfl]
      rw [hGs, hG0]
      have h1 := hC s ⟨hsle, hs.2.le⟩ 0 ⟨le_rfl, zero_le_one⟩ 0 0 (by norm_num)
        z θ hz hθpos hθlt
      simpa [Work.Spaces.mixed, sub_zero, abs_of_nonneg hsle] using h1
    -- divide by `z`: the weight becomes `z^{1/2}/(1+z)² ≤ z^{1/2}`
    have hbound : ∀ p : ℝ × ℝ, 0 < p.1 →
        ‖p.1⁻¹ * deriv
          (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) 0‖
          ≤ C * Real.sqrt p.1 := by
      intro p hp
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr hp)]
      calc p.1⁻¹ * |deriv
            (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) 0|
          ≤ p.1⁻¹ * (C * (p.1 ^ ((3:ℝ)/2) / (1+p.1)^2)) :=
            mul_le_mul_of_nonneg_left (hderiv p.1 hp) (le_of_lt (inv_pos.mpr hp))
        _ = C * (Real.sqrt p.1 / (1+p.1)^2) := hident p.1 hp
        _ ≤ C * Real.sqrt p.1 := mul_le_mul_of_nonneg_left
            (div_le_self (Real.sqrt_nonneg p.1) (one_le_pow₀ (by linarith))) hC0
    rw [Metric.tendsto_nhds]
    intro ε hε
    have htend : Filter.Tendsto (fun z : ℝ => C * Real.sqrt z)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
      have h1 : Filter.Tendsto (fun z : ℝ => Real.sqrt z)
          (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul h1)
    have hev0 : ∀ᶠ z in nhdsWithin (0:ℝ) (Set.Ioi 0), C * Real.sqrt z < ε :=
      htend.eventually (Iio_mem_nhds hε)
    have hev : ∀ᶠ p : ℝ × ℝ in nhdsWithin (0,0) (Set.Ioi (0:ℝ) ×ˢ Set.univ),
        0 < p.1 → C * Real.sqrt p.1 < ε :=
      eventually_nhdsWithin_fst (P := fun z => 0 < z → C * Real.sqrt z < ε)
        (hev0.mono (fun z hz _ => hz))
    filter_upwards [hev, self_mem_nhdsWithin] with p hp hpmem
    rw [dist_zero_right]
    exact lt_of_le_of_lt (hbound p hpmem.1) (hp hpmem.1)

end Work.FTS_RegExport.RXR1
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.hd1z_limit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.hd1z_limit`

The R1 field `hd1z` for the sanitised right-Taylor family `gS α (tauExt g)`: for every
`θ ∈ Iθ` the `z`-derivative of the `τ`-derivative at `τ = 0` of the `θ`-slice tends to `0`
along `z → 0⁺`.

The proof is a difference-quotient argument.  The hypothesis `hw` supplies the uniform-in-`τ`
estimate

`|D_z (g(τ) - g(τ'))| ≤ C z^{3/2}/(1+z)^2 |τ - τ'|`  (`a + b ≤ 1`, in particular `a = 0, b = 1`),

so the family of difference quotients `Φ_τ = (g(τ) - g(0))/τ` has, on `(0,∞)`, a
`z`-derivative bounded by `C √z`; the pointwise limit of `Φ_τ` as `τ → 0⁺` is the
`τ`-derivative at `0` (`H5.h0` is a two-sided `τ`-derivative at `0`), and a pointwise limit of
differentiable functions whose derivatives are bounded by a monotone continuous `φ` satisfies
`|G'| ≤ φ`.  Passing to the limit at `z → 0⁺` gives the claim.  On the two boundary angles
`θ = 0, π/2` the family vanishes identically (it is `0` there by `RegPkgMin.vanish`).
-/

namespace Work.FTS_RegExport.RXR1

open Filter Set
open scoped Topology

/-! ## Auxiliary real-analysis lemmas -/

/-- **Uniformly bounded derivatives pass to a pointwise limit.**  If `F i` is differentiable on
`(0,∞)` with `|deriv (F i) x| ≤ φ x`, where `φ` is continuous, nonnegative and monotone, and
`F i x → G x` along the filter `l`, then `|deriv G x| ≤ φ x` for `x > 0`.

(`deriv G x` is `0` at a point where `G` is not differentiable, so that case is trivial.) -/
theorem deriv_bound_of_pointwise_tendsto {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {F : ι → ℝ → ℝ} {G φ : ℝ → ℝ}
    (hF : ∀ i, ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (F i) x)
    (hφc : ContinuousOn φ (Set.Ioi 0))
    (hφ0 : ∀ x ∈ Set.Ioi 0, 0 ≤ φ x)
    (hφm : ∀ x ∈ Set.Ioi 0, ∀ y ∈ Set.Ioi 0, x ≤ y → φ x ≤ φ y)
    (hd : ∀ i, ∀ x ∈ Set.Ioi 0, |deriv (F i) x| ≤ φ x)
    (hpt : ∀ x ∈ Set.Ioi 0, Filter.Tendsto (fun i => F i x) l (nhds (G x))) :
    ∀ x ∈ Set.Ioi 0, |deriv G x| ≤ φ x := by
  have key_le : ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (0 : ℝ), x ≤ y →
      |G y - G x| ≤ φ y * |y - x| := by
    intro x hx y hy hxy
    have hbdd : ∀ᶠ i in l, |F i y - F i x| ≤ φ y * |y - x| := by
      refine Filter.Eventually.of_forall (fun i => ?_)
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := F i) (s := Set.Icc x y)
        (x := x) (y := y) (C := φ y)
        (fun t ht => hF i t (lt_of_lt_of_le hx ht.1))
        (fun t ht => by
          rw [Real.norm_eq_abs]
          exact le_trans (hd i t (lt_of_lt_of_le hx ht.1))
            (hφm t (lt_of_lt_of_le hx ht.1) y hy ht.2))
        (convex_Icc x y) ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩
      simpa only [Real.norm_eq_abs] using hmvt
    have hlim : Filter.Tendsto (fun i => |F i y - F i x|) l (nhds |G y - G x|) :=
      ((hpt y hy).sub (hpt x hx)).abs
    exact le_of_tendsto_of_tendsto hlim tendsto_const_nhds hbdd
  have key : ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (0 : ℝ),
      |G y - G x| ≤ φ (max x y) * |y - x| := by
    intro x hx y hy
    rcases le_total x y with hxy | hyx
    · simpa only [max_eq_right hxy] using key_le x hx y hy hxy
    · have h1 := key_le y hy x hx hyx
      rw [max_eq_left hyx]
      rwa [abs_sub_comm (G x) (G y), abs_sub_comm x y] at h1
  intro x hx
  have hx' : (0 : ℝ) < x := hx
  by_cases hD : DifferentiableAt ℝ G x
  · have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ • (G (x + t) - G x))
        (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (deriv G x)) := hD.hasDerivAt.tendsto_slope_zero
    have hslope' : Filter.Tendsto (fun t : ℝ => t⁻¹ * (G (x + t) - G x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv G x)) := by
      have h1 := hslope.mono_left
        (nhdsWithin_mono 0 (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ne_of_gt ht))
      simpa only [smul_eq_mul] using h1
    have hbnd : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        |t⁻¹ * (G (x + t) - G x)| ≤ φ (x + t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hxt : (0 : ℝ) < x + t := by linarith
      have h1 : |G (x + t) - G x| ≤ φ (x + t) * t := by
        have h2 := key x hx (x + t) hxt
        rw [max_eq_right (by linarith : x ≤ x + t)] at h2
        rwa [add_sub_cancel_left, abs_of_pos ht0] at h2
      have htne : t ≠ 0 := ne_of_gt ht0
      calc |t⁻¹ * (G (x + t) - G x)| = t⁻¹ * |G (x + t) - G x| := by
            rw [abs_mul, abs_inv, abs_of_pos ht0]
        _ ≤ t⁻¹ * (φ (x + t) * t) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr ht0.le)
        _ = φ (x + t) := by field_simp
    have hlimφ : Filter.Tendsto (fun t : ℝ => φ (x + t)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (φ x)) := by
      have hcont : ContinuousAt φ x := hφc.continuousAt (isOpen_Ioi.mem_nhds hx)
      have hadd : ContinuousAt (fun t : ℝ => x + t) 0 :=
        continuousAt_const.add continuousAt_id
      have h1 : Filter.Tendsto (fun t : ℝ => x + t) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds x) := by
        simpa using hadd.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Function.comp_def] using hcont.tendsto.comp h1
    exact le_of_tendsto_of_tendsto hslope'.abs hlimφ hbnd
  · rw [deriv_zero_of_not_differentiableAt hD]
    simpa using hφ0 x hx

/-- **A `√z` bound on the derivative gives the limit `0` at `0⁺`.** -/
theorem tendsto_deriv_of_abs_le_sqrt {G : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), |deriv G z| ≤ C * Real.sqrt z) :
    Filter.Tendsto (fun p : ℝ × ℝ => deriv G p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
  have hbdd : ∀ᶠ p : ℝ × ℝ in nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ),
      |deriv G p.1| ≤ C * Real.sqrt p.1 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact h p.1 hp.1
  have hlim : Filter.Tendsto (fun p : ℝ × ℝ => C * Real.sqrt p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun p : ℝ × ℝ => p.1)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds (0 : ℝ)) :=
      (continuous_fst.tendsto (0, 0)).mono_left nhdsWithin_le_nhds
    have h2 : Filter.Tendsto (fun p : ℝ × ℝ => Real.sqrt p.1)
        (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    simpa using h2.const_mul C
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [Real.norm_eq_abs] using
    squeeze_zero' (Filter.Eventually.of_forall (fun p => abs_nonneg _)) hbdd hlim

/-! ## Slice differentiability and the boundary-angle degenerate case -/

/-- The `z`-slices of the family are differentiable at every interior point of the quadrant,
from the `C⁴`-regularity hypothesis `RegPkgMin.c4`. -/
private lemma slice_differentiableAt {g : Work.FTS.Galerkin.Fam}
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0)
    {τ x θ : ℝ} (hτ : 0 ≤ τ) (hx : 0 < x) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    DifferentiableAt ℝ (fun z => g z θ τ) x := by
  have hmem : (x, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hx, hθ0, hθ1⟩
  have hopen : Work.FTS.EllipticEst.Q0 ∈ 𝓝 (x, θ) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem
  have hca : ContDiffAt ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (x, θ) :=
    (hc4 τ hτ).contDiffAt hopen
  have hpd : DifferentiableAt ℝ (Function.uncurry (Work.FTS.Galerkin.slice g τ)) (x, θ) :=
    hca.differentiableAt (by norm_num)
  have hf : DifferentiableAt ℝ (fun z : ℝ => (z, θ)) x :=
    differentiableAt_id.prodMk (differentiableAt_const θ)
  have hcomp := hpd.comp x hf
  simpa only [Function.comp_def, Function.uncurry_apply_pair, Work.FTS.Galerkin.slice_apply]
    using hcomp

/-- On the two boundary angles `θ = 0, π/2` the sanitised family vanishes identically in
`(z, τ)` (the boundary values of `g` vanish by `RegPkgMin.vanish`, and the right-Taylor
extension reproduces them). -/
private lemma gS_tauExt_eq_zero_of_boundary {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hvan : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z →
      g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    {θ : ℝ} (hθ : θ = 0 ∨ θ = Real.pi / 2) :
    ∀ z s : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s = 0 := by
  intro z s
  rcases hθ with rfl | rfl
  · by_cases hz : 0 < z
    · have hb : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ Real.pi / 2 := ⟨le_rfl, by positivity⟩
      simp only [Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hb, Work.FTS.FinalV2.tauExt]
      by_cases hs : s < 0
      · rw [ite_eq_left hs]
        have hv : g z 0 0 = 0 := (hvan 0 le_rfl z hz.le).1
        have h0mem : (0 : ℝ) ∈ Set.Ici 0 := by simp
        have hd : derivWithin (fun t => g z 0 t) (Set.Ici 0) 0 = 0 := by
          have he : Set.EqOn (fun t => g z 0 t) (fun _ : ℝ => (0 : ℝ)) (Set.Ici 0) :=
            fun t ht => (hvan t ht z hz.le).1
          rw [derivWithin_congr he (he h0mem)]
          simp
        rw [hv, hd]
        ring
      · rw [ite_eq_right hs]
        exact (hvan s (not_lt.mp hs) z hz.le).1
    · simp only [Work.FTS.FinalV2.gS, ite_eq_right hz]
  · by_cases hz : 0 < z
    · have hb : (0 : ℝ) ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ Real.pi / 2 := ⟨by positivity, le_rfl⟩
      simp only [Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hb, Work.FTS.FinalV2.tauExt]
      by_cases hs : s < 0
      · rw [ite_eq_left hs]
        have hv : g z (Real.pi / 2) 0 = 0 := (hvan 0 le_rfl z hz.le).2
        have h0mem : (0 : ℝ) ∈ Set.Ici 0 := by simp
        have hd : derivWithin (fun t => g z (Real.pi / 2) t) (Set.Ici 0) 0 = 0 := by
          have he : Set.EqOn (fun t => g z (Real.pi / 2) t) (fun _ : ℝ => (0 : ℝ)) (Set.Ici 0) :=
            fun t ht => (hvan t ht z hz.le).2
          rw [derivWithin_congr he (he h0mem)]
          simp
        rw [hv, hd]
        ring
      · rw [ite_eq_right hs]
        exact (hvan s (not_lt.mp hs) z hz.le).2
    · simp only [Work.FTS.FinalV2.gS, ite_eq_right hz]

/-- If the `θ`-slice vanishes identically then the target function vanishes identically. -/
private lemma tendsto_deriv_of_slice_eq_zero {h : Work.FTS.Galerkin.Fam} {θ : ℝ}
    (hz : ∀ z s : ℝ, h z θ s = 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => h z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
  have hG : (fun z : ℝ => deriv (fun s => h z θ s) 0) = fun _ => (0 : ℝ) := by
    funext z
    have h1 : (fun s => h z θ s) = fun _ => (0 : ℝ) := funext (fun s => hz z s)
    rw [h1]
    exact deriv_const 0 0
  have hfinal : (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => h z θ s) 0) p.1)
      = fun _ => (0 : ℝ) := by
    rw [hG]
    funext p
    exact deriv_const p.1 0
  rw [hfinal]
  exact tendsto_const_nhds

/-- `z^{3/2} = √z · z`. -/
private lemma rpow_three_halves (x : ℝ) (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = Real.sqrt x * x := by
  rw [show (3 : ℝ) / 2 = 1 / 2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow]

/-! ## The interior estimate -/

/-- **The interior case**: for `0 < θ < π/2`, the difference-quotient argument described in the
module docstring.  `hgh` records that the sanitised family agrees with `g` on the closed quadrant
at nonnegative times, `hc4` the `C⁴`-regularity of the slices, `hdiff` the two-sided `τ`
differentiability at `τ = 0`, and `hwC` the `hw` estimate. -/
private lemma interior_case {h g : Work.FTS.Galerkin.Fam} {C : ℝ} (hC : 0 ≤ C)
    (hgh : ∀ z θ τ : ℝ, 0 < z → 0 ≤ θ → θ ≤ Real.pi / 2 → 0 ≤ τ → h z θ τ = g z θ τ)
    (hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0)
    (hdiff : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun s => h z θ s) 0)
    (hwC : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ b a : ℕ, a + b ≤ 1 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'|)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => h z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0 : ℝ)) Set.univ)) (nhds 0) := by
  set F : ℝ → ℝ → ℝ :=
    (fun i z => if 0 < i ∧ i ≤ 1 then (h z θ i - h z θ 0) / i else 0) with hF
  -- the slices of `g` are differentiable in `z` at interior points of the quadrant
  have hslicei : ∀ i : ℝ, 0 < i → ∀ x ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z => g z θ i) x :=
    fun i hi x hx => slice_differentiableAt hc4 hi.le hx hθ0 hθ1
  have hslice0 : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun z => g z θ 0) x :=
    fun x hx => slice_differentiableAt hc4 le_rfl hx hθ0 hθ1
  -- (1) the difference quotients are differentiable on `(0,∞)`
  have hFdiff : ∀ i, ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (F i) x := by
    intro i x hx
    by_cases hi : 0 < i ∧ i ≤ 1
    · have hFi : F i = fun z => (h z θ i - h z θ 0) / i := by
        funext z; rw [hF]; exact ite_eq_left hi
      rw [hFi]
      have h1 : DifferentiableAt ℝ (fun z => h z θ i) x := by
        refine (hslicei i hi.1 x hx).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
        exact hgh z θ i hz hθ0.le hθ1.le hi.1.le
      have h2 : DifferentiableAt ℝ (fun z => h z θ 0) x := by
        refine (hslice0 x hx).congr_of_eventuallyEq ?_
        filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
        exact hgh z θ 0 hz hθ0.le hθ1.le le_rfl
      exact (h1.sub h2).div_const i
    · have hFi : F i = fun _ => (0 : ℝ) := by
        funext z; rw [hF]; exact ite_eq_right hi
      rw [hFi]
      exact differentiableAt_const 0
  -- (2) the derivative bound `|deriv (F i) x| ≤ C √x`
  have hFbnd : ∀ i, ∀ x ∈ Set.Ioi (0 : ℝ), |deriv (F i) x| ≤ C * Real.sqrt x := by
    intro i x hx
    by_cases hi : 0 < i ∧ i ≤ 1
    · have hFi : F i = fun z => (h z θ i - h z θ 0) / i := by
        funext z; rw [hF]; exact ite_eq_left hi
      have hx' : (0 : ℝ) < x := hx
      have h1 : DifferentiableAt ℝ (fun z => g z θ i) x := hslicei i hi.1 x hx
      have h2 : DifferentiableAt ℝ (fun z => g z θ 0) x := hslice0 x hx
      -- identify the derivative of the difference quotient
      have hev : (fun z => (h z θ i - h z θ 0) / i) =ᶠ[𝓝 x]
          fun z => (g z θ i - g z θ 0) / i := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
        rw [hgh z θ i hz hθ0.le hθ1.le hi.1.le, hgh z θ 0 hz hθ0.le hθ1.le le_rfl]
      have hsub : deriv (fun z => g z θ i - g z θ 0) x
          = deriv (fun z => g z θ i) x - deriv (fun z => g z θ 0) x := deriv_sub h1 h2
      have hderiv : deriv (F i) x
          = (deriv (fun z => g z θ i - g z θ 0) x) / i := by
        rw [hFi, hev.deriv_eq, deriv_div_const, hsub]
      -- the `hw` bound, in the form `|mixed ...| ≤ C (x^{3/2}/(1+x)^2) * i`
      have hb := hwC i ⟨hi.1.le, hi.2⟩ 0 ⟨le_rfl, zero_le_one⟩ 1 0 (by norm_num) x θ hx hθ0 hθ1
      rw [sub_zero, abs_of_pos hi.1] at hb
      -- identify `x * deriv (g i - g 0)` with `mixed 1 0 (slice g i - slice g 0)`
      have hmix : Work.Spaces.mixed 1 0
            (Work.FTS.Galerkin.slice g i - Work.FTS.Galerkin.slice g 0) x θ
          = x * deriv (fun z => g z θ i - g z θ 0) x := by
        simp only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_zero, Work.Spaces.Dz, Work.Spaces.pz, Pi.sub_apply,
          Work.FTS.Galerkin.slice_apply]
      have hxabs : |x| = x := abs_of_pos hx
      have hiabs : |i| = i := abs_of_pos hi.1
      have hxne : x ≠ 0 := ne_of_gt hx
      have hine : i ≠ 0 := ne_of_gt hi.1
      have hmain : |deriv (F i) x| = |x * deriv (fun z => g z θ i - g z θ 0) x| / (i * x) := by
        rw [hderiv, abs_div, abs_mul, hxabs, hiabs]
        field_simp
      rw [hmain, ← hmix]
      have hix : 0 < i * x := mul_pos hi.1 hx
      calc |Work.Spaces.mixed 1 0
              (Work.FTS.Galerkin.slice g i - Work.FTS.Galerkin.slice g 0) x θ| / (i * x)
          ≤ (C * (x ^ ((3 : ℝ) / 2) / (1 + x) ^ 2) * i) / (i * x) :=
            div_le_div_of_nonneg_right hb hix.le
        _ = C * (Real.sqrt x / (1 + x) ^ 2) := by
            have h1x : (1 + x) ≠ 0 := by positivity
            have h1x2 : (1 + x) ^ 2 ≠ 0 := pow_ne_zero 2 h1x
            rw [rpow_three_halves x hx]
            field_simp
        _ ≤ C * Real.sqrt x := by
            have hone : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith [sq_nonneg x, hx']
            have hnn : 0 ≤ C * Real.sqrt x := by positivity
            calc C * (Real.sqrt x / (1 + x) ^ 2)
                = C * Real.sqrt x / (1 + x) ^ 2 := by ring
              _ ≤ C * Real.sqrt x / 1 :=
                  div_le_div_of_nonneg_left hnn zero_lt_one hone
              _ = C * Real.sqrt x := by ring
    · have hFi : F i = fun _ => (0 : ℝ) := by
        funext z; rw [hF]; exact ite_eq_right hi
      rw [hFi, deriv_const, abs_zero]
      exact mul_nonneg hC (Real.sqrt_nonneg x)
  -- (3) pointwise convergence of the difference quotients to the `τ`-derivative at `0`
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun i => F i x) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (deriv (fun s => h x θ s) 0)) := by
    intro x hx
    have hslope : Filter.Tendsto (fun t : ℝ => t⁻¹ * (h x θ t - h x θ 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (deriv (fun s => h x θ s) 0)) := by
      have h1 : Filter.Tendsto
          (fun t : ℝ => t⁻¹ • ((fun s => h x θ s) (0 + t) - (fun s => h x θ s) 0))
          (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (deriv (fun s => h x θ s) 0)) :=
        (hdiff x θ hx hθ0 hθ1).hasDerivAt.tendsto_slope_zero
      have h2 := h1.mono_left
        (nhdsWithin_mono 0 (fun t (ht : t ∈ Set.Ioi (0 : ℝ)) => ne_of_gt ht))
      simpa only [zero_add, smul_eq_mul] using h2
    have hi1 : ∀ᶠ i in nhdsWithin (0 : ℝ) (Set.Ioi 0), i ≤ 1 := by
      have hmem : Set.Iio (1 : ℝ) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hmem] with i hi using le_of_lt hi
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hi1] with i hi hi1'
    rw [hF]
    have hicond : 0 < i ∧ i ≤ 1 := ⟨hi, hi1'⟩
    simp only [ite_eq_left hicond, div_eq_inv_mul]
  -- (4) assemble
  have hbound : ∀ x ∈ Set.Ioi (0 : ℝ),
      |deriv (fun z => deriv (fun s => h z θ s) 0) x| ≤ C * Real.sqrt x :=
    deriv_bound_of_pointwise_tendsto (φ := fun x => C * Real.sqrt x)
      (G := fun z => deriv (fun s => h z θ s) 0) hFdiff
      (Real.continuous_sqrt.continuousOn.const_mul C)
      (fun x hx => mul_nonneg hC (Real.sqrt_nonneg x))
      (fun x hx y hy hxy => mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hxy) hC)
      hFbnd hpt
  exact tendsto_deriv_of_abs_le_sqrt hC hbound

/-! ## The target -/

theorem hd1z_limit {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)))
    (hw : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) 1, ∀ τ' ∈ Set.Icc (0:ℝ) 1,
      ∀ b a : ℕ, a + b ≤ 1 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ - Work.FTS.Galerkin.slice g τ') z θ| ≤
          C * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'|) :
    ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto
      (fun p : ℝ × ℝ => deriv (fun z => deriv
        (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) Set.univ)) (nhds 0) := by
  obtain ⟨C, hC, hwC⟩ := hw
  set h : Work.FTS.Galerkin.Fam := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) with hh
  have hc4 : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Galerkin.slice g τ))
      Work.FTS.EllipticEst.Q0 := fun τ hτ => hOK.1.1.c4 τ hτ
  have hvan : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z →
      g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0 := fun τ hτ z hz => hOK.1.1.vanish τ hτ z hz
  have hgh : ∀ z θ τ : ℝ, 0 < z → 0 ≤ θ → θ ≤ Real.pi / 2 → 0 ≤ τ → h z θ τ = g z θ τ := by
    intro z θ τ hz hθ0 hθ1 hτ
    have hb : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := ⟨hθ0, hθ1⟩
    simp only [hh, Work.FTS.FinalV2.gS, ite_eq_left hz, ite_eq_left hb,
      Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
  have hdiff : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      DifferentiableAt ℝ (fun s => h z θ s) 0 := by
    intro z θ hz hθ0 hθ1
    have hmem : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
    exact ((H5 1 one_pos).h0 z θ hz hmem).differentiableAt
  intro θ hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · exact tendsto_deriv_of_slice_eq_zero
      (gS_tauExt_eq_zero_of_boundary hvan (Or.inl h0.symm))
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · exact tendsto_deriv_of_slice_eq_zero
      (gS_tauExt_eq_zero_of_boundary hvan (Or.inr hpi))
  · exact interior_case hC hgh hc4 hdiff hwC h0 hpi

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR1.tau_cluster =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR1.tau_cluster` — the `τ`-regularity cluster of the `R1` block

The target is the pair of `τ`-derivative fields of `RegExportIface.R1Block`
(`hjdt` and `ht0`, at `θ ∈ Iθ` and `τ₀ ∈ Ico 0 (S+1)`) for the sanitised family
`G := gS α (tauExt g)`, from the primitive `R5Parts` data at the horizon `S+1`.

The proof goes through the right-hand side of the fake-time equation
`R τ z θ := dynLin (pExp α) G τ z θ + dynRHS (pExp α) Φ G τ z θ`:

* `R5Parts.hsol`/`h0` identify `∂_τ G` with `R` at every `τ ≥ 0` on the open quadrant, and the
  right-Taylor branch of `tauExt` identifies it with the *right* derivative of `G` at `τ = 0` for
  `τ < 0`; hence `deriv (fun s => G z θ s) s' = R (max s' 0) z θ`;
* `R5Parts.hJ` (the four `Jet`s) + `hmb`/`hmbh` upgrade to a `Jet` of `R` itself
  (`Der.rhs_jet_of_parts`), which by `tauJetMax`/`tauJetTau` is continuous at `z = 0⁺` and from
  the right at `τ = 0`;
* `R5Parts.hRz0` says `R τ 0 θ = 0`;
* on the two angular ends `θ = 0, π/2` the family and its `τ`-derivative vanish identically
  (`DynOK'.1.1.vanish`), so both limits are trivial there.
-/

namespace Work.FTS_RegExport.RXR1

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-! ## `Jet`-continuity at `z = 0⁺` and from the right at `τ = 0` -/

/-- **A `Jet` is right-continuous at `τ = 0`.**  From the `τ`-modulus of `Jet.tmod` and the
continuity of `t ↦ N·t^α` at `0` (`α > 0`). -/
theorem tauJetTau {α T N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α T N h) (hα : 0 < α) (hT : 0 < T)
    {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Filter.Tendsto (fun τ => h z θ τ) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (h z θ 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hN0 : 0 ≤ N := H.1
  have hcont : ContinuousAt (fun t : ℝ => N * t ^ α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
  have htend : Filter.Tendsto (fun t : ℝ => N * t ^ α) (𝓝 (0:ℝ)) (𝓝 0) := by
    have h := hcont.tendsto
    have h0 : N * (0:ℝ) ^ α = 0 := by rw [Real.zero_rpow hα.ne', mul_zero]
    rwa [h0] at h
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (Metric.tendsto_nhds.mp htend ε hε)
  have hbound : ∀ s : ℝ, 0 ≤ s → s < δ₁ → N * s ^ α < ε := by
    intro s hs0 hs1
    have hsball : s ∈ Metric.ball (0:ℝ) δ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]; exact hs1
    have h := hδ₁ hsball
    simp only [Set.mem_ofPred_eq] at h
    rw [Real.dist_eq, sub_zero] at h
    rwa [abs_of_nonneg (mul_nonneg hN0 (Real.rpow_nonneg hs0 α))] at h
  refine ⟨min δ₁ T, lt_min hδ₁pos hT, ?_⟩
  intro τ hτ hdist
  have hτ0 : 0 ≤ τ := le_of_lt hτ
  have hdist_eq : dist τ (0:ℝ) = |τ - 0| := Real.dist_eq τ 0
  have hslt : |τ - 0| < δ₁ := by
    rw [← hdist_eq]
    exact lt_of_lt_of_le hdist (min_le_left δ₁ T)
  have hτT : τ ≤ T := by
    have h2 := lt_of_lt_of_le hdist (min_le_right δ₁ T)
    rw [hdist_eq, sub_zero, abs_of_nonneg hτ0] at h2
    exact h2.le
  have hb := H.tmod (z := z) (θ := θ) (τ := τ) (τ' := 0) hz hθ ⟨hτ0, hτT⟩ ⟨le_rfl, hT.le⟩
  rw [Real.dist_eq]
  calc |h z θ τ - h z θ 0| ≤ N * |τ - 0| ^ α := hb
    _ < ε := hbound _ (abs_nonneg _) hslt

/-- **A `Jet` is continuous at `z = 0⁺`** (jointly in `τ`): the right-hand side of the fake-time
equation tends to its value at `z = 0` as `(z, τ) → (0⁺, τ₀)`, `τ ∈ (-∞,T]`. -/
theorem tauJetMax {α T N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α T N h) (hα : 0 < α) (hT : 0 < T)
    {θ τ₀ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hτ₀ : τ₀ ∈ Set.Ico 0 T) :
    Filter.Tendsto (fun p : ℝ × ℝ => h p.1 θ (max p.2 0))
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0 : ℝ)) (Set.univ)))
      (nhds (h 0 θ τ₀)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hN0 : 0 ≤ N := H.1
  have hcont : ContinuousAt (fun t : ℝ => N * t ^ α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 α (Or.inr hα.le))
  have htend : Filter.Tendsto (fun t : ℝ => N * t ^ α) (𝓝 (0:ℝ)) (𝓝 0) := by
    have h := hcont.tendsto
    have h0 : N * (0:ℝ) ^ α = 0 := by rw [Real.zero_rpow hα.ne', mul_zero]
    rwa [h0] at h
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp (Metric.tendsto_nhds.mp htend ε hε)
  have hbound : ∀ s : ℝ, 0 ≤ s → s < δ₁ → N * s ^ α < ε := by
    intro s hs0 hs1
    have hsball : s ∈ Metric.ball (0:ℝ) δ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs0]; exact hs1
    have h := hδ₁ hsball
    simp only [Set.mem_ofPred_eq] at h
    rw [Real.dist_eq, sub_zero] at h
    rwa [abs_of_nonneg (mul_nonneg hN0 (Real.rpow_nonneg hs0 α))] at h
  have hτ₀0 : 0 ≤ τ₀ := hτ₀.1
  have hT0 : 0 < T - τ₀ := by linarith [hτ₀.2]
  refine ⟨min (δ₁ / 2) ((T - τ₀) / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro p hp hdist
  have hp1 : 0 < p.1 := hp.1
  have hd1 : dist p ((0:ℝ), τ₀) < δ₁ / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : dist p ((0:ℝ), τ₀) < (T - τ₀) / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hdist_eq : dist p ((0:ℝ), τ₀) = max |p.1| |p.2 - τ₀| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
  have h1 : |p.1| ≤ dist p ((0:ℝ), τ₀) := by rw [hdist_eq]; exact le_max_left _ _
  have h2 : |p.2 - τ₀| ≤ dist p ((0:ℝ), τ₀) := by rw [hdist_eq]; exact le_max_right _ _
  have h3 : |max p.2 0 - τ₀| ≤ dist p ((0:ℝ), τ₀) := by
    rcases le_or_gt 0 p.2 with h2' | h2'
    · calc |max p.2 0 - τ₀| = |p.2 - τ₀| := by rw [max_eq_left h2']
        _ ≤ dist p ((0:ℝ), τ₀) := h2
    · have hmax0 : max p.2 0 = 0 := max_eq_right h2'.le
      have h4 : τ₀ ≤ dist p ((0:ℝ), τ₀) := by
        rw [hdist_eq]
        have h8 : τ₀ ≤ |p.2 - τ₀| := by
          rw [abs_sub_comm, abs_of_pos (by linarith : (0:ℝ) < τ₀ - p.2)]
          linarith
        exact le_trans h8 (le_max_right |p.1| |p.2 - τ₀|)
      rw [hmax0, zero_sub, abs_neg, abs_of_nonneg hτ₀.1]
      exact h4
  have hmaxT : max p.2 0 ≤ T := by
    have h6 : |p.2 - τ₀| < (T - τ₀) / 2 := lt_of_le_of_lt h2 hd2
    have h7 : p.2 - τ₀ ≤ |p.2 - τ₀| := le_abs_self _
    have h5 : p.2 < T := by linarith
    exact max_le h5.le hT.le
  have hsum : |p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀| ≤ 2 * dist p ((0:ℝ), τ₀) := by
    simp only [sub_zero, sub_self, abs_zero, add_zero]
    linarith [h1, h3]
  have hsum0 : 0 ≤ |p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀| := by positivity
  have hsumlt : |p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀| < δ₁ := by
    linarith [hsum, hd1]
  have hholder := H.2.2 p.1 0 θ θ (max p.2 0) τ₀ (le_of_lt hp1) le_rfl hθ hθ
    ⟨le_max_right _ _, hmaxT⟩ ⟨hτ₀.1, le_of_lt hτ₀.2⟩
  rw [Real.dist_eq]
  calc |h p.1 θ (max p.2 0) - h 0 θ τ₀|
      ≤ N * (|p.1 - 0| + |θ - θ| + |max p.2 0 - τ₀|) ^ α := hholder
    _ < ε := hbound _ hsum0 hsumlt

/-! ## The general reduction -/

/-- **The general reduction.**  For a family `G` carrying the primitive `R5` data on `[0,T]`,
which vanishes identically on the two angular ends, and whose negative-`τ` branch is its own
right-Taylor jet, the `τ`-derivative of `G` has the `R1` limits: it tends to `0` as
`(z,τ) → (0⁺,τ₀)` and it is right-continuous at `τ = 0`. -/
theorem tau_of_r5 {α T : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hT : 0 < T)
    {G Φ : Work.FTS.Galerkin.Fam} (hR5 : Work.FTS.RegPkgGal.R5Parts α T G Φ)
    (hend : ∀ z θ, 0 < z → θ ∈ Work.Spaces.Iθ → (θ = 0 ∨ θ = π / 2) → ∀ s, G z θ s = 0)
    (haff : ∀ z θ s, 0 < z → θ ∈ Work.Spaces.Iθ → s < 0 →
      G z θ s = G z θ 0 + s * derivWithin (fun u => G z θ u) (Set.Ici 0) 0) :
    (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 T,
      Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => G p.1 θ s) p.2)
        (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun τ => deriv (fun s => G z θ s) τ)
        (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => G z θ s) 0))) := by
  obtain ⟨NJ, hL, hN₀, hN, hNs⟩ := hR5.hJ
  obtain ⟨Nc, hJet⟩ :=
    Work.FTS.RegPkgGal.Der.rhs_jet_of_parts hα hα13 hT hL hN₀ hN hNs hR5.hmb hR5.hmbh
  set R : ℝ → ℝ → ℝ → ℝ := fun τ z θ =>
      Work.FTS.Galerkin.dynLin (Work.FTS.Regularity.pExp α) G τ z θ
        + Work.FTS.Galerkin.dynRHS (Work.FTS.Regularity.pExp α) Φ G τ z θ with hRdef
  have hJetR : Work.FTS.Regularity.Jet α T Nc (fun z θ τ => R τ z θ) := hJet
  have hRz0 : ∀ τ ∈ Set.Icc 0 T, ∀ θ ∈ Work.Spaces.Iθ, R τ 0 θ = 0 := hR5.hRz0
  -- ### The derivative of `G` is the right-hand side, at `max s' 0`
  have hderiv_int : ∀ θ ∈ Work.Spaces.Iθ, 0 < θ → θ < π / 2 → ∀ z : ℝ, 0 < z → ∀ s' : ℝ,
      deriv (fun s => G z θ s) s' = R (max s' 0) z θ := by
    intro θ hθ hθ0 hθ1 z hz s'
    have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
    rcases lt_trichotomy s' 0 with hs | hs | hs
    · -- `s' < 0`: the affine branch of the right-Taylor extension
      have hev : (fun u : ℝ => G z θ u) =ᶠ[𝓝 s']
          (fun u => G z θ 0 + u * derivWithin (fun u => G z θ u) (Set.Ici 0) 0) := by
        filter_upwards [isOpen_Iio.mem_nhds hs] with u hu
        exact haff z θ u hz hθ hu
      rw [hev.deriv_eq, max_eq_right hs.le]
      have hd : HasDerivAt (fun u : ℝ =>
            G z θ 0 + u * derivWithin (fun u => G z θ u) (Set.Ici 0) 0)
          (derivWithin (fun u => G z θ u) (Set.Ici 0) 0) s' := by
        simpa using (((hasDerivAt_id s').mul_const
          (derivWithin (fun u => G z θ u) (Set.Ici 0) 0)).const_add (G z θ 0))
      rw [hd.deriv]
      exact ((hR5.h0 z θ hz hzθ).hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ici 0)
    · -- `s' = 0`: the two-sided equation at `τ = 0`
      subst hs; rw [max_self]; exact (hR5.h0 z θ hz hzθ).deriv
    · -- `s' > 0`: the dynamic equation
      rw [max_eq_left hs.le]
      exact ((hR5.hsol z θ s' hs.le hzθ).hasDerivAt (Ici_mem_nhds hs)).deriv
  constructor
  · -- ### `hjdt`: the joint limit at `z = 0⁺`
    intro θ hθ τ₀ hτ₀
    by_cases hθe : θ = 0 ∨ θ = π / 2
    · -- the angular ends: everything vanishes identically
      refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0:ℝ)))
      filter_upwards [self_mem_nhdsWithin] with p hp
      rw [show (fun s => G p.1 θ s) = fun _ => (0:ℝ) from funext (hend p.1 θ hp.1 hθ hθe),
        deriv_const]
    · push Not at hθe
      have hh0 : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθe.1)
      have hh1 : θ < π / 2 := lt_of_le_of_ne hθ.2 hθe.2
      have hlim := tauJetMax hJetR hα hT hθ hτ₀
      rw [hRz0 τ₀ ⟨hτ₀.1, le_of_lt hτ₀.2⟩ θ hθ] at hlim
      refine Filter.Tendsto.congr' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact (hderiv_int θ hθ hh0 hh1 p.1 hp.1 p.2).symm
  · -- ### `ht0`: right-continuity of `∂_τ G` at `τ = 0`
    intro θ hθ z hz
    by_cases hθe : θ = 0 ∨ θ = π / 2
    · have hzero : ∀ τ, deriv (fun s => G z θ s) τ = 0 := by
        intro τ
        rw [show (fun s => G z θ s) = fun _ => (0:ℝ) from funext (hend z θ hz hθ hθe),
          deriv_const]
      rw [hzero 0]
      refine Filter.Tendsto.congr'
        (Filter.Eventually.of_forall (fun τ => (hzero τ).symm)) tendsto_const_nhds
    · push Not at hθe
      have hh0 : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθe.1)
      have hh1 : θ < π / 2 := lt_of_le_of_ne hθ.2 hθe.2
      have hval : deriv (fun s => G z θ s) 0 = R 0 z θ := by
        rw [hderiv_int θ hθ hh0 hh1 z hz 0, max_self]
      have hlim := tauJetTau hJetR hα hT hz.le hθ
      rw [hval]
      refine Filter.Tendsto.congr' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      rw [hderiv_int θ hθ hh0 hh1 z hz τ, max_eq_left hτ.le]

theorem tau_cluster {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ,
      g z θ 0 = Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hSt1 : ∀ S > 0,
      Work.FTS.RegPkgGal.St1Class α S (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g))) :
    ∀ S > 0,
      (∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
        Filter.Tendsto (fun p : ℝ × ℝ =>
            deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) p.1 θ s) p.2)
          (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)) ∧
      (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun τ =>
            deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) τ)
          (nhdsWithin 0 (Set.Ioi (0:ℝ)))
          (nhds (deriv (fun s => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ s) 0))) := by
  intro S hS
  set G : Work.FTS.Galerkin.Fam := Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) with hGdef
  set ΦΦ : Work.FTS.Galerkin.Fam :=
    Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) with hΦdef
  have hR5 : Work.FTS.RegPkgGal.R5Parts α (S + 1) G ΦΦ := by
    rw [hGdef, hΦdef]; exact H5 (S + 1) (by linarith)
  refine tau_of_r5 hα hα13 (by linarith : (0:ℝ) < S + 1) hR5 ?_ ?_
  · -- the angular ends: `G` vanishes identically (from `DynOK'.1.1.vanish`)
    intro z θ hz hθ hθe s
    have hv := hOK.1.1.vanish
    have hg0 : ∀ u, 0 ≤ u → g z θ u = 0 := by
      intro u hu
      rcases hθe with h | h
      · rw [h]; exact (hv u hu z hz.le).1
      · rw [h]; exact (hv u hu z hz.le).2
    have hG_eq : G z θ s = Work.FTS.FinalV2.tauExt g z θ s := by
      rw [hGdef]
      simp only [Work.FTS.FinalV2.gS]
      rw [if_pos hz, if_pos ⟨hθ.1, hθ.2⟩]
    rw [hG_eq]
    by_cases hs : s < 0
    · rw [Work.FTS.FinalV2.tauExt_of_neg g hs]
      have hdw : derivWithin (fun u => g z θ u) (Set.Ici 0) 0 = 0 := by
        have h1 : derivWithin (fun u => g z θ u) (Set.Ici (0:ℝ)) 0
            = derivWithin (Function.const ℝ (0:ℝ)) (Set.Ici 0) 0 :=
          derivWithin_congr (fun u hu => hg0 u hu) (hg0 0 le_rfl)
        rw [h1, derivWithin_const]
        simp
      rw [hg0 0 le_rfl, hdw]; ring
    · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hs)]
      exact hg0 s (not_lt.mp hs)
  · -- the affine branch of `G` for `s < 0` is the right-Taylor jet of `g`
    intro z θ s hz hθ hs
    have hθ0 : 0 ≤ θ := hθ.1
    have hθ1 : θ ≤ π / 2 := hθ.2
    have hG_eq : ∀ u : ℝ, G z θ u = Work.FTS.FinalV2.tauExt g z θ u := by
      intro u
      rw [hGdef]
      simp only [Work.FTS.FinalV2.gS]
      rw [if_pos hz, if_pos ⟨hθ0, hθ1⟩]
    have hG0 : G z θ 0 = g z θ 0 := by
      rw [hG_eq 0, Work.FTS.FinalV2.tauExt_of_nonneg g le_rfl]
    have hdc : derivWithin (fun u => g z θ u) (Set.Ici 0) 0
        = derivWithin (fun u => G z θ u) (Set.Ici 0) 0 := by
      refine derivWithin_congr (f₁ := fun u => g z θ u) (f := fun u => G z θ u) ?_ ?_
      · intro u hu
        exact ((hG_eq u).trans (Work.FTS.FinalV2.tauExt_of_nonneg g hu)).symm
      · exact hG0.symm
    rw [hG_eq s, Work.FTS.FinalV2.tauExt_of_neg g hs, hG0, hdc]

end Work.FTS_RegExport.RXR1
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.omega_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

/-! ## Elementary facts about the angular factor `Γ(θ) = (sinθ·cos²θ)^α` -/

/-- `Γ` is positive on the open angular interval. -/
lemma Gamma_pos (α θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    0 < Work.FTS.Regularity.Gamma α θ := by
  refine Real.rpow_pos_of_pos ?_ α
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ1, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩
  positivity

/-- `∂_θΓ = Γ·(2α·c2m θ)/sin 2θ` on the open angular interval. -/
lemma hasDerivAt_Gamma (α θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun θ' : ℝ => Work.FTS.Regularity.Gamma α θ')
      (Work.FTS.Regularity.Gamma α θ
        * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [hθ1, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩
  have hφpos : 0 < Real.sin θ * Real.cos θ ^ 2 := by positivity
  have hφ : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ' ^ 2)
      (Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))) θ :=
    (Real.hasDerivAt_sin θ).mul ((Real.hasDerivAt_cos θ).fun_pow 2)
  have hΓ := hφ.rpow_const (p := α) (Or.inl (ne_of_gt hφpos))
  refine hΓ.congr_deriv ?_
  have hA : Real.cos θ * Real.cos θ ^ 2
        + Real.sin θ * (2 * Real.cos θ ^ (2 - 1) * (-Real.sin θ))
      = Real.cos θ * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    norm_num
    ring
  have hpow : Work.FTS.Regularity.Gamma α θ
      = (Real.sin θ * Real.cos θ ^ 2) ^ (α - 1) * (Real.sin θ * Real.cos θ ^ 2) := by
    show (Real.sin θ * Real.cos θ ^ 2) ^ α = _
    conv_lhs => rw [show α = (α - 1) + 1 by ring]
    rw [Real.rpow_add hφpos, Real.rpow_one]
  have hsin2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hc2m : Work.Construction.c2m θ = Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2 := by
    rw [Work.Construction.c2m, Real.cos_two_mul']
    ring
  rw [hA, hpow, hsin2, hc2m]
  have hs0 : Real.sin θ ≠ 0 := ne_of_gt hs
  have hc0 : Real.cos θ ≠ 0 := ne_of_gt hc
  field_simp

/-! ## The two partial derivatives of `ω` -/

/-- `∂_z ω α z θ = ω α z θ · 2/(z(1+z))` for `z > 0`. -/
lemma hasDerivAt_omega_z (α z θ : ℝ) (hz : 0 < z) :
    HasDerivAt (fun z' => Work.FTS.RegExportIface.ω α z' θ)
      (Work.FTS.RegExportIface.ω α z θ * (2 / (z * (1 + z)))) z := by
  have hbase : HasDerivAt (fun z' : ℝ => z' ^ 2 / (1 + z') ^ 2) (2 * z / (1 + z) ^ 3) z := by
    have hnum : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z ^ (2 - 1) * 1) z := by
      simpa using hasDerivAt_pow 2 z
    have hden : HasDerivAt (fun z' : ℝ => (1 + z') ^ 2)
        (2 * (1 + z) ^ (2 - 1) * (0 + 1)) z := by
      have hlin : HasDerivAt (fun z' : ℝ => 1 + z') (0 + 1) z :=
        (hasDerivAt_const z (1:ℝ)).add (hasDerivAt_id z)
      exact hlin.fun_pow 2
    have hpos : (1 + z : ℝ) ^ 2 ≠ 0 := by positivity
    have hdiv := hnum.div hden hpos
    exact hdiv.congr_deriv (by norm_num; field_simp; ring)
  have h1 : HasDerivAt (fun z' : ℝ => Work.FTS.Regularity.Gamma α θ * (z' ^ 2 / (1 + z') ^ 2))
      (Work.FTS.Regularity.Gamma α θ * (2 * z / (1 + z) ^ 3)) z := hbase.const_mul _
  have h2 : HasDerivAt (fun z' : ℝ => z' ^ 2 * Work.FTS.Regularity.Gamma α θ / (1 + z') ^ 2)
      (Work.FTS.Regularity.Gamma α θ * (2 * z / (1 + z) ^ 3)) z :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z' => by ring))
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : (1 + z : ℝ) ≠ 0 := by positivity
  exact h2.congr_deriv (by simp only [Work.FTS.RegExportIface.ω]; field_simp)

/-- `∂_θ ω α z θ = ω α z θ · 2α·c2m θ / sin 2θ` for `0 < θ < π/2`. -/
lemma hasDerivAt_omega_theta (α z θ : ℝ) (_hα : 0 < α) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun θ' => Work.FTS.RegExportIface.ω α z θ')
      (Work.FTS.RegExportIface.ω α z θ
        * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ))) θ := by
  have hbase := hasDerivAt_Gamma α θ hθ0 hθ1
  have h1 : HasDerivAt
      (fun θ' : ℝ => z ^ 2 / (1 + z) ^ 2 * Work.FTS.Regularity.Gamma α θ')
      (z ^ 2 / (1 + z) ^ 2
        * (Work.FTS.Regularity.Gamma α θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))) θ :=
    hbase.const_mul _
  have h2 : HasDerivAt
      (fun θ' : ℝ => z ^ 2 * Work.FTS.Regularity.Gamma α θ' / (1 + z) ^ 2)
      (z ^ 2 / (1 + z) ^ 2
        * (Work.FTS.Regularity.Gamma α θ
          * (2 * α * Work.Construction.c2m θ / Real.sin (2 * θ)))) θ :=
    h1.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun θ' => by ring))
  exact h2.congr_deriv (by simp only [Work.FTS.RegExportIface.ω]; ring)

/-- Elementary facts about the weight `ω α z θ = z²·(sinθ·cos²θ)^α/(1+z)²` of the
self-similar variables (`Work.FTS.RegExportIface.ω`, whose angular factor is
`Work.FTS.Regularity.Gamma α θ = (sinθ·cos²θ)^α`; note `Work.Spaces.pExp α = 3α`, so this is
`Work.Spaces.Gam (pExp α) θ`), for `α > 0`, `z > 0`, `0 < θ < π/2`:

* `ω α z θ > 0`;
* `∂_z ω = ω·2/(z(1+z))`;
* `∂_θ ω = ω·2α·c2m(θ)/sin 2θ`, where `c2m θ = cos 2θ − sin²θ = cos²θ − 2 sin²θ`
  (`Work.Construction.c2m`).

The last identity: `∂_θΓ = α·Γ·(cos²θ − 2sin²θ)/(sinθ cosθ) = Γ·α·c2m θ/(sinθ cosθ)`,
and `1/(sinθcosθ) = 2/sin 2θ`. -/
theorem omega_facts (α : ℝ) (hα : 0 < α) :
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 < Work.FTS.RegExportIface.ω α z θ) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun z' => Work.FTS.RegExportIface.ω α z' θ)
        (Work.FTS.RegExportIface.ω α z θ * (2 / (z * (1 + z)))) z) ∧
    (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun θ' => Work.FTS.RegExportIface.ω α z θ')
        (Work.FTS.RegExportIface.ω α z θ * (2 * α * Work.Construction.c2m θ
          / Real.sin (2 * θ))) θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z θ hz hθ0 hθ1
    have hG : 0 < Work.FTS.Regularity.Gamma α θ := Gamma_pos α θ hθ0 hθ1
    rw [show Work.FTS.RegExportIface.ω α z θ
        = z ^ 2 * Work.FTS.Regularity.Gamma α θ / (1 + z) ^ 2 from rfl]
    positivity
  · intro z θ hz _ _
    exact hasDerivAt_omega_z α z θ hz
  · intro z θ _ hθ0 hθ1
    exact hasDerivAt_omega_theta α z θ hα hθ0 hθ1

end Work.FTS_RegExport.RXT
end
