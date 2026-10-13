/-
# `Work.FTS.MeridianDyn.Main` — the dynamic meridian bridge

The main theorem of the area: **the fake-time dynamic equation implies the meridian scalar
equation for the meridian pair of the physical reconstruction**, i.e. design §3 item 9,

  `Work.FTS.MeridianDyn.meridianEq_of_dynEq`.

## The statement

From

* a solution `(Φ, g)` of the dynamic modulated problem (`Work.FTS.Galerkin.IsDynGSolWith`, i.e. the
  elliptic law together with the fake-time equation `IsDynEqOn`),
* the regularity package `Work.FTS.Galerkin.RegPkg (pExp α) g`,
* interior `C²` of `Φ` on the quadrant and oddness of `Φ` in `θ`,
* the static derivation data `Work.FTS.MeridianDyn.ProfDerivData`,
* the clock data (`C.A = 2·A_v`, `A' = -(1+μ)A`, `B' = -(1-μ)B`, `B > 0`, `C.mu = muDyn`),

(no hypothesis on the `L₁₂`-zero-mode of the transport term: since the sign fix
`Work.Construction.mufunS` the delivered modulation constant agrees with the paper's *by
definition*, `Work.FTS.MeridianDyn.muDyn_eq_muDynStar`) the meridian pair of the reconstruction,

  `W(r,z,t) = merProfile α A B g C r z t`,   `ψ(r,z,t) = merPsi (3α) A B Φ C r z t`,

satisfies the **meridian scalar equation** off the axis and off the equatorial plane, for every
`t ∈ (0, C.T)`:

  `∂ₜW + (∂_zψ)·∂_rW + ( -(ψ/r) - ∂_rψ )·∂_zW = ((∂_zψ)/r)·W`.

The two halves are:

* `z > 0`: the pointwise identity `meridianResid_dyn` (residual = `a·σ'·(E)`) composed
  with the profile equation `(E)` (`DynEqF_of_isDynEqOn_odd`) and the clock normalisation
  `C.A = 2·A_v`;
* `z < 0`: the parity of the residual (`Odd.meridianResid_odd_win`), using the odd extension in
  `θ` of the profile and the oddness of `Φ`.

The sign convention of correction 1 is handled by `MeridianEqOn.neg_left` (the physical vorticity
is `−physOmega`), so the result here transports to the physical pair with one rewrite.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.FTS.MeridianDyn.ResidDyn
import Submission.Work.FTS.MeridianDyn.DynEqF
import Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd_win
import Submission.Work.FTS.MeridianDyn.Clock.amplitude_hasDerivAt
import Submission.Work.FTS.MeridianDyn.Clock.scale_hasDerivAt
import Submission.Work.FTS.MeridianDyn.Smooth.profFamOdd_contDiffAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set
open scoped Topology

namespace Work.FTS.MeridianDyn

set_option autoImplicit false

/-! ## Parity -/

/-- The full profile extended oddly in `θ` is odd in its angular argument, off `θ = 0`. -/
theorem profFamOdd_neg {α : ℝ} {g : Fam} {Z Θ σ : ℝ} (hΘ : Θ ≠ 0) :
    profFamOdd α g Z (-Θ) σ = -profFamOdd α g Z Θ σ := by
  by_cases h : 0 ≤ Θ
  · have h' : ¬ (0 ≤ -Θ) := by
      intro hcon
      exact hΘ (le_antisymm (neg_nonneg.mp hcon) h)
    have hprof : profFamOdd α g Z Θ σ
        = Work.Construction.Fstar α Z Θ + g Z Θ σ := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile_of_nonneg h]
      rfl
    have hprof' : profFamOdd α g Z (-Θ) σ
        = -(Work.Construction.Fstar α Z Θ + g Z Θ σ) := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile, if_neg h']
      simp
    rw [hprof, hprof']
  · have h' : 0 ≤ -Θ := by linarith
    have hprof : profFamOdd α g Z (-Θ) σ
        = Work.Construction.Fstar α Z (-Θ) + g Z (-Θ) σ := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile_of_nonneg h']
      rfl
    have hprof' : profFamOdd α g Z Θ σ
        = -(Work.Construction.Fstar α Z (-Θ) + g Z (-Θ) σ) := by
      rw [profFamOdd_apply, Work.ConstructionInstance.profile, if_neg h]
      simp
    rw [hprof, hprof']
    ring

/-- The polar radius is even in the axial variable. -/
theorem rhoP_neg (r z : ℝ) : Work.Cyl.rhoP r (-z) = Work.Cyl.rhoP r z := by
  rw [Work.Cyl.rhoP, Work.Cyl.rhoP]
  congr 1
  ring

/-- The polar angle is odd in the axial variable. -/
theorem thetaP_neg (r z : ℝ) : Work.Cyl.thetaP r (-z) = -Work.Cyl.thetaP r z := by
  rw [Work.Cyl.thetaP, Work.Cyl.thetaP, neg_div, Real.arctan_neg]

/-- The polar angle only vanishes on the equatorial plane. -/
theorem thetaP_ne_zero {r z : ℝ} (hr : r ≠ 0) (hz : z ≠ 0) : Work.Cyl.thetaP r z ≠ 0 := by
  intro h0
  have h1 : Real.tan (Work.Cyl.thetaP r z) = 0 := by rw [h0, Real.tan_zero]
  rw [Work.Cyl.thetaP, Real.tan_arctan] at h1
  rcases div_eq_zero_iff.mp h1 with h | h
  · exact hz h
  · exact hr h

/-! ## The main theorem -/

/-- **The dynamic meridian bridge.**  The fake-time dynamic equation for `(Φ, g)` implies the
meridian scalar equation for the meridian pair of the reconstruction, on the time window
`(0, C.T)`, off the axis and off the equatorial plane. -/
theorem meridianEq_of_dynEq {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {A B : ℝ → ℝ} {Φ g : Fam} {C : Work.FTS.Physical.PhysClock}
    (hsol : Galerkin.IsDynGSolWith (Elliptic.IsBslSol (Regularity.pExp α))
      (Regularity.pExp α) Φ g)
    (hreg : Galerkin.RegPkg (Regularity.pExp α) g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd)
    (hΦodd : ∀ τ : ℝ, 0 < τ → ∀ Z Θ : ℝ, Φ Z (-Θ) τ = -Φ Z Θ τ)
    (hD : ProfDerivData (Regularity.pExp α) Φ g)
    (hA : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hAd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + C.mu τ) * A τ) τ)
    (hBd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt B (-(1 - C.mu τ) * B τ) τ)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    (hmu : ∀ τ : ℝ, 0 ≤ τ → C.mu τ = Galerkin.muDyn (Regularity.pExp α) Φ g τ) :
    MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
      (merPsi (Regularity.pExp α) A B Φ C) C.T := by
  have hp0 : 0 < Regularity.pExp α := Regularity.pExp_pos hα
  have hp1 : Regularity.pExp α ≤ 1 := Regularity.pExp_le_one hα13
  -- the modulation stays away from `-1`
  have hne : ∀ τ : ℝ, 0 ≤ τ → 1 + Galerkin.muDyn (Regularity.pExp α) Φ g τ ≠ 0 := by
    intro τ hτ h0
    have h1 := C.hmu_lo τ hτ
    have h2 := hmu τ hτ
    rw [h2] at h1
    linarith
  -- the profile equation `(E)` for the odd extension of `F_* + g`
  have hWeak : DynEqF (Regularity.pExp α) (Galerkin.muDyn (Regularity.pExp α) Φ g)
      (profFamOdd (Regularity.pExp α) g) Φ :=
    DynEqF_of_isDynEqOn_odd hp0 hp1 hD hsol.2 hne
  -- the positive half-plane
  have hpos : ∀ r z t : ℝ, 0 < r → 0 < z → t ∈ Set.Ioo 0 C.T →
      Work.CoreResiduals.meridianResid (Work.FTS.Physical.merProfile α A B g C)
        (merPsi (Regularity.pExp α) A B Φ C) r z t = 0 := by
    intro r z t hr hz ht
    have hσpos : 0 < Work.FTS.Physical.clockInv C t :=
      Work.FTS.Physical.clockInv_pos_of_pos C ht
    have hσnn : 0 ≤ Work.FTS.Physical.clockInv C t := le_of_lt hσpos
    have hbpos : 0 < B (Work.FTS.Physical.clockInv C t) := hB _ hσnn
    have hApos : 0 < A (Work.FTS.Physical.clockInv C t) := by
      have h1 := hA _ hσnn
      have h2 := C.hApos _ hσnn
      linarith
    have hθpos : 0 < Work.Cyl.thetaP r z := by
      rw [Work.Cyl.thetaP]; exact Real.arctan_pos.mpr (div_pos hz hr)
    have hθlt : Work.Cyl.thetaP r z < Real.pi / 2 := by
      rw [Work.Cyl.thetaP]; exact Real.arctan_lt_pi_div_two _
    have hZpos : 0 < Work.Cyl.rhoP r z ^ Regularity.pExp α
        / B (Work.FTS.Physical.clockInv C t) :=
      div_pos (Real.rpow_pos_of_pos (Work.Cyl.rhoP_pos hr z) _) hbpos
    -- joint `C¹` of the odd extension of the profile
    have hFc : ContDiffAt ℝ 1
        (fun q : ℝ × ℝ × ℝ => profFamOdd (Regularity.pExp α) g q.1 q.2.1 q.2.2)
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z, Work.FTS.Physical.clockInv C t) :=
      Smooth.profFamOdd_contDiffAt hp0 hreg hZpos hθpos hθlt (by linarith)
    -- joint `C¹` of the stream function, in the meridian variables
    have hΦc : ContDiffAt ℝ 1 (fun q : ℝ × ℝ => Φ q.1 q.2 (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z) := by
      have hQd : (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t),
          Work.Cyl.thetaP r z) ∈ Work.Construction.Qd := ⟨hZpos, hθpos, hθlt⟩
      have hQdopen : IsOpen Work.Construction.Qd :=
        show IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) from
          isOpen_Ioi.prod isOpen_Ioo
      exact ((hΦ _ hσpos).contDiffAt (hQdopen.mem_nhds hQd)).of_le
        (by norm_num : ((1 : ℕ) : WithTop ℕ∞) ≤ ((2 : ℕ) : WithTop ℕ∞))
    -- the fake-time derivative of the profile at the point
    have hFt : HasDerivAt (fun s => profFamOdd (Regularity.pExp α) g
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP r z) s)
        (deriv (fun s => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t))
        (Work.FTS.Physical.clockInv C t) := by
      have hd : DifferentiableAt ℝ (fun s : ℝ => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t) := by
        show DifferentiableAt ℝ
          ((fun q : ℝ × ℝ × ℝ => profFamOdd (Regularity.pExp α) g q.1 q.2.1 q.2.2)
            ∘ fun s : ℝ => (Work.Cyl.rhoP r z ^ Regularity.pExp α
                / B (Work.FTS.Physical.clockInv C t), Work.Cyl.thetaP r z, s))
          (Work.FTS.Physical.clockInv C t)
        exact (hFc.differentiableAt (by norm_num)).comp
          (Work.FTS.Physical.clockInv C t) (by fun_prop)
      exact hd.hasDerivAt
    -- the three chain-rule facts of amplitude, scale and clock
    have hσ' : HasDerivAt (Work.FTS.Physical.clockInv C)
        ((C.A (Work.FTS.Physical.clockInv C t))⁻¹) t :=
      Work.FTS.Physical.clockInv_hasDerivAt C ht
    have ha : HasDerivAt (fun s => (A (Work.FTS.Physical.clockInv C s))⁻¹)
        ((1 + C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          * (A (Work.FTS.Physical.clockInv C t))⁻¹) t :=
      Clock.amplitude_hasDerivAt (A := A) (C := C) hAd hApos ht
    have hb : HasDerivAt (fun s => B (Work.FTS.Physical.clockInv C s))
        (-(1 - C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
          * B (Work.FTS.Physical.clockInv C t)) t :=
      Clock.scale_hasDerivAt (B := B) (C := C) hBd ht
    have hb' : HasDerivAt (fun s => B (Work.FTS.Physical.clockInv C s))
        (-((1 - C.mu (Work.FTS.Physical.clockInv C t))
          * (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
          * B (Work.FTS.Physical.clockInv C t)) t := by
      convert hb using 1
      ring
    have h2s : 2 * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        = (A (Work.FTS.Physical.clockInv C t))⁻¹ := by
      have h1 := hA _ hσnn
      have hne1 : A (Work.FTS.Physical.clockInv C t) ≠ 0 := ne_of_gt hApos
      have hne2 : C.A (Work.FTS.Physical.clockInv C t) ≠ 0 := ne_of_gt (C.hApos _ hσnn)
      rw [h1]
      field_simp
    -- the residual identity of the area
    have hres := meridianResid_dyn (p := Regularity.pExp α)
      (a := fun s => (A (Work.FTS.Physical.clockInv C s))⁻¹)
      (b := fun s => B (Work.FTS.Physical.clockInv C s))
      (σ := Work.FTS.Physical.clockInv C)
      (F := profFamOdd (Regularity.pExp α) g) (Φ := Φ)
      (r := r) (z := z) (t := t)
      (A' := (1 + C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹
        * (A (Work.FTS.Physical.clockInv C t))⁻¹)
      (B' := -((1 - C.mu (Work.FTS.Physical.clockInv C t))
        * (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
        * B (Work.FTS.Physical.clockInv C t))
      (sp := (C.A (Work.FTS.Physical.clockInv C t))⁻¹)
      (μa := C.mu (Work.FTS.Physical.clockInv C t))
      (fτ := deriv (fun s => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t))
      hr (ne_of_gt hbpos) ha hb' hσ' rfl rfl h2s hFc hΦc hFt
    -- the profile equation `(E)` at the clock time, with the clock's modulation
    have hE : dynEqLHS (Regularity.pExp α) (C.mu (Work.FTS.Physical.clockInv C t))
        (fun Z Θ => profFamOdd (Regularity.pExp α) g Z Θ (Work.FTS.Physical.clockInv C t))
        (fun Z Θ => Φ Z Θ (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
        (Work.Cyl.thetaP r z)
        (deriv (fun s => profFamOdd (Regularity.pExp α) g
          (Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
          (Work.Cyl.thetaP r z) s) (Work.FTS.Physical.clockInv C t)) = 0 := by
      have h := hWeak _ _ _ ⟨hZpos, hθpos, hθlt⟩ hσpos
      rw [← hmu _ hσnn] at h
      exact h
    rw [hE, mul_zero] at hres
    exact hres
  -- parity of the meridian pair
  have hWdyn : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo 0 C.T →
      merProfileDyn α A B g C r (-z) t = -merProfileDyn α A B g C r z t := by
    intro r z t hr hz _
    have hθne : Work.Cyl.thetaP r z ≠ 0 := thetaP_ne_zero hr hz
    have hprof := profFamOdd_neg (α := Regularity.pExp α) (g := g)
      (Z := Work.Cyl.rhoP r z ^ Regularity.pExp α / B (Work.FTS.Physical.clockInv C t))
      (Θ := Work.Cyl.thetaP r z) (σ := Work.FTS.Physical.clockInv C t) hθne
    rw [merProfileDyn_apply', merProfileDyn_apply', rhoP_neg, thetaP_neg, hprof]
    ring
  have hWodd : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo 0 C.T →
      Work.FTS.Physical.merProfile α A B g C r (-z) t
        = -Work.FTS.Physical.merProfile α A B g C r z t := by
    intro r z t hr hz ht
    rw [← merProfileDyn_eq]
    exact hWdyn r z t hr hz ht
  have hψodd : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo 0 C.T →
      merPsi (Regularity.pExp α) A B Φ C r (-z) t
        = -merPsi (Regularity.pExp α) A B Φ C r z t := by
    intro r z t _ _ ht
    have hσpos : 0 < Work.FTS.Physical.clockInv C t :=
      Work.FTS.Physical.clockInv_pos_of_pos C ht
    simp only [merPsi, dynPsi_apply]
    rw [rhoP_neg, thetaP_neg, hΦodd _ hσpos]
    ring
  -- assemble
  intro r z t hr hz ht
  rcases lt_trichotomy z 0 with hlt | heq | hgt
  · have h := Odd.meridianResid_odd_win (T := C.T) hWodd hψodd r (-z) t
      (ne_of_gt hr) (by linarith) ht
    rw [neg_neg] at h
    rw [h, hpos r (-z) t hr (by linarith) ht, neg_zero]
  · exact absurd heq hz
  · exact hpos r z t hr hgt ht

/-- **The main theorem, in the "defect-free" form of the pre-fix design.**  Same statement as
`meridianEq_of_dynEq`.  The pre-fix version took the *paper's* relation between the modulation
constant and the `AK`-coefficient of the fake-time equation,

  `2α·muDyn α Φ g τ = μ̄ + L₁₂(Transport (g τ))(0)`   (`μ̄ = mubar (N₀) (N)`),

as a hypothesis `hdef`; with the sign fix that relation is *definitional*
(`Work.Construction.two_mul_mufunS`, `two_mul_muDyn`), so the hypothesis is gone and this theorem
is now literally `meridianEq_of_dynEq`.  It is kept as the explicit interface for callers that
still name the relation. -/
theorem meridianEq_of_dynEq_of_defect {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {A B : ℝ → ℝ} {Φ g : Fam} {C : Work.FTS.Physical.PhysClock}
    (hsol : Galerkin.IsDynGSolWith (Elliptic.IsBslSol (Regularity.pExp α))
      (Regularity.pExp α) Φ g)
    (hreg : Galerkin.RegPkg (Regularity.pExp α) g)
    (hΦ : ∀ τ : ℝ, 0 < τ →
      ContDiffOn ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) Work.Construction.Qd)
    (hΦodd : ∀ τ : ℝ, 0 < τ → ∀ Z Θ : ℝ, Φ Z (-Θ) τ = -Φ Z Θ τ)
    (hD : ProfDerivData (Regularity.pExp α) Φ g)
    (hA : ∀ τ : ℝ, 0 ≤ τ → C.A τ = 2 * A τ)
    (hAd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt A (-(1 + C.mu τ) * A τ) τ)
    (hBd : ∀ τ : ℝ, 0 ≤ τ → HasDerivAt B (-(1 - C.mu τ) * B τ) τ)
    (hB : ∀ τ : ℝ, 0 ≤ τ → 0 < B τ)
    (hmu : ∀ τ : ℝ, 0 ≤ τ → C.mu τ = Galerkin.muDyn (Regularity.pExp α) Φ g τ) :
    MeridianEqOn (Work.FTS.Physical.merProfile α A B g C)
      (merPsi (Regularity.pExp α) A B Φ C) C.T :=
  meridianEq_of_dynEq hα hα13 hsol hreg hΦ hΦodd hD hA hAd hBd hB hmu

end Work.FTS.MeridianDyn
