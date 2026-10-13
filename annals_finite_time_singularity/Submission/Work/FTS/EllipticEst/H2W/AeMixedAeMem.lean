/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/AeMixedAeMem` — the a.e. slice honesty of the mixed slot `z ∂_z∂_θu`

## The statement

For a datum `AeData α u G` (the almost-everywhere class of the level-`0` elliptic estimate,
`H2W/Ae/Defs.lean`) the *mixed* slot `z ∂_z∂_θu = ∂_θ(z ∂_zu)` has honest angular slices for
almost every `z > 0`:
`∀ᵐ z ∂(volume.restrict (Ioi 0)), IntegrableOn (fun θ => (z * ∂_z∂_θu z θ)^2 * σ θ) Iθ`,
`σ θ = sin(2θ)^(-η) = AngSecond.sig θ`.

This is *literally* the first conjunct of the tree's `Cores.AeStep2Aux.aeMixedAe_mem` (which asks
for that conjunct together with the outer `IntegrableOn` of the slice functional on `Iz`), and it
is the form every consumer of the slot needs.

## What is proved in this file

* `AeMixedAeMem_of_fin` — the reduction of the target to the finiteness of the *iterated*
  weighted `∫⁻` `∫⁻_z∫⁻_θ (z ∂_z∂_θu)² σ < ⊤` (first conjunct of
  `Cores.AeStep2Aux.aeMixedAe_mem_of_fin`).
* `AeMixedAeMem_of_hslot` — **the reduction of the target to the a.e. slice honesty of the
  `H`-slot** `H = ∂_θ²(z∂_zu) = D_z(∂_θ²u)`.  The mixed slot is the *first* angular derivative
  of the slice `θ ↦ z ∂_zu(z,θ)`; by the one-variable Cauchy trick
  (`H2W.slice_deriv_of_sq_deriv_deriv`: a `C^∞` function on `(0,π/2)` whose second derivative is
  `σ`-square-integrable has a bounded, hence `σ`-square-integrable, first derivative) the
  `σ`-honesty of the `H`-slot at a given `z` forces the `σ`-honesty of the mixed slot at the
  *same* `z`, with no trace hypothesis.  The `H`-slot is exactly what the tree's `I₁`-chain
  carries as a hypothesis (`Cores.Pieces.ae_i1_slice_ineq`,
  `AngSecond.hkMem_pthIter2_grad_to_H`), so this is the natural reduction of the target.
* `AeMixedAeMem_of_hslot_cont_bdd` — a consumer-ready corollary: if a.e. slice of the `H`-slot is
  continuous on `(0,π/2)` and bounded there, the target follows
  (`H2W.integrableOn_sq_mul_sEta_of_bdd` produces the `σ`-integrability).

## What is *not* proved here

The target itself.  The whole content of the target is now isolated as the a.e. `σ`-honesty of
the `H`-slot (the two reductions above), which is one of the recorded forms of the project's open
crux.  The analysis is recorded in `Cores/AeStep2Aux/NOTES_aeMixedAe_mem.md`,
`H2W/NOTES_AeMixedAeMem2.md` and `Prop/Ang2/NOTES_aePpFinite_ROUTE2.md`; in brief:

* the four *diagonal* slots `U = ∫∫ρu²`, `Z = ∫∫ρ(D_zu)²`, `T = ∫∫ρ(∂_θ²u)²`,
  `B = ∫∫ρ(z²∂_z²u)²` are all available and finite from `AeData` alone, but the mixed slot is not
  obtainable from them by any one-dimensional (radial or angular) Agmon/interpolation argument;
* the `∀ z` (slicewise) version of the conclusion is **false** in-tree
  (`AngAWeak/NOTES_aeMixedHon_FALSE.md`, staggered shrinking bumps), the failure occurring at a
  *single* point `z₀`; in that datum the *global* mixed integral converges (`Σ 1/n²`), which is
  why the a.e. weakening is the correct form and is not refuted;
* the continuous proof (Elgindi's `prop:L2`, Step 2: multiply the equation by `-∂_θθu σ` and
  integrate by parts radially and angularly, producing the mixed slot with a *positive* sign) is
  obstructed by the two `θ`-boundary (trace) terms: the route needs the one-sided limits of the
  slices of `D_zu`, which are **not** derivable from `AeData` (the sibling trace lemmas were
  filed and rejected repeatedly as under-hypothesised, and the accepted repairs add
  `HkMem α 0 (z·∂_z∂_θu)` — i.e. this conclusion — as a hypothesis);
* mode-level analysis supports *truth*: for superpositions `u = Σ_n d_n(z) g_n(θ)` the sharp
  angular interpolation `P_n² ≤ N_n Q_n` plus the sharp radial Agmon–Nirenberg give
  `X_n = √(T_n B_n)`, hence `X ≤ C(B + T + Z + U)`; and the counterexample mechanism needs
  infinitely many modes to sit *simultaneously at a critical point* of their `z`-profiles, while
  each mode's critical set `{g = 0, g' ≠ 0}` is discrete (a zero with non-zero slope is
  isolated) and the per-slice hypotheses hold at *every* `z`, not merely a.e.

Everything else the consumers need is available; the mixed honesty itself is carried as an
explicit hypothesis there (`Final/AeI1Paper_mix_fts`, `H2W/EllCore/AeI1HonestCore.lean`,
`AngAWeak/aeI1Mixed.lean`, `Cores/AeStep2Aux/i1Paper_weakMixed.lean`, ...).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem_of_fin
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.H2.STBasic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.H2W.slice_deriv_of_sq_deriv_deriv
import Submission.Work.FTS.EllipticEst.H2W.integrableOn_sq_mul_sEta_of_bdd
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option autoImplicit false

/-! ## The reduction of the target to the finiteness of the iterated `∫⁻` -/

/-- **The target follows from the finiteness of the iterated weighted `∫⁻`.**

This is the first conjunct of `Cores.AeStep2Aux.aeMixedAe_mem_of_fin` (Tonelli plus the
measurability of the integrand, which is continuous on the open quadrant).  `AngSecond.sig` is
definitionally `fun θ => Real.sin (2 * θ) ^ (-(Spaces.eta))`, so the conclusion is the requested
statement. -/
theorem AeMixedAeMem_of_fin {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ)) < ⊤) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hconj := (Work.FTS.EllipticEst.Cores.AeStep2Aux.aeMixedAe_mem_of_fin α u G h hfin).1
  simpa [Work.FTS.EllipticEst.AngSecond.sig] using hconj

/-! ## The reduction of the target to the `H`-slot `∂_θ²(z∂_zu)`

The mixed slot `z∂_z∂_θu` is the *first* angular derivative of the slice `θ ↦ z ∂_zu(z,θ)`; its
`σ`-honesty follows, at the *same* `z`, from the `σ`-honesty of the *second* angular derivative
`H = ∂_θ²(z∂_zu) = ∂_θ²(D_zu) = D_z(∂_θ²u)` by the one-variable Cauchy trick
(`H2W.slice_deriv_of_sq_deriv_deriv`). -/

/-- The `H`-slot `∂_θ²(D_zu)` *is* the second derivative of the angular slice
`θ ↦ z ∂_z u(z,θ)`: both are `∂_θ(∂_θ(z ∂_zu))` with `∂_θ` the one-dimensional derivative of the
slice. -/
private theorem hslot_slice_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = deriv (fun t : ℝ => deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') t) θ := rfl

/-- **The target from the a.e. `σ`-honesty of the `H`-slot** `∂_θ²(z ∂_zu)`.

The `H`-slot is the *second* angular derivative of the slice `θ ↦ z ∂_zu(z,θ)`; by
`H2W.slice_deriv_of_sq_deriv_deriv` its a.e. `σ`-honesty forces the a.e. `σ`-honesty of the
*first* angular derivative, i.e. of the mixed slot.  The identification of the mixed slot with
`z ∂_z∂_θu` uses the Clairaut identity `∂_θ∂_z u = ∂_z∂_θu` on the open quadrant
(`Spaces.pz_pth_comm`). -/
theorem AeMixedAeMem_of_hslot {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hH : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall fun n => h.smooth n
  have hSpz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz u) := hSO.pz
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hH] with z hz hHz
  -- the slice `θ ↦ z ∂_z u(z,θ)` is `C^∞` on the open angular interval
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n (fun θ : ℝ => z * Work.Spaces.pz u z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have h1 : ContDiffOn ℝ n (fun θ : ℝ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_iff_forall_nat_le.mp (hSpz.curry_θ hz)) n le_top
    exact h1.const_smul z
  -- the `H`-slot *is* the second derivative of that slice
  have hsec : MeasureTheory.IntegrableOn
      (fun θ : ℝ =>
        (deriv (fun t : ℝ => deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    hHz.congr (Filter.Eventually.of_forall fun θ => by
      show (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ
        = (deriv (fun t : ℝ => deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') t) θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ
      rw [hslot_slice_eq u z θ])
  have hkey := Work.FTS.EllipticEst.H2W.slice_deriv_of_sq_deriv_deriv hslice hsec
  -- identify the first derivative of the slice with the mixed slot, a.e. on `Iθ`
  have hae : (fun θ : ℝ =>
        (deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by
    have hIooIcc : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
        = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
          (b := Real.pi / 2)).symm
    rw [Work.Spaces.Iθ, hIooIcc]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
    have hcl : Work.Spaces.pth (Work.Spaces.pz u) z θ = Work.Spaces.pz (Work.Spaces.pth u) z θ :=
      (Work.Spaces.pz_pth_comm (f := u)
        ((hSO.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)))).symm
    show (deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
    have h1 : deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') θ
        = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := by
      rw [deriv_const_mul_field]
      rfl
    rw [h1, hcl]
    rfl
  exact hkey.congr hae

/-- **Consumer-ready corollary**: if almost every angular slice of the `H`-slot
`∂_θ²(z∂_zu) = pthIter 2 (grad u)` is continuous on `(0,π/2)` and bounded there, the target
holds.  The `σ`-integrability of `(H-slot)² σ` is then
`H2W.integrableOn_sq_mul_sEta_of_bdd`. -/
theorem AeMixedAeMem_of_hslot_cont_bdd {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ : ℝ => Work.Spaces.pthIter 2
          (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ) (Set.Ioo 0 (Real.pi / 2)) ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
          |Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ| ≤ M) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  refine AeMixedAeMem_of_hslot h ?_
  filter_upwards [hb] with z hz
  exact Work.FTS.EllipticEst.H2W.integrableOn_sq_mul_sEta_of_bdd hz.1 hz.2

/-! ## The `HkMem` form of the two reductions

Every consumer of the mixed slot in the tree carries the slot's honesty in the `HkMem α 0`
form (`Final/AeI1Paper_mix_fts`, `H2W/EllCore/AeI1HonestCore.lean`, `AngAWeak/aeI1Mixed.lean`,
`Cores/AeStep2Aux/i1Paper_weakMixed.lean`, …), i.e.

`HkMem α 0 (fun z θ => z * pz (pth u) z θ)`   (the mixed slot `z ∂_z∂_θu`) or
`HkMem α 0 (pthIter 2 (grad u))`              (the `H`-slot `∂_θ²(z∂_zu)`).

`HkMem α 0 f` is the honesty of `HkIntegrand α 0 f z θ = (f z θ · w z / sin(2θ)^{η/2})²`, which
equals `w(z)² σ(θ) f(z,θ)²`; since `w z ≠ 0` for `z > 0`, the *first* conjunct of `HkMem` (which
holds for **every** `z ∈ Iz`) gives the `σ`-slice honesty of `f` for every `z > 0`.  The bridges
below turn those `HkMem`-form hypotheses into the target. -/

/-- The `k = 0` `HkIntegrand` is `w(z)² · (f z θ)² · σ θ` on `Iθ`. -/
theorem HkIntegrand_zero_eq_w (α : ℝ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (Work.Spaces.w z) ^ 2 * ((f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  have h0 : Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [h0, Work.FTS.EllipticEst.AngSecond.sq_mul_W f hθ]
  simp only [Work.FTS.EllipticEst.AngSecond.w2, Work.FTS.EllipticEst.AngSecond.sig,
    Work.FTS.EllipticEst.sEta]
  ring

/-- **The target from the `HkMem`-form honesty of the `H`-slot** — the form in which the tree
carries the slot (`Cores.Pieces.ae_i1_slice_ineq`, `AngSecond.hkMem_pthIter2_grad_to_H`). -/
theorem AeMixedAeMem_of_hslot_HkMem {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hslot : Work.Spaces.HkMem α 0
      (Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  refine AeMixedAeMem_of_hslot h ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  set Hslot : ℝ → ℝ := fun θ => Work.Spaces.pthIter 2
    (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ with hHslot
  have hslice : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((Hslot θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iθ :=
    (hslot.1 z (Set.mem_Ici.mpr (le_of_lt hz))).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => HkIntegrand_zero_eq_w α _ hθ))
  have hwne0 : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have hzpos : 0 < z := hz
    have h1 : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hzpos))
    exact pow_ne_zero 2 h1
  have hwne : ((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2 = 1 :=
    inv_mul_cancel₀ hwne0
  refine ((hslice.const_mul ((Work.Spaces.w z) ^ 2)⁻¹)).congr
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_))
  change ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
      * (Hslot θ ^ 2 * Work.FTS.EllipticEst.sEta θ)) = Hslot θ ^ 2
    * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
  calc ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
        * (Hslot θ ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
        * (Hslot θ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring
    _ = Hslot θ ^ 2 * Work.FTS.EllipticEst.sEta θ := by rw [hwne, one_mul]
    _ = Hslot θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := rfl

/-- **The target from the `HkMem`-form honesty of the *mixed slot*** `z ∂_z∂_θu` — the exact
hypothesis the tree's consumers record (`Final/AeI1Paper_mix_fts`,
`H2W/EllCore/AeI1HonestCore.lean`, …). -/
theorem AeMixedAeMem_of_mixedHkMem {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hmix : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hz
  set slot : ℝ → ℝ := fun θ => z * Work.Spaces.pz (Work.Spaces.pth u) z θ with hslot
  have hslice : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.w z) ^ 2 * ((slot θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iθ :=
    (hmix.1 z (Set.mem_Ici.mpr (le_of_lt hz))).congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => HkIntegrand_zero_eq_w α _ hθ))
  have hwne0 : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have hzpos : 0 < z := hz
    have h1 : Work.Spaces.w z ≠ 0 := by
      rw [Work.Spaces.w]
      exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt hzpos))
    exact pow_ne_zero 2 h1
  have hwne : ((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2 = 1 :=
    inv_mul_cancel₀ hwne0
  refine ((hslice.const_mul ((Work.Spaces.w z) ^ 2)⁻¹)).congr
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_))
  change ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
      * (slot θ ^ 2 * Work.FTS.EllipticEst.sEta θ)) = slot θ ^ 2
    * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
  calc ((Work.Spaces.w z) ^ 2)⁻¹ * ((Work.Spaces.w z) ^ 2
        * (slot θ ^ 2 * Work.FTS.EllipticEst.sEta θ))
      = (((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2)
        * (slot θ ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring
    _ = slot θ ^ 2 * Work.FTS.EllipticEst.sEta θ := by rw [hwne, one_mul]
    _ = slot θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) := rfl

/-- **The exact per-slice decomposition of the target.**  The target follows from the
one-dimensional slice dichotomy (the tree's `Dispatch.slice_pairing_forces_deriv_integrable`,
stated here as an explicit hypothesis `hdich` since it is open), applied a.e. in `z` to the
angular slice `f_z := θ ↦ z ∂_zu(z,θ)` of `D_zu`, together with the per-slice data `hdata` that
the dichotomy consumes:

* `f_z ∈ C²(0,π/2)` (automatic from `AeData` — `f_z` is the `θ`-slice of the smooth `D_zu`);
* `f_z → 0` at both angular endpoints (the "(FIN)" trace condition; **not** derivable from
  `AeData`, see `NOTES_AeMixedAeMem3.md` Finding 2);
* `∫_θ σ f_z² < ∞` (the `σ`-honesty of the `D_zu`-slot, `HkMem α 0 (D_zu)`);
* `∫_θ |σ f_z f_z''| < ∞`, the honesty of the *pairing* `D_zu·∂_θ²(D_zu)`.  This is *equivalent*
  to the `H`-slot crux (Cauchy–Schwarz in `θ` forces `∫σ(∂_θ²(D_zu))²<∞`), so it is **not** a
  consequence of `AeData`: `NOTES_AeMixedAeMem3.md` "Finding 1 (RETRACTED)" records the tempting
  product-rule argument and its flaw.

The dichotomy then gives the `σ`-honesty of `f_z' = ∂_θ(z∂_zu)`, and the identification of
`f_z'` with `z ∂_z∂_θu` is Clairaut on the open quadrant. -/
theorem AeMixedAeMem_of_sliceData {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hdich : ∀ f : ℝ → ℝ,
      ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => f θ * deriv (fun t => deriv f t) θ
          * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)))
    (hdata : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ : ℝ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => z * Work.Spaces.pz u z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        (Set.Ioo 0 (Real.pi / 2)) ∧
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz u z θ)
          * deriv (fun t : ℝ => deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') t) θ
          * Work.FTS.EllipticEst.sEta θ) (Set.Ioo 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall fun n => h.smooth n
  have hSpz : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz u) := hSO.pz
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hdata]
    with z hz hzdata
  obtain ⟨hlim0, hlim1, hP, hT⟩ := hzdata
  -- the slice is `C²` on the open angular interval
  have hslice : ContDiffOn ℝ 2 (fun θ : ℝ => z * Work.Spaces.pz u z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.pz u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (contDiffOn_iff_forall_nat_le.mp (hSpz.curry_θ hz)) 2 le_top
    exact h1.const_smul z
  -- the one-dimensional dichotomy on that slice
  have hkey := hdich (fun θ : ℝ => z * Work.Spaces.pz u z θ) hslice hlim0 hlim1 hP hT
  -- identify `f'` with `z ∂_z∂_θu` and transfer `(0,π/2)` to `Iθ` (null difference)
  have hIooIcc : MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 2))
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.pi / 2)).symm
  -- `IntegrableOn … (Ioo 0 (π/2))` as an `Integrable` against the explicit measure, so that the
  -- (null-set) change of the domain to `Iθ = Icc 0 (π/2)` is a rewrite
  have hkey2 : MeasureTheory.Integrable
      (fun θ : ℝ => (deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) := hkey
  rw [← hIooIcc] at hkey2
  refine hkey2.congr ?_
  have hae : (fun θ : ℝ => (deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) := by
    rw [Work.Spaces.Iθ, hIooIcc]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo fun θ hθ => ?_
    have hcl : Work.Spaces.pth (Work.Spaces.pz u) z θ = Work.Spaces.pz (Work.Spaces.pth u) z θ :=
      (Work.Spaces.pz_pth_comm (f := u)
        ((hSO.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)))).symm
    show (deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ
      = (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
    have h1 : deriv (fun θ' : ℝ => z * Work.Spaces.pz u z θ') θ
        = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := by
      rw [deriv_const_mul_field]
      rfl
    rw [h1, hcl]
    rfl
  exact hae

/-- The requested statement: the angular slice `θ ↦ (z ∂_z∂_θu)^2 σ θ` of the mixed slot is
integrable for almost every `z > 0`.

The proof is one of the two reductions above; the `σ`-honesty of the `H`-slot
`∂_θ²(z∂_zu) = pthIter 2 (grad u)` (equivalently, the finiteness of the iterated weighted `∫⁻`,
`AeMixedAeMem_of_fin`) is the project's open crux (see the module docstring), so this step is not
yet available. -/
theorem AeMixedAeMem {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ := by
  sorry

end Work.FTS.EllipticEst.H2W
