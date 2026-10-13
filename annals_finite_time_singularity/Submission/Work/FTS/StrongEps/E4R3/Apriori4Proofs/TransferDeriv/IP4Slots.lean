import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.IP4Prep
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.slotPairing_abs_le_gen
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.integrable_slot_of_dom
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Flat
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leafSlotSliceIntegrable
import Submission.Work.FTS.StrongEps.HkMem_Jeps
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.JepsSmoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/IP4Slots.lean` — the slot level of the derivative-priced transfer

* The diagonal slot factor `√(wip w (slot) (slot))` is bounded by the `ℋ^m`-norm of the datum,
  through the composed-slot identity `mixed_comp` and the single-slot Cauchy–Schwarz
  `slotPairing_abs_le_gen` (`sqrt_wip_comp_le`, `sqrt_wip_cut_le`).
* The composed slot of a leaf weight is dominated by the `ℋ^m`-integrand (`dom_comp_slot`,
  `dom_comp_slot_Jeps`).
* The six integrability certificates of `SlotIntegrableDeriv` at the cuts of the shifted slots
  (`slotIntegrableDeriv_cut`), discharged from the above through `integrable_slot_of_dom`.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The diagonal slot factor is bounded by the `ℋ^m`-norm -/

/-- **The diagonal factor of a slot transfer.**  For a leaf weight of the angular slot `a + a₀` and
a slot of order at most `m`, the flat pairing of the composed slot of `f` is at most `|f|_{ℋ^m}²`,
so its square root is at most `|f|_{ℋ^m}`.

The slot `D_z^bD_θ^a(D_z^{b₀}D_θ^{a₀}f)` of `f` is rewritten as the composed slot
`D_z^{b+b₀}D_θ^{a+a₀}f` on the open quadrant (`mixed_comp`), where the single-slot Cauchy–Schwarz
applies. -/
theorem sqrt_wip_comp_le {α : ℝ} (hα : 0 < α) {f : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) (hmf : Work.Spaces.HkMem α m f) :
    Real.sqrt (Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f)))
      ≤ Work.Spaces.HkNorm α m f := by
  have hcomp : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ
        = Work.Spaces.mixed (b + b₀) (a + a₀) f z θ :=
    fun z θ hh => mixed_comp hfs b₀ a₀ b a hh
  have hwip : Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
      = Work.FTS.TransportS.slotPairing w (a + a₀) (b + b₀) f f := by
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.JT.slotPairing_eq_wip]
    exact Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_both hcomp hcomp
  rw [hwip]
  refine Real.sqrt_le_iff.mpr ⟨Work.Spaces.HkNorm_nonneg α m f, ?_⟩
  have hcs := Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.slotPairing_abs_le_gen
    hα (a := a + a₀) (b := b + b₀) (n := m) (by omega) hleaf hfs hfs hmf hmf
  have hsq : Work.FTS.TransportS.slotPairing w (a + a₀) (b + b₀) f f
      ≤ (Work.Spaces.HkNorm α m f) ^ 2 := by
    rw [sq]
    exact (abs_le.mp hcs).2
  exact hsq

/-- The same bound for a slot of the *cut* of a profile: the cut agrees with the profile on the
open quadrant, where the pairings live. -/
theorem sqrt_wip_cut_le {α : ℝ} (hα : 0 < α) {f : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) (hmf : Work.Spaces.HkMem α m f) :
    Real.sqrt (Work.Coercivity.wip w
        (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f))))
      ≤ Work.Spaces.HkNorm α m f := by
  have heq : Work.Coercivity.wip w (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)))
        (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)))
      = Work.Coercivity.wip w (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f))
        (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f)) :=
    Work.FTS.StrongEps.EpsE4Thr.wip_congr_Q0_both
      (fun z θ h => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a h)
      (fun z θ h => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a h)
  rw [heq]
  exact sqrt_wip_comp_le hα hfs hab hleaf hmf

/-! ## The pointwise domination of a composed slot -/

/-- The composed slot of a leaf weight is dominated by the `ℋ^m`-integrand. -/
theorem dom_comp_slot {α : ℝ} (hα : 0 < α) {f : Fn}
    (hfs : Work.FTS.EllipticEst.SmoothOpen f) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) {z θ : ℝ}
    (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    w z θ * (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m f z θ := by
  have h : Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ
      = Work.Spaces.mixed (b + b₀) (a + a₀) f z θ := mixed_comp hfs b₀ a₀ b a hp
  rw [h]
  exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_dom_gen hα hab hleaf
    ⟨hp.2.1, hp.2.2⟩

/-- The composed slot of a leaf weight applied to `J_ε h` is dominated by the `ℋ^m`-integrand of
`J_ε h`. -/
theorem dom_comp_slot_Jeps {α : ℝ} (hα : 0 < α) {h : Fn}
    (hhs : Work.FTS.EllipticEst.SmoothOpen h) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) {m a b a₀ b₀ : ℕ}
    (hab : (a + a₀) + (b + b₀) ≤ m) {w : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α (a + a₀) w) {z θ : ℝ}
    (hp : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    w z θ * (Work.Spaces.mixed b a
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α m (Work.FTS.StrongEps.Jeps ρ ε h) z θ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry h) Work.FTS.StrongEps.Quad :=
    fun n => hhs.forall n
  have e1 : Work.Spaces.mixed b a
        (Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b₀ a₀ h)) z θ
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h)) z θ :=
    Work.FTS.StrongEps.mixed_Jeps ρ hρ hε (fun n => (hhs.mixed b₀ a₀).forall n) hp.1 hp.2 b a
  have e2 : Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h))
      = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed (b + b₀) (a + a₀) h) :=
    Jeps_congr_Q0 (fun z' θ' h' => mixed_comp hhs b₀ a₀ b a h') ρ ε
  have e3 : Work.FTS.StrongEps.Jeps ρ ε
        (Work.Spaces.mixed (b + b₀) (a + a₀) h) z θ
      = Work.Spaces.mixed (b + b₀) (a + a₀) (Work.FTS.StrongEps.Jeps ρ ε h) z θ :=
    (Work.FTS.StrongEps.mixed_Jeps ρ hρ hε (fun n => hhs.forall n) hp.1 hp.2
      (b + b₀) (a + a₀)).symm
  rw [e1, e2, e3]
  exact Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_dom_gen hα hab hleaf
    ⟨hp.2.1, hp.2.2⟩

/-! ## The integrability certificates of the slot transfer -/

/-- **The integrability certificates of the slot transfer, at the cuts of the shifted slots.**  The
six conditions of `SlotIntegrableDeriv`, all discharged from the composed-slot identity, the
`ℋ⁴`- (respectively `ℋ⁵`-) membership of the two data, and the vanishing of the cuts — and of
`J_ε` — outside the open quadrant. -/
theorem slotIntegrableDeriv_cut {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) {ε : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    {f h : Fn} (hfs : Work.FTS.EllipticEst.SmoothOpen f)
    (hhs : Work.FTS.EllipticEst.SmoothOpen h) (hmf : Work.Spaces.HkMem α 4 f)
    (hmh : Work.Spaces.HkMem α 5 h) {a₀ b₀ a b : ℕ} (hab₀ : a₀ + b₀ ≤ 3)
    (hab : a + b ≤ 1) {w : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a w) :
    SlotIntegrableDeriv ρ ε w a b (cut (Work.Spaces.mixed b₀ a₀ f))
      (cut (Work.Spaces.mixed b₀ a₀ h)) := by
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hmh5 : Work.Spaces.HkMem α 5 h := hmh
  -- the cuts and the mollified second slot
  have hAsm : Work.FTS.EllipticEst.SmoothOpen (cut (Work.Spaces.mixed b₀ a₀ f)) :=
    smoothOpen_cut (hfs.mixed b₀ a₀)
  have hBsm : Work.FTS.EllipticEst.SmoothOpen (cut (Work.Spaces.mixed b₀ a₀ h)) :=
    smoothOpen_cut (hhs.mixed b₀ a₀)
  have hJsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.Jeps ρ ε (cut (Work.Spaces.mixed b₀ a₀ h))) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0 (fun n => hBsm.forall n)
  have hJmh : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε h) :=
    Work.FTS.StrongEps.HkMem_Jeps (ρ := ρ) (k := 4) hρ.moll hα hε0
      (fun n => hhs.forall n) (Work.FTS.OpenPkg.HkMem_mono_open hhs 4 (by norm_num) hmh)
  have hJsme : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε h) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0 (fun n => hhs.forall n)
  -- the cuts agree with the data on the open quadrant
  have hcutA : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)) z θ
        = Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ f) z θ :=
    fun z θ hh => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ f) b a hh
  have hcutB : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ
        = Work.Spaces.mixed b a (Work.Spaces.mixed b₀ a₀ h) z θ :=
    fun z θ hh => mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) b a hh
  -- the order bounds
  have hord1 : (a + a₀) + (b + b₀) ≤ 4 := by omega
  have hord2 : (a + a₀) + (b + 1 + b₀) ≤ 5 := by omega
  have hord3 : (a + 1 + a₀) + (b + b₀) ≤ 5 := by omega
  -- the three diagonal certificates
  have i1 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)) z θ) ^ 2)) volume := by
    refine integrable_slot_of_dom (m := 4) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ f))
      (D := f) hAsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hfs hmf)
    intro z θ hθ
    rw [hcutA z θ hθ]
    exact dom_comp_slot hα0 hfs hord1 (IsLeafW.add hleaf) hθ
  have i2 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2)) volume := by
    refine integrable_slot_of_dom (m := 5) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ h))
      (D := h) hBsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hhs hmh5)
    intro z θ hθ
    rw [hcutB z θ hθ]
    exact dom_comp_slot hα0 hhs (by omega : (a + a₀) + (b + b₀) ≤ 5) (IsLeafW.add hleaf) hθ
  have i3 : MeasureTheory.Integrable (Function.uncurry (fun z θ => w z θ
      * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε
          (cut (Work.Spaces.mixed b₀ a₀ h))) z θ) ^ 2)) volume := by
    refine integrable_slot_of_dom (m := 4) (ρ := w)
      (A := Work.FTS.StrongEps.Jeps ρ ε (cut (Work.Spaces.mixed b₀ a₀ h)))
      (D := Work.FTS.StrongEps.Jeps ρ ε h) hJsm (Jeps_zero_off ρ ε _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hJsme hJmh)
    intro z θ hθ
    rw [Jeps_cut ρ ε (Work.Spaces.mixed b₀ a₀ h)]
    exact dom_comp_slot_Jeps hα0 hhs hρ.moll hε0 hord1 (IsLeafW.add hleaf) hθ
  -- the cross term
  have i4 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * Work.Spaces.mixed b a (cut (Work.Spaces.mixed b₀ a₀ f)) z θ
        * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε
            (cut (Work.Spaces.mixed b₀ a₀ h))) z θ)) volume :=
    integrable_cross_of_zero_off
      (mixed_eq_zero_of_zero_off (cut_zero_off _) b a)
      (mixed_eq_zero_of_zero_off (Jeps_zero_off ρ ε _) b a)
      (hAsm.mixed b a).continuousOn (hJsm.mixed b a).continuousOn
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) i1 i3
  -- the two shifted slots of the second argument
  have i5 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed (b + 1) a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2))
      volume := by
    refine integrable_slot_of_dom (m := 5) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ h))
      (D := h) hBsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hhs hmh5)
    intro z θ hθ
    rw [show Work.Spaces.mixed (b + 1) a (cut (Work.Spaces.mixed b₀ a₀ h)) z θ
        = Work.Spaces.mixed (b + 1) a (Work.Spaces.mixed b₀ a₀ h) z θ from
      mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) (b + 1) a hθ]
    exact dom_comp_slot hα0 hhs hord2 (IsLeafW.mono hleaf (Nat.le_add_right a a₀)) hθ
  have i6 : MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      w z θ * (Work.Spaces.mixed b (a + 1) (cut (Work.Spaces.mixed b₀ a₀ h)) z θ) ^ 2))
      volume := by
    refine integrable_slot_of_dom (m := 5) (ρ := w) (A := cut (Work.Spaces.mixed b₀ a₀ h))
      (D := h) hBsm (cut_zero_off _)
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.continuousOn_leafW hleaf)
      (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leaf_nonneg hleaf) ?_
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces3.integrable_HkIntegrand
        hhs hmh5)
    intro z θ hθ
    rw [show Work.Spaces.mixed b (a + 1) (cut (Work.Spaces.mixed b₀ a₀ h)) z θ
        = Work.Spaces.mixed b (a + 1) (Work.Spaces.mixed b₀ a₀ h) z θ from
      mixed_cut_eqOn_Q0 (Work.Spaces.mixed b₀ a₀ h) b (a + 1) hθ]
    exact dom_comp_slot hα0 hhs hord3 (IsLeafW.mono hleaf (by omega : a ≤ a + 1 + a₀)) hθ
  exact ⟨i1, i2, i3, i4, i5, i6⟩


end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
