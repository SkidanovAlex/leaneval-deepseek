import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

/-- `SlotBd` for `Φ̃ = PhiTil α g (E g)`: the `U`-slot `Uprime α Φ̃ = Uop α Φ̃ / sin 2θ` and the
`V`-slot `Vop Φ̃` have sup bounds on the open quadrant in terms of the package's `ℋ⁶`-bounds.
Route: `EllPkgK α 6 Ce g (E g)` gives `HQo α 6` (i.e. `SmoothOpen ∧ HkMem α 6`) of both slots with
`HkNorm α 6 (slot) ≤ Ce * Xn6 α g`, and
`Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le` gives `|D_z^b D_θ^a f| ≤ C(α) * HkNorm α 6 f` for
`a + b ≤ 4`; SlotBd needs `D_z^j Uprime` (j ≤ 2), `mixed 0 1 Uprime = D_θ U'`, and `D_z^j Vop`
(j ≤ 1).  Note `Uprime α Φ̃ = Uop α Φ̃ / s2` definitionally, and `mixed b 0 = DzIter b`. -/
theorem slotBd_phiTil {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fn),
      Work.FTS.ClassC.ClassC α g → Work.FTS.ClassC.EllPkgK α 6 Ce g (E g) →
      Work.FTS.StreamBdryIface.SlotBd α (Work.Construction.PhiTil α g (E g))
        (K * (Ce * Work.FTS.StrongGlobal.Xn6 α g)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le α hα hα1
  refine ⟨C, hCpos, ?_⟩
  intro E g hg hK
  -- The two slots are exactly the ones packaged by `EllPkgK α 6 Ce g (E g)`.
  have hUmem : Work.FTS.VocabO.HQo α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) := hK.U.1
  have hVmem : Work.FTS.VocabO.HQo α 6
      (Work.Construction.Vop (Work.Construction.PhiTil α g (E g))) := hK.V.1
  have hUnorm : Work.Spaces.HkNorm α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g := hK.U.2
  have hVnorm : Work.Spaces.HkNorm α 6
      (Work.Construction.Vop (Work.Construction.PhiTil α g (E g)))
        ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g := hK.V.2
  -- `HkNorm ≥ 0`, so the package forces the scale factor to be nonnegative.
  have hMnn : 0 ≤ Ce * Work.FTS.StrongGlobal.Xn6 α g := by
    have h1 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
          / Work.Construction.s2 θ) := Work.Spaces.HkNorm_nonneg _ _ _
    linarith
  -- `Uprime` is the `U`-slot, definitionally.
  have hUeq : Work.FTS.StreamBdryIface.Uprime α (Work.Construction.PhiTil α g (E g))
      = (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
          / Work.Construction.s2 θ) := rfl
  intro z θ hzθ
  obtain ⟨hz, hθ0, hθ2⟩ : 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
    simpa only [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] using hzθ
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    have h := hC (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) hUmem.1 hUmem.2 j 0 (by omega) z θ hz hθ0 hθ2
    have hb := mul_le_mul_of_nonneg_left hUnorm hCpos.le
    calc |Work.Spaces.DzIter j (Work.FTS.StreamBdryIface.Uprime α
          (Work.Construction.PhiTil α g (E g))) z θ|
        = |Work.Spaces.mixed j 0 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) z θ| := by
          rw [hUeq, Work.Spaces.mixed_zero_right]
      _ ≤ C * Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) := h
      _ ≤ C * (Ce * Work.FTS.StrongGlobal.Xn6 α g) := hb
  · have h := hC (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α g (E g)) z θ
        / Work.Construction.s2 θ) hUmem.1 hUmem.2 0 1 (by omega) z θ hz hθ0 hθ2
    have hb := mul_le_mul_of_nonneg_left hUnorm hCpos.le
    calc |Work.Spaces.mixed 0 1 (Work.FTS.StreamBdryIface.Uprime α
          (Work.Construction.PhiTil α g (E g))) z θ|
        = |Work.Spaces.mixed 0 1 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) z θ| := by
          rw [hUeq]
      _ ≤ C * Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.Uop α
            (Work.Construction.PhiTil α g (E g)) z θ / Work.Construction.s2 θ) := h
      _ ≤ C * (Ce * Work.FTS.StrongGlobal.Xn6 α g) := hb
  · intro j hj
    have h := hC (Work.Construction.Vop (Work.Construction.PhiTil α g (E g)))
        hVmem.1 hVmem.2 j 0 (by omega) z θ hz hθ0 hθ2
    have hb := mul_le_mul_of_nonneg_left hVnorm hCpos.le
    calc |Work.Spaces.DzIter j (Work.Construction.Vop
          (Work.Construction.PhiTil α g (E g))) z θ|
        = |Work.Spaces.mixed j 0 (Work.Construction.Vop
            (Work.Construction.PhiTil α g (E g))) z θ| := by
          rw [Work.Spaces.mixed_zero_right]
      _ ≤ C * Work.Spaces.HkNorm α 6 (Work.Construction.Vop
            (Work.Construction.PhiTil α g (E g))) := h
      _ ≤ C * (Ce * Work.FTS.StrongGlobal.Xn6 α g) := hb

end Work.FTS_EllLimOK.ProducerH
