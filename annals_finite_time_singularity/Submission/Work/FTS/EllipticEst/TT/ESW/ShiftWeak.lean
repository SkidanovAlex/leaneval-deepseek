/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Cores/Repair/DzShift` — the `D_z`-shift of the weak class, in a *buildable* module

The piece proved here is the radial shift of the weak elliptic hypothesis class

  `Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ  →  EllWeakPos α (k-1) (D_z F) (D_z Ψ)`

for `2 ≤ k`, i.e. the paper's Step 3 (`L(D_R Ψ) = D_R F`, "the equation commutes with `D_R`")
which lets the induction hypothesis at level `k-1` be applied to the *sliced* data.

## Why this file exists

The same result is proved in `Submission/Work/FTS/EllipticEst/remov/EllWeakPos_DzIter_one_shift.lean`
(declaration `EllWeakPos_DzIter_one_shift_of_two_le`), but that module **cannot be built**: it
imports `remov/Fstar_DzIter_one_Psi.lean`, which imports `remov/DzIter_one_Psi_estimate.lean`,
which imports the module `remov/pzMulSinCos2RectIntegrable` that has been **deleted** from the tree
after its statement was refuted (`remov/NOTES_pzMulSinCos2RectIntegrable_FALSE.md`).  Consequently
`remov/EllWeakPos_DzIter_one_shift.lean`, and with it the whole general-`ℋ^k` chain
(`remov/A_top_slot_bound`, `remov/B_top_slot_bound`, `remov/EllEstUnif_top_core`,
`remov/EllEstUnif_step`, `Mine/ShiftLevel`, `Mine/LevelOne`), does not elaborate at all.

This module is a **faithful copy** of the *proof* of that file with the broken imports removed and
the two angular-moment inputs supplied by their *proved*, importable versions:

* the `F`-half `F_*(D_z F) ≡ 0` for `k ≥ 2` — `remov.Fstar_DzIter_one_F_ge_two` (proved);
* the `Ψ`-half `F_*(D_z Ψ) ≡ 0` for `k ≥ 1` — `Mine.FstarDzOnePsi` (proved);
* (the `k = 1` instance of the `F`-half is *false* from `EllWeakPos α 1` alone, see the notes of
  `Mine/ShiftLevel.lean`: it would need the boundary trace of `∂_zΨ` at `θ = 0`.)

The declarations are placed in the namespace `Work.FTS.EllipticEst.Cores.Repair`, so that this
module can be imported *together* with the original (once the latter is repaired) without an
environment clash.

## The analytic content (all of it bookkeeping)

* `SmoothOpen_of_bslOp_eq` — the source `F` of the weak class is `C^∞` on the open quadrant
  (it agrees there with `bslOp α Ψ`);
* `HkIntegrand_Dz_shift_le` and `HkMem_Dz_shift` — the pointwise domination
  `HkIntegrand α (k-1) (D_z f) ≤ (k + k²)·HkIntegrand α k f` and its membership form;
* `Dz_pthIter_two_comm` — `D_z` commutes with `∂_θ²` on the open quadrant (Clairaut twice);
* `EllWeakPos_DzIter_one_shift_of_moments` / `..._of_two_le` — the nine fields of the shifted
  datum: equation (`bslOp_DzIter_eq`), Dirichlet data, the two moment conditions, smoothness,
  and the three `HkMem` clauses (through `HkMem_Dz_shift`, `ZsqPz2Comm` and `Dz_pthIter_two_comm`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDescent
import Submission.Work.EllipticEst.H2W.pthIter2_DzIter_comm
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two
import Submission.Work.FTS.EllipticEst.Mine.FstarDzOnePsi
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.TT.ESW.OpenMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW.Shift

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools -/

/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots: for `f` of class `C^∞` on the open quadrant and `(z,θ)` in the open
quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Work.FTS.EllipticEst.remov.Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Work.FTS.EllipticEst.remov.Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Work.FTS.EllipticEst.remov.Step.DzIter_congr_of_isOpen Work.FTS.EllipticEst.remov.Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Work.FTS.EllipticEst.remov.Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The pointwise `D_z`-shift bound on the open quadrant.**  Every slot of
`HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the commutation of `D_z`
with `D_θ^i`), and each single slot is dominated by the whole integrand; counting `k` radial and
`k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Work.FTS.EllipticEst.remov.Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Work.FTS.EllipticEst.remov.Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2 := by
      unfold Work.FTS.EllipticEst.remov.Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Work.FTS.EllipticEst.remov.Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Work.FTS.EllipticEst.remov.Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Work.FTS.EllipticEst.remov.Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Work.FTS.EllipticEst.remov.Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Work.FTS.EllipticEst.remov.Step.Zsum k f z θ + Work.FTS.EllipticEst.remov.Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine Work.FTS.EllipticEst.TT.ESW.HkMem_of_majorant_ae α (k - 1) (f := Work.Spaces.Dz f)
    (M := fun z θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
    ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllipticEst.SmoothOpen.Dz hf).continuousOn_HkIntegrand α (k - 1)
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · show MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [MeasureTheory.integral_const_mul] using hmem.2.const_mul _
  · intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | hz0
    · subst h0
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ _ => by
        rw [Work.FTS.LocData.HkIntegrand_zero_fst α (k - 1) (Work.Spaces.Dz f) θ,
          Work.FTS.LocData.HkIntegrand_zero_fst α k f θ, mul_zero]
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun θ hθ =>
        HkIntegrand_Dz_shift_le α hk f hz0 hθ hf

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice. -/
theorem pz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ
      (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ)) := by
  intro z θ hz hθ hlt
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ, hlt⟩
  have hcd : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      ContDiffAt ℝ 2 (Function.uncurry Ψ) (z', θ') := fun z' θ' hz' hθ' hlt' =>
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨ 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', hθ', hlt'⟩))
  have hcd_pth : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pth Ψ)) (z, θ) :=
    ((Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ψ)).mp
      (Work.FTS.EllipticEst.SmoothOpen.pth hΨ) 2).contDiffAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hmem)
  have h1 : Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ :=
    Work.Spaces.pz_pth_comm (f := Work.Spaces.pth Ψ) hcd_pth
  have hagree : Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.pz (Work.Spaces.pth Ψ))
      (Work.Spaces.pth (Work.Spaces.pz Ψ)) :=
    fun z' θ' hz' hθ' hlt' => Work.Spaces.pz_pth_comm (f := Ψ) (hcd z' θ' hz' hθ' hlt')
  have h2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth Ψ)) z θ
      = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz Ψ)) z θ :=
    Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
      (fun p hp => by
        obtain ⟨z', θ'⟩ := p
        exact hagree z' θ' hp.1 hp.2.1 hp.2.2) hmem
  show Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  exact h1.trans h2

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.** -/
theorem Dz_pthIter_two_comm {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.AgreeOnQ (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))
      (Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)) := by
  have hplain := pz_pthIter_two_comm hΨ
  have hmul : Work.Spaces.pth (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pz Ψ z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz Ψ z θ') θ
    rw [deriv_const_mul_field]
  have hstep : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
      = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ := by
    have h2 : Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ)
        = Work.Spaces.pth (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ) := by
      rw [← hmul]
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
    rw [h2]
    funext z θ
    show deriv (fun θ' => z * Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz Ψ) z θ') θ
    rw [deriv_const_mul_field]
  intro z θ hz hθ hlt
  show z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.Dz Ψ) z θ
  rw [hstep, hplain z θ hz hθ hlt]

/-! ## The shift -/

/-- **The assembly of the shift, given the two moment conditions.**  All nine fields of
`EllWeakPos α (k-1) (D_z F) (D_z Ψ)` are produced here except the two moment conditions, which
are supplied as explicit hypotheses. -/
theorem EllWeakPos_DzIter_one_shift_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k)
    {F Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · exact hmomF
  · exact hmomΨ
  · intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.TT.ESW.SmoothOpen_zsq_mul (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.memA
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `ℋ^{k-1}`-honesty of the diagonal second-order term of the shifted datum:
    -- `z ∂_z∂_θθ(D_zΨ) = D_z (D_z ∂_θθΨ)`, and `∂_θθ` commutes with `D_z`.
    have hZ : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ))) :=
      HkMem_Dz_shift hk
        (Work.FTS.EllipticEst.SmoothOpen.Dz
          (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2))
        h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hZ ?_
    intro z hz θ hθ
    show Work.Spaces.Dz (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) z θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        (Work.EllipticEst.H2W.pthIter2_DzIter_comm hSΨ 1) ⟨hz, hθ⟩
    rw [hpe, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
    rfl


/-- **The shift, for `2 ≤ k`** — the instance needed by the induction step of `prop:Hk` (the
shifted data are consumed at level `k-1 ≥ 2`) and by the level-`2` assembly.  Both moment
conditions are available from proved lemmas: the `F`-half from `Fstar_DzIter_one_F_ge_two`
(which needs `k ≥ 2`) and the `Ψ`-half from `Mine.FstarDzOnePsi`. -/
theorem EllWeakPos_DzIter_one_shift_of_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k)
    {F Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments (by omega) h
    (Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two hk h)
    (Work.FTS.EllipticEst.Mine.FstarDzOnePsi α (by omega) F Ψ h)

end Work.FTS.EllipticEst.TT.ESW.Shift
