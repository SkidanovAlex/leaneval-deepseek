-- FORK of `remov.EllWeakPos_DzIter_one_shift` (agent of `slice_rhs_domination`, 2026-10-04).
--
-- Copy of Submission/Work/FTS/EllipticEst/remov/EllWeakPos_DzIter_one_shift.lean with two
-- changes, both aimed at removing the fragile subsystem
--   EllHyp_certificates -> propHk_fts -> Prop.{Level0,Step,bSlotTop} -> Cert.HkMem_{Fstar,Gbar}_sin
-- (a live construction site: import cycles and mid-refactor type errors) from the dependency
-- cone of `remov.slice_rhs_domination`:
--   1. the import of `…EllipticEst.EllHyp_certificates` is dropped (that module is the fragile one);
--   2. the two declarations of `EllHyp_certificates` that the body uses -- `SmoothOpen.zsq_mul`
--      and `HkMem_of_majorant_ae` -- are taken instead from the *green* repair copy
--      `…EllipticEst.AeMom.Repair.ShiftAeRepair`, which reproduces their statements verbatim
--      under the fresh namespace `Work.FTS.EllipticEst.AeMom.Repair` (written by another agent
--      for exactly this reason); the two occurrences in the body are redirected accordingly.
-- Declaration names and namespaces are otherwise unchanged, so the copied proof is verbatim.
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.TT.SliceDatum
import Submission.Work.FTS.EllipticEst.TT.bslOp_DzIter_eq
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_Psi
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Tools

Three bookkeeping facts are needed, none of which is analytic:

* `SmoothOpen_of_bslOp_eq`: the source `F` of the weak class is `C^∞` on the open quadrant,
  because there it coincides with `bslOp α Ψ`;
* `HkMem_Dz_shift`: the *membership* form of the `D_z`-shift
  `HkIntegrand α (k-1) (D_z f) ≤ (k + k²)·HkIntegrand α k f` (`Step.HkIntegrand_shift_le`),
  obtained through the domination lemma `HkMem_of_majorant_ae`;
* `Dz_pthIter2_eq`: `D_z` commutes with `∂_θ²` on the open quadrant (Clairaut twice). -/

/-- **The source of the weak class is `C^∞` on the open quadrant.**  On `Q0` it agrees with
`bslOp α Ψ`, which is `C^∞` there by `SmoothOpen_bslOp_of_smoothOpen`. -/
theorem SmoothOpen_of_bslOp_eq {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (heq : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hΨ) heq

/-- The shifted mixed slots, at the genuine smooth order: for `f` of class `C^∞` on the open
quadrant and `(z,θ)` in the open quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`.
This is `D_z`-commutation with `D_θ^i` (`DthIterDzCommOpen`) followed by
`D_z^j (D_z g) = D_z^{j+1} g` and the local congruence of iterated `D_z` on the open quadrant. -/
theorem mixed_Dz_shift_eq {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Step.DzIter_congr_of_isOpen Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The pointwise `D_z`-shift bound on the open quadrant, at the genuine smooth order.**
Every slot of `HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the
commutation of `D_z` with `D_θ^i`), and each single slot is dominated by the whole integrand;
counting `k` radial and `k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2 := by
      unfold Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
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
  rw [Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Step.Zsum k f z θ + Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]

/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`.  This is the domination lemma
`Work.FTS.LocData.HkMem_of_majorant` applied to the pointwise bound
`HkIntegrand_Dz_shift_le`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine Work.FTS.EllipticEst.AeMom.Repair.HkMem_of_majorant_ae α (k - 1) (f := Work.Spaces.Dz f)
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

/-- **`∂_z` commutes with `∂_θ²` on the open quadrant**: Clairaut's theorem applied twice
(the first step with `∂_θ Ψ` as the function, the second by congruence on the open set). -/
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

/-- **`D_z` commutes with `∂_θ²` on the open quadrant.**  Since `D_z f = z·∂_z f` and the
factor `z` does not depend on `θ`, the plain commutation `pz_pthIter_two_comm` gives the
identity for `D_z` as well. -/
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

/-! ## The target -/

/-- **The assembly of the shift, given the two moment conditions.**

All nine fields of `EllWeakPos α (k-1) (D_z F) (D_z Ψ)` are produced here except the two moment
conditions, which are supplied as explicit hypotheses:

* the equation is preserved because `bslOp` commutes with `D_z`
  (`Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`);
* the Dirichlet data are preserved (`Work.FTS.EllipticEst.TT.DzIter_zero_at_zero`,
  `..._pi_half`);
* the smoothness is preserved (`SmoothOpen.DzIter`);
* the `ℋ`-membership of the three fields follows from the pointwise domination
  `HkIntegrand α (k-1) (D_z g) ≤ ((k:ℝ)+(k:ℝ)*(k:ℝ)) * HkIntegrand α k g`
  (`Work.FTS.EllipticEst.remov.HkIntegrand_Dz_shift_le`, at the genuine `C^∞` order, via
  `Work.FTS.EllipticEst.HkMem_of_majorant_ae`) for `g ∈ {F, z²∂_zzΨ, ∂_θθΨ}`;
* the auxiliary identities are `pthIter 2 (D_z Ψ) = D_z (pthIter 2 Ψ)`
  (`Dz_pthIter_two_comm`) and `z² ∂_zz(D_z Ψ) = D_z (z² ∂_zzΨ)`
  (`Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm`), both pointwise on the open quadrant. -/
theorem EllWeakPos_DzIter_one_shift_of_moments {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hmomF : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0)
    (hmomΨ : ∀ z, 0 < z → Work.Elliptic.Fstar (Work.Spaces.DzIter 1 Ψ) z = 0) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) := by
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen h
  have hSF : Work.FTS.EllipticEst.SmoothOpen F :=
    SmoothOpen_of_bslOp_eq hSΨ (fun z θ hz hθ hlt => h.1 z hz θ hθ hlt)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the equation commutes with `D_z`
    exact Work.FTS.EllipticEst.TT.bslOp_DzIter_eq α F Ψ 1 h.smooth h.1
  · -- the Dirichlet data at `θ = 0`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_zero Ψ 1 h.zero
  · -- the Dirichlet data at `θ = π/2`
    exact Work.FTS.EllipticEst.TT.DzIter_zero_at_pi_half Ψ 1 h.pi_half
  · -- the source moment condition
    exact hmomF
  · -- the solution moment condition
    exact hmomΨ
  · -- smoothness on the open quadrant is preserved by `D_z`
    intro n
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.DzIter 1 Ψ)).mp
      (Work.FTS.EllipticEst.TT.EllWeakPos.smoothOpen_DzIter h 1) n
  · -- `D_z F ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz F) :=
      HkMem_Dz_shift hk hSF h.memF
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using hmem
  · -- `z² ∂_zz(D_z Ψ) ∈ ℋ^{k-1}`
    have hG : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
      Work.FTS.EllipticEst.AeMom.Repair.SmoothOpen.zsq_mul (Work.FTS.EllipticEst.SmoothOpen.pzIter hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) :=
      HkMem_Dz_shift hk hG h.memA
    have hEqOn := Work.FTS.EllipticEst.DzAmgm.ZsqPz2Comm Ψ hSΨ 1 0
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact (hEqOn (show ((z, θ) : ℝ × ℝ) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)
      from ⟨hz, hθ⟩)).symm
  · -- `∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)) :=
      HkMem_Dz_shift hk (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2) h.memB
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    exact Dz_pthIter_two_comm hSΨ z θ hz hθ.1 hθ.2
  · -- `z ∂_z∂_θθ(D_z Ψ) ∈ ℋ^{k-1}`
    have hGs : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) :=
      Work.FTS.EllipticEst.SmoothOpen.Dz
        (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hSΨ 2)
    have hmem : Work.Spaces.HkMem α (k - 1)
        (Work.Spaces.Dz (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ)) :=
      HkMem_Dz_shift hk hGs h.memZPth2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α (k - 1) hmem ?_
    intro z hz θ hθ
    have hEqOn : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pthIter 2 Ψ)))
        (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      rintro ⟨z', θ'⟩ ⟨hz', hθ'⟩
      exact Dz_pthIter_two_comm hSΨ z' θ' hz' hθ'.1 hθ'.2
    have hpe : Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) z θ
        = Work.Spaces.pz (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ :=
      Work.Spaces.pz_congr_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
        hEqOn.symm ⟨hz, hθ⟩
    rw [hpe]
    rfl

/-- **The radially differentiated data are again of the weak class, one level down.**

`EllWeakPos α (k-1) (D_z F) (D_z Ψ)` is exactly the hypothesis needed to apply the induction
hypothesis `EllEstUnif (k-1)` to the *sliced* data: the equation is preserved because `bslOp`
commutes with `D_z` (`Work.FTS.EllipticEst.TT.bslOp_DzIter_eq`), the Dirichlet data are preserved
(`Work.FTS.EllipticEst.TT.DzIter_zero_at_zero`, `..._pi_half`), the smoothness is preserved
(`SmoothOpen.DzIter`), the `ℋ`-membership of the three fields follows from the pointwise
domination `HkIntegrand α (k-1) (D_z g) ≤ ((k:ℝ)+(k:ℝ)*(k:ℝ)) * HkIntegrand α k g`
(`Work.FTS.EllipticEst.remov.Step.HkIntegrand_shift_le`, via
`Work.FTS.LocData.HkMem_of_majorant`) for `g ∈ {F, z²∂_zzΨ, ∂_θθΨ}`, and the two moment
conditions are the sibling `Work.FTS.EllipticEst.remov.Fstar_DzIter_one_eq_zero` (add
`import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_eq_zero`, once it is proved; it
may also be re-proved directly).
The auxiliary identities needed are `pthIter 2 (D_z Ψ) = D_z (pthIter 2 Ψ)` and
`z² ∂_zz(D_z Ψ) = D_z (z² ∂_zzΨ)` (both pointwise on the open quadrant). -/
theorem EllWeakPos_DzIter_one_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments hk h (Fstar_DzIter_one_F hk h)
    (Fstar_DzIter_one_Psi hk h)

/-- **The shift, for `2 ≤ k`.**  This is the instance of `EllWeakPos_DzIter_one_shift` which is
needed by the induction step of `prop:Hk` (the shifted data are consumed at level `k-1 ≥ 2`) and
by `shift_weak`; here both moment conditions are available from the *proved* lemmas
`Fstar_DzIter_one_F_ge_two` (the `F`-half, via the chain rule at `j = 0, 1` and the continuity of
`F_*(D_z F)`) and `Fstar_DzIter_one_Psi` (the `Ψ`-half, by the first-order difference-quotient
argument), so the statement is complete. -/
theorem EllWeakPos_DzIter_one_shift_of_two_le {α : ℝ} {k : ℕ} (hk : 2 ≤ k) {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.TT.EllWeakPos α (k - 1)
      (Work.Spaces.DzIter 1 F) (Work.Spaces.DzIter 1 Ψ) :=
  EllWeakPos_DzIter_one_shift_of_moments (by omega) h
    (Fstar_DzIter_one_F_ge_two hk h) (Fstar_DzIter_one_Psi (by omega) h)

end Work.FTS.EllipticEst.remov
