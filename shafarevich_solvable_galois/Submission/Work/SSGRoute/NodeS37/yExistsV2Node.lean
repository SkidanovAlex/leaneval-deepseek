import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.NodeS37.chainCleanNode
import Submission.Work.SSGRoute.NodeS37.yPrescribedNode
import Submission.Work.SSGRoute.step4_coker_data_of_level_data
import Submission.Work.SSGRoute.step4_y_tnew_split_T0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! TEMPORARY COPY (node lane, session 42) of `Submission/Work/SSGRoute/step4_y_exists_v2.lean`.
The only differences are (i) the import of `step4_y_escape_v2.ChainCleanV2` is replaced by this
lane's `NodeS37.chainCleanNode` (a verbatim copy of that file whose `ySeriesTwo_kill_v3` exponent
induction is rewritten in `ZMod p` instead of `•`-notation, so that it still compiles under the
global `priority := 1300` `SMul` instance added to `properStageAssemblyData.lean:378`), and (ii) the
node theorem is named `step4_y_exists_v2_node`.  Delete this file once that instance is made local
(see `URGENT_smul_instance_breaks_nsmul_and_chaincleanv2.md`). -/

/-! Guidance from the project lead (the requester):

LEAD 09-30: new Step-4 route (design: _NOTE_STEP4_DESIGN.md at the workspace root; read the section for your node). step4_yLarge_exists was FALSE (it asks for an everywhere-unramified y); Step4YPrescribed with the escape at D.Λ is right. Frattini argument for i ≥ 2 (N1), Grünwald with escape (N2, pairing-free; do NOT use kummerChar_eq_zero_iff_local_powClass, which has a sorry), the E-valued version (N3), local data (N4), and the (1,1) → (2,1) step via shafarevich_existence (N5). No Hochschild–Serre transgression and no Poitou–Tate input. Import sibling nodes you depend on (sorried until they land).
-/

/-! ## State of this node (prover's note, session 09-30)

This file **builds** and its proof is complete; its only non-logical axiom is the `sorry` of
`Work.SSGRoute.GrunwaldEscapeCore.grunwald_escape_correction`
(`Submission/Work/SSGRoute/GrunwaldEscapeCore/grunwald_escape_correction.lean:220`), reached through
the rewired chain
`step4_y_exists_v2` → `step4_grunwald_E_escape_v2.gesv2_grunwald_escape_support_zmod` →
`Work.SSGRoute.grunwald_escape_relative_smul_form` → `grunwald_escape_relative_core` →
`GrunwaldEscapeCore.grunwald_escape_correction`.
Every other declaration in the cone is axiom-clean (N1 `step4_frattini_newPlace_v2`, N3
`grunwald_escape_support_E_v2`, N4 `step4_y_localData_escape_v2`, the clause verification and the
coker-datum existence are all proved in this directory).  So the node lands as soon as that single
arithmetic theorem is proved anywhere.

Pieces of that theorem proved this session, in `Submission/Work/SSGRoute/step4_y_escape_v2/`:
`RayClass.lean` (ray-class Čebotarev `Work.SSGRoute.rayClass_chebotarev_v2`, unconditional),
`ReadOff.lean` (`Work.SSGRoute.readOff_gesU`, the reading-off of `U = im(Kˣ·E_{T,unr})`) and
`ChebotarevSplit.lean` (`Work.SSGRoute.chebotarev_split_of_mem_sup`, Čebotarev with the split
condition, from the orthogonality `x ∈ U ⊔ N_{N/K}C_N`).  See
`NOTE_step4_y_exists_v2_status.md`, `PING_rayClass_chebotarev_proved.md` and
`PING_readOff_gesU_proved.md` in `Submission/Work/SSGRoute/`. -/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

/-- The coker-side datum with `D.m = n` (a local copy of `Work.SSGRoute.step4_coker_data_exists`,
kept here so that this module does not import the `step4_yLarge_exists` lane). -/
theorem step4_coker_data_exists_v2 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j) (hn : 1 ≤ n) :
    ∃ D : Work.SSGRoute.Step4CokerData p K n i j, D.m = n := by
  obtain ⟨φn, ψn, hdata⟩ := Work.SSGRoute.exists_data_of_isProperStage p K n i j (hP n hn)
  obtain ⟨D, hm, -, -, -⟩ :=
    Work.SSGRoute.step4_coker_data_of_level_data p K n i j n hn le_rfl
      (Work.CohomologicalShrinking.OperatorMap.ofLe (K ≃ₐ[ℚ] K) le_rfl) φn ψn hdata
  exact ⟨D, hm⟩

/-- `Step4YPrescribed` for every coker datum, from the arithmetic input
`Work.SSGRoute.step4_y_localData_escape_v2` (node N4, proved in `step4_y_chain_v2`) and the proved
clause verification `step4_yPrescribed_of_localData` (this is the body of the sibling node
`step4_y_prescribed_v2`, inlined so that this module depends on the arithmetic input only). -/
theorem step4_y_prescribed_v2' (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : 2 ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hTnewS : ∀ A ∈ Tnew, A ∈ D.S)
    (hT0Tnew : ∀ A ∈ D.T0, A ∉ Tnew)
    (hTnewfin : ∀ A ∈ Tnew, SSGRoute.IsFinPlace ℚ A)
    (hTnewnotp : ∀ A ∈ Tnew, ¬ A.valuation (p : SSGRoute.QBar) < 1)
    (hTnewφ : ∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1)
    (hTnewsplit : ∀ A ∈ Tnew, SSGRoute.IsSplitIn ℚ K A)
    (hηt : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A,
        ηt A hA (σ * τ) = ηt A hA σ + ηt A hA τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (ηt A hA) ∧
      (∀ σ, SSGRoute.IsInertia ℚ A σ → ηt A hA σ = 0) ∧
      IsCyclic (Subgroup.closure
        ((flowTwistE p K n i j (ηt A hA) D.psi) ''
          (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        flowTwistE p K n i j (ηt A hA) D.psi τ = flowTwistE p K n i j (ηt A hA) D.psi σ)) :
    Step4YPrescribed D Tnew ηt := by
  obtain ⟨hL⟩ :=
    Work.SSGRoute.step4_y_localData_escape_v3 p K n i j hj hji hi hμ D Tnew ηt hTnewS hTnewfin
      hTnewφ hTnewsplit (fun A hA => ⟨(hηt A hA).1, (hηt A hA).2.1⟩)
  exact Work.SSGRoute.step4_yPrescribed_of_localData_node p K n i j D Tnew ηt hTnewS hT0Tnew hTnewfin
    hTnewnotp hTnewφ hTnewsplit (fun A hA σ hσ => (hηt A hA).2.2.1 σ hσ) hL

/-- CORRECTED (ssg8): the old statement plus `hi : 2 ≤ i`; the proof is unchanged except that it
passes `hi` to the Fourth-Step arithmetic.  The case `(i,j) = (1,1)` is handled by `scholz_two_one` at
the level of `scholz_succ_of_properStage`. -/
theorem step4_y_exists_v2_node (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : 2 ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j) (hn : 1 ≤ n) :
    ∃ (D : Work.SSGRoute.Step4CokerData p K n i j),
      ∃ y : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j,
        Work.SSGRoute.Step4YData p K n i j D y := by
  obtain ⟨D, _⟩ := step4_coker_data_exists_v2 p K n i j hj hji hμ hP hn
  obtain ⟨Tnew, ηt, hTnewS, hT0Tnew, hTnewfin, hTnewnotp, hTnewφ, hTnewsplit, hcover, hηt⟩ :=
    Work.SSGRoute.step4_y_tnew_split_T0 p K n i j hj hji D
  have hpres :=
    step4_y_prescribed_v2' p K n i j hj hji hi hμ D Tnew ηt hTnewS hT0Tnew hTnewfin hTnewnotp
      hTnewφ hTnewsplit hηt
  obtain ⟨y, hyoff, hyadd, hyloc, hesc, hinert, hdecomp, hT0, hTnew, hconjTnew, hconjT0⟩ := hpres
  exact ⟨D, y, Work.SSGRoute.fork_step4_yData_of_prescribed D Tnew ηt hTnewS hTnewfin hTnewnotp
    hTnewφ hTnewsplit hcover hηt y hyoff hyadd hyloc hesc hinert hdecomp hT0 hTnew hconjTnew
    hconjT0⟩

end Work.SSGRoute
