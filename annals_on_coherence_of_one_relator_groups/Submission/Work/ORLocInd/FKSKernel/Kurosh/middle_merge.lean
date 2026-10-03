import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.BSWalk
import Submission.Work.ORLocInd.FKSKernel.Kurosh.edgeRel_general
import Submission.Work.ORLocInd.FKSKernel.Kurosh.EdgeLink
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_inv
import Submission.Work.ORLocInd.FKSKernel.Kurosh.merge_case1
import Submission.Work.ORLocInd.FKSKernel.Kurosh.merge_case2
import Submission.Work.ORLocInd.FKSKernel.Kurosh.merge_case4
import Submission.Work.ORLocInd.FKSKernel.Kurosh.helpers
import Submission.Work.ORLocInd.FKSKernel.Kurosh.merge_case3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Quiver

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]
  {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
  

/-! ### Helper lemmas

The proof of `middle_merge` compares vertex-group elements living at *propositionally* equal vertex
orbits; `gEltHom_congr` is the congruence that transports `gEltHom` along such an equality (the
subtype proofs are irrelevant, only the underlying element of `G` matters). -/

private lemma gEltHom_congr {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
    (D : d.PresData) {A B : Work.ORBassSerre.orbitV G V} (h : A = B)
    {x : ↥(d.vgroup A)} {y : ↥(d.vgroup B)} (hxy : (x : G) = (y : G)) :
    d.gEltHom D A x = d.gEltHom D B y := by
  revert x y
  rw [h]
  intro x y hxy
  congr 1
  exact Subtype.ext hxy

/-- If `a • x = b • x` then `b⁻¹ * a` stabilises `x`. -/
private lemma mem_stabilizer_of_smul_eq {x : Quiver.Total V} {a b : G} (h : a • x = b • x) :
    b⁻¹ * a ∈ MulAction.stabilizer G x := by
  rw [MulAction.mem_stabilizer_iff, mul_smul, h, inv_smul_smul]

private lemma mk_smul_eq (g : G) (x : V) :
    (Quotient.mk'' (g • x) : Work.ORBassSerre.orbitV G V) = Quotient.mk'' x :=
  Quotient.sound ⟨g, rfl⟩

private lemma mk_smul_eq_total (g : G) (x : Quiver.Total V) :
    (Quotient.mk'' (g • x) : Work.ORBassSerre.orbitE G V) = Quotient.mk'' x :=
  Quotient.sound ⟨g, rfl⟩

private lemma mk_z (W : TreeDatum.PathWord d) (j : ℕ) :
    (Quotient.mk'' (W.z j) : Work.ORBassSerre.orbitV G V) = W.orb j := by
  show Quotient.mk'' (W.pre j • d.vert (W.orb j)) = W.orb j
  rw [mk_smul_eq, d.vert_mk]

private lemma orbit_F_true (W : TreeDatum.PathWord d) (j : ℕ) (h : W.stepB j = true) :
    (Quotient.mk'' (W.F j) : Work.ORBassSerre.orbitE G V) = W.stepE j := by
  show (Quotient.mk'' ((W.pre j * ((W.letter j).2 : G)) • d.move (W.stepE j) (W.stepB j)) :
    Work.ORBassSerre.orbitE G V) = W.stepE j
  rw [mk_smul_eq_total, h]
  exact d.orbit_move_true (W.stepE j)

private lemma orbit_F_false (W : TreeDatum.PathWord d) (j : ℕ) (h : W.stepB j = false) :
    (Quotient.mk'' (W.F j) : Work.ORBassSerre.orbitE G V) =
      Work.ORBassSerre.orbitEReverse (W.stepE j) := by
  show (Quotient.mk'' ((W.pre j * ((W.letter j).2 : G)) • d.move (W.stepE j) (W.stepB j)) :
    Work.ORBassSerre.orbitE G V) = Work.ORBassSerre.orbitEReverse (W.stepE j)
  rw [mk_smul_eq_total, h]
  exact d.orbit_move_false (W.stepE j)

private lemma reverse_injective' :
    Function.Injective (Quiver.Total.reverse : Quiver.Total V → Quiver.Total V) :=
  Function.Involutive.injective fun e => Quiver.Total.reverse_reverse e

private lemma orbit_backtrack (W : TreeDatum.PathWord d) {k : ℕ}
    (hback : W.F (k + 1) = (W.F k).reverse) :
    (Quotient.mk'' (W.F (k + 1)) : Work.ORBassSerre.orbitE G V) =
      Work.ORBassSerre.orbitEReverse (Quotient.mk'' (W.F k)) := by
  rw [hback, Work.ORBassSerre.orbitEReverse_mk]

private lemma stepB_eq_false {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

-- The four Γ-computations that merge a backtrack are proved separately, in the modules
-- `merge_case1`…`merge_case4` (imported above).

theorem middle_merge {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
    
    (D : d.PresData) (W : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.PathWord d) {k : ℕ}
    (hk : k + 1 < W.len) (hback : W.F (k + 1) = (W.F k).reverse) :
    ∃ l : d.Letter, l.1 = W.orb k ∧
      Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.Letter.gam (W.letter k) D *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D (W.stepE k) (W.stepB k) *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.Letter.gam (W.letter (k + 1)) D *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) *
        Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.Letter.gam (W.letter (k + 2)) D =
      Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.Letter.gam l D := by
  have hk' : k < W.len := by omega
  have hk0 : k ≤ W.len := by omega
  have hk1 : k + 1 ≤ W.len := by omega
  have hk2 : k + 2 ≤ W.len := by omega
  have horb2 : W.orb (k + 2) = W.orb k := by
    have hz : W.z (k + 2) = W.z k := by
      have h1 := W.F_left (k + 1) hk
      have h2 := W.F_right (k + 1) hk
      rw [hback, Quiver.Total.reverse_left] at h1
      rw [hback, Quiver.Total.reverse_right] at h2
      rw [W.F_right k hk'] at h1
      rw [W.F_left k hk'] at h2
      exact h2.symm
    have h := congrArg (fun v : V => (Quotient.mk'' v : Work.ORBassSerre.orbitV G V)) hz
    rwa [mk_z W (k + 2), mk_z W k] at h
  by_cases hb : W.stepB k = true
  · by_cases hb' : W.stepB (k + 1) = true
    · -- CASE 1
      have hE' : W.stepE (k + 1) = Work.ORBassSerre.orbitEReverse (W.stepE k) := by
        have h2 := orbit_backtrack W hback
        rw [orbit_F_true W (k + 1) hb', orbit_F_true W k hb] at h2
        exact h2
      have alpha : W.orb k = Work.ORBassSerre.Action.srcE (W.stepE k) := by
        rw [← W.step_src k hk', hb]
        rfl
      have beta : W.orb (k + 1) = Work.ORBassSerre.Action.tgtE (W.stepE k) := by
        rw [← W.step_tgt k hk', hb]
        rfl
      have hpre : W.pre (k + 1) = W.pre k * ((W.letter k).2 : G) * d.sElt (W.stepE k) := by
        rw [W.pre_succ, hb, d.moveElt_true]
      have hmem : d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * d.linkG (W.stepE k) ∈
          d.eGroup (W.stepE k) := by
        have h1 : W.F (k + 1) = (W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
            d.linkG (W.stepE k)) • (d.elift (W.stepE k)).reverse := by
          show (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) •
            d.move (W.stepE (k + 1)) (W.stepB (k + 1)) = _
          rw [hb']
          show (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) • d.elift (W.stepE (k + 1)) = _
          rw [hE', ← d.linkG_smul, ← mul_smul]
        have h2 : (W.F k).reverse = (W.pre k * ((W.letter k).2 : G)) •
            (d.elift (W.stepE k)).reverse := by
          show ((W.pre k * ((W.letter k).2 : G)) • d.move (W.stepE k) (W.stepB k)).reverse = _
          rw [hb, ← GraphAction.smul_reverse_apply]
          rfl
        have h : (W.pre (k + 1) * ((W.letter (k + 1)).2 : G) * d.linkG (W.stepE k)) •
            (d.elift (W.stepE k)).reverse =
            (W.pre k * ((W.letter k).2 : G)) • (d.elift (W.stepE k)).reverse := by
          rw [← h1, ← h2]
          exact hback
        have hmem0 := mem_stabilizer_of_smul_eq h
        rw [hpre] at hmem0
        have hsimp : (W.pre k * ((W.letter k).2 : G))⁻¹ * (W.pre k * ((W.letter k).2 : G) *
            d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * d.linkG (W.stepE k)) =
            d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * d.linkG (W.stepE k) := by group
        rw [hsimp] at hmem0
        rw [show MulAction.stabilizer G ((d.elift (W.stepE k)).reverse) =
            d.eGroup (W.stepE k) from stabilizer_reverse (d.elift (W.stepE k))] at hmem0
        exact hmem0
      have hu : ((W.letter k).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) = d.vgroup ((W.letter k).1) from by
          rw [← alpha, ← W.letter_orbit k hk0]]
        exact (W.letter k).2.2
      have hv : ((W.letter (k + 1)).2 : G) ∈
          d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) =
            d.vgroup ((W.letter (k + 1)).1) from by
          rw [← beta, ← W.letter_orbit (k + 1) hk1]]
        exact (W.letter (k + 1)).2.2
      have hw : ((W.letter (k + 2)).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) =
            d.vgroup ((W.letter (k + 2)).1) from by
          rw [← alpha, ← horb2, ← W.letter_orbit (k + 2) hk2]]
        exact (W.letter (k + 2)).2.2
      let c : ↥(d.eGroup (W.stepE k)) :=
        ⟨d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * d.linkG (W.stepE k), hmem⟩
      have hc_eq : (d.eGroupToTgt (W.stepE k) c : G) =
          ((W.letter (k + 1)).2 : G) * (d.linkK (W.stepE k) : G) := by
        rw [d.eGroupToTgt_apply]
        change (d.sElt (W.stepE k))⁻¹ * (d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) *
            d.linkG (W.stepE k)) * d.sElt (W.stepE k) =
          ((W.letter (k + 1)).2 : G) * (d.linkK (W.stepE k) : G)
        rw [show (d.linkK (W.stepE k) : G) = d.linkG (W.stepE k) * d.sElt (W.stepE k) from rfl]
        group
      have hγu : TreeDatum.Letter.gam (W.letter k) D =
          d.gEltHom D (Work.ORBassSerre.Action.srcE (W.stepE k)) ⟨((W.letter k).2 : G), hu⟩ :=
        gEltHom_congr D ((W.letter_orbit k hk0).trans alpha) rfl
      have hγv : TreeDatum.Letter.gam (W.letter (k + 1)) D =
          d.gEltHom D (Work.ORBassSerre.Action.tgtE (W.stepE k)) ⟨((W.letter (k + 1)).2 : G), hv⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 1) hk1).trans beta) rfl
      have hγw : TreeDatum.Letter.gam (W.letter (k + 2)) D =
          d.gEltHom D (Work.ORBassSerre.Action.srcE (W.stepE k)) ⟨((W.letter (k + 2)).2 : G), hw⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 2) hk2).trans (horb2.trans alpha)) rfl
      have hσ : TreeDatum.stepGam D (W.stepE k) (W.stepB k) = TreeDatum.stepGam D (W.stepE k) true := by rw [hb]
      have hσ' : TreeDatum.stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) =
          TreeDatum.stepGam D (Work.ORBassSerre.orbitEReverse (W.stepE k)) true := by rw [hb', hE']
      have hkey := merge_case1 D (W.stepE k) ((W.letter k).2 : G) ((W.letter (k + 1)).2 : G)
        ((W.letter (k + 2)).2 : G) hu hv hw c hc_eq
      have hy : ((W.letter k).2 : G) * (d.eGroupToSrc (W.stepE k) c : G) *
          (d.linkH (W.stepE k) : G) * ((W.letter (k + 2)).2 : G) ∈ d.vgroup (W.orb k) := by
        rw [alpha]
        exact mul_mem (mul_mem (mul_mem hu (d.eGroupToSrc (W.stepE k) c).2)
          (by rw [← tgtE_orbitEReverse]; exact (d.linkH (W.stepE k)).2)) hw
      refine ⟨⟨W.orb k, ⟨((W.letter k).2 : G) * (d.eGroupToSrc (W.stepE k) c : G) *
        (d.linkH (W.stepE k) : G) * ((W.letter (k + 2)).2 : G), hy⟩⟩, rfl, ?_⟩
      rw [hγu, hγv, hγw, hσ, hσ']
      exact hkey.trans (gEltHom_congr D alpha.symm rfl)
    · -- CASE 2
      have hbF' : W.stepB (k + 1) = false := stepB_eq_false hb'
      have hE' : W.stepE (k + 1) = W.stepE k := by
        have h2 := orbit_backtrack W hback
        rw [orbit_F_false W (k + 1) hbF', orbit_F_true W k hb] at h2
        exact Work.ORBassSerre.orbitEReverse_involutive.injective h2
      have alpha : W.orb k = Work.ORBassSerre.Action.srcE (W.stepE k) := by
        rw [← W.step_src k hk', hb]
        rfl
      have beta : W.orb (k + 1) = Work.ORBassSerre.Action.tgtE (W.stepE k) := by
        rw [← W.step_tgt k hk', hb]
        rfl
      have hpre : W.pre (k + 1) = W.pre k * ((W.letter k).2 : G) * d.sElt (W.stepE k) := by
        rw [W.pre_succ, hb, d.moveElt_true]
      have hmem : d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * (d.sElt (W.stepE k))⁻¹ ∈
          d.eGroup (W.stepE k) := by
        have h1 : W.F (k + 1) = ((W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
            (d.sElt (W.stepE k))⁻¹) • d.elift (W.stepE k)).reverse := by
          show (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) •
            d.move (W.stepE (k + 1)) (W.stepB (k + 1)) = _
          rw [hbF', hE']
          show (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) •
            ((d.sElt (W.stepE k))⁻¹ • d.elift (W.stepE k)).reverse = _
          rw [GraphAction.smul_reverse_apply, ← mul_smul]
        have h2 : (W.F k).reverse =
            ((W.pre k * ((W.letter k).2 : G)) • d.elift (W.stepE k)).reverse := by
          show ((W.pre k * ((W.letter k).2 : G)) • d.move (W.stepE k) (W.stepB k)).reverse = _
          rw [hb]
          rfl
        have h' : (W.pre (k + 1) * ((W.letter (k + 1)).2 : G) * (d.sElt (W.stepE k))⁻¹) •
            d.elift (W.stepE k) = (W.pre k * ((W.letter k).2 : G)) • d.elift (W.stepE k) := by
          apply reverse_injective'
          rw [← h1, ← h2]
          exact hback
        have hmem0 := mem_stabilizer_of_smul_eq h'
        rw [hpre] at hmem0
        have hsimp : (W.pre k * ((W.letter k).2 : G))⁻¹ * (W.pre k * ((W.letter k).2 : G) *
            d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * (d.sElt (W.stepE k))⁻¹) =
            d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * (d.sElt (W.stepE k))⁻¹ := by group
        rw [hsimp] at hmem0
        exact hmem0
      have hu : ((W.letter k).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) = d.vgroup ((W.letter k).1) from by
          rw [← alpha, ← W.letter_orbit k hk0]]
        exact (W.letter k).2.2
      have hv : ((W.letter (k + 1)).2 : G) ∈
          d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) =
            d.vgroup ((W.letter (k + 1)).1) from by
          rw [← beta, ← W.letter_orbit (k + 1) hk1]]
        exact (W.letter (k + 1)).2.2
      have hw : ((W.letter (k + 2)).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) =
            d.vgroup ((W.letter (k + 2)).1) from by
          rw [← alpha, ← horb2, ← W.letter_orbit (k + 2) hk2]]
        exact (W.letter (k + 2)).2.2
      let c : ↥(d.eGroup (W.stepE k)) :=
        ⟨d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) * (d.sElt (W.stepE k))⁻¹, hmem⟩
      have hc_eq : (d.eGroupToTgt (W.stepE k) c : G) = ((W.letter (k + 1)).2 : G) := by
        rw [d.eGroupToTgt_apply]
        change (d.sElt (W.stepE k))⁻¹ * (d.sElt (W.stepE k) * ((W.letter (k + 1)).2 : G) *
            (d.sElt (W.stepE k))⁻¹) * d.sElt (W.stepE k) = ((W.letter (k + 1)).2 : G)
        group
      have hγu : TreeDatum.Letter.gam (W.letter k) D =
          d.gEltHom D (Work.ORBassSerre.Action.srcE (W.stepE k)) ⟨((W.letter k).2 : G), hu⟩ :=
        gEltHom_congr D ((W.letter_orbit k hk0).trans alpha) rfl
      have hγv : TreeDatum.Letter.gam (W.letter (k + 1)) D =
          d.gEltHom D (Work.ORBassSerre.Action.tgtE (W.stepE k)) ⟨((W.letter (k + 1)).2 : G), hv⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 1) hk1).trans beta) rfl
      have hγw : TreeDatum.Letter.gam (W.letter (k + 2)) D =
          d.gEltHom D (Work.ORBassSerre.Action.srcE (W.stepE k)) ⟨((W.letter (k + 2)).2 : G), hw⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 2) hk2).trans (horb2.trans alpha)) rfl
      have hσ : TreeDatum.stepGam D (W.stepE k) (W.stepB k) = TreeDatum.stepGam D (W.stepE k) true := by rw [hb]
      have hσ' : TreeDatum.stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) =
          TreeDatum.stepGam D (W.stepE k) false := by rw [hbF', hE']
      have hkey := merge_case2 D (W.stepE k) ((W.letter k).2 : G) ((W.letter (k + 1)).2 : G)
        ((W.letter (k + 2)).2 : G) hu hv hw c hc_eq
      have hy : ((W.letter k).2 : G) * (d.eGroupToSrc (W.stepE k) c : G) *
          ((W.letter (k + 2)).2 : G) ∈ d.vgroup (W.orb k) := by
        rw [alpha]
        exact mul_mem (mul_mem hu (d.eGroupToSrc (W.stepE k) c).2) hw
      refine ⟨⟨W.orb k, ⟨((W.letter k).2 : G) * (d.eGroupToSrc (W.stepE k) c : G) *
        ((W.letter (k + 2)).2 : G), hy⟩⟩, rfl, ?_⟩
      rw [hγu, hγv, hγw, hσ, hσ']
      exact hkey.trans (gEltHom_congr D alpha.symm rfl)
  · have hbF : W.stepB k = false := stepB_eq_false hb
    by_cases hb' : W.stepB (k + 1) = true
    · -- CASE 3
      have hE' : W.stepE (k + 1) = W.stepE k := by
        have h2 := orbit_backtrack W hback
        rw [orbit_F_true W (k + 1) hb', orbit_F_false W k hbF] at h2
        rw [Work.ORBassSerre.orbitEReverse_involutive (W.stepE k)] at h2
        exact h2
      have alpha : W.orb k = Work.ORBassSerre.Action.tgtE (W.stepE k) := by
        rw [← W.step_src k hk', hbF]
        rfl
      have beta : W.orb (k + 1) = Work.ORBassSerre.Action.srcE (W.stepE k) := by
        rw [← W.step_tgt k hk', hbF]
        rfl
      have hpre : W.pre (k + 1) = W.pre k * ((W.letter k).2 : G) * (d.sElt (W.stepE k))⁻¹ := by
        rw [W.pre_succ, hbF, d.moveElt_false]
      have hmem : ((W.letter (k + 1)).2 : G) ∈ d.eGroup (W.stepE k) := by
        have h1 : W.F (k + 1) = (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) •
            d.elift (W.stepE k) := by
          show (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) •
            d.move (W.stepE (k + 1)) (W.stepB (k + 1)) = _
          rw [hb', hE']
          rfl
        have h2 : (W.F k).reverse = W.pre (k + 1) • d.elift (W.stepE k) := by
          show ((W.pre k * ((W.letter k).2 : G)) • d.move (W.stepE k) (W.stepB k)).reverse = _
          rw [hbF]
          show ((W.pre k * ((W.letter k).2 : G)) •
            ((d.sElt (W.stepE k))⁻¹ • d.elift (W.stepE k)).reverse).reverse = _
          rw [GraphAction.smul_reverse_apply, Quiver.Total.reverse_reverse, ← mul_smul, hpre]
        have h' : (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) • d.elift (W.stepE k) =
            W.pre (k + 1) • d.elift (W.stepE k) := by
          rw [← h1, ← h2]
          exact hback
        have hmem0 := mem_stabilizer_of_smul_eq h'
        have hsimp : (W.pre (k + 1))⁻¹ * (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) =
            ((W.letter (k + 1)).2 : G) := by group
        rw [hsimp] at hmem0
        exact hmem0
      have hu : ((W.letter k).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) = d.vgroup ((W.letter k).1) from by
          rw [← alpha, ← W.letter_orbit k hk0]]
        exact (W.letter k).2.2
      have hv : ((W.letter (k + 1)).2 : G) ∈
          d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) =
            d.vgroup ((W.letter (k + 1)).1) from by
          rw [← beta, ← W.letter_orbit (k + 1) hk1]]
        exact (W.letter (k + 1)).2.2
      have hw : ((W.letter (k + 2)).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) =
            d.vgroup ((W.letter (k + 2)).1) from by
          rw [← alpha, ← horb2, ← W.letter_orbit (k + 2) hk2]]
        exact (W.letter (k + 2)).2.2
      let c : ↥(d.eGroup (W.stepE k)) := ⟨((W.letter (k + 1)).2 : G), hmem⟩
      have hc_eq : (d.eGroupToSrc (W.stepE k) c : G) = ((W.letter (k + 1)).2 : G) := by
        rw [d.eGroupToSrc_apply]
      have hγu : TreeDatum.Letter.gam (W.letter k) D =
          d.gEltHom D (Work.ORBassSerre.Action.tgtE (W.stepE k)) ⟨((W.letter k).2 : G), hu⟩ :=
        gEltHom_congr D ((W.letter_orbit k hk0).trans alpha) rfl
      have hγv : TreeDatum.Letter.gam (W.letter (k + 1)) D =
          d.gEltHom D (Work.ORBassSerre.Action.srcE (W.stepE k)) ⟨((W.letter (k + 1)).2 : G), hv⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 1) hk1).trans beta) rfl
      have hγw : TreeDatum.Letter.gam (W.letter (k + 2)) D =
          d.gEltHom D (Work.ORBassSerre.Action.tgtE (W.stepE k)) ⟨((W.letter (k + 2)).2 : G), hw⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 2) hk2).trans (horb2.trans alpha)) rfl
      have hσ : TreeDatum.stepGam D (W.stepE k) (W.stepB k) = TreeDatum.stepGam D (W.stepE k) false := by rw [hbF]
      have hσ' : TreeDatum.stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) =
          TreeDatum.stepGam D (W.stepE k) true := by rw [hb', hE']
      have hkey := merge_case3 D (W.stepE k) ((W.letter k).2 : G) ((W.letter (k + 1)).2 : G)
        ((W.letter (k + 2)).2 : G) hu hv hw c hc_eq
      have hy : ((W.letter k).2 : G) * (d.eGroupToTgt (W.stepE k) c : G) *
          ((W.letter (k + 2)).2 : G) ∈ d.vgroup (W.orb k) := by
        rw [alpha]
        exact mul_mem (mul_mem hu (d.eGroupToTgt (W.stepE k) c).2) hw
      refine ⟨⟨W.orb k, ⟨((W.letter k).2 : G) * (d.eGroupToTgt (W.stepE k) c : G) *
        ((W.letter (k + 2)).2 : G), hy⟩⟩, rfl, ?_⟩
      rw [hγu, hγv, hγw, hσ, hσ']
      exact hkey.trans (gEltHom_congr D alpha.symm rfl)
    · -- CASE 4
      have hbF' : W.stepB (k + 1) = false := stepB_eq_false hb'
      have hE' : W.stepE (k + 1) = Work.ORBassSerre.orbitEReverse (W.stepE k) := by
        have h2 := orbit_backtrack W hback
        rw [orbit_F_false W (k + 1) hbF', orbit_F_false W k hbF] at h2
        have h3 := congrArg Work.ORBassSerre.orbitEReverse h2
        rw [Work.ORBassSerre.orbitEReverse_involutive (W.stepE (k + 1)),
          Work.ORBassSerre.orbitEReverse_involutive
            (Work.ORBassSerre.orbitEReverse (W.stepE k))] at h3
        exact h3
      have alpha : W.orb k = Work.ORBassSerre.Action.tgtE (W.stepE k) := by
        rw [← W.step_src k hk', hbF]
        rfl
      have beta : W.orb (k + 1) = Work.ORBassSerre.Action.srcE (W.stepE k) := by
        rw [← W.step_tgt k hk', hbF]
        rfl
      have hpre : W.pre (k + 1) = W.pre k * ((W.letter k).2 : G) * (d.sElt (W.stepE k))⁻¹ := by
        rw [W.pre_succ, hbF, d.moveElt_false]
      have hmem : ((W.letter (k + 1)).2 : G) *
          (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ * d.linkG (W.stepE k) ∈
          d.eGroup (W.stepE k) := by
        have h1 : W.F (k + 1) = ((W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
            (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹) •
            d.elift (Work.ORBassSerre.orbitEReverse (W.stepE k))).reverse := by
          show (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) •
            d.move (W.stepE (k + 1)) (W.stepB (k + 1)) = _
          rw [hbF', hE']
          show (W.pre (k + 1) * ((W.letter (k + 1)).2 : G)) •
            ((d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ •
              d.elift (Work.ORBassSerre.orbitEReverse (W.stepE k))).reverse = _
          rw [GraphAction.smul_reverse_apply, ← mul_smul]
        have h2 : (W.F k).reverse = W.pre (k + 1) • d.elift (W.stepE k) := by
          show ((W.pre k * ((W.letter k).2 : G)) • d.move (W.stepE k) (W.stepB k)).reverse = _
          rw [hbF]
          show ((W.pre k * ((W.letter k).2 : G)) •
            ((d.sElt (W.stepE k))⁻¹ • d.elift (W.stepE k)).reverse).reverse = _
          rw [GraphAction.smul_reverse_apply, Quiver.Total.reverse_reverse, ← mul_smul, hpre]
        have hrw : (d.elift (Work.ORBassSerre.orbitEReverse (W.stepE k))).reverse =
            d.linkG (W.stepE k) • d.elift (W.stepE k) := by
          rw [← d.linkG_smul, ← GraphAction.smul_reverse_apply, Quiver.Total.reverse_reverse]
        have hh : (W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
            (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹) •
            (d.elift (Work.ORBassSerre.orbitEReverse (W.stepE k))).reverse =
            W.pre (k + 1) • d.elift (W.stepE k) := by
          have h0 : ((W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
              (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹) •
              d.elift (Work.ORBassSerre.orbitEReverse (W.stepE k))).reverse =
              W.pre (k + 1) • d.elift (W.stepE k) := by
            rw [← h1, ← h2]
            exact hback
          rwa [← GraphAction.smul_reverse_apply] at h0
        have hh2 : (W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
            (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹) •
            (d.elift (Work.ORBassSerre.orbitEReverse (W.stepE k))).reverse =
            (W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
              (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ * d.linkG (W.stepE k)) •
            d.elift (W.stepE k) := by
          rw [hrw, ← mul_smul]
        have h' : (W.pre (k + 1) * ((W.letter (k + 1)).2 : G) *
            (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ * d.linkG (W.stepE k)) •
            d.elift (W.stepE k) = W.pre (k + 1) • d.elift (W.stepE k) :=
          hh2.symm.trans hh
        have hmem0 := mem_stabilizer_of_smul_eq h'
        rw [hpre] at hmem0
        have hsimp : (W.pre k * ((W.letter k).2 : G) * (d.sElt (W.stepE k))⁻¹)⁻¹ *
            (W.pre k * ((W.letter k).2 : G) * (d.sElt (W.stepE k))⁻¹ *
              ((W.letter (k + 1)).2 : G) *
              (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ *
              d.linkG (W.stepE k)) =
            ((W.letter (k + 1)).2 : G) *
              (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ * d.linkG (W.stepE k) := by
          group
        rw [hsimp] at hmem0
        exact hmem0
      have hu : ((W.letter k).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) = d.vgroup ((W.letter k).1) from by
          rw [← alpha, ← W.letter_orbit k hk0]]
        exact (W.letter k).2.2
      have hv : ((W.letter (k + 1)).2 : G) ∈
          d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.srcE (W.stepE k)) =
            d.vgroup ((W.letter (k + 1)).1) from by
          rw [← beta, ← W.letter_orbit (k + 1) hk1]]
        exact (W.letter (k + 1)).2.2
      have hw : ((W.letter (k + 2)).2 : G) ∈ d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) := by
        rw [show d.vgroup (Work.ORBassSerre.Action.tgtE (W.stepE k)) =
            d.vgroup ((W.letter (k + 2)).1) from by
          rw [← alpha, ← horb2, ← W.letter_orbit (k + 2) hk2]]
        exact (W.letter (k + 2)).2.2
      let c : ↥(d.eGroup (W.stepE k)) :=
        ⟨((W.letter (k + 1)).2 : G) *
          (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ * d.linkG (W.stepE k), hmem⟩
      have hc_eq : (d.eGroupToSrc (W.stepE k) c : G) =
          ((W.letter (k + 1)).2 : G) * (d.linkH (W.stepE k) : G)⁻¹ := by
        rw [d.eGroupToSrc_apply]
        change ((W.letter (k + 1)).2 : G) *
            (d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)))⁻¹ * d.linkG (W.stepE k) =
          ((W.letter (k + 1)).2 : G) * (d.linkH (W.stepE k) : G)⁻¹
        rw [show (d.linkH (W.stepE k) : G) = (d.linkG (W.stepE k))⁻¹ *
            d.sElt (Work.ORBassSerre.orbitEReverse (W.stepE k)) from rfl]
        group
      have hγu : TreeDatum.Letter.gam (W.letter k) D =
          d.gEltHom D (Work.ORBassSerre.Action.tgtE (W.stepE k)) ⟨((W.letter k).2 : G), hu⟩ :=
        gEltHom_congr D ((W.letter_orbit k hk0).trans alpha) rfl
      have hγv : TreeDatum.Letter.gam (W.letter (k + 1)) D =
          d.gEltHom D (Work.ORBassSerre.Action.srcE (W.stepE k)) ⟨((W.letter (k + 1)).2 : G), hv⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 1) hk1).trans beta) rfl
      have hγw : TreeDatum.Letter.gam (W.letter (k + 2)) D =
          d.gEltHom D (Work.ORBassSerre.Action.tgtE (W.stepE k)) ⟨((W.letter (k + 2)).2 : G), hw⟩ :=
        gEltHom_congr D ((W.letter_orbit (k + 2) hk2).trans (horb2.trans alpha)) rfl
      have hσ : TreeDatum.stepGam D (W.stepE k) (W.stepB k) = TreeDatum.stepGam D (W.stepE k) false := by rw [hbF]
      have hσ' : TreeDatum.stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) =
          TreeDatum.stepGam D (Work.ORBassSerre.orbitEReverse (W.stepE k)) false := by rw [hbF', hE']
      have hkey := merge_case4 D (W.stepE k) ((W.letter k).2 : G) ((W.letter (k + 1)).2 : G)
        ((W.letter (k + 2)).2 : G) hu hv hw c hc_eq
      have hy : ((W.letter k).2 : G) * (d.eGroupToTgt (W.stepE k) c : G) *
          (d.linkK (W.stepE k) : G)⁻¹ * ((W.letter (k + 2)).2 : G) ∈ d.vgroup (W.orb k) := by
        rw [alpha]
        refine mul_mem (mul_mem (mul_mem hu (d.eGroupToTgt (W.stepE k) c).2) ?_) hw
        refine inv_mem ?_
        rw [← congrArg d.vgroup (srcE_orbitEReverse (G := G) (V := V) (W.stepE k))]
        exact (d.linkK (W.stepE k)).2
      refine ⟨⟨W.orb k, ⟨((W.letter k).2 : G) * (d.eGroupToTgt (W.stepE k) c : G) *
        (d.linkK (W.stepE k) : G)⁻¹ * ((W.letter (k + 2)).2 : G), hy⟩⟩, rfl, ?_⟩
      rw [hγu, hγv, hγw, hσ, hσ']
      exact hkey.trans (gEltHom_congr D alpha.symm rfl)

end Work.ORLocInd.FKSKernel.Kurosh
