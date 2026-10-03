import Mathlib
import Submission.Work.ORLocInd.FKSKernel.Kurosh.BSWalk
import Submission.Work.ORLocInd.FKSKernel.Kurosh.edgeRel_general
import Submission.Work.ORLocInd.FKSKernel.Kurosh.exists_inv
import Submission.Work.ORLocInd.FKSKernel.Kurosh.middle_merge

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ORLocInd.FKSKernel.Kurosh

open Work.ORBassSerre
open Work.ORBassSerre.Action

open Quiver

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-! ## Translating an arrow or a vertex does not change its orbit -/

theorem mk_smul_orbitE (g : G) (u : Quiver.Total V) :
    (Quotient.mk'' (g • u) : Work.ORBassSerre.orbitE G V) = Quotient.mk'' u :=
  Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)

theorem mk_smul_orbitV (g : G) (x : V) :
    (Quotient.mk'' (g • x) : Work.ORBassSerre.orbitV G V) = Quotient.mk'' x :=
  Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)

namespace TreeDatum

variable {d : TreeDatum G V}


/-- The orbit of the `k`-th vertex of the walk is `W.orb k`. -/
theorem PathWord.z_mk (W : PathWord d) (k : ℕ) :
    (Quotient.mk'' (W.z k) : Work.ORBassSerre.orbitV G V) = W.orb k := by
  rw [PathWord.z, mk_smul_orbitV, d.vert_mk]

/-- A backtrack in the walk forces the vertex two steps later to coincide with the current
vertex, hence the same vertex orbit. -/
theorem PathWord.orb_add_two_eq (W : PathWord d) {k : ℕ} (hk : k + 1 < W.len)
    (hback : W.F (k + 1) = (W.F k).reverse) : W.orb (k + 2) = W.orb k := by
  have hz : W.z (k + 2) = W.z k := by
    have h1 : W.z (k + 2) = (W.F (k + 1)).right := (W.F_right (k + 1) hk).symm
    rw [h1, hback, Quiver.Total.reverse_right, W.F_left k (by omega)]
  have h := congrArg (fun x => (Quotient.mk'' x : Work.ORBassSerre.orbitV G V)) hz
  rwa [PathWord.z_mk, PathWord.z_mk] at h

/-- **The shortening step, given the merged middle letter.**  If the Γ-product of the middle
segment `u_k σ_k u_{k+1} σ_{k+1} u_{k+2}` collapses to a single letter `l` at `W.orb k`, then the
path word can be shortened by two steps without changing its element or its endpoints. -/
theorem exists_shorten_of_merge (D : d.PresData) (W : PathWord d) {k : ℕ} (hk : k + 1 < W.len)
    (hback : W.F (k + 1) = (W.F k).reverse)
    (l : Letter d) (hl : l.1 = W.orb k)
    (hgam : Letter.gam (W.letter k) D * stepGam D (W.stepE k) (W.stepB k) *
        Letter.gam (W.letter (k + 1)) D * stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) *
        Letter.gam (W.letter (k + 2)) D = Letter.gam l D) :
    ∃ W' : PathWord d, W'.len + 2 = W.len ∧ W'.elt D = W.elt D ∧
      W'.orb 0 = W.orb 0 ∧ W'.orb W'.len = W.orb W.len := by
  have horb : W.orb (k + 2) = W.orb k := W.orb_add_two_eq hk hback
  let len' : ℕ := W.len - 2
  let orb' : ℕ → Work.ORBassSerre.orbitV G V :=
    fun j => if j ≤ k then W.orb j else W.orb (j + 2)
  let E' : ℕ → Work.ORBassSerre.orbitE G V :=
    fun j => if j < k then W.stepE j else W.stepE (j + 2)
  let B' : ℕ → Bool := fun j => if j < k then W.stepB j else W.stepB (j + 2)
  let lm : ℕ → Letter d :=
    fun j => if j < k then W.letter j else if j = k then l else W.letter (j + 2)
  have horb_le : ∀ j, j ≤ k → orb' j = W.orb j := by
    intro j hj; dsimp only [orb']; rw [if_pos hj]
  have horb_gt : ∀ j, k < j → orb' j = W.orb (j + 2) := by
    intro j hj; dsimp only [orb']; rw [if_neg (not_le.mpr hj)]
  have hlm_lt : ∀ j, j < k → lm j = W.letter j := by
    intro j hj; dsimp only [lm]; rw [if_pos hj]
  have hlm_gt : ∀ j, k < j → lm j = W.letter (j + 2) := by
    intro j hj; dsimp only [lm]
    rw [if_neg (not_lt.mpr (le_of_lt hj)), if_neg (ne_of_gt hj)]
  have hlm_k : lm k = l := by
    dsimp only [lm]; rw [if_neg (lt_irrefl k), if_pos rfl]
  have hE_lt : ∀ j, j < k → E' j = W.stepE j := by
    intro j hj; dsimp only [E']; rw [if_pos hj]
  have hE_gt : ∀ j, k < j → E' j = W.stepE (j + 2) := by
    intro j hj; dsimp only [E']; rw [if_neg (not_lt.mpr (le_of_lt hj))]
  have hE_k : E' k = W.stepE (k + 2) := by
    dsimp only [E']; rw [if_neg (lt_irrefl k)]
  have hB_lt : ∀ j, j < k → B' j = W.stepB j := by
    intro j hj; dsimp only [B']; rw [if_pos hj]
  have hB_gt : ∀ j, k < j → B' j = W.stepB (j + 2) := by
    intro j hj; dsimp only [B']; rw [if_neg (not_lt.mpr (le_of_lt hj))]
  have hB_k : B' k = W.stepB (k + 2) := by
    dsimp only [B']; rw [if_neg (lt_irrefl k)]
  let W' : PathWord d :=
    { len := len'
      orb := orb'
      letter := lm
      letter_orbit := by
        intro j hj
        have hj' : j ≤ W.len - 2 := hj
        by_cases hjk : j < k
        · rw [hlm_lt j hjk, horb_le j (le_of_lt hjk), W.letter_orbit j (by omega)]
        · by_cases hjeq : j = k
          · rw [hjeq, hlm_k, hl, horb_le k le_rfl]
          · have hgt : k < j := lt_of_le_of_ne (le_of_not_gt hjk) (Ne.symm hjeq)
            rw [hlm_gt j hgt, horb_gt j hgt, W.letter_orbit (j + 2) (by omega)]
      stepE := E'
      stepB := B'
      step_src := by
        intro j hj
        have hj' : j < W.len - 2 := hj
        have hj2 : j + 2 < W.len := by omega
        by_cases hjk : j < k
        · rw [hE_lt j hjk, hB_lt j hjk, horb_le j (le_of_lt hjk), W.step_src j (by omega)]
        · by_cases hjeq : j = k
          · rw [hjeq, hE_k, hB_k, horb_le k le_rfl, W.step_src (k + 2) (by omega), horb]
          · have hgt : k < j := lt_of_le_of_ne (le_of_not_gt hjk) (Ne.symm hjeq)
            rw [hE_gt j hgt, hB_gt j hgt, horb_gt j hgt, W.step_src (j + 2) hj2]
      step_tgt := by
        intro j hj
        have hj' : j < W.len - 2 := hj
        have hj2 : j + 2 < W.len := by omega
        have hjl : j < W.len := by omega
        by_cases hjk : j < k
        · rw [hE_lt j hjk, hB_lt j hjk, W.step_tgt j hjl, horb_le (j + 1) (by omega)]
        · by_cases hjeq : j = k
          · rw [hjeq, hE_k, hB_k, W.step_tgt (k + 2) (by omega), horb_gt (k + 1) (by omega)]
          · have hgt : k < j := lt_of_le_of_ne (le_of_not_gt hjk) (Ne.symm hjeq)
            rw [hE_gt j hgt, hB_gt j hgt, W.step_tgt (j + 2) hj2, horb_gt (j + 1) (by omega)] }
  have hW'len : W'.len = W.len - 2 := rfl
  have hW'orb : W'.orb = orb' := rfl
  have hW'letter : W'.letter = lm := rfl
  have hW'stepE : W'.stepE = E' := rfl
  have hW'stepB : W'.stepB = B' := rfl
  have tpre_le : ∀ m, m ≤ k → W'.tpre D m = W.tpre D m := by
    intro m
    induction m with
    | zero => intro _; rw [PathWord.tpre_zero, PathWord.tpre_zero]
    | succ n ih =>
        intro hn
        have hnk : n < k := by omega
        have ih' : W'.tpre D n = W.tpre D n := ih (by omega)
        have hletter : W'.letter n = W.letter n := by rw [hW'letter, hlm_lt n hnk]
        have hstepE : W'.stepE n = W.stepE n := by rw [hW'stepE, hE_lt n hnk]
        have hstepB : W'.stepB n = W.stepB n := by rw [hW'stepB, hB_lt n hnk]
        rw [show W'.tpre D (n + 1) = W'.tpre D n * Letter.gam (W'.letter n) D *
            stepGam D (W'.stepE n) (W'.stepB n) from PathWord.tpre_succ W' D n,
          ih', hletter, hstepE, hstepB,
          show W.tpre D (n + 1) = W.tpre D n * Letter.gam (W.letter n) D *
            stepGam D (W.stepE n) (W.stepB n) from PathWord.tpre_succ W D n]
  have hkey : W.tpre D (k + 2) * Letter.gam (W.letter (k + 2)) D =
      W.tpre D k * Letter.gam l D := by
    have hmid : W.tpre D (k + 2) * Letter.gam (W.letter (k + 2)) D =
        W.tpre D k * (Letter.gam (W.letter k) D * stepGam D (W.stepE k) (W.stepB k) *
          Letter.gam (W.letter (k + 1)) D * stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) *
          Letter.gam (W.letter (k + 2)) D) := by
      rw [show W.tpre D (k + 2) = W.tpre D (k + 1) * Letter.gam (W.letter (k + 1)) D *
            stepGam D (W.stepE (k + 1)) (W.stepB (k + 1)) from PathWord.tpre_succ W D (k + 1),
          show W.tpre D (k + 1) = W.tpre D k * Letter.gam (W.letter k) D *
            stepGam D (W.stepE k) (W.stepB k) from PathWord.tpre_succ W D k]
      group
    rw [hmid, hgam]
  have tpre_ge : ∀ m, k + 1 ≤ m → W'.tpre D m = W.tpre D (m + 2) := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ n ih =>
        intro hn
        by_cases hnk : n = k
        · rw [hnk]
          show W'.tpre D (k + 1) = W.tpre D (k + 3)
          have h1 : W'.tpre D (k + 1) = W.tpre D k * Letter.gam l D *
              stepGam D (W.stepE (k + 2)) (W.stepB (k + 2)) := by
            rw [show W'.tpre D (k + 1) = W'.tpre D k * Letter.gam (W'.letter k) D *
                stepGam D (W'.stepE k) (W'.stepB k) from PathWord.tpre_succ W' D k,
              tpre_le k le_rfl, hW'letter, hW'stepE, hW'stepB, hlm_k, hE_k, hB_k]
          have h2 : W.tpre D (k + 3) = W.tpre D k * Letter.gam l D *
              stepGam D (W.stepE (k + 2)) (W.stepB (k + 2)) := by
            rw [show W.tpre D (k + 3) = W.tpre D (k + 2) * Letter.gam (W.letter (k + 2)) D *
                stepGam D (W.stepE (k + 2)) (W.stepB (k + 2)) from PathWord.tpre_succ W D (k + 2),
              hkey]
          rw [h1, h2]
        · have hgt : k < n := by omega
          have hn1 : k + 1 ≤ n := by omega
          have h1 : W'.tpre D (n + 1) = W.tpre D (n + 2) * Letter.gam (W.letter (n + 2)) D *
              stepGam D (W.stepE (n + 2)) (W.stepB (n + 2)) := by
            rw [show W'.tpre D (n + 1) = W'.tpre D n * Letter.gam (W'.letter n) D *
                stepGam D (W'.stepE n) (W'.stepB n) from PathWord.tpre_succ W' D n,
              ih hn1, hW'letter, hW'stepE, hW'stepB, hlm_gt n hgt, hE_gt n hgt, hB_gt n hgt]
          rw [h1]
          show W.tpre D (n + 2) * Letter.gam (W.letter (n + 2)) D *
              stepGam D (W.stepE (n + 2)) (W.stepB (n + 2)) = W.tpre D (n + 3)
          rw [show W.tpre D (n + 3) = W.tpre D (n + 2) * Letter.gam (W.letter (n + 2)) D *
              stepGam D (W.stepE (n + 2)) (W.stepB (n + 2)) from PathWord.tpre_succ W D (n + 2)]
  have helt : W'.elt D = W.elt D := by
    rcases eq_or_lt_of_le (show k + 2 ≤ W.len by omega) with hlen | hlen
    · have hlen' : W'.len = k := by rw [hW'len, ← hlen]; omega
      have hL : W'.elt D = W.tpre D k * Letter.gam l D := by
        show W'.tpre D W'.len * Letter.gam (W'.letter W'.len) D = W.tpre D k * Letter.gam l D
        rw [hlen', tpre_le k le_rfl, hW'letter, hlm_k]
      have hR : W.elt D = W.tpre D k * Letter.gam l D := by
        show W.tpre D W.len * Letter.gam (W.letter W.len) D = W.tpre D k * Letter.gam l D
        rw [← hlen, hkey]
      rw [hL, hR]
    · have hk' : k < W.len - 2 := by omega
      have hge : k + 1 ≤ W.len - 2 := by omega
      have hsub : W.len - 2 + 2 = W.len := by omega
      have hL : W'.elt D = W.tpre D W.len * Letter.gam (W.letter W.len) D := by
        show W'.tpre D W'.len * Letter.gam (W'.letter W'.len) D = W.tpre D W.len *
          Letter.gam (W.letter W.len) D
        rw [hW'len, tpre_ge (W.len - 2) hge, hW'letter, hlm_gt (W.len - 2) hk', hsub]
      have hE : W.elt D = W.tpre D W.len * Letter.gam (W.letter W.len) D := rfl
      rw [hL, hE]
  refine ⟨W', ?_, helt, ?_, ?_⟩
  · rw [hW'len]; omega
  · rw [hW'orb, horb_le 0 (Nat.zero_le k)]
  · rcases eq_or_lt_of_le (show k + 2 ≤ W.len by omega) with hlen | hlen
    · have hlen' : W'.len = k := by rw [hW'len, ← hlen]; omega
      rw [hW'orb, hlen', horb_le k le_rfl, ← hlen, horb]
    · have hk' : k < W.len - 2 := by omega
      have hsub : W.len - 2 + 2 = W.len := by omega
      rw [hW'orb, hW'len, horb_gt (W.len - 2) hk', hsub]

end TreeDatum

/-- **The shortening step of the walk proof.**  If two consecutive arrows of the walk of a path
word are mutually inverse, the path word can be replaced by a path word with two fewer steps (so
that iterating produces a *reduced* path word with the same `elt` and the same endpoints).

NOTE FOR THE PROVER: the statement does **not** need `IsTree V` or `ActsWithoutInversions`; the
four cases of the argument are written out in the file
`Submission/Work/ORBassSerre/Action/Structure/shortening_notes.lean`. -/
theorem exists_shorten_of_backtrack {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum G V}
    
    (D : d.PresData) (W : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.PathWord d) {k : ℕ}
    (hk : k + 1 < W.len) (hback : W.F (k + 1) = (W.F k).reverse) :
    ∃ W' : Work.ORLocInd.FKSKernel.Kurosh.TreeDatum.PathWord d,
      W'.len + 2 = W.len ∧ W'.elt D = W.elt D ∧
        W'.orb 0 = W.orb 0 ∧ W'.orb W'.len = W.orb W.len := by
  obtain ⟨l, hl, hgam⟩ := middle_merge D W hk hback
  exact TreeDatum.exists_shorten_of_merge D W hk hback l hl hgam

end Work.ORLocInd.FKSKernel.Kurosh
