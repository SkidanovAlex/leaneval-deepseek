import Submission.ZagierHoffmanProof.StepL75
import Submission.ZagierHoffmanProof.StepL54
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L101: G5T (q,q) — the ORDERED level-2 CASE-2 j=0 leaf (SESSION 252)

★ g5T_qq : AdmExpT F (q+q) 2 (pair qExp qExp) — the depth-2 all-q in-domain
tuple expands at level 2 into its BC-iterate b-members (D := g5D := BCqIter F 1
(toData r1Rel)): weights 2q (g5D_member_weight), 2-adm (g5D_member_twoAdm), the
ζ-identity hid (g5qq_zeta + eq_neg + Finset.sum_neg_distrib + neg_coe_mul_zeta),
and the ORDERS ℓ ≥ 2 AUTOMATIC (depth-2 (q,q) saturates: psum(pair q q) ℓ =
weight = q+q by psum_ge_depth, member psum ≤ weight via psum_le_weight).
★ g5T_case2 (w s hw hr2 hp1 hq0) : AdmExpT F w 2 s — the in-domain (q,q)
wrapper (s = pair q q via tuple_two_eq_of_pad0 + weight transport), mirroring the
weak g5_case2_step with AdmExpT.
These supply main2T_of_g5T's CASE-2 (q,q) leaf.  REMAINING for g5T_total: G5T_case1
(the ORDERED CASE-1 j=0 splice ((q, s₂>q, …)) — port StepL80's weak
g5_case1_step/g5_case1_step-orders: same D := BCqIter F 1 (toData R0) chain, per-member
e with admExpT_self/rec, plus the a/b-member ORDER lemmas (ℓ ≥ 2:
psum(D.cA a)ℓ ≤ psum s ℓ and psum(D.cB p)ℓ ≤ psum s ℓ over the
level-2 j=0 chain), then g5T_total := l2_induction + g5T_case1 + g5T_case2, and
main2T := main2T_of_g5T g5T_total closes A(1,2,3)@w via StepL97.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ G5T (q,q): the ORDERED (AdmExpT) level-2 expansion of the depth-2 all-q
tuple into its BC-iterate b-members (2-adm, weight 2q; orders ℓ ≥ 2 automatic:
depth-2 (q,q) saturates at ℓ ≥ 2). -/
theorem g5T_qq :
    AdmExpT F ((qExp F : ℕ) + (qExp F : ℕ)) 2 (pair (qExp F) (qExp F)) := by
  classical
  let D := g5D F
  refine ⟨D.ιB, inferInstance, D.depB, D.hdepB, D.cB, (fun p => -(D.aB p)), ?_, ?_, ?_, ?_⟩
  · intro p
    change weight (D.depB p) (D.cB p) = (qExp F : ℕ) + (qExp F : ℕ)
    dsimp [D]
    exact g5D_member_weight F p
  · intro p
    change kAdmissible (Nat.card F) (D.cB p) 2
    dsimp [D]
    exact g5D_member_twoAdm F p
  · intro p ℓ hℓ
    have hwl := psum_le_weight (D.cB p) ℓ
    have hw : weight (D.depB p) (D.cB p) = (qExp F : ℕ) + (qExp F : ℕ) := by
      dsimp [D]
      exact g5D_member_weight F p
    have hpd := psum_ge_depth (pair (qExp F) (qExp F)) hℓ
    have hpeq : psum (pair (qExp F) (qExp F)) ℓ = (qExp F : ℕ) + (qExp F : ℕ) := by
      rw [weight_pair] at hpd
      change psum (pair (qExp F) (qExp F)) ℓ = (qExp F : ℕ) + (qExp F : ℕ) at hpd
      exact hpd
    rw [hw] at hwl
    rw [← hpeq] at hwl
    exact hwl
  · have hz : ζ_A F (pair (qExp F) (qExp F)) +
        (∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (D.cB p))) = 0 := by
      dsimp [D]
      exact g5qq_zeta F
    calc
      ζ_A F (pair (qExp F) (qExp F)) =
          -(∑ p : D.ιB, (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (D.cB p))) := eq_neg_of_add_eq_zero_left hz
      _ = ∑ p : D.ιB, -(((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (D.cB p)) := by
            rw [← Finset.sum_neg_distrib]
      _ = ∑ p : D.ιB, (((-(D.aB p : RatFunc F) : RatFunc F) : RatFunc.CompletionAtInfty F) *
            ζ_A F (D.cB p)) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact (neg_coe_mul_zeta F (D.aB p) (D.cB p)).symm

/-- G5T CASE-2 step: the in-domain head-q depth-2 tuple (q,q) (r = 2, pad0 s 1 = q)
expands at level 2 in ORDERED form via g5T_qq. -/
theorem g5T_case2 (w : ℕ) {r : ℕ} (s : Fin r → ℕ+) (hw : weight r s = w)
    (hr2 : r = 2) (hp1 : pad0 s 1 = Nat.card F) (hq0 : pad0 s 0 = Nat.card F) :
    AdmExpT F w 2 s := by
  classical
  subst r
  have hp0' : pad0 s 0 = (qExp F : ℕ) := by
    change pad0 s 0 = Nat.card F
    exact hq0
  have hp1' : pad0 s 1 = (qExp F : ℕ) := by
    change pad0 s 1 = Nat.card F
    exact hp1
  have hseq : s = pair (qExp F) (qExp F) := tuple_two_eq_of_pad0 s (qExp F) (qExp F) hp0' hp1'
  have hw2 : weight 2 s = (qExp F : ℕ) + (qExp F : ℕ) := by
    rw [hseq]
    exact weight_pair (qExp F) (qExp F)
  have hweq : w = (qExp F : ℕ) + (qExp F : ℕ) := by
    rw [← hw2]
    exact hw.symm
  have hA : AdmExpT F w 2 (pair (qExp F) (qExp F)) := by
    simpa [hweq] using g5T_qq F
  rw [hseq]
  exact hA

end ZagierHoffmanPositiveChar
