import Submission.ZagierHoffmanProof.StepL93
import Submission.ZagierHoffmanProof.StepL92
import Submission.ZagierHoffmanProof.StepL82
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L94: g53_case2_qqq — the (q,q,q) CASE-2 j=0 leaf at level 3 (SESSION 249)

★ g53_case2_qqq (w s hw) (h0q : s₀ = q) (h1q : s₁ = q) (h2q : s₂ = q)
(rec : Main3Step → 2-adm → ¬3-adm → AdmExpT F w 3) : AdmExpT F w 3 s
— the depth-3 all-q in-domain tuple (2-adm ∧ ¬3-adm, weight 3q) expands at
level 3 into its iterate-2 b-members (D := BCqIter F 2 (toData r1Rel), a-side =
(q,q,q) coeff 1, members = D.cB).

STRUCTURE (StepL75's g5qq script at n = 2): g53qqq_aSide collapses the PUnit a-side
of BinaryRel.zeta (of the toBinaryRel-iterate-2) to ζ(consVec q (pair q q));
g53qqq_zeta := BCqIter_zeta_zero F 2 + the aSide collapse gives ζ(s) + Σ_b
(aB p)·ζ(cB p) = 0; the single-family fold (mdep/mc/ma over D.ιB, hid via
eq_neg + Finset.sum_neg_distrib + neg_coe_mul_zeta); per-member e: weight = 3q
(g53D_member_weight), 2-adm (g53D_member_twoAdm), 3-adm → admExpT_self /
¬3-adm → Main3Step by the STRICT prefix-3 drop (g53D_member_psum3_lt —
NO InitLt) → rec; horder trivial (depth-3 s saturates); splice by
admExpT_combine.  s is carried as a Fin-3 value-tuple (h0q/h1q/h2q) so main3's
CASE-2 b=q∧a=q branch calls it directly with rec := main3's own l3-induction IH.
NEXT: wire main3's CASE-2 b=q branch (a=q → this; a<q → main3_case2_j1) and
commit main3.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- collapse of the PUnit a-side sum of the (q,q,q) chain (explicit iterate-2 form,
matching BCqIter_zeta_zero's unfolded statement). -/
lemma g53qqq_aSide :
    (∑ i : (RelData.toBinaryRel F (RelData.BCqIter F 2 (toData F (r1Rel F)))
        (BCqIter_valid F 2 (r1Rel F))).ιA,
      ((((RelData.toBinaryRel F (RelData.BCqIter F 2 (toData F (r1Rel F)))
        (BCqIter_valid F 2 (r1Rel F))).aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F ((RelData.toBinaryRel F (RelData.BCqIter F 2 (toData F (r1Rel F)))
        (BCqIter_valid F 2 (r1Rel F))).cA i))) =
    ζ_A F (consVec (qExp F) (pair (qExp F) (qExp F))) := by
  classical
  change (∑ i : PUnit,
      ((((RelData.BCqIter F 2 (toData F (r1Rel F))).aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F ((RelData.BCqIter F 2 (toData F (r1Rel F))).cA i))) =
    ζ_A F (consVec (qExp F) (pair (qExp F) (qExp F)))
  have h1 : (∑ i : PUnit,
      ((((RelData.BCqIter F 2 (toData F (r1Rel F))).aA i : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F ((RelData.BCqIter F 2 (toData F (r1Rel F))).cA i))) =
      ((((RelData.BCqIter F 2 (toData F (r1Rel F))).aA PUnit.unit : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F ((RelData.BCqIter F 2 (toData F (r1Rel F))).cA PUnit.unit)) := by
    rw [show (Finset.univ : Finset PUnit) = {PUnit.unit} by ext i; simp]
    rw [Finset.sum_singleton]
  rw [h1]
  have hc : (((RelData.BCqIter F 2 (toData F (r1Rel F))).aA PUnit.unit : RatFunc F) : RatFunc.CompletionAtInfty F) = 1 := by
    change ((1 : RatFunc F) : RatFunc.CompletionAtInfty F) = 1
    simp [completion_coe_one]
  have ht : ζ_A F ((RelData.BCqIter F 2 (toData F (r1Rel F))).cA PUnit.unit) =
      ζ_A F (consVec (qExp F) (pair (qExp F) (qExp F))) := by
    congr 1
    change consVec (qExp F) (consVec (qExp F) (single (qExp F))) =
      consVec (qExp F) (pair (qExp F) (qExp F))
    rw [consVec_single_q_eq_pair]
  rw [hc, ht]
  simp

/-- ζ-identity of the (q,q,q) chain: ζ(consVec q (pair q q)) + Σ_b (aB p)·ζ(cB p) = 0. -/
theorem g53qqq_zeta :
    ζ_A F (consVec (qExp F) (pair (qExp F) (qExp F))) +
      (∑ p : (RelData.BCqIter F 2 (toData F (r1Rel F))).ιB,
        ((((RelData.BCqIter F 2 (toData F (r1Rel F))).aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F ((RelData.BCqIter F 2 (toData F (r1Rel F))).cB p))) = 0 := by
  classical
  have hz0 := BCqIter_zeta_zero F 2 (r1Rel F)
  unfold BinaryRel.zeta at hz0
  rw [g53qqq_aSide F] at hz0
  exact hz0

/-- ★ the (q,q,q) CASE-2 j=0 leaf: the depth-3 all-q tuple (weight 3q) expands at
level 3 into its iterate-2 members (2-adm, weight-3q, strict prefix-3 drop; per-member
3-adm → self / ¬3-adm → rec). -/
theorem g53_case2_qqq (w : ℕ) (s : Fin 3 → ℕ+) (hw : weight 3 s = w)
    (h0q : (s ⟨0, by omega⟩ : ℕ) = Nat.card F)
    (h1q : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (h2q : (s ⟨2, by omega⟩ : ℕ) = Nat.card F)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      Main3Step (Nat.card F) s m → kAdmissible (Nat.card F) m 2 →
      ¬ kAdmissible (Nat.card F) m 3 → AdmExpT F w 3 m) :
    AdmExpT F w 3 s := by
  classical
  let D : RelData F := g53D F
  let s0 : Fin 3 → ℕ+ := consVec (qExp F) (pair (qExp F) (qExp F))
  have hseq : s = s0 := by
    dsimp [s0]
    apply tuple3_eq_consVec_pair (a := qExp F) (b := qExp F) (c := qExp F)
    · exact h0q
    · exact h1q
    · rw [h2q]
      rw [show (qExp F : ℕ) = Nat.card F by rfl]
  have hw3 : weight 3 s = (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) := by
    rw [hseq]
    dsimp [s0]
    rw [weight_consVec]
    rw [weight_pair]
    change (qExp F : ℕ) + ((qExp F : ℕ) + (qExp F : ℕ)) =
      (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ)
    omega
  have hz : ζ_A F s +
      (∑ p : D.ιB, ((((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (D.cB p)))) = 0 := by
    have hz0 := g53qqq_zeta F
    -- hz0 : ζ(consVec q (pair q q)) + Σ over the explicit iterate = 0
    have h1 : ζ_A F s = ζ_A F (consVec (qExp F) (pair (qExp F) (qExp F))) := by
      rw [hseq]
    rw [← h1] at hz0
    -- sums over D (D := g53D := BCqIter F 2 (toData r1Rel)): defeq by g53D's def
    exact hz0
  -- single-family fold
  let ι : Type := D.ιB
  let mdep (p : ι) : ℕ := D.depB p
  let mhdep (p : ι) : 0 < mdep p := by
    dsimp [mdep]
    exact D.hdepB p
  let mc (p : ι) : Fin (mdep p) → ℕ+ := D.cB p
  let ma (p : ι) : RatFunc F := -(D.aB p)
  let x (p : ι) : RatFunc.CompletionAtInfty F :=
    (((D.aB p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (D.cB p))
  have hid3 : ζ_A F s = -(∑ p : ι, x p) := by
    have hz' : ζ_A F s + (∑ p : ι, x p) = 0 := by
      simpa [x] using hz
    exact eq_neg_of_add_eq_zero_left hz'
  have hid : ζ_A F s = ∑ p : ι, (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    rw [hid3]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp [x, ma, mc]
    exact (neg_coe_mul_zeta F (D.aB p) (D.cB p)).symm
  have hps3 : psum s 3 = (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) := by
    rw [hseq]
    dsimp [s0]
    rw [psum_ge_depth s0 (le_refl 3)]
    rw [weight_consVec]
    rw [weight_pair]
    change (qExp F : ℕ) + ((qExp F : ℕ) + (qExp F : ℕ)) =
      (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ)
    omega
  -- per-member
  have e : ∀ p : ι, AdmExpT F w 3 (mc p) := by
    intro p
    have hw1 : weight (D.depB p) (D.cB p) = weight 3 s := by
      have hmw := g53D_member_weight F p
      change weight (D.depB p) (D.cB p) = (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) at hmw
      rw [hmw]
      exact hw3.symm
    have h2m : kAdmissible (Nat.card F) (D.cB p) 2 := by
      change kAdmissible (Nat.card F) (D.cB p) 2
      exact g53D_member_twoAdm F p
    by_cases h3m : kAdmissible (Nat.card F) (D.cB p) 3
    · have hd : 0 < D.depB p := D.hdepB p
      have hw' : weight (D.depB p) (D.cB p) = w := by
        rw [hw1]; exact hw
      exact admExpT_self F w 3 hd (D.cB p) hw' h3m
    · have hstep : Main3Step (Nat.card F) s (D.cB p) := by
        have hps : psum (D.cB p) 3 < (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) := by
          exact g53D_member_psum3_lt F p
        have hps' : psum (D.cB p) 3 < psum s 3 := by
          rw [hps3]
          exact hps
        exact Or.inl hps'
      have hwm' : weight (D.depB p) (D.cB p) = w := by
        rw [hw1]; exact hw
      have hres := rec (D.depB p) (D.cB p) hwm' hstep h2m h3m
      exact hres
  -- member orders: trivial (depth-3 s saturates)
  have horder : ∀ p : ι, ∀ ℓ : ℕ, 3 ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    have hwl := psum_le_weight (mc p) ℓ
    have hwm : weight (mdep p) (mc p) = weight 3 s := by
      have hmw := g53D_member_weight F p
      change weight (D.depB p) (D.cB p) = (qExp F : ℕ) + (qExp F : ℕ) + (qExp F : ℕ) at hmw
      dsimp [mdep, mc]
      rw [hmw]
      exact hw3.symm
    have hpeq : weight 3 s = psum s ℓ := (psum_ge_depth s hℓ).symm
    rw [hwm, hpeq] at hwl
    exact hwl
  exact admExpT_combine F w 3 s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
