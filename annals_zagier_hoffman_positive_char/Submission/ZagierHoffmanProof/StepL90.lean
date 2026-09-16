import Submission.ZagierHoffmanProof.StepL53
import Submission.ZagierHoffmanProof.StepL49
import Submission.ZagierHoffmanProof.StepL1
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L90: case3_leaf_j2 — the level-3 CASE-2 j=2 leaf (SESSION 233, committed 248)

★ case3_leaf_j2 (a b : ℕ+) (ha : a ≤ q) (hb : b < q) :
    AdmExpT F (a+b+q) 3 (consVec a (pair b (qExp F)))
— the depth-3 (a, b, q) in-domain level-3 input (2-adm ∧ ¬3-adm via the
depth-3 form; CASE-2 / Prop-2.13 side at j = 2, i.e. b < q) expands at level 3
with exactly TWO 3-adm members, NO recursion:
    ζ(a,b,q) = −D1c·ζ(a, b, 1, q−1) − D1c·ζ(a, b+1, q−1)
(m2 := consVec a (consVec b (pair oneExp (qMinusExp F))) (depth 4), m3 :=
consVec a (pair ⟨b+1⟩ (qMinusExp F)) (depth 3)).  Mirrors case2_level2
(StepL53): the FixedOver chain over r1Rel at head b with front-prepend Q :=
FixedOver.prepend Bs a (the (k=3, j=2) Prop-2.13 chain), zeta_fixed_bridge,
bstar_type1/2/3_tuple + bstar_a_coeffs collapses, AdmExpT ∃-assembly
(weights = a+b+q, both members 3-adm, prefix-ℓ ≤ psum s ℓ automatic at
ℓ ≥ 3 by weight saturation).
For main3's CASE-2 wiring: b<q subcase calls this with s = consVec a (pair b q)
(a := s⟨0⟩, b := s⟨1⟩).  NEXT: the (a,q,q)@a<q j=1 dispatch
(StepL91's case2j1 member facts + the ζ-identity/e/horder/rec assembly) and
the (q,q,q) leaf.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## SESSION 233 — the level-3 CASE-2 leaf: depth-3 (a, b, q) with a ≤ q, b < q
expands at level 3 with TWO 3-adm members (no recursion).

Mirror of case2_level2 (StepL53, the level-2 depth-2-form leaf over r1Rel at head
b): the SAME FixedOver chain with the extra front-prepend `a` (the (k=3, j=2)
Prop-2.13 chain) gives
  ζ(a,b,q) = −D1c·ζ(a, b, 1, q−1) − D1c·ζ(a, b+1, q−1)
whose members m2 = consVec a (consVec b (pair 1 (q−1))) (depth 4) and
m3 = consVec a (pair (b+1) (q−1)) (depth 3) are 3-admissible (weight a+b+q) — a
LEAF for MAIN(3)'s CASE-2 side at j = 2.  -/

theorem case3_leaf_j2 (a b : ℕ+) (ha : (a : ℕ) ≤ Nat.card F) (hb : (b : ℕ) < Nat.card F) :
    AdmExpT F ((a : ℕ) + (b : ℕ) + Nat.card F) 3 (consVec a (pair b (qExp F))) := by
  classical
  let s : Fin 3 → ℕ+ := consVec a (pair b (qExp F))
  let D : RelData F := toData F (r1Rel F)
  let Bs : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) :=
    ofBstarOver F D b (fun e => BCqIter_valid F 0 (r1Rel F) e)
      (RelData.iterate_merge_hv F 0 (r1Rel F) b (by omega) (r1Rel_hbhd F))
  let Q : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) := FixedOver.prepend F Bs a
  let w : ℕ := (a : ℕ) + (b : ℕ) + Nat.card F
  let f : D.ιA ⊕ (D.ιB ⊕ D.ιB) → RatFunc.CompletionAtInfty F := fun p =>
    ((Q.a p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c p)
  have hzeta : (∑ p : D.ιA ⊕ (D.ιB ⊕ D.ιB), f p) = 0 := by
    have hz := zeta_fixed_bridge F Q.dep Q.hdep Q.c Q.a
      (fun d : ℕ => by
        have hv' := FixedOver.valid Q d
        simpa [FixedOver.level] using hv')
    dsimp [f]
    exact hz
  have hsplit := triple_sum_split F f
  rw [hsplit] at hzeta
  have hQa_eq : Q.a = Bs.a := by rfl
  have hca1 : (((Q.a (Sum.inl PUnit.unit) : RatFunc F)) : RatFunc.CompletionAtInfty F) = 1 := by
    have hc := (bstar_a_coeffs F b hb).1
    have hc' : (((Q.a (Sum.inl PUnit.unit) : RatFunc F)) : RatFunc.CompletionAtInfty F) =
        ((1 : RatFunc F) : RatFunc.CompletionAtInfty F) := by
      rw [hQa_eq]
      dsimp [Bs, D]
      rw [hc]
    rw [hc']
    simp [completion_coe_one]
  have haZeta : (∑ i : D.ιA, f (Sum.inl i)) = ζ_A F (consVec a (pair b (qExp F))) := by
    dsimp [f]
    rw [show (∑ x : D.ιA, ((Q.a (Sum.inl x) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl x))) =
      ((Q.a (Sum.inl PUnit.unit) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl PUnit.unit)) by
          change (∑ x : PUnit, ((Q.a (Sum.inl x) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Q.c (Sum.inl x))) =
            ((Q.a (Sum.inl PUnit.unit) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Q.c (Sum.inl PUnit.unit))
          simp]
    rw [hca1]
    simp [completion_coe_one]
    have ht := bstar_type1_tuple F b hb
    have hq : ζ_A F (Q.c (Sum.inl PUnit.unit)) = ζ_A F (consVec a (pair b (qExp F))) := by
      have hpre : Q.c (Sum.inl PUnit.unit) = consVec a (Bs.c (Sum.inl PUnit.unit)) := by rfl
      rw [hpre]
      exact congrArg (fun t : Fin 2 → ℕ+ => ζ_A F (consVec a t)) ht
    rw [hq]
  have hrel0 : ζ_A F (consVec a (pair b (qExp F))) +
      (∑ i : D.ιB, f (Sum.inr (Sum.inl i))) +
      (∑ i : D.ιB, f (Sum.inr (Sum.inr i))) = 0 := by
    rw [haZeta] at hzeta
    simpa using hzeta
  -- collapse the two b-sums (PUnit singletons over D.ιB)
  have hc2 : (((Q.a (Sum.inr (Sum.inl PUnit.unit)) : RatFunc F)) : RatFunc.CompletionAtInfty F) =
      ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) := by
    have hc := (bstar_a_coeffs F b hb).2.1
    rw [hQa_eq]
    dsimp [Bs, D]
    rw [hc]
  have hc3 : (((Q.a (Sum.inr (Sum.inr PUnit.unit)) : RatFunc F)) : RatFunc.CompletionAtInfty F) =
      ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) := by
    have hc := (bstar_a_coeffs F b hb).2.2
    rw [hQa_eq]
    dsimp [Bs, D]
    rw [hc]
  let b1 : ℕ+ := ⟨(b : ℕ) + 1, Nat.succ_pos (b : ℕ)⟩
  let m2 : Fin 4 → ℕ+ := consVec a (consVec b (pair oneExp (qMinusExp F)))
  let m3 : Fin 3 → ℕ+ := consVec a (pair b1 (qMinusExp F))
  have hz2 : ζ_A F (Q.c (Sum.inr (Sum.inl PUnit.unit))) = ζ_A F m2 := by
    have hpre : Q.c (Sum.inr (Sum.inl PUnit.unit)) = consVec a (Bs.c (Sum.inr (Sum.inl PUnit.unit))) := by rfl
    rw [hpre]
    have ht := bstar_type2_tuple F b hb
    exact congrArg (fun t : Fin 3 → ℕ+ => ζ_A F (consVec a t)) ht
  have hz3 : ζ_A F (Q.c (Sum.inr (Sum.inr PUnit.unit))) = ζ_A F m3 := by
    have hpre : Q.c (Sum.inr (Sum.inr PUnit.unit)) = consVec a (Bs.c (Sum.inr (Sum.inr PUnit.unit))) := by rfl
    rw [hpre]
    have ht := bstar_type3_tuple F b hb
    exact congrArg (fun t : Fin 2 → ℕ+ => ζ_A F (consVec a t)) ht
  have hrel2 : ζ_A F (consVec a (pair b (qExp F))) +
      ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F m2 +
      ((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F m3 = 0 := by
    rw [show (∑ i : D.ιB, f (Sum.inr (Sum.inl i))) =
        (((Q.a (Sum.inr (Sum.inl PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inl PUnit.unit)))) by
          dsimp [f]
          change (∑ x : PUnit, (((Q.a (Sum.inr (Sum.inl x)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Q.c (Sum.inr (Sum.inl x))))) =
            (((Q.a (Sum.inr (Sum.inl PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Q.c (Sum.inr (Sum.inl PUnit.unit))))
          simp] at hrel0
    rw [show (∑ i : D.ιB, f (Sum.inr (Sum.inr i))) =
        (((Q.a (Sum.inr (Sum.inr PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inr PUnit.unit)))) by
          dsimp [f]
          change (∑ x : PUnit, (((Q.a (Sum.inr (Sum.inr x)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Q.c (Sum.inr (Sum.inr x))))) =
            (((Q.a (Sum.inr (Sum.inr PUnit.unit)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
              ζ_A F (Q.c (Sum.inr (Sum.inr PUnit.unit))))
          simp] at hrel0
    rw [hc2, hc3, hz2, hz3] at hrel0
    exact hrel0
  have hneg : ζ_A F (consVec a (pair b (qExp F))) =
      -(((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F m2) +
        -(((D1rat F : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F m3) := by
    have hz := eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hrel2)
    rw [hz]
    rw [neg_add]
  let depc : PUnit ⊕ PUnit → ℕ := fun p => match p with | Sum.inl _ => 4 | Sum.inr _ => 3
  have hdepc : ∀ p : PUnit ⊕ PUnit, 0 < depc p := by
    intro p
    cases p <;> dsimp [depc] <;> omega
  let cc : ∀ p : PUnit ⊕ PUnit, Fin (depc p) → ℕ+ := fun p => match p with
    | Sum.inl _ => m2 | Sum.inr _ => m3
  let ac : PUnit ⊕ PUnit → RatFunc F := fun p => match p with
    | Sum.inl _ => -D1rat F | Sum.inr _ => -D1rat F
  have hw2 : weight 4 m2 = w := by
    dsimp [m2, w]
    rw [weight_consVec, weight_consVec, weight_pair]
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
    have ho : (oneExp : ℕ) = 1 := rfl
    rw [hq, ho]
    have hq2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have hw3 : weight 3 m3 = w := by
    dsimp [m3, w]
    rw [weight_consVec]
    rw [weight_pair b1 (qMinusExp F)]
    have hb1 : (b1 : ℕ) = (b : ℕ) + 1 := rfl
    have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
    rw [hb1, hq]
    have hq2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  have ha2 : kAdmissible (Nat.card F) m2 3 := by
    constructor
    · intro x hx
      have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by omega
      rcases hx3 with hx0 | hx1 | hx2
      · subst x
        have hp : pad0 m2 0 = (a : ℕ) := by
          dsimp [m2]
          rw [pad0_of_lt (consVec a (consVec b (pair oneExp (qMinusExp F)))) (by omega : 0 < 4)]
          rfl
        rw [hp]
        exact ha
      · subst x
        have hp : pad0 m2 1 = (b : ℕ) := by
          dsimp [m2]
          rw [pad0_consVec]
          rw [pad0_of_lt (consVec b (pair oneExp (qMinusExp F))) (by omega : 0 < 3)]
          rfl
        rw [hp]
        omega
      · subst x
        have hp : pad0 m2 2 = 1 := by
          dsimp [m2]
          rw [pad0_consVec]
          rw [pad0_consVec]
          rw [pad0_of_lt (pair oneExp (qMinusExp F)) (by omega : 0 < 2)]
          rfl
        rw [hp]
        have hq2 : 2 ≤ Nat.card F := card_ge_two F
        omega
    · intro hf
      rcases hf with ⟨hr1, hdep, hall, hlast⟩
      omega
  have ha3 : kAdmissible (Nat.card F) m3 3 := by
    constructor
    · intro x hx
      have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by omega
      rcases hx3 with hx0 | hx1 | hx2
      · subst x
        have hp : pad0 m3 0 = (a : ℕ) := by
          dsimp [m3]
          rw [pad0_of_lt (consVec a (pair ⟨(b : ℕ) + 1, Nat.succ_pos (b : ℕ)⟩ (qMinusExp F)))
            (by omega : 0 < 3)]
          rfl
        rw [hp]
        exact ha
      · subst x
        have hp : pad0 m3 1 = (b : ℕ) + 1 := by
          dsimp [m3]
          rw [pad0_consVec]
          rw [pad0_of_lt (pair b1 (qMinusExp F)) (by omega : 0 < 2)]
          rfl
        rw [hp]
        omega
      · subst x
        have hp : pad0 m3 2 = (qMinusExp F : ℕ) := by
          dsimp [m3]
          rw [pad0_consVec]
          rw [pad0_of_lt (pair b1 (qMinusExp F)) (by omega : 1 < 2)]
          rfl
        rw [hp]
        change (qMinusExp F : ℕ) ≤ Nat.card F
        have hq : (qMinusExp F : ℕ) = Nat.card F - 1 := rfl
        rw [hq]
        omega
    · intro hf
      rcases hf with ⟨hr1, hdep, hall, hlast⟩
      have hp2 : pad0 m3 2 = (qMinusExp F : ℕ) := by
        dsimp [m3]
        rw [pad0_consVec]
        rw [pad0_of_lt (pair b1 (qMinusExp F)) (by omega : 1 < 2)]
        rfl
      have hlast2 : (m3 ⟨2, (by omega : 2 < 3)⟩ : ℕ) = Nat.card F := by
        change (m3 ⟨3 - 1, by omega⟩ : ℕ) = Nat.card F
        exact hlast
      have hpad : pad0 m3 2 = (m3 ⟨2, (by omega : 2 < 3)⟩ : ℕ) := by
        rw [pad0_of_lt m3 (by omega : 2 < 3)]
      have hval : (m3 ⟨2, (by omega : 2 < 3)⟩ : ℕ) = Nat.card F - 1 := by
        rw [← hpad]
        exact hp2
      have hq2 : 2 ≤ Nat.card F := card_ge_two F
      omega
  have hps : ∀ ℓ : ℕ, 3 ≤ ℓ → psum s ℓ = w := by
    intro ℓ hℓ
    have hd := psum_ge_depth s (by omega : 3 ≤ ℓ)
    rw [hd]
    dsimp [s, w]
    rw [weight_consVec, weight_pair]
    have hq : (qExp F : ℕ) = Nat.card F := rfl
    rw [hq]
    omega
  have horder2 : ∀ ℓ : ℕ, 3 ≤ ℓ → psum m2 ℓ ≤ psum s ℓ := by
    intro ℓ hℓ
    rw [hps ℓ hℓ]
    have h1 := psum_le_weight m2 ℓ
    rw [hw2] at h1
    exact h1
  have horder3 : ∀ ℓ : ℕ, 3 ≤ ℓ → psum m3 ℓ ≤ psum s ℓ := by
    intro ℓ hℓ
    rw [hps ℓ hℓ]
    have h1 := psum_le_weight m3 ℓ
    rw [hw3] at h1
    exact h1
  refine ⟨PUnit ⊕ PUnit, inferInstance, depc, hdepc, cc, ac, ?_, ?_, ?_, ?_⟩
  · intro p
    cases p with
    | inl _ => exact hw2
    | inr _ => exact hw3
  · intro p
    cases p with
    | inl _ => exact ha2
    | inr _ => exact ha3
  · intro p ℓ hℓ
    cases p with
    | inl _ => exact horder2 ℓ hℓ
    | inr _ => exact horder3 ℓ hℓ
  · rw [hneg]
    rw [Fintype.sum_sum_type]
    dsimp [ac, cc, m2, m3, depc]
    rw [sum_PUnit, sum_PUnit]
    rw [ratFunc_coe_neg F (D1rat F)]
    ring

end ZagierHoffmanPositiveChar
