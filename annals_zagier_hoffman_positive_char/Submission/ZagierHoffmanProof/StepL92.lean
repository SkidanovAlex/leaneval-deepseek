import Submission.ZagierHoffmanProof.StepL91
import Submission.ZagierHoffmanProof.StepL89
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L92: main3_case2_j1 — the CASE-2 (a,q,q) j=1 splice at level 3 (SESSION 248)

★ main3_case2_j1 (w s hw h2) (hsj : s₀ < q) (h1q : s₁ = q)
(h2q : s₂ = q) (rec : Main3Step → 2-adm → ¬3-adm → AdmExpT F w 3)
: AdmExpT F w 3 s — the in-domain depth-3 tuple (a, q, q) with a < q (CASE-2,
b = q, the last remaining j=1 boundary form) expands at level 3.

STRUCTURE (prop213_step1 at (3,1) + main2_case1_j1-style two-family fold):
derive hqend (s₁ = s₂ = q) + hsleq (2-adm pad0-bounds); rcases
prop213_step1 F 3 s 1 … with ⟨hrel, hT2, hT3⟩ (R1 chain: D := BCqIter F 1
(toData r1Rel), Bs := ofBstarOver D (s⟨0⟩), Q := prependList Bs (sPrefix 3 s 1) =
Bs since the front is empty); hrel0 := simpa [D, Bs, Q, sPrefix] using hrel
(ζ(s) + type-2 + type-3 = 0); the two-family fold (mdep/mc/ma over
ι := D.ιB ⊕ D.ιB, Fintype.sum_sum_type + neg_coe_mul_zeta);
per-member e: weight = weight 3 s via EXACT (hT2 i).1/(hT3 i).1 (proof-irrelevance
bridges the let-expanded member tuples to the Q/Bs lets — no simp!), 2-adm via
StepL91's case2j1_type{2,3}_twoAdm (exact again), 3-adm → admExpT_self /
¬3-adm → Main3Step ((hT2 i).2 strict prefix-3 drop, or (hT3 i).2.1 ≤ +
(hT3 i).2.2 InitLt → l3_member_step) → rec; horder trivial by weight
saturation (depth-3 s: psum s ℓ = weight 3 s for ℓ ≥ 3) with
psum_le_weight; splice by admExpT_combine.
ALSO: tuple3_eq_consVec_pair (generic depth-3 reconstruction from entries — used
by main3's CASE-2 b<q leaf wiring to express s = consVec a (pair b q)).
NEXT: the (q,q,q) leaf (level-3 G5 analogue of StepL75's g5_case2_qq with
D := BCqIter F 2 (toData r1Rel)), then main3's CASE-2 b=q branch wiring and
main3 committed.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ MAIN(3) CASE-2 j=1: the depth-3 (a,q,q) in-domain tuple (a < q = s₁ = s₂)
expands at level 3 via prop213_step1 at (3,1), with rec for ¬3-adm members. -/
theorem main3_case2_j1 (w : ℕ) (s : Fin 3 → ℕ+) (hw : weight 3 s = w)
    (h2 : kAdmissible (Nat.card F) s 2)
    (hsj : (s ⟨0, by omega⟩ : ℕ) < Nat.card F)
    (h1q : (s ⟨1, by omega⟩ : ℕ) = Nat.card F)
    (h2q : (s ⟨2, by omega⟩ : ℕ) = Nat.card F)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      Main3Step (Nat.card F) s m → kAdmissible (Nat.card F) m 2 →
      ¬ kAdmissible (Nat.card F) m 3 → AdmExpT F w 3 m) :
    AdmExpT F w 3 s := by
  classical
  have hqend : ∀ i : Fin 3, (1 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 3 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    have hiv : (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by omega
    rcases hiv with hi'1 | hi'2
    · have hidx : i = ⟨1, (by omega : 1 < 3)⟩ := by
        apply Fin.ext
        omega
      rw [hidx]
      exact h1q
    · have hidx : i = ⟨2, (by omega : 2 < 3)⟩ := by
        apply Fin.ext
        omega
      rw [hidx]
      exact h2q
  have hsleq : ∀ x : ℕ, x < 3 - 1 → pad0 s x ≤ Nat.card F := by
    intro x hx
    exact kAdmissible.pad0_le h2 x (by omega)
  rcases prop213_step1 F 3 s 1 (by omega : 1 ≤ 3) (by omega : 1 ≤ 1)
    (by omega : 1 ≤ 3 - 1) hsj hqend hsleq with ⟨hrel, hT2, hT3⟩
  let a : ℕ+ := s ⟨0, by omega⟩
  let D : RelData F := RelData.BCqIter F 1 (toData F (r1Rel F))
  let Bs : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) :=
    ofBstarOver F D (s ⟨0, by omega⟩) (fun e => BCqIter_valid F 1 (r1Rel F) e)
      (RelData.iterate_merge_hv F 1 (r1Rel F) (s ⟨0, by omega⟩) (by omega) (r1Rel_hbhd F))
  let Q : FixedOver F (D.ιA ⊕ (D.ιB ⊕ D.ιB)) :=
    FixedOver.prependList F Bs (sPrefix 3 s 1 (by omega) (by omega))
  have ha : (a : ℕ) < Nat.card F := by
    dsimp [a]
    exact hsj
  -- the (2.15) ζ-identity at (3,1): ζ(s) + type2 + type3 = 0
  have hrel0 : ζ_A F s +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inl i))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inr (Sum.inr i))))) = 0 := by
    simpa [D, Bs, Q, sPrefix] using hrel
  -- two-family fold
  let ι : Type := D.ιB ⊕ D.ιB
  let mdep (p : ι) : ℕ := match p with
    | Sum.inl i => Q.dep (Sum.inr (Sum.inl i))
    | Sum.inr i => Q.dep (Sum.inr (Sum.inr i))
  let mhdep (p : ι) : 0 < mdep p := by
    dsimp [mdep]
    cases p with
    | inl i => exact Q.hdep (Sum.inr (Sum.inl i))
    | inr i => exact Q.hdep (Sum.inr (Sum.inr i))
  let mc (p : ι) : Fin (mdep p) → ℕ+ := match p with
    | Sum.inl i => Q.c (Sum.inr (Sum.inl i))
    | Sum.inr i => Q.c (Sum.inr (Sum.inr i))
  let ma (p : ι) : RatFunc F := match p with
    | Sum.inl i => -(Q.a (Sum.inr (Sum.inl i)))
    | Sum.inr i => -(Q.a (Sum.inr (Sum.inr i)))
  let x₂ (i : D.ιB) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let x₃ (i : D.ιB) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hid3 : ζ_A F s = -(∑ i : D.ιB, x₂ i) + -(∑ i : D.ιB, x₃ i) := by
    have hrel' : ζ_A F s + (∑ i : D.ιB, x₂ i) + (∑ i : D.ιB, x₃ i) = 0 := by
      simpa [x₂, x₃] using hrel0
    have h' : ζ_A F s + ((∑ i : D.ιB, x₂ i) + (∑ i : D.ιB, x₃ i)) = 0 := by simpa [add_assoc] using hrel'
    have hz : ζ_A F s = -((∑ i : D.ιB, x₂ i) + (∑ i : D.ιB, x₃ i)) := eq_neg_of_add_eq_zero_left h'
    rw [hz]
    abel
  have hid3' : ζ_A F s = ∑ p : ι, (match p with
      | Sum.inl i => -(x₂ i)
      | Sum.inr i => -(x₃ i)) := by
    calc
      ζ_A F s = -(∑ i : D.ιB, x₂ i) + -(∑ i : D.ιB, x₃ i) := hid3
      _ = ∑ p : ι, (match p with
           | Sum.inl i => -(x₂ i)
           | Sum.inr i => -(x₃ i)) := by
             classical
             rw [Fintype.sum_sum_type]
             simp [Finset.sum_neg_distrib]
  have hid : ζ_A F s = ∑ p : ι, (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    rw [hid3']
    apply Finset.sum_congr rfl
    intro p hp
    cases p with
    | inl i =>
        dsimp [x₂, ma, mc]
        exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i)))).symm
    | inr i =>
        dsimp [x₃, ma, mc]
        exact (neg_coe_mul_zeta F (Q.a (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i)))).symm
  -- per-member expansions
  have e : ∀ p : ι, AdmExpT F w 3 (mc p) := by
    intro p
    cases p with
    | inl i =>
        have hw1 : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = weight 3 s := by
          exact (hT2 i).1
        have h2m : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 2 := by
          exact (case2j1_type2_twoAdm F a ha i)
        by_cases h3m : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 3
        · have hd : 0 < Q.dep (Sum.inr (Sum.inl i)) := Q.hdep (Sum.inr (Sum.inl i))
          have hw' : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w := by
            rw [hw1]; exact hw
          exact admExpT_self F w 3 hd (Q.c (Sum.inr (Sum.inl i))) hw' h3m
        · have hstep : Main3Step (Nat.card F) s (Q.c (Sum.inr (Sum.inl i))) := by
            have hps : psum (Q.c (Sum.inr (Sum.inl i))) 3 < psum s 3 := by
              exact (hT2 i).2
            exact Or.inl hps
          have hwm' : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w := by
            rw [hw1]; exact hw
          exact rec (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) hwm' hstep h2m h3m
    | inr i =>
        have hw1 : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = weight 3 s := by
          exact (hT3 i).1
        have h2m : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
          exact (case2j1_type3_twoAdm F a ha i)
        by_cases h3m : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 3
        · have hd : 0 < Q.dep (Sum.inr (Sum.inr i)) := Q.hdep (Sum.inr (Sum.inr i))
          have hw' : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w := by
            rw [hw1]; exact hw
          exact admExpT_self F w 3 hd (Q.c (Sum.inr (Sum.inr i))) hw' h3m
        · have hstep : Main3Step (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
            have hle : psum (Q.c (Sum.inr (Sum.inr i))) 3 ≤ psum s 3 := by
              exact (hT3 i).2.1
            have hinit : InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
              exact (hT3 i).2.2
            exact l3_member_step (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))
              (Or.inr ⟨hle, hinit⟩)
          have hwm' : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w := by
            rw [hw1]; exact hw
          exact rec (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) hwm' hstep h2m h3m
  -- member orders: trivial (depth-3 s saturates at ℓ ≥ 3)
  have horder : ∀ p : ι, ∀ ℓ : ℕ, 3 ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    have hwl := psum_le_weight (mc p) ℓ
    have hwm : weight (mdep p) (mc p) = weight 3 s := by
      cases p with
      | inl i => dsimp [mdep, mc]; exact (hT2 i).1
      | inr i => dsimp [mdep, mc]; exact (hT3 i).1
    have hpeq : weight 3 s = psum s ℓ := (psum_ge_depth s hℓ).symm
    rw [hwm, hpeq] at hwl
    exact hwl
  exact admExpT_combine F w 3 s mdep mhdep mc ma hid horder e

/-- A depth-3 tuple is determined by its three entries. -/
lemma tuple3_eq_consVec_pair (s : Fin 3 → ℕ+) (a b c : ℕ+)
    (h0 : (s ⟨0, by omega⟩ : ℕ) = (a : ℕ))
    (h1 : (s ⟨1, by omega⟩ : ℕ) = (b : ℕ))
    (h2 : (s ⟨2, by omega⟩ : ℕ) = (c : ℕ)) : s = consVec a (pair b c) := by
  funext j
  by_cases hj0 : (j : ℕ) = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext (by simpa using hj0)
    rw [hj]
    rw [consVec_zero]
    apply Subtype.ext
    exact h0
  · by_cases hj1 : (j : ℕ) = 1
    · have hj : j = ⟨1, by omega⟩ := Fin.ext (by simpa using hj1)
      rw [hj]
      change (s ⟨1, by omega⟩ : ℕ+) =
        (consVec a (pair b c)) ⟨(0 : Fin 2).1 + 1, by omega⟩
      rw [consVec_succ]
      change (s ⟨1, by omega⟩ : ℕ+) = (pair b c) ⟨0, by omega⟩
      rw [pair]
      simp
      apply Subtype.ext
      exact h1
    · have hj2 : (j : ℕ) = 2 := by omega
      have hj : j = ⟨2, by omega⟩ := Fin.ext (by simpa using hj2)
      rw [hj]
      change (s ⟨2, by omega⟩ : ℕ+) =
        (consVec a (pair b c)) ⟨(1 : Fin 2).1 + 1, by omega⟩
      rw [consVec_succ]
      change (s ⟨2, by omega⟩ : ℕ+) = (pair b c) ⟨1, by omega⟩
      rw [pair]
      simp
      apply Subtype.ext
      exact h2
end ZagierHoffmanPositiveChar
