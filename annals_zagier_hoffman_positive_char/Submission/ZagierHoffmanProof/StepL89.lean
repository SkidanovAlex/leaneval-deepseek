import Submission.ZagierHoffmanProof.StepL88
import Submission.ZagierHoffmanProof.StepL87
import Submission.ZagierHoffmanProof.StepL86
import Submission.ZagierHoffmanProof.StepL82
import Submission.ZagierHoffmanProof.StepL73
import Submission.ZagierHoffmanProof.StepL49
import Submission.ZagierHoffmanProof.StepL34
import Submission.ZagierHoffmanProof.StepL48
import Submission.ZagierHoffmanProof.StepL47
import Submission.ZagierHoffmanProof.StepL32
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L89: main3_case1_j2 — the CASE-1 j=2 splice (prop212 at (3,2))

SESSION 248.  ★ main3_case1_j2 (w r s hw) (hcase3 : 3 ≤ r) (hbigv : q < s⟨2⟩)
(hs0 : s₀ ≤ q) (hs1q : s₁ < q) (rec : Main3Step → 2-adm → ¬3-adm →
AdmExpT F w 3) : AdmExpT F w 3 s — every in-domain (2-adm ∧ ¬3-adm) weight-w
tuple with the j=2 shape (s₁ < q ≤ ... ≥ s₂ > q; s₀ ≤ q) expands at level 3.
main3's CASE-1 dispatch calls this in the pad0 s 1 < q subcase (with rec := main3's
own l3-induction IH).

STRUCTURE: exact (3,2) mirror of StepL88's main3_case1_j1 (same script, j-shifted):
rcases lemma_2_9_rel at (r−3, w1, B); derive hc0/hwtA/hhead/hXw/hbndB/hpref;
chain ζ-identity hid0 := simpa [D, Bs, Q] using (zeta_214_reindexed … at (3,2))
with D := BCqIter F 0, B*_{s₁}, front = sPrefix r s 2 = [s₀, s₁] (the simpa
bridges the (3−2−1)-chain to the (0)-chain); 3-family fold (main2_case1_j1
script); per-member e with the StepL87 level3_j2_type{1,2,3}_twoAdm_of facts
(type-3 now needs NO weight arg); horder via type1_psum_decompose_ge +
type2_psum_ge_k_lt/type3_psum_ge_k_le + weight saturation; splice by
admExpT_combine.  hmid is VACUOUS at j=2 (entries 2 ≤ i < 2 don't exist);
hsleq uses hs0 for pad0 s 0 and hs1q for pad0 s 1.  NEXT: main3's CASE-1 wiring
(j=0 via g53_case1_step / j=1 / j=2 by_cases on pad0 s 1 = q), then CASE-2 and
the theorem_A span.  theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]


theorem main3_case1_j2 (w : ℕ) (r : ℕ) (s : Fin r → ℕ+) (hw : weight r s = w)
    (hcase3 : 3 ≤ r) (hbigv : (Nat.card F : ℕ) < (s ⟨2, by omega⟩ : ℕ))
    (hs0 : (s ⟨0, by omega⟩ : ℕ) ≤ Nat.card F)
    (hs1q : (s ⟨1, by omega⟩ : ℕ) < Nat.card F)
    (rec : ∀ (r' : ℕ) (m : Fin r' → ℕ+) (hm : weight r' m = w),
      Main3Step (Nat.card F) s m → kAdmissible (Nat.card F) m 2 →
      ¬ kAdmissible (Nat.card F) m 3 → AdmExpT F w 3 m) :
    AdmExpT F w 3 s := by
  classical
  have hmid : ∀ i : Fin r, (2 : ℕ) ≤ (i : ℕ) → (i : ℕ) < 2 → (s i : ℕ) = Nat.card F := by
    intro i hi1 hi2
    omega
  have hsleq : ∀ x : ℕ, x < 2 → pad0 s x ≤ Nat.card F := by
    intro x hx
    have hx01 : x = 0 ∨ x = 1 := by omega
    rcases hx01 with hx0 | hx1
    · subst x
      have hp : pad0 s 0 = (s ⟨0, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 0 < r)
      rw [hp]
      exact hs0
    · subst x
      have hp : pad0 s 1 = (s ⟨1, by omega⟩ : ℕ) := pad0_of_lt s (by omega : 1 < r)
      rw [hp]
      omega
  have hsum : psum s 3 = psum s (3 - 1) + (s ⟨2, by omega⟩ : ℕ) := by
    have hpl := psum_last r s 3 (by omega : 1 ≤ 3) hcase3
    simpa using hpl
  have hmono : psum s 3 ≤ psum s r := psum_mono s hcase3
  have hmono2 : psum s (3 - 1) ≤ psum s r := psum_mono s (by omega : 3 - 1 ≤ r)
  have hq1 : 1 ≤ Nat.card F := by
    have h2 : 2 ≤ Nat.card F := card_ge_two F
    omega
  let w1 : ℕ+ := w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv
  let B : Fin (r - 3) → ℕ+ := sTail r s 3 hcase3
  rcases lemma_2_9_rel F (r - 3) w1 B with ⟨R0, u, hdep, ha, hc, hleA, hbhd, hleB, hvalid⟩
  have hdepu : R0.depA u = (r - 3) + 1 := hdep
  have hau : R0.aA u = 1 := ha
  have hc0 : ∀ hd : R0.depA u = (r - 3) + 1,
      (fun x : Fin ((r - 3) + 1) => R0.cA u (Fin.cast hd.symm x)) =
        bstarBase F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv := by
    intro hd
    simpa [bstarBase, w1, B] using hc hd
  have hwtA : ∀ i : R0.ιA, i ≠ u → weight (R0.depA i) (R0.cA i) = psum s r - psum s (3 - 1) := by
    intro i hi
    have hL := hleA i hi
    have hw' : (w1 : ℕ) = (s ⟨3 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depA i) (R0.cA i)
          = weight 1 (single (qExp F)) + weight ((r - 3) + 1) (consVec w1 B) := hL.1.1
      _ = (qExp F : ℕ) + ((w1 : ℕ) + weight (r - 3) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = Nat.card F + ((w1 : ℕ) + (psum s r - psum s 3)) := by
            rw [show (qExp F : ℕ) = Nat.card F by rfl]
            rw [weight_sTail r s 3 hcase3]
      _ = psum s r - psum s (3 - 1) := by
            rw [hw']
            have hnorm : (s ⟨3 - 1, by omega⟩ : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨3 - 1, by omega⟩ : ℕ) := by
    intro i hi
    have hL2 := (hleA i hi).2
    have hwadd : (qExp F : ℕ) + (w1 : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by
      dsimp [w1]
      exact w1Of_add F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv
    have hL2' : ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨2, by omega⟩ : ℕ) := by
      simpa [hwadd] using hL2
    have hnorm : (s ⟨3 - 1, by omega⟩ : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by rfl
    rw [hnorm]
    exact hL2'
  have hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (3 - 1) - 1 := by
    intro j'
    have hL := hleB j'
    have hw' : (w1 : ℕ) = (s ⟨3 - 1, by omega⟩ : ℕ) - Nat.card F := by
      dsimp [w1]
      rfl
    calc
      weight (R0.depB j' - 1) (expTail (R0.cB j'))
          = weight 1 (single (qMinusExp F)) + weight ((r - 3) + 1) (consVec w1 B) := hL.1
      _ = (qMinusExp F : ℕ) + ((w1 : ℕ) + weight (r - 3) B) := by
            rw [weight_single]
            rw [weight_consVec]
      _ = (Nat.card F - 1) + ((w1 : ℕ) + (psum s r - psum s 3)) := by
            rw [show (qMinusExp F : ℕ) = Nat.card F - 1 by rfl]
            rw [weight_sTail r s 3 hcase3]
      _ = psum s r - psum s (3 - 1) - 1 := by
            rw [hw']
            have hnorm : (s ⟨3 - 1, by omega⟩ : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by rfl
            rw [hnorm]
            omega
  have hbndB : ∀ j' : R0.ιB, ∀ m : ℕ,
      psum (expTail (R0.cB j')) m ≤ psumSeq (tupPadSum (single (qMinusExp F))
        (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) m := by
    intro j' m
    have hL := hleB j'
    simpa [w1, B] using (hL.2 m)
  have hpref : ∀ i : R0.ιA, i ≠ u → ∀ m : ℕ,
      psum (R0.cA i) m ≤ psumSeq (tupPadSum (single (qExp F))
        (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) m := by
    intro i hi m
    have hL := (hleA i hi).1
    simpa [w1, B] using (hL.2 m)
  -- the (2.14) chain ζ-identity at (3, 1) (zeta_214_reindexed packages it)
  have hz := zeta_214_reindexed F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
    (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 u hau hdepu hc0 hbhd

  let D := RelData.BCqIter F 0 (toData F R0)
  let Bs := ofBstarOver F D (s ⟨1, by omega⟩) (fun e => BCqIter_valid F 0 R0 e)
        (RelData.iterate_merge_hv F 0 R0 (s ⟨1, by omega⟩) (by omega) hbhd)
  let Q := FixedOver.prependList F Bs (sPrefix r s 2 (by omega) (by omega))
  have hid0 : ζ_A F s +
      (∑ i₀ : R0.ιA, (if i₀ = u then 0 else
        (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inl i))))) +
      (∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
          ζ_A F (Q.c (Sum.inr (Sum.inr i))))) = 0 := by
    simpa [D, Bs, Q] using hz
  -- expansion family (the main2_case1_j1 3-part fold at level 3)
  let ι₁ : Type := {i₀ : R0.ιA // i₀ ≠ u}
  let ι₂ : Type := D.ιB
  let ι₃ : Type := D.ιB
  let ι : Type := ι₁ ⊕ (ι₂ ⊕ ι₃)
  let inst₁ : Fintype ι₁ :=
    Fintype.subtype ((Finset.univ : Finset R0.ιA).filter (fun i₀ => i₀ ≠ u))
      (by intro x; simp [Finset.mem_filter])
  letI : Fintype ι₁ := inst₁
  let mdep (p : ι) : ℕ := match p with
    | Sum.inl q => Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.dep (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.dep (Sum.inr (Sum.inr i))
  let mhdep (p : ι) : 0 < mdep p := by
    dsimp [mdep]
    cases p with
    | inl q => exact Q.hdep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
    | inr s => cases s with
      | inl i => exact Q.hdep (Sum.inr (Sum.inl i))
      | inr i => exact Q.hdep (Sum.inr (Sum.inr i))
  let mc (p : ι) : Fin (mdep p) → ℕ+ := match p with
    | Sum.inl q => Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
    | Sum.inr (Sum.inl i) => Q.c (Sum.inr (Sum.inl i))
    | Sum.inr (Sum.inr i) => Q.c (Sum.inr (Sum.inr i))
  let ma (p : ι) : RatFunc F := match p with
    | Sum.inl q => -(Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)))
    | Sum.inr (Sum.inl i) => -(Q.a (Sum.inr (Sum.inl i)))
    | Sum.inr (Sum.inr i) => -(Q.a (Sum.inr (Sum.inr i)))
  let A : RatFunc.CompletionAtInfty F :=
    ∑ i₀ : R0.ιA, (if i₀ = u then 0 else
      (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))))
  let B : RatFunc.CompletionAtInfty F :=
    ∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let C : RatFunc.CompletionAtInfty F :=
    ∑ i : D.ιB, (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hrel' : ζ_A F s + A + B + C = 0 := by
    dsimp [A, B, C, Q, Bs, D]
    exact hid0
  have hid3 : ζ_A F s = -A + -B + -C := eq_neg_add_add_add' (ζ_A F s) A B C hrel'
  let x₁ (p : ι₁) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) p.1)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
      ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) p.1))))
  let x₂ (i : ι₂) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inl i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inl i))))
  let x₃ (i : ι₃) : RatFunc.CompletionAtInfty F :=
    (((Q.a (Sum.inr (Sum.inr i)) : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (Q.c (Sum.inr (Sum.inr i))))
  have hA : A = ∑ p : ι₁, x₁ p := by
    dsimp [A, x₁]
    exact sum_guarded_subtype' (u := u)
      (f := fun i₀ : R0.ιA => (((Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)) : RatFunc F) : RatFunc.CompletionAtInfty F) *
        ζ_A F (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) i₀)))))
  rw [hA] at hid3
  have hid3' : ζ_A F s = ∑ p : ι,
      (match p with
       | Sum.inl q => -(x₁ q)
       | Sum.inr (Sum.inl i) => -(x₂ i)
       | Sum.inr (Sum.inr i) => -(x₃ i)) := by
    calc
      ζ_A F s = -(∑ p : ι₁, x₁ p) + -(∑ i : ι₂, x₂ i) + -(∑ i : ι₃, x₃ i) := by
        simpa [x₂, x₃] using hid3
      _ = ∑ p : ι, (match p with
           | Sum.inl q => -(x₁ q)
           | Sum.inr (Sum.inl i) => -(x₂ i)
           | Sum.inr (Sum.inr i) => -(x₃ i)) := by
        exact neg_sum_sum_type' x₁ x₂ x₃
  have hid : ζ_A F s = ∑ p : ι, (((ma p : RatFunc F) : RatFunc.CompletionAtInfty F) * ζ_A F (mc p)) := by
    rw [hid3']
    apply Finset.sum_congr rfl
    intro p hp
    cases p with
    | inl q =>
        dsimp [x₁, ma, mc]
        exact (neg_coe_mul_zeta F (Q.a (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)))
          (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)))).symm
    | inr s =>
        cases s with
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
    | inl q =>
        let m : Fin (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) → ℕ+ :=
          Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
        have hw1 : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) m = weight r s := by
          simpa [m] using (type1_weight_eq F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
            (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd q.1 (hwtA q.1 q.2))
        by_cases h3m : kAdmissible (Nat.card F) m 3
        · have hd : 0 < Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)) :=
            Q.hdep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))
          have hw' : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1)))
              (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) = w := by
            rw [hw1]; exact hw
          have h3m' : kAdmissible (Nat.card F)
              (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) 3 := by simpa [m] using h3m
          exact admExpT_self F w 3 hd (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) hw' h3m'
        · have h2m' : kAdmissible (Nat.card F)
              (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) 2 := by
            simpa [m] using (level3_j2_type1_twoAdm_of F r s hcase3 hbigv hs0 hs1q R0 u hbhd q.1 q.2)
          have h2m : kAdmissible (Nat.card F) m 2 := by simpa [m] using h2m'
          have hstep : Main3Step (Nat.card F) s m := by
            have hps : psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) 3 < psum s 3 := by
              simpa [m] using (type1_psum_lt_k F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd q.1 (hhead q.1 q.2))
            exact Or.inl (by simpa [m] using hps)
          have hwm' : weight (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) m = w := by
            rw [hw1]; exact hw
          have hres := rec (Q.dep (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) m hwm' hstep h2m h3m
          simpa [m] using hres
    | inr s =>
        cases s with
        | inl i =>
            let m : Fin (Q.dep (Sum.inr (Sum.inl i))) → ℕ+ := Q.c (Sum.inr (Sum.inl i))
            have hw1 : weight (Q.dep (Sum.inr (Sum.inl i))) m = weight r s := by
              simpa [m] using (type2_weight_eq F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd i hXw)
            by_cases h3m : kAdmissible (Nat.card F) m 3
            · have hd : 0 < Q.dep (Sum.inr (Sum.inl i)) := Q.hdep (Sum.inr (Sum.inl i))
              have hw' : weight (Q.dep (Sum.inr (Sum.inl i))) (Q.c (Sum.inr (Sum.inl i))) = w := by
                rw [hw1]; exact hw
              have h3m' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 3 := by simpa [m] using h3m
              exact admExpT_self F w 3 hd (Q.c (Sum.inr (Sum.inl i))) hw' h3m'
            · have h2m' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inl i))) 2 := by
                simpa [m] using (level3_j2_type2_twoAdm_of F r s hcase3 hbigv hs0 hs1q R0 u hbhd i)
              have h2m : kAdmissible (Nat.card F) m 2 := by simpa [m] using h2m'
              have hstep : Main3Step (Nat.card F) s m := by
                have hps : psum (Q.c (Sum.inr (Sum.inl i))) 3 < psum s 3 := by
                  simpa [m] using (type2_psum_lt_k F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                    (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd i)
                exact Or.inl (by simpa [m] using hps)
              have hwm' : weight (Q.dep (Sum.inr (Sum.inl i))) m = w := by
                rw [hw1]; exact hw
              have hres := rec (Q.dep (Sum.inr (Sum.inl i))) m hwm' hstep h2m h3m
              simpa [m] using hres
        | inr i =>
            let m : Fin (Q.dep (Sum.inr (Sum.inr i))) → ℕ+ := Q.c (Sum.inr (Sum.inr i))
            have hw1 : weight (Q.dep (Sum.inr (Sum.inr i))) m = weight r s := by
              simpa [m] using (type3_weight_eq F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd i hXw)
            by_cases h3m : kAdmissible (Nat.card F) m 3
            · have hd : 0 < Q.dep (Sum.inr (Sum.inr i)) := Q.hdep (Sum.inr (Sum.inr i))
              have hw' : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w := by
                rw [hw1]; exact hw
              have h3m' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 3 := by simpa [m] using h3m
              exact admExpT_self F w 3 hd (Q.c (Sum.inr (Sum.inr i))) hw' h3m'
            · have h2m' : kAdmissible (Nat.card F) (Q.c (Sum.inr (Sum.inr i))) 2 := by
                simpa [m] using (level3_j2_type3_twoAdm_of F r s hcase3 hbigv hs0 hs1q R0 u hbhd i)
              have h2m : kAdmissible (Nat.card F) m 2 := by simpa [m] using h2m'
              have hstep : Main3Step (Nat.card F) s m := by
                have hle : psum (Q.c (Sum.inr (Sum.inr i))) 3 ≤ psum s 3 := by
                  simpa [m] using (type3_psum_k_le_X F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                    (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd
                    (fun mm : ℕ => psumSeq (tupPadSum (single (qMinusExp F))
                      (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) mm)
                    hbndB (lemma29_X1_le F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) i)
                have hinit : InitLt (Nat.card F) s (Q.c (Sum.inr (Sum.inr i))) := by
                  simpa [m] using (type3_Init_gt F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                    (by omega : 2 ≤ 3 - 1) hbigv hs1q hsleq R0 hbhd i)
                exact l3_member_step (Nat.card F) s (Q.c (Sum.inr (Sum.inr i)))
                  (Or.inr ⟨hle, hinit⟩)
              have hwm' : weight (Q.dep (Sum.inr (Sum.inr i))) m = w := by
                rw [hw1]; exact hw
              have hres := rec (Q.dep (Sum.inr (Sum.inr i))) m hwm' hstep h2m h3m
              simpa [m] using hres
  -- member orders (type-lemmas at k=3 for ℓ ∈ [3, r]; saturation beyond r)
  have horder : ∀ p : ι, ∀ ℓ : ℕ, 3 ≤ ℓ → psum (mc p) ℓ ≤ psum s ℓ := by
    intro p ℓ hℓ
    by_cases hℓr : ℓ ≤ r
    · cases p with
      | inl q =>
          -- type-1: decompose psum(member)ℓ = psum s 2 + psum(R0.cA q.1)(ℓ−2), bound by hpref + qExp-telescope
          have hdec0 := type1_psum_decompose_ge F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
            (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd q.1 ℓ hℓ
          have hdec : psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) ℓ =
              psum s (3 - 1) + psum (R0.cA q.1) (ℓ - 2) := by
            simpa [show ℓ - 3 + 1 = ℓ - 2 by omega] using hdec0
          have hpre := hpref q.1 q.2 (ℓ - 2)
          have htel := lemma29_qExp_telescope F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv (ℓ - 2) (by omega : 1 ≤ ℓ - 2)
          have htel' : psumSeq (tupPadSum (single (qExp F))
              (consVec (w1Of F r s 3 (by omega : 1 ≤ 3) hcase3 hbigv) (sTail r s 3 hcase3))) (ℓ - 2) ≤
              (s ⟨2, by omega⟩ : ℕ) + (psum s ℓ - psum s 3) := by
            rw [htel]
            congr 1
            have hidx : 3 + (ℓ - 2) - 1 = ℓ := by omega
            rw [hidx]
          have hb : psum (R0.cA q.1) (ℓ - 2) ≤ (s ⟨2, by omega⟩ : ℕ) + (psum s ℓ - psum s 3) := by
            exact le_trans hpre htel'
          have hmono3 : psum s 3 ≤ psum s ℓ := psum_mono s (by omega : 3 ≤ ℓ)
          have hnorm : (s ⟨3 - 1, by omega⟩ : ℕ) = (s ⟨2, by omega⟩ : ℕ) := by rfl
          have hsum2 : psum s 3 = psum s (3 - 1) + (s ⟨2, by omega⟩ : ℕ) := by
            rw [hnorm]
            exact hsum
          calc
            psum (Q.c (Sum.inl (RelData.iterIdx F 0 (toData F R0) q.1))) ℓ
                = psum s (3 - 1) + psum (R0.cA q.1) (ℓ - 2) := hdec
            _ ≤ psum s (3 - 1) + ((s ⟨2, by omega⟩ : ℕ) + (psum s ℓ - psum s 3)) := by
                  exact Nat.add_le_add_left hb (psum s (3 - 1))
            _ ≤ psum s ℓ := by omega
      | inr s =>
          cases s with
          | inl i =>
              -- type-2: ℓ = 3 via the strict drop; ℓ ≥ 4 via type2_psum_ge_k_lt
              by_cases h3e : ℓ = 3
              · subst ℓ
                have hps : psum (Q.c (Sum.inr (Sum.inl i))) 3 ≤ psum s 3 := by
                  have hlt : psum (Q.c (Sum.inr (Sum.inl i))) 3 < psum s 3 := by
                    simpa using (type2_psum_lt_k F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                      (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd i)
                  exact le_of_lt hlt
                exact hps
              · have hgt3 : 3 < ℓ := by omega
                have ho := type2_psum_ge_k_lt F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                  (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd hbndB i ℓ hgt3 hℓr
                exact le_of_lt ho
          | inr i =>
              have ho := type3_psum_ge_k_le F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
                (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd hbndB i ℓ hℓ hℓr
              exact ho
    · -- ℓ > r: saturation (both psums are the common weight)
      have hgt : r < ℓ := lt_of_not_ge hℓr
      have hwl := psum_le_weight (mc p) ℓ
      have hwm : weight (mdep p) (mc p) = weight r s := by
        cases p with
        | inl q => simpa using (type1_weight_eq F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
            (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd q.1 (hwtA q.1 q.2))
        | inr s => cases s with
          | inl i => simpa using (type2_weight_eq F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
              (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd i hXw)
          | inr i => simpa using (type3_weight_eq F r s 3 2 (by omega : 1 ≤ 3) hcase3 (by omega : 1 ≤ 2)
              (by omega : 2 ≤ 3 - 1) hbigv hs1q hmid R0 hbhd i hXw)
      have hpeq : weight r s = psum s ℓ := (psum_ge_depth s (le_of_lt hgt)).symm
      rw [hwm, hpeq] at hwl
      exact hwl
  exact admExpT_combine F w 3 s mdep mhdep mc ma hid horder e

end ZagierHoffmanPositiveChar
