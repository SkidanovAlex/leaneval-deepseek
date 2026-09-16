import Submission.ZagierHoffmanProof.StepL177
import Submission.ZagierHoffmanProof.StepL172
import Submission.ZagierHoffmanProof.StepL171

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L178: the CHAIN TIE FACTS — the `Init`-data of the chain members (roadmap item (3)(ii))

The `AdmExpTie` composition (`admExpTie_combine`, StepL177) needs, for each member `m` of a
chain at level `j` with `psum m Λ = psum s Λ`, the `Init`-data `initVal s ≤ initVal m`
(plus, in the C3 case, the entry comparison).  This module supplies:
  • ★ `initData_of_or` — the generic extractor from the shape the chains actually prove:
      `InitLt q s m ∨ (initList q s = initList q m ∧ pad0 m (initLen m) < pad0 s (initLen s))`
    ⟹ `initVal s ≤ initVal m` AND (`initVal s = initVal m` ⟹ the strict entry drop).
    (No injectivity of `padCode` is needed: the strict-lex branch makes the second premise
    vacuous, the equal-`Init` branch carries the entry data directly.)
  • ★★ `maink_g5_aSide_initData` — the G5 a-side family (`maink_g5_aSide_Init`, StepL171);
  • ★ `maink_case1_type1_initData` — the generic `(k,j)` chain's TYPE-1 family
    (`type1_Init`, StepL162) — the two families whose `Init`-data the paper's (α) argument
    gives as a `≺`-or-entry-drop disjunction.
The remaining families (type-2 / type-3 / the b-sides) are reductions of the same shape
(type-3: `InitLt` only; type-2: `Init(m) = Init(s)` or an extension, via the member's
explicit prepended prefix) — see PLAN SESSION 271's roadmap.
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★ The `Init`-data extractor: the chains' `InitLt ∨ (equal ∧ entry drop)` disjunction
yields the `initVal`-comparison and, in the equal case, the C3 entry comparison. -/
lemma initData_of_or (q w : ℕ) {r r' : ℕ} (s : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (hs : weight r s = w) (hm : weight r' m = w)
    (h : InitLt q s m ∨ (initList q s = initList q m ∧
        pad0 m (initLen q m) < pad0 s (initLen q s))) :
    initVal q w s ≤ initVal q w m ∧
      (initVal q w s = initVal q w m →
        pad0 m (initLen q m) < pad0 s (initLen q s)) := by
  rcases h with hlex | ⟨heqi, hdrop⟩
  · have hlt := initVal_lex_lt q w s hs m hm hlex
    exact ⟨le_of_lt hlt, fun hcon => absurd hcon (ne_of_lt hlt)⟩
  · refine ⟨?_, fun _ => hdrop⟩
    have : initVal q w s = initVal q w m := by
      dsimp [initVal]
      rw [heqi]
    omega

/-- ★ The `InitLt` case alone (type-3 families of every chain). -/
lemma initData_of_initLt (q w : ℕ) {r r' : ℕ} (s : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (hs : weight r s = w) (hm : weight r' m = w) (h : InitLt q s m) :
    initVal q w s ≤ initVal q w m ∧
      (initVal q w s = initVal q w m →
        pad0 m (initLen q m) < pad0 s (initLen q s)) :=
  initData_of_or q w s m hs hm (Or.inl h)

/-- ★★ G5 a-side `Init`-data (`maink_g5_aSide_Init`, StepL171). -/
theorem maink_g5_aSide_initData (r : ℕ) (s : Fin r → ℕ+) (k : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hallq : ∀ x : ℕ, x < k - 1 → pad0 s x = Nat.card F)
    (R0 : BinaryRel F) (u : R0.ιA)
    (hhead : ∀ i : R0.ιA, i ≠ u →
      ((R0.cA i) ⟨0, R0.hdepA i⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hwtA : ∀ i : R0.ιA, i ≠ u →
      weight (R0.depA i) (R0.cA i) = psum s r - psum s (k - 1))
    (w : ℕ) (hw : weight r s = w) :
    let D := RelData.BCqIter F (k - 1) (toData F R0)
    ∀ i : D.ιA, i ≠ RelData.iterIdx F (k - 1) (toData F R0) u →
      initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (D.cA i) ∧
        (initVal (Nat.card F) w s = initVal (Nat.card F) w (D.cA i) →
          pad0 (D.cA i) (initLen (Nat.card F) (D.cA i))
            < pad0 s (initLen (Nat.card F) s)) := by
  classical
  intro D i hi
  have hinit := maink_g5_aSide_Init F r s k hk1 hkr hbig hallq R0 u hhead i hi
  have hmdw : weight (D.depA i) (D.cA i) = w :=
    (maink_g5_aSide_weight F r s k hk1 hkr hallq R0 u hwtA i hi).trans hw
  exact initData_of_or (Nat.card F) w s (D.cA i) hw hmdw hinit

/-- ★ The generic `(k,j)` chain's TYPE-1 `Init`-data (`type1_Init`, StepL162, combined with
`type1_weight_eq`, StepL32). -/
theorem maink_case1_type1_initData (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hwtA : ∀ i₀ : R0.ιA, weight (R0.depA i₀) (R0.cA i₀) = psum s r - psum s (k - 1))
    (w : ℕ) (hw : weight r s = w) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ) →
      initVal (Nat.card F) w s
          ≤ initVal (Nat.card F) w (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ∧
        (initVal (Nat.card F) w s
            = initVal (Nat.card F) w
                (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) →
          pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
              (initLen (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))))
            < pad0 s (initLen (Nat.card F) s)) := by
  classical
  intro D Bs Q i₀ hhead
  have hinit := type1_Init F r s k j hk1 hkr hj1 hjk hbig hsj hmid hsleq R0 hbhd i₀ hhead
  have hmdw : weight (Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
      (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) = w :=
    (type1_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ (hwtA i₀)).trans hw
  exact initData_of_or (Nat.card F) w s _ hw hmdw hinit

/-- ★ The generic `(k,j)` chain's TYPE-3 `Init`-data (`type3_Init_gt`, StepL33, with
`type3_weight_eq`, StepL32). -/
theorem maink_case1_type3_initData (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1)
    (hXw : ∀ j' : R0.ιB, weight (R0.depB j' - 1) (expTail (R0.cB j')) =
      psum s r - psum s (k - 1) - 1)
    (w : ℕ) (hw : weight r s = w) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i : D.ιB,
      initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (Q.c (Sum.inr (Sum.inr i))) ∧
        (initVal (Nat.card F) w s = initVal (Nat.card F) w (Q.c (Sum.inr (Sum.inr i))) →
          pad0 (Q.c (Sum.inr (Sum.inr i))) (initLen (Nat.card F) (Q.c (Sum.inr (Sum.inr i))))
            < pad0 s (initLen (Nat.card F) s)) := by
  classical
  intro D Bs Q i
  have hinit := type3_Init_gt F r s k j hk1 hkr hj1 hjk hbig hsj hsleq R0 hbhd i
  have hmdw : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w :=
    (type3_weight_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i hXw).trans hw
  exact initData_of_initLt (Nat.card F) w s _ hw hmdw hinit

/-- ★ The CASE-2 chain's TYPE-3 `Init`-data (`prop213_step1`'s third conjunct, StepL44). -/
theorem maink_case2_type3_initData (k : ℕ) (s : Fin k → ℕ+) (j : ℕ) (hk1 : 1 ≤ k) (hj1 : 1 ≤ j)
    (hjk : j ≤ k - 1) (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hqend : ∀ i : Fin k, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (w : ℕ) (hw : weight k s = w) :
    let D := RelData.BCqIter F (k - j - 1) (toData F (r1Rel F))
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩)
        (fun e => BCqIter_valid F (k - j - 1) (r1Rel F) e)
        (RelData.iterate_merge_hv F (k - j - 1) (r1Rel F) (s ⟨j - 1, by omega⟩) (by omega)
          (r1Rel_hbhd F))
    let Q := FixedOver.prependList F Bs (sPrefix k s j (by omega) (by omega))
    ∀ i : D.ιB,
      initVal (Nat.card F) w s ≤ initVal (Nat.card F) w (Q.c (Sum.inr (Sum.inr i))) ∧
        (initVal (Nat.card F) w s = initVal (Nat.card F) w (Q.c (Sum.inr (Sum.inr i))) →
          pad0 (Q.c (Sum.inr (Sum.inr i))) (initLen (Nat.card F) (Q.c (Sum.inr (Sum.inr i))))
            < pad0 s (initLen (Nat.card F) s)) := by
  classical
  intro D Bs Q i
  have hT := prop213_step1 F k s j hk1 hj1 hjk hsj hqend hsleq
  obtain ⟨-, -, hT3⟩ := hT
  have hmdw : weight (Q.dep (Sum.inr (Sum.inr i))) (Q.c (Sum.inr (Sum.inr i))) = w :=
    (hT3 i).1.trans hw
  exact initData_of_initLt (Nat.card F) w s _ hw hmdw (hT3 i).2.2

end ZagierHoffmanPositiveChar
