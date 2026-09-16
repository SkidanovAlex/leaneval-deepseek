import Submission.ZagierHoffmanProof.StepL161
import Submission.ZagierHoffmanProof.StepM2
set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators
/-!
# Step L162: the type-1 member FRONT facts and its `Init` comparison (SESSION 269)

The type-1 members of the `(k,j)` CASE-1 chain have tuple
`(s₁,…,s_j) ++ (q,…,q) ++ D.cA i₀` with `k−1−j` leading `q`'s.  Hence:
  • `type1_pad0_mid` : positions `x ∈ [j, k−1)` carry the value `q = Nat.card F`;
  • `type1_pad0_front_eq` : positions `x < k−1` agree with `s`;
  • ★ `type1_Init` : `Init(member) = Init(s) ++ rest`, so either `InitLt s member`
    (when `rest ≠ []`) or `Init(s) = Init(member)` together with the entry drop
    `pad0 member (initLen member) < pad0 s (initLen s)` (the paper's Prop-2.12 type-1
    member conclusion, the `C2'`/`C3` cases of the ambient measure).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The leading `q`'s of the type-1 member: positions `[j, k−1)`. -/
lemma type1_pad0_mid (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, ∀ x : ℕ, j ≤ x → x < k - 1 →
      pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) x = Nat.card F := by
  classical
  intro D Bs Q i₀ x hjx hxk
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  have hshift := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i x hjx
  have hdepi : D.depA i = (toData F R0).depA i₀ + (k - j - 1) := by
    dsimp [i, D]
    exact RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
  have hpos : 1 ≤ (toData F R0).depA i₀ := R0.hdepA i₀
  have hxj : x - j < D.depA i := by
    rw [hdepi]
    omega
  have hlt : x - j < k - j - 1 := by omega
  have hval : ((D.cA i) ⟨x - j, hxj⟩ : ℕ) = (qExp F : ℕ) := by
    have hv := RelData.BCqIter_cA_value F (k - j - 1) (toData F R0) i₀
      ⟨x - j, by rw [← hdepi]; exact hxj⟩
    have hidx : (Fin.cast (RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀).symm
        ⟨x - j, by rw [← hdepi]; exact hxj⟩) = ⟨x - j, hxj⟩ := Fin.ext rfl
    rw [hidx] at hv
    have hcond : (x - j : ℕ) < k - j - 1 := hlt
    simp only [hcond, dif_pos] at hv
    exact congrArg (fun t : ℕ+ => (t : ℕ)) hv
  rw [hshift, pad0_of_lt (D.cA i) hxj, hval]
  rfl

/-- Positions below `k−1` of a type-1 member agree with `s`. -/
lemma type1_pad0_front_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, ∀ x : ℕ, x < k - 1 →
      pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) x = pad0 s x := by
  classical
  intro D Bs Q i₀ x hx
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  by_cases hxj : x < j - 1
  · -- front region
    have hQdep : Q.dep (Sum.inl i) = Bs.dep (Sum.inl i) + (sPrefix r s j (by omega) (by omega)).length :=
      FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) _
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    have hmdep : x < Q.dep (Sum.inl i) := by
      rw [hQdep, hlen]
      have hBs : 1 ≤ Bs.dep (Sum.inl i) := by
        have : Bs.dep (Sum.inl i) = D.depA i + 1 := by dsimp [Bs, ofBstarOver, D]
        omega
      omega
    have hfr := prependList_c_front_value F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i) x
      hmdep (by rw [hlen]; omega)
    have hrev := sPrefix_reverse_value r s j (by omega) (by omega) x (by simpa [hlen] using hxj)
    have hxr : x < r := by omega
    rw [pad0_of_lt (Q.c (Sum.inl i)) hmdep, pad0_of_lt s hxr]
    rw [hfr]
    rw [hrev]
  · -- mid region: x = j-1 or x > j-1
    by_cases hxj' : x = j - 1
    · subst hxj'
      have hQdep : Q.dep (Sum.inl i) = Bs.dep (Sum.inl i) + (sPrefix r s j (by omega) (by omega)).length :=
        FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) _
      have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
        sPrefix_length r s j (by omega) (by omega)
      have hmdep : j - 1 < Q.dep (Sum.inl i) := by
        rw [hQdep, hlen]
        have hBs : 1 ≤ Bs.dep (Sum.inl i) := by
          have : Bs.dep (Sum.inl i) = D.depA i + 1 := by dsimp [Bs, ofBstarOver, D]
          omega
        omega
      rw [pad0_of_lt (Q.c (Sum.inl i)) hmdep, pad0_of_lt s (by omega : j - 1 < r)]
      exact type1_sj_at_jm1 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i hmdep
    · have hjx : j ≤ x := by omega
      have hmid' := type1_pad0_mid F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀ x hjx hx
      rw [hmid']
      have hs := hmid ⟨x, by omega⟩ hjx hx
      rw [pad0_of_lt s (by omega : x < r)]
      exact hs.symm

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Depth of a type-1 member: `depA i₀ + (k−1)`. -/
lemma type1_dep_eq (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) =
        (toData F R0).depA i₀ + (k - 1) := by
  classical
  intro D Bs Q i₀
  have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
    sPrefix_length r s j (by omega) (by omega)
  have hQdep : Q.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) =
      Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) +
        (sPrefix r s j (by omega) (by omega)).length :=
    FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) _
  have hBsdep : Bs.dep (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)) =
      D.depA (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) + 1 := by
    dsimp [Bs, ofBstarOver, D]
  have hDdep : D.depA (RelData.iterIdx F (k - j - 1) (toData F R0) i₀) =
      (toData F R0).depA i₀ + (k - j - 1) := by
    dsimp [D]
    exact RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
  rw [hQdep, hBsdep, hDdep, hlen]
  omega

/-- The value of a type-1 member at position `k−1`: the head of the base `a`-tuple. -/
lemma type1_pad0_at_k1 (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA,
      pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) (k - 1) =
        ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) := by
  classical
  intro D Bs Q i₀
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  have hk1d : k - 1 < Q.dep (Sum.inl i) := by
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    have hQdep := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
    have hBsdep : Bs.dep (Sum.inl i) = D.depA i + 1 := by dsimp [Bs, ofBstarOver, D]
    have hDdep : D.depA i = (toData F R0).depA i₀ + (k - j - 1) := by
      dsimp [i, D]
      exact RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
    have hpos : 1 ≤ (toData F R0).depA i₀ := R0.hdepA i₀
    rw [hQdep, hBsdep, hDdep, hlen]
    omega
  have hshift := type1_pad0_shift F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i (k - 1) (by omega)
  have hkj : (k - 1) - j = k - j - 1 := by omega
  rw [hshift, hkj]
  have hdepi : D.depA i = (toData F R0).depA i₀ + (k - j - 1) := by
    dsimp [i, D]
    exact RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
  have hidx : k - j - 1 < D.depA i := by
    rw [hdepi]
    have hpos : 1 ≤ (toData F R0).depA i₀ := R0.hdepA i₀
    omega
  rw [pad0_of_lt (D.cA i) hidx]
  have hv := RelData.BCqIter_cA_value F (k - j - 1) (toData F R0) i₀
    ⟨k - j - 1, by rw [← hdepi]; exact hidx⟩
  have hidx2 : (Fin.cast (RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀).symm
      ⟨k - j - 1, by rw [← hdepi]; exact hidx⟩) = ⟨k - j - 1, hidx⟩ := Fin.ext rfl
  rw [hidx2] at hv
  have hcond : ¬ ((k - j - 1 : ℕ) < k - j - 1) := by omega
  simp only [hcond, dif_neg, not_false_eq_true] at hv
  rw [hv]
  simp only [Nat.sub_self]
  rfl

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Local copy of the generic `List.Lex` append fact (also requested from the commons). -/
private lemma lex_append_ne_nil {α : Type*} (r : α → α → Prop) (l rest : List α)
    (h : rest ≠ []) : List.Lex r l (l ++ rest) := by
  induction l with
  | nil => cases rest with
    | nil => exact absurd rfl h
    | cons b l => exact List.Lex.nil
  | cons a l ih => exact List.Lex.cons ih

/-- ★ The type-1 `Init` comparison (paper Prop 2.12's type-1 member conclusion):
either `Init(s) ≺ Init(member)`, or the two initial tuples are EQUAL and the entry at the
initial length strictly drops.  This is the `C2'`/`C3` datum of the ambient measure. -/
lemma type1_Init (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ))
    (hsj : (s ⟨j - 1, by omega⟩ : ℕ) < Nat.card F)
    (hmid : ∀ i : Fin r, (j : ℕ) ≤ (i : ℕ) → (i : ℕ) < k - 1 → (s i : ℕ) = Nat.card F)
    (hsleq : ∀ x : ℕ, x < k - 1 → pad0 s x ≤ Nat.card F)
    (R0 : BinaryRel F)
    (hbhd : ∀ j' : R0.ιB, ((R0.cB j') ⟨0, R0.hdepB j'⟩ : ℕ) = 1) :
    let D := RelData.BCqIter F (k - j - 1) (toData F R0)
    let Bs := ofBstarOver F D (s ⟨j - 1, by omega⟩) (fun e => BCqIter_valid F (k - j - 1) R0 e)
        (RelData.iterate_merge_hv F (k - j - 1) R0 (s ⟨j - 1, by omega⟩) (by omega) hbhd)
    let Q := FixedOver.prependList F Bs (sPrefix r s j (by omega) (by omega))
    ∀ i₀ : R0.ιA, ((R0.cA i₀) ⟨0, R0.hdepA i₀⟩ : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ) →
      (InitLt (Nat.card F) s (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ∨
        (initList (Nat.card F) s =
            initList (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))) ∧
          pad0 (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀)))
              (initLen (Nat.card F) (Q.c (Sum.inl (RelData.iterIdx F (k - j - 1) (toData F R0) i₀))))
            < pad0 s (initLen (Nat.card F) s))) := by
  classical
  intro D Bs Q i₀ hhead
  let i : D.ιA := RelData.iterIdx F (k - j - 1) (toData F R0) i₀
  let q : ℕ := Nat.card F
  have hk2 : 2 ≤ q := card_ge_two F
  have hdep : Q.dep (Sum.inl i) = (toData F R0).depA i₀ + (k - 1) := by
    have hlen : (sPrefix r s j (by omega) (by omega)).length = j - 1 :=
      sPrefix_length r s j (by omega) (by omega)
    have hQdep := FixedOver.prependList_dep F Bs (sPrefix r s j (by omega) (by omega)) (Sum.inl i)
    have hBsdep : Bs.dep (Sum.inl i) = D.depA i + 1 := by dsimp [Bs, ofBstarOver, D]
    have hDdep : D.depA i = (toData F R0).depA i₀ + (k - j - 1) := by
      dsimp [i, D]
      exact RelData.BCqIter_depA_at F (k - j - 1) (toData F R0) i₀
    rw [hQdep, hBsdep, hDdep, hlen]
    omega
  have hdepk : k ≤ Q.dep (Sum.inl i) := by
    rw [hdep]
    have hpos : 1 ≤ (toData F R0).depA i₀ := R0.hdepA i₀
    omega
  have hfront : ∀ x : ℕ, x < k - 1 → pad0 (Q.c (Sum.inl i)) x = pad0 s x :=
    fun x hx => type1_pad0_front_eq F r s k j hk1 hkr hj1 hjk hbig hsj hmid R0 hbhd i₀ x hx
  -- the value-list front equality
  have htake : (valueList s).take (k - 1) = (valueList (Q.c (Sum.inl i))).take (k - 1) :=
    valueList_take_eq_of_pad0_eq (Q.c (Sum.inl i)) s k hk1 hdepk hkr hfront
  -- `initList s = take (k-1)` (value list of `s`)
  have hlenS : (valueList s).length = r := valueList_length s
  have htakeleS : ∀ v ∈ (valueList s).take (k - 1), v ≤ q :=
    valueList_take_le q s (k - 1) hsleq
  have hdropS : (valueList s).drop (k - 1) =
      (s ⟨k - 1, by omega⟩ : ℕ) :: (valueList s).drop k := by
    have hlt : k - 1 < (valueList s).length := by rw [hlenS]; omega
    rw [List.drop_eq_getElem_cons hlt]
    have hk' : k - 1 + 1 = k := by omega
    rw [hk']
    congr 1
    exact valueList_getElem s (k - 1) (by omega)
  have hinitS : initList q s = (valueList s).take (k - 1) := by
    have hsplit : valueList s = (valueList s).take (k - 1) ++ (valueList s).drop (k - 1) :=
      (List.take_append_drop (k - 1) (valueList s)).symm
    have happ := initListAux_append_le q ((valueList s).take (k - 1)) ((valueList s).drop (k - 1)) htakeleS
    have hnil : initListAux q ((valueList s).drop (k - 1)) = [] := by
      rw [hdropS]
      exact initListAux_cons_gt q _ _ (by simpa [q] using hbig)
    rw [initList, hsplit, happ, hnil, List.append_nil]
    rw [List.take_append_of_le_length (by rw [List.length_take]; rw [hlenS]; omega)]
    rw [List.take_take]
    congr 1
    omega
  -- `initList member` decomposition
  have htakeleM : ∀ v ∈ (valueList (Q.c (Sum.inl i))).take (k - 1), v ≤ q := by
    apply valueList_take_le q (Q.c (Sum.inl i)) (k - 1)
    intro x hx
    rw [hfront x hx]
    exact hsleq x hx
  have hinitM : initList q (Q.c (Sum.inl i)) =
      (valueList (Q.c (Sum.inl i))).take (k - 1) ++
        initListAux q ((valueList (Q.c (Sum.inl i))).drop (k - 1)) := by
    have hsplit : valueList (Q.c (Sum.inl i)) =
        (valueList (Q.c (Sum.inl i))).take (k - 1) ++
          (valueList (Q.c (Sum.inl i))).drop (k - 1) :=
      (List.take_append_drop (k - 1) (valueList (Q.c (Sum.inl i)))).symm
    conv_lhs => rw [initList, hsplit]
    exact initListAux_append_le q _ _ htakeleM
  have hmain : initList q (Q.c (Sum.inl i)) = initList q s ++
      initListAux q ((valueList (Q.c (Sum.inl i))).drop (k - 1)) := by
    rw [hinitM, hinitS, ← htake]
  have hlenS2 : (initList q s).length = k - 1 := by
    rw [hinitS, List.length_take]
    rw [hlenS]
    omega
  set R : List ℕ := initListAux q ((valueList (Q.c (Sum.inl i))).drop (k - 1)) with hRdef
  by_cases hR : R = []
  · right
    refine ⟨?_, ?_⟩
    · rw [hmain, hR, List.append_nil]
    · have hinitMlen : (initList q (Q.c (Sum.inl i))).length = k - 1 := by
        rw [hmain, hR, List.append_nil, hlenS2]
      have hinitLenM : initLen q (Q.c (Sum.inl i)) = k - 1 := hinitMlen
      have hinitLenS : initLen q s = k - 1 := hlenS2
      rw [hinitLenM, hinitLenS]
      have hval := type1_pad0_at_k1 F r s k j hk1 hkr hj1 hjk hbig hsj R0 hbhd i₀
      rw [hval]
      have hss : pad0 s (k - 1) = (s ⟨k - 1, by omega⟩ : ℕ) := pad0_of_lt s (by omega)
      rw [hss]
      exact hhead
  · left
    rw [InitLt, hmain]
    exact lex_append_ne_nil (fun a b : ℕ => a < b) (initList q s) R hR

end ZagierHoffmanPositiveChar
