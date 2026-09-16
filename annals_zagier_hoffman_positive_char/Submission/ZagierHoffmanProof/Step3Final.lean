import Submission.ZagierHoffmanProof.Step3General
import Submission.Commons.NumberTheory.MZV.suffix_dvd_eq_pred
import Submission.Commons.Combinatorics.Nat.false_of_suffix_eq_pred
import Submission.Commons.Combinatorics.List.getElem_option_eq_of_take_eq
import Submission.Commons.Combinatorics.List.take_eq_take_iff_getElem_option
import Submission.Commons.Combinatorics.List.le_length_takeWhile_zip_of_take_eq_of_ne
import Submission.Commons.Combinatorics.List.sum_map_fst_drop_eq_sum_Icc
import Submission.Commons.Combinatorics.List.sum_map_fst_eq_sum_range

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# The endgame of Dac §5.3 Step 3

The exponent sequence `T0e w hw v : ℕ → ℕ` of a value `v ∈ 𝒯0 F w` (the `j`-th entry of the chosen
representative tuple, `0` beyond the end), together with its list-theoretic incarnations, and the
final combinatorial contradiction.
-/

namespace ZagierHoffmanPositiveChar

attribute [local instance 100] Classical.decEq

variable {F : Type*} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The exponent sequence -/

/-- The `j`-th exponent of the chosen representative tuple of `v ∈ 𝒯0 F w` (`0` beyond the end). -/
noncomputable def T0e (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) (j : ℕ) : ℕ :=
  if h : j < (T0list F w hw v).length then (T0exp F w hw v ⟨j, h⟩ : ℕ) else 0

lemma T0e_of_lt (w : ℕ) (hw : 1 ≤ w) (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    {j : ℕ} (h : j < (T0list F w hw v).length) :
    T0e w hw v j = (T0exp F w hw v ⟨j, h⟩ : ℕ) := by
  simp only [T0e]
  exact dif_pos h

lemma T0e_of_ge (w : ℕ) (hw : 1 ≤ w) (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    {j : ℕ} (h : (T0list F w hw v).length ≤ j) : T0e w hw v j = 0 := by
  simp only [T0e]
  exact dif_neg (by omega)

lemma T0e_pos (w : ℕ) (hw : 1 ≤ w) (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    {j : ℕ} (h : j < (T0list F w hw v).length) : 1 ≤ T0e w hw v j := by
  rw [T0e_of_lt w hw v h]
  exact (T0exp F w hw v ⟨j, h⟩).pos

lemma T0e_lt (w : ℕ) (hw : 1 ≤ w) (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    {j : ℕ} (h : j < (T0list F w hw v).length) : T0e w hw v j < Nat.card F := by
  rw [T0e_of_lt w hw v h, T0exp_val F w hw v]
  exact T0tuple_lt F w hw v _

lemma T0e_sum (w : ℕ) (hw : 1 ≤ w) (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ∑ j ∈ Finset.range (T0list F w hw v).length, T0e w hw v j = w := by
  have h : (∑ j : Fin (T0list F w hw v).length, T0e w hw v j)
      = (∑ j : Fin (T0list F w hw v).length, (T0exp F w hw v j : ℕ)) :=
    Finset.sum_congr rfl (fun j _ => T0e_of_lt w hw v j.isLt)
  have h2 : (∑ j : Fin (T0list F w hw v).length, T0e w hw v j) = w := by
    rw [h, T0exp_weight F w hw v]
  rwa [Fin.sum_univ_eq_sum_range] at h2

/-- The concrete form of the `j`-th entry of the list of `v`. -/
lemma T0e_getElem? (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) (j : ℕ) :
    (tupleListP F (T0exp F w hw v))[j]?
      = if h : j < (T0list F w hw v).length then
          some (T0e w hw v j, (1 : Polynomial (Ambient F))) else none := by
  rw [tupleListP_getElem?]
  by_cases h : j < (T0list F w hw v).length
  · rw [dif_pos h, dif_pos h, T0e_of_lt w hw v h]
  · rw [dif_neg h, dif_neg h]

/-! ## §2. The list incarnations of the exponent sequence -/

/-- **`tmWeight` of the dropped tail as an index-interval sum of the exponent sequence.** -/
lemma tmWeight_drop_eq_sum_Icc (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) (k : ℕ) :
    tmWeight (K := Ambient F) ((tupleListP F (T0exp F w hw v)).drop k)
      = ∑ i ∈ Finset.Icc k ((T0list F w hw v).length - 1), T0e w hw v i := by
  rw [tmWeight, Commons.Combinatorics.List.sum_map_fst_drop_eq_sum_Icc]
  rw [tupleListP_length F (T0exp F w hw v)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hir : i < (T0list F w hw v).length := by
    have h := Finset.mem_Icc.mp hi
    have hne : (T0list F w hw v).length ≠ 0 := by
      intro h0
      exact T0list_ne_nil F w hw v (List.eq_nil_of_length_eq_zero h0)
    omega
  rw [T0e_getElem?, dif_pos hir]
  rfl

/-- **The pointwise consequence of Step 3's divisibility**: if every suffix sum from `k` on is
divisible by `q - 1`, then every exponent from `k` on is `q - 1`. -/
theorem T0e_eq_pred_of_dvd (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hdvd : ∀ j, k ≤ j → j < (T0list F w hw v).length →
      (Nat.card F - 1) ∣ ∑ i ∈ Finset.Icc j ((T0list F w hw v).length - 1), T0e w hw v i) :
    ∀ j, k ≤ j → j < (T0list F w hw v).length → T0e w hw v j = Nat.card F - 1 := by
  refine Commons.NumberTheory.MZV.suffix_dvd_eq_pred (q := Nat.card F) (two_le_ambCard F)
    (s := T0e w hw v) (r := (T0list F w hw v).length) (m := k) ?_ ?_ hdvd
  · intro j hj
    exact T0e_pos w hw v hj
  · intro j hj
    have h := T0e_lt w hw v hj
    omega

/-! ## §3. The list ↔ exponent-sequence dictionary -/

/-- Agreeing prefixes give agreeing exponent sequences. -/
lemma T0e_eq_of_take_eq (w : ℕ) (hw : 1 ≤ w)
    {u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} {k : ℕ}
    (h : (tupleListP F (T0exp F w hw u)).take k
      = (tupleListP F (T0exp F w hw v)).take k) :
    ∀ j, j < k → T0e w hw u j = T0e w hw v j := by
  intro j hj
  have h1 := Commons.Combinatorics.List.getElem_option_eq_of_take_eq h j hj
  rw [T0e_getElem? w hw u j, T0e_getElem? w hw v j] at h1
  by_cases hu : j < (T0list F w hw u).length
  · by_cases hv : j < (T0list F w hw v).length
    · rw [dif_pos hu, dif_pos hv] at h1
      exact congrArg Prod.fst (Option.some.inj h1)
    · rw [dif_pos hu, dif_neg hv] at h1
      exact absurd h1 (by simp)
  · by_cases hv : j < (T0list F w hw v).length
    · rw [dif_neg hu, dif_pos hv] at h1
      exact absurd h1 (by simp)
    · rw [dif_neg hu, dif_neg hv] at h1
      rw [T0e_of_ge w hw u (by omega), T0e_of_ge w hw v (by omega)]

/-- Agreeing exponent sequences give agreeing prefixes. -/
lemma take_eq_of_T0e_eq (w : ℕ) (hw : 1 ≤ w)
    {u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} {k : ℕ}
    (h : ∀ j, j < k → T0e w hw u j = T0e w hw v j) :
    (tupleListP F (T0exp F w hw u)).take k
      = (tupleListP F (T0exp F w hw v)).take k := by
  refine (Commons.Combinatorics.List.take_eq_take_iff_getElem_option _ _ k).mpr (fun j hj => ?_)
  rw [T0e_getElem? w hw u j, T0e_getElem? w hw v j]
  by_cases hu : j < (T0list F w hw u).length
  · by_cases hv : j < (T0list F w hw v).length
    · rw [dif_pos hu, dif_pos hv, h j hj]
    · rw [dif_pos hu, dif_neg hv]
      exact absurd (h j hj) (by
        rw [T0e_of_ge w hw v (by omega)]
        exact ne_of_gt (T0e_pos w hw u hu))
  · by_cases hv : j < (T0list F w hw v).length
    · rw [dif_pos hv, dif_neg hu]
      exact absurd (h j hj).symm (by
        rw [T0e_of_ge w hw u (by omega)]
        exact ne_of_gt (T0e_pos w hw v hv))
    · rw [dif_neg hu, dif_neg hv]

/-! ## §4. The final contradiction -/

/-- **Dac §5.3 Step 3, endgame**: two distinct tuples of `𝒯0 F w` whose exponent sequences agree up
to `K` but not up to `K+1`, and whose entries from `K` on are all `q - 1`, are impossible. -/
theorem false_of_T0e {w : ℕ} (hw : 1 ≤ w) (hq : 2 ≤ Nat.card F)
    (u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) (K : ℕ)
    (hagree : ∀ l, l < K → T0e w hw u l = T0e w hw v l)
    (hnotagree : ¬ ∀ l, l < K + 1 → T0e w hw u l = T0e w hw v l)
    (hdivu : ∀ j, K < j → j < (T0list F w hw u).length → T0e w hw u j = Nat.card F - 1)
    (hdivv : ∀ j, K < j → j < (T0list F w hw v).length → T0e w hw v j = Nat.card F - 1) :
    False :=
  Commons.Combinatorics.Nat.false_of_suffix_eq_pred (q := Nat.card F) (w := w) (K := K)
    (two_le_ambCard F) (r₁ := (T0list F w hw u).length) (r₂ := (T0list F w hw v).length)
    (fun j hj => T0e_pos w hw u hj) (fun j hj => T0e_pos w hw v hj)
    (fun j hj => T0e_lt w hw u hj) (fun j hj => T0e_lt w hw v hj)
    (fun j hj => T0e_of_ge w hw u hj) (fun j hj => T0e_of_ge w hw v hj)
    (T0e_sum w hw u) (T0e_sum w hw v) hagree hnotagree hdivu hdivv

/-! ## §5. The maximal agreement length and its consequences -/

/-- The list of exponents attached to a value `v` (its chosen representative tuple). -/
noncomputable def T0L (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    List (ℕ × Polynomial (Ambient F)) :=
  tupleListP F (T0exp F w hw v)

lemma T0L_mem_T0S (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : T0L w hw v ∈ T0S F w hw :=
  Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩

/-- The list of exponents determines the value. -/
lemma T0L_injective (w : ℕ) (hw : 1 ≤ w) {u v : {x : RatFunc.CompletionAtInfty F //
    x ∈ 𝒯0 F w}} (h : T0L w hw u = T0L w hw v) : u = v :=
  T0exp_listP_injective F hw h

/-- The agreement length of the exponent sequences of `u` and `v`. -/
noncomputable def agreeLen (w : ℕ) (hw : 1 ≤ w)
    (u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : ℕ :=
  Nat.findGreatest (fun k => ∀ l, l < k → T0e w hw u l = T0e w hw v l)
    (max (T0list F w hw u).length (T0list F w hw v).length + 1)

lemma agreeLen_le (w : ℕ) (hw : 1 ≤ w)
    (u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    agreeLen w hw u v
      ≤ max (T0list F w hw u).length (T0list F w hw v).length + 1 :=
  Nat.findGreatest_le _

lemma agreeLen_spec (w : ℕ) (hw : 1 ≤ w)
    (u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ∀ l, l < agreeLen w hw u v → T0e w hw u l = T0e w hw v l := by
  rw [agreeLen]
  exact Nat.findGreatest_spec (P := fun k => ∀ l, l < k → T0e w hw u l = T0e w hw v l)
    (Nat.zero_le _) (fun l hl => absurd hl (Nat.not_lt_zero l))

lemma le_agreeLen (w : ℕ) (hw : 1 ≤ w)
    {u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} {k : ℕ}
    (h : ∀ l, l < k → T0e w hw u l = T0e w hw v l)
    (hk : k ≤ max (T0list F w hw u).length (T0list F w hw v).length + 1) :
    k ≤ agreeLen w hw u v :=
  Nat.le_findGreatest hk h

lemma agreeLen_comm (w : ℕ) (hw : 1 ≤ w)
    (u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    agreeLen w hw u v = agreeLen w hw v u := by
  refine le_antisymm ?_ ?_
  · have hk : agreeLen w hw u v
        ≤ max (T0list F w hw v).length (T0list F w hw u).length + 1 := by
      rw [max_comm]
      exact agreeLen_le w hw u v
    exact le_agreeLen w hw (u := v) (v := u)
      (fun l hl => (agreeLen_spec w hw u v l hl).symm) hk
  · have hk : agreeLen w hw v u
        ≤ max (T0list F w hw u).length (T0list F w hw v).length + 1 := by
      rw [max_comm]
      exact agreeLen_le w hw v u
    exact le_agreeLen w hw (u := u) (v := v)
      (fun l hl => (agreeLen_spec w hw v u l hl).symm) hk

/-- The maximal agreement length over the distinct pairs of `T`. -/
noncomputable def maxAgree (w : ℕ) (hw : 1 ≤ w)
    (T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : ℕ :=
  ((T.product T).filter (fun p => p.1 ≠ p.2)).sup (fun p => agreeLen w hw p.1 p.2)

lemma maxAgree_eq (w : ℕ) (hw : 1 ≤ w)
    (T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    maxAgree w hw T = ((T.product T).filter (fun p => p.1 ≠ p.2)).sup
      (fun p => agreeLen w hw p.1 p.2) := rfl

/-- The listing of the exponent sequences of the elements of `T`. -/
lemma maxAgree_le_of_mem (w : ℕ) (hw : 1 ≤ w)
    {T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    {x u : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} (hx : x ∈ T) (hu : u ∈ T)
    (hxu : x ≠ u) : agreeLen w hw x u ≤ maxAgree w hw T := by
  have hmem : (x, u) ∈ (T.product T).filter (fun p : {x : RatFunc.CompletionAtInfty F //
      x ∈ 𝒯0 F w} × {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} => p.1 ≠ p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hu⟩, hxu⟩
  rw [maxAgree_eq]
  exact Finset.le_sup (f := fun p : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} ×
    {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} => agreeLen w hw p.1 p.2) hmem

/-- **The maximal agreement length is attained.** -/
theorem exists_pair_maxAgree (w : ℕ) (hw : 1 ≤ w)
    {T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} (hT : 2 ≤ T.card) :
    ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ maxAgree w hw T = agreeLen w hw u v := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  have hne : ((T.product T).filter (fun p : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} ×
      {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} => p.1 ≠ p.2)).Nonempty :=
    ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩
  obtain ⟨p, hp, hpK⟩ := Finset.exists_mem_eq_sup _ hne
    (fun p : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} ×
      {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} => agreeLen w hw p.1 p.2)
  have hp2 := (Finset.mem_filter.mp hp).2
  obtain ⟨hpT1, hpT2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  refine ⟨p.1, hpT1, p.2, hpT2, hp2, ?_⟩
  rw [maxAgree_eq]
  exact hpK

/-- A helper: if the exponent sequences of `x` and `u` agree below `k`, then either `x = u` or
`k` is bounded by any number dominating the agreement lengths. -/
lemma eq_or_le_of_agree (w : ℕ) (hw : 1 ≤ w)
    {x u : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} {k K : ℕ}
    (hK : agreeLen w hw x u ≤ K)
    (h : ∀ l, l < k → T0e w hw x l = T0e w hw u l) : x = u ∨ k ≤ K := by
  by_cases hk : k ≤ max (T0list F w hw x).length (T0list F w hw u).length + 1
  · exact Or.inr (le_trans (le_agreeLen w hw h hk) hK)
  · left
    have hle : max (T0list F w hw x).length (T0list F w hw u).length + 1 ≤ k := by omega
    have htake : (T0L w hw x).take (max (T0list F w hw x).length
          (T0list F w hw u).length + 1)
        = (T0L w hw u).take (max (T0list F w hw x).length
          (T0list F w hw u).length + 1) :=
      take_eq_of_T0e_eq w hw (fun l hl => h l (lt_of_lt_of_le hl hle))
    have h1 : (T0L w hw x).take (max (T0list F w hw x).length
        (T0list F w hw u).length + 1) = T0L w hw x :=
      List.take_of_length_le (by
        rw [T0L, tupleListP_length]
        omega)
    have h2 : (T0L w hw u).take (max (T0list F w hw x).length
        (T0list F w hw u).length + 1) = T0L w hw u :=
      List.take_of_length_le (by
        rw [T0L, tupleListP_length]
        omega)
    exact T0L_injective w hw (by rw [← h1, ← h2]; exact htake)

/-- **Agreement below the maximal agreement length.** -/
lemma T0e_eq_of_maxAgree (w : ℕ) (hw : 1 ≤ w)
    {T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    {u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    (hK : maxAgree w hw T = agreeLen w hw u v) :
    ∀ l, l < maxAgree w hw T → T0e w hw u l = T0e w hw v l := by
  intro l hl
  rw [hK] at hl
  exact agreeLen_spec w hw u v l hl

/-- **Disagreement at the next level.** -/
lemma not_T0e_eq_succ_of_maxAgree (w : ℕ) (hw : 1 ≤ w)
    {T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    {u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} (hu : u ∈ T) (hv : v ∈ T)
    (huv : u ≠ v) (hK : maxAgree w hw T = agreeLen w hw u v) :
    ¬ ∀ l, l < maxAgree w hw T + 1 → T0e w hw u l = T0e w hw v l := by
  intro hall
  rcases eq_or_le_of_agree w hw (x := u) (u := v)
    (le_of_eq hK.symm) (fun l hl => hall l hl) with h | h
  · exact huv h
  · omega

/-- **Uniqueness of the extension of the maximal agreement prefix** (the `huniq` hypothesis of
`dvd_pred_weight_MZVD` at level `maxAgree + 1`). -/
lemma unique_take_of_maxAgree (w : ℕ) (hw : 1 ≤ w)
    {T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    {u v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} (hu : u ∈ T) (hv : v ∈ T)
    (huv : u ≠ v) (hK : maxAgree w hw T = agreeLen w hw u v) :
    ∀ x ∈ T, (T0L w hw x).take (maxAgree w hw T + 1) = (T0L w hw u).take (maxAgree w hw T + 1)
      → x = u := by
  intro x hx htake
  by_cases hxu : x = u
  · exact hxu
  · rcases eq_or_le_of_agree w hw (x := x) (u := u)
      (maxAgree_le_of_mem w hw hx hu hxu)
      (fun l hl => T0e_eq_of_take_eq w hw htake l hl) with h | h
    · exact absurd h hxu
    · omega

/-! ## §6. The datum of a support, and the divisibility at the maximal agreement -/

/-- The datum of a support `T`: the `MZVD` of the image of `T` under `T0L`. -/
noncomputable def restrictS (w : ℕ) (hw : 1 ≤ w)
    (T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    Finset (List (ℕ × Polynomial (Ambient F))) :=
  T.image (fun v => T0L w hw v)

lemma mem_restrictS {w : ℕ} {hw : 1 ≤ w}
    {T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    {s : List (ℕ × Polynomial (Ambient F))} :
    s ∈ restrictS w hw T ↔ ∃ v ∈ T, T0L w hw v = s := by
  simp only [restrictS, Finset.mem_image]

/-- The `MZVD` datum of a support. -/
noncomputable def restrictMZVD (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : MZVD F w where
  S := restrictS w hw T
  two := by
    intro s hs x hx
    obtain ⟨v, hv, rfl⟩ := (mem_restrictS (w := w) (hw := hw)).mp hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    exact T0S_get_two F (T0L_mem_T0S w hw v) j
  pos := by
    intro s hs x hx
    obtain ⟨v, hv, rfl⟩ := (mem_restrictS (w := w) (hw := hw)).mp hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    exact T0S_get_pos F (T0L_mem_T0S w hw v) j
  le := by
    intro s hs x hx
    obtain ⟨v, hv, rfl⟩ := (mem_restrictS (w := w) (hw := hw)).mp hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    exact T0S_get_le F (T0L_mem_T0S w hw v) j
  weight := by
    intro s hs
    obtain ⟨v, hv, rfl⟩ := (mem_restrictS (w := w) (hw := hw)).mp hs
    exact T0S_weight F (T0L_mem_T0S w hw v)

lemma restrictMZVD_S (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    (restrictMZVD w hw T).S = restrictS w hw T := rfl

/-- **Monotonicity of the uniqueness of extensions**: uniqueness at level `k` implies uniqueness at
every level `j ≥ k`. -/
lemma unique_take_mono {w : ℕ} {hw : 1 ≤ w}
    {T : Finset {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    {u : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} {k : ℕ}
    (h : ∀ x ∈ T, (T0L w hw x).take k = (T0L w hw u).take k → x = u) {j : ℕ} (hj : k ≤ j) :
    ∀ x ∈ T, (T0L w hw x).take j = (T0L w hw u).take j → x = u := by
  intro x hx hxj
  have h1 : (T0L w hw x).take k = ((T0L w hw x).take j).take k := by
    rw [List.take_take, Nat.min_eq_left hj]
  have h2 : (T0L w hw u).take k = ((T0L w hw u).take j).take k := by
    rw [List.take_take, Nat.min_eq_left hj]
  exact h x hx (by rw [h1, h2, hxj])

/-! ## §7. From the divisibility input to the exponent sequence -/

/-- **The divisibility at the maximal agreement level.**  Given the divisibility input of Dac's
Step 3 at every level, the exponent sequence of `v` is `q - 1` beyond every such level. -/
theorem T0e_eq_pred_of_dvd_all (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}} {k : ℕ}
    (hdvd : ∀ j, k ≤ j → j < (T0list F w hw v).length →
      (Nat.card F - 1) ∣ w - tmWeight (K := Ambient F)
        ((tupleListP F (T0exp F w hw v)).take j)) :
    ∀ j, k ≤ j → j < (T0list F w hw v).length → T0e w hw v j = Nat.card F - 1 := by
  have hwt : tmWeight (K := Ambient F) (tupleListP F (T0exp F w hw v)) = w :=
    T0S_weight F (T0L_mem_T0S w hw v)
  have hdvd' : ∀ j, k ≤ j → j < (T0list F w hw v).length →
      (Nat.card F - 1) ∣ ∑ i ∈ Finset.Icc j ((T0list F w hw v).length - 1), T0e w hw v i := by
    intro j hj hjr
    rw [← tmWeight_drop_eq_sum_Icc w hw v j]
    have h1 := tmWeight_take_add_drop (K := Ambient F) (tupleListP F (T0exp F w hw v)) j
    have h2 : w - tmWeight (K := Ambient F) ((tupleListP F (T0exp F w hw v)).take j)
        = tmWeight (K := Ambient F) ((tupleListP F (T0exp F w hw v)).drop j) := by
      omega
    rw [← h2]
    exact hdvd j hj hjr
  intro j hj
  exact T0e_eq_pred_of_dvd w hw v (k := k) hdvd' j hj

end ZagierHoffmanPositiveChar
