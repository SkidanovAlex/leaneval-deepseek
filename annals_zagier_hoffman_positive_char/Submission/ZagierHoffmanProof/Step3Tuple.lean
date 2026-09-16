import Submission.ZagierHoffmanProof.Step3Final
import Submission.Commons.NumberTheory.MZV.suffix_dvd_eq_pred
import Submission.Commons.Combinatorics.Nat.false_of_suffix_eq_pred

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# The endgame of Dac §5.3 Step 3, at the level of tuples

`Step3Final.lean` runs the endgame for the *values* of `𝒯0 F w` (via the chosen representatives
`T0exp`).  For the induction one needs it for an arbitrary injective family of tuples; this file
provides the tuple-level version.
-/

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F] [DecidableEq (RatFunc F)]

attribute [local instance 100] Classical.decEq

/-! ## §1. The exponent sequence of a tuple -/

/-- The `j`-th entry of a tuple of positive exponents (`0` beyond the end). -/
noncomputable def tupE {r : ℕ} (𝔰 : Fin r → ℕ+) (j : ℕ) : ℕ :=
  if h : j < r then (𝔰 ⟨j, h⟩ : ℕ) else 0

lemma tupE_of_lt {r : ℕ} (𝔰 : Fin r → ℕ+) {j : ℕ} (h : j < r) :
    tupE 𝔰 j = (𝔰 ⟨j, h⟩ : ℕ) := by
  simp only [tupE]
  exact dif_pos h

lemma tupE_of_ge {r : ℕ} (𝔰 : Fin r → ℕ+) {j : ℕ} (h : r ≤ j) : tupE 𝔰 j = 0 := by
  simp only [tupE]
  exact dif_neg (by omega)

lemma tupE_pos {r : ℕ} (𝔰 : Fin r → ℕ+) {j : ℕ} (h : j < r) : 1 ≤ tupE 𝔰 j := by
  rw [tupE_of_lt 𝔰 h]
  exact (𝔰 ⟨j, h⟩).pos

lemma tupE_sum {r : ℕ} (𝔰 : Fin r → ℕ+) :
    ∑ j ∈ Finset.range r, tupE 𝔰 j = ∑ j : Fin r, (𝔰 j : ℕ) := by
  have h : (∑ j : Fin r, tupE 𝔰 j) = ∑ j : Fin r, (𝔰 j : ℕ) :=
    Finset.sum_congr rfl (fun j _ => tupE_of_lt 𝔰 j.isLt)
  rwa [Fin.sum_univ_eq_sum_range] at h

/-- The concrete form of the `j`-th entry of the list of a tuple. -/
lemma tupleListP_getElem?_tupE {r : ℕ} (𝔰 : Fin r → ℕ+) (j : ℕ) :
    (tupleListP F 𝔰)[j]? = if h : j < r then
      some (tupE 𝔰 j, (1 : Polynomial (Ambient F))) else none := by
  rw [tupleListP_getElem?]
  by_cases h : j < r
  · rw [dif_pos h, dif_pos h, tupE_of_lt 𝔰 h]
  · rw [dif_neg h, dif_neg h]

/-! ## §2. The list ↔ exponent-sequence dictionary -/

lemma tupE_eq_of_take_eq {r₁ r₂ k : ℕ} {𝔰₁ : Fin r₁ → ℕ+} {𝔰₂ : Fin r₂ → ℕ+}
    (h : (tupleListP F 𝔰₁).take k = (tupleListP F 𝔰₂).take k) :
    ∀ j, j < k → tupE 𝔰₁ j = tupE 𝔰₂ j := by
  intro j hj
  have h1 := Commons.Combinatorics.List.getElem_option_eq_of_take_eq h j hj
  rw [tupleListP_getElem?_tupE 𝔰₁ j, tupleListP_getElem?_tupE 𝔰₂ j] at h1
  by_cases h1a : j < r₁
  · by_cases h2a : j < r₂
    · rw [dif_pos h1a, dif_pos h2a] at h1
      exact congrArg Prod.fst (Option.some.inj h1)
    · rw [dif_pos h1a, dif_neg h2a] at h1
      exact absurd h1 (by simp)
  · by_cases h2a : j < r₂
    · rw [dif_neg h1a, dif_pos h2a] at h1
      exact absurd h1 (by simp)
    · rw [dif_neg h1a, dif_neg h2a] at h1
      rw [tupE_of_ge 𝔰₁ (by omega), tupE_of_ge 𝔰₂ (by omega)]

lemma take_eq_of_tupE_eq {r₁ r₂ k : ℕ} {𝔰₁ : Fin r₁ → ℕ+} {𝔰₂ : Fin r₂ → ℕ+}
    (h : ∀ j, j < k → tupE 𝔰₁ j = tupE 𝔰₂ j) :
    (tupleListP F 𝔰₁).take k = (tupleListP F 𝔰₂).take k := by
  refine (Commons.Combinatorics.List.take_eq_take_iff_getElem_option _ _ k).mpr (fun j hj => ?_)
  rw [tupleListP_getElem?_tupE 𝔰₁ j, tupleListP_getElem?_tupE 𝔰₂ j]
  by_cases h1a : j < r₁
  · by_cases h2a : j < r₂
    · rw [dif_pos h1a, dif_pos h2a, h j hj]
    · rw [dif_pos h1a, dif_neg h2a]
      exact absurd (h j hj) (by
        rw [tupE_of_ge 𝔰₂ (by omega)]
        exact ne_of_gt (tupE_pos 𝔰₁ h1a))
  · by_cases h2a : j < r₂
    · rw [dif_neg h1a, dif_pos h2a]
      exact absurd (h j hj).symm (by
        rw [tupE_of_ge 𝔰₁ (by omega)]
        exact ne_of_gt (tupE_pos 𝔰₂ h2a))
    · rw [dif_neg h1a, dif_neg h2a]

/-! ## §3. `tmWeight` of a dropped tail, and the divisibility conversion -/

lemma tmWeight_drop_tupleListP {r : ℕ} (𝔰 : Fin r → ℕ+) (k : ℕ) :
    tmWeight (K := Ambient F) ((tupleListP F 𝔰).drop k)
      = ∑ i ∈ Finset.Icc k (r - 1), tupE 𝔰 i := by
  rw [tmWeight, Commons.Combinatorics.List.sum_map_fst_drop_eq_sum_Icc,
    tupleListP_length F 𝔰]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [tupleListP_getElem?_tupE 𝔰 i]
  by_cases hir : i < r
  · rw [dif_pos hir]
    rfl
  · rw [dif_neg hir, tupE_of_ge 𝔰 (by omega)]
    rfl

/-- **The pointwise consequence of Step 3's divisibility** for an arbitrary sequence. -/
theorem eq_pred_of_dvd {q r : ℕ} {e : ℕ → ℕ} {k : ℕ} (hq : 2 ≤ q)
    (hpos : ∀ j, j < r → 1 ≤ e j) (hlt : ∀ j, j < r → e j < q)
    (hdvd : ∀ j, k ≤ j → j < r → (q - 1) ∣ ∑ i ∈ Finset.Icc j (r - 1), e i) :
    ∀ j, k ≤ j → j < r → e j = q - 1 :=
  Commons.NumberTheory.MZV.suffix_dvd_eq_pred hq hpos (fun j hj => by have := hlt j hj; omega) hdvd

/-! ## §4. The final contradiction, at the level of tuples -/

/-- **Dac §5.3 Step 3, endgame (tuple form)**: two tuples of weight `w` with entries `< q` whose
exponent sequences agree below `K` but not below `K + 1`, and whose entries beyond `K` are all
`q - 1`, are impossible. -/
theorem false_of_tupE {q w K : ℕ} (hq : 2 ≤ q) {r₁ r₂ : ℕ} {𝔰₁ : Fin r₁ → ℕ+}
    {𝔰₂ : Fin r₂ → ℕ+}
    (hlt₁ : ∀ j, (𝔰₁ j : ℕ) < q) (hlt₂ : ∀ j, (𝔰₂ j : ℕ) < q)
    (hwt₁ : ∑ j : Fin r₁, (𝔰₁ j : ℕ) = w) (hwt₂ : ∑ j : Fin r₂, (𝔰₂ j : ℕ) = w)
    (hagree : ∀ l, l < K → tupE 𝔰₁ l = tupE 𝔰₂ l)
    (hnotagree : ¬ ∀ l, l < K + 1 → tupE 𝔰₁ l = tupE 𝔰₂ l)
    (hdiv₁ : ∀ j, K < j → j < r₁ → tupE 𝔰₁ j = q - 1)
    (hdiv₂ : ∀ j, K < j → j < r₂ → tupE 𝔰₂ j = q - 1) : False :=
  Commons.Combinatorics.Nat.false_of_suffix_eq_pred (q := q) (w := w) (K := K) hq
    (r₁ := r₁) (r₂ := r₂)
    (fun j hj => tupE_pos 𝔰₁ hj) (fun j hj => tupE_pos 𝔰₂ hj)
    (fun j hj => by have := hlt₁ ⟨j, hj⟩; rw [tupE_of_lt 𝔰₁ hj]; exact_mod_cast this)
    (fun j hj => by have := hlt₂ ⟨j, hj⟩; rw [tupE_of_lt 𝔰₂ hj]; exact_mod_cast this)
    (fun j hj => tupE_of_ge 𝔰₁ hj) (fun j hj => tupE_of_ge 𝔰₂ hj)
    (by rw [tupE_sum]; exact hwt₁) (by rw [tupE_sum]; exact hwt₂)
    hagree hnotagree hdiv₁ hdiv₂

/-! ## §5. The maximal agreement length of a tuple family -/

section MaxPref

variable {ι : Type*} [DecidableEq ι]

/-- The agreement length of the exponent sequences of two tuples. -/
noncomputable def tupAgree {r₁ r₂ : ℕ} (𝔰₁ : Fin r₁ → ℕ+) (𝔰₂ : Fin r₂ → ℕ+) : ℕ :=
  Nat.findGreatest (fun k => ∀ l, l < k → tupE 𝔰₁ l = tupE 𝔰₂ l) (max r₁ r₂ + 1)

lemma tupAgree_le {r₁ r₂ : ℕ} (𝔰₁ : Fin r₁ → ℕ+) (𝔰₂ : Fin r₂ → ℕ+) :
    tupAgree 𝔰₁ 𝔰₂ ≤ max r₁ r₂ + 1 := Nat.findGreatest_le _

lemma tupAgree_spec {r₁ r₂ : ℕ} (𝔰₁ : Fin r₁ → ℕ+) (𝔰₂ : Fin r₂ → ℕ+) :
    ∀ l, l < tupAgree 𝔰₁ 𝔰₂ → tupE 𝔰₁ l = tupE 𝔰₂ l := by
  rw [tupAgree]
  exact Nat.findGreatest_spec (P := fun k => ∀ l, l < k → tupE 𝔰₁ l = tupE 𝔰₂ l)
    (Nat.zero_le _) (fun l hl => absurd hl (Nat.not_lt_zero l))

lemma le_tupAgree {r₁ r₂ k : ℕ} {𝔰₁ : Fin r₁ → ℕ+} {𝔰₂ : Fin r₂ → ℕ+}
    (h : ∀ l, l < k → tupE 𝔰₁ l = tupE 𝔰₂ l) (hk : k ≤ max r₁ r₂ + 1) :
    k ≤ tupAgree 𝔰₁ 𝔰₂ :=
  Nat.le_findGreatest hk h

/-- **A tuple agrees with another below any level it agrees with** — or the two lists coincide. -/
lemma eq_or_le_of_tupAgree {r₁ r₂ k K : ℕ} {𝔰₁ : Fin r₁ → ℕ+} {𝔰₂ : Fin r₂ → ℕ+}
    (hK : tupAgree 𝔰₁ 𝔰₂ ≤ K) (h : ∀ l, l < k → tupE 𝔰₁ l = tupE 𝔰₂ l) :
    tupleListP F 𝔰₁ = tupleListP F 𝔰₂ ∨ k ≤ K := by
  by_cases hk : k ≤ max r₁ r₂ + 1
  · exact Or.inr (le_trans (le_tupAgree h hk) hK)
  · left
    have hle : max r₁ r₂ + 1 ≤ k := by omega
    have htake : (tupleListP F 𝔰₁).take (max r₁ r₂ + 1)
        = (tupleListP F 𝔰₂).take (max r₁ r₂ + 1) :=
      take_eq_of_tupE_eq (fun l hl => h l (lt_of_lt_of_le hl hle))
    rw [List.take_of_length_le (by rw [tupleListP_length]; omega),
      List.take_of_length_le (by rw [tupleListP_length]; omega)] at htake
    exact htake

/-- The maximal agreement length over the distinct pairs of `T`. -/
noncomputable def maxAgreeT (T : Finset ι) (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+) : ℕ :=
  ((T.product T).filter (fun p : ι × ι => p.1 ≠ p.2)).sup
    (fun p => tupAgree (𝔰 p.1).2 (𝔰 p.2).2)

lemma maxAgreeT_eq (T : Finset ι) (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+) :
    maxAgreeT T 𝔰 = ((T.product T).filter (fun p : ι × ι => p.1 ≠ p.2)).sup
      (fun p => tupAgree (𝔰 p.1).2 (𝔰 p.2).2) := rfl

lemma maxAgreeT_le_of_mem {T : Finset ι} {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+} {x u : ι}
    (hx : x ∈ T) (hu : u ∈ T) (hxu : x ≠ u) :
    tupAgree (𝔰 x).2 (𝔰 u).2 ≤ maxAgreeT T 𝔰 := by
  have hmem : (x, u) ∈ (T.product T).filter (fun p : ι × ι => p.1 ≠ p.2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hu⟩, hxu⟩
  rw [maxAgreeT_eq]
  exact Finset.le_sup (f := fun p : ι × ι => tupAgree (𝔰 p.1).2 (𝔰 p.2).2) hmem

/-- **The maximal agreement length is attained.** -/
theorem exists_pair_maxAgreeT {T : Finset ι} {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+} (hT : 2 ≤ T.card) :
    ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ maxAgreeT T 𝔰 = tupAgree (𝔰 u).2 (𝔰 v).2 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  have hne : ((T.product T).filter (fun p : ι × ι => p.1 ≠ p.2)).Nonempty :=
    ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩⟩
  obtain ⟨p, hp, hpK⟩ := Finset.exists_mem_eq_sup _ hne
    (fun p : ι × ι => tupAgree (𝔰 p.1).2 (𝔰 p.2).2)
  have hp2 := (Finset.mem_filter.mp hp).2
  obtain ⟨hpT1, hpT2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  refine ⟨p.1, hpT1, p.2, hpT2, hp2, ?_⟩
  rw [maxAgreeT_eq]
  exact hpK

/-- **Agreement below the maximal agreement length.** -/
lemma tupE_eq_of_maxAgreeT {T : Finset ι} {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+} {u v : ι}
    (hK : maxAgreeT T 𝔰 = tupAgree (𝔰 u).2 (𝔰 v).2) :
    ∀ l, l < maxAgreeT T 𝔰 → tupE (𝔰 u).2 l = tupE (𝔰 v).2 l := by
  intro l hl
  rw [hK] at hl
  exact tupAgree_spec (𝔰 u).2 (𝔰 v).2 l hl

/-- **Disagreement at the next level.** -/
lemma not_tupE_eq_succ_of_maxAgreeT {T : Finset ι} {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+} {u v : ι}
    (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v)
    (hne : tupleListP F (𝔰 u).2 ≠ tupleListP F (𝔰 v).2)
    (hK : maxAgreeT T 𝔰 = tupAgree (𝔰 u).2 (𝔰 v).2) :
    ¬ ∀ l, l < maxAgreeT T 𝔰 + 1 → tupE (𝔰 u).2 l = tupE (𝔰 v).2 l := by
  intro hall
  rcases eq_or_le_of_tupAgree (F := F) (hK := le_of_eq hK.symm) (fun l hl => hall l hl) with h | h
  · exact hne h
  · omega

/-- **Uniqueness of the extension of the maximal agreement prefix.** -/
lemma unique_take_of_maxAgreeT {T : Finset ι} {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+} {u v : ι}
    (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v)
    (hlinj : ∀ i j, i ∈ T → j ∈ T → tupleListP F (𝔰 i).2 = tupleListP F (𝔰 j).2 → i = j)
    (hK : maxAgreeT T 𝔰 = tupAgree (𝔰 u).2 (𝔰 v).2) :
    ∀ x ∈ T, (tupleListP F (𝔰 x).2).take (maxAgreeT T 𝔰 + 1)
      = (tupleListP F (𝔰 u).2).take (maxAgreeT T 𝔰 + 1) → x = u := by
  intro x hx htake
  by_cases hxu : x = u
  · exact hxu
  · rcases eq_or_le_of_tupAgree (F := F) (hK := maxAgreeT_le_of_mem (𝔰 := 𝔰) hx hu hxu)
      (fun l hl => tupE_eq_of_take_eq htake l hl) with h | h
    · exact absurd (hlinj x u hx hu h) hxu
    · omega

end MaxPref

end ZagierHoffmanPositiveChar