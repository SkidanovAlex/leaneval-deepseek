import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.CritIdxCardLe
import Submission.Work.WilG4c.WordCountsLe
import Submission.Work.WilG4c.SumWordCounts
import Submission.Work.WilG4c.FilterCardInitialSegment
import Submission.Work.WilG4c.CardFinFilterIco

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c
open Work.WilkG4c

/-! ## My development -/

/-- prefix sum of a counts vector -/
def psum {N : ℕ} (c : Fin N → ℕ) (i : Fin N) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin N => k ≤ i), c k

/-- prefix sum strictly before `i` -/
def pre {N : ℕ} (c : Fin N → ℕ) (i : Fin N) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), c k

lemma psum_mono {N : ℕ} (c : Fin N → ℕ) : ∀ a b : Fin N, a ≤ b → psum c a ≤ psum c b := by
  intro a b hab
  simp only [psum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => Nat.zero_le _)
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact le_trans hk hab

lemma psum_last {n : ℕ} (c : Fin (n+1) → ℕ) : psum c (Fin.last n) = ∑ i, c i := by
  simp only [psum]
  rw [Finset.filter_true_of_mem (fun x _ => Fin.le_last x)]

lemma psum_eq_pre {N : ℕ} (c : Fin N → ℕ) (i : Fin N) : psum c i = pre c i + c i := by
  have hins : Finset.univ.filter (fun k : Fin N => k ≤ i)
      = insert i (Finset.univ.filter (fun k : Fin N => k.val < i.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hk
      rcases lt_or_eq_of_le hk with h | h
      · exact Or.inr (Fin.lt_def.mp h)
      · exact Or.inl h
    · rintro (rfl | hk)
      · exact le_rfl
      · exact le_of_lt (Fin.lt_def.mpr hk)
  have hnot : i ∉ Finset.univ.filter (fun k : Fin N => k.val < i.val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_irrefl i.val
  simp only [psum, pre]
  rw [hins, Finset.sum_insert hnot]
  exact Nat.add_comm _ _

lemma psum_le_pre {N : ℕ} (c : Fin N → ℕ) {k i : Fin N} (h : k.val < i.val) :
    psum c k ≤ pre c i := by
  simp only [psum, pre]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => Nat.zero_le _)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  have : j.val ≤ k.val := Fin.le_def.mp hj
  omega

lemma pre_add_psum {N : ℕ} (c : Fin N → ℕ) {k i : Fin N} (h : i.val ≤ k.val) :
    pre c i + c i ≤ psum c k := by
  rw [← psum_eq_pre]
  simp only [psum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => Nat.zero_le _)
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact Fin.le_def.mpr (le_trans (Fin.le_def.mp hj) h)

lemma psum_eq_pre_of_val_succ {N : ℕ} (c : Fin N → ℕ) {i' i : Fin N} (h : i'.val + 1 = i.val) :
    psum c i' = pre c i := by
  have hs : Finset.univ.filter (fun k : Fin N => k ≤ i')
      = Finset.univ.filter (fun k : Fin N => k.val < i.val) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      have := Fin.le_def.mp hk
      omega
    · intro hk
      exact Fin.le_def.mpr (by omega)
  simp only [psum, pre, hs]

lemma pre_eq_zero {N : ℕ} (c : Fin N → ℕ) {i : Fin N} (hi : i.val = 0) : pre c i = 0 := by
  have h : Finset.univ.filter (fun k : Fin N => k.val < i.val) = ∅ :=
    Finset.filter_false_of_mem (fun k _ hk => by omega)
  simp only [pre, h, Finset.sum_empty]

lemma cntWord_val {n m : ℕ} (c : Fin (n+1) → ℕ) (hsum : ∑ i, c i = m) (j : Fin m) :
    (cntWord n m c j).val
      = (Finset.univ.filter (fun i : Fin (n+1) => psum c i ≤ j.val)).card := by
  have hTle : (Finset.univ.filter (fun i : Fin (n+1) => psum c i ≤ j.val)).card ≤ n := by
    have hsub : Finset.univ.filter (fun i : Fin (n+1) => psum c i ≤ j.val)
        ⊆ Finset.Iio (Fin.last n) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rw [Finset.mem_Iio]
      by_contra hk'
      push_neg at hk'
      have h1 : psum c (Fin.last n) ≤ psum c k := psum_mono c _ _ hk'
      rw [psum_last, hsum] at h1
      omega
    have h2 := Finset.card_le_card hsub
    rw [Fin.card_Iio, Fin.val_last] at h2
    exact h2
  show (cntWord n m c j).val = _
  simp only [cntWord, psum]
  exact Nat.min_eq_left hTle

lemma psum_wordCounts {n m : ℕ} (v : Fin m → Fin (n+1)) (i : Fin (n+1)) :
    psum (wordCounts v) i = (Finset.univ.filter (fun j : Fin m => v j ≤ i)).card := by
  have htop : (Finset.univ.filter (fun k : Fin (n+1) => k ≤ i)) = Finset.Iic i := by
    ext k; simp [Finset.mem_Iic]
  calc psum (wordCounts v) i
      = ∑ k ∈ Finset.Iic i, (Finset.univ.filter (fun j : Fin m => v j = k)).card := by
        simp only [psum, htop, wordCounts]
    _ = (Finset.univ.filter (fun j : Fin m => v j ∈ Finset.Iic i)).card :=
        Finset.sum_card_fiberwise_eq_card_filter _ _ v
    _ = (Finset.univ.filter (fun j : Fin m => v j ≤ i)).card := by
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]

lemma psum_wordCounts_le_iff {n m : ℕ} {v : Fin m → Fin (n+1)}
    (hv : ∀ i j : Fin m, i ≤ j → v i ≤ v j) (i : Fin (n+1)) (j : Fin m) :
    psum (wordCounts v) i ≤ j.val ↔ i.val < (v j).val := by
  rw [psum_wordCounts]
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hvji : v j ≤ i := Fin.le_def.mpr hlt
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun j' : Fin m => v j' ≤ i) := by
      intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans (hv _ _ (Finset.mem_Iic.mp hj')) hvji
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    omega
  · intro h
    have hsub : Finset.univ.filter (fun j' : Fin m => v j' ≤ i) ⊆ Finset.Iio j := by
      intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      rw [Finset.mem_Iio]
      by_contra hnot
      push_neg at hnot
      have h1 : v j ≤ v j' := hv _ _ hnot
      have h2 : (v j).val ≤ i.val := Fin.le_def.mp (le_trans h1 hj')
      omega
    have hc := Finset.card_le_card hsub
    rwa [Fin.card_Iio] at hc

lemma eq_of_forall_fin_val_lt {N a b : ℕ} (ha : a < N) (hb : b < N)
    (h : ∀ i : Fin N, (i.val < a ↔ i.val < b)) : a = b := by
  have h1 : a ≤ b := by
    by_contra hc
    push_neg at hc
    exact absurd ((h ⟨b, hb⟩).mp hc) (lt_irrefl b)
  have h2 : b ≤ a := by
    by_contra hc
    push_neg at hc
    exact absurd ((h ⟨a, ha⟩).mpr hc) (lt_irrefl a)
  omega

lemma cntWord_wordCounts {n m : ℕ} {v : Fin m → Fin (n+1)}
    (hv : ∀ i j : Fin m, i ≤ j → v i ≤ v j) :
    cntWord n m (wordCounts v) = v := by
  have hsum := SumWordCounts v
  funext j
  apply Fin.ext
  rw [cntWord_val (wordCounts v) hsum j]
  set T := (Finset.univ.filter (fun i : Fin (n+1) => psum (wordCounts v) i ≤ j.val)).card with hT
  have hTlt : T < n + 1 := by
    have h1 : (cntWord n m (wordCounts v) j).val = T := by
      rw [hT]; exact cntWord_val (wordCounts v) hsum j
    have h2 := (cntWord n m (wordCounts v) j).isLt
    rwa [h1] at h2
  refine eq_of_forall_fin_val_lt hTlt (v j).isLt (fun i => ?_)
  rw [hT]
  exact (FilterCardInitialSegment (psum (wordCounts v)) (psum_mono (wordCounts v)) j.val i).symm.trans
    (psum_wordCounts_le_iff hv i j)

lemma key_lemma {n m : ℕ} (c : Fin (n+1) → ℕ) (hsum : ∑ i, c i = m) (j : Fin m) (i : Fin (n+1)) :
    ((Finset.univ.filter (fun i' : Fin (n+1) => psum c i' ≤ j.val)).card = i.val)
      ↔ (pre c i ≤ j.val ∧ j.val < pre c i + c i) := by
  constructor
  · intro hTi
    have H : ∀ i' : Fin (n+1), (psum c i' ≤ j.val ↔ i'.val < i.val) := by
      intro i'
      have h := FilterCardInitialSegment (psum c) (psum_mono c) j.val i'
      rw [hTi] at h
      exact h
    constructor
    · rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
      · have : pre c i = 0 := pre_eq_zero c hi0
        omega
      · set i' : Fin (n+1) := ⟨i.val - 1, by omega⟩ with hi'
        have hval : i'.val = i.val - 1 := rfl
        have hsucc : i'.val + 1 = i.val := by omega
        have hlt : i'.val < i.val := by omega
        have hpe : psum c i' = pre c i := psum_eq_pre_of_val_succ c hsucc
        have := (H i').mpr hlt
        omega
    · have hni : ¬ (psum c i ≤ j.val) := fun hh => absurd ((H i).mp hh) (lt_irrefl i.val)
      have hp : psum c i = pre c i + c i := psum_eq_pre c i
      omega
  · rintro ⟨h1, h2⟩
    have H : ∀ i' : Fin (n+1), (psum c i' ≤ j.val ↔ i'.val < i.val) := by
      intro i'
      constructor
      · intro hle
        by_contra hlt
        push_neg at hlt
        have h3 : pre c i + c i ≤ psum c i' := pre_add_psum c hlt
        omega
      · intro hlt
        have h3 : psum c i' ≤ pre c i := psum_le_pre c hlt
        omega
    have hfil : (Finset.univ.filter (fun i' : Fin (n+1) => psum c i' ≤ j.val))
        = (Finset.univ.filter (fun i' : Fin (n+1) => i'.val < i.val)) :=
      Finset.filter_congr (fun i' _ => H i')
    rw [hfil]
    have hio : (Finset.univ.filter (fun i' : Fin (n+1) => i'.val < i.val)) = Finset.Iio i := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
    rw [hio, Fin.card_Iio]

lemma cntWord_eq_iff {n m : ℕ} (c : Fin (n+1) → ℕ) (hsum : ∑ i, c i = m)
    (j : Fin m) (i : Fin (n+1)) :
    cntWord n m c j = i ↔ (pre c i ≤ j.val ∧ j.val < pre c i + c i) := by
  rw [Fin.ext_iff, cntWord_val c hsum j]
  exact key_lemma c hsum j i

lemma wordCounts_cntWord {n m : ℕ} (c : Fin (n+1) → ℕ) (hsum : ∑ i, c i = m) :
    wordCounts (cntWord n m c) = c := by
  funext i
  show (Finset.univ.filter (fun j : Fin m => cntWord n m c j = i)).card = c i
  have hle : pre c i + c i ≤ m := by
    calc pre c i + c i = psum c i := (psum_eq_pre c i).symm
      _ ≤ psum c (Fin.last n) := psum_mono c i (Fin.last n) (Fin.le_last i)
      _ = ∑ j, c j := psum_last c
      _ = m := hsum
  have hfil : (Finset.univ.filter (fun j : Fin m => cntWord n m c j = i))
      = (Finset.univ.filter (fun j : Fin m => pre c i ≤ j.val ∧ j.val < pre c i + c i)) :=
    Finset.filter_congr (fun j _ => cntWord_eq_iff c hsum j i)
  rw [hfil, CardFinFilterIco hle]

/-! ## The target -/

theorem CntWordFacts (n k : ℕ) :
    (∀ {m : ℕ} (v : Fin m → Fin (n + 1)), (∀ i j : Fin m, i ≤ j → v i ≤ v j) →
      Work.WilkG4c.cntWord n m (Work.WilkG4c.wordCounts v) = v) ∧
    (∀ {m : ℕ} (v : Fin m → Fin (n + 1)) (i : Fin (n + 1)),
      Work.WilkG4c.wordCounts (Work.WilkG4c.cntWord n m (Work.WilkG4c.wordCounts v)) i =
        Work.WilkG4c.wordCounts v i) ∧
    ((Work.WilkG4c.critIdx n k).card ≤ k * k ^ (n + 1) + 1) ∧
    (∀ {m : ℕ} (v : Fin m → Fin (n + 1)) (i : Fin (n + 1)),
      Work.WilkG4c.wordCounts v i ≤ m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m v hv
    exact cntWord_wordCounts hv
  · intro m v i
    exact congrFun (wordCounts_cntWord (wordCounts v) (SumWordCounts v)) i
  · exact CritIdxCardLe n k
  · intro m v i
    exact WordCountsLe v i

end Work.WilG4c
