import Mathlib
import Submission.Work.SSSR.Cohomology.Crux33.EzGen
import Submission.Work.SSSR.Cohomology.Crux33.ShuffleIndex
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option maxHeartbeats 4000000
set_option autoImplicit false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial
namespace Work.SSSR.KunnethEZ

open Work.SSSR.Cohomology.Crux33
noncomputable section

variable {n : ℕ}


/-- The number of `E`-steps before the vertex `m` of a shuffle over `Fin n`. -/
def ANat (S : Finset (Fin n)) (m : ℕ) : ℕ :=
  (((Finset.univ : Finset (Fin n)).filter (fun j => j.val < m)) \ S).card

/-- The number of `N`-steps before the vertex `m` of a shuffle over `Fin n`. -/
def BNat (S : Finset (Fin n)) (m : ℕ) : ℕ :=
  (S.filter (fun j => j.val < m)).card

lemma pANat_eq_ANat {p q : ℕ} (S : Finset (Fin (p + q))) (m : ℕ) :
    pANat S m = ANat S m := rfl

lemma pBNat_eq_BNat {p q : ℕ} (S : Finset (Fin (p + q))) (m : ℕ) :
    pBNat S m = BNat S m := rfl

lemma card_univ_filter_val_lt {n : ℕ} (m : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun j => j.val < m)).card = min m n := by
  rw [← Finset.card_range (min m n)]
  refine Finset.card_bij
    (fun (j : Fin n) (_ : j ∈ (Finset.univ : Finset (Fin n)).filter (fun j => j.val < m)) =>
      j.val) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [Finset.mem_range]; omega
  · intro a _ b _ hab
    exact Fin.ext hab
  · intro b hb
    simp only [Finset.mem_range] at hb
    exact ⟨⟨b, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega, rfl⟩

lemma BNat_eq {n : ℕ} (S : Finset (Fin n)) (m : ℕ) :
    BNat S m = ((Finset.univ : Finset (Fin n)).filter (fun j => j.val < m) ∩ S).card := by
  rw [BNat]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  tauto

lemma ANat_add_BNat {n : ℕ} (S : Finset (Fin n)) (m : ℕ) :
    ANat S m + BNat S m = min m n := by
  rw [ANat, BNat_eq, Finset.card_sdiff_add_card_inter, card_univ_filter_val_lt]

lemma ANat_zero {n : ℕ} (S : Finset (Fin n)) : ANat S 0 = 0 := by
  simp [ANat]

lemma BNat_zero {n : ℕ} (S : Finset (Fin n)) : BNat S 0 = 0 := by
  simp [BNat]

lemma BNat_succ {n : ℕ} (S : Finset (Fin n)) {m : ℕ} (hm : m < n) :
    BNat S (m + 1) = BNat S m + (if (⟨m, hm⟩ : Fin n) ∈ S then 1 else 0) := by
  rw [BNat, BNat]
  by_cases hmem : (⟨m, hm⟩ : Fin n) ∈ S
  · have h : S.filter (fun j => j.val < m + 1)
        = insert (⟨m, hm⟩ : Fin n) (S.filter (fun j => j.val < m)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hxS, hxlt⟩
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hxlt) with h | h
        · exact Or.inr ⟨hxS, h⟩
        · exact Or.inl (Fin.ext h)
      · rintro (rfl | ⟨hxS, hxlt⟩)
        · exact ⟨hmem, by simp⟩
        · exact ⟨hxS, by omega⟩
    rw [h, Finset.card_insert_of_notMem (by simp [Finset.mem_filter]), if_pos hmem]
  · have h : S.filter (fun j => j.val < m + 1) = S.filter (fun j => j.val < m) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hxS, hxlt⟩
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hxlt) with h | h
        · exact ⟨hxS, h⟩
        · exact absurd (h ▸ hxS) hmem
      · rintro ⟨hxS, hxlt⟩
        exact ⟨hxS, by omega⟩
    rw [h, if_neg hmem]
    simp

lemma ANat_succ {n : ℕ} (S : Finset (Fin n)) {m : ℕ} (hm : m < n) :
    ANat S (m + 1) = ANat S m + (if (⟨m, hm⟩ : Fin n) ∈ S then 0 else 1) := by
  have hmin1 : min (m + 1) n = m + 1 := min_eq_left (by omega)
  have hmin0 : min m n = m := min_eq_left (by omega)
  by_cases hmem : (⟨m, hm⟩ : Fin n) ∈ S
  · have h1 := ANat_add_BNat S (m + 1)
    have h2 := ANat_add_BNat S m
    have h3 := BNat_succ S hm
    rw [hmin1] at h1; rw [hmin0] at h2
    rw [if_pos hmem] at h3
    rw [if_pos hmem]
    omega
  · have h1 := ANat_add_BNat S (m + 1)
    have h2 := ANat_add_BNat S m
    have h3 := BNat_succ S hm
    rw [hmin1] at h1; rw [hmin0] at h2
    rw [if_neg hmem] at h3
    rw [if_neg hmem]
    omega

lemma ANat_mono {n : ℕ} (S : Finset (Fin n)) : Monotone (ANat S) := by
  intro m m' hmm'
  rw [ANat, ANat]
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 hmm', hx.2⟩

lemma BNat_mono {n : ℕ} (S : Finset (Fin n)) : Monotone (BNat S) := by
  intro m m' hmm'
  rw [BNat, BNat]
  refine Finset.card_le_card (fun x hx => ?_)
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2 hmm'⟩

lemma ANat_le {n : ℕ} (S : Finset (Fin n)) (m : ℕ) : ANat S m ≤ min m n := by
  have := ANat_add_BNat S m; omega

/-- `BNat` at the far vertex is the cardinality. -/
lemma BNat_last {n : ℕ} (S : Finset (Fin n)) : BNat S n = S.card := by
  rw [BNat, Finset.filter_true_of_mem (fun x _ => x.isLt)]

/-- `ANat` at the far vertex is the number of `E`-steps. -/
lemma ANat_last {n : ℕ} (S : Finset (Fin n)) : ANat S n = n - S.card := by
  have h := ANat_add_BNat S n
  rw [BNat_last, min_self] at h
  omega






/-! ## Inserting and deleting a step -/

/-- Insert a gap at `pos ∈ Fin N` into `Fin (N-1)`.  Its image is `Fin N \ {pos}`. -/
def insIdx {N : ℕ} (pos : Fin N) : Fin (N - 1) → Fin N :=
  fun k => if k.val < pos.val then ⟨k.val, by have := k.isLt; omega⟩
           else ⟨k.val + 1, by have := k.isLt; have := pos.isLt; omega⟩

lemma insIdx_val {N : ℕ} (pos : Fin N) (k : Fin (N - 1)) :
    (insIdx pos k).val = if k.val < pos.val then k.val else k.val + 1 := by
  unfold insIdx
  split_ifs <;> simp

lemma insIdx_lt {N : ℕ} (pos : Fin N) (k : Fin (N - 1)) (h : k.val < pos.val) :
    insIdx pos k = ⟨k.val, by have := k.isLt; omega⟩ := by
  simp only [insIdx, if_pos h]

lemma insIdx_ge {N : ℕ} (pos : Fin N) (k : Fin (N - 1)) (h : ¬ k.val < pos.val) :
    insIdx pos k = ⟨k.val + 1, by have := k.isLt; have := pos.isLt; omega⟩ := by
  simp only [insIdx, if_neg h]

lemma insIdx_injective {N : ℕ} (pos : Fin N) : Function.Injective (insIdx pos) := by
  intro k₁ k₂ h
  have hv : (insIdx pos k₁).val = (insIdx pos k₂).val := congrArg Fin.val h
  by_cases h₁ : k₁.val < pos.val <;> by_cases h₂ : k₂.val < pos.val
  · rw [insIdx_lt pos k₁ h₁, insIdx_lt pos k₂ h₂] at hv
    simp only [Fin.val_mk] at hv
    exact Fin.ext hv
  · rw [insIdx_lt pos k₁ h₁, insIdx_ge pos k₂ h₂] at hv
    simp only [Fin.val_mk] at hv
    omega
  · rw [insIdx_ge pos k₁ h₁, insIdx_lt pos k₂ h₂] at hv
    simp only [Fin.val_mk] at hv
    omega
  · rw [insIdx_ge pos k₁ h₁, insIdx_ge pos k₂ h₂] at hv
    simp only [Fin.val_mk] at hv
    exact Fin.ext (by omega)

lemma insIdx_ne {N : ℕ} (pos : Fin N) (k : Fin (N - 1)) : insIdx pos k ≠ pos := by
  intro h
  have hv : (insIdx pos k).val = pos.val := congrArg Fin.val h
  by_cases hk : k.val < pos.val
  · rw [insIdx_lt pos k hk] at hv
    simp only [Fin.val_mk] at hv
    omega
  · rw [insIdx_ge pos k hk] at hv
    simp only [Fin.val_mk] at hv
    omega

lemma insIdx_surj {N : ℕ} (pos : Fin N) (k : Fin N) (hk : k ≠ pos) :
    ∃ k' : Fin (N - 1), insIdx pos k' = k := by
  have hval : k.val < pos.val ∨ pos.val < k.val := by
    rcases lt_trichotomy k.val pos.val with h | h | h
    · exact Or.inl h
    · exact absurd (Fin.ext h) hk
    · exact Or.inr h
  rcases hval with h | h
  · refine ⟨⟨k.val, by have := k.isLt; omega⟩, ?_⟩
    exact insIdx_lt pos _ h
  · refine ⟨⟨k.val - 1, by have := k.isLt; omega⟩, ?_⟩
    have h' : ¬ (k.val - 1 < pos.val) := by omega
    rw [insIdx_ge pos _ h']
    exact Fin.ext (by simp only [Fin.val_mk]; omega)

/-- Insert an `E`-step (a non-element) at `pos`. -/
def insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) : Finset (Fin N) :=
  T.image (insIdx pos)

/-- Insert an `N`-step (an element) at `pos`. -/
def insertN {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) : Finset (Fin N) :=
  insert pos (insertE T pos)

/-- Delete the element at `pos` (a non-element, i.e. an `E`-step). -/
def deleteE {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) : Finset (Fin (N - 1)) :=
  Finset.univ.filter (fun k => insIdx pos k ∈ S)

/-- Delete the element at `pos` (an element, i.e. an `N`-step). -/
def deleteN {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) : Finset (Fin (N - 1)) :=
  deleteE (S.erase pos) pos

lemma mem_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) (k : Fin N) :
    k ∈ insertE T pos ↔ ∃ k' ∈ T, insIdx pos k' = k := by
  simp [insertE, Finset.mem_image]

lemma mem_deleteE {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) (k : Fin (N - 1)) :
    k ∈ deleteE S pos ↔ insIdx pos k ∈ S := by
  simp [deleteE]

lemma mem_deleteN {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) (k : Fin (N - 1)) :
    k ∈ deleteN S pos ↔ insIdx pos k ∈ S ∧ insIdx pos k ≠ pos := by
  rw [deleteN, mem_deleteE, Finset.mem_erase]
  exact and_comm

lemma card_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    (insertE T pos).card = T.card :=
  Finset.card_image_of_injective T (insIdx_injective pos)

lemma pos_notMem_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    pos ∉ insertE T pos := by
  rw [mem_insertE]
  rintro ⟨k', -, hk'⟩
  exact insIdx_ne pos k' hk'

lemma deleteE_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    deleteE (insertE T pos) pos = T := by
  ext k
  rw [mem_deleteE, mem_insertE]
  constructor
  · rintro ⟨k', hk', hkk'⟩
    exact (insIdx_injective pos hkk') ▸ hk'
  · intro hk
    exact ⟨k, hk, rfl⟩

lemma insertE_deleteE {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) :
    insertE (deleteE S pos) pos = S.erase pos := by
  ext k
  rw [mem_insertE]
  constructor
  · rintro ⟨k', hk', hkk'⟩
    rw [mem_deleteE] at hk'
    rw [← hkk', Finset.mem_erase]
    exact ⟨insIdx_ne pos k', hk'⟩
  · intro hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkne, hkmem⟩ := hk
    obtain ⟨k', hk'⟩ := insIdx_surj pos k hkne
    exact ⟨k', by rw [mem_deleteE, hk']; exact hkmem, hk'⟩

lemma deleteN_insertN {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    deleteN (insertN T pos) pos = T := by
  rw [deleteN, insertN, Finset.erase_insert (pos_notMem_insertE T pos), deleteE_insertE]

lemma insertN_deleteN {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) (hpos : pos ∈ S) :
    insertN (deleteN S pos) pos = S := by
  rw [deleteN, insertN, insertE_deleteE,
    Finset.erase_eq_of_notMem (Finset.notMem_erase pos S), Finset.insert_erase hpos]

lemma card_insertN {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    (insertN T pos).card = T.card + 1 := by
  rw [insertN, Finset.card_insert_of_notMem (pos_notMem_insertE T pos), card_insertE]

lemma card_deleteN {N : ℕ} (S : Finset (Fin N)) (pos : Fin N) (hpos : pos ∈ S) :
    (deleteN S pos).card = S.card - 1 := by
  have h := card_insertN (deleteN S pos) pos
  rw [insertN_deleteN S pos hpos] at h
  omega

/-! ## The path counts of an insertion -/

lemma insIdx_val_lt_iff {N : ℕ} (pos : Fin N) (k : Fin (N - 1)) (v : ℕ) :
    (insIdx pos k).val < v ↔ k.val < (if v ≤ pos.val then v else v - 1) := by
  rw [insIdx_val]
  by_cases hk : k.val < pos.val
  · rw [if_pos hk]
    by_cases hv : v ≤ pos.val
    · rw [if_pos hv]
    · rw [if_neg hv]
      constructor <;> intro h <;> omega
  · rw [if_neg hk]
    by_cases hv : v ≤ pos.val
    · rw [if_pos hv]
      constructor <;> intro h <;> omega
    · rw [if_neg hv]
      constructor <;> intro h <;> omega

lemma BNat_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) (v : ℕ) :
    BNat (insertE T pos) v = BNat T (if v ≤ pos.val then v else v - 1) := by
  simp only [BNat, insertE]
  rw [Finset.filter_image, Finset.card_image_of_injective _ (insIdx_injective pos)]
  congr 1
  exact Finset.filter_congr (fun k _ => insIdx_val_lt_iff pos k v)

lemma ANat_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) (v : ℕ) :
    ANat (insertE T pos) v = if v ≤ pos.val then ANat T v else ANat T (v - 1) + 1 := by
  have h1 := ANat_add_BNat (insertE T pos) v
  have h2 := ANat_add_BNat T (if v ≤ pos.val then v else v - 1)
  have h3 := BNat_insertE T pos v
  rw [h3] at h1
  have hpos : pos.val < N := pos.isLt
  have h4 : min v N = min (if v ≤ pos.val then v else v - 1) (N - 1)
      + (if pos.val < v then 1 else 0) := by
    by_cases hv : v ≤ pos.val
    · rw [if_pos hv, if_neg (by omega)]
      omega
    · rw [if_neg hv, if_pos (by omega)]
      omega
  by_cases hv : v ≤ pos.val
  · rw [if_pos hv] at h1 h2 h4
    rw [if_pos hv]
    omega
  · rw [if_neg hv] at h1 h2 h4
    rw [if_neg hv]
    omega

lemma BNat_insert_pos {N : ℕ} (A : Finset (Fin N)) (pos : Fin N) (h : pos ∉ A) (v : ℕ) :
    BNat (insert pos A) v = BNat A v + (if pos.val < v then 1 else 0) := by
  simp only [BNat]
  rw [Finset.filter_insert]
  by_cases hp : pos.val < v
  · rw [if_pos hp, if_pos hp]
    rw [Finset.card_insert_of_notMem (fun hh => h (Finset.mem_of_mem_filter _ hh))]
  · rw [if_neg hp, if_neg hp, add_zero]

lemma BNat_insertN {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) (v : ℕ) :
    BNat (insertN T pos) v = if v ≤ pos.val then BNat T v else BNat T (v - 1) + 1 := by
  rw [insertN, BNat_insert_pos (insertE T pos) pos (pos_notMem_insertE T pos) v,
    BNat_insertE T pos v]
  by_cases hv : v ≤ pos.val
  · rw [if_pos hv, if_pos hv, if_neg (by omega), add_zero]
  · rw [if_neg hv, if_neg hv, if_pos (by omega)]

lemma ANat_insertN {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) (v : ℕ) :
    ANat (insertN T pos) v = ANat T (if v ≤ pos.val then v else v - 1) := by
  have h1 := ANat_add_BNat (insertN T pos) v
  have h2 := ANat_add_BNat T (if v ≤ pos.val then v else v - 1)
  have h3 := BNat_insertN T pos v
  rw [h3] at h1
  have hpos : pos.val < N := pos.isLt
  have h4 : min v N = min (if v ≤ pos.val then v else v - 1) (N - 1)
      + (if pos.val < v then 1 else 0) := by
    by_cases hv : v ≤ pos.val
    · rw [if_pos hv, if_neg (by omega)]
      omega
    · rw [if_neg hv, if_pos (by omega)]
      omega
  by_cases hv : v ≤ pos.val
  · rw [if_pos hv] at h1 h2 h4
    rw [if_pos hv]
    omega
  · rw [if_neg hv] at h1 h2 h4
    rw [if_neg hv]
    omega

/-! ## The Eilenberg–Zilber sign of a general shuffle -/

/-- The number of inversions of a shuffle at a general ambient: pairs (an `N`-step before an
`E`-step). -/
def invCountN {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  ((Finset.univ : Finset (Fin N)) \ S).sum (fun j => BNat S j.val)

/-- The Eilenberg–Zilber sign of a shuffle at a general ambient. -/
def shufSignN {N : ℕ} (S : Finset (Fin N)) : ℤ := (-1) ^ (invCountN S)

lemma invCount_eq_invCountN {p q : ℕ} (S : Finset (Fin (p + q))) :
    invCount S = invCountN S := by
  simp only [invCount, invCountN, pBNat_eq_BNat]

lemma shufSign_eq_shufSignN {p q : ℕ} (S : Finset (Fin (p + q))) :
    shufSign S = shufSignN S := by
  simp only [shufSign, shufSignN, invCount_eq_invCountN]

lemma BNat_insertE_insIdx {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N)
    (k : Fin (N - 1)) :
    BNat (insertE T pos) (insIdx pos k).val = BNat T k.val := by
  by_cases hk : k.val < pos.val
  · rw [insIdx_lt pos k hk]
    have h : (⟨k.val, by have := k.isLt; omega⟩ : Fin N).val ≤ pos.val := by
      simp only [Fin.val_mk]; omega
    rw [BNat_insertE, if_pos h]
  · rw [insIdx_ge pos k hk]
    have h : ¬ (⟨k.val + 1, by have := k.isLt; have := pos.isLt; omega⟩ : Fin N).val ≤ pos.val := by
      simp only [Fin.val_mk]; omega
    rw [BNat_insertE, if_neg h]
    congr 1

lemma BNat_insertE_pos {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    BNat (insertE T pos) pos.val = BNat T pos.val := by
  rw [BNat_insertE, if_pos (le_refl _)]

lemma compl_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    (Finset.univ : Finset (Fin N)) \ insertE T pos
      = insert pos (((Finset.univ : Finset (Fin (N - 1))) \ T).image (insIdx pos)) := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, mem_insertE, Finset.mem_insert,
    Finset.mem_image]
  constructor
  · rintro hk
    by_cases hkp : k = pos
    · exact Or.inl hkp
    · obtain ⟨k', hk'⟩ := insIdx_surj pos k hkp
      refine Or.inr ?_
      exact ⟨k', (fun hT => hk ⟨k', hT, hk'⟩), hk'⟩
  · rintro (hkp | ⟨k', hk'T, hk'k⟩)
    · rintro ⟨k'', -, hk''⟩
      exact insIdx_ne pos k'' (hk''.trans hkp)
    · rintro ⟨k'', hk''T, hk''⟩
      exact hk'T (insIdx_injective pos (hk''.trans hk'k.symm) ▸ hk''T)

lemma invCountN_insertE {N : ℕ} (T : Finset (Fin (N - 1))) (pos : Fin N) :
    invCountN (insertE T pos) = invCountN T + BNat T pos.val := by
  rw [invCountN, invCountN, compl_insertE]
  rw [Finset.sum_insert (by
    change pos ∉ insertE ((Finset.univ : Finset (Fin (N - 1))) \ T) pos
    rw [mem_insertE]
    rintro ⟨k', hk', hk'⟩
    exact insIdx_ne pos k' hk')]
  rw [BNat_insertE_pos, Finset.sum_image (fun x _ y _ hxy => insIdx_injective pos hxy),
    add_comm (BNat T pos.val)]
  congr 1
  exact Finset.sum_congr rfl (fun k _ => BNat_insertE_insIdx T pos k)


/-! ## The smaller shuffles and their monotone maps

For the `(p,q)` prism the faces of the shuffle cells that lie on the boundary are the
`(p-1,q)`- and `(p,q-1)`-cells; we index the former by `Fin (p+q-1)`-subsets of cardinality `q` and
the latter by `Fin (p+q-1)`-subsets of cardinality `q-1`.  Each carries the two monotone maps given
by its `E`- and `N`-counts. -/

/-- The `(p-1,q)`-shuffles, as subsets of `Fin (p+q-1)` of cardinality `q`. -/
abbrev Sh23 (p q : ℕ) : Type := {T : Finset (Fin (p + q - 1)) // T.card = q}

/-- The `(p,q-1)`-shuffles, as subsets of `Fin (p+q-1)` of cardinality `q-1`. -/
abbrev Sh32 (p q : ℕ) : Type := {U : Finset (Fin (p + q - 1)) // U.card = q - 1}

/-- The `E`-count map `⦋p+q-1⦌ ⟶ ⦋p-1⦌` of a `(p-1,q)`-shuffle. -/
def aMap23 (p q : ℕ) (T : Sh23 p q) : ⦋p + q - 1⦌ ⟶ ⦋p - 1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨ANat T.1 k.val, by
        have h1 : ANat T.1 k.val ≤ ANat T.1 (p + q - 1) :=
          ANat_mono T.1 (by have := k.isLt; omega)
        rw [ANat_last, T.2] at h1
        show ANat T.1 k.val < ⦋p - 1⦌.len + 1
        rw [SimplexCategory.len_mk]
        omega⟩
      monotone' := fun a b hab => by
        simp only [Fin.le_def]
        exact ANat_mono T.1 hab }

/-- The `N`-count map `⦋p+q-1⦌ ⟶ ⦋q⦌` of a `(p-1,q)`-shuffle. -/
def bMap23 (p q : ℕ) (T : Sh23 p q) : ⦋p + q - 1⦌ ⟶ ⦋q⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨BNat T.1 k.val, by
        have h1 : BNat T.1 k.val ≤ BNat T.1 (p + q - 1) :=
          BNat_mono T.1 (by have := k.isLt; omega)
        rw [BNat_last, T.2] at h1
        show BNat T.1 k.val < ⦋q⦌.len + 1
        rw [SimplexCategory.len_mk]
        omega⟩
      monotone' := fun a b hab => by
        simp only [Fin.le_def]
        exact BNat_mono T.1 hab }

/-- The `E`-count map `⦋p+q-1⦌ ⟶ ⦋p⦌` of a `(p,q-1)`-shuffle. -/
def aMap32 (p q : ℕ) (U : Sh32 p q) : ⦋p + q - 1⦌ ⟶ ⦋p⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨ANat U.1 k.val, by
        have h1 : ANat U.1 k.val ≤ ANat U.1 (p + q - 1) :=
          ANat_mono U.1 (by have := k.isLt; omega)
        rw [ANat_last, U.2] at h1
        show ANat U.1 k.val < ⦋p⦌.len + 1
        rw [SimplexCategory.len_mk]
        omega⟩
      monotone' := fun a b hab => by
        simp only [Fin.le_def]
        exact ANat_mono U.1 hab }

/-- The `N`-count map `⦋p+q-1⦌ ⟶ ⦋q-1⦌` of a `(p,q-1)`-shuffle. -/
def bMap32 (p q : ℕ) (U : Sh32 p q) : ⦋p + q - 1⦌ ⟶ ⦋q - 1⦌ :=
  SimplexCategory.mkHom
    { toFun := fun k => ⟨BNat U.1 k.val, by
        have h1 : BNat U.1 k.val ≤ BNat U.1 (p + q - 1) :=
          BNat_mono U.1 (by have := k.isLt; omega)
        rw [BNat_last, U.2] at h1
        show BNat U.1 k.val < ⦋q - 1⦌.len + 1
        rw [SimplexCategory.len_mk]
        omega⟩
      monotone' := fun a b hab => by
        simp only [Fin.le_def]
        exact BNat_mono U.1 hab }

@[simp] lemma aMap23_apply (p q : ℕ) (T : Sh23 p q) (k : Fin ((p + q - 1) + 1)) :
    ((aMap23 p q T) k).val = ANat T.1 k.val := rfl

@[simp] lemma bMap23_apply (p q : ℕ) (T : Sh23 p q) (k : Fin ((p + q - 1) + 1)) :
    ((bMap23 p q T) k).val = BNat T.1 k.val := rfl

@[simp] lemma aMap32_apply (p q : ℕ) (U : Sh32 p q) (k : Fin ((p + q - 1) + 1)) :
    ((aMap32 p q U) k).val = ANat U.1 k.val := rfl

@[simp] lemma bMap32_apply (p q : ℕ) (U : Sh32 p q) (k : Fin ((p + q - 1) + 1)) :
    ((bMap32 p q U) k).val = BNat U.1 k.val := rfl


/-! ## The boundary and interior faces of a shuffle cell -/

/-- The step preceding the vertex `j`. -/
def stepPrev {N : ℕ} (j : Fin (N + 1)) (h : 0 < j.val) : Fin N :=
  ⟨j.val - 1, by have hj := j.isLt; have hh := h; omega⟩

/-- The step following the vertex `j`. -/
def stepCur {N : ℕ} (j : Fin (N + 1)) (h : j.val < N) : Fin N := ⟨j.val, h⟩

@[simp] lemma stepPrev_val {N : ℕ} (j : Fin (N + 1)) (h : 0 < j.val) :
    (stepPrev j h).val = j.val - 1 := rfl

@[simp] lemma stepCur_val {N : ℕ} (j : Fin (N + 1)) (h : j.val < N) :
    (stepCur j h).val = j.val := rfl

/-- The face `(S,j)` is an `X`-boundary face: all steps adjacent to the vertex `j` are `E`-steps. -/
def IsBX {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) : Prop :=
  ∀ k : Fin N, (k.val = j.val - 1 ∨ k.val = j.val) → k ∉ S

/-- The face `(S,j)` is a `Y`-boundary face: all steps adjacent to the vertex `j` are `N`-steps. -/
def IsBY {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) : Prop :=
  ∀ k : Fin N, (k.val = j.val - 1 ∨ k.val = j.val) → k ∈ S

/-- The face `(S,j)` is interior: neither on the `X`- nor on the `Y`-boundary. -/
def IsInt {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) : Prop := ¬ IsBX S j ∧ ¬ IsBY S j

lemma not_both_boundary {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (j : Fin (N + 1)) :
    ¬ (IsBX S j ∧ IsBY S j) := by
  rintro ⟨h1, h2⟩
  have hjle : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
  have hlt : min j.val (N - 1) < N :=
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
  have hk : (min j.val (N - 1) : ℕ) = j.val - 1 ∨ min j.val (N - 1) = j.val := by
    rcases Nat.lt_or_ge (N - 1) j.val with h | h
    · refine Or.inl ?_
      have : j.val = N := by omega
      rw [this, min_eq_right (by omega)]
    · exact Or.inr (min_eq_left h)
  exact h1 ⟨min j.val (N - 1), hlt⟩ hk (h2 ⟨min j.val (N - 1), hlt⟩ hk)

lemma IsBX_iff_pos {N : ℕ} (S : Finset (Fin N)) {j : Fin (N + 1)}
    (h1 : 0 < j.val) (h2 : j.val < N) :
    IsBX S j ↔ (stepPrev j h1 ∉ S ∧ stepCur j h2 ∉ S) := by
  constructor
  · intro h
    exact ⟨h (stepPrev j h1) (Or.inl (stepPrev_val j h1)),
      h (stepCur j h2) (Or.inr (stepCur_val j h2))⟩
  · rintro ⟨ha, hb⟩ k hk
    rcases hk with hk | hk
    · rw [show k = stepPrev j h1 from Fin.ext (by simp only [Fin.val_mk, stepPrev_val]; omega)]
      exact ha
    · rw [show k = stepCur j h2 from Fin.ext (by simp only [Fin.val_mk, stepCur_val]; omega)]
      exact hb

lemma IsBY_iff_pos {N : ℕ} (S : Finset (Fin N)) {j : Fin (N + 1)}
    (h1 : 0 < j.val) (h2 : j.val < N) :
    IsBY S j ↔ (stepPrev j h1 ∈ S ∧ stepCur j h2 ∈ S) := by
  constructor
  · intro h
    exact ⟨h (stepPrev j h1) (Or.inl (stepPrev_val j h1)),
      h (stepCur j h2) (Or.inr (stepCur_val j h2))⟩
  · rintro ⟨ha, hb⟩ k hk
    rcases hk with hk | hk
    · rw [show k = stepPrev j h1 from Fin.ext (by simp only [Fin.val_mk, stepPrev_val]; omega)]
      exact ha
    · rw [show k = stepCur j h2 from Fin.ext (by simp only [Fin.val_mk, stepCur_val]; omega)]
      exact hb

lemma IsBX_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    IsBX S 0 ↔ ((⟨0, hN⟩ : Fin N) ∉ S) := by
  constructor
  · intro h; exact h _ (Or.inr (by simp))
  · intro h k hk
    have : k.val = 0 := by rcases hk with hk | hk <;> simpa using hk
    rw [show k = ⟨0, hN⟩ from Fin.ext this]; exact h

lemma IsBY_zero {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    IsBY S 0 ↔ ((⟨0, hN⟩ : Fin N) ∈ S) := by
  constructor
  · intro h; exact h _ (Or.inr (by simp))
  · intro h k hk
    have : k.val = 0 := by rcases hk with hk | hk <;> simpa using hk
    rw [show k = ⟨0, hN⟩ from Fin.ext this]; exact h

lemma IsBX_last {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    IsBX S ⟨N, Nat.lt_succ_self N⟩ ↔ ((⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ : Fin N) ∉ S) := by
  constructor
  · intro h
    exact h ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ (Or.inl rfl)
  · intro h k hk
    have hkv : k.val = N - 1 := by
      rcases hk with hk | hk
      · exact hk
      · exact absurd (hk ▸ k.isLt) (by simp)
    rw [show k = (⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ : Fin N) from Fin.ext hkv]; exact h

lemma IsBY_last {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) :
    IsBY S ⟨N, Nat.lt_succ_self N⟩ ↔ ((⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ : Fin N) ∈ S) := by
  constructor
  · intro h
    exact h ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ (Or.inl rfl)
  · intro h k hk
    have hkv : k.val = N - 1 := by
      rcases hk with hk | hk
      · exact hk
      · exact absurd (hk ▸ k.isLt) (by simp)
    rw [show k = (⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ : Fin N) from Fin.ext hkv]; exact h

lemma IsInt_zero {N : ℕ} (S : Finset (Fin N)) : ¬ IsInt S 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro h
    exact h.1 (fun k => Fin.elim0 k)
  · rw [IsInt]
    by_cases h : ((⟨0, hN⟩ : Fin N) ∈ S)
    · exact fun hh => hh.2 ((IsBY_zero hN S).mpr h)
    · exact fun hh => hh.1 ((IsBX_zero hN S).mpr h)

lemma IsInt_last {N : ℕ} (S : Finset (Fin N)) : ¬ IsInt S ⟨N, Nat.lt_succ_self N⟩ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    intro h
    exact h.1 (fun k => Fin.elim0 k)
  · rw [IsInt]
    by_cases h : ((⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ : Fin N) ∈ S)
    · exact fun hh => hh.2 ((IsBY_last hN S).mpr h)
    · exact fun hh => hh.1 ((IsBX_last hN S).mpr h)

lemma IsInt_lt {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    0 < j.val ∧ j.val < N := by
  have hjle : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
  constructor
  · rcases Nat.eq_zero_or_pos j.val with h0 | h0
    · exact absurd (show IsInt S 0 from
        (show j = 0 from Fin.ext (by simpa using h0)) ▸ h) (IsInt_zero S)
    · exact h0
  · rcases eq_or_lt_of_le hjle with hlt | hlt
    · exact absurd (show IsInt S (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) from
        (show j = ⟨N, Nat.lt_succ_self N⟩ from Fin.ext (by simpa using hlt)) ▸ h) (IsInt_last S)
    · exact hlt

lemma IsInt_step_ne {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    ((stepPrev j (IsInt_lt S j h).1 ∈ S) ≠ (stepCur j (IsInt_lt S j h).2 ∈ S)) := by
  obtain ⟨h1, h2⟩ := IsInt_lt S j h
  by_cases hA : stepPrev j h1 ∈ S <;> by_cases hB : stepCur j h2 ∈ S
  · exact absurd ((IsBY_iff_pos S h1 h2).mpr ⟨hA, hB⟩) h.2
  · simp [hA, hB]
  · simp [hA, hB]
  · exact absurd ((IsBX_iff_pos S h1 h2).mpr ⟨hA, hB⟩) h.1

lemma value_IsBX {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1))
    (h : ∀ v : Fin (N + 1), ANat S v.val = ANat S j.val → v = j) : IsBX S j := by
  intro k hk hkS
  have h1 : ANat S (k.val + 1) = ANat S k.val := by
    have hsucc := ANat_succ S k.isLt
    rw [if_pos hkS, add_zero] at hsucc
    exact hsucc
  have hkj : k.val ≤ j.val := by rcases hk with hk | hk <;> omega
  have hjk : j.val ≤ k.val + 1 := by rcases hk with hk | hk <;> omega
  have heq : ANat S k.val = ANat S j.val := by
    refine le_antisymm (ANat_mono S hkj) ?_
    calc ANat S j.val ≤ ANat S (k.val + 1) := ANat_mono S hjk
      _ = ANat S k.val := h1
  have hklt : k.val + 1 < N + 1 := by have := k.isLt; omega
  by_cases hcase : k.val + 1 = j.val
  · refine absurd (h ⟨k.val, by have := k.isLt; omega⟩ heq) ?_
    intro hc
    have hp := congrArg Fin.val hc
    simp only [Fin.val_mk] at hp
    omega
  · refine absurd (h ⟨k.val + 1, hklt⟩ (by rw [h1]; exact heq)) ?_
    intro hc
    have hp := congrArg Fin.val hc
    simp only [Fin.val_mk] at hp
    omega

lemma IsBX_pos_notMem {N : ℕ} (hN : 0 < N) (S : Finset (Fin N)) (j : Fin (N + 1))
    (h : IsBX S j) : ((⟨min j.val (N - 1), by omega⟩ : Fin N)) ∉ S := by
  rcases Nat.lt_or_ge (N - 1) j.val with hc | hc
  · have hfin : (⟨min j.val (N - 1), by omega⟩ : Fin N)
        = ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ :=
      Fin.ext (by simp only [Fin.val_mk]; rw [min_eq_right (by omega)])
    rw [hfin]
    have hjle : j.val ≤ N := Nat.lt_succ_iff.mp j.isLt
    exact h ⟨N - 1, Nat.sub_lt hN Nat.one_pos⟩ (Or.inl (by simp only [Fin.val_mk]; omega))
  · have hfin : (⟨min j.val (N - 1), by omega⟩ : Fin N) = ⟨j.val, by omega⟩ :=
      Fin.ext (by simp only [Fin.val_mk]; exact min_eq_left hc)
    rw [hfin]
    exact h ⟨j.val, by omega⟩ (Or.inr rfl)


/-! ## The interior involution -/

/-- The transposition exchanging `a` and `b`. -/
def swap2 {N : ℕ} (a b : Fin N) : Fin N → Fin N :=
  fun k => if k = a then b else if k = b then a else k

lemma swap2_self_left {N : ℕ} (a b : Fin N) : swap2 a b a = b := by
  rw [swap2, if_pos rfl]

lemma swap2_self_right {N : ℕ} (a b : Fin N) : swap2 a b b = a := by
  by_cases h : b = a
  · rw [swap2, if_pos h]; exact h
  · rw [swap2, if_neg h, if_pos rfl]

lemma swap2_of_ne {N : ℕ} (a b k : Fin N) (h1 : k ≠ a) (h2 : k ≠ b) : swap2 a b k = k := by
  rw [swap2, if_neg h1, if_neg h2]

lemma swap2_involutive {N : ℕ} (a b : Fin N) : Function.Involutive (swap2 a b) := by
  intro k
  by_cases h1 : k = a
  · rw [h1, swap2_self_left, swap2_self_right]
  · by_cases h2 : k = b
    · rw [h2, swap2_self_right, swap2_self_left]
    · rw [swap2_of_ne a b k h1 h2, swap2_of_ne a b k h1 h2]

lemma swap2_injective {N : ℕ} (a b : Fin N) : Function.Injective (swap2 a b) :=
  (swap2_involutive a b).injective

/-- Flip the two steps adjacent to the vertex `j` of a lattice path. -/
def flipS {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) : Finset (Fin N) :=
  if h : 0 < j.val ∧ j.val < N then
    (if stepPrev j h.1 ∈ S then insert (stepCur j h.2) (S.erase (stepPrev j h.1))
      else insert (stepPrev j h.1) (S.erase (stepCur j h.2)))
  else S

lemma flipS_of_pos {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1))
    (h1 : 0 < j.val) (h2 : j.val < N) :
    flipS S j = (if stepPrev j h1 ∈ S then insert (stepCur j h2) (S.erase (stepPrev j h1))
      else insert (stepPrev j h1) (S.erase (stepCur j h2))) := by
  rw [flipS, dif_pos ⟨h1, h2⟩]

lemma IsInt_iff {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) :
    IsInt S j ↔ ∃ (h1 : 0 < j.val) (h2 : j.val < N),
      ((stepPrev j h1 ∈ S) ≠ (stepCur j h2 ∈ S)) := by
  constructor
  · intro h
    exact ⟨(IsInt_lt S j h).1, (IsInt_lt S j h).2, IsInt_step_ne S j h⟩
  · rintro ⟨h1, h2, hne⟩
    constructor
    · intro hb
      rw [IsBX_iff_pos S h1 h2] at hb
      exact hne (propext (iff_of_false hb.1 hb.2))
    · intro hb
      rw [IsBY_iff_pos S h1 h2] at hb
      exact hne (propext (iff_of_true hb.1 hb.2))

lemma flipS_eq_image {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    flipS S j = S.image (swap2 (stepPrev j (IsInt_lt S j h).1)
      (stepCur j (IsInt_lt S j h).2)) := by
  obtain ⟨h1, h2⟩ := IsInt_lt S j h
  have hne := IsInt_step_ne S j h
  rw [flipS_of_pos S j h1 h2]
  by_cases hA : stepPrev j h1 ∈ S
  · have hB : stepCur j h2 ∉ S := fun hc => hne (propext (iff_of_true hA hc))
    rw [if_pos hA]
    ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro (rfl | ⟨hkA, hkS⟩)
      · exact ⟨stepPrev j h1, hA, swap2_self_left _ _⟩
      · exact ⟨k, hkS, swap2_of_ne _ _ _ hkA (fun hc => hB (hc ▸ hkS))⟩
    · rintro ⟨s, hs, hsk⟩
      by_cases hsa : s = stepPrev j h1
      · exact Or.inl (by rw [← hsk, hsa, swap2_self_left])
      · have hsB : s ≠ stepCur j h2 := fun hc => hB (hc ▸ hs)
        refine Or.inr ⟨?_, ?_⟩
        · rw [← hsk, swap2_of_ne _ _ _ hsa hsB]; exact hsa
        · rw [← hsk, swap2_of_ne _ _ _ hsa hsB]; exact hs
  · have hB : stepCur j h2 ∈ S := by
      by_contra hc
      exact hne (propext (iff_of_false hA hc))
    rw [if_neg hA]
    ext k
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro (rfl | ⟨hkB, hkS⟩)
      · exact ⟨stepCur j h2, hB, swap2_self_right _ _⟩
      · exact ⟨k, hkS, swap2_of_ne _ _ _ (fun hc => hA (hc ▸ hkS)) hkB⟩
    · rintro ⟨s, hs, hsk⟩
      by_cases hsb : s = stepCur j h2
      · exact Or.inl (by rw [← hsk, hsb, swap2_self_right])
      · have hsA : s ≠ stepPrev j h1 := fun hc => hA (hc ▸ hs)
        refine Or.inr ⟨?_, ?_⟩
        · rw [← hsk, swap2_of_ne _ _ _ hsA hsb]; exact hsb
        · rw [← hsk, swap2_of_ne _ _ _ hsA hsb]; exact hs


lemma flipS_mem_iff {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j)
    (k : Fin N) :
    k ∈ flipS S j ↔ swap2 (stepPrev j (IsInt_lt S j h).1) (stepCur j (IsInt_lt S j h).2) k ∈ S := by
  rw [flipS_eq_image S j h, Finset.mem_image]
  constructor
  · rintro ⟨s, hs, hsk⟩
    rw [← hsk, swap2_involutive]
    exact hs
  · intro hk
    exact ⟨_, hk, swap2_involutive _ _ k⟩

lemma flipS_card {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    (flipS S j).card = S.card := by
  rw [flipS_eq_image S j h]
  exact Finset.card_image_of_injective _ (swap2_injective _ _)

lemma IsInt_flipS {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    IsInt (flipS S j) j := by
  obtain ⟨h1, h2, hne⟩ := (IsInt_iff S j).mp h
  refine (IsInt_iff _ j).mpr ⟨h1, h2, ?_⟩
  rw [flipS_mem_iff S j h (stepPrev j h1), flipS_mem_iff S j h (stepCur j h2)]
  rw [swap2_self_left, swap2_self_right]
  exact fun heq => hne heq.symm

lemma flipS_flipS {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    flipS (flipS S j) j = S := by
  ext k
  rw [flipS_mem_iff (flipS S j) j (IsInt_flipS S j h) k]
  rw [flipS_mem_iff S j h]
  rw [swap2_involutive]

lemma flipS_ne {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    flipS S j ≠ S := by
  obtain ⟨h1, h2, hne⟩ := (IsInt_iff S j).mp h
  intro hc
  have e1 : (stepPrev j h1 ∈ S) ↔ (stepPrev j h1 ∈ flipS S j) := by rw [hc]
  have e2 : (stepPrev j h1 ∈ flipS S j) ↔ (stepCur j h2 ∈ S) := by
    rw [flipS_mem_iff S j h (stepPrev j h1), swap2_self_left]
  exact hne (propext (e1.trans e2))

lemma BNat_flipS {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) {v : ℕ}
    (hv : v ≠ j.val) : BNat (flipS S j) v = BNat S v := by
  obtain ⟨h1, h2, -⟩ := (IsInt_iff S j).mp h
  rw [BNat, BNat, flipS_eq_image S j h, Finset.filter_image,
    Finset.card_image_of_injective _ (swap2_injective _ _)]
  congr 1
  refine Finset.filter_congr (fun k hk => ?_)
  by_cases hkA : k = stepPrev j h1
  · rw [hkA, swap2_self_left, stepCur_val, stepPrev_val]
    constructor <;> intro hc <;> omega
  · by_cases hkB : k = stepCur j h2
    · rw [hkB, swap2_self_right, stepPrev_val, stepCur_val]
      constructor <;> intro hc <;> omega
    · rw [swap2_of_ne _ _ _ hkA hkB]

lemma ANat_flipS {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) {v : ℕ}
    (hv : v ≠ j.val) : ANat (flipS S j) v = ANat S v := by
  have h1 := ANat_add_BNat (flipS S j) v
  have h2 := ANat_add_BNat S v
  rw [BNat_flipS S j h hv] at h1
  omega


/-! ## The sign change of the interior involution -/

lemma BNat_insertN_insIdx {N : ℕ} (T : Finset (Fin (N - 1))) (p : Fin N) (k : Fin (N - 1)) :
    BNat (insertN T p) (insIdx p k).val
      = BNat T k.val + (if p.val ≤ k.val then 1 else 0) := by
  by_cases hk : k.val < p.val
  · rw [insIdx_lt p k hk]
    have hle : (⟨k.val, by have := k.isLt; omega⟩ : Fin N).val ≤ p.val := by
      show k.val ≤ p.val; omega
    rw [BNat_insertN, if_pos hle, if_neg (by omega : ¬ p.val ≤ k.val), add_zero]
  · rw [insIdx_ge p k hk]
    have hle : ¬ (⟨k.val + 1, by have := k.isLt; have := p.isLt; omega⟩ : Fin N).val ≤ p.val := by
      show ¬ (k.val + 1 ≤ p.val); omega
    rw [BNat_insertN, if_neg hle, if_pos (by omega : p.val ≤ k.val)]
    have hval : (⟨k.val + 1, by have := k.isLt; have := p.isLt; omega⟩ : Fin N).val - 1
        = (k : ℕ) := by
      show k.val + 1 - 1 = k.val; omega
    rw [hval]

lemma compl_insertN {N : ℕ} (T : Finset (Fin (N - 1))) (p : Fin N) :
    (Finset.univ : Finset (Fin N)) \ insertN T p
      = ((Finset.univ : Finset (Fin (N - 1))) \ T).image (insIdx p) := by
  ext k
  rw [Finset.mem_sdiff, Finset.mem_image]
  constructor
  · intro hk
    have hkp : k ≠ p := fun hc =>
      hk.2 (by rw [insertN, hc]; exact Finset.mem_insert_self _ _)
    have hk2 : k ∉ insertE T p := fun hc =>
      hk.2 (by rw [insertN]; exact Finset.mem_insert_of_mem hc)
    obtain ⟨k', hk'⟩ := insIdx_surj p k hkp
    refine ⟨k', ?_, hk'⟩
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, fun hk'T => hk2 (by rw [mem_insertE]; exact ⟨k', hk'T, hk'⟩)⟩
  · rintro ⟨k', hk', hk'k⟩
    rw [Finset.mem_sdiff] at hk'
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmem
    rw [insertN, Finset.mem_insert] at hmem
    rcases hmem with hkp | hmem
    · rw [← hk'k] at hkp; exact insIdx_ne p k' hkp
    · rw [mem_insertE] at hmem
      obtain ⟨k'', hk''T, hk''⟩ := hmem
      rw [← hk'k] at hk''
      exact hk'.2 (insIdx_injective p hk'' ▸ hk''T)

lemma invCountN_insertN {N : ℕ} (T : Finset (Fin (N - 1))) (p : Fin N) :
    invCountN (insertN T p) = invCountN T + (((N - 1) - T.card) - ANat T p.val) := by
  have hstep : (∑ k ∈ ((Finset.univ : Finset (Fin (N - 1))) \ T),
        BNat (insertN T p) (insIdx p k).val)
      = ∑ k ∈ ((Finset.univ : Finset (Fin (N - 1))) \ T),
        (BNat T k.val + (if p.val ≤ k.val then 1 else 0)) :=
    Finset.sum_congr rfl (fun k _ => BNat_insertN_insIdx T p k)
  rw [invCountN, compl_insertN,
    Finset.sum_image (fun x _ y _ hxy => insIdx_injective p hxy), hstep,
    Finset.sum_add_distrib, invCountN]
  congr 1
  rw [← Finset.card_filter]
  set V := (Finset.univ : Finset (Fin (N - 1))) \ T with hVdef
  have hV : V.card = (N - 1) - T.card := by
    rw [hVdef, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hVlt : (V.filter (fun k => k.val < p.val)).card = ANat T p.val := by
    rw [ANat]
    congr 1
    rw [hVdef]
    ext k
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  have hset : V.filter (fun k => p.val ≤ k.val) = V \ (V.filter (fun k => k.val < p.val)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hk, hle⟩
      exact ⟨hk, fun hc => absurd hc.2 (by omega)⟩
    · rintro ⟨hk, hnot⟩
      exact ⟨hk, by by_contra hc; exact hnot ⟨hk, by omega⟩⟩
  rw [hset, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hVlt, hV]


lemma neg_one_pow_succ (k : ℕ) : (-1 : ℤ) ^ (k + 1) = -((-1) ^ k) := by
  rw [pow_succ]; ring

lemma invCountN_flipS_aux {N : ℕ} (S : Finset (Fin N)) {a b : Fin N} (ha : a ∈ S) (hb : b ∉ S)
    (hval : b.val = a.val + 1)
    (hB : ∀ t : Fin N, t ∉ S → t ≠ b → BNat (insert b (S.erase a)) t.val = BNat S t.val)
    (hA : BNat (insert b (S.erase a)) a.val = BNat S a.val) :
    invCountN (insert b (S.erase a)) + 1 = invCountN S := by
  have hab : a ≠ b := by intro hc; exact hb (hc ▸ ha)
  have hcompl : (Finset.univ : Finset (Fin N)) \ (insert b (S.erase a))
      = (((Finset.univ : Finset (Fin N)) \ S) \ {b}) ∪ {a} := by
    ext k
    rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff,
      Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hk⟩
      rw [not_or] at hk
      by_cases hka : k = a
      · exact Or.inr hka
      · exact Or.inl ⟨⟨Finset.mem_univ k, fun hkS => hk.2 ⟨hka, hkS⟩⟩, hk.1⟩
    · rintro (⟨⟨-, hkS⟩, hkb⟩ | hka)
      · refine ⟨Finset.mem_univ k, ?_⟩
        rw [not_or]
        exact ⟨hkb, fun hc => hkS hc.2⟩
      · refine ⟨Finset.mem_univ k, ?_⟩
        rw [not_or]
        exact ⟨fun hc => hab (hka.symm.trans hc), fun hc => hc.1 hka⟩
  have hdisj : Disjoint (((Finset.univ : Finset (Fin N)) \ S) \ {b}) {a} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_sdiff, Finset.mem_sdiff]
    exact fun hc => hc.1.2 ha
  have hsum : (∑ t ∈ (((Finset.univ : Finset (Fin N)) \ S) \ {b}),
        BNat (insert b (S.erase a)) t.val)
      = ∑ t ∈ (((Finset.univ : Finset (Fin N)) \ S) \ {b}), BNat S t.val := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_sdiff, Finset.mem_sdiff, Finset.mem_singleton] at ht
    exact hB t ht.1.2 ht.2
  have hbS : b ∈ (Finset.univ : Finset (Fin N)) \ S :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hb⟩
  have hsplit : invCountN S
      = (∑ t ∈ (((Finset.univ : Finset (Fin N)) \ S) \ {b}), BNat S t.val)
        + BNat S b.val := by
    rw [invCountN, ← Finset.sum_sdiff (show ({b} : Finset (Fin N)) ⊆
      (Finset.univ : Finset (Fin N)) \ S from by
        intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact hbS)]
    rw [Finset.sum_singleton]
  have hbval : BNat S b.val = BNat S a.val + 1 := by
    have hlt : a.val < N := by have := b.isLt; omega
    rw [hval, BNat_succ S hlt]
    rw [if_pos (show (⟨a.val, hlt⟩ : Fin N) ∈ S from ha)]
  rw [invCountN, hcompl]
  rw [Finset.sum_union hdisj, Finset.sum_singleton, hsum, hA]
  omega

lemma invCountN_flipS_dich {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    invCountN (flipS S j) + 1 = invCountN S ∨ invCountN (flipS S j) = invCountN S + 1 := by
  obtain ⟨h1, h2, hne⟩ := (IsInt_iff S j).mp h
  have hABne : stepPrev j h1 ≠ stepCur j h2 := by
    intro hc
    have hv := congrArg Fin.val hc
    rw [stepPrev_val, stepCur_val] at hv
    omega
  have hvalAB : (stepCur j h2).val = (stepPrev j h1).val + 1 := by
    rw [stepCur_val, stepPrev_val]; omega
  have hAjN : (stepPrev j h1).val < N := by
    rw [stepPrev_val]; have := (IsInt_lt S j h).1; omega
  have hBjN : (stepCur j h2).val < N := by
    rw [stepCur_val]; exact (stepCur j h2).isLt
  by_cases hmem : stepPrev j h1 ∈ S
  · left
    have hBnot : stepCur j h2 ∉ S := fun hc => hne (propext (iff_of_true hmem hc))
    have hflip : flipS S j = insert (stepCur j h2) (S.erase (stepPrev j h1)) := by
      rw [flipS_of_pos S j h1 h2, if_pos hmem]
    rw [hflip]
    refine invCountN_flipS_aux S hmem hBnot hvalAB ?_ ?_
    · intro t ht htb
      rw [← hflip]
      refine BNat_flipS S j h ?_
      intro hc
      exact htb (Fin.ext (by rw [hc, stepCur_val]))
    · rw [← hflip]
      refine BNat_flipS S j h ?_
      rw [stepPrev_val]
      omega
  · right
    have hBmem : stepCur j h2 ∈ S := by
      by_contra hc
      exact hne (propext (iff_of_false hmem hc))
    have hflip : flipS S j = insert (stepPrev j h1) (S.erase (stepCur j h2)) := by
      rw [flipS_of_pos S j h1 h2, if_neg hmem]
    have hcompl : (Finset.univ : Finset (Fin N)) \ (insert (stepPrev j h1) (S.erase (stepCur j h2)))
        = (((Finset.univ : Finset (Fin N)) \ S) \ {stepPrev j h1}) ∪ {stepCur j h2} := by
      ext k
      rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff,
        Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hk⟩
        rw [not_or] at hk
        by_cases hkb : k = stepCur j h2
        · exact Or.inr hkb
        · exact Or.inl ⟨⟨Finset.mem_univ k, fun hkS => hk.2 ⟨hkb, hkS⟩⟩, hk.1⟩
      · rintro (⟨⟨-, hkS⟩, hka⟩ | hkb)
        · refine ⟨Finset.mem_univ k, ?_⟩
          rw [not_or]
          exact ⟨hka, fun hc => hkS hc.2⟩
        · refine ⟨Finset.mem_univ k, ?_⟩
          rw [not_or]
          exact ⟨fun hc => hABne (hkb.symm.trans hc).symm, fun hc => hc.1 hkb⟩
    have hdisj : Disjoint (((Finset.univ : Finset (Fin N)) \ S) \ {stepPrev j h1})
        {stepCur j h2} := by
      rw [Finset.disjoint_singleton_right, Finset.mem_sdiff, Finset.mem_sdiff]
      exact fun hc => hc.1.2 hBmem
    have hsum : (∑ t ∈ (((Finset.univ : Finset (Fin N)) \ S) \ {stepPrev j h1}),
          BNat (insert (stepPrev j h1) (S.erase (stepCur j h2))) t.val)
        = ∑ t ∈ (((Finset.univ : Finset (Fin N)) \ S) \ {stepPrev j h1}), BNat S t.val := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      have htS : t ∉ S := by
        rw [Finset.mem_sdiff, Finset.mem_sdiff] at ht
        exact ht.1.2
      rw [← hflip]
      refine BNat_flipS S j h (fun hc => ?_)
      have heq : t = stepCur j h2 := Fin.ext (by show t.val = j.val; exact hc)
      exact htS (heq ▸ hBmem)
    have haS : stepPrev j h1 ∈ (Finset.univ : Finset (Fin N)) \ S :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hmem⟩
    have hsplit : invCountN S
        = (∑ t ∈ (((Finset.univ : Finset (Fin N)) \ S) \ {stepPrev j h1}), BNat S t.val)
          + BNat S (stepPrev j h1).val := by
      rw [invCountN, ← Finset.sum_sdiff (show ({stepPrev j h1} : Finset (Fin N)) ⊆
        (Finset.univ : Finset (Fin N)) \ S from by
          intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact haS)]
      rw [Finset.sum_singleton]
    have hbval : BNat S (stepCur j h2).val = BNat S (stepPrev j h1).val := by
      rw [hvalAB, BNat_succ S hAjN, if_neg hmem, add_zero]
    have hnew : BNat (insert (stepPrev j h1) (S.erase (stepCur j h2))) (stepCur j h2).val
        = BNat S (stepPrev j h1).val + 1 := by
      have hmemX : (⟨(stepPrev j h1).val, hAjN⟩ : Fin N) ∈ flipS S j := by
        rw [flipS_mem_iff S j h, swap2_self_left]
        exact hBmem
      have hfin : (⟨(stepPrev j h1).val, hAjN⟩ : Fin N) = stepPrev j h1 := Fin.ext rfl
      rw [← hflip, hvalAB, BNat_succ (flipS S j) hAjN,
        if_pos (by rw [hfin]; exact hmemX), BNat_flipS S j h (by rw [stepPrev_val]; omega)]
    rw [invCountN, hflip, hcompl]
    rw [Finset.sum_union hdisj, Finset.sum_singleton, hsum, hnew]
    omega

lemma shufSignN_flipS {N : ℕ} (S : Finset (Fin N)) (j : Fin (N + 1)) (h : IsInt S j) :
    shufSignN (flipS S j) = - shufSignN S := by
  rcases invCountN_flipS_dich S j h with hc | hc
  · rw [shufSignN, shufSignN, ← hc, neg_one_pow_succ]
    ring
  · rw [shufSignN, shufSignN, hc, neg_one_pow_succ]

end

end Work.SSSR.KunnethEZ
