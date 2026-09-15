import Mathlib
import Submission.Commons.Combinatorics.Ramsey.mdhj_of_dhj
import Submission.Commons.Combinatorics.Ramsey.kvec_injective

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Part 0: three-block concatenation -/

/-- Concatenate `a`, `z`, `c` (blocks of lengths `A`, `M`, `C`) into a word of length `n`. -/
def dktCat3 {α : Type*} {A M C n : ℕ} (h : A + M + C = n) (a : Fin A → α) (z : Fin M → α)
    (c : Fin C → α) : Fin n → α :=
  fun i => if h1 : (i:ℕ) < A then a ⟨i, h1⟩
    else if h2 : (i:ℕ) < A + M then z ⟨(i:ℕ) - A, by omega⟩
    else c ⟨(i:ℕ) - A - M, by omega⟩

lemma dktCat3_apply_lt {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) (i : Fin n) (hi : (i:ℕ) < A) :
    dktCat3 h a z c i = a ⟨i, hi⟩ := dif_pos hi

lemma dktCat3_apply_mid {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) (i : Fin n)
    (h1 : A ≤ (i:ℕ)) (h2 : (i:ℕ) < A + M) :
    dktCat3 h a z c i = z ⟨(i:ℕ) - A, by omega⟩ := by
  rw [dktCat3, dif_neg (by omega), dif_pos h2]

lemma dktCat3_apply_ge {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) (i : Fin n)
    (h1 : A + M ≤ (i:ℕ)) :
    dktCat3 h a z c i = c ⟨(i:ℕ) - A - M, by omega⟩ := by
  rw [dktCat3, dif_neg (by omega), dif_neg (by omega)]

/-- Left block of a word. -/
def dktResA {α : Type*} {A M C n : ℕ} (h : A + M + C = n) (x : Fin n → α) : Fin A → α :=
  fun i => x ⟨i, by omega⟩

/-- Middle block of a word. -/
def dktMid {α : Type*} {A M C n : ℕ} (h : A + M + C = n) (x : Fin n → α) : Fin M → α :=
  fun i => x ⟨A + (i:ℕ), by omega⟩

/-- Right block of a word. -/
def dktDelC {α : Type*} {A M C n : ℕ} (h : A + M + C = n) (x : Fin n → α) : Fin C → α :=
  fun j => x ⟨A + M + (j:ℕ), by omega⟩

lemma dktResA_cat3 {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) :
    dktResA h (dktCat3 h a z c) = a := by
  funext i
  rw [dktResA, dktCat3_apply_lt h a z c _ i.2]

lemma dktDelC_cat3 {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) :
    dktDelC h (dktCat3 h a z c) = c := by
  funext j
  rw [dktDelC, dktCat3_apply_ge h a z c _ (by simp only [Fin.val_mk]; omega)]
  exact congrArg c (Fin.ext (by simp only [Fin.val_mk]; omega))

lemma dktMid_cat3 {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) :
    dktMid h (dktCat3 h a z c) = z := by
  funext j
  rw [dktMid, dktCat3_apply_mid h a z c _ (by simp only [Fin.val_mk]; omega)
    (by simp only [Fin.val_mk]; omega)]
  exact congrArg z (Fin.ext (by simp only [Fin.val_mk]; omega))

lemma dktCat3_res_mid_del {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (x : Fin n → α) :
    dktCat3 h (dktResA h x) (dktMid h x) (dktDelC h x) = x := by
  funext i
  by_cases h1 : (i:ℕ) < A
  · rw [dktCat3_apply_lt h _ _ _ i h1, dktResA]
  · by_cases h2 : (i:ℕ) < A + M
    · rw [dktCat3_apply_mid h _ _ _ i (by omega) h2, dktMid]
      exact congrArg x (Fin.ext (by simp only [Fin.val_mk]; omega))
    · rw [dktCat3_apply_ge h _ _ _ i (by omega), dktDelC]
      exact congrArg x (Fin.ext (by simp only [Fin.val_mk]; omega))

/-- Slicing sum for a three-block decomposition. -/
lemma dktCard_eq_sum_cat3 {α : Type*} [Fintype α] [DecidableEq α] {A M C n : ℕ}
    (h : A + M + C = n) (T : Finset (Fin n → α)) :
    T.card = ∑ p : (Fin A → α) × (Fin C → α),
      ((Finset.univ : Finset (Fin M → α)).filter (fun z => dktCat3 h p.1 z p.2 ∈ T)).card := by
  have hfib : T.card = ∑ p : (Fin A → α) × (Fin C → α),
      (T.filter (fun x => (dktResA h x, dktDelC h x) = p)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : Fin n → α => (dktResA h x, dktDelC h x))
      (s := T) (t := Finset.univ) (fun a _ => Finset.mem_univ _)]
  rw [hfib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  refine Finset.card_bij (fun x _ => dktMid h x) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxT, hxp⟩ := hx
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : p.1 = dktResA h x := (congrArg Prod.fst hxp).symm
    have h2 : p.2 = dktDelC h x := (congrArg Prod.snd hxp).symm
    rw [h1, h2, dktCat3_res_mid_del h x]
    exact hxT
  · intro x hx x' hx' heq
    rw [Finset.mem_filter] at hx hx'
    obtain ⟨hxT, hxp⟩ := hx
    obtain ⟨hx'T, hx'p⟩ := hx'
    have h1 : p.1 = dktResA h x := (congrArg Prod.fst hxp).symm
    have h2 : p.2 = dktDelC h x := (congrArg Prod.snd hxp).symm
    have h1' : p.1 = dktResA h x' := (congrArg Prod.fst hx'p).symm
    have h2' : p.2 = dktDelC h x' := (congrArg Prod.snd hx'p).symm
    calc x = dktCat3 h (dktResA h x) (dktMid h x) (dktDelC h x) := (dktCat3_res_mid_del h x).symm
      _ = dktCat3 h p.1 (dktMid h x) p.2 := by rw [h1, h2]
      _ = dktCat3 h p.1 (dktMid h x') p.2 := by rw [heq]
      _ = dktCat3 h (dktResA h x') (dktMid h x') (dktDelC h x') := by rw [h1', h2']
      _ = x' := dktCat3_res_mid_del h x'
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨dktCat3 h p.1 z p.2, ?_, dktMid_cat3 h p.1 z p.2⟩
    rw [Finset.mem_filter]
    exact ⟨hz.2, by rw [dktResA_cat3, dktDelC_cat3]⟩


/-! ## Part 0b: two-block concatenation -/

/-- Concatenate `v` (length `B`) and `c` (length `C`). -/
def dktCat2 {α : Type*} {B C n : ℕ} (h : B + C = n) (v : Fin B → α) (c : Fin C → α) :
    Fin n → α :=
  fun i => if hi : (i:ℕ) < B then v ⟨i, hi⟩ else c ⟨(i:ℕ) - B, by omega⟩

lemma dktCat2_apply_lt {α : Type*} {B C n : ℕ} (h : B + C = n)
    (v : Fin B → α) (c : Fin C → α) (i : Fin n) (hi : (i:ℕ) < B) :
    dktCat2 h v c i = v ⟨i, hi⟩ := dif_pos hi

lemma dktCat2_apply_ge {α : Type*} {B C n : ℕ} (h : B + C = n)
    (v : Fin B → α) (c : Fin C → α) (i : Fin n) (hi : ¬ (i:ℕ) < B) :
    dktCat2 h v c i = c ⟨(i:ℕ) - B, by omega⟩ := dif_neg hi

/-- Prefix block of a word. -/
def dktPre2 {α : Type*} {B C n : ℕ} (h : B + C = n) (x : Fin n → α) : Fin B → α :=
  fun i => x ⟨i, by omega⟩

/-- Suffix block of a word. -/
def dktSuf2 {α : Type*} {B C n : ℕ} (h : B + C = n) (x : Fin n → α) : Fin C → α :=
  fun j => x ⟨B + (j:ℕ), by omega⟩

lemma dktCat2_pre_suf {α : Type*} {B C n : ℕ} (h : B + C = n) (x : Fin n → α) :
    dktCat2 h (dktPre2 h x) (dktSuf2 h x) = x := by
  funext i
  by_cases hi : (i:ℕ) < B
  · rw [dktCat2_apply_lt h _ _ i hi, dktPre2]
  · rw [dktCat2_apply_ge h _ _ i hi, dktSuf2]
    exact congrArg x (Fin.ext (by simp only [Fin.val_mk]; omega))

lemma dktPre2_cat2 {α : Type*} {B C n : ℕ} (h : B + C = n)
    (v : Fin B → α) (c : Fin C → α) : dktPre2 h (dktCat2 h v c) = v := by
  funext i
  rw [dktPre2, dktCat2_apply_lt h v c _ i.2]

lemma dktSuf2_cat2 {α : Type*} {B C n : ℕ} (h : B + C = n)
    (v : Fin B → α) (c : Fin C → α) : dktSuf2 h (dktCat2 h v c) = c := by
  funext j
  rw [dktSuf2, dktCat2_apply_ge h v c _ (by simp only [Fin.val_mk]; omega)]
  exact congrArg c (Fin.ext (by simp only [Fin.val_mk]; omega))

lemma dktCat2_comp3 {α : Type*} {A M C n B : ℕ} (h : A + M + C = n) (h1 : A + M = B)
    (h2 : B + C = n) (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) :
    dktCat2 h2 (dktCat2 h1 a z) c = dktCat3 h a z c := by
  funext i
  by_cases hi : (i:ℕ) < A
  · rw [dktCat2_apply_lt h2 _ _ i (by omega), dktCat2_apply_lt h1 _ _ _ hi,
      dktCat3_apply_lt h a z c i hi]
  · by_cases hi2 : (i:ℕ) < B
    · rw [dktCat2_apply_lt h2 _ _ i hi2, dktCat2_apply_ge h1 _ _ _ (by omega),
        dktCat3_apply_mid h a z c i (by omega) (by omega)]
    · rw [dktCat2_apply_ge h2 _ _ _ hi2, dktCat3_apply_ge h a z c i (by omega)]
      exact congrArg c (Fin.ext (by simp only [Fin.val_mk]; omega))

/-! ## Part 1: insensitivity is preserved by coordinate-fixing maps -/

/-- The word relation underlying `IsInsens`. -/
def dktRel {k : ℕ} (i : Fin k) {n : ℕ} (x y : Fin n → Fin (k+1)) : Prop :=
  ∀ j, y j = x j ∨ (x j = Fin.last k ∧ y j = Fin.castSucc i) ∨
    (y j = Fin.last k ∧ x j = Fin.castSucc i)

lemma dktRel.symm {k n : ℕ} {i : Fin k} {x y : Fin n → Fin (k+1)} (h : dktRel i x y) :
    dktRel i y x := by
  intro j
  rcases h j with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1.symm
  · exact Or.inr (Or.inr ⟨h1, h2⟩)
  · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-- Preimage of an insensitive set under a relation-preserving map. -/
lemma dktIsInsens_filter {k n n' : ℕ} {i : Fin k} {D : Finset (Fin n → Fin (k+1))}
    (hD : IsInsens i D) (φ : (Fin n' → Fin (k+1)) → (Fin n → Fin (k+1)))
    (hφ : ∀ x y, dktRel i x y → dktRel i (φ x) (φ y)) :
    IsInsens i (Finset.univ.filter (fun x => φ x ∈ D)) := by
  intro x hx y hy
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_univ _, hD (φ x) hx.2 (φ y) (hφ x y hy)⟩

/-- Slicing an insensitive set by the right block preserves insensitivity. -/
lemma dktRel_cat2_right {k B C n : ℕ} {i : Fin k} {x y : Fin B → Fin (k+1)}
    (hxy : dktRel i x y) (h : B + C = n) (c : Fin C → Fin (k+1)) :
    dktRel i (dktCat2 h x c) (dktCat2 h y c) := by
  intro j
  by_cases hj : (j:ℕ) < B
  · rw [dktCat2_apply_lt h x c j hj, dktCat2_apply_lt h y c j hj]
    exact hxy ⟨j, hj⟩
  · rw [dktCat2_apply_ge h x c j hj, dktCat2_apply_ge h y c j hj]
    exact Or.inl rfl

/-- Slicing an insensitive set by the left block preserves insensitivity. -/
lemma dktRel_cat2_left {k B C n : ℕ} {i : Fin k} {z w : Fin C → Fin (k+1)}
    (hzw : dktRel i z w) (h : B + C = n) (a : Fin B → Fin (k+1)) :
    dktRel i (dktCat2 h a z) (dktCat2 h a w) := by
  intro j
  by_cases hj : (j:ℕ) < B
  · rw [dktCat2_apply_lt h a z j hj, dktCat2_apply_lt h a w j hj]
    exact Or.inl rfl
  · rw [dktCat2_apply_ge h a z j hj, dktCat2_apply_ge h a w j hj]
    exact hzw ⟨(j:ℕ) - B, by omega⟩

lemma dktIsInsens_slice2_right {k B C n : ℕ} {i : Fin k} {D : Finset (Fin n → Fin (k+1))}
    (hD : IsInsens i D) (h : B + C = n) (c : Fin C → Fin (k+1)) :
    IsInsens i (Finset.univ.filter (fun v : Fin B → Fin (k+1) => dktCat2 h v c ∈ D)) :=
  dktIsInsens_filter hD (fun v => dktCat2 h v c) (fun _ _ hxy => dktRel_cat2_right hxy h c)

lemma dktIsInsens_slice2_left {k B C n : ℕ} {i : Fin k} {D : Finset (Fin n → Fin (k+1))}
    (hD : IsInsens i D) (h : B + C = n) (a : Fin B → Fin (k+1)) :
    IsInsens i (Finset.univ.filter (fun z : Fin C → Fin (k+1) => dktCat2 h a z ∈ D)) :=
  dktIsInsens_filter hD (fun z => dktCat2 h a z) (fun _ _ hxy => dktRel_cat2_left hxy h a)

lemma dktIsInsens_sdiff {k n : ℕ} {i : Fin k} {D E : Finset (Fin n → Fin (k+1))}
    (hD : IsInsens i D) (hE : IsInsens i E) : IsInsens i (D \ E) := by
  intro x hx y hy
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨hD x hx.1 y hy, ?_⟩
  intro hc
  exact hx.2 (hE y hc x (dktRel.symm hy))

/-! ## Part 2: a dense set that is insensitive contains a whole subspace -/

/-- If `A` is insensitive and a subspace maps `kvec` into `A`, then all of `A` contains the image. -/
lemma dktSubImage_subset_of_insens {k d M : ℕ} {i : Fin k}
    {A : Finset (Fin M → Fin (k+1))} (hA : IsInsens i A)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (hV : ∀ x : Fin d → Fin k, V (kvec x) ∈ A) :
    ∀ u : Fin d → Fin (k+1), V u ∈ A := by
  intro u
  set x : Fin d → Fin k := fun e =>
    if he : u e = Fin.last k then i
    else ⟨(u e : ℕ), Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (u e).isLt)
      (fun hc => he (Fin.ext (by simp [hc])))⟩ with hx
  have hrel : dktRel i (V (kvec x)) (V u) := by
    intro p
    cases hp : V.idxFun p with
    | inl a =>
      have e1 : V (kvec x) p = a := by simp [Subspace.coe_apply, hp]
      have e2 : V u p = a := by simp [Subspace.coe_apply, hp]
      rw [e1, e2]; exact Or.inl rfl
    | inr e =>
      have e1 : V (kvec x) p = (kvec x) e := by simp [Subspace.coe_apply, hp]
      have e2 : V u p = u e := by simp [Subspace.coe_apply, hp]
      have hxe : kvec x e = Fin.castSucc (x e) := rfl
      rw [e1, e2, hxe]
      by_cases hue : u e = Fin.last k
      · have hx1 : x e = i := by rw [hx]; exact dif_pos hue
        rw [hx1]
        exact Or.inr (Or.inr ⟨hue, rfl⟩)
      · have hx1 : x e = ⟨(u e : ℕ), Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (u e).isLt)
            (fun hc => hue (Fin.ext (by simp [hc])))⟩ := by rw [hx]; exact dif_neg hue
        have hcast : Fin.castSucc (x e) = u e := by
          rw [hx1]
          apply Fin.ext
          simp only [Fin.val_castSucc, Fin.val_mk]
        rw [hcast]
        exact Or.inl rfl
  exact hA (V (kvec x)) (hV x) (V u) hrel



/-! ## Part 2b: slices and fibres -/

/-- The slice of `E` through the suffix `c`. -/
def dktSlice2 {α : Type*} [Fintype α] [DecidableEq α] {B C n : ℕ} (h : B + C = n)
    (E : Finset (Fin n → α)) (c : Fin C → α) : Finset (Fin B → α) :=
  Finset.univ.filter (fun v => dktCat2 h v c ∈ E)

lemma mem_dktSlice2 {α : Type*} [Fintype α] [DecidableEq α] {B C n : ℕ} {h : B + C = n}
    {E : Finset (Fin n → α)} {c : Fin C → α} {v : Fin B → α} :
    v ∈ dktSlice2 h E c ↔ dktCat2 h v c ∈ E := by
  simp [dktSlice2]

/-- The fibre of `E` through `(a,c)`. -/
def dktFib {α : Type*} [Fintype α] [DecidableEq α] {A M C n : ℕ} (h : A + M + C = n)
    (E : Finset (Fin n → α)) (a : Fin A → α) (c : Fin C → α) : Finset (Fin M → α) :=
  Finset.univ.filter (fun z => dktCat3 h a z c ∈ E)

lemma mem_dktFib {α : Type*} [Fintype α] [DecidableEq α] {A M C n : ℕ} {h : A + M + C = n}
    {E : Finset (Fin n → α)} {a : Fin A → α} {c : Fin C → α} {z : Fin M → α} :
    z ∈ dktFib h E a c ↔ dktCat3 h a z c ∈ E := by
  simp [dktFib]

lemma dktCat3_eq_cat2 {α : Type*} {A M C B n : ℕ} (h : A + M + C = n) (hAB : A + M = B)
    (hB : B + C = n) (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) :
    dktCat3 h a z c = dktCat2 hB (dktCat2 hAB a z) c := by
  funext i
  by_cases h1 : (i:ℕ) < A
  · rw [dktCat3_apply_lt h a z c i h1, dktCat2_apply_lt hB _ _ i (by omega),
      dktCat2_apply_lt hAB _ _ _ h1]
  · by_cases h2 : (i:ℕ) < B
    · rw [dktCat3_apply_mid h a z c i (by omega) (by omega), dktCat2_apply_lt hB _ _ i h2,
        dktCat2_apply_ge hAB _ _ _ (by omega)]
    · rw [dktCat3_apply_ge h a z c i (by omega), dktCat2_apply_ge hB _ _ _ h2]
      exact congrArg c (Fin.ext (by simp only [Fin.val_mk]; omega))

lemma dktFib_insens {k A M C B n : ℕ} {i : Fin k} (h : A + M + C = n) (hAB : A + M = B)
    (hB : B + C = n) {E : Finset (Fin n → Fin (k+1))} {a : Fin A → Fin (k+1)}
    {c : Fin C → Fin (k+1)} (hP : IsInsens i (dktSlice2 hB E c)) :
    IsInsens i (dktFib h E a c) := by
  have heq : (Finset.univ.filter (fun z : Fin M → Fin (k+1) =>
      dktCat2 hAB a z ∈ dktSlice2 hB E c)) = dktFib h E a c := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_dktFib, mem_dktSlice2,
      ← dktCat3_eq_cat2 h hAB hB a z c]
  rw [← heq]
  exact dktIsInsens_filter hP (φ := fun z : Fin M → Fin (k+1) => dktCat2 hAB a z)
    (fun x y hxy => dktRel_cat2_left hxy hAB a)

lemma dktFib_card_le {α : Type*} [Fintype α] [DecidableEq α] {A M C n : ℕ} {h : A + M + C = n}
    {E : Finset (Fin n → α)} (a : Fin A → α) (c : Fin C → α) :
    (dktFib h E a c).card ≤ Fintype.card α ^ M := by
  rw [dktFib]
  have h1 : (Finset.univ.filter (fun z => dktCat3 h a z c ∈ E)).card
      ≤ (Finset.univ : Finset (Fin M → α)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
  exact h1

lemma dktCard_eq_sum_fib {α : Type*} [Fintype α] [DecidableEq α] {A M C n : ℕ}
    (h : A + M + C = n) (E : Finset (Fin n → α)) :
    E.card = ∑ p : (Fin A → α) × (Fin C → α), (dktFib h E p.1 p.2).card := by
  rw [dktCard_eq_sum_cat3 h E]
  simp only [dktFib]

lemma dktCard_cast_eq_sum_fib {α : Type*} [Fintype α] [DecidableEq α] {A M C n : ℕ}
    (h : A + M + C = n) (E : Finset (Fin n → α)) :
    (E.card : ℝ) = ∑ p : (Fin A → α) × (Fin C → α), ((dktFib h E p.1 p.2).card : ℝ) := by
  rw [dktCard_eq_sum_fib h E, Nat.cast_sum]

/-! ## Part 2d: extraction lemmas for the two-block gluing -/

lemma dktCat2_assoc3 {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (h' : A + (M + C) = n) (a : Fin A → α) (z : Fin M → α) (c : Fin C → α) :
    dktCat2 h' a (dktCat2 rfl z c) = dktCat3 h a z c := by
  funext i
  by_cases hi : (i:ℕ) < A
  · rw [dktCat2_apply_lt h' _ _ i hi, dktCat3_apply_lt h a z c i hi]
  · by_cases hi2 : (i:ℕ) < A + M
    · rw [dktCat2_apply_ge h' _ _ _ hi, dktCat2_apply_lt rfl z c _
        (by simp only [Fin.val_mk]; omega),
        dktCat3_apply_mid h a z c i (by omega) hi2]
    · rw [dktCat2_apply_ge h' _ _ _ hi, dktCat2_apply_ge rfl z c _
        (by simp only [Fin.val_mk]; omega),
        dktCat3_apply_ge h a z c i (by omega)]

lemma dktResA_cat2 {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (h' : A + (M + C) = n) (a : Fin A → α) (c' : Fin (M + C) → α) :
    dktResA h (dktCat2 h' a c') = a := by
  funext i
  rw [dktResA, dktCat2_apply_lt h' a c' _ i.2]

lemma dktMid_cat2 {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (h' : A + (M + C) = n) (a : Fin A → α) (c' : Fin (M + C) → α) :
    dktMid h (dktCat2 h' a c') = dktPre2 rfl c' := by
  funext i
  rw [dktMid, dktCat2_apply_ge h' a c' _ (by simp only [Fin.val_mk]; omega), dktPre2]
  exact congrArg c' (Fin.ext (by simp only [Fin.val_mk]; omega))

lemma dktDelC_cat2 {α : Type*} {A M C n : ℕ} (h : A + M + C = n)
    (h' : A + (M + C) = n) (a : Fin A → α) (c' : Fin (M + C) → α) :
    dktDelC h (dktCat2 h' a c') = dktSuf2 rfl c' := by
  funext j
  rw [dktDelC, dktCat2_apply_ge h' a c' _ (by simp only [Fin.val_mk]; omega), dktSuf2]
  exact congrArg c' (Fin.ext (by simp only [Fin.val_mk]; omega))

/-! ## Part 3: points, families and the step -/

/-- Distinct points of a subspace have distinct images under the subspace map. -/
lemma dktSubspace_injective {k d M : ℕ} (V : Subspace (Fin d) (Fin (k+1)) (Fin M)) :
    Function.Injective (fun u : Fin d → Fin (k+1) => V u) := by
  intro u u' h
  funext e
  obtain ⟨p, hp⟩ := V.proper e
  have h1 : V u p = u e := by simp [Subspace.coe_apply, hp]
  have h2 : V u' p = u' e := by simp [Subspace.coe_apply, hp]
  rw [← h1, ← h2]
  exact congrFun h p

lemma dktImage_card {k d M A C n : ℕ} (h : A + M + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M)) (a : Fin A → Fin (k+1)) (c : Fin C → Fin (k+1)) :
    ((Finset.univ : Finset (Fin d → Fin (k+1))).image (fun u => dktCat3 h a (V u) c)).card
      = (k+1)^d := by
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_fun]
  · intro u u' heq
    apply dktSubspace_injective V
    have := congrArg (dktMid h) heq
    rw [dktMid_cat3, dktMid_cat3] at this
    exact this

/-- The points covered by the inserted subspaces indexed by `S` (three-block form). -/
def dktPoints {k A M C n d : ℕ} (h : A + M + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) : Finset (Fin n → Fin (k+1)) :=
  S.biUnion (fun p => (Finset.univ : Finset (Fin d → Fin (k+1))).image
    (fun u => dktCat3 h p.1 (V u) p.2))

/-- The points covered by the inserted subspaces indexed by `S` (two-block form). -/
def dktPoints' {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) : Finset (Fin n → Fin (k+1)) :=
  S.biUnion (fun p => (Finset.univ : Finset (Fin d → Fin (k+1))).image
    (fun u => dktCat2 hB (dktCat2 hAB p.1 (V u)) p.2))

lemma dktPoints_eq' {k d M A B C n : ℕ} (h : A + M + C = n) (hAB : A + M = B)
    (hB : B + C = n) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) :
    dktPoints' hAB hB V S = dktPoints h V S := by
  ext x
  simp only [dktPoints', dktPoints, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨p, hp, u, hu⟩
    exact ⟨p, hp, u, by rw [← hu, dktCat3_eq_cat2 h hAB hB]⟩
  · rintro ⟨p, hp, u, hu⟩
    exact ⟨p, hp, u, by rw [← hu, dktCat3_eq_cat2 h hAB hB]⟩

lemma dktPoints_pairwise {k d M A C n : ℕ} (h : A + M + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) :
    ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → Disjoint
      ((Finset.univ : Finset (Fin d → Fin (k+1))).image (fun u => dktCat3 h p.1 (V u) p.2))
      ((Finset.univ : Finset (Fin d → Fin (k+1))).image (fun u => dktCat3 h p'.1 (V u) p'.2)) := by
  intro p hp p' hp' hne
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨u, -, hu⟩ := hx
  obtain ⟨u', -, hu'⟩ := hx'
  have e1 : p.1 = dktResA h x := by
    have hh := congrArg (dktResA h) hu
    rwa [dktResA_cat3] at hh
  have e2 : p.2 = dktDelC h x := by
    have hh := congrArg (dktDelC h) hu
    rwa [dktDelC_cat3] at hh
  have e3 : p'.1 = dktResA h x := by
    have hh := congrArg (dktResA h) hu'
    rwa [dktResA_cat3] at hh
  have e4 : p'.2 = dktDelC h x := by
    have hh := congrArg (dktDelC h) hu'
    rwa [dktDelC_cat3] at hh
  exact absurd (Prod.ext (e1.trans e3.symm) (e2.trans e4.symm)) hne

lemma dktPoints_card {k d M A C n : ℕ} (h : A + M + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) :
    (dktPoints h V S).card = S.card * (k+1)^d := by
  rw [dktPoints, Finset.card_biUnion]
  · trans ∑ p ∈ S, (k+1)^d
    · apply Finset.sum_congr rfl
      intro p hp
      exact dktImage_card h V p.1 p.2
    · rw [Finset.sum_const, smul_eq_mul]
  · intro p hp p' hp' hne
    exact dktPoints_pairwise h V S p hp p' hp' hne

lemma dktPoints'_card {k d M A B C n : ℕ} (h : A + M + C = n) (hAB : A + M = B)
    (hB : B + C = n) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) :
    (dktPoints' hAB hB V S).card = S.card * (k+1)^d := by
  rw [dktPoints_eq' h hAB hB V S, dktPoints_card h V S]

lemma dktRel_cat3_left {k A M C n : ℕ} {i : Fin k} {x y : Fin A → Fin (k+1)}
    (hxy : dktRel i x y) (h : A + M + C = n) (w : Fin M → Fin (k+1))
    (c : Fin C → Fin (k+1)) :
    dktRel i (dktCat3 h x w c) (dktCat3 h y w c) := by
  intro j
  by_cases h1 : (j:ℕ) < A
  · rw [dktCat3_apply_lt h x w c j h1, dktCat3_apply_lt h y w c j h1]
    exact hxy ⟨j, h1⟩
  · by_cases h2 : (j:ℕ) < A + M
    · rw [dktCat3_apply_mid h x w c j (by omega) h2,
        dktCat3_apply_mid h y w c j (by omega) h2]
      exact Or.inl rfl
    · rw [dktCat3_apply_ge h x w c j (by omega), dktCat3_apply_ge h y w c j (by omega)]
      exact Or.inl rfl

/-- The full set of index pairs for which the inserted subspace lies in `E`. -/
def dktSset' {k A M B C n d : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (E : Finset (Fin n → Fin (k+1))) (V : Subspace (Fin d) (Fin (k+1)) (Fin M)) :
    Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1))) :=
  Finset.univ.filter (fun p => ∀ u : Fin d → Fin (k+1),
    dktCat2 hB (dktCat2 hAB p.1 (V u)) p.2 ∈ E)

lemma mem_dktSset' {k A M B C n d : ℕ} {hAB : A + M = B} {hB : B + C = n}
    {E : Finset (Fin n → Fin (k+1))} {V : Subspace (Fin d) (Fin (k+1)) (Fin M)}
    {p : (Fin A → Fin (k+1)) × (Fin C → Fin (k+1))} :
    p ∈ dktSset' hAB hB E V ↔ ∀ u : Fin d → Fin (k+1),
      dktCat2 hB (dktCat2 hAB p.1 (V u)) p.2 ∈ E := by
  simp [dktSset']

/-- The set of prefixes `a` such that `a` glued to the fixed subspace lies in `E`. -/
lemma dktIsInsens_Sc {k d M A B C n : ℕ} {i : Fin k} (h : A + M + C = n) (hAB : A + M = B)
    (hB : B + C = n) {E : Finset (Fin n → Fin (k+1))} {c : Fin C → Fin (k+1)}
    (hP : IsInsens i (dktSlice2 hB E c))
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M)) :
    IsInsens i (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
      ∀ u : Fin d → Fin (k+1), dktCat2 hB (dktCat2 hAB a (V u)) c ∈ E)) := by
  intro a ha a' hrel
  rw [Finset.mem_filter] at ha ⊢
  refine ⟨Finset.mem_univ _, fun u => ?_⟩
  have h1 : dktCat2 hAB a (V u) ∈ dktSlice2 hB E c := by
    rw [mem_dktSlice2]
    exact ha.2 u
  have h2 := hP _ h1 _ (dktRel_cat2_right hrel hAB (V u))
  rwa [mem_dktSlice2] at h2

/-- The preimage of the covered points under `a ↦ a ⧺ c'` is insensitive. -/
lemma dktIsInsens_uniPre {k d M A B C n : ℕ} {i : Fin k} (h : A + M + C = n) (hAB : A + M = B)
    (hB : B + C = n) {E : Finset (Fin n → Fin (k+1))}
    (hP : ∀ c : Fin C → Fin (k+1), IsInsens i (dktSlice2 hB E c))
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (c' : Fin (M + C) → Fin (k+1)) :
    IsInsens i (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
      dktCat2 (show A + (M+C) = n by omega) a c'
        ∈ dktPoints' hAB hB V (dktSset' hAB hB E V))) := by
  intro a ha a' hrel
  rw [Finset.mem_filter] at ha ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [dktPoints', Finset.mem_biUnion] at ha ⊢
  obtain ⟨p, hpS, hxp⟩ := ha.2
  rw [Finset.mem_image] at hxp
  obtain ⟨u, -, hu⟩ := hxp
  have heq : dktCat3 h p.1 (V u) p.2 = dktCat2 (show A + (M+C) = n by omega) a c' := by
    rw [dktCat3_eq_cat2 h hAB hB, hu]
  have hp1 : p.1 = a := by
    have hh := congrArg (dktResA h) heq
    rw [dktResA_cat3, dktResA_cat2 h (show A + (M+C) = n by omega) a c'] at hh
    exact hh
  have hp2 : p.2 = dktSuf2 rfl c' := by
    have hh := congrArg (dktDelC h) heq
    rw [dktDelC_cat3, dktDelC_cat2 h (show A + (M+C) = n by omega) a c'] at hh
    exact hh
  have hzu : V u = dktPre2 rfl c' := by
    have hh := congrArg (dktMid h) heq
    rw [dktMid_cat3, dktMid_cat2 h (show A + (M+C) = n by omega) a c'] at hh
    exact hh
  refine ⟨(a', dktSuf2 rfl c'), ?_, ?_⟩
  · rw [mem_dktSset']
    intro u'
    have h1 : dktCat2 hAB a (V u') ∈ dktSlice2 hB E (dktSuf2 rfl c') := by
      rw [mem_dktSlice2, ← dktCat3_eq_cat2 h hAB hB a (V u') (dktSuf2 rfl c')]
      rw [← hp1, ← hp2]
      have hh := (mem_dktSset'.mp hpS) u'
      rwa [← dktCat3_eq_cat2 h hAB hB] at hh
    have h2 := hP (dktSuf2 rfl c') _ h1 _ (dktRel_cat2_right hrel hAB (V u'))
    rwa [mem_dktSlice2] at h2
  · rw [Finset.mem_image]
    refine ⟨u, Finset.mem_univ _, ?_⟩
    simp only [hzu, ← dktCat3_eq_cat2 h hAB hB a' (dktPre2 rfl c') (dktSuf2 rfl c'),
      ← dktCat2_assoc3 h (show A + (M+C) = n by omega) a' (dktPre2 rfl c') (dktSuf2 rfl c'),
      dktCat2_pre_suf rfl c']

lemma dktIsInsens_rest {k A M C n : ℕ} {i : Fin k} {h' : A + (M+C) = n}
    {E UNI : Finset (Fin n → Fin (k+1))} (c' : Fin (M + C) → Fin (k+1))
    (h1 : IsInsens i (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
      dktCat2 h' a c' ∈ E)))
    (h2 : IsInsens i (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
      dktCat2 h' a c' ∈ UNI))) :
    IsInsens i (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
      dktCat2 h' a c' ∈ (E \ UNI))) := by
  have heq : Finset.univ.filter (fun a : Fin A → Fin (k+1) => dktCat2 h' a c' ∈ (E \ UNI))
      = Finset.univ.filter (fun a : Fin A → Fin (k+1) => dktCat2 h' a c' ∈ E)
        \ Finset.univ.filter (fun a : Fin A → Fin (k+1) => dktCat2 h' a c' ∈ UNI) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  rw [heq]
  exact dktIsInsens_sdiff h1 h2

/-- A subspace whose index word uses the first `d` directions. -/
def dktIdSub {k d M : ℕ} (hdM : d ≤ M) : Subspace (Fin d) (Fin (k+1)) (Fin M) where
  idxFun p := if h : (p:ℕ) < d then Sum.inr ⟨p, h⟩ else Sum.inl 0
  proper e := ⟨⟨e, by have := e.2; omega⟩, by
    rw [dif_pos e.2]⟩

/-- The number of `d`-dimensional subspaces of the `M`-cube. -/
noncomputable def dktC0 (k d M : ℕ) : ℕ := Fintype.card (Subspace (Fin d) (Fin (k+1)) (Fin M))

/-- The index word of the insertion of a subspace into the block `[A, A+M)`. -/
def dktInsIdx {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (a : Fin A → Fin (k+1)) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (c : Fin C → Fin (k+1)) (p : Fin n) : Fin (k+1) ⊕ Fin d :=
  if hp : (p:ℕ) < A then Sum.inl (a ⟨p, hp⟩)
  else if hp2 : (p:ℕ) < B then V.idxFun ⟨(p:ℕ) - A, by omega⟩
  else Sum.inl (c ⟨(p:ℕ) - B, by omega⟩)

lemma dktInsIdx_lt {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (a : Fin A → Fin (k+1)) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (c : Fin C → Fin (k+1)) (p : Fin n) (hp : (p:ℕ) < A) :
    dktInsIdx hAB hB a V c p = Sum.inl (a ⟨p, hp⟩) := dif_pos hp

lemma dktInsIdx_mid {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (a : Fin A → Fin (k+1)) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (c : Fin C → Fin (k+1)) (p : Fin n) (hp : ¬ (p:ℕ) < A) (hp2 : (p:ℕ) < B) :
    dktInsIdx hAB hB a V c p = V.idxFun ⟨(p:ℕ) - A, by omega⟩ := by
  rw [dktInsIdx, dif_neg hp, dif_pos hp2]

lemma dktInsIdx_ge {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (a : Fin A → Fin (k+1)) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (c : Fin C → Fin (k+1)) (p : Fin n) (hp : ¬ (p:ℕ) < A) (hp2 : ¬ (p:ℕ) < B) :
    dktInsIdx hAB hB a V c p = Sum.inl (c ⟨(p:ℕ) - B, by omega⟩) := by
  rw [dktInsIdx, dif_neg hp, dif_neg hp2]

/-- Inserting a subspace into the block `[A, A+M)` of a word. -/
def dktIns' {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (a : Fin A → Fin (k+1)) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (c : Fin C → Fin (k+1)) : Subspace (Fin d) (Fin (k+1)) (Fin n) where
  idxFun := dktInsIdx hAB hB a V c
  proper e := by
    obtain ⟨q, hq⟩ := V.proper e
    refine ⟨⟨A + (q:ℕ), by omega⟩, ?_⟩
    have h1 : ¬ ((A + (q:ℕ) : ℕ) < A) := by omega
    have h2 : (A + (q:ℕ) : ℕ) < B := by have := q.2; omega
    rw [dktInsIdx, dif_neg h1, dif_pos h2]
    rw [show (⟨(A + (q:ℕ)) - A, by omega⟩ : Fin M) = q from
      Fin.ext (by simp only [Fin.val_mk]; omega)]
    exact hq

lemma dktIns'_apply {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (a : Fin A → Fin (k+1)) (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (c : Fin C → Fin (k+1)) (u : Fin d → Fin (k+1)) :
    dktIns' hAB hB a V c u = dktCat2 hB (dktCat2 hAB a (V u)) c := by
  funext p
  rw [Subspace.coe_apply]
  show (dktInsIdx hAB hB a V c p).elim id u = _
  by_cases h1 : (p:ℕ) < A
  · rw [dktInsIdx_lt hAB hB a V c p h1, dktCat2_apply_lt hB _ _ p (by omega),
      dktCat2_apply_lt hAB _ _ _ h1]
    simp
  · by_cases h2 : (p:ℕ) < B
    · rw [dktInsIdx_mid hAB hB a V c p h1 h2, dktCat2_apply_lt hB _ _ p h2,
        dktCat2_apply_ge hAB _ _ _ h1]
      simp [Subspace.coe_apply]
    · rw [dktInsIdx_ge hAB hB a V c p h1 h2, dktCat2_apply_ge hB _ _ _ h2]
      simp

/-- The family of subspaces indexed by `S`. -/
def dktFam' {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) :
    Finset (Subspace (Fin d) (Fin (k+1)) (Fin n)) :=
  S.image (fun p => dktIns' hAB hB p.1 V p.2)

/-- The union of the point sets of a family of subspaces. -/
def dktUni {k d n : ℕ} (VS : Finset (Subspace (Fin d) (Fin (k+1)) (Fin n))) :
    Finset (Fin n → Fin (k+1)) :=
  VS.biUnion (fun S => (Finset.univ : Finset (Fin d → Fin (k+1))).image (fun x => S x))

lemma mem_dktUni {k d n : ℕ} {VS : Finset (Subspace (Fin d) (Fin (k+1)) (Fin n))}
    {x : Fin n → Fin (k+1)} :
    x ∈ dktUni VS ↔ ∃ S ∈ VS, ∃ y : Fin d → Fin (k+1), S y = x := by
  simp only [dktUni, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]

lemma dktUni_union {k d n : ℕ} (VS₁ VS₂ : Finset (Subspace (Fin d) (Fin (k+1)) (Fin n))) :
    dktUni (VS₁ ∪ VS₂) = dktUni VS₁ ∪ dktUni VS₂ := by
  rw [dktUni, dktUni, dktUni, Finset.union_biUnion]

lemma dktUni_dktFam' {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) :
    dktUni (dktFam' hAB hB V S) = dktPoints' hAB hB V S := by
  ext x
  simp only [dktUni, dktFam', dktPoints', Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨S', ⟨p, hp, rfl⟩, y, hy⟩
    exact ⟨p, hp, y, (dktIns'_apply hAB hB p.1 V p.2 y).symm.trans hy⟩
  · rintro ⟨p, hp, y, hy⟩
    exact ⟨dktIns' hAB hB p.1 V p.2, ⟨p, hp, rfl⟩, y,
      (dktIns'_apply hAB hB p.1 V p.2 y).trans hy⟩

lemma dktFam'_pairwise {k d M A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n)
    (V : Subspace (Fin d) (Fin (k+1)) (Fin M))
    (S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))) :
    ∀ S₁ ∈ dktFam' hAB hB V S, ∀ S₂ ∈ dktFam' hAB hB V S, S₁ ≠ S₂ →
      Disjoint (Finset.univ.image (fun x : Fin d → Fin (k+1) => S₁ x))
        (Finset.univ.image (fun x : Fin d → Fin (k+1) => S₂ x)) := by
  intro S₁ h1 S₂ h2 hne
  rw [dktFam', Finset.mem_image] at h1 h2
  obtain ⟨p, hp, rfl⟩ := h1
  obtain ⟨p', hp', rfl⟩ := h2
  have hpp : p ≠ p' := fun hpp => hne (by rw [hpp])
  have h : A + M + C = n := by omega
  have e1 : (Finset.univ.image (fun x : Fin d → Fin (k+1) => dktIns' hAB hB p.1 V p.2 x))
      = (Finset.univ.image (fun u : Fin d → Fin (k+1) => dktCat3 h p.1 (V u) p.2)) := by
    apply Finset.image_congr
    intro u _
    simp only [dktIns'_apply, dktCat3_eq_cat2 h hAB hB]
  have e2 : (Finset.univ.image (fun x : Fin d → Fin (k+1) => dktIns' hAB hB p'.1 V p'.2 x))
      = (Finset.univ.image (fun u : Fin d → Fin (k+1) => dktCat3 h p'.1 (V u) p'.2)) := by
    apply Finset.image_congr
    intro u _
    simp only [dktIns'_apply, dktCat3_eq_cat2 h hAB hB]
  rw [e1, e2]
  exact dktPoints_pairwise h V S p hp p' hp' hpp

lemma dktCard_eq_sum_fib' {α : Type*} [Fintype α] [DecidableEq α] {A M B C n : ℕ}
    (h : A + M + C = n) (hAB : A + M = B) (hB : B + C = n) (E : Finset (Fin n → α)) :
    E.card = ∑ p : (Fin A → α) × (Fin C → α),
      ((Finset.univ : Finset (Fin M → α)).filter
        (fun z => dktCat2 hB (dktCat2 hAB p.1 z) p.2 ∈ E)).card := by
  rw [dktCard_eq_sum_cat3 h E]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [dktCat3_eq_cat2 h hAB hB]

lemma dktCard_cast_eq_sum_fib' {α : Type*} [Fintype α] [DecidableEq α] {A M B C n : ℕ}
    (h : A + M + C = n) (hAB : A + M = B) (hB : B + C = n) (E : Finset (Fin n → α)) :
    (E.card : ℝ) = ∑ p : (Fin A → α) × (Fin C → α),
      (((Finset.univ : Finset (Fin M → α)).filter
        (fun z => dktCat2 hB (dktCat2 hAB p.1 z) p.2 ∈ E)).card : ℝ) := by
  rw [dktCard_eq_sum_fib' h hAB hB E, Nat.cast_sum]

/-- One step of the tiling. -/
lemma dktStep {k : ℕ} (hk : 2 ≤ k) {d M : ℕ} (hd : 1 ≤ d) (hdM : d ≤ M)
    {i : Fin k} {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hhc5 : ∀ F : Finset (Fin M → Fin (k+1)), β * (((k+1 : ℕ) : ℝ))^M ≤ (F.card : ℝ) →
      ∃ V : Subspace (Fin d) (Fin (k+1)) (Fin M), ∀ x : Fin d → Fin k, V (kvec x) ∈ F)
    {A B C n : ℕ} (hAB : A + M = B) (hB : B + C = n) (E : Finset (Fin n → Fin (k+1)))
    (hP : ∀ c : Fin C → Fin (k+1), IsInsens i (dktSlice2 hB E c))
    (hdens : 2*β*(((k+1 : ℕ) : ℝ))^n ≤ (E.card : ℝ)) :
    ∃ V : Subspace (Fin d) (Fin (k+1)) (Fin M),
    ∃ S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1))),
      (∀ p ∈ S, ∀ u : Fin d → Fin (k+1), dktCat2 hB (dktCat2 hAB p.1 (V u)) p.2 ∈ E) ∧
      (β * (((k+1 : ℕ) : ℝ))^(n-M) / (dktC0 k d M : ℝ) ≤ (S.card : ℝ)) ∧
      (β * (((k+1 : ℕ) : ℝ))^n /
          ((dktC0 k d M : ℝ) * (((k+1 : ℕ) : ℝ))^(M-d)) ≤
            ((dktPoints' hAB hB V S).card : ℝ)) ∧
      (∀ c' : Fin (M + C) → Fin (k+1),
        IsInsens i (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
          dktCat2 (show A + (M+C) = n by omega) a c' ∈ (E \ dktPoints' hAB hB V S)))) := by
  classical
  have h : A + M + C = n := by omega
  set W : ℝ := (((k+1 : ℕ) : ℝ))^M with hW
  set Pair := ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1))) with hPair
  have hWpos : 0 < W := by rw [hW]; positivity
  have hk1pos : (0 : ℝ) < (((k+1 : ℕ) : ℝ)) := by positivity
  have hNp : (Finset.univ : Finset Pair).card = (k+1)^(n-M) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← pow_add]
    congr 1
    omega
  set fib : Pair → Finset (Fin M → Fin (k+1)) := fun p =>
    Finset.univ.filter (fun z => dktCat2 hB (dktCat2 hAB p.1 z) p.2 ∈ E) with hfib
  have hfib_insens : ∀ p : Pair, IsInsens i (fib p) := by
    intro p
    have heq : (Finset.univ.filter (fun z : Fin M → Fin (k+1) =>
        dktCat2 hAB p.1 z ∈ dktSlice2 hB E p.2)) = fib p := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfib, mem_dktSlice2]
    rw [← heq]
    exact dktIsInsens_filter (hP p.2) (fun z => dktCat2 hAB p.1 z)
      (fun x y hxy => dktRel_cat2_left hxy hAB p.1)
  set T : Finset Pair := Finset.univ.filter (fun p => β * W ≤ ((fib p).card : ℝ)) with hT
  have mem_fib : ∀ (p : Pair) (z : Fin M → Fin (k+1)),
      z ∈ fib p ↔ dktCat2 hB (dktCat2 hAB p.1 z) p.2 ∈ E := by
    intro p z
    simp only [hfib, Finset.mem_filter, Finset.mem_univ, true_and]
  have hsum : (E.card : ℝ) = ∑ p : Pair, ((fib p).card : ℝ) :=
    dktCard_cast_eq_sum_fib' h hAB hB E
  have hsplit : (∑ p : Pair, ((fib p).card : ℝ))
      = T.sum (fun p => ((fib p).card : ℝ))
        + (Finset.univ.filter (fun p : Pair => ¬ β * W ≤ ((fib p).card : ℝ))).sum
            (fun p => ((fib p).card : ℝ)) := by
    rw [hT]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset Pair)
      (fun p => β * W ≤ ((fib p).card : ℝ))
      (fun p => ((fib p).card : ℝ))).symm
  have hfib_le : ∀ p : Pair, ((fib p).card : ℝ) ≤ W := by
    intro p
    rw [hfib]
    have h1 : (Finset.univ.filter (fun z : Fin M → Fin (k+1) =>
        dktCat2 hB (dktCat2 hAB p.1 z) p.2 ∈ E)).card
        ≤ (Finset.univ : Finset (Fin M → Fin (k+1))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
    calc ((Finset.univ.filter (fun z : Fin M → Fin (k+1) =>
            dktCat2 hB (dktCat2 hAB p.1 z) p.2 ∈ E)).card : ℝ)
        ≤ (((k+1)^M : ℕ) : ℝ) := by exact_mod_cast h1
      _ = W := by rw [hW]; push_cast; ring
  have hTle : T.sum (fun p => ((fib p).card : ℝ)) ≤ (T.card : ℝ) * W := by
    calc T.sum (fun p => ((fib p).card : ℝ)) ≤ T.sum (fun _ => W) :=
          Finset.sum_le_sum (fun p _ => hfib_le p)
      _ = (T.card : ℝ) * W := by rw [Finset.sum_const, nsmul_eq_mul]
  have hTnple : T.card ≤ (k+1)^(n-M) := by
    rw [← hNp]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hcompcard : (Finset.univ.filter (fun p : Pair => ¬ β * W ≤ ((fib p).card : ℝ))).card
      = (k+1)^(n-M) - T.card := by
    have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Pair))
      (p := fun p => β * W ≤ ((fib p).card : ℝ))
    rw [← hT, hNp] at hc
    omega
  have hcle : (Finset.univ.filter (fun p : Pair => ¬ β * W ≤ ((fib p).card : ℝ))).sum
      (fun p => ((fib p).card : ℝ))
      ≤ (((k+1)^(n-M) - T.card : ℕ) : ℝ) * (β * W) := by
    calc (Finset.univ.filter (fun p : Pair => ¬ β * W ≤ ((fib p).card : ℝ))).sum
          (fun p => ((fib p).card : ℝ))
        ≤ (Finset.univ.filter (fun p : Pair => ¬ β * W ≤ ((fib p).card : ℝ))).sum
            (fun _ => β * W) := by
          apply Finset.sum_le_sum
          intro p hp
          have hp' := (Finset.mem_filter.mp hp).2
          push_neg at hp'
          linarith
      _ = (((Finset.univ.filter (fun p : Pair => ¬ β * W ≤ ((fib p).card : ℝ))).card : ℕ) : ℝ)
            * (β * W) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((k+1)^(n-M) - T.card : ℕ) : ℝ) * (β * W) := by rw [hcompcard]
  have hcsub : ((((k+1)^(n-M) - T.card : ℕ)) : ℝ)
      = (((k+1 : ℕ) : ℝ)^(n-M)) - (T.card : ℝ) := by
    rw [Nat.cast_sub hTnple]
    push_cast
    ring
  have hEbound : (E.card : ℝ) ≤ (T.card : ℝ) * W
      + ((((k+1 : ℕ) : ℝ)^(n-M)) - (T.card : ℝ)) * (β * W) := by
    rw [hsum, hsplit]
    calc T.sum (fun p => ((fib p).card : ℝ))
          + (Finset.univ.filter (fun p : Pair => ¬ β * W ≤ ((fib p).card : ℝ))).sum
              (fun p => ((fib p).card : ℝ))
        ≤ (T.card : ℝ) * W + ((((k+1)^(n-M) - T.card : ℕ) : ℝ) * (β * W)) :=
          add_le_add hTle hcle
      _ = (T.card : ℝ) * W + ((((k+1 : ℕ) : ℝ)^(n-M)) - (T.card : ℝ)) * (β * W) := by
          rw [hcsub]
  have hNpW : (((k+1 : ℕ) : ℝ)^(n-M)) * W = (((k+1 : ℕ) : ℝ))^n := by
    rw [hW, ← pow_add]
    congr 1
    omega
  have hbig : 2*β*(((k+1 : ℕ) : ℝ)^n)
      ≤ (T.card : ℝ) * W + ((((k+1 : ℕ) : ℝ)^(n-M)) - (T.card : ℝ)) * (β * W) :=
    le_trans hdens hEbound
  have hTcard : β * (((k+1 : ℕ) : ℝ)^(n-M)) ≤ (T.card : ℝ) := by
    rw [← hNpW] at hbig
    have hbTcW : (0 : ℝ) ≤ β * (T.card : ℝ) * W := by positivity
    have hkey : β * (((k+1 : ℕ) : ℝ)^(n-M)) * W ≤ (T.card : ℝ) * W := by
      nlinarith [hbig, hbTcW]
    exact le_of_mul_le_mul_right hkey hWpos
  let f : Pair → Subspace (Fin d) (Fin (k+1)) (Fin M) := fun p =>
    if hp : p ∈ T then
      Classical.choose (hhc5 (fib p) ((Finset.mem_filter.mp hp).2))
    else dktIdSub hdM
  have hf_spec : ∀ p ∈ T, ∀ u : Fin d → Fin (k+1),
      dktCat2 hB (dktCat2 hAB p.1 (f p u)) p.2 ∈ E := by
    intro p hp u
    have hmem : β * W ≤ ((fib p).card : ℝ) := (Finset.mem_filter.mp hp).2
    have hVx := Classical.choose_spec (hhc5 (fib p) hmem)
    have hmem2 : (Classical.choose (hhc5 (fib p) hmem)) u ∈ fib p :=
      dktSubImage_subset_of_insens (hfib_insens p)
        (Classical.choose (hhc5 (fib p) hmem)) hVx u
    have hfp : f p = Classical.choose (hhc5 (fib p) hmem) := by
      dsimp only [f]
      rw [dif_pos hp]
    have hmem3 : (f p) u ∈ fib p := by rw [hfp]; exact hmem2
    exact (mem_fib p ((f p) u)).mp hmem3
  have hDpos : 0 < dktC0 k d M := by
    rw [dktC0]
    exact Fintype.card_pos_iff.mpr ⟨dktIdSub hdM⟩
  have hD : ((T.image f).card : ℕ) ≤ dktC0 k d M := by
    rw [dktC0]
    exact Finset.card_le_univ _
  have hcpos : 0 < β * (((k+1 : ℕ) : ℝ)^(n-M)) := mul_pos hβ (pow_pos hk1pos _)
  obtain ⟨V, hV⟩ := exists_card_fiber_ge_div (s := T) (f := f)
    (c := β * (((k+1 : ℕ) : ℝ)^(n-M))) (D := dktC0 k d M) hcpos hDpos hD hTcard
  refine ⟨V, dktSset' hAB hB E V, ?_, ?_, ?_, ?_⟩
  · intro p hp u
    exact (mem_dktSset'.mp hp) u
  · have hsub : T.filter (fun p => f p = V) ⊆ dktSset' hAB hB E V := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [mem_dktSset']
      intro u
      have hfu := hf_spec p hp.1 u
      rw [hp.2] at hfu
      exact hfu
    calc β * (((k+1 : ℕ) : ℝ)^(n-M)) / (dktC0 k d M : ℝ)
        ≤ ((T.filter (fun p => f p = V)).card : ℝ) := hV
      _ ≤ ((dktSset' hAB hB E V).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
  · have hSge : β * (((k+1 : ℕ) : ℝ)^(n-M)) / (dktC0 k d M : ℝ)
        ≤ ((dktSset' hAB hB E V).card : ℝ) := by
      have hsub : T.filter (fun p => f p = V) ⊆ dktSset' hAB hB E V := by
        intro p hp
        rw [Finset.mem_filter] at hp
        rw [mem_dktSset']
        intro u
        have hfu := hf_spec p hp.1 u
        rw [hp.2] at hfu
        exact hfu
      calc β * (((k+1 : ℕ) : ℝ)^(n-M)) / (dktC0 k d M : ℝ)
          ≤ ((T.filter (fun p => f p = V)).card : ℝ) := hV
        _ ≤ ((dktSset' hAB hB E V).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    have hpc : (dktPoints' hAB hB V (dktSset' hAB hB E V)).card
        = (dktSset' hAB hB E V).card * (k+1)^d := dktPoints'_card h hAB hB V _
    have hMd : (0 : ℝ) < (((k+1 : ℕ) : ℝ))^(M-d) := pow_pos hk1pos _
    have hpow : (((k+1 : ℕ) : ℝ))^n
        = (((k+1 : ℕ) : ℝ))^(n-M+d) * (((k+1 : ℕ) : ℝ))^(M-d) := by
      rw [← pow_add]
      congr 1
      omega
    calc β * (((k+1 : ℕ) : ℝ))^n / ((dktC0 k d M : ℝ) * (((k+1 : ℕ) : ℝ))^(M-d))
        = (β * (((k+1 : ℕ) : ℝ)^(n-M)) / (dktC0 k d M : ℝ)) * (((k+1 : ℕ) : ℝ))^d := by
          rw [hpow]
          field_simp
          ring
      _ ≤ ((dktSset' hAB hB E V).card : ℝ) * (((k+1 : ℕ) : ℝ))^d :=
          mul_le_mul_of_nonneg_right hSge (by positivity)
      _ = ((((dktSset' hAB hB E V).card * (k+1)^d : ℕ)) : ℝ) := by push_cast; ring
      _ = ((dktPoints' hAB hB V (dktSset' hAB hB E V)).card : ℝ) := by rw [hpc]
  · intro c'
    have hfib' : IsInsens i (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
        dktCat2 (show A + (M+C) = n by omega) a c' ∈ E)) := by
      have hslice := hP (dktSuf2 rfl c')
      have hh := dktIsInsens_slice2_right (B := A) (C := M) (n := B) hslice hAB
        (dktPre2 rfl c')
      have hc'eq : ∀ a : Fin A → Fin (k+1),
          dktCat2 (show A + (M+C) = n by omega) a c'
            = dktCat2 hB (dktCat2 hAB a (dktPre2 rfl c')) (dktSuf2 rfl c') := by
        intro a
        calc dktCat2 (show A + (M+C) = n by omega) a c'
            = dktCat2 (show A + (M+C) = n by omega) a
                (dktCat2 rfl (dktPre2 rfl c') (dktSuf2 rfl c')) := by
              rw [dktCat2_pre_suf rfl c']
          _ = dktCat3 h a (dktPre2 rfl c') (dktSuf2 rfl c') :=
              dktCat2_assoc3 h (show A + (M+C) = n by omega) a (dktPre2 rfl c')
                (dktSuf2 rfl c')
          _ = dktCat2 hB (dktCat2 hAB a (dktPre2 rfl c')) (dktSuf2 rfl c') :=
              dktCat3_eq_cat2 h hAB hB a (dktPre2 rfl c') (dktSuf2 rfl c')
      have heq : (Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
            dktCat2 (show A + (M+C) = n by omega) a c' ∈ E))
          = Finset.univ.filter (fun a : Fin A → Fin (k+1) =>
              dktCat2 hAB a (dktPre2 rfl c')
                ∈ dktSlice2 hB E (dktSuf2 rfl c')) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_dktSlice2, hc'eq a]
      rw [heq]
      exact hh
    have h2 := dktIsInsens_uniPre h hAB hB hP V c'
    exact dktIsInsens_rest c' hfib' h2

/-! ## Part 4: the iteration -/

/-- Prefix length after `t` steps: `n`, `n-M`, `n-2M`, ... -/
def dktP (M n : ℕ) : ℕ → ℕ
  | 0 => n
  | (t+1) => dktP M n t - M

/-- Suffix length after `t` steps: `0`, `M`, `2M`, ... -/
def dktC (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | (t+1) => M + dktC M t

@[simp] lemma dktP_zero (M n : ℕ) : dktP M n 0 = n := rfl
@[simp] lemma dktP_succ (M n t : ℕ) : dktP M n (t+1) = dktP M n t - M := rfl
@[simp] lemma dktC_zero (M : ℕ) : dktC M 0 = 0 := rfl
@[simp] lemma dktC_succ (M t : ℕ) : dktC M (t+1) = M + dktC M t := rfl

lemma dktC_eq (M t : ℕ) : dktC M t = M * t := by
  induction t with
  | zero => simp
  | succ t ih => rw [dktC_succ, ih]; ring

lemma dktP_add_dktC (M n : ℕ) : ∀ t, dktC M t ≤ n → dktP M n t + dktC M t = n := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro h
    have h1 : dktC M t ≤ n := by rw [dktC_succ] at h; omega
    have ih' := ih h1
    have hM : M ≤ dktP M n t := by
      rw [dktC_succ] at h
      omega
    rw [dktP_succ, dktC_succ]
    omega

lemma dktP_eq (M n t : ℕ) (h : dktC M t ≤ n) : dktP M n t = n - dktC M t := by
  have := dktP_add_dktC M n t h
  omega

lemma dktSlice2_zero {k n : ℕ} {i : Fin k} (h : n + 0 = n)
    {D : Finset (Fin n → Fin (k+1))} (hD : IsInsens i D) (c : Fin 0 → Fin (k+1)) :
    IsInsens i (dktSlice2 h D c) := by
  have heq : dktSlice2 h D c = D := by
    ext v
    simp only [dktSlice2, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc : dktCat2 h v c = v := by
      funext i
      rw [dktCat2_apply_lt h v c i i.2]
    rw [hc]
  rw [heq]
  exact hD

lemma dktUni_subset {k d n : ℕ} {VS : Finset (Subspace (Fin d) (Fin (k+1)) (Fin n))}
    {A : Finset (Fin n → Fin (k+1))} (h : ∀ S ∈ VS, ∀ x : Fin d → Fin (k+1), S x ∈ A) :
    dktUni VS ⊆ A := by
  intro x hx
  rw [mem_dktUni] at hx
  obtain ⟨S, hS, y, rfl⟩ := hx
  exact h S hS y

lemma dktPoints'_subset {k d M A B C n : ℕ} {hAB : A + M = B} {hB : B + C = n}
    {V : Subspace (Fin d) (Fin (k+1)) (Fin M)}
    {S : Finset ((Fin A → Fin (k+1)) × (Fin C → Fin (k+1)))}
    {E : Finset (Fin n → Fin (k+1))}
    (h : ∀ p ∈ S, ∀ u : Fin d → Fin (k+1), dktCat2 hB (dktCat2 hAB p.1 (V u)) p.2 ∈ E) :
    dktPoints' hAB hB V S ⊆ E := by
  intro x hx
  rw [dktPoints', Finset.mem_biUnion] at hx
  obtain ⟨p, hp, hxp⟩ := hx
  rw [Finset.mem_image] at hxp
  obtain ⟨u, _, rfl⟩ := hxp
  exact h p hp u

/-- **Lemma 12 (Dodos–Kanellopoulos–Tyros).**  An insensitive dense set can be tiled by
pairwise disjoint `d`-dimensional subspaces up to a `2β` error. -/
theorem dktSingle {k : ℕ} (hk : 2 ≤ k) {d M : ℕ} (hd : 1 ≤ d) (hdM : d ≤ M)
    {i : Fin k} {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hhc5 : ∀ F : Finset (Fin M → Fin (k+1)), β * (((k+1 : ℕ) : ℝ))^M ≤ (F.card : ℝ) →
      ∃ V : Subspace (Fin d) (Fin (k+1)) (Fin M), ∀ x : Fin d → Fin k, V (kvec x) ∈ F)
    (T : ℕ) (hTθ : 1 ≤ (T : ℝ) * (β / ((dktC0 k d M : ℝ) * (((k+1 : ℕ) : ℝ))^(M-d)))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ D : Finset (Fin n → Fin (k+1)),
      IsInsens i D → 2*β*(((k+1 : ℕ) : ℝ))^n ≤ (D.card : ℝ) →
      ∃ VS : Finset (Subspace (Fin d) (Fin (k+1)) (Fin n)),
        (∀ S ∈ VS, ∀ x : Fin d → Fin (k+1), S x ∈ D) ∧
        (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
          Disjoint (Finset.univ.image (fun x : Fin d → Fin (k+1) => S x))
            (Finset.univ.image (fun x : Fin d → Fin (k+1) => S' x))) ∧
        (D.card : ℝ) - 2*β*(((k+1 : ℕ) : ℝ))^n ≤ ((dktUni VS).card : ℝ) := by
  classical
  set θ : ℝ := β / ((dktC0 k d M : ℝ) * (((k+1 : ℕ) : ℝ))^(M-d)) with hθ
  have hC0pos : 0 < dktC0 k d M := by
    rw [dktC0]
    exact Fintype.card_pos_iff.mpr ⟨dktIdSub hdM⟩
  have hk1pos : (0 : ℝ) < (((k+1 : ℕ) : ℝ)) := by positivity
  have hθpos : 0 < θ := by rw [hθ]; positivity
  refine ⟨(T+1)*M, ?_⟩
  intro n hn D hD hdens
  have hCt : ∀ t ≤ T, dktC M t ≤ n := by
    intro t ht
    rw [dktC_eq]
    calc M * t ≤ M * (T+1) := Nat.mul_le_mul_left M (by omega)
      _ = (T+1) * M := by ring
      _ ≤ n := hn
  have key : ∀ (t : ℕ) (ht : t ≤ T), ∃ VS : Finset (Subspace (Fin d) (Fin (k+1)) (Fin n)),
      (∀ S ∈ VS, ∀ x : Fin d → Fin (k+1), S x ∈ D) ∧
      (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
        Disjoint (Finset.univ.image (fun x : Fin d → Fin (k+1) => S x))
          (Finset.univ.image (fun x : Fin d → Fin (k+1) => S' x))) ∧
      ((((D \ dktUni VS).card : ℝ) < 2*β*(((k+1 : ℕ) : ℝ))^n) ∨
       (2*β*(((k+1 : ℕ) : ℝ))^n ≤ ((D \ dktUni VS).card : ℝ) ∧
        (∀ c : Fin (dktC M t) → Fin (k+1),
          IsInsens i (dktSlice2 (dktP_add_dktC M n t (hCt t ht)) (D \ dktUni VS) c)) ∧
        (((D \ dktUni VS).card : ℝ) ≤ (D.card : ℝ) - (t:ℝ)*θ*(((k+1 : ℕ) : ℝ))^n))) := by
    intro t
    induction t with
    | zero =>
      intro ht
      have hE : D \ dktUni (∅ : Finset (Subspace (Fin d) (Fin (k+1)) (Fin n))) = D := by
        simp [dktUni]
      refine ⟨∅, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
      · intro S hS; simp at hS
      · intro S hS; simp at hS
      · rw [hE]; exact hdens
      · intro c
        have h0 : dktC M 0 ≤ n := hCt 0 (Nat.zero_le T)
        rw [hE]
        exact dktSlice2_zero (k := k) (n := n) (i := i) (dktP_add_dktC M n 0 h0) hD c
      · rw [hE]; simp
    | succ s ih =>
      intro hst
      have hs : s ≤ T := by omega
      obtain ⟨VS, hsub, hdisj, hcase⟩ := ih hs
      rcases hcase with hsmall | ⟨hbig, hgood, hdens'⟩
      · exact ⟨VS, hsub, hdisj, Or.inl hsmall⟩
      · have hCs : dktC M s ≤ n := hCt s hs
        have hCs1 : dktC M (s+1) ≤ n := hCt (s+1) (by omega)
        have hAB : dktP M n (s+1) + M = dktP M n s := by
          have h2 : M ≤ dktP M n s := by
            rw [dktC_succ] at hCs1
            rw [dktP_eq M n s hCs]
            omega
          rw [dktP_succ]
          exact Nat.sub_add_cancel h2
        have hB : dktP M n s + dktC M s = n := dktP_add_dktC M n s hCs
        obtain ⟨V, S, hSp, hSbnd, hgain, hgood2⟩ :=
          dktStep (k := k) hk (d := d) (M := M) hd hdM (i := i) hβ hβ1 hhc5
            hAB hB (D \ dktUni VS) hgood hbig
        have hpointsSub : dktPoints' hAB hB V S ⊆ D \ dktUni VS :=
          dktPoints'_subset hSp
        have hsubNew : ∀ S' ∈ dktFam' hAB hB V S, ∀ x : Fin d → Fin (k+1), S' x ∈ D := by
          intro S' hS' x
          rw [dktFam', Finset.mem_image] at hS'
          obtain ⟨p, hp, rfl⟩ := hS'
          rw [dktIns'_apply]
          exact (Finset.mem_sdiff.mp (hSp p hp x)).1
        have hsub' : ∀ S' ∈ VS ∪ dktFam' hAB hB V S, ∀ x : Fin d → Fin (k+1), S' x ∈ D := by
          intro S' hS' x
          rcases Finset.mem_union.mp hS' with h | h
          · exact hsub S' h x
          · exact hsubNew S' h x
        have hsubU : dktUni VS ⊆ D := dktUni_subset hsub
        have hsubU' : dktUni (VS ∪ dktFam' hAB hB V S) ⊆ D := dktUni_subset hsub'
        have huni : dktUni (VS ∪ dktFam' hAB hB V S) = dktUni VS ∪ dktPoints' hAB hB V S := by
          rw [dktUni_union, dktUni_dktFam']
        have hdisj' : ∀ S₁ ∈ VS ∪ dktFam' hAB hB V S, ∀ S₂ ∈ VS ∪ dktFam' hAB hB V S,
            S₁ ≠ S₂ →
            Disjoint (Finset.univ.image (fun x : Fin d → Fin (k+1) => S₁ x))
              (Finset.univ.image (fun x : Fin d → Fin (k+1) => S₂ x)) := by
          intro S₁ h₁ S₂ h₂ hne
          rcases Finset.mem_union.mp h₁ with h₁ | h₁ <;> rcases Finset.mem_union.mp h₂ with h₂ | h₂
          · exact hdisj S₁ h₁ S₂ h₂ hne
          · rw [Finset.disjoint_left]
            intro x hx hx'
            rw [Finset.mem_image] at hx hx'
            obtain ⟨y, -, hy⟩ := hx
            obtain ⟨z, -, hz⟩ := hx'
            have hxV : x ∈ dktUni VS := by
              rw [mem_dktUni]; exact ⟨S₁, h₁, y, hy⟩
            have hxS : x ∈ dktPoints' hAB hB V S := by
              rw [← dktUni_dktFam', mem_dktUni]
              exact ⟨S₂, h₂, z, hz⟩
            exact (Finset.mem_sdiff.mp (hpointsSub hxS)).2 hxV
          · rw [Finset.disjoint_left]
            intro x hx hx'
            rw [Finset.mem_image] at hx hx'
            obtain ⟨y, -, hy⟩ := hx
            obtain ⟨z, -, hz⟩ := hx'
            have hxV : x ∈ dktUni VS := by
              rw [mem_dktUni]; exact ⟨S₂, h₂, z, hz⟩
            have hxS : x ∈ dktPoints' hAB hB V S := by
              rw [← dktUni_dktFam', mem_dktUni]
              exact ⟨S₁, h₁, y, hy⟩
            exact (Finset.mem_sdiff.mp (hpointsSub hxS)).2 hxV
          · exact dktFam'_pairwise hAB hB V S S₁ h₁ S₂ h₂ hne
        have heq2 : (D \ (dktUni VS ∪ dktPoints' hAB hB V S))
            = (D \ dktUni VS) \ dktPoints' hAB hB V S := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          tauto
        have hcardR : ((D \ dktUni (VS ∪ dktFam' hAB hB V S)).card : ℝ)
            = ((D \ dktUni VS).card : ℝ) - ((dktPoints' hAB hB V S).card : ℝ) := by
          have h₁ : D \ dktUni (VS ∪ dktFam' hAB hB V S)
              = (D \ dktUni VS) \ dktPoints' hAB hB V S := by
            rw [huni]; exact heq2
          rw [h₁, Finset.card_sdiff_of_subset hpointsSub,
            Nat.cast_sub (Finset.card_le_card hpointsSub)]
        have hθeq : θ*(((k+1 : ℕ) : ℝ))^n
            = β*(((k+1 : ℕ) : ℝ))^n
              / ((dktC0 k d M : ℝ) * (((k+1 : ℕ) : ℝ))^(M-d)) := by
          rw [hθ, div_mul_eq_mul_div]
        have hbound : ((D \ dktUni (VS ∪ dktFam' hAB hB V S)).card : ℝ)
            ≤ (D.card : ℝ) - ((s+1:ℕ):ℝ)*θ*(((k+1 : ℕ) : ℝ))^n := by
          have h2 : ((s+1 : ℕ) : ℝ) = (s:ℝ) + 1 := by push_cast; ring
          rw [hcardR, h2]
          linarith [hdens', hgain, hθeq]
        by_cases hsmall2 : ((D \ dktUni (VS ∪ dktFam' hAB hB V S)).card : ℝ)
            < 2*β*(((k+1 : ℕ) : ℝ))^n
        · exact ⟨VS ∪ dktFam' hAB hB V S, hsub', hdisj', Or.inl hsmall2⟩
        · refine ⟨VS ∪ dktFam' hAB hB V S, hsub', hdisj', Or.inr ⟨le_of_not_gt hsmall2, ?_, hbound⟩⟩
          intro c'
          have hh := hgood2 c'
          rw [huni, heq2]
          exact hh
  obtain ⟨VS, hsub, hdisj, hcase⟩ := key T le_rfl
  refine ⟨VS, hsub, hdisj, ?_⟩
  rcases hcase with hsmall | ⟨hbig, hgood, hdens'⟩
  · have hle : ((D \ dktUni VS).card : ℝ) = (D.card : ℝ) - ((dktUni VS).card : ℝ) := by
      rw [Finset.card_sdiff_of_subset (dktUni_subset hsub),
        Nat.cast_sub (Finset.card_le_card (dktUni_subset hsub))]
    linarith [hsmall, hle]
  · have hDle : (D.card : ℝ) ≤ (((k+1 : ℕ) : ℝ))^n := by
      have h1 : D.card ≤ (Finset.univ : Finset (Fin n → Fin (k+1))).card :=
        Finset.card_le_univ D
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
      calc (D.card : ℝ) ≤ (((k+1)^n : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (((k+1 : ℕ) : ℝ))^n := by push_cast; ring
    have hXpos : (0 : ℝ) < (((k+1 : ℕ) : ℝ))^n := pow_pos hk1pos _
    have hzero : (D.card : ℝ) - (T:ℝ)*θ*(((k+1 : ℕ) : ℝ))^n ≤ 0 := by
      nlinarith [hDle, hTθ, hXpos, hθpos]
    have hpos : (0 : ℝ) < 2*β*(((k+1 : ℕ) : ℝ))^n := by positivity
    have hlt : ((D \ dktUni VS).card : ℝ) < 2*β*(((k+1 : ℕ) : ℝ))^n := by
      linarith [hdens', hzero]
    exfalso
    linarith [hbig, hlt]
/-! ## Part 5: pulling back and composing subspaces -/

lemma dktInsens_pullback {k p n : ℕ} {i : Fin k}
    (V : Subspace (Fin p) (Fin (k+1)) (Fin n))
    {A : Finset (Fin n → Fin (k+1))} (hA : IsInsens i A) :
    IsInsens i (Finset.univ.filter (fun x : Fin p → Fin (k+1) => V x ∈ A)) := by
  apply dktIsInsens_filter hA (φ := fun x => V x)
  intro x y hxy q
  cases hq : V.idxFun q with
  | inl a =>
    simp only [Subspace.coe_apply, hq, Sum.elim_inl, id_eq, true_or]
  | inr e =>
    simp only [Subspace.coe_apply, hq, Sum.elim_inr]
    exact hxy e

lemma dktImage_card' {k p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n)) :
    ((Finset.univ : Finset (Fin p → Fin (k+1))).image V).card = (k+1)^p := by
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_fun]
  · intro x y h
    exact dktSubspace_injective V h

/-- The index word of a composed subspace. -/
def dktCompIdx {k d p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n))
    (W : Subspace (Fin d) (Fin (k+1)) (Fin p)) (i : Fin n) : Fin (k+1) ⊕ Fin d :=
  (V.idxFun i).elim (fun a => Sum.inl a) (fun e => W.idxFun e)

lemma dktCompIdx_inl {k d p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n))
    (W : Subspace (Fin d) (Fin (k+1)) (Fin p)) (i : Fin n) (a : Fin (k+1))
    (h : V.idxFun i = Sum.inl a) : dktCompIdx V W i = Sum.inl a := by
  rw [dktCompIdx, h]; rfl

lemma dktCompIdx_inr {k d p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n))
    (W : Subspace (Fin d) (Fin (k+1)) (Fin p)) (i : Fin n) (e : Fin p)
    (h : V.idxFun i = Sum.inr e) : dktCompIdx V W i = W.idxFun e := by
  rw [dktCompIdx, h]; rfl

/-- Composition of combinatorial subspaces. -/
def dktComp {k d p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n))
    (W : Subspace (Fin d) (Fin (k+1)) (Fin p)) : Subspace (Fin d) (Fin (k+1)) (Fin n) where
  idxFun := dktCompIdx V W
  proper e := by
    obtain ⟨q, hq⟩ := W.proper e
    obtain ⟨i, hi⟩ := V.proper q
    exact ⟨i, by rw [dktCompIdx, hi]; simp only [Sum.elim_inr]; exact hq⟩

lemma dktComp_apply {k d p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n))
    (W : Subspace (Fin d) (Fin (k+1)) (Fin p)) (x : Fin d → Fin (k+1)) :
    dktComp V W x = V (W x) := by
  funext i
  rw [Subspace.coe_apply, Subspace.coe_apply]
  show Sum.elim id x (dktCompIdx V W i) = Sum.elim id (W x) (V.idxFun i)
  cases hq : V.idxFun i with
  | inl a => rw [dktCompIdx_inl V W i a hq]; simp only [Sum.elim_inl, id_eq]
  | inr e =>
    rw [dktCompIdx_inr V W i e hq]
    cases hq2 : W.idxFun e <;>
      simp only [hq2, Sum.elim_inl, Sum.elim_inr, id_eq, Subspace.coe_apply]

lemma dktCompImg {k d p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n))
    (W : Subspace (Fin d) (Fin (k+1)) (Fin p)) :
    (Finset.univ.image (fun x : Fin d → Fin (k+1) => dktComp V W x))
      = (Finset.univ.image (fun y : Fin d → Fin (k+1) => W y)).image V := by
  rw [Finset.image_image]
  apply Finset.image_congr
  intro x _
  exact dktComp_apply V W x

lemma dktSubspace_inj_image {k p n : ℕ} (V : Subspace (Fin p) (Fin (k+1)) (Fin n)) :
    Set.InjOn V Set.univ := by
  intro x _ y _ h
  exact dktSubspace_injective V h

/-- **Corollary 13 (Dodos–Kanellopoulos–Tyros).**  An intersection of `r` insensitive sets of
density `≥ 2rβ` can be tiled by pairwise disjoint `m`-dimensional subspaces up to a `2rβ` error. -/
theorem dktMulti {k : ℕ} (hk : 2 ≤ k) (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hone : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (i : Fin k) (D : Finset (Fin n → Fin (k+1))),
      IsInsens i D → 2*β*(((k+1 : ℕ) : ℝ))^n ≤ (D.card : ℝ) →
      ∃ VS : Finset (Subspace (Fin m) (Fin (k+1)) (Fin n)),
        (∀ S ∈ VS, ∀ x : Fin m → Fin (k+1), S x ∈ D) ∧
        (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
          Disjoint (Finset.univ.image (fun x : Fin m → Fin (k+1) => S x))
            (Finset.univ.image (fun x : Fin m → Fin (k+1) => S' x))) ∧
        (D.card : ℝ) - 2*β*(((k+1 : ℕ) : ℝ))^n ≤ ((dktUni VS).card : ℝ)) :
    ∀ r : ℕ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (i : Fin r → Fin k) (Ds : Fin r → Finset (Fin n → Fin (k+1))),
        (∀ j, IsInsens (i j) (Ds j)) →
        ∀ D : Finset (Fin n → Fin (k+1)), D = Finset.univ.filter (fun x => ∀ j, x ∈ Ds j) →
        2*(r:ℝ)*β*(((k+1 : ℕ) : ℝ))^n ≤ (D.card : ℝ) →
        ∃ VS : Finset (Subspace (Fin m) (Fin (k+1)) (Fin n)),
          (∀ S ∈ VS, ∀ x : Fin m → Fin (k+1), S x ∈ D) ∧
          (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
            Disjoint (Finset.univ.image (fun x : Fin m → Fin (k+1) => S x))
              (Finset.univ.image (fun x : Fin m → Fin (k+1) => S' x))) ∧
          (D.card : ℝ) - 2*(r:ℝ)*β*(((k+1 : ℕ) : ℝ))^n ≤ ((dktUni VS).card : ℝ) := by
  classical
  intro r
  induction r with
  | zero => intro h; omega
  | succ r ih =>
    intro hr m hm
    by_cases hr0 : r = 0
    · subst hr0
      obtain ⟨N0, hN0⟩ := hone m hm
      refine ⟨N0, ?_⟩
      intro n hn i Ds hIns D hD hdens
      have hD' : D = Ds 0 := by
        rw [hD]
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; exact h 0
        · intro h j; fin_cases j; exact h
      obtain ⟨VS, h1, h2, h3⟩ := hN0 n hn (i 0) D (by rw [hD']; exact hIns 0)
        (by simpa using hdens)
      refine ⟨VS, fun S hS x => h1 S hS x, h2, ?_⟩
      simpa using h3
    · obtain ⟨NP, hNP⟩ := hone m hm
      set Pm : ℕ := max 1 NP with hPm
      have hPm1 : 1 ≤ Pm := le_max_left _ _
      have hPmGe : NP ≤ Pm := le_max_right _ _
      have hN1 : ∀ n : ℕ, Pm ≤ n → ∀ (i : Fin k) (D : Finset (Fin n → Fin (k+1))),
          IsInsens i D → 2*β*(((k+1 : ℕ) : ℝ))^n ≤ (D.card : ℝ) →
          ∃ VS : Finset (Subspace (Fin m) (Fin (k+1)) (Fin n)),
            (∀ S ∈ VS, ∀ x : Fin m → Fin (k+1), S x ∈ D) ∧
            (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
              Disjoint (Finset.univ.image (fun x : Fin m → Fin (k+1) => S x))
                (Finset.univ.image (fun x : Fin m → Fin (k+1) => S' x))) ∧
            (D.card : ℝ) - 2*β*(((k+1 : ℕ) : ℝ))^n ≤ ((dktUni VS).card : ℝ) :=
        fun n hn => hNP n (le_trans hPmGe hn)
      obtain ⟨N2, hN2⟩ := ih (by omega) Pm hPm1
      refine ⟨N2, ?_⟩
      intro n hn i Ds hIns D hD hdens
      set Ds' : Fin r → Finset (Fin n → Fin (k+1)) := fun j => Ds (Fin.castSucc j) with hDs'
      set A : Finset (Fin n → Fin (k+1)) :=
        Finset.univ.filter (fun x => ∀ j : Fin r, x ∈ Ds' j) with hA
      have hmemD : ∀ x : Fin n → Fin (k+1), x ∈ D ↔ ∀ j : Fin (r+1), x ∈ Ds j := by
        intro x
        rw [hD]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hmemA : ∀ x : Fin n → Fin (k+1), x ∈ A ↔ ∀ j : Fin r, x ∈ Ds (Fin.castSucc j) := by
        intro x
        rw [hA]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h j; have := h j; rwa [hDs'] at this
        · intro h j; rw [hDs']; exact h j
      have hAins : ∀ j, IsInsens (i (Fin.castSucc j)) (Ds' j) := fun j => hIns _
      have hDsubA : D ⊆ A := by
        intro x hx
        rw [hmemA]
        intro j
        rw [hmemD] at hx
        exact hx (Fin.castSucc j)
      have hdensA : 2*(r:ℝ)*β*(((k+1 : ℕ) : ℝ))^n ≤ (A.card : ℝ) := by
        have h1 : (D.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hDsubA
        have h2 : 2*(r:ℝ)*β*(((k+1 : ℕ) : ℝ))^n ≤ 2*((r:ℝ)+1)*β*(((k+1 : ℕ) : ℝ))^n := by
          have : (0:ℝ) ≤ β*(((k+1 : ℕ) : ℝ))^n := by positivity
          nlinarith
        have h3 : 2*((r:ℝ)+1)*β*(((k+1 : ℕ) : ℝ))^n
            = 2*((r+1:ℕ):ℝ)*β*(((k+1 : ℕ) : ℝ))^n := by push_cast; ring
        linarith
      obtain ⟨VS1, hsub1, hdisj1, hcov1⟩ :=
        hN2 n hn (fun j => i (Fin.castSucc j)) Ds' hAins A rfl hdensA
      set AV : Subspace (Fin Pm) (Fin (k+1)) (Fin n) → Finset (Fin Pm → Fin (k+1)) :=
        fun V => Finset.univ.filter (fun x => V x ∈ Ds (Fin.last r)) with hAV
      set DV : Subspace (Fin Pm) (Fin (k+1)) (Fin n) → Finset (Fin Pm → Fin (k+1)) :=
        fun V => Finset.univ.filter (fun x => V x ∈ D) with hDV
      have hAVins : ∀ V, IsInsens (i (Fin.last r)) (AV V) := fun V =>
        dktInsens_pullback V (hIns (Fin.last r))
      have hDVsub : ∀ V, DV V ⊆ AV V := by
        intro V x hx
        rw [hDV, Finset.mem_filter] at hx
        rw [hAV, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmemD] at hx
        exact hx.2 (Fin.last r)
      have hinner : ∀ V, ∃ VSV : Finset (Subspace (Fin m) (Fin (k+1)) (Fin Pm)),
          (∀ W ∈ VSV, ∀ y : Fin m → Fin (k+1), W y ∈ AV V) ∧
          (∀ W ∈ VSV, ∀ W' ∈ VSV, W ≠ W' →
            Disjoint (Finset.univ.image (fun x : Fin m → Fin (k+1) => W x))
              (Finset.univ.image (fun x : Fin m → Fin (k+1) => W' x))) ∧
          ((DV V).card : ℝ) - 2*β*(((k+1 : ℕ) : ℝ))^Pm ≤ ((dktUni VSV).card : ℝ) := by
        intro V
        by_cases hcond : 2*β*(((k+1 : ℕ) : ℝ))^Pm ≤ ((AV V).card : ℝ)
        · obtain ⟨VSV, h1, h2, h3⟩ := hN1 Pm le_rfl (i (Fin.last r)) (AV V) (hAVins V) hcond
          refine ⟨VSV, h1, h2, ?_⟩
          have hdle : ((DV V).card : ℝ) ≤ ((AV V).card : ℝ) := by
            exact_mod_cast Finset.card_le_card (hDVsub V)
          linarith
        · refine ⟨∅, ?_, ?_, ?_⟩
          · intro W hW; simp at hW
          · intro W hW; simp at hW
          · have h1 : ((DV V).card : ℝ) ≤ ((AV V).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (hDVsub V)
            have h2 : ((DV V).card : ℝ) < 2*β*(((k+1 : ℕ) : ℝ))^Pm :=
              lt_of_le_of_lt h1 (lt_of_not_ge hcond)
            simp only [dktUni, Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero]
            linarith
      choose innerV hinner1 hinner2 hinner3 using hinner
      set UNI : Finset (Subspace (Fin m) (Fin (k+1)) (Fin n)) :=
        VS1.biUnion (fun V => (innerV V).image (fun W => dktComp V W)) with hUNI
      have hinnerSubDV : ∀ V ∈ VS1, dktUni (innerV V) ⊆ DV V := by
        intro V hV x hx
        rw [mem_dktUni] at hx
        obtain ⟨W, hW, y, rfl⟩ := hx
        rw [hDV, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmemD]
        intro j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · have h1 : V (W y) ∈ A := hsub1 V hV (W y)
          rw [hmemA] at h1
          exact h1 j'
        · have h1 := hinner1 V W hW y
          rw [hAV, Finset.mem_filter] at h1
          exact h1.2
      have hUni_eq : dktUni UNI = VS1.biUnion (fun V => (dktUni (innerV V)).image V) := by
        ext x
        constructor
        · intro hx
          rw [hUNI, mem_dktUni] at hx
          obtain ⟨S, hS, y, rfl⟩ := hx
          rw [Finset.mem_biUnion] at hS
          obtain ⟨V, hV, hSV⟩ := hS
          rw [Finset.mem_image] at hSV
          obtain ⟨W, hW, rfl⟩ := hSV
          rw [Finset.mem_biUnion]
          refine ⟨V, hV, ?_⟩
          rw [Finset.mem_image]
          exact ⟨W y, mem_dktUni.mpr ⟨W, hW, y, rfl⟩, (dktComp_apply V W y).symm⟩
        · intro hx
          rw [Finset.mem_biUnion] at hx
          obtain ⟨V, hV, hxV⟩ := hx
          rw [Finset.mem_image] at hxV
          obtain ⟨y, hy, rfl⟩ := hxV
          rw [mem_dktUni] at hy
          obtain ⟨W, hW, u, rfl⟩ := hy
          rw [mem_dktUni]
          exact ⟨dktComp V W, by
            rw [Finset.mem_biUnion]
            exact ⟨V, hV, by rw [Finset.mem_image]; exact ⟨W, hW, rfl⟩⟩,
            u, dktComp_apply V W u⟩
      have hDUNI1 : D ∩ dktUni VS1 = VS1.biUnion (fun V => (DV V).image V) := by
        ext x
        constructor
        · intro hx
          rw [Finset.mem_inter, mem_dktUni] at hx
          obtain ⟨hxD, hxu⟩ := hx
          obtain ⟨V, hV, y, rfl⟩ := hxu
          rw [Finset.mem_biUnion]
          refine ⟨V, hV, ?_⟩
          rw [Finset.mem_image]
          exact ⟨y, by rw [hDV, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hxD⟩, rfl⟩
        · intro hx
          rw [Finset.mem_biUnion] at hx
          obtain ⟨V, hV, hxV⟩ := hx
          rw [Finset.mem_image] at hxV
          obtain ⟨y, hy, rfl⟩ := hxV
          rw [Finset.mem_inter, mem_dktUni]
          rw [hDV, Finset.mem_filter] at hy
          exact ⟨hy.2, ⟨V, hV, y, rfl⟩⟩
      have hdisjMID : (VS1 : Set (Subspace (Fin Pm) (Fin (k+1)) (Fin n))).PairwiseDisjoint
          (fun V => (DV V).image V) := by
        intro V₁ hV₁ V₂ hV₂ hne
        have hdis := hdisj1 V₁ hV₁ V₂ hV₂ hne
        show Disjoint ((DV V₁).image V₁) ((DV V₂).image V₂)
        rw [Finset.disjoint_left] at hdis ⊢
        intro z hz hz'
        rw [Finset.mem_image] at hz hz'
        obtain ⟨y₁, -, hy₁⟩ := hz
        obtain ⟨y₂, -, hy₂⟩ := hz'
        exact hdis
          (Finset.mem_image.mpr ⟨y₁, Finset.mem_univ _, hy₁⟩)
          (Finset.mem_image.mpr ⟨y₂, Finset.mem_univ _, hy₂⟩)
      have hdisjNID : (VS1 : Set (Subspace (Fin Pm) (Fin (k+1)) (Fin n))).PairwiseDisjoint
          (fun V => (dktUni (innerV V)).image V) := by
        intro V₁ hV₁ V₂ hV₂ hne
        have hdis := hdisj1 V₁ hV₁ V₂ hV₂ hne
        show Disjoint ((dktUni (innerV V₁)).image V₁) ((dktUni (innerV V₂)).image V₂)
        rw [Finset.disjoint_left] at hdis ⊢
        intro z hz hz'
        rw [Finset.mem_image] at hz hz'
        obtain ⟨y₁, -, hy₁⟩ := hz
        obtain ⟨y₂, -, hy₂⟩ := hz'
        exact hdis
          (Finset.mem_image.mpr ⟨y₁, Finset.mem_univ _, hy₁⟩)
          (Finset.mem_image.mpr ⟨y₂, Finset.mem_univ _, hy₂⟩)
      have hcardDV : ∀ V, ((DV V).image V).card = (DV V).card := by
        intro V
        rw [Finset.card_image_of_injective]
        intro y y' h
        exact dktSubspace_injective V h
      have hcardNID : ∀ V, ((dktUni (innerV V)).image V).card = (dktUni (innerV V)).card := by
        intro V
        rw [Finset.card_image_of_injective]
        intro y y' h
        exact dktSubspace_injective V h
      have hVS1card : (VS1.card : ℝ) * (((k+1 : ℕ) : ℝ))^Pm = ((dktUni VS1).card : ℝ) := by
        have h1 : ((dktUni VS1).card : ℝ) = ∑ V ∈ VS1, (((k+1 : ℕ) : ℝ))^Pm := by
          rw [dktUni, Finset.card_biUnion hdisj1, Nat.cast_sum]
          apply Finset.sum_congr rfl
          intro V _
          rw [dktImage_card' V]
          push_cast; ring
        rw [h1, Finset.sum_const, nsmul_eq_mul]
      have hXDle : ((dktUni VS1).card : ℝ) ≤ (((k+1 : ℕ) : ℝ))^n := by
        have h1 := Finset.card_le_univ (dktUni VS1)
        simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at h1
        calc ((dktUni VS1).card : ℝ) ≤ (((k+1)^n : ℕ) : ℝ) := by exact_mod_cast h1
          _ = (((k+1 : ℕ) : ℝ))^n := by push_cast; ring
      have hDVsum : ∑ V ∈ VS1, ((DV V).card : ℝ) = ((D ∩ dktUni VS1).card : ℝ) := by
        rw [hDUNI1, Finset.card_biUnion hdisjMID, Nat.cast_sum]
        exact Finset.sum_congr rfl (fun V _ => by rw [hcardDV V])
      have hNIDsum : ∑ V ∈ VS1, ((dktUni (innerV V)).card : ℝ) = ((dktUni UNI).card : ℝ) := by
        rw [hUni_eq, Finset.card_biUnion hdisjNID, Nat.cast_sum]
        exact Finset.sum_congr rfl (fun V _ => by rw [hcardNID V])
      have hstepV : ∀ V ∈ VS1,
          ((DV V).card : ℝ) ≤ ((dktUni (innerV V)).card : ℝ) + 2*β*(((k+1 : ℕ) : ℝ))^Pm := by
        intro V hV
        have hsd : ((DV V).card : ℝ) - ((dktUni (innerV V)).card : ℝ)
            = (((DV V) \ dktUni (innerV V)).card : ℝ) := by
          rw [Finset.card_sdiff_of_subset (hinnerSubDV V hV),
            Nat.cast_sub (Finset.card_le_card (hinnerSubDV V hV))]
        have hb : (((DV V) \ dktUni (innerV V)).card : ℝ) ≤ 2*β*(((k+1 : ℕ) : ℝ))^Pm := by
          have h4 : ((DV V).card : ℝ) - ((dktUni (innerV V)).card : ℝ)
              ≤ 2*β*(((k+1 : ℕ) : ℝ))^Pm := by
            linarith [hinner3 V]
          linarith [hsd ▸ h4]
        linarith [hsd ▸ hb]
      have hDcard : (D.card : ℝ)
          = ((D \ dktUni VS1).card : ℝ) + ((D ∩ dktUni VS1).card : ℝ) := by
        have h1 : (D \ dktUni VS1).card + (D ∩ dktUni VS1).card = D.card :=
          Finset.card_sdiff_add_card_inter D (dktUni VS1)
        rw [← h1, Nat.cast_add]
      have hcovA : ((D \ dktUni VS1).card : ℝ) ≤ 2*(r:ℝ)*β*(((k+1 : ℕ) : ℝ))^n := by
        have h1 : (D \ dktUni VS1).card ≤ (A \ dktUni VS1).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_sdiff] at hx ⊢
          exact ⟨hDsubA hx.1, hx.2⟩
        have h2 : ((A \ dktUni VS1).card : ℝ) ≤ 2*(r:ℝ)*β*(((k+1 : ℕ) : ℝ))^n := by
          rw [Finset.card_sdiff_of_subset (dktUni_subset hsub1),
            Nat.cast_sub (Finset.card_le_card (dktUni_subset hsub1))]
          linarith [hcov1]
        exact le_trans (by exact_mod_cast h1) h2
      have hsubUNI : ∀ S ∈ UNI, ∀ x : Fin m → Fin (k+1), S x ∈ D := by
        intro S hS x
        rw [hUNI, Finset.mem_biUnion] at hS
        obtain ⟨V, hV, hSV⟩ := hS
        rw [Finset.mem_image] at hSV
        obtain ⟨W, hW, rfl⟩ := hSV
        rw [dktComp_apply]
        rw [hmemD]
        intro j
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · have h1 : V (W x) ∈ A := hsub1 V hV (W x)
          rw [hmemA] at h1
          exact h1 j'
        · have h1 := hinner1 V W hW x
          rw [hAV, Finset.mem_filter] at h1
          exact h1.2
      have hdisjUNI : ∀ S₁ ∈ UNI, ∀ S₂ ∈ UNI, S₁ ≠ S₂ →
          Disjoint (Finset.univ.image (fun x : Fin m → Fin (k+1) => S₁ x))
            (Finset.univ.image (fun x : Fin m → Fin (k+1) => S₂ x)) := by
        intro S₁ hS₁ S₂ hS₂ hne
        rw [hUNI, Finset.mem_biUnion] at hS₁ hS₂
        obtain ⟨V₁, hV₁, hS₁V⟩ := hS₁
        obtain ⟨V₂, hV₂, hS₂V⟩ := hS₂
        rw [Finset.mem_image] at hS₁V hS₂V
        obtain ⟨W₁, hW₁, rfl⟩ := hS₁V
        obtain ⟨W₂, hW₂, rfl⟩ := hS₂V
        rw [dktCompImg, dktCompImg]
        by_cases hVV : V₁ = V₂
        · cases hVV
          have hWW : W₁ ≠ W₂ := fun hWW => hne (by rw [hWW])
          have hdis := hinner2 V₁ W₁ hW₁ W₂ hW₂ hWW
          rw [Finset.disjoint_left] at hdis ⊢
          intro z hz hz'
          rw [Finset.mem_image] at hz hz'
          obtain ⟨y₁, hy₁, hy1⟩ := hz
          obtain ⟨y₂, hy₂, hy2⟩ := hz'
          have hye : y₁ = y₂ := dktSubspace_injective V₁ (hy1.trans hy2.symm)
          subst hye
          exact hdis hy₁ hy₂
        · rw [Finset.disjoint_left]
          intro z hz hz'
          rw [Finset.mem_image] at hz hz'
          obtain ⟨y₁, -, hy₁⟩ := hz
          obtain ⟨y₂, -, hy₂⟩ := hz'
          exact (Finset.disjoint_left.mp (hdisj1 V₁ hV₁ V₂ hV₂ hVV))
            (Finset.mem_image.mpr ⟨y₁, Finset.mem_univ _, hy₁⟩)
            (Finset.mem_image.mpr ⟨y₂, Finset.mem_univ _, hy₂⟩)
      have hcovUNI : (D.card : ℝ) - 2*((r:ℝ)+1)*β*(((k+1 : ℕ) : ℝ))^n ≤ ((dktUni UNI).card : ℝ) := by
        have hsum1 : ∑ V ∈ VS1, ((DV V).card : ℝ)
            ≤ (∑ V ∈ VS1, ((dktUni (innerV V)).card : ℝ))
              + 2*β*(((k+1 : ℕ) : ℝ))^Pm * (VS1.card : ℝ) := by
          calc ∑ V ∈ VS1, ((DV V).card : ℝ)
              ≤ ∑ V ∈ VS1, (((dktUni (innerV V)).card : ℝ) + 2*β*(((k+1 : ℕ) : ℝ))^Pm) :=
                Finset.sum_le_sum hstepV
            _ = (∑ V ∈ VS1, ((dktUni (innerV V)).card : ℝ))
                  + (VS1.card : ℝ) * (2*β*(((k+1 : ℕ) : ℝ))^Pm) := by
                rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            _ = (∑ V ∈ VS1, ((dktUni (innerV V)).card : ℝ))
                  + 2*β*(((k+1 : ℕ) : ℝ))^Pm * (VS1.card : ℝ) := by ring
        have hXp : 2*β*(((k+1 : ℕ) : ℝ))^Pm * (VS1.card : ℝ) ≤ 2*β*(((k+1 : ℕ) : ℝ))^n := by
          have h6 : 2*β*(((k+1 : ℕ) : ℝ))^Pm * (VS1.card : ℝ)
              = 2*β * ((VS1.card : ℝ) * (((k+1 : ℕ) : ℝ))^Pm) := by ring
          rw [h6, hVS1card]
          have h7 : (0:ℝ) ≤ 2*β := by positivity
          nlinarith [hXDle, h7]
        have hDUNC : ((D ∩ dktUni VS1).card : ℝ) ≤ ((dktUni UNI).card : ℝ)
            + 2*β*(((k+1 : ℕ) : ℝ))^n := by
          rw [← hDVsum, ← hNIDsum]
          linarith [hsum1, hXp]
        have hbig : (D.card : ℝ) ≤ 2*(r:ℝ)*β*(((k+1 : ℕ) : ℝ))^n + ((dktUni UNI).card : ℝ)
            + 2*β*(((k+1 : ℕ) : ℝ))^n := by
          linarith [hDcard, hcovA, hDUNC]
        have hone2 : 2*β*(((k+1 : ℕ) : ℝ))^n = 2*(1:ℝ)*β*(((k+1 : ℕ) : ℝ))^n := by ring
        linarith [hbig]
      have hcast : 2*((r+1:ℕ):ℝ)*β*(((k+1 : ℕ) : ℝ))^n
          = 2*((r:ℝ)+1)*β*(((k+1 : ℕ) : ℝ))^n := by push_cast; ring
      have hleUNI : ((D \ dktUni UNI).card : ℝ) = (D.card : ℝ) - ((dktUni UNI).card : ℝ) := by
        rw [Finset.card_sdiff_of_subset (dktUni_subset hsubUNI),
          Nat.cast_sub (Finset.card_le_card (dktUni_subset hsubUNI))]
      refine ⟨UNI, hsubUNI, hdisjUNI, ?_⟩
      rw [hcast]
      exact hcovUNI
/-- **The tiling lemma** of Dodos–Kanellopoulos–Tyros (their Corollary 13). -/
theorem dkt_tiling (k : ℕ) (hk : 2 ≤ k)
    (hc5 : ∀ (m : ℕ), 1 ≤ m → ∀ β : ℝ, 0 < β → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ D : Finset (Fin n → Fin (k+1)), β * (((k+1 : ℕ) : ℝ)) ^ n ≤ (D.card : ℝ) →
        ∃ V : _root_.Combinatorics.Subspace (Fin m) (Fin (k+1)) (Fin n),
          ∀ x : Fin m → Fin k, V (Commons.Combinatorics.Ramsey.kvec x) ∈ D)
    (d : ℕ) (hd : 1 ≤ d) (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ Ds : Fin k → Finset (Fin n → Fin (k+1)),
      (∀ i, Commons.Combinatorics.Ramsey.IsInsens i (Ds i)) →
      ∀ D : Finset (Fin n → Fin (k+1)), D = Finset.univ.filter (fun x => ∀ i, x ∈ Ds i) →
      2 * ((k : ℝ)) * β * (((k+1 : ℕ) : ℝ)) ^ n ≤ (D.card : ℝ) →
      ∃ VS : Finset (_root_.Combinatorics.Subspace (Fin d) (Fin (k+1)) (Fin n)),
        (∀ S ∈ VS, ∀ x : Fin d → Fin (k+1), S x ∈ D) ∧
        (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
          Disjoint (Finset.univ.image (fun x => S x)) (Finset.univ.image (fun x => S' x))) ∧
        (D.card : ℝ) - 2 * ((k : ℝ)) * β * (((k+1 : ℕ) : ℝ)) ^ n ≤
          ((VS.biUnion (fun S => Finset.univ.image (fun x => S x))).card : ℝ) := by
  classical
  have hone : ∀ m : ℕ, 1 ≤ m → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (i : Fin k) (D : Finset (Fin n → Fin (k+1))),
      IsInsens i D → 2*β*(((k+1 : ℕ) : ℝ))^n ≤ (D.card : ℝ) →
      ∃ VS : Finset (Subspace (Fin m) (Fin (k+1)) (Fin n)),
        (∀ S ∈ VS, ∀ x : Fin m → Fin (k+1), S x ∈ D) ∧
        (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
          Disjoint (Finset.univ.image (fun x : Fin m → Fin (k+1) => S x))
            (Finset.univ.image (fun x : Fin m → Fin (k+1) => S' x))) ∧
        (D.card : ℝ) - 2*β*(((k+1 : ℕ) : ℝ))^n ≤ ((dktUni VS).card : ℝ) := by
    intro m hm
    obtain ⟨Nh, hNh⟩ := hc5 m hm β hβ
    set M : ℕ := max m Nh with hM
    have hMge : Nh ≤ M := le_max_right _ _
    have hMm : m ≤ M := le_max_left _ _
    have hhc5M : ∀ F : Finset (Fin M → Fin (k+1)),
        β * (((k+1 : ℕ) : ℝ))^M ≤ (F.card : ℝ) →
        ∃ V : Subspace (Fin m) (Fin (k+1)) (Fin M), ∀ x : Fin m → Fin k, V (kvec x) ∈ F :=
      fun F hF => hNh M (le_trans hMge le_rfl) F hF
    have hC0pos : 0 < dktC0 k m M := by
      rw [dktC0]
      exact Fintype.card_pos_iff.mpr ⟨dktIdSub hMm⟩
    have hk1pos : (0 : ℝ) < (((k+1 : ℕ) : ℝ)) := by positivity
    set D0 : ℝ := (dktC0 k m M : ℝ) * (((k+1 : ℕ) : ℝ))^(M-m) with hD0
    have hD0pos : 0 < D0 := by rw [hD0]; positivity
    have hθpos : 0 < β / D0 := div_pos hβ hD0pos
    obtain ⟨T, hT⟩ : ∃ T : ℕ, 1 ≤ (T : ℝ) * (β / D0) := by
      refine ⟨⌊(β / D0)⁻¹⌋₊ + 1, ?_⟩
      have hlt : (β / D0)⁻¹ < ((⌊(β / D0)⁻¹⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have hT1 : ((⌊(β / D0)⁻¹⌋₊ + 1 : ℕ) : ℝ) * (β / D0) ≥ (β / D0)⁻¹ * (β / D0) := by
        have h1 : (β / D0)⁻¹ ≤ ((⌊(β / D0)⁻¹⌋₊ : ℕ) : ℝ) + 1 := le_of_lt hlt
        have h2 : ((⌊(β / D0)⁻¹⌋₊ + 1 : ℕ) : ℝ) = ((⌊(β / D0)⁻¹⌋₊ : ℕ) : ℝ) + 1 := by
          push_cast; ring
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt hθpos)
      rwa [inv_mul_cancel₀ (ne_of_gt hθpos)] at hT1
    have hNsingle : ∀ i : Fin k, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ D : Finset (Fin n → Fin (k+1)), IsInsens i D →
        2*β*(((k+1 : ℕ) : ℝ))^n ≤ (D.card : ℝ) →
        ∃ VS : Finset (Subspace (Fin m) (Fin (k+1)) (Fin n)),
          (∀ S ∈ VS, ∀ x : Fin m → Fin (k+1), S x ∈ D) ∧
          (∀ S ∈ VS, ∀ S' ∈ VS, S ≠ S' →
            Disjoint (Finset.univ.image (fun x : Fin m → Fin (k+1) => S x))
              (Finset.univ.image (fun x : Fin m → Fin (k+1) => S' x))) ∧
          (D.card : ℝ) - 2*β*(((k+1 : ℕ) : ℝ))^n ≤ ((dktUni VS).card : ℝ) :=
      fun i => dktSingle (k := k) hk (d := m) (M := M) hm hMm (i := i) hβ hβ1 hhc5M T hT
    refine ⟨(Finset.univ : Finset (Fin k)).sup (fun i => Classical.choose (hNsingle i)), ?_⟩
    intro n hn i D hD hdens
    exact Classical.choose_spec (hNsingle i) n
      (le_trans (Finset.le_sup (f := fun i => Classical.choose (hNsingle i))
        (Finset.mem_univ i)) hn) D hD hdens
  obtain ⟨N, hN⟩ := dktMulti (k := k) hk β hβ hβ1 hone k (by omega) d hd
  refine ⟨N, ?_⟩
  intro n hn Ds hIns D hD hdens
  obtain ⟨VS, h1, h2, h3⟩ := hN n hn (fun i => i) Ds hIns D hD hdens
  exact ⟨VS, h1, h2, h3⟩

end

end Commons.Combinatorics.Ramsey
