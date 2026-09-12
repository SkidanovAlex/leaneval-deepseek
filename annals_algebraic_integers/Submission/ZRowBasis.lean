import Mathlib

noncomputable section
open scoped BigOperators Matrix

/-!
# Clearing an integer column by unimodular row operations

Two elementary lemmas over the integers, used by `Submission.MinkFlagBasis`:

* `pair_clean`: from a pair `(a, b) ≠ (0, 0)` we can reach `(g, 0)` with `g ≠ 0`
  by a `2×2` integer matrix of determinant one (`g` is the gcd of `a` and `b`).

* `clearVec`: any nonzero integer vector `c : Fin (k + 1) → ℤ` can be transformed by
  an integer matrix `Q` of determinant `1` into a vector whose first entry is nonzero
  and all of whose other entries are zero.
-/

namespace Submission.ZRowBasis



theorem pair_clean {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) :
    ∃ (g : ℤ) (M : Matrix (Fin 2) (Fin 2) ℤ),
      g ≠ 0 ∧ M.det = 1 ∧ (M *ᵥ ![a, b] = ![g, 0]) := by
  have hgpos : 0 < a.gcd b := by
    rcases h with ha | hb
    · exact Int.gcd_pos_of_ne_zero_left b ha
    · exact Int.gcd_pos_of_ne_zero_right a hb
  have hg0nat : (a.gcd b : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hgpos)
  let g : ℤ := (a.gcd b : ℤ)
  have hg0 : g ≠ 0 := by simpa [g] using hg0nat
  obtain ⟨a', b', hcop, haeq, hbeq⟩ := Int.exists_gcd_one hgpos
  have haeq' : a = a' * g := by simpa [g] using haeq
  have hbeq' : b = b' * g := by simpa [g] using hbeq
  let s : ℤ := a'.gcdA b'
  let t : ℤ := a'.gcdB b'
  have hbez : a' * s + b' * t = 1 := by
    have hg := Int.gcd_eq_gcd_ab a' b'
    rw [hcop] at hg
    simpa [s, t] using hg.symm
  have hL : a * s + b * t = g := by
    calc
      a * s + b * t = (a' * g) * s + (b' * g) * t := by rw [haeq', hbeq']
      _ = (a' * s + b' * t) * g := by ring
      _ = g := by rw [hbez]; ring
  have hR : -b' * a + a' * b = 0 := by
    calc
      -b' * a + a' * b = -b' * (a' * g) + a' * (b' * g) := by rw [haeq', hbeq']
      _ = 0 := by ring
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![s, t; -b', a']
  refine ⟨g, M, ?_, ?_, ?_⟩
  · exact hg0
  · rw [Matrix.det_fin_two_of]
    nlinarith [hbez]
  · ext i
    fin_cases i
    · simp [M]
      nlinarith [hL]
    · simp [M]
      nlinarith [hR]

/-- Embed a square matrix `B` into the top-left of a matrix of size `n+1`, fixing the last
coordinate (identity on row/column `Fin.last n`). -/
def emb {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i j =>
    if hi : i = Fin.last n then (if i = j then 1 else 0)
    else if hj : j = Fin.last n then 0
    else B (Fin.castPred i hi) (Fin.castPred j hj)

@[simp] lemma emb_castSucc_castSucc {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    emb B (Fin.castSucc i) (Fin.castSucc j) = B i j := by
  simp [emb]

@[simp] lemma emb_castSucc_last {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    emb B (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [emb]

@[simp] lemma emb_last_castSucc {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    emb B (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [emb]
  exact (Fin.castSucc_ne_last j).symm

@[simp] lemma emb_last_last {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    emb B (Fin.last n) (Fin.last n) = 1 := by
  simp [emb]

lemma emb_mulVec_castSucc {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (w : Fin (n + 1) → ℤ)
    (i : Fin n) : (emb B *ᵥ w) (Fin.castSucc i) = (B *ᵥ (w ∘ Fin.castSucc)) i := by
  change (∑ j : Fin (n + 1), emb B (Fin.castSucc i) j * w j) =
    (∑ j : Fin n, B i j * w (Fin.castSucc j))
  rw [Fin.sum_univ_castSucc]
  simp

lemma emb_mulVec_last {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (w : Fin (n + 1) → ℤ) :
    (emb B *ᵥ w) (Fin.last n) = w (Fin.last n) := by
  change (∑ j : Fin (n + 1), emb B (Fin.last n) j * w j) = w (Fin.last n)
  rw [Fin.sum_univ_castSucc]
  simp

/-- `Fin (n+1) ≃ Fin n ⊕ Unit`, sending `castSucc i` to `inl i` and `last n` to `inr ()`. -/
def finLastEquiv (n : ℕ) : Fin (n + 1) ≃ (Fin n ⊕ Unit) where
  toFun i := if h : i = Fin.last n then Sum.inr Unit.unit else Sum.inl (Fin.castPred i h)
  invFun s := Sum.elim Fin.castSucc (fun _ => Fin.last n) s
  left_inv := by
    intro i
    by_cases h : i = Fin.last n
    · simp [h]
    · simp [h]
  right_inv := by
    intro s
    cases s with
    | inl i => simp
    | inr u => simp

@[simp] lemma finLastEquiv_castSucc (n : ℕ) (i : Fin n) :
    finLastEquiv n (Fin.castSucc i) = Sum.inl i := by
  simp [finLastEquiv]

@[simp] lemma finLastEquiv_last (n : ℕ) :
    finLastEquiv n (Fin.last n) = Sum.inr Unit.unit := by
  simp [finLastEquiv]

@[simp] lemma finLastEquiv_symm_inl (n : ℕ) (i : Fin n) :
    (finLastEquiv n).symm (Sum.inl i) = Fin.castSucc i := by
  rfl

@[simp] lemma finLastEquiv_symm_inr (n : ℕ) (u : Unit) :
    (finLastEquiv n).symm (Sum.inr u) = Fin.last n := by
  rfl

lemma det_emb {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : (emb B).det = B.det := by
  let e : Fin (n + 1) ≃ (Fin n ⊕ Unit) := finLastEquiv n
  have hre : Matrix.reindex e e (emb B) =
      Matrix.fromBlocks B 0 0 (1 : Matrix Unit Unit ℤ) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Matrix.reindex_apply, e]
      | inr u => simp [Matrix.reindex_apply, e]
    | inr u =>
      cases j with
      | inl j => simp [Matrix.reindex_apply, e]
      | inr v => simp [Matrix.reindex_apply, e]
  calc
    (emb B).det = (Matrix.reindex e e (emb B)).det := by
      rw [Matrix.det_reindex_self]
    _ = (Matrix.fromBlocks B 0 0 (1 : Matrix Unit Unit ℤ)).det := by rw [hre]
    _ = B.det * (1 : Matrix Unit Unit ℤ).det := by rw [Matrix.det_fromBlocks_zero₂₁]
    _ = B.det := by simp

/-- A 2×2 matrix `M` acting on the pair of coordinates `(0, Fin.last (n+1))` of a vector of
length `n+2`, leaving every other coordinate fixed. -/
def blockLast {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ :=
  fun i j =>
    if hi0 : i = 0 then
      (if hj0 : j = 0 then M 0 0
       else if hjL : j = Fin.last (n + 1) then M 0 1 else 0)
    else if hiL : i = Fin.last (n + 1) then
      (if hj0 : j = 0 then M 1 0
       else if hjL : j = Fin.last (n + 1) then M 1 1 else 0)
    else if i = j then 1 else 0

@[simp] lemma blockLast_00 {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) :
    blockLast (n := n) M 0 0 = M 0 0 := by
  simp [blockLast]

@[simp] lemma blockLast_0L {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) :
    blockLast (n := n) M 0 (Fin.last (n + 1)) = M 0 1 := by
  simp [blockLast]

@[simp] lemma blockLast_L0 {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) :
    blockLast (n := n) M (Fin.last (n + 1)) 0 = M 1 0 := by
  simp [blockLast]

@[simp] lemma blockLast_LL {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) :
    blockLast (n := n) M (Fin.last (n + 1)) (Fin.last (n + 1)) = M 1 1 := by
  simp [blockLast]

@[simp] lemma blockLast_0_succ_castSucc {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin n) :
    blockLast (n := n) M 0 (Fin.succ (Fin.castSucc x)) = 0 := by
  have hx0 : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero (Fin.castSucc x)
  have hxL : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp [blockLast, hx0, hxL]

@[simp] lemma blockLast_L_succ_castSucc {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin n) :
    blockLast (n := n) M (Fin.last (n + 1)) (Fin.succ (Fin.castSucc x)) = 0 := by
  have hx0 : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero (Fin.castSucc x)
  have hxL : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp [blockLast, hx0, hxL]

@[simp] lemma blockLast_succ_castSucc_0 {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin n) :
    blockLast (n := n) M (Fin.succ (Fin.castSucc x)) 0 = 0 := by
  have hx0 : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero (Fin.castSucc x)
  have hxL : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp [blockLast, hx0, hxL]

@[simp] lemma blockLast_succ_castSucc_L {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin n) :
    blockLast (n := n) M (Fin.succ (Fin.castSucc x)) (Fin.last (n + 1)) = 0 := by
  have hx0 : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero (Fin.castSucc x)
  have hxL : (Fin.succ (Fin.castSucc x) : Fin (n + 2)) ≠ Fin.last (n + 1) := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_last] at hv
    omega
  simp [blockLast, hx0, hxL]


@[simp] lemma blockLast_mid_mid {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (i j : Fin n) :
    blockLast (n := n) M (Fin.succ (Fin.castSucc i)) (Fin.succ (Fin.castSucc j)) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [blockLast]
  · have hne : ¬ Fin.succ (Fin.castSucc i) = Fin.succ (Fin.castSucc j) := by
      intro h
      apply hij
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    have hi0 : (Fin.succ (Fin.castSucc i) : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero (Fin.castSucc i)
    have hiL : (Fin.succ (Fin.castSucc i) : Fin (n + 2)) ≠ Fin.last (n + 1) := by
      intro h
      have hv := congrArg Fin.val h
      simp [Fin.val_castSucc, Fin.val_last] at hv
      omega
    simp [blockLast, hne, hi0, hiL, hij]

lemma blockLast_mulVec_0 {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (c : Fin (n + 2) → ℤ) :
    (blockLast (n := n) M *ᵥ c) 0 = M 0 0 * c 0 + M 0 1 * c (Fin.last (n + 1)) := by
  change (∑ j : Fin (n + 2), blockLast (n := n) M 0 j * c j) =
    M 0 0 * c 0 + M 0 1 * c (Fin.last (n + 1))
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_succ]
  simp

lemma blockLast_mulVec_last {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (c : Fin (n + 2) → ℤ) :
    (blockLast (n := n) M *ᵥ c) (Fin.last (n + 1)) =
      M 1 0 * c 0 + M 1 1 * c (Fin.last (n + 1)) := by
  change (∑ j : Fin (n + 2), blockLast (n := n) M (Fin.last (n + 1)) j * c j) =
    M 1 0 * c 0 + M 1 1 * c (Fin.last (n + 1))
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_succ]
  simp

lemma blockLast_mulVec_mid {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) (c : Fin (n + 2) → ℤ)
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hiL : i ≠ Fin.last (n + 1)) :
    (blockLast (n := n) M *ᵥ c) i = c i := by
  change (∑ j : Fin (n + 2), blockLast (n := n) M i j * c j) = c i
  have hrow : ∀ j : Fin (n + 2), blockLast (n := n) M i j = if i = j then 1 else 0 := by
    intro j
    simp [blockLast, hi0, hiL]
  simp_rw [hrow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hne
    by_cases h : i = j
    · exact False.elim (hne h.symm)
    · simp [h]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ i))

/-- forward map of `finHeadLastEquiv` -/
def finHeadLast_toFun (n : ℕ) : Fin (n + 2) → (Fin 2 ⊕ Fin n) := fun i =>
  if h0 : i = 0 then Sum.inl 0
  else if hL : i = Fin.last (n + 1) then Sum.inl 1
  else Sum.inr ⟨i.1 - 1, by
      have hi0' : i.1 ≠ 0 := fun hv => h0 (Fin.ext (by simpa [hv]))
      have hiL' : i.1 ≠ n + 1 := fun hv => hL (Fin.ext (by simpa [hv, Fin.val_last]))
      omega⟩

/-- backward map of `finHeadLastEquiv` -/
def finHeadLast_invFun (n : ℕ) : (Fin 2 ⊕ Fin n) → Fin (n + 2) := fun s =>
  match s with
  | Sum.inl j => if j = 0 then (0 : Fin (n + 2)) else Fin.last (n + 1)
  | Sum.inr x => Fin.succ (Fin.castSucc x)

/-- `Fin (n+2) ≃ Fin 2 ⊕ Fin n`, sending `0` to `inl 0`, `Fin.last (n+1)` to `inl 1`,
and middle coordinates `Fin.succ (Fin.castSucc x)` to `inr x`. -/
def finHeadLastEquiv (n : ℕ) : Fin (n + 2) ≃ (Fin 2 ⊕ Fin n) :=
{ toFun := finHeadLast_toFun n
  invFun := finHeadLast_invFun n
  left_inv := by
    intro i
    by_cases h0 : i = 0
    · subst i
      simp [finHeadLast_toFun, finHeadLast_invFun]
    · by_cases hL : i = Fin.last (n + 1)
      · subst i
        simp [finHeadLast_toFun, finHeadLast_invFun]
      · have hv0 : i.1 ≠ 0 := fun hv => h0 (Fin.ext (by simpa [hv]))
        have hvL : i.1 ≠ n + 1 := fun hv => hL (Fin.ext (by simpa [hv, Fin.val_last]))
        simp [finHeadLast_toFun, finHeadLast_invFun, h0, hL]
        apply Fin.ext
        simp [Fin.val_castSucc, Fin.val_succ]
        omega
  right_inv := by
    intro s
    cases s with
    | inl j =>
        by_cases hj : j = 0
        · subst j
          simp [finHeadLast_toFun, finHeadLast_invFun]
        · have hjv : j.1 ≠ 0 := fun hv => hj (Fin.ext (by simpa [hv]))
          have hj1 : j = (1 : Fin 2) := by
            apply Fin.ext
            omega
          rw [hj1]
          simp [finHeadLast_toFun, finHeadLast_invFun]
    | inr x =>
        simp [finHeadLast_toFun, finHeadLast_invFun] }

@[simp] lemma finHeadLastEquiv_zero (n : ℕ) : finHeadLastEquiv n (0 : Fin (n + 2)) = Sum.inl 0 := by
  simp [finHeadLastEquiv, finHeadLast_toFun]

@[simp] lemma finHeadLastEquiv_last (n : ℕ) :
    finHeadLastEquiv n (Fin.last (n + 1)) = Sum.inl 1 := by
  simp [finHeadLastEquiv, finHeadLast_toFun]

@[simp] lemma finHeadLastEquiv_succ_castSucc (n : ℕ) (x : Fin n) :
    finHeadLastEquiv n (Fin.succ (Fin.castSucc x)) = Sum.inr x := by
  simp [finHeadLastEquiv, finHeadLast_toFun]

@[simp] lemma finHeadLastEquiv_symm_inl_zero (n : ℕ) :
    (finHeadLastEquiv n).symm (Sum.inl (0 : Fin 2)) = (0 : Fin (n + 2)) := by
  rfl

@[simp] lemma finHeadLastEquiv_symm_inl_one (n : ℕ) :
    (finHeadLastEquiv n).symm (Sum.inl (1 : Fin 2)) = Fin.last (n + 1) := by
  rfl

@[simp] lemma finHeadLastEquiv_symm_inr (n : ℕ) (x : Fin n) :
    (finHeadLastEquiv n).symm (Sum.inr x) = Fin.succ (Fin.castSucc x) := by
  rfl

lemma det_blockLast {n : ℕ} (M : Matrix (Fin 2) (Fin 2) ℤ) : (blockLast (n := n) M).det = M.det := by
  let e : Fin (n + 2) ≃ (Fin 2 ⊕ Fin n) := finHeadLastEquiv n
  have hre : Matrix.reindex e e (blockLast (n := n) M) =
      Matrix.fromBlocks M 0 0 (1 : Matrix (Fin n) (Fin n) ℤ) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> simp [Matrix.reindex_apply, e, finHeadLastEquiv, finHeadLast_invFun]
      | inr j => fin_cases i <;> simp [Matrix.reindex_apply, e, finHeadLastEquiv, finHeadLast_invFun]
    | inr i =>
      cases j with
      | inl j => fin_cases j <;> simp [Matrix.reindex_apply, e, finHeadLastEquiv, finHeadLast_invFun]
      | inr j => simp [Matrix.reindex_apply, e, finHeadLastEquiv, finHeadLast_invFun, Matrix.one_apply]
  calc
    (blockLast (n := n) M).det = (Matrix.reindex e e (blockLast (n := n) M)).det := by
      rw [Matrix.det_reindex_self]
    _ = (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin n) (Fin n) ℤ)).det := by rw [hre]
    _ = M.det * (1 : Matrix (Fin n) (Fin n) ℤ).det := by rw [Matrix.det_fromBlocks_zero₂₁]
    _ = M.det := by simp

def shear {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  fun i k => (if i = k then 1 else 0) + (if i = 0 then (if k = j then 1 else 0) else 0)

lemma shear_eq_updateRow {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) :
    shear j hj = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ).updateRow 0
      ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) 0 + 1 • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) j) := by
  ext i k
  by_cases hi : i = 0
  · subst i
    simp [shear, Matrix.one_apply, eq_comm]
  · simp [shear, hi, Matrix.one_apply]

lemma shear_det {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) : (shear j hj).det = 1 := by
  rw [shear_eq_updateRow j hj]
  simpa using (Matrix.det_updateRow_add_smul_self (A := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ))
    (i := 0) (j := j) hj.symm (c := 1))

lemma shear_apply_zero {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) (c : Fin (n + 1) → ℤ) :
    (shear j hj *ᵥ c) 0 = c 0 + c j := by
  change (∑ k : Fin (n + 1), (shear j hj) 0 k * c k) = c 0 + c j
  rw [show shear j hj 0 = (fun k : Fin (n + 1) => (if 0 = k then 1 else 0) + (if k = j then 1 else 0)) by
    funext k
    simp [shear]]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp

lemma shear_apply_of_ne {n : ℕ} (j : Fin (n + 1)) (hj : j ≠ 0) (c : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) (hi : i ≠ 0) : (shear j hj *ᵥ c) i = c i := by
  change (∑ k : Fin (n + 1), (shear j hj) i k * c k) = c i
  have hrow : ∀ k : Fin (n + 1), (shear j hj) i k = if i = k then 1 else 0 := by
    intro k
    simp [shear, hi]
  simp_rw [hrow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hne
    by_cases h : i = k
    · exact False.elim (hne h.symm)
    · simp [h]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ i))

/-- If the first entry of `c` is nonzero then a unimodular matrix clears all other entries,
leaving the first entry nonzero. -/
theorem clearHead (n : ℕ) : ∀ c : Fin (n + 1) → ℤ, c 0 ≠ 0 →
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      Q.det = 1 ∧ (Q *ᵥ c) 0 ≠ 0 ∧ ∀ i : Fin (n + 1), i ≠ 0 → (Q *ᵥ c) i = 0 := by
  intro c hc0
  induction n with
  | zero =>
      refine ⟨1, ?_, ?_, ?_⟩
      · simp
      · simpa using hc0
      · intro i hi
        exfalso
        exact hi (Fin.ext (by simp))
  | succ n ih =>
      obtain ⟨g, M, hg, hdetM, hvec⟩ :=
        pair_clean (a := c 0) (b := c (Fin.last (n + 1))) (Or.inl hc0)
      let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ := blockLast (n := n) M
      have hA0 : (A *ᵥ c) 0 = g := by
        rw [blockLast_mulVec_0]
        simpa using (congrFun hvec 0)
      have hAL : (A *ᵥ c) (Fin.last (n + 1)) = 0 := by
        rw [blockLast_mulVec_last]
        simpa using (congrFun hvec 1)
      have hdetA : A.det = 1 := by
        dsimp [A]
        rw [det_blockLast]
        exact hdetM
      let w : Fin (n + 2) → ℤ := A *ᵥ c
      have hw0 : w 0 ≠ 0 := by
        dsimp [w]
        rw [hA0]
        exact hg
      let p : Fin (n + 1) → ℤ := fun i => w (Fin.castSucc i)
      have hp0 : p 0 ≠ 0 := by
        simpa [p] using hw0
      obtain ⟨B, hdetB, hB0, hBrest⟩ := ih p hp0
      let E : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ := emb B
      let Q : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ := E * A
      refine ⟨Q, ?_, ?_, ?_⟩
      · dsimp [Q, E]
        rw [Matrix.det_mul, det_emb]
        rw [hdetB, hdetA]
        simp
      · have hqw : Q *ᵥ c = E *ᵥ w := by
          dsimp [Q, w]
          rw [← Matrix.mulVec_mulVec]
        rw [hqw]
        dsimp [E]
        change ¬ (emb B *ᵥ w) (Fin.castSucc (0 : Fin (n + 1))) = 0
        rw [emb_mulVec_castSucc]
        have hcomp : w ∘ Fin.castSucc = p := by
          funext i
          rfl
        rw [hcomp]
        exact hB0
      · intro i hi
        have hqw : Q *ᵥ c = E *ᵥ w := by
          dsimp [Q, w]
          rw [← Matrix.mulVec_mulVec]
        rw [hqw]
        have hcases := Fin.eq_castSucc_or_eq_last i
        rcases hcases with ⟨i0, hi0⟩ | hiL
        · have hi00 : i0 ≠ 0 := by
            intro h0
            apply hi
            rw [hi0, h0]
            rfl
          subst hi0
          dsimp [E]
          rw [emb_mulVec_castSucc]
          have hcomp : w ∘ Fin.castSucc = p := by
            funext i
            rfl
          rw [hcomp]
          exact hBrest i0 hi00
        · rw [hiL]
          dsimp [E]
          rw [emb_mulVec_last]
          dsimp [w]
          exact hAL

/-- A nonzero integer vector `c` of length `k + 1` can be cleared into its first entry. -/
theorem clearVec (k : ℕ) : ∀ c : Fin (k + 1) → ℤ, c ≠ 0 →
    ∃ Q : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ,
      Q.det = 1 ∧ (Q *ᵥ c) 0 ≠ 0 ∧
        (∀ i : Fin (k + 1), i ≠ 0 → (Q *ᵥ c) i = 0) := by
  intro c hc
  by_cases hc0 : c 0 ≠ 0
  · obtain ⟨Q, hdet, h0, hrest⟩ := clearHead k c hc0
    exact ⟨Q, hdet, h0, hrest⟩
  · -- first entry vanishes: some other entry must be nonzero
    have hneq : c 0 = 0 := not_not.mp hc0
    have hex : ∃ j : Fin (k + 1), c j ≠ 0 := by
      by_contra h
      apply hc
      funext i
      by_contra hci
      exact (h ⟨i, hci⟩)
    obtain ⟨j, hj⟩ := hex
    have hj0 : j ≠ 0 := by
      intro hzero
      subst j
      exact hj hneq
    let S : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ := shear j hj0
    have hS0 : (S *ᵥ c) 0 ≠ 0 := by
      dsimp [S]
      rw [shear_apply_zero, hneq]
      simpa using hj
    obtain ⟨Q, hdet, h0, hrest⟩ := clearHead k (S *ᵥ c) hS0
    let R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ := Q * S
    refine ⟨R, ?_, ?_, ?_⟩
    · dsimp [R]
      rw [Matrix.det_mul, hdet, shear_det]
      simp
    · dsimp [R]
      rw [← Matrix.mulVec_mulVec]
      exact h0
    · intro i hi
      dsimp [R]
      rw [← Matrix.mulVec_mulVec]
      exact hrest i hi

end Submission.ZRowBasis

