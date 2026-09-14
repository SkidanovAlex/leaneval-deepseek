import Mathlib
open Matrix

namespace Commons.Data.Matrix

namespace rc_aux

def gval (A B : ℤ) : ℤ := (A.gcd B : ℤ)
def qA (A B : ℤ) : ℤ := A / gval A B
def qB (A B : ℤ) : ℤ := B / gval A B
def cA (A B : ℤ) : ℤ := (qA A B).gcdA (qB A B)
def cB (A B : ℤ) : ℤ := (qA A B).gcdB (qB A B)

def pairM {d : ℕ} (i j : Fin d) (A B : ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  fun r c =>
    if r = i then
      if c = i then cA A B
      else if c = j then cB A B else 0
    else if r = j then
      if c = i then -qB A B
      else if c = j then qA A B else 0
    else if c = r then 1 else 0

def pairInv {d : ℕ} (i j : Fin d) (A B : ℤ) : Matrix (Fin d) (Fin d) ℤ :=
  fun r c =>
    if r = i then
      if c = i then qA A B
      else if c = j then -cB A B else 0
    else if r = j then
      if c = i then qB A B
      else if c = j then cA A B else 0
    else if c = r then 1 else 0

lemma gcd_pos_of_ne_both_zero (A B : ℤ) (h : A ≠ 0 ∨ B ≠ 0) : 0 < A.gcd B := by
  rcases h with hA | hB
  · exact Int.gcd_pos_of_ne_zero_left B hA
  · exact Int.gcd_pos_of_ne_zero_right A hB

lemma qA_gcd_qB (A B : ℤ) (h : 0 < A.gcd B) : (qA A B).gcd (qB A B) = 1 := by
  dsimp [qA, qB, gval]
  exact Int.gcd_ediv_gcd_ediv_gcd h

lemma bezout_qA_qB (A B : ℤ) (h : 0 < A.gcd B) : qA A B * cA A B + qB A B * cB A B = 1 := by
  have hq : (qA A B).gcd (qB A B) = 1 := qA_gcd_qB A B h
  have hb := Int.gcd_eq_gcd_ab (qA A B) (qB A B)
  rw [hq] at hb
  norm_num at hb
  simpa [cA, cB] using hb.symm

lemma bezout_comm (A B : ℤ) (h : 0 < A.gcd B) : cA A B * qA A B + cB A B * qB A B = 1 := by
  have hb := bezout_qA_qB A B h
  nlinarith

lemma pairM_mulVec_of_ne {d : ℕ} (i j r : Fin d) (hri : r ≠ i) (hrj : r ≠ j)
    (v : Fin d → ℤ) (A B : ℤ) :
    (pairM i j A B).mulVec v r = v r := by
  classical
  change (∑ c : Fin d, pairM i j A B r c * v c) = v r
  simp [pairM, hri, hrj]

lemma pairM_mulVec_i {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (v : Fin d → ℤ) (A B : ℤ) :
    (pairM i j A B).mulVec v i = cA A B * v i + cB A B * v j := by
  classical
  change (∑ c : Fin d, pairM i j A B i c * v c) = cA A B * v i + cB A B * v j
  simp [pairM]
  have hsplit : ∀ c : Fin d, (if c = i then cA A B * v c else if c = j then cB A B * v c else 0)
      = (if c = i then cA A B * v c else 0) + (if c = j then cB A B * v c else 0) := by
    intro c
    by_cases hci : c = i
    · subst c; simp [hij]
    · by_cases hcj : c = j
      · subst c; simp [hci]
      · simp [hci, hcj]
  rw [show (∑ c, (if c = i then cA A B * v c else if c = j then cB A B * v c else 0))
        = (∑ c, ((if c = i then cA A B * v c else 0) + (if c = j then cB A B * v c else 0))) by
          apply Finset.sum_congr rfl; intro c hc; exact hsplit c]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

lemma pairM_mulVec_j {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (v : Fin d → ℤ) (A B : ℤ) :
    (pairM i j A B).mulVec v j = -(qB A B * v i) + qA A B * v j := by
  classical
  change (∑ c : Fin d, pairM i j A B j c * v c) = -(qB A B * v i) + qA A B * v j
  simp [pairM, hij.symm]
  have hsplit : ∀ c : Fin d, (if c = i then -(qB A B * v c) else if c = j then qA A B * v c else 0)
      = (if c = i then -(qB A B * v c) else 0) + (if c = j then qA A B * v c else 0) := by
    intro c
    by_cases hci : c = i
    · subst c; simp [hij]
    · by_cases hcj : c = j
      · subst c; simp [hci]
      · simp [hci, hcj]
  rw [show (∑ c, (if c = i then -(qB A B * v c) else if c = j then qA A B * v c else 0))
        = (∑ c, ((if c = i then -(qB A B * v c) else 0) + (if c = j then qA A B * v c else 0))) by
          apply Finset.sum_congr rfl; intro c hc; exact hsplit c]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

lemma pairM_mul_pairInv {d : ℕ} (i j : Fin d) (hij : i ≠ j) (A B : ℤ) (h : A ≠ 0 ∨ B ≠ 0) :
    pairM i j A B * pairInv i j A B = 1 := by
  classical
  ext r c
  change (pairM i j A B).mulVec (fun k : Fin d => pairInv i j A B k c) r
    = (1 : Matrix (Fin d) (Fin d) ℤ) r c
  rw [Matrix.one_apply]
  by_cases hri : r = i
  · subst r
    rw [pairM_mulVec_i i j hij (fun k => pairInv i j A B k c) A B]
    by_cases hci : c = i
    · subst c
      simp [pairInv, hij.symm]
      rw [bezout_comm A B (gcd_pos_of_ne_both_zero A B h)]
    · by_cases hcj : c = j
      · subst c
        simp [pairInv, hij, hij.symm]
        ring
      · have hic : i ≠ c := fun hc => hci hc.symm
        simp [pairInv, hci, hcj, hic, hij.symm]
  · by_cases hrj : r = j
    · subst r
      rw [pairM_mulVec_j i j hij (fun k => pairInv i j A B k c) A B]
      by_cases hci : c = i
      · subst c
        simp [pairInv, hij.symm]
        ring
      · by_cases hcj : c = j
        · subst c
          simp [pairInv, hij.symm]
          nlinarith [bezout_qA_qB A B (gcd_pos_of_ne_both_zero A B h)]
        · have hjc : j ≠ c := fun hc => hcj hc.symm
          simp [pairInv, hci, hcj, hjc, hij.symm]
    · rw [pairM_mulVec_of_ne i j r hri hrj (fun k => pairInv i j A B k c) A B]
      by_cases hcr : c = r
      · subst c
        simp [pairInv, hri, hrj]
      · have hrc : r ≠ c := fun hc => hcr hc.symm
        simp [pairInv, hri, hrj, hrc, hcr]

lemma pairM_det_unit {d : ℕ} (i j : Fin d) (hij : i ≠ j) (A B : ℤ) (h : A ≠ 0 ∨ B ≠ 0) :
    IsUnit (pairM i j A B).det := by
  have hprod : pairM i j A B * pairInv i j A B = 1 := pairM_mul_pairInv i j hij A B h
  have hdet : (pairM i j A B).det * (pairInv i j A B).det = 1 := by
    rw [← Matrix.det_mul, hprod, Matrix.det_one]
  exact ⟨⟨(pairM i j A B).det, (pairInv i j A B).det, hdet, by rw [mul_comm, hdet]⟩, rfl⟩

-- generic arithmetic helpers
lemma pairArith_i (A B m n x y g : ℤ) (hm : m * g = A) (hn : n * g = B) (hx : x * m + y * n = 1) :
    x * A + y * B = g := by
  calc
    x * A + y * B = x * (m * g) + y * (n * g) := by rw [← hm, ← hn]
    _ = (x * m + y * n) * g := by ring
    _ = 1 * g := by rw [hx]
    _ = g := by ring

lemma pairArith_j (A B m n g : ℤ) (hm : m * g = A) (hn : n * g = B) :
    -(n * A) + m * B = 0 := by
  calc
    -(n * A) + m * B = -(n * (m * g)) + m * (n * g) := by rw [← hm, ← hn]
    _ = 0 := by ring

lemma qA_mul_gval (A B : ℤ) : qA A B * gval A B = A := by
  dsimp [qA, gval]
  exact Int.ediv_mul_cancel (Int.gcd_dvd_left A B)

lemma qB_mul_gval (A B : ℤ) : qB A B * gval A B = B := by
  dsimp [qB, gval]
  exact Int.ediv_mul_cancel (Int.gcd_dvd_right A B)

lemma pairM_i_eq_gval {d : ℕ} (i j : Fin d) (hij : i ≠ j) (v : Fin d → ℤ)
    (h : v i ≠ 0 ∨ v j ≠ 0) :
    (pairM i j (v i) (v j)).mulVec v i = gval (v i) (v j) := by
  classical
  have hpos : 0 < (v i).gcd (v j) := gcd_pos_of_ne_both_zero (v i) (v j) h
  rw [pairM_mulVec_i i j hij v (v i) (v j)]
  exact pairArith_i (v i) (v j) (qA (v i) (v j)) (qB (v i) (v j))
    (cA (v i) (v j)) (cB (v i) (v j)) (gval (v i) (v j))
    (qA_mul_gval (v i) (v j)) (qB_mul_gval (v i) (v j)) (bezout_comm (v i) (v j) hpos)

lemma pairM_j_eq_zero {d : ℕ} (i j : Fin d) (hij : i ≠ j) (v : Fin d → ℤ) :
    (pairM i j (v i) (v j)).mulVec v j = 0 := by
  classical
  rw [pairM_mulVec_j i j hij v (v i) (v j)]
  exact pairArith_j (v i) (v j) (qA (v i) (v j)) (qB (v i) (v j)) (gval (v i) (v j))
    (qA_mul_gval (v i) (v j)) (qB_mul_gval (v i) (v j))

lemma pairM_g_ne_zero {d : ℕ} (i j : Fin d) (v : Fin d → ℤ)
    (h : v i ≠ 0 ∨ v j ≠ 0) : gval (v i) (v j) ≠ 0 := by
  have hpos : 0 < (v i).gcd (v j) := gcd_pos_of_ne_both_zero (v i) (v j) h
  dsimp [gval]
  exact_mod_cast (ne_of_gt hpos)

lemma pair_zero {d : ℕ} (i j : Fin d) (hij : i ≠ j) (v : Fin d → ℤ) (h : v i ≠ 0 ∨ v j ≠ 0) :
    ∃ (E : Matrix (Fin d) (Fin d) ℤ) (g : ℤ),
      IsUnit E.det ∧ g ≠ 0 ∧ (E.mulVec v) i = g ∧ (E.mulVec v) j = 0 ∧
      ∀ k : Fin d, k ≠ i → k ≠ j → (E.mulVec v) k = v k := by
  refine ⟨pairM i j (v i) (v j), gval (v i) (v j),
    pairM_det_unit i j hij (v i) (v j) h, pairM_g_ne_zero i j v h,
    pairM_i_eq_gval i j hij v h, pairM_j_eq_zero i j hij v, ?_⟩
  intro k hki hkj
  exact pairM_mulVec_of_ne i j k hki hkj v (v i) (v j)

-- product of units helper
lemma isUnit_mul_int {a b : ℤ} (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a * b) := by
  rcases ha with ⟨u, rfl⟩
  rcases hb with ⟨v, rfl⟩
  exact ⟨u * v, by simp⟩

/-- Sequential zeroing: process each coordinate in the list (assumed ≠ a), zeroing it into `a`. -/
def reduceProc {d : ℕ} (a : Fin d) : List (Fin d) → (Fin d → ℤ) → Matrix (Fin d) (Fin d) ℤ →
    (Fin d → ℤ) × Matrix (Fin d) (Fin d) ℤ
  | [], w, U => (w, U)
  | x :: xs, w, U =>
      let E := pairM a x (w a) (w x)
      reduceProc a xs (E.mulVec w) (E * U)

lemma reduceProc_correct {d : ℕ} (a : Fin d) (v : Fin d → ℤ) :
  ∀ (l : List (Fin d)), (∀ x ∈ l, x ≠ a) →
  ∀ (U : Matrix (Fin d) (Fin d) ℤ) (w : Fin d → ℤ),
    w = U.mulVec v → IsUnit U.det → w a ≠ 0 →
    let r := reduceProc a l w U
    r.1 = r.2.mulVec v ∧ IsUnit r.2.det ∧ r.1 a ≠ 0 ∧
      (∀ y ∈ l, r.1 y = 0) ∧ (∀ y, y ≠ a → y ∉ l → r.1 y = w y) := by
  classical
  intro l
  induction l with
  | nil =>
      intro hl U w hw hU hwa
      simp [reduceProc]
      exact ⟨hw, hU, hwa⟩
  | cons x xs ih =>
      intro hl U w hw hU hwa
      let E := pairM a x (w a) (w x)
      have hxa : x ≠ a := hl x (by simp)
      have hax : a ≠ x := fun h => hxa h.symm
      have hcond : w a ≠ 0 ∨ w x ≠ 0 := Or.inl hwa
      have hEunit : IsUnit E.det := pairM_det_unit a x hax (w a) (w x) hcond
      have hw1a : (E.mulVec w) a ≠ 0 := by
        have hg : gval (w a) (w x) ≠ 0 := pairM_g_ne_zero a x w hcond
        rw [pairM_i_eq_gval a x hax w hcond]
        exact hg
      have hw1x : (E.mulVec w) x = 0 := pairM_j_eq_zero a x hax w
      have hw1 : (E.mulVec w) = (E * U).mulVec v := by
        calc
          E.mulVec w = E.mulVec (U.mulVec v) := by rw [hw]
          _ = (E * U).mulVec v := by rw [Matrix.mulVec_mulVec]
      have hE1 : IsUnit (E * U).det := by
        rw [Matrix.det_mul]
        exact isUnit_mul_int hEunit hU
      have hlxs : ∀ x ∈ xs, x ≠ a := by
        intro y hy
        exact hl y (by simp [hy])
      have ih' := ih hlxs (E * U) (E.mulVec w) hw1 hE1 hw1a
      change
        (reduceProc a xs (E.mulVec w) (E * U)).1 = (reduceProc a xs (E.mulVec w) (E * U)).2.mulVec v ∧
        IsUnit (reduceProc a xs (E.mulVec w) (E * U)).2.det ∧
        (reduceProc a xs (E.mulVec w) (E * U)).1 a ≠ 0 ∧
        (∀ y ∈ x :: xs, (reduceProc a xs (E.mulVec w) (E * U)).1 y = 0) ∧
        (∀ y, y ≠ a → y ∉ x :: xs → (reduceProc a xs (E.mulVec w) (E * U)).1 y = w y)
      rcases ih' with ⟨h11, h12, h13, h14, h15⟩
      refine ⟨h11, h12, h13, ?_, ?_⟩
      · intro y hy
        rw [List.mem_cons] at hy
        rcases hy with h_eq | hyx
        · subst y
          by_cases hxxs : x ∈ xs
          · exact h14 x hxxs
          · have hun := h15 x hxa hxxs
            rw [hun, hw1x]
        · exact h14 y hyx
      · intro y hya hyout
        have hyxs : y ∉ xs := by intro hyi; exact hyout (by simp [hyi])
        have hyx : y ≠ x := by intro hyx; exact hyout (by simp [hyx])
        have hun := h15 y hya hyxs
        rw [hun]
        exact pairM_mulVec_of_ne a x y hya hyx w (w a) (w x)

end rc_aux

open rc_aux

theorem reduce_col_to_single_nonzero {d : ℕ} [NeZero d] (v : Fin d → ℤ)
    (hv : ∃ i : Fin d, v i ≠ 0) :
    ∃ (U : Matrix (Fin d) (Fin d) ℤ) (g : ℤ),
      IsUnit U.det ∧ g ≠ 0 ∧ (U.mulVec v) 0 = g ∧
      ∀ i : Fin d, i ≠ 0 → (U.mulVec v) i = 0 := by
  classical
  rcases hv with ⟨a, hva⟩
  let l : List (Fin d) := (Finset.univ.erase a).toList
  have mem_l : ∀ x : Fin d, x ∈ l ↔ x ≠ a := by
    intro x
    change x ∈ (Finset.univ.erase a).toList ↔ x ≠ a
    rw [Finset.mem_toList]
    rw [Finset.mem_erase]
    simp
  have hl : ∀ x ∈ l, x ≠ a := by
    intro x hx
    exact (mem_l x).1 hx
  have hw0 : v = (1 : Matrix (Fin d) (Fin d) ℤ).mulVec v := (Matrix.one_mulVec v).symm
  have hU0 : IsUnit (1 : Matrix (Fin d) (Fin d) ℤ).det := by simp
  rcases reduceProc_correct a v l hl (1 : Matrix (Fin d) (Fin d) ℤ) v hw0 hU0 hva
    with ⟨hw, hU1, hwa, hz, hun⟩
  let w1 : Fin d → ℤ := (reduceProc a l v 1).1
  let U1 : Matrix (Fin d) (Fin d) ℤ := (reduceProc a l v 1).2
  change w1 = U1.mulVec v at hw
  change IsUnit U1.det at hU1
  change w1 a ≠ 0 at hwa
  change (∀ y ∈ l, w1 y = 0) at hz
  change (∀ y, y ≠ a → y ∉ l → w1 y = v y) at hun
  by_cases ha0 : a = 0
  · subst a
    refine ⟨U1, (U1.mulVec v) 0, hU1, ?gne, ?eq, ?z⟩
    · rw [← hw]
      exact hwa
    · rfl
    · intro i hi0
      rw [← hw]
      exact hz i ((mem_l i).2 hi0)
  · have h0a : (0 : Fin d) ≠ a := fun h => ha0 h.symm
    rcases pair_zero 0 a h0a w1 (Or.inr hwa) with ⟨E2, g2, hE2unit, hg2ne, hE20, hE2a, hE2other⟩
    have hU2v : ((E2 * U1).mulVec v) = E2.mulVec w1 := by
      calc
        (E2 * U1).mulVec v = E2.mulVec (U1.mulVec v) := by rw [← Matrix.mulVec_mulVec]
        _ = E2.mulVec w1 := by rw [← hw]
    refine ⟨E2 * U1, (E2 * U1).mulVec v 0, ?unit2, ?gne2, rfl, ?z2⟩
    · rw [Matrix.det_mul]
      exact isUnit_mul_int hE2unit hU1
    · rw [hU2v, hE20]
      exact hg2ne
    · intro i hi0
      rw [hU2v]
      by_cases hia : i = a
      · subst i
        exact hE2a
      · have hw1i : w1 i = 0 := hz i ((mem_l i).2 hia)
        rw [hE2other i hi0 hia, hw1i]
