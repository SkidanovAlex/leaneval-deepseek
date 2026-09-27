import Mathlib

namespace Work.Cohomology

open Finset

theorem neg_one_pow_self_add {R : Type} [Ring R] (n : ℕ) : (-1:R)^(n+n) = 1 :=
  Even.neg_one_pow ⟨n, by ring⟩

theorem neg_one_pow_succ_add {R : Type} [Ring R] (n : ℕ) : (-1:R)^(n+1+n) = -1 :=
  Odd.neg_one_pow ⟨n, by ring⟩

abbrev od (m : ℕ) (p : Fin (m+3) × Fin (m+2)) : Prop :=
  p.1.val < p.2.val ∨ p.2.val + 2 ≤ p.1.val

def phiFun {m : ℕ} (x : Fin (m+2) × Fin (m+1)) : Fin (m+3) × Fin (m+2) :=
  if x.1.val ≤ x.2.val then (x.1.castSucc, x.2.succ) else (x.1.succ, x.2.castSucc)

def psi {m : ℕ} (p : Fin (m+3) × Fin (m+2)) : Fin (m+2) × Fin (m+1) :=
  if h : p.1.val < p.2.val then
    (⟨p.1.val, by omega⟩, ⟨p.2.val - 1, by omega⟩)
  else if h2 : p.2.val < m+1 then
    (⟨p.1.val - 1, by omega⟩, ⟨p.2.val, by omega⟩)
  else (0, 0)

theorem od_phiFun {m : ℕ} (x : Fin (m+2) × Fin (m+1)) : od m (phiFun x) := by
  obtain ⟨b, a⟩ := x
  simp only [phiFun]
  split_ifs with h
  · left; simp only [Fin.val_castSucc, Fin.val_succ]; omega
  · right; simp only [Fin.val_castSucc, Fin.val_succ]; omega

theorem psi_phiFun {m : ℕ} (x : Fin (m+2) × Fin (m+1)) : psi (phiFun x) = x := by
  obtain ⟨b, a⟩ := x
  by_cases hba : b.val ≤ a.val
  · have hphi : phiFun (b, a) = (b.castSucc, a.succ) := by simp only [phiFun, if_pos hba]
    rw [hphi]
    have hlt : (b.castSucc).val < (a.succ).val := by
      simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [psi, dif_pos hlt]
    apply Prod.ext
    · apply Fin.ext; simp only [Fin.val_castSucc]
    · apply Fin.ext; simp only [Fin.val_succ]; omega
  · have hphi : phiFun (b, a) = (b.succ, a.castSucc) := by simp only [phiFun, if_neg hba]
    rw [hphi]
    have hnlt : ¬ (b.succ).val < (a.castSucc).val := by
      simp only [Fin.val_castSucc, Fin.val_succ]; omega
    rw [psi, dif_neg hnlt]
    have h2 : (a.castSucc).val < m+1 := by rw [Fin.val_castSucc]; exact a.isLt
    rw [dif_pos h2]
    apply Prod.ext
    · apply Fin.ext; simp only [Fin.val_succ]; omega
    · apply Fin.ext; simp only [Fin.val_castSucc]

theorem phiFun_psi {m : ℕ} (p : Fin (m+3) × Fin (m+2)) (h : od m p) : phiFun (psi p) = p := by
  obtain ⟨l, k⟩ := p
  simp only [od] at h
  rcases h with h | h
  · rw [psi, dif_pos h]
    have hble : (⟨l.val, by omega⟩ : Fin (m+2)).val ≤ (⟨k.val - 1, by omega⟩ : Fin (m+1)).val := by
      simp only; omega
    simp only [phiFun, if_pos hble]
    apply Prod.ext
    · apply Fin.ext; simp only [Fin.val_castSucc]
    · apply Fin.ext; simp only [Fin.val_succ]; omega
  · have hnlt : ¬ l.val < k.val := by omega
    rw [psi, dif_neg hnlt]
    have h2 : k.val < m+1 := by omega
    rw [dif_pos h2]
    have hnle : ¬ (⟨l.val-1, by omega⟩ : Fin (m+2)).val ≤ (⟨k.val, by omega⟩ : Fin (m+1)).val := by
      simp only; omega
    simp only [phiFun, if_neg hnle]
    apply Prod.ext
    · apply Fin.ext; simp only [Fin.val_succ]; omega
    · apply Fin.ext; simp only [Fin.val_castSucc]

def dFun {m : ℕ} (x : Fin (m+2) × Fin 2) : Fin (m+3) × Fin (m+2) :=
  if (x.2 : ℕ) = 0 then (x.1.castSucc, x.1) else (x.1.succ, x.1)

def dInv {m : ℕ} (p : Fin (m+3) × Fin (m+2)) : Fin (m+2) × Fin 2 :=
  (p.2, if p.1.val = p.2.val then (0 : Fin 2) else 1)

theorem nod_dFun {m : ℕ} (x : Fin (m+2) × Fin 2) : ¬ od m (dFun x) := by
  obtain ⟨k, e⟩ := x
  simp only [dFun, od]
  split_ifs with h
  · simp only [Fin.val_castSucc]; omega
  · simp only [Fin.val_succ]; omega

theorem dInv_dFun {m : ℕ} (x : Fin (m+2) × Fin 2) : dInv (dFun x) = x := by
  obtain ⟨k, e⟩ := x
  by_cases he : (e : ℕ) = 0
  · have hdf : dFun (k, e) = (k.castSucc, k) := by simp only [dFun, if_pos he]
    rw [hdf]
    have he0 : e = 0 := by apply Fin.ext; simpa using he
    rw [he0]
    simp [dInv, Fin.val_castSucc]
  · have hdf : dFun (k, e) = (k.succ, k) := by simp only [dFun, if_neg he]
    rw [hdf]
    have he1 : e = 1 := by
      apply Fin.ext; simp only [Fin.val_one]; omega
    rw [he1]
    simp [dInv, Fin.val_succ]

theorem dFun_dInv {m : ℕ} (p : Fin (m+3) × Fin (m+2)) (h : ¬ od m p) : dFun (dInv p) = p := by
  obtain ⟨l, k⟩ := p
  simp only [od] at h
  have hl : l.val = k.val ∨ l.val = k.val + 1 := by omega
  rcases hl with hl | hl
  · have hdi : dInv (l, k) = (k, (0 : Fin 2)) := by simp [dInv, hl]
    rw [hdi]
    have hdf : dFun (k, (0 : Fin 2)) = (k.castSucc, k) := by simp [dFun]
    rw [hdf]
    apply Prod.ext
    · apply Fin.ext; simp only [Fin.val_castSucc]; omega
    · rfl
  · have hdi : dInv (l, k) = (k, (1 : Fin 2)) := by simp [dInv, hl]
    rw [hdi]
    have hdf : dFun (k, (1 : Fin 2)) = (k.succ, k) := by simp [dFun]
    rw [hdf]
    apply Prod.ext
    · apply Fin.ext; simp only [Fin.val_succ]; omega
    · rfl

def W {R : Type} [CommRing R] {m : ℕ} (G : Fin (m+3) → Fin (m+2) → R)
    (p : Fin (m+3) × Fin (m+2)) : R := (-1:R)^(p.1.val + p.2.val) * G p.1 p.2

theorem prism_sign1 {R : Type} [CommRing R] (a b : ℕ) (X : R) :
    (-1:R)^b * ((-1:R)^a * X) = - ((-1:R)^(b + (a+1)) * X) := by
  have hh : b + (a+1) = (a+b)+1 := by ring
  rw [hh, pow_succ, pow_add]; ring

theorem prism_sign2 {R : Type} [CommRing R] (a b : ℕ) (X : R) :
    (-1:R)^b * ((-1:R)^a * X) = - ((-1:R)^((b+1) + a) * X) := by
  have hh : (b+1) + a = (a+b)+1 := by ring
  rw [hh, pow_succ, pow_add]; ring

theorem W_dFun_zero {R : Type} [CommRing R] {m : ℕ} (G : Fin (m+3) → Fin (m+2) → R) (k : Fin (m+2)) :
    (-1:R)^(k.val + k.val) * G k.castSucc k = G k.castSucc k := by
  rw [neg_one_pow_self_add, one_mul]

theorem W_dFun_one {R : Type} [CommRing R] {m : ℕ} (G : Fin (m+3) → Fin (m+2) → R) (k : Fin (m+2)) :
    (-1:R)^((k.val + 1) + k.val) * G k.succ k = - G k.succ k := by
  rw [neg_one_pow_succ_add]; ring

/-- **Combinatorial prism identity for a simplicial homotopy.**

For `A` and `G` as below (in the intended application `A a b = u (h_a (∂_b τ))` and
`G l k = u (∂_l (h_k τ))` for the components `h_i : S_n → T_{n+1}` of a simplicial homotopy,
`u` a cochain on `T` of degree `m+1` and `τ` an `(m+1)`-simplex of `S`), the alternating double
sum over the "off-diagonal" pairs reduces, using the cocycle condition `hc`, to the telescoping
sum on the diagonal.

Proof strategy.  Let `Φ : Fin (m+1) × Fin (m+2) → Fin (m+3) × Fin (m+2)` be
`Φ (a,b) = if b.val ≤ a.val then (b.castSucc, a.succ) else (b.succ, a.castSucc)`.
Then `Φ` is a bijection from `Fin (m+1) × Fin (m+2)` onto the off-diagonal set
`{p | p.1.val < p.2.val ∨ p.2.val + 2 ≤ p.1.val}`, and for `p = Φ (a,b)` one has
`(-1)^a * (-1)^b * A a b = -((-1)^{p.1.val} * (-1)^{p.2.val} * G p.1 p.2)`.
So the left side is `- (alternating sum of G over the off-diagonal pairs)`.  Since the alternating
sum of `G` over *all* pairs vanishes by `hc`, this equals the alternating sum over the complementary
(diagonal) pairs `{p | p.1.val = p.2.val ∨ p.1.val = p.2.val + 1}`, whose elements are
`(k.castSucc, k)` and `(k.succ, k)` for `k : Fin (m+2)`, giving exactly the right hand side. -/
lemma prism_sum {R : Type} [CommRing R] {m : ℕ}
    (A : Fin (m+1) → Fin (m+2) → R) (G : Fin (m+3) → Fin (m+2) → R)
    (h1 : ∀ a b, b.val ≤ a.val → A a b = G b.castSucc a.succ)
    (h2 : ∀ a b, a.val < b.val → A a b = G b.succ a.castSucc)
    (hc : ∀ k : Fin (m+2), ∑ l : Fin (m+3), (-1 : R) ^ (l : ℕ) * G l k = 0) :
    ∑ b : Fin (m+2), ∑ a : Fin (m+1), (-1 : R) ^ (b : ℕ) * ((-1 : R) ^ (a : ℕ) * A a b)
      = ∑ k : Fin (m+2), (G k.castSucc k - G k.succ k) := by
  set OS := ∑ p : Fin (m+3) × Fin (m+2), (if od m p then W G p else 0) with hOS
  set DS := ∑ p : Fin (m+3) × Fin (m+2), (if od m p then 0 else W G p) with hDS
  have ht : ∑ p : Fin (m+3) × Fin (m+2), W G p = 0 := by
    rw [Fintype.sum_prod_type]
    have hterm : ∀ (l : Fin (m+3)) (k : Fin (m+2)),
        W G (l,k) = (-1:R)^(k.val) * ((-1:R)^(l.val) * G l k) := by
      intro l k; simp only [W]; rw [pow_add]; ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro k _
    rw [← Finset.mul_sum, hc k, mul_zero]
  have hsplit : (∑ p : Fin (m+3) × Fin (m+2), W G p) = OS + DS := by
    rw [hOS, hDS, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : od m p <;> simp [hp]
  have hoff_eq : OS = -DS := by
    rw [eq_neg_iff_add_eq_zero, ← hsplit, ht]
  have hLHS : (∑ b : Fin (m+2), ∑ a : Fin (m+1), (-1:R)^(b:ℕ) * ((-1:R)^(a:ℕ) * A a b)) = -OS := by
    rw [← Fintype.sum_prod_type (fun x : Fin (m+2) × Fin (m+1) => (-1:R)^(x.1.val) * ((-1:R)^(x.2.val) * A x.2 x.1))]
    have hbij : (∑ x : Fin (m+2) × Fin (m+1), (-1:R)^(x.1.val) * ((-1:R)^(x.2.val) * A x.2 x.1))
        = ∑ p ∈ (Finset.univ.filter (od m)), (-(W G p)) := by
      apply Finset.sum_bij (fun x _ => phiFun x)
      · intro x _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact od_phiFun x
      · intro x1 _ x2 _ hx; rw [← psi_phiFun x1, hx, psi_phiFun x2]
      · intro p hp; rw [Finset.mem_filter] at hp
        exact ⟨psi p, Finset.mem_univ _, phiFun_psi p hp.2⟩
      · intro x _
        obtain ⟨b, a⟩ := x
        by_cases hba : b.val ≤ a.val
        · have hphi : phiFun (b, a) = (b.castSucc, a.succ) := by simp only [phiFun, if_pos hba]
          rw [hphi, h1 a b hba]
          simp only [W, Fin.val_castSucc, Fin.val_succ]
          exact prism_sign1 a.val b.val (G b.castSucc a.succ)
        · have hphi : phiFun (b, a) = (b.succ, a.castSucc) := by simp only [phiFun, if_neg hba]
          rw [hphi]
          have hab : a.val < b.val := by omega
          rw [h2 a b hab]
          simp only [W, Fin.val_castSucc, Fin.val_succ]
          exact prism_sign2 a.val b.val (G b.succ a.castSucc)
    rw [hbij, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_filter]
  have hdiag : DS = ∑ k : Fin (m+2), (G k.castSucc k - G k.succ k) := by
    have hf : (∑ p : Fin (m+3) × Fin (m+2), (if od m p then 0 else W G p))
        = ∑ p ∈ (Finset.univ.filter (fun p => ¬ od m p)), W G p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : od m p <;> simp [hp]
    rw [hDS, hf]
    have hbij2 : (∑ x : Fin (m+2) × Fin 2,
        (if (x.2:ℕ) = 0 then G x.1.castSucc x.1 else - G x.1.succ x.1))
        = ∑ p ∈ (Finset.univ.filter (fun p => ¬ od m p)), W G p := by
      apply Finset.sum_bij (fun x _ => dFun x)
      · intro x _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact nod_dFun x
      · intro x1 _ x2 _ hx; rw [← dInv_dFun x1, hx, dInv_dFun x2]
      · intro p hp; rw [Finset.mem_filter] at hp
        exact ⟨dInv p, Finset.mem_univ _, dFun_dInv p hp.2⟩
      · intro x _
        obtain ⟨k, e⟩ := x
        by_cases he : (e:ℕ) = 0
        · have hdf : dFun (k,e) = (k.castSucc, k) := by simp only [dFun, if_pos he]
          have he0 : e = 0 := by apply Fin.ext; simpa using he
          subst he0
          rw [hdf]
          simp only [W, Fin.val_castSucc, Fin.val_zero, if_true]
          exact (W_dFun_zero G k).symm
        · have hdf : dFun (k,e) = (k.succ, k) := by simp only [dFun, if_neg he]
          have he1 : e = 1 := by apply Fin.ext; simp only [Fin.val_one]; omega
          subst he1
          rw [hdf]
          simp only [W, Fin.val_succ, Fin.val_one, if_neg (by norm_num : (1:ℕ) ≠ 0)]
          exact (W_dFun_one G k).symm
    rw [← hbij2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, if_true, Fin.val_one, if_neg (by norm_num : (1:ℕ) ≠ 0)]
    ring
  rw [hLHS]
  rw [hoff_eq]
  rw [neg_neg]
  rw [hdiag]

end Work.Cohomology
