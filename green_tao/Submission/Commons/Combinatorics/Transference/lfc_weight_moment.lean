import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_data
import Submission.Commons.NumberTheory.Sieve.qmod_rat_div
import Submission.Commons.NumberTheory.Sieve.isSmallRat_rat_div
import Submission.Commons.Combinatorics.Finset.card_sigma_bool_false

set_option autoImplicit false

namespace Commons.Combinatorics.Transference

open _root_.Finset
open scoped BigOperators
open Commons.NumberTheory.Sieve

/-!
# The weighted cube moment from the linear forms condition
-/

/-- Coordinate type for the variables `(h_0,…,h_{d-1}, x, s, s')`. -/
abbrev Ix (d : ℕ) := Fin d ⊕ Fin 3

open Commons.Combinatorics.Finset in
private lemma zmod_natCast_eq_zero_iff (p n : ℕ) : (n : ZMod p) = 0 ↔ p ∣ n := by
  rw [← Int.natCast_dvd_natCast (m := p) (n := n),
    ← Int.cast_natCast (R := ZMod p)]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd (n : ℤ) p

/-- The equivalence `(Fin d ⊕ Fin 3 → α) ≃ (Fin d → α) × α × α × α`. -/
def ixEquiv (α : Type*) (d : ℕ) :
    ((Fin d ⊕ Fin 3) → α) ≃ ((Fin d → α) × α × α × α) where
  toFun v := (fun j => v (Sum.inl j), v (Sum.inr 0), v (Sum.inr 1), v (Sum.inr 2))
  invFun q := Sum.elim q.1 ![q.2.1, q.2.2.1, q.2.2.2]
  left_inv v := by
    funext k
    rcases k with j | k
    · rfl
    · fin_cases k <;> rfl
  right_inv q := by
    rcases q with ⟨f, a, b, c⟩
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl rfl))

/-- Reindex a function on `Fin d ⊕ Fin 3` as a tuple `(h, x, s, s')`. -/
theorem sum_fun_sum_equiv {p d : ℕ} [Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (F : (Ix d → ZMod p) → M) :
    (∑ v : Ix d → ZMod p, F v)
      = ∑ h : Fin d → ZMod p, ∑ x : ZMod p, ∑ s : ZMod p, ∑ s' : ZMod p,
          F (Sum.elim h ![x, s, s']) := by
  rw [← Equiv.sum_comp (ixEquiv (ZMod p) d).symm F]
  simp only [Fintype.sum_prod_type, ixEquiv, Equiv.coe_fn_symm_mk]

/-- The linear forms condition with the linear forms written on an arbitrary coordinate type
`V ≃ Fin t` (the linear forms having rational coefficients, small in the sense of
`IsSmallRat`). -/
theorem lfc_apply_equiv {p : ℕ} [Fact p.Prime] {ν : ZMod p → ℝ} {m₀ t₀ L₀ : ℕ} {ε : ℝ}
    (hLFC : LinFormsCond p ν m₀ t₀ L₀ ε)
    {t : ℕ} (ht1 : 1 ≤ t) (ht2 : t ≤ t₀)
    {V : Type} [Fintype V] [DecidableEq V] (e : V ≃ Fin t)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι1 : 1 ≤ Fintype.card ι) (hι2 : Fintype.card ι ≤ m₀)
    (L : ι → V → ℚ) (hLs : ∀ i j, IsSmallRat L₀ (L i j))
    (hne : ∀ i, ∃ j, L i j ≠ 0)
    (hnp : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, L i' j = lam * L i j)
    (b : ι → ZMod p) :
    |((Fintype.card (V → ZMod p) : ℝ))⁻¹ *
      (∑ v : V → ZMod p, ∏ i, ν ((∑ j, qmod p (L i j) * v j) + b i)) - 1| ≤ ε := by
  set L' : ι → Fin t → ℚ := fun i k => L i (e.symm k) with hL'def
  have hLs' : ∀ i k, IsSmallRat L₀ (L' i k) := fun i k => hLs i _
  have hne' : ∀ i, NonzeroTuple (L' i) := by
    intro i
    obtain ⟨j, hj⟩ := hne i
    exact ⟨e j, by simpa [hL'def] using hj⟩
  have hnp' : ∀ i i', i ≠ i' → NotProp (L' i) (L' i') := by
    rintro i i' hii ⟨lam, hlam⟩
    exact hnp i i' hii ⟨lam, fun j => by
      have := hlam (e j)
      simpa [hL'def] using this⟩
  have h := hLFC ι hι1 hι2 t ht1 ht2 L' hLs' hne' hnp' b
  set Φ : (V → ZMod p) ≃ (Fin t → ZMod p) := e.arrowCongr (Equiv.refl (ZMod p)) with hΦ
  have hΦapply : ∀ (v : V → ZMod p) (k : Fin t), Φ v k = v (e.symm k) := by
    intro v k
    simp [hΦ, Equiv.arrowCongr_apply]
  have hsum : (∑ x : Fin t → ZMod p, ∏ i, ν (linForm p (L' i) (b i) x))
      = ∑ v : V → ZMod p, ∏ i, ν ((∑ j, qmod p (L i j) * v j) + b i) := by
    rw [← Equiv.sum_comp Φ (fun x : Fin t → ZMod p => ∏ i, ν (linForm p (L' i) (b i) x))]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.prod_congr rfl
    intro i _
    have h1 : (∑ k : Fin t, qmod p (L' i k) * Φ v k) = ∑ j : V, qmod p (L i j) * v j := by
      rw [← Equiv.sum_comp e (fun k : Fin t => qmod p (L' i k) * Φ v k)]
      apply Finset.sum_congr rfl
      intro j _
      simp [hL'def, hΦapply]
    rw [linForm, h1]
  have hcard : (Fintype.card (Fin t → ZMod p) : ℝ) = (Fintype.card (V → ZMod p) : ℝ) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_congr e]
  rw [hcard, hsum] at h
  exact h

/-- The rational coefficient of `h_j` in the form `φ_i`, chosen so that its `qmod` is
`1 - (i+1)/(j+1)` in `ZMod p`. -/
noncomputable def phiC (p i j : ℕ) : ℚ :=
  if p ∣ (j + 1) then 1 else (((j : ℚ) - (i : ℚ)) / ((j + 1 : ℕ) : ℚ))

lemma qmod_sub_div_nat {p : ℕ} [Fact p.Prime] (j i n : ℕ) (hn : n ≠ 0) (hp : ¬ p ∣ n) :
    qmod p (((j : ℚ) - (i : ℚ)) / ((n : ℕ) : ℚ))
      = ((j : ZMod p) - (i : ZMod p)) / ((n : ℕ) : ZMod p) := by
  have h := qmod_rat_div (p := p) ((j : ℤ) - (i : ℤ)) n hn hp
  simpa only [Int.cast_sub, Int.cast_natCast] using h

lemma phiC_qmod {p : ℕ} [Fact p.Prime] (i j : ℕ) :
    qmod p (phiC p i j)
      = 1 - (((i + 1 : ℕ)) : ZMod p) * ((((j + 1 : ℕ)) : ZMod p))⁻¹ := by
  by_cases hp : p ∣ (j + 1)
  · rw [phiC, if_pos hp, qmod_one]
    have hz : (((j + 1 : ℕ)) : ZMod p) = 0 := (zmod_natCast_eq_zero_iff p (j + 1)).mpr hp
    rw [hz, inv_zero, mul_zero, sub_zero]
  · have hq : phiC p i j = ((j : ℚ) - (i : ℚ)) / (((j + 1 : ℕ)) : ℚ) := by
      rw [phiC, if_neg hp]
    rw [hq, qmod_sub_div_nat (p := p) j i (j + 1) (by omega) hp]
    have hz : (((j + 1 : ℕ)) : ZMod p) ≠ 0 := by
      intro h; exact hp ((zmod_natCast_eq_zero_iff p (j + 1)).mp h)
    have hj : ((j : ZMod p)) = (((j + 1 : ℕ)) : ZMod p) - 1 := by push_cast; ring
    rw [hj]
    have hcast : (((j + 1 : ℕ)) : ZMod p) - 1 - ((i : ℕ) : ZMod p)
        = (((j + 1 : ℕ)) : ZMod p) - (((i + 1 : ℕ)) : ZMod p) := by push_cast; ring
    rw [hcast, sub_div, div_self hz, div_eq_mul_inv]

/-- The cube form `x + ω·h` in `(h,x,s,s')` coordinates. -/
noncomputable def cubeCoeff (d : ℕ) (ω : Fin d → Bool) : Ix d → ℚ :=
  Sum.elim (fun j => if ω j then 1 else 0) ![1, 0, 0]

lemma cubeCoeff_inl (d : ℕ) (ω : Fin d → Bool) (j : Fin d) :
    cubeCoeff d ω (Sum.inl j) = if ω j then 1 else 0 := rfl

lemma cubeCoeff_inr0 (d : ℕ) (ω : Fin d → Bool) : cubeCoeff d ω (Sum.inr 0) = 1 := rfl
lemma cubeCoeff_inr1 (d : ℕ) (ω : Fin d → Bool) : cubeCoeff d ω (Sum.inr 1) = 0 := rfl
lemma cubeCoeff_inr2 (d : ℕ) (ω : Fin d → Bool) : cubeCoeff d ω (Sum.inr 2) = 0 := rfl

/-- The form `φ_i(x+ω·h,s)`. -/
noncomputable def phiCoeff (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) : Ix d → ℚ :=
  Sum.elim (fun j => if ω j then phiC p i.val j.val else 0)
    ![1, -((((i.val + 1 : ℕ)) : ℚ)), 0]

/-- The form `φ_i(x+ω·h,s')`. -/
noncomputable def phiCoeff' (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) : Ix d → ℚ :=
  Sum.elim (fun j => if ω j then phiC p i.val j.val else 0)
    ![1, 0, -((((i.val + 1 : ℕ)) : ℚ))]

lemma phiCoeff_inl (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) (j : Fin d) :
    phiCoeff p d i ω (Sum.inl j) = if ω j then phiC p i.val j.val else 0 := rfl
lemma phiCoeff_inr0 (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff p d i ω (Sum.inr 0) = 1 := rfl
lemma phiCoeff_inr1 (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff p d i ω (Sum.inr 1) = -((((i.val + 1 : ℕ)) : ℚ)) := rfl
lemma phiCoeff_inr2 (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff p d i ω (Sum.inr 2) = 0 := rfl

lemma phiCoeff'_inl (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) (j : Fin d) :
    phiCoeff' p d i ω (Sum.inl j) = if ω j then phiC p i.val j.val else 0 := rfl
lemma phiCoeff'_inr0 (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff' p d i ω (Sum.inr 0) = 1 := rfl
lemma phiCoeff'_inr1 (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff' p d i ω (Sum.inr 1) = 0 := rfl
lemma phiCoeff'_inr2 (p d : ℕ) (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff' p d i ω (Sum.inr 2) = -((((i.val + 1 : ℕ)) : ℚ)) := rfl

lemma qmod_neg {p : ℕ} [Fact p.Prime] (q : ℚ) : qmod p (-q) = -qmod p q := by
  rw [qmod, qmod, Rat.neg_num, Rat.neg_den]
  push_cast
  rw [neg_div]

lemma qmod_intCast {p : ℕ} [Fact p.Prime] (n : ℤ) : qmod p ((n : ℤ) : ℚ) = (n : ZMod p) := by
  rw [qmod, Rat.num_intCast, Rat.den_intCast]
  simp

lemma qmod_natCast {p : ℕ} [Fact p.Prime] (n : ℕ) :
    qmod p ((n : ℕ) : ℚ) = ((n : ℕ) : ZMod p) := by
  have h : ((n : ℕ) : ℚ) = ((n : ℤ) : ℚ) := Int.cast_natCast n
  rw [h, qmod_intCast]
  exact Int.cast_natCast (R := ZMod p) n

lemma qmod_neg_natCast {p : ℕ} [Fact p.Prime] (n : ℕ) :
    qmod p (-(((n : ℕ)) : ℚ)) = -(((n : ℕ)) : ZMod p) := by
  rw [qmod_neg, qmod_natCast]

lemma phiCoeff_qmod_apply {p : ℕ} [Fact p.Prime] {d : ℕ} (i : Fin d) (ω : Fin d → Bool)
    (j : Fin d) :
    qmod p (phiCoeff p d i ω (Sum.inl j))
      = (if ω j then (1 : ZMod p) else 0)
        * (1 - (((i.val + 1 : ℕ)) : ZMod p) * ((((j.val + 1 : ℕ)) : ZMod p))⁻¹) := by
  rw [phiCoeff_inl]
  split_ifs
  · rw [phiC_qmod, one_mul]
  · rw [qmod_zero, zero_mul]

lemma phiCoeff'_qmod_apply {p : ℕ} [Fact p.Prime] {d : ℕ} (i : Fin d) (ω : Fin d → Bool)
    (j : Fin d) :
    qmod p (phiCoeff' p d i ω (Sum.inl j))
      = (if ω j then (1 : ZMod p) else 0)
        * (1 - (((i.val + 1 : ℕ)) : ZMod p) * ((((j.val + 1 : ℕ)) : ZMod p))⁻¹) := by
  rw [phiCoeff'_inl]
  split_ifs
  · rw [phiC_qmod, one_mul]
  · rw [qmod_zero, zero_mul]

/-- The linear form attached to the cube vertex `ω`. -/
noncomputable def cubeForm {p : ℕ} [Fact p.Prime] (d : ℕ) (v : Ix d → ZMod p)
    (ω : Fin d → Bool) : ZMod p :=
  ∑ k : Ix d, qmod p (cubeCoeff d ω k) * v k

/-- The linear form attached to `(i, ω)` with `ω i = false`, using the `s` coordinate. -/
noncomputable def phiForm {p : ℕ} [Fact p.Prime] {d : ℕ} (i : Fin d) (ω : Fin d → Bool)
    (v : Ix d → ZMod p) : ZMod p :=
  ∑ k : Ix d, qmod p (phiCoeff p d i ω k) * v k

/-- The linear form attached to `(i, ω)` with `ω i = false`, using the `s'` coordinate. -/
noncomputable def phiForm' {p : ℕ} [Fact p.Prime] {d : ℕ} (i : Fin d) (ω : Fin d → Bool)
    (v : Ix d → ZMod p) : ZMod p :=
  ∑ k : Ix d, qmod p (phiCoeff' p d i ω k) * v k

lemma eval_phiForm {p : ℕ} [Fact p.Prime] {d : ℕ} (i : Fin d) (ω : Fin d → Bool)
    (v : Ix d → ZMod p) :
    phiForm i ω v
      = v (Sum.inr 0)
        + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
        - (((i.val + 1 : ℕ)) : ZMod p)
          * (v (Sum.inr 1)
            + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1)) := by
  rw [phiForm, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h1 : ∀ j : Fin d,
      qmod p (phiCoeff p d i ω (Sum.inl j)) * v (Sum.inl j)
        = (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
          - (((i.val + 1 : ℕ)) : ZMod p)
            * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1)) := by
    intro j
    rw [phiCoeff_qmod_apply]
    have hj : ((((j.val + 1 : ℕ)) : ZMod p)) = (j : ZMod p) + 1 := by push_cast; rfl
    rw [hj]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  have h2 : qmod p (phiCoeff p d i ω (Sum.inr 0)) * v (Sum.inr 0) = v (Sum.inr 0) := by
    rw [phiCoeff_inr0, qmod_one, one_mul]
  have h3 : qmod p (phiCoeff p d i ω (Sum.inr 1)) * v (Sum.inr 1)
      = -(((i.val + 1 : ℕ)) : ZMod p) * v (Sum.inr 1) := by
    rw [phiCoeff_inr1, qmod_neg_natCast]
  have h4 : qmod p (phiCoeff p d i ω (Sum.inr 2)) * v (Sum.inr 2) = 0 := by
    rw [phiCoeff_inr2, qmod_zero, zero_mul]
  rw [h2, h3, h4, Finset.sum_sub_distrib]
  have hsumB : (∑ j : Fin d, (((i.val + 1 : ℕ)) : ZMod p)
        * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1)))
      = (((i.val + 1 : ℕ)) : ZMod p)
        * ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1) := by
    rw [Finset.mul_sum]
  rw [hsumB, mul_add]
  ring

lemma eval_phiForm' {p : ℕ} [Fact p.Prime] {d : ℕ} (i : Fin d) (ω : Fin d → Bool)
    (v : Ix d → ZMod p) :
    phiForm' i ω v
      = v (Sum.inr 0)
        + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
        - (((i.val + 1 : ℕ)) : ZMod p)
          * (v (Sum.inr 2)
            + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1)) := by
  rw [phiForm', Fintype.sum_sum_type, Fin.sum_univ_three]
  have h1 : ∀ j : Fin d,
      qmod p (phiCoeff' p d i ω (Sum.inl j)) * v (Sum.inl j)
        = (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j)
          - (((i.val + 1 : ℕ)) : ZMod p)
            * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1)) := by
    intro j
    rw [phiCoeff'_qmod_apply]
    have hj : ((((j.val + 1 : ℕ)) : ZMod p)) = (j : ZMod p) + 1 := by push_cast; rfl
    rw [hj]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  have h2 : qmod p (phiCoeff' p d i ω (Sum.inr 0)) * v (Sum.inr 0) = v (Sum.inr 0) := by
    rw [phiCoeff'_inr0, qmod_one, one_mul]
  have h3 : qmod p (phiCoeff' p d i ω (Sum.inr 1)) * v (Sum.inr 1) = 0 := by
    rw [phiCoeff'_inr1, qmod_zero, zero_mul]
  have h4 : qmod p (phiCoeff' p d i ω (Sum.inr 2)) * v (Sum.inr 2)
      = -(((i.val + 1 : ℕ)) : ZMod p) * v (Sum.inr 2) := by
    rw [phiCoeff'_inr2, qmod_neg_natCast]
  rw [h2, h3, h4, Finset.sum_sub_distrib]
  have hsumB : (∑ j : Fin d, (((i.val + 1 : ℕ)) : ZMod p)
        * ((if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1)))
      = (((i.val + 1 : ℕ)) : ZMod p)
        * ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) / ((j : ZMod p) + 1) := by
    rw [Finset.mul_sum]
  rw [hsumB, mul_add]
  ring

lemma eval_cubeForm {p : ℕ} [Fact p.Prime] {d : ℕ} (ω : Fin d → Bool) (v : Ix d → ZMod p) :
    cubeForm d v ω
      = v (Sum.inr 0) + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) := by
  rw [cubeForm, Fintype.sum_sum_type, Fin.sum_univ_three]
  have h1 : ∀ j : Fin d, qmod p (cubeCoeff d ω (Sum.inl j)) * v (Sum.inl j)
      = (if ω j then (1 : ZMod p) else 0) * v (Sum.inl j) := by
    intro j
    rw [cubeCoeff_inl]
    split_ifs
    · rw [qmod_one, one_mul]
    · rw [qmod_zero, zero_mul]
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  have h2 : qmod p (cubeCoeff d ω (Sum.inr 0)) * v (Sum.inr 0) = v (Sum.inr 0) := by
    rw [cubeCoeff_inr0, qmod_one, one_mul]
  have h3 : qmod p (cubeCoeff d ω (Sum.inr 1)) * v (Sum.inr 1) = 0 := by
    rw [cubeCoeff_inr1, qmod_zero, zero_mul]
  have h4 : qmod p (cubeCoeff d ω (Sum.inr 2)) * v (Sum.inr 2) = 0 := by
    rw [cubeCoeff_inr2, qmod_zero, zero_mul]
  rw [h2, h3, h4]
  ring

/-- The cube form in the coordinates `(h, x, s, s')`. -/
lemma cubeForm_mk {p : ℕ} [Fact p.Prime] {d : ℕ} (h : Fin d → ZMod p) (x s s' : ZMod p)
    (ω : Fin d → Bool) :
    cubeForm d (Sum.elim h ![x, s, s']) ω
      = x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j := by
  rw [eval_cubeForm]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp

/-- The `s`-form in the coordinates `(h, x, s, s')`. -/
lemma phiForm_mk {p : ℕ} [Fact p.Prime] {d : ℕ} (h : Fin d → ZMod p) (x s s' : ZMod p)
    (i : Fin d) (ω : Fin d → Bool) :
    phiForm i ω (Sum.elim h ![x, s, s'])
      = x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j
        - (((i.val + 1 : ℕ)) : ZMod p)
          * (s + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j / ((j : ZMod p) + 1)) := by
  rw [eval_phiForm]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp

/-- The `s'`-form in the coordinates `(h, x, s, s')`. -/
lemma phiForm'_mk {p : ℕ} [Fact p.Prime] {d : ℕ} (h : Fin d → ZMod p) (x s s' : ZMod p)
    (i : Fin d) (ω : Fin d → Bool) :
    phiForm' i ω (Sum.elim h ![x, s, s'])
      = x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j
        - (((i.val + 1 : ℕ)) : ZMod p)
          * (s' + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j / ((j : ZMod p) + 1)) := by
  rw [eval_phiForm']
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp

lemma isSmallRat_intCast {L₀ : ℕ} (hL : 1 ≤ L₀) (n : ℤ) (hn : n.natAbs ≤ L₀) :
    IsSmallRat L₀ ((n : ℤ) : ℚ) := by
  rw [IsSmallRat, Rat.num_intCast, Rat.den_intCast]
  exact ⟨hn, hL⟩

lemma phiC_ne_zero {p d : ℕ} {i j : Fin d} (h : i ≠ j) : phiC p i.val j.val ≠ 0 := by
  unfold phiC
  split_ifs with hp
  · norm_num
  · apply div_ne_zero
    · rw [sub_ne_zero]
      have : j.val ≠ i.val := fun hc => h (Fin.ext hc.symm)
      exact_mod_cast this
    · exact_mod_cast (by omega : (j.val + 1 : ℕ) ≠ 0)

lemma isSmallRat_phiC_val {p d : ℕ} (hd : 1 ≤ d) (i j : Fin d) :
    IsSmallRat d (phiC p i.val j.val) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold phiC
  split_ifs with hp
  · exact isSmallRat_one hd
  · have h := isSmallRat_rat_div (L₀ := d) (a := ((j.val : ℤ) - (i.val : ℤ))) (n := j.val + 1)
      (by omega) (by omega) (by omega)
    convert h using 2
    push_cast; ring

lemma isSmallRat_cubeCoeff {d : ℕ} (hd : 1 ≤ d) (ω : Fin d → Bool)
    (j : Ix d) : IsSmallRat d (cubeCoeff d ω j) := by
  rcases j with j | k
  · rw [cubeCoeff_inl]; split_ifs
    · exact isSmallRat_one hd
    · exact isSmallRat_zero hd
  · fin_cases k
    · change IsSmallRat d (cubeCoeff d ω (Sum.inr 0)); rw [cubeCoeff_inr0]
      exact isSmallRat_one hd
    · change IsSmallRat d (cubeCoeff d ω (Sum.inr 1)); rw [cubeCoeff_inr1]
      exact isSmallRat_zero hd
    · change IsSmallRat d (cubeCoeff d ω (Sum.inr 2)); rw [cubeCoeff_inr2]
      exact isSmallRat_zero hd

lemma isSmallRat_neg_natCast {L₀ : ℕ} (hd : 1 ≤ L₀) (n : ℕ) (hn : n ≤ L₀) :
    IsSmallRat L₀ (-(((n : ℕ)) : ℚ)) := by
  have h := isSmallRat_intCast (L₀ := L₀) hd (-(n : ℤ)) (by simp; omega)
  simpa using h

lemma isSmallRat_phiCoeff {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (i : Fin d)
    (ω : Fin d → Bool) (j : Ix d) : IsSmallRat d (phiCoeff p d i ω j) := by
  rcases j with j' | k
  · rw [phiCoeff_inl]; split_ifs
    · exact isSmallRat_phiC_val hd i j'
    · exact isSmallRat_zero hd
  · fin_cases k
    · change IsSmallRat d (phiCoeff p d i ω (Sum.inr 0)); rw [phiCoeff_inr0]
      exact isSmallRat_one hd
    · change IsSmallRat d (phiCoeff p d i ω (Sum.inr 1)); rw [phiCoeff_inr1]
      exact isSmallRat_neg_natCast hd _ (by have := i.isLt; omega)
    · change IsSmallRat d (phiCoeff p d i ω (Sum.inr 2)); rw [phiCoeff_inr2]
      exact isSmallRat_zero hd

lemma isSmallRat_phiCoeff' {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) (i : Fin d)
    (ω : Fin d → Bool) (j : Ix d) : IsSmallRat d (phiCoeff' p d i ω j) := by
  rcases j with j' | k
  · rw [phiCoeff'_inl]; split_ifs
    · exact isSmallRat_phiC_val hd i j'
    · exact isSmallRat_zero hd
  · fin_cases k
    · change IsSmallRat d (phiCoeff' p d i ω (Sum.inr 0)); rw [phiCoeff'_inr0]
      exact isSmallRat_one hd
    · change IsSmallRat d (phiCoeff' p d i ω (Sum.inr 1)); rw [phiCoeff'_inr1]
      exact isSmallRat_zero hd
    · change IsSmallRat d (phiCoeff' p d i ω (Sum.inr 2)); rw [phiCoeff'_inr2]
      exact isSmallRat_neg_natCast hd _ (by have := i.isLt; omega)

lemma cubeCoeff_ne {d : ℕ} {ω ω' : Fin d → Bool} (h : ω ≠ ω') :
    cubeCoeff d ω ≠ cubeCoeff d ω' := by
  intro hc
  apply h
  funext j
  have := congrFun hc (Sum.inl j)
  rw [cubeCoeff_inl, cubeCoeff_inl] at this
  by_cases hω : ω j <;> by_cases hω' : ω' j <;> simp_all

lemma phiCoeff_inj {p d : ℕ} {i i' : Fin d} {ω ω' : Fin d → Bool}
    (hω : ω i = false) (hω' : ω' i' = false)
    (h : phiCoeff p d i ω = phiCoeff p d i' ω') : i = i' ∧ ω = ω' := by
  have h1 := congrFun h (Sum.inr 1)
  rw [phiCoeff_inr1, phiCoeff_inr1] at h1
  have hii : i = i' := by
    have h2 : ((i.val + 1 : ℕ) : ℚ) = ((i'.val + 1 : ℕ) : ℚ) := neg_inj.mp h1
    have h3 : i.val + 1 = i'.val + 1 := Nat.cast_injective h2
    exact Fin.ext (by omega)
  refine ⟨hii, ?_⟩
  subst hii
  funext j
  by_cases hj : j = i
  · subst hj
    rw [hω, hω']
  · have hz : phiC p i.val j.val ≠ 0 := phiC_ne_zero (Ne.symm hj)
    have h2 := congrFun h (Sum.inl j)
    rw [phiCoeff_inl, phiCoeff_inl] at h2
    by_cases hωj : ω j
    · by_cases hω'j : ω' j
      · simp [hωj, hω'j]
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2
    · by_cases hω'j : ω' j
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2.symm
      · simp [hωj, hω'j]

lemma phiCoeff'_inj {p d : ℕ} {i i' : Fin d} {ω ω' : Fin d → Bool}
    (hω : ω i = false) (hω' : ω' i' = false)
    (h : phiCoeff' p d i ω = phiCoeff' p d i' ω') : i = i' ∧ ω = ω' := by
  have h1 := congrFun h (Sum.inr 2)
  rw [phiCoeff'_inr2, phiCoeff'_inr2] at h1
  have hii : i = i' := by
    have h2 : ((i.val + 1 : ℕ) : ℚ) = ((i'.val + 1 : ℕ) : ℚ) := neg_inj.mp h1
    have h3 : i.val + 1 = i'.val + 1 := Nat.cast_injective h2
    exact Fin.ext (by omega)
  refine ⟨hii, ?_⟩
  subst hii
  funext j
  by_cases hj : j = i
  · subst hj
    rw [hω, hω']
  · have hz : phiC p i.val j.val ≠ 0 := phiC_ne_zero (Ne.symm hj)
    have h2 := congrFun h (Sum.inl j)
    rw [phiCoeff'_inl, phiCoeff'_inl] at h2
    by_cases hωj : ω j
    · by_cases hω'j : ω' j
      · simp [hωj, hω'j]
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2
    · by_cases hω'j : ω' j
      · refine absurd ?_ hz
        simpa [hωj, hω'j] using h2.symm
      · simp [hωj, hω'j]

/-! ## Non-degeneracy of the coefficient families -/

/-- Index type of the cube forms. -/
abbrev CubeIx (d : ℕ) := Fin d → Bool

/-- Index type of the `φ_i` forms with `ω i = false`. -/
abbrev PhiIx (d : ℕ) := Σ i : Fin d, {ω : Fin d → Bool // ω i = false}

lemma neg_natCast_succ_ne_zero {d : ℕ} (i : Fin d) : -(((i.val + 1 : ℕ)) : ℚ) ≠ 0 := by
  rw [neg_ne_zero]
  exact Nat.cast_ne_zero.mpr (by omega)

lemma notProp_of_x_eq_one {d : ℕ} {L L' : Ix d → ℚ} (hL : L (Sum.inr 0) = 1)
    (hL' : L' (Sum.inr 0) = 1) (hne : L ≠ L') :
    ¬ ∃ lam : ℚ, ∀ j, L' j = lam * L j := by
  rintro ⟨lam, hlam⟩
  apply hne
  funext k
  have h0 := hlam (Sum.inr 0)
  rw [hL, hL', mul_one] at h0
  rw [hlam k, ← h0, one_mul]

lemma notProp_of_zero_coord {d : ℕ} {L L' : Ix d → ℚ} {k : Ix d}
    (hL : L k = 0) (hL' : L' k ≠ 0) : ¬ ∃ lam : ℚ, ∀ j, L' j = lam * L j := by
  rintro ⟨lam, hlam⟩
  have h0 := hlam k
  rw [hL, mul_zero] at h0
  exact hL' h0

lemma notProp_of_zero_coord' {d : ℕ} {L L' : Ix d → ℚ} {k : Ix d}
    (hL : L k ≠ 0) (hL' : L' k = 0) (hL'0 : L' (Sum.inr 0) = 1) :
    ¬ ∃ lam : ℚ, ∀ j, L' j = lam * L j := by
  rintro ⟨lam, hlam⟩
  have h0 : lam * L k = 0 := by rw [← hlam k, hL']
  have hlam0 : lam = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd h hL
  have h1 := hlam (Sum.inr 0)
  rw [hL'0, hlam0, zero_mul] at h1
  exact one_ne_zero h1

lemma notProp_cube {d : ℕ} {ω ω' : Fin d → Bool} (h : ω ≠ ω') :
    ¬ ∃ lam : ℚ, ∀ j, cubeCoeff d ω' j = lam * cubeCoeff d ω j :=
  notProp_of_x_eq_one (L := cubeCoeff d ω) (L' := cubeCoeff d ω')
    (cubeCoeff_inr0 d ω) (cubeCoeff_inr0 d ω') (cubeCoeff_ne h)

lemma notProp_phi {p d : ℕ} {s s' : PhiIx d} (h : s ≠ s') :
    ¬ ∃ lam : ℚ, ∀ j, phiCoeff p d s'.1 s'.2.1 j = lam * phiCoeff p d s.1 s.2.1 j := by
  obtain ⟨i, ω, hω⟩ := s
  obtain ⟨i', ω', hω'⟩ := s'
  refine notProp_of_x_eq_one (L := phiCoeff p d i ω) (L' := phiCoeff p d i' ω')
    (phiCoeff_inr0 p d i ω) (phiCoeff_inr0 p d i' ω') ?_
  intro hc
  apply h
  obtain ⟨h1a, h1b⟩ := phiCoeff_inj hω hω' hc
  subst h1a
  congr 1
  exact Subtype.ext h1b

lemma notProp_phi' {p d : ℕ} {s s' : PhiIx d} (h : s ≠ s') :
    ¬ ∃ lam : ℚ, ∀ j, phiCoeff' p d s'.1 s'.2.1 j = lam * phiCoeff' p d s.1 s.2.1 j := by
  obtain ⟨i, ω, hω⟩ := s
  obtain ⟨i', ω', hω'⟩ := s'
  refine notProp_of_x_eq_one (L := phiCoeff' p d i ω) (L' := phiCoeff' p d i' ω')
    (phiCoeff'_inr0 p d i ω) (phiCoeff'_inr0 p d i' ω') ?_
  intro hc
  apply h
  obtain ⟨h1a, h1b⟩ := phiCoeff'_inj hω hω' hc
  subst h1a
  congr 1
  exact Subtype.ext h1b

/-! ## The three applications of the linear forms condition -/

noncomputable abbrev Lcube (d : ℕ) : CubeIx d → Ix d → ℚ := fun ω => cubeCoeff d ω
noncomputable abbrev Lphi (p d : ℕ) : PhiIx d → Ix d → ℚ := fun s => phiCoeff p d s.1 s.2.1
noncomputable abbrev Lphi' (p d : ℕ) : PhiIx d → Ix d → ℚ := fun s => phiCoeff' p d s.1 s.2.1

lemma cubeCoeff_inr0_ne {d : ℕ} (ω : Fin d → Bool) : cubeCoeff d ω (Sum.inr 0) ≠ 0 := by
  rw [cubeCoeff_inr0]; norm_num

lemma phiCoeff_inr0_ne (p : ℕ) {d : ℕ} (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff p d i ω (Sum.inr 0) ≠ 0 := by
  rw [phiCoeff_inr0]; norm_num

lemma phiCoeff'_inr0_ne (p : ℕ) {d : ℕ} (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff' p d i ω (Sum.inr 0) ≠ 0 := by
  rw [phiCoeff'_inr0]; norm_num

lemma phiCoeff_inr1_ne (p : ℕ) {d : ℕ} (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff p d i ω (Sum.inr 1) ≠ 0 := by
  rw [phiCoeff_inr1]; exact neg_natCast_succ_ne_zero i

lemma phiCoeff'_inr2_ne (p : ℕ) {d : ℕ} (i : Fin d) (ω : Fin d → Bool) :
    phiCoeff' p d i ω (Sum.inr 2) ≠ 0 := by
  rw [phiCoeff'_inr2]; exact neg_natCast_succ_ne_zero i

lemma card_cubeIx (d : ℕ) : Fintype.card (CubeIx d) = 2 ^ d := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

lemma card_phiIx (d : ℕ) : Fintype.card (PhiIx d) = d * 2 ^ (d - 1) :=
  Commons.Combinatorics.Finset.card_sigma_bool_false

lemma pow_two_eq (d : ℕ) (hd : 1 ≤ d) : 2 ^ d = 2 * 2 ^ (d - 1) := by
  conv_lhs => rw [show d = d - 1 + 1 from by omega]
  rw [pow_succ']

lemma lfc_gvn_S0 {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ} {ε : ℝ}
    (hLFC : LinFormsCond p ν (2 ^ d * (d + 1)) (d + 3) d ε) :
    |((Fintype.card (Ix d → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix d → ZMod p, ∏ ω : CubeIx d, ν (cubeForm d v ω)) - 1| ≤ ε := by
  have hcard1 : 1 ≤ Fintype.card (CubeIx d) := by
    rw [card_cubeIx]
    exact Nat.one_le_two_pow
  have hcard2 : Fintype.card (CubeIx d) ≤ 2 ^ d * (d + 1) := by
    rw [card_cubeIx]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have h := lfc_apply_equiv (V := Ix d) (e := finSumFinEquiv) hLFC (t := d + 3)
    (by omega) le_rfl hcard1 hcard2 (Lcube d)
    (fun i j => isSmallRat_cubeCoeff hd i j)
    (fun i => ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩)
    (fun i i' hii => notProp_cube hii)
    (fun _ => 0)
  simpa only [Lcube, cubeForm, Pi.zero_apply, add_zero] using h

lemma lfc_gvn_S1 {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ} {ε : ℝ}
    (hLFC : LinFormsCond p ν (2 ^ d * (d + 1)) (d + 3) d ε) :
    |((Fintype.card (Ix d → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix d → ZMod p,
        (∏ ω : CubeIx d, ν (cubeForm d v ω))
        * ∏ s : PhiIx d, ν (phiForm s.1 s.2.1 v)) - 1| ≤ ε := by
  have hcard : Fintype.card (CubeIx d ⊕ PhiIx d) ≤ 2 ^ d * (d + 1) := by
    rw [Fintype.card_sum, card_cubeIx, card_phiIx]
    calc 2 ^ d + d * 2 ^ (d - 1) ≤ 2 ^ d + d * 2 ^ d :=
          Nat.add_le_add_left
            (Nat.mul_le_mul_left d (Nat.pow_le_pow_right (by norm_num) (by omega))) _
      _ = 2 ^ d * (d + 1) := by ring
  have hcard1 : 1 ≤ Fintype.card (CubeIx d ⊕ PhiIx d) := by
    rw [Fintype.card_sum, card_cubeIx]
    have := Nat.one_le_two_pow (n := d)
    omega
  have h := lfc_apply_equiv (V := Ix d) (e := finSumFinEquiv) hLFC (t := d + 3)
    (by omega) le_rfl hcard1 hcard
    (Sum.elim (Lcube d) (Lphi p d))
    (fun i j => by
      rcases i with i | i
      · exact isSmallRat_cubeCoeff hd i j
      · exact isSmallRat_phiCoeff (p := p) hd i.1 i.2.1 j)
    (fun i => by
      rcases i with i | i
      · exact ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩
      · exact ⟨Sum.inr 0, phiCoeff_inr0_ne p i.1 i.2.1⟩)
    (fun i i' hii => by
      rcases i with i | i <;> rcases i' with i' | i'
      · exact notProp_cube (fun hc => hii (by rw [hc]))
      · exact notProp_of_zero_coord (L := cubeCoeff d i) (L' := phiCoeff p d i'.1 i'.2.1)
          (k := Sum.inr 1) (cubeCoeff_inr1 d i) (phiCoeff_inr1_ne p i'.1 i'.2.1)
      · refine notProp_of_zero_coord' (L := phiCoeff p d i.1 i.2.1) (L' := cubeCoeff d i')
          (k := Sum.inr 1) (phiCoeff_inr1_ne p i.1 i.2.1) (cubeCoeff_inr1 d i') ?_
        exact cubeCoeff_inr0 d i'
      · exact notProp_phi (fun hc => hii (by rw [hc])))
    (fun _ => 0)
  simp only [Fintype.prod_sum_type] at h
  simpa only [Lcube, Lphi, Sum.elim_inl, Sum.elim_inr, cubeForm, phiForm, Pi.zero_apply,
    add_zero] using h

lemma lfc_gvn_S2 {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ} {ε : ℝ}
    (hLFC : LinFormsCond p ν (2 ^ d * (d + 1)) (d + 3) d ε) :
    |((Fintype.card (Ix d → ZMod p) : ℝ))⁻¹ *
      (∑ v : Ix d → ZMod p,
        (∏ ω : CubeIx d, ν (cubeForm d v ω))
        * (∏ s : PhiIx d, ν (phiForm s.1 s.2.1 v))
        * ∏ s : PhiIx d, ν (phiForm' s.1 s.2.1 v)) - 1| ≤ ε := by
  have hcard : Fintype.card (CubeIx d ⊕ (PhiIx d ⊕ PhiIx d)) ≤ 2 ^ d * (d + 1) := by
    rw [Fintype.card_sum, Fintype.card_sum, card_cubeIx, card_phiIx, pow_two_eq d hd]
    have : 2 * 2 ^ (d - 1) + (d * 2 ^ (d - 1) + d * 2 ^ (d - 1))
        = 2 * 2 ^ (d - 1) * (d + 1) := by ring
    rw [this]
  have hcard1 : 1 ≤ Fintype.card (CubeIx d ⊕ (PhiIx d ⊕ PhiIx d)) := by
    rw [Fintype.card_sum, card_cubeIx]
    have := Nat.one_le_two_pow (n := d)
    omega
  have h := lfc_apply_equiv (V := Ix d) (e := finSumFinEquiv) hLFC (t := d + 3)
    (by omega) le_rfl hcard1 hcard
    (Sum.elim (Lcube d) (Sum.elim (Lphi p d) (Lphi' p d)))
    (fun i j => by
      rcases i with i | i | i
      · exact isSmallRat_cubeCoeff hd i j
      · exact isSmallRat_phiCoeff (p := p) hd i.1 i.2.1 j
      · exact isSmallRat_phiCoeff' (p := p) hd i.1 i.2.1 j)
    (fun i => by
      rcases i with i | i | i
      · exact ⟨Sum.inr 0, cubeCoeff_inr0_ne i⟩
      · exact ⟨Sum.inr 0, phiCoeff_inr0_ne p i.1 i.2.1⟩
      · exact ⟨Sum.inr 0, phiCoeff'_inr0_ne p i.1 i.2.1⟩)
    (fun i i' hii => by
      rcases i with i | i | i <;> rcases i' with i' | i' | i'
      · exact notProp_cube (fun hc => hii (by rw [hc]))
      · exact notProp_of_zero_coord (L := cubeCoeff d i) (L' := phiCoeff p d i'.1 i'.2.1)
          (k := Sum.inr 1) (cubeCoeff_inr1 d i) (phiCoeff_inr1_ne p i'.1 i'.2.1)
      · exact notProp_of_zero_coord (L := cubeCoeff d i) (L' := phiCoeff' p d i'.1 i'.2.1)
          (k := Sum.inr 2) (cubeCoeff_inr2 d i) (phiCoeff'_inr2_ne p i'.1 i'.2.1)
      · refine notProp_of_zero_coord' (L := phiCoeff p d i.1 i.2.1) (L' := cubeCoeff d i')
          (k := Sum.inr 1) (phiCoeff_inr1_ne p i.1 i.2.1) (cubeCoeff_inr1 d i') ?_
        exact cubeCoeff_inr0 d i'
      · exact notProp_phi (fun hc => hii (by rw [hc]))
      · refine notProp_of_zero_coord' (L := phiCoeff p d i.1 i.2.1)
          (L' := phiCoeff' p d i'.1 i'.2.1) (k := Sum.inr 1) (phiCoeff_inr1_ne p i.1 i.2.1)
          (phiCoeff'_inr1 p d i'.1 i'.2.1) ?_
        exact phiCoeff'_inr0 p d i'.1 i'.2.1
      · refine notProp_of_zero_coord' (L := phiCoeff' p d i.1 i.2.1) (L' := cubeCoeff d i')
          (k := Sum.inr 2) (phiCoeff'_inr2_ne p i.1 i.2.1) (cubeCoeff_inr2 d i') ?_
        exact cubeCoeff_inr0 d i'
      · exact notProp_of_zero_coord (L := phiCoeff' p d i.1 i.2.1)
          (L' := phiCoeff p d i'.1 i'.2.1) (k := Sum.inr 1) (phiCoeff'_inr1 p d i.1 i.2.1)
          (phiCoeff_inr1_ne p i'.1 i'.2.1)
      · exact notProp_phi' (fun hc => hii (by rw [hc])))
    (fun _ => 0)
  simp only [Fintype.prod_sum_type] at h
  simpa only [Lcube, Lphi, Lphi', Sum.elim_inl, Sum.elim_inr, cubeForm, phiForm, phiForm',
    Pi.zero_apply, add_zero, mul_assoc] using h

/-! ## The weighted cube moment -/

/-- The cube weight `∏_ω ν(x + ω·h)`. -/
noncomputable def T0 (p : ℕ) [Fact p.Prime] (d : ℕ) (ν : ZMod p → ℝ)
    (h : Fin d → ZMod p) (x : ZMod p) : ℝ :=
  ∏ ω : CubeIx d, ν (x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j)

/-- The `φ`-product `∏_{i, ω_i = 0} ν(φ_i(x + ω·h, s))`. -/
noncomputable def PhiF (p : ℕ) [Fact p.Prime] (d : ℕ) (ν : ZMod p → ℝ)
    (h : Fin d → ZMod p) (x s : ZMod p) : ℝ :=
  ∏ i : Fin d, ∏ ω ∈ (Finset.univ.filter (fun ω : Fin d → Bool => ω i = false)),
    ν (x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j
      - (((1 + i.val : ℕ)) : ZMod p)
        * (s + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j / ((j : ZMod p) + 1)))

/-- The average of `PhiF` over `s`. -/
noncomputable def Aavg (p : ℕ) [Fact p.Prime] (d : ℕ) (ν : ZMod p → ℝ)
    (h : Fin d → ZMod p) (x : ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * ∑ s : ZMod p, PhiF p d ν h x s

/-- The canonical equivalence between `{ω // ω i = false}` and the corresponding `Finset`
subtype. -/
def phiSubtypeEquiv (d : ℕ) (i : Fin d) :
    {ω : Fin d → Bool // ω i = false} ≃
      ↥(Finset.univ.filter (fun ω : Fin d → Bool => ω i = false)) where
  toFun ω := ⟨ω.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ω.2⟩⟩
  invFun ω := ⟨ω.1, (Finset.mem_filter.mp ω.2).2⟩
  left_inv ω := by ext; rfl
  right_inv ω := by ext; rfl

lemma prod_phiIx {d : ℕ} {M : Type*} [CommMonoid M] {F : (i : Fin d) → (Fin d → Bool) → M} :
    (∏ s : PhiIx d, F s.1 s.2.1)
      = ∏ i : Fin d, ∏ ω ∈ (Finset.univ.filter (fun ω : Fin d → Bool => ω i = false)), F i ω := by
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_attach (Finset.univ.filter (fun ω : Fin d → Bool => ω i = false)) (F i),
    Finset.attach_eq_univ]
  exact Fintype.prod_equiv (phiSubtypeEquiv d i) (fun b => F i b.1) (fun y => F i y.1)
    (fun b => rfl)

lemma prod_cube_mk {p : ℕ} [Fact p.Prime] {d : ℕ} {ν : ZMod p → ℝ}
    {h : Fin d → ZMod p} {x s s' : ZMod p} :
    (∏ ω : CubeIx d, ν (cubeForm d (Sum.elim h ![x, s, s']) ω)) = T0 p d ν h x := by
  rw [T0]
  apply Finset.prod_congr rfl
  intro ω _
  rw [cubeForm_mk]

lemma prod_phi_mk {p : ℕ} [Fact p.Prime] {d : ℕ} {ν : ZMod p → ℝ}
    {h : Fin d → ZMod p} {x s s' : ZMod p} :
    (∏ s0 : PhiIx d, ν (phiForm s0.1 s0.2.1 (Sum.elim h ![x, s, s']))) = PhiF p d ν h x s := by
  rw [PhiF]
  rw [prod_phiIx (F := fun i ω => ν (phiForm i ω (Sum.elim h ![x, s, s'])))]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro ω _
  rw [phiForm_mk]
  congr 1
  rw [show (((i.val + 1 : ℕ)) : ZMod p) = (((1 + i.val : ℕ)) : ZMod p) from by
    push_cast; ring]

lemma prod_phi'_mk {p : ℕ} [Fact p.Prime] {d : ℕ} {ν : ZMod p → ℝ}
    {h : Fin d → ZMod p} {x s s' : ZMod p} :
    (∏ s0 : PhiIx d, ν (phiForm' s0.1 s0.2.1 (Sum.elim h ![x, s, s']))) = PhiF p d ν h x s' := by
  rw [PhiF]
  rw [prod_phiIx (F := fun i ω => ν (phiForm' i ω (Sum.elim h ![x, s, s'])))]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro ω _
  rw [phiForm'_mk]
  congr 1
  rw [show (((i.val + 1 : ℕ)) : ZMod p) = (((1 + i.val : ℕ)) : ZMod p) from by
    push_cast; ring]

lemma zmod_sum_const {p : ℕ} [Fact p.Prime] (c : ℝ) :
    (∑ _ : ZMod p, c) = (p : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]

lemma zmod_sum_sum_const {p : ℕ} [Fact p.Prime] (c : ℝ) :
    (∑ _ : ZMod p, ∑ _ : ZMod p, c) = (p : ℝ) * ((p : ℝ) * c) := by
  simp only [zmod_sum_const]

lemma zmod_sum_sum_smul {p : ℕ} [Fact p.Prime] (c : ℝ) (F : ZMod p → ℝ) :
    (∑ s : ZMod p, ∑ _ : ZMod p, c * F s) = (c * ∑ s, F s) * (p : ℝ) := by
  have h1 : (∑ s : ZMod p, ∑ _ : ZMod p, c * F s) = ∑ s, (c * F s) * (p : ℝ) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [zmod_sum_const]
    ring
  rw [h1, ← Finset.sum_mul, ← Finset.mul_sum]

lemma zmod_sum_sum_mul {p : ℕ} [Fact p.Prime] (c : ℝ) (F G : ZMod p → ℝ) :
    (∑ s : ZMod p, ∑ s' : ZMod p, c * F s * G s') = c * (∑ s, F s) * (∑ s', G s') := by
  have h1 : (∑ s : ZMod p, ∑ s' : ZMod p, c * F s * G s')
      = ∑ s, (c * F s) * (∑ s', G s') := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum]
  rw [h1, ← Finset.sum_mul, ← Finset.mul_sum]

lemma sum_sum_sub {ι κ : Type*} [Fintype ι] [Fintype κ] (f g : ι → κ → ℝ) :
    (∑ i, ∑ j, (f i j - g i j)) = (∑ i, ∑ j, f i j) - (∑ i, ∑ j, g i j) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]

lemma sum_sum_add {ι κ : Type*} [Fintype ι] [Fintype κ] (f g : ι → κ → ℝ) :
    (∑ i, ∑ j, (f i j + g i j)) = (∑ i, ∑ j, f i j) + (∑ i, ∑ j, g i j) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]

set_option maxHeartbeats 1000000 in
theorem lfc_weight_moment {p : ℕ} [Fact p.Prime] {d : ℕ} (hd : 1 ≤ d) {ν : ZMod p → ℝ}
    (hν : ∀ x, 0 ≤ ν x) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hLFC : Commons.NumberTheory.Sieve.LinFormsCond p ν (2 ^ d * (d + 1)) (d + 3) d ε) :
    (∑ h : Fin d → ZMod p, ∑ x : ZMod p,
        (∏ ω : Fin d → Bool, ν (x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
        * ((((p : ℝ))⁻¹ * ∑ s : ZMod p,
            ∏ i : Fin d, ∏ ω ∈ (Finset.univ.filter (fun ω : Fin d → Bool => ω i = false)),
              ν (x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j
                - (((1 + i.val : ℕ)) : ZMod p)
                  * (s + ∑ j : Fin d,
                      (if ω j then (1 : ZMod p) else 0) * h j / ((j : ZMod p) + 1)))
            - 1)^2))
      ≤ 4 * ε * (p : ℝ) ^ (d + 1) := by
  set P : ℝ := (p : ℝ) with hP
  have hPpos : 0 < P := by
    rw [hP]; exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hpne : (p : ℝ) ≠ 0 := by
    have h := (Fact.out : Nat.Prime p).pos
    exact_mod_cast (ne_of_gt h)
  have hPne : P ≠ 0 := by rw [hP]; exact hpne
  -- the three linear-forms-condition averages, in nested coordinates
  have hS0 := lfc_gvn_S0 (p := p) hd hLFC
  have hS1 := lfc_gvn_S1 (p := p) hd hLFC
  have hS2 := lfc_gvn_S2 (p := p) hd hLFC
  rw [sum_fun_sum_equiv] at hS0 hS1 hS2
  simp only [prod_cube_mk] at hS0 hS1 hS2
  simp only [prod_phi_mk] at hS1 hS2
  simp only [prod_phi'_mk] at hS2
  have hNval : (Fintype.card (Ix d → ZMod p) : ℝ) = P ^ (d + 3) := by
    rw [Fintype.card_fun, ZMod.card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    push_cast
    rw [hP]
  rw [hNval] at hS0 hS1 hS2
  have hNpos : 0 < P ^ (d + 3) := by positivity
  have hNne : P ^ (d + 3) ≠ 0 := ne_of_gt hNpos
  have hb0 := abs_le.mp hS0
  have hb1 := abs_le.mp hS1
  have hb2 := abs_le.mp hS2
  have key0 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x)
      ≤ (1 + ε) * P ^ (d + 3) := by
    have h1 : (P ^ (d + 3))⁻¹ * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x)
        ≤ 1 + ε := by linarith [hb0.2]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul, mul_comm (P ^ (d + 3)) (1 + ε)] at h2
  have key1 : (1 - ε) * P ^ (d + 3)
      ≤ (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x * PhiF p d ν h x s) := by
    have h1 : 1 - ε ≤ (P ^ (d + 3))⁻¹
        * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x * PhiF p d ν h x s) := by
      linarith [hb1.1]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul, mul_comm (P ^ (d + 3)) (1 - ε)] at h2
  have key2 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p d ν h x * PhiF p d ν h x s * PhiF p d ν h x s')
      ≤ (1 + ε) * P ^ (d + 3) := by
    have h1 : (P ^ (d + 3))⁻¹ * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p d ν h x * PhiF p d ν h x s * PhiF p d ν h x s') ≤ 1 + ε := by
      linarith [hb2.2]
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hNpos)
    rwa [← mul_assoc, mul_inv_cancel₀ hNne, one_mul, mul_comm (P ^ (d + 3)) (1 + ε)] at h2
  -- evaluation of the `s`-averages
  have hA : ∀ h x, P * Aavg p d ν h x = ∑ s : ZMod p, PhiF p d ν h x s := by
    intro h x
    rw [hP, Aavg, ← mul_assoc, mul_inv_cancel₀ hpne, one_mul]
  -- the three averages in terms of `P²` and the `(h,x)`-sums
  have h0 : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x)
      = P ^ 2 * (∑ h, ∑ x, T0 p d ν h x) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x) = P ^ 2 * T0 p d ν h x := by
      intro h x
      rw [zmod_sum_sum_const, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x)
          = ∑ h, ∑ x, P ^ 2 * T0 p d ν h x from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have h1e : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x * PhiF p d ν h x s)
      = P ^ 2 * (∑ h, ∑ x, T0 p d ν h x * Aavg p d ν h x) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x * PhiF p d ν h x s)
        = P ^ 2 * (T0 p d ν h x * Aavg p d ν h x) := by
      intro h x
      rw [zmod_sum_sum_smul, ← hA h x, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x * PhiF p d ν h x s)
          = ∑ h, ∑ x, P ^ 2 * (T0 p d ν h x * Aavg p d ν h x) from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  have h2e : (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
        T0 p d ν h x * PhiF p d ν h x s * PhiF p d ν h x s')
      = P ^ 2 * (∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x) ^ 2) := by
    have e : ∀ h x, (∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p d ν h x * PhiF p d ν h x s * PhiF p d ν h x s')
        = P ^ 2 * (T0 p d ν h x * (Aavg p d ν h x) ^ 2) := by
      intro h x
      rw [zmod_sum_sum_mul, ← hA h x, hP]
      ring
    rw [show (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
          T0 p d ν h x * PhiF p d ν h x s * PhiF p d ν h x s')
          = ∑ h, ∑ x, P ^ 2 * (T0 p d ν h x * (Aavg p d ν h x) ^ 2) from by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro x _
        exact e h x]
    simp only [Finset.mul_sum]
  -- expansion of the square
  have hLexp : (∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x - 1) ^ 2)
      = (∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x) ^ 2)
        - 2 * (∑ h, ∑ x, T0 p d ν h x * Aavg p d ν h x)
        + (∑ h, ∑ x, T0 p d ν h x) := by
    have h2Y : 2 * (∑ h, ∑ x, T0 p d ν h x * Aavg p d ν h x)
        = ∑ h, ∑ x, 2 * (T0 p d ν h x * Aavg p d ν h x) := by
      simp only [Finset.mul_sum]
    rw [h2Y, ← sum_sum_sub, ← sum_sum_add]
    apply Finset.sum_congr rfl
    intro h _
    apply Finset.sum_congr rfl
    intro x _
    ring
  -- the main identity
  have hP2L : P ^ 2 * (∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x - 1) ^ 2)
      = (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p d ν h x * PhiF p d ν h x s * PhiF p d ν h x s')
        - 2 * (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p,
            T0 p d ν h x * PhiF p d ν h x s)
        + (∑ h, ∑ x, ∑ s : ZMod p, ∑ s' : ZMod p, T0 p d ν h x) := by
    rw [hLexp]
    have e : P ^ 2 * ((∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x) ^ 2)
          - 2 * (∑ h, ∑ x, T0 p d ν h x * Aavg p d ν h x)
          + (∑ h, ∑ x, T0 p d ν h x))
        = P ^ 2 * (∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x) ^ 2)
          - 2 * (P ^ 2 * (∑ h, ∑ x, T0 p d ν h x * Aavg p d ν h x))
          + P ^ 2 * (∑ h, ∑ x, T0 p d ν h x) := by ring
    rw [e, ← h2e, ← h1e, ← h0]
  -- assemble the bound
  have hNfact : P ^ (d + 3) = P ^ 2 * (p : ℝ) ^ (d + 1) := by
    rw [hP, show d + 3 = 2 + (d + 1) from by omega, pow_add]
  have hP2pos : 0 < P ^ 2 := by positivity
  have hfinal : P ^ 2 * (∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x - 1) ^ 2)
      ≤ P ^ 2 * (4 * ε * (p : ℝ) ^ (d + 1)) := by
    rw [hP2L]
    have h4 : (1 + ε) * P ^ (d + 3) - 2 * ((1 - ε) * P ^ (d + 3)) + (1 + ε) * P ^ (d + 3)
        = 4 * ε * (P ^ 2 * (p : ℝ) ^ (d + 1)) := by
      rw [hNfact]; ring
    linarith [key0, key1, key2, h4]
  have hfin := (mul_le_mul_iff_of_pos_left hP2pos).mp hfinal
  have hgoal : (∑ h : Fin d → ZMod p, ∑ x : ZMod p,
        (∏ ω : Fin d → Bool, ν (x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j))
        * ((((p : ℝ))⁻¹ * ∑ s : ZMod p,
            ∏ i : Fin d, ∏ ω ∈ (Finset.univ.filter (fun ω : Fin d → Bool => ω i = false)),
              ν (x + ∑ j : Fin d, (if ω j then (1 : ZMod p) else 0) * h j
                - (((1 + i.val : ℕ)) : ZMod p)
                  * (s + ∑ j : Fin d,
                      (if ω j then (1 : ZMod p) else 0) * h j / ((j : ZMod p) + 1)))
            - 1)^2))
      = (∑ h, ∑ x, T0 p d ν h x * (Aavg p d ν h x - 1) ^ 2) := by
    simp only [T0, Aavg, PhiF]
  rw [hgoal]
  exact hfin

end Commons.Combinatorics.Transference
