import Mathlib
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.Combinatorics.MvPolynomial.union_shift_mconvex

open Finsupp MvPolynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

lemma ds_coeff_X_mul_shift {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (i : σ) (m : σ →₀ ℕ) (hm : m i ≥ 1) :
    MvPolynomial.coeff m (MvPolynomial.X i * p) =
      MvPolynomial.coeff (m - Finsupp.single i 1) p := by
  have hsplit : Finsupp.single i 1 + (m - Finsupp.single i 1) = m := by
    ext k
    by_cases hki : k = i
    · subst i
      simp [Finsupp.add_apply]
      omega
    · simp [Finsupp.add_apply, hki]
  calc
    MvPolynomial.coeff m (MvPolynomial.X i * p)
        = MvPolynomial.coeff (Finsupp.single i 1 + (m - Finsupp.single i 1)) (MvPolynomial.X i * p) := by
            rw [hsplit]
    _ = MvPolynomial.coeff (m - Finsupp.single i 1) p := by
            rw [MvPolynomial.coeff_X_mul]

lemma ds_coeff_X_mul_zero {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (i : σ) (m : σ →₀ ℕ) (hm : m i = 0) :
    MvPolynomial.coeff m (MvPolynomial.X i * p) = 0 := by
  classical
  by_contra hc
  have hmem : m ∈ (MvPolynomial.X i * p).support := MvPolynomial.mem_support_iff.mpr hc
  have hcomm : MvPolynomial.X i * p = p * MvPolynomial.X i := by ring
  rw [hcomm] at hmem
  rw [MvPolynomial.support_mul_X] at hmem
  rcases Finset.mem_map.mp hmem with ⟨a, ha, hmap⟩
  have hm' : a + Finsupp.single i 1 = m := hmap
  have hval : a i + 1 = m i := by
    simpa [Finsupp.add_apply] using congrArg (fun x : σ →₀ ℕ => x i) hm'
  omega

lemma ds_coeff_deform_term {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (i j : σ) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.X i * MvPolynomial.pderiv j p) =
      (if m i ≥ 1 then
         MvPolynomial.coeff ((m - Finsupp.single i 1) + Finsupp.single j 1) p *
           (((m - Finsupp.single i 1 : σ →₀ ℕ) j) + 1)
       else 0) := by
  classical
  by_cases hm : m i ≥ 1
  · rw [if_pos hm]
    have hshift : MvPolynomial.coeff m (MvPolynomial.X i * MvPolynomial.pderiv j p) =
        MvPolynomial.coeff (m - Finsupp.single i 1) (MvPolynomial.pderiv j p) :=
      ds_coeff_X_mul_shift (MvPolynomial.pderiv j p) i m hm
    rw [hshift]
    rw [MvPolynomial.coeff_pderiv]
  · rw [if_neg hm]
    have hm0 : m i = 0 := by omega
    rw [ds_coeff_X_mul_zero (MvPolynomial.pderiv j p) i m hm0]

lemma ds_coeff_deform_term_ne_zero_iff {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (i j : σ) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.X i * MvPolynomial.pderiv j p) ≠ 0 ↔
      m i ≥ 1 ∧ MvPolynomial.coeff ((m - Finsupp.single i 1) + Finsupp.single j 1) p ≠ 0 := by
  classical
  rw [ds_coeff_deform_term]
  by_cases hm : m i ≥ 1
  · rw [if_pos hm]
    constructor
    · intro hne
      constructor
      · exact hm
      · intro hco
        apply hne
        rw [hco]
        simp
    · intro h
      intro hz
      rcases h with ⟨_, hco⟩
      have hc : (((m - Finsupp.single i 1 : σ →₀ ℕ) j) + 1 : ℝ) ≠ 0 := by
        let m' : σ →₀ ℕ := m - Finsupp.single i 1
        exact_mod_cast (Nat.succ_ne_zero (m' j))
      exact hco ((mul_eq_zero.mp hz).resolve_right hc)
  · rw [if_neg hm]
    constructor
    · intro hne
      exact False.elim (hne rfl)
    · intro h
      exact False.elim (hm h.1)

lemma ds_support_X_mul_pderiv {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (i j : σ) :
    ((MvPolynomial.X i * MvPolynomial.pderiv j p).support : Set (σ →₀ ℕ)) =
      {m : σ →₀ ℕ | m i ≥ 1 ∧ m - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support} := by
  classical
  ext m
  simp only [Finset.mem_coe]
  rw [MvPolynomial.mem_support_iff]
  rw [ds_coeff_deform_term_ne_zero_iff p i j m]
  constructor
  · rintro ⟨hmi, hco⟩
    exact ⟨hmi, MvPolynomial.mem_support_iff.mpr hco⟩
  · rintro ⟨hmi, hco⟩
    exact ⟨hmi, MvPolynomial.mem_support_iff.mp hco⟩

lemma ds_mem_support_add {σ : Type*} [DecidableEq σ] (p q : MvPolynomial σ ℝ)
    (hnnp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) (hnnq : ∀ m : σ →₀ ℕ, 0 ≤ q.coeff m) (m : σ →₀ ℕ) :
    m ∈ (p + q).support ↔ m ∈ p.support ∨ m ∈ q.support := by
  classical
  rw [MvPolynomial.mem_support_iff]
  rw [MvPolynomial.coeff_add]
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
  constructor
  · intro hne
    by_contra h
    push_neg at h
    rcases h with ⟨hp, hq⟩
    apply hne
    rw [hp, hq]
    ring
  · intro hpq
    rcases hpq with hp | hq
    · intro hz
      exact hp (by nlinarith [hnnp m, hnnq m, hz])
    · intro hz
      exact hq (by nlinarith [hnnp m, hnnq m, hz])

lemma ds_support_add_of_nonneg {σ : Type*} [DecidableEq σ] (p q : MvPolynomial σ ℝ)
    (hnnp : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) (hnnq : ∀ m : σ →₀ ℕ, 0 ≤ q.coeff m) :
    (p + q).support = p.support ∪ q.support := by
  classical
  ext m
  rw [ds_mem_support_add p q hnnp hnnq m]
  simp [Finset.mem_union]

lemma ds_support_C_mul_of_ne_zero {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (a : ℝ) (ha : a ≠ 0) :
    ((MvPolynomial.C a) * p).support = p.support := by
  classical
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff]
  rw [MvPolynomial.coeff_C_mul]
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro h
    exact mul_ne_zero ha h

lemma ds_support_deform {σ : Type*} [DecidableEq σ] (p : MvPolynomial σ ℝ)
    (θ : ℝ) (hθ : 0 < θ) (hnn : ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m) (i j : σ) :
    ((p + (MvPolynomial.C θ) * MvPolynomial.X i * MvPolynomial.pderiv j p).support :
        Set (σ →₀ ℕ)) =
      (p.support : Set (σ →₀ ℕ)) ∪
        {m : σ →₀ ℕ | m i ≥ 1 ∧ m - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support} := by
  classical
  let q : MvPolynomial σ ℝ := (MvPolynomial.C θ) * MvPolynomial.X i * MvPolynomial.pderiv j p
  have hnnq : ∀ m : σ →₀ ℕ, 0 ≤ q.coeff m := by
    intro m
    dsimp [q]
    rw [mul_assoc]
    rw [MvPolynomial.coeff_C_mul]
    rw [ds_coeff_deform_term]
    by_cases hm : m i ≥ 1
    · rw [if_pos hm]
      have hco : 0 ≤ MvPolynomial.coeff ((m - Finsupp.single i 1) + Finsupp.single j 1) p :=
        hnn ((m - Finsupp.single i 1) + Finsupp.single j 1)
      have hc : (0 : ℝ) ≤ (((m - Finsupp.single i 1 : σ →₀ ℕ) j) + 1 : ℕ) := by
        let m' : σ →₀ ℕ := m - Finsupp.single i 1
        exact_mod_cast (Nat.zero_le (m' j + 1))
      positivity
    · rw [if_neg hm]
      simp
  have h1 : (p + q).support = p.support ∪ q.support := ds_support_add_of_nonneg p q hnn hnnq
  have h2 : q.support = (MvPolynomial.X i * MvPolynomial.pderiv j p).support := by
    dsimp [q]
    rw [mul_assoc]
    exact ds_support_C_mul_of_ne_zero (MvPolynomial.X i * MvPolynomial.pderiv j p) θ (ne_of_gt hθ)
  have hfin : (p + q).support = p.support ∪ (MvPolynomial.X i * MvPolynomial.pderiv j p).support := by
    rw [h1, h2]
  rw [hfin]
  ext m
  simp only [Finset.mem_coe, Finset.mem_union, Set.mem_union]
  have hXi : m ∈ (MvPolynomial.X i * MvPolynomial.pderiv j p).support ↔
      (m i ≥ 1 ∧ m - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support) := by
    rw [← Finset.mem_coe]
    rw [ds_support_X_mul_pderiv p i j]
    rfl
  rw [hXi]
  simp [Set.mem_setOf_eq]


/-- Brändén–Huh, Proposition 2.12 (deform), "Lemma support": the operation
`(1 + θ·X_i·∂_j)` preserves M-convexity of the support of a homogeneous polynomial
with nonnegative coefficients, for every `θ ≥ 0`. -/
theorem deform_support_MConvex (n d : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (i j : Fin n)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
    (hM : Commons.LorentzianPolynomials.IsMConvex (p.support : Set (Fin n →₀ ℕ)))
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    Commons.LorentzianPolynomials.IsMConvex
      (((p + MvPolynomial.C θ * MvPolynomial.X i * MvPolynomial.pderiv j p).support) :
        Set (Fin n →₀ ℕ)) := by
  by_cases hθ0 : θ = 0
  · have hq : p + (MvPolynomial.C θ) * MvPolynomial.X i * MvPolynomial.pderiv j p = p := by
      rw [hθ0]
      simp
    rw [hq]
    exact hM
  · have hθpos : 0 < θ := lt_of_le_of_ne hθ (by
      intro h0θ
      exact hθ0 h0θ.symm)
    rw [ds_support_deform p θ hθpos hnn i j]
    exact Commons.Combinatorics.MvPolynomial.union_shift_mconvex
      (A := (p.support : Set (Fin n →₀ ℕ))) (i := i) (j := j) hM

end Commons.LorentzianPolynomials
