import Mathlib
import Submission.Commons.Algebra.MvPolynomial.lap_zterm

open scoped BigOperators
open MvPolynomial

noncomputable section

namespace Commons.Algebra.MvPolynomial

variable {n : ℕ} [NeZero n]

/-- Laplacian -/
abbrev zh_lap (φ : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i φ)

@[simp] lemma zh_lap_add (φ ψ : MvPolynomial (Fin n) ℝ) :
    zh_lap (φ + ψ) = zh_lap φ + zh_lap ψ := by
  simp only [zh_lap, map_add]
  exact Finset.sum_add_distrib

@[simp] lemma zh_lap_smul (a : ℝ) (φ : MvPolynomial (Fin n) ℝ) :
    zh_lap (a • φ) = a • zh_lap φ := by
  simp [zh_lap, Finset.smul_sum]

@[simp] lemma zh_lap_zero : zh_lap (0 : MvPolynomial (Fin n) ℝ) = 0 := by
  simp [zh_lap]


/-- Radial sum of squares on coordinates other than 0 -/
abbrev zh_Sq : MvPolynomial (Fin n) ℝ :=
  ∑ i : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ)^2

/-- exponent at coordinate i -/
def zh_E (i : Fin n) (a : ℕ) : Fin n →₀ ℕ := Finsupp.single i a

section Coeff

/-- coordinate 1 (needs n ≥ 2) -/
def zh_e1 (hn2 : 2 ≤ n) : Fin n := ⟨1, by omega⟩

lemma zh_e1_ne_zero (hn2 : 2 ≤ n) : zh_e1 hn2 ≠ (0 : Fin n) := by
  intro h
  have hh := congrArg (fun i : Fin n => (i : ℕ)) h
  dsimp [zh_e1] at hh
  norm_num at hh

/-- distributivity of coeff over the subtype sum -/
lemma zh_coeff_sum_subtype (d : Fin n →₀ ℕ)
    (g : {i : Fin n // i ≠ 0} → MvPolynomial (Fin n) ℝ) :
    MvPolynomial.coeff d (∑ i : {i : Fin n // i ≠ 0}, g i) =
      ∑ i : {i : Fin n // i ≠ 0}, MvPolynomial.coeff d (g i) := by
  exact map_sum (MvPolynomial.coeffAddMonoidHom d) g Finset.univ

/-- S^w monomials never involve coordinate 0. -/
lemma zh_Sq_pow_avoid0 (w : ℕ) {d : Fin n →₀ ℕ} (hd : 0 < d (0 : Fin n)) :
    MvPolynomial.coeff d (zh_Sq ^ w) = 0 := by
  classical
  induction w generalizing d with
  | zero =>
      rw [pow_zero]
      rw [MvPolynomial.coeff_one]
      by_cases h0 : (0 : Fin n →₀ ℕ) = d
      · exfalso
        rw [← h0] at hd
        simp at hd
      · simp [h0]
  | succ w ih =>
      rw [pow_succ]
      change MvPolynomial.coeff d
        (zh_Sq ^ w * (∑ i : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ)^2)) = 0
      rw [Finset.mul_sum]
      rw [zh_coeff_sum_subtype d (fun i : {i : Fin n // i ≠ 0} => zh_Sq ^ w * (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ)^2)]
      apply Finset.sum_eq_zero
      intro i hi
      let j : Fin n := i.1
      have hj : j ≠ (0 : Fin n) := i.2
      rw [MvPolynomial.X_pow_eq_monomial (e := 2) (n := j)]
      rw [MvPolynomial.coeff_mul_monomial' (m := d) (s := Finsupp.single j 2) (r := 1)]
      by_cases hle : Finsupp.single j 2 ≤ d
      · rw [if_pos hle]
        have hs0 : (Finsupp.single j 2) (0 : Fin n) = 0 := by
          simp [hj]
        have hd' : 0 < ((d - Finsupp.single j 2 : Fin n →₀ ℕ)) (0 : Fin n) := by
          rw [Finsupp.tsub_apply, hs0]
          simpa using hd
        rw [ih hd']
        simp
      · rw [if_neg hle]

/-- Coefficient of the pure monomial `X zh_e1 ^ (2ℓ)` in `zh_Sq^w` is 1 exactly when `w = ℓ`. -/
lemma zh_coeff_E1_Sq_pow (hn2 : 2 ≤ n) (w ℓ : ℕ) :
    MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ)) (zh_Sq ^ w) =
      (if w = ℓ then (1 : ℝ) else 0) := by
  classical
  induction w generalizing ℓ with
  | zero =>
      rw [pow_zero]
      rw [MvPolynomial.coeff_one]
      by_cases hℓ : ℓ = 0
      · subst hℓ
        simp [zh_E]
      · have hE : (zh_E (zh_e1 hn2) (2*ℓ) = 0) → False := by
          intro h
          have hh := congrArg (fun e : Fin n →₀ ℕ => e (zh_e1 hn2)) h
          simp [zh_E] at hh
          omega
        have h0 : ¬ (0 : Fin n →₀ ℕ) = zh_E (zh_e1 hn2) (2*ℓ) := by
          intro hz; apply hE; exact hz.symm
        have h0' : zh_E (zh_e1 hn2) (2*ℓ) ≠ 0 := fun hz => hE hz
        have h0ℓ : ¬ (0 : ℕ) = ℓ := fun hz => hℓ hz.symm
        simp [h0, h0', h0ℓ]
  | succ w ih =>
      rw [pow_succ]
      change MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ))
        (zh_Sq ^ w * (∑ i : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ)^2)) =
          (if w + 1 = ℓ then (1 : ℝ) else 0)
      rw [Finset.mul_sum]
      rw [zh_coeff_sum_subtype (zh_E (zh_e1 hn2) (2*ℓ)) (fun i : {i : Fin n // i ≠ 0} => zh_Sq ^ w * (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ)^2)]
      let i1 : {i : Fin n // i ≠ 0} := ⟨zh_e1 hn2, zh_e1_ne_zero hn2⟩
      rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ _)]
      · rw [MvPolynomial.X_pow_eq_monomial (e := 2) (n := zh_e1 hn2)]
        rw [MvPolynomial.coeff_mul_monomial' (m := zh_E (zh_e1 hn2) (2*ℓ)) (s := Finsupp.single (zh_e1 hn2) 2) (r := 1)]
        by_cases hℓ0 : ℓ = 0
        · subst hℓ0
          have hnle : ¬ Finsupp.single (zh_e1 hn2) 2 ≤ (0 : Fin n →₀ ℕ) := by
            intro hle
            have hh := hle (zh_e1 hn2)
            simp [zh_E] at hh
          simp [zh_E, hnle]
        · have hle2 : Finsupp.single (zh_e1 hn2) 2 ≤ zh_E (zh_e1 hn2) (2*ℓ) := by
            intro j
            by_cases hj : j = zh_e1 hn2
            · subst j
              simp [zh_E]
              omega
            · simp [zh_E, hj]
          rw [if_pos hle2]
          have hsub : ((zh_E (zh_e1 hn2) (2*ℓ) - Finsupp.single (zh_e1 hn2) 2 : Fin n →₀ ℕ))
              = zh_E (zh_e1 hn2) (2*ℓ - 2) := by
            ext j
            by_cases hj : j = zh_e1 hn2
            · subst j
              simp [zh_E]
            · simp [zh_E, hj]
          rw [hsub]
          have h2 : 2*ℓ - 2 = 2*(ℓ - 1) := by omega
          rw [h2]
          rw [ih (ℓ - 1)]
          have h' : w + 1 = ℓ ↔ w = ℓ - 1 := by omega
          by_cases hw : w + 1 = ℓ
          · have hw' : w = ℓ - 1 := (h'.mp hw)
            rw [if_pos hw, if_pos hw']
            simp
          · have hw' : w ≠ ℓ - 1 := fun hx => hw (h'.mpr hx)
            rw [if_neg hw, if_neg hw']
            simp
      · intro i hi hine
        rw [MvPolynomial.X_pow_eq_monomial (e := 2) (n := (i : Fin n))]
        rw [MvPolynomial.coeff_mul_monomial' (m := zh_E (zh_e1 hn2) (2*ℓ)) (s := Finsupp.single (i : Fin n) 2) (r := 1)]
        have hc : i.1 ≠ zh_e1 hn2 := by
          intro hEq
          apply hine
          exact Subtype.ext hEq
        have hnle : ¬ Finsupp.single (i : Fin n) 2 ≤ zh_E (zh_e1 hn2) (2*ℓ) := by
          intro hle
          have hh := hle (i : Fin n)
          simp [zh_E, hc] at hh
        rw [if_neg hnle]

end Coeff



section Laplace

/-- coefficient of a monomial with X0-part b in `(X0 ^ c) * zh_Sq ^ w` -/
lemma zh_coeff_X0_mul_Sq (hn2 : 2 ≤ n) (c w : ℕ) (ℓ b : ℕ) :
    MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) b)
      ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ)^c * zh_Sq ^ w) =
      if b = c then MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ)) (zh_Sq ^ w) else 0 := by
  classical
  have he0ne1 : (0 : Fin n) ≠ zh_e1 hn2 := by
    intro h
    have hh := congrArg (fun i : Fin n => (i : ℕ)) h
    dsimp [zh_e1] at hh
    norm_num at hh
  rw [MvPolynomial.X_pow_eq_monomial (e := c) (n := (0 : Fin n))]
  rw [MvPolynomial.coeff_monomial_mul' (m := zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) b)
    (s := Finsupp.single (0 : Fin n) c) (r := 1)]
  have hle_iff : (Finsupp.single (0 : Fin n) c ≤ zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) b) ↔ c ≤ b := by
    constructor
    · intro h
      have hh := h (0 : Fin n)
      simp [zh_E, he0ne1] at hh
      exact hh
    · intro h j
      by_cases hj : j = (0 : Fin n)
      · subst j
        simp [zh_E, he0ne1, h]
      · have h1 : (Finsupp.single (0 : Fin n) c) j = 0 := by
          simp [hj]
        simp [h1]
  have hsub (hcb : c ≤ b) :
      ((zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) b) - Finsupp.single (0 : Fin n) c : Fin n →₀ ℕ)
        = zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) (b - c) := by
    ext j
    by_cases hj : j = (0 : Fin n)
    · subst j
      simp [zh_E, he0ne1, Finsupp.tsub_apply]
    · have h1 : (Finsupp.single (0 : Fin n) c) j = 0 := by simp [hj]
      have h2 : (Finsupp.single (0 : Fin n) b) j = 0 := by simp [hj]
      simp [zh_E, Finsupp.tsub_apply, h1, h2]
  by_cases hb : b = c
  · subst b
    have hle : Finsupp.single (0 : Fin n) c ≤ zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) c :=
      (hle_iff.mpr (Nat.le_refl c))
    rw [if_pos hle]
    rw [hsub (Nat.le_refl c)]
    simp [zh_E]
  · rw [if_neg hb]
    by_cases hle : Finsupp.single (0 : Fin n) c ≤ zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) b
    · rw [if_pos hle]
      have hcb : c ≤ b := hle_iff.mp hle
      rw [hsub hcb]
      rw [one_mul]
      apply zh_Sq_pow_avoid0 w
      have hpos : 0 < b - c := by omega
      have hb0 : (zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) (b - c)) (0 : Fin n) = b - c := by
        simp [zh_E, he0ne1]
      rw [hb0]
      exact hpos
    · rw [if_neg hle]

end Laplace


section Core

/-- zonal term: X0^(k-2j) * zh_Sq^j -/
def zh_zterm (k j : ℕ) : MvPolynomial (Fin n) ℝ :=
  (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2*j) * zh_Sq ^ j


/-- laplacian of a zonal basis term `X0^a * Sq^j` (def-form of the delegated identity) -/
lemma zh_lap_zterm (a j : ℕ) :
    zh_lap ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ)^a * zh_Sq ^ j) =
      (MvPolynomial.C (((a * (a - 1)) : ℕ) : ℝ)) *
          (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (a - 2) * zh_Sq ^ j +
      (MvPolynomial.C (((2 * j * (n + 2*j - 3)) : ℕ) : ℝ)) *
          (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ a * zh_Sq ^ (j - 1) := by
  unfold zh_lap zh_Sq
  rw [lap_zterm]

/-- zh_lap of a Finset sum -/
lemma zh_lap_finset_sum {ι : Type} (s : Finset ι) (g : ι → MvPolynomial (Fin n) ℝ) :
    zh_lap (∑ i ∈ s, g i) = ∑ i ∈ s, zh_lap (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, zh_lap_add, ih, Finset.sum_insert has]

/-- value lemma 1: coefficient of X0^((k-2j)-2) zh_Sq^j at monomial zh_E zh_e1 2ℓ + zh_E e0 (k-2ℓ-2) -/
lemma zh_val1_eq (hn2 : 2 ≤ n) (k ℓ j : ℕ) :
    MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) (k - 2*ℓ - 2))
      ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ ((k - 2*j) - 2) * zh_Sq ^ j) =
      (if j = ℓ then (1 : ℝ) else 0) := by
  classical
  rw [zh_coeff_X0_mul_Sq hn2 ((k - 2*j) - 2) j ℓ (k - 2*ℓ - 2)]
  rw [zh_coeff_E1_Sq_pow hn2 j ℓ]
  by_cases hj : j = ℓ
  · subst j
    have hcond : k - 2*ℓ - 2 = (k - 2*ℓ) - 2 := by omega
    rw [if_pos hcond]
  · by_cases hcond : k - 2*ℓ - 2 = (k - 2*j) - 2
    · rw [if_pos hcond]
    · rw [if_neg hcond]
      simp [hj]

/-- value lemma 2: coefficient of X0^(k-2j) zh_Sq^(j-1) at monomial zh_E zh_e1 2ℓ + zh_E e0 (k-2ℓ-2) -/
lemma zh_val2_eq (hn2 : 2 ≤ n) (k ℓ j : ℕ) (hj1 : 1 ≤ j) :
    MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) (k - 2*ℓ - 2))
      ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2*j) * zh_Sq ^ (j - 1)) =
      (if j = ℓ + 1 then (1 : ℝ) else 0) := by
  classical
  rw [zh_coeff_X0_mul_Sq hn2 (k - 2*j) (j - 1) ℓ (k - 2*ℓ - 2)]
  rw [zh_coeff_E1_Sq_pow hn2 (j - 1) ℓ]
  by_cases hj : j = ℓ + 1
  · subst j
    have hcond : k - 2*ℓ - 2 = k - 2*(ℓ + 1) := by omega
    rw [if_pos hcond]
    have hjp : (ℓ + 1) - 1 = ℓ := by omega
    rw [hjp]
    simp
  · have hjl : j - 1 ≠ ℓ := by omega
    by_cases hcond : k - 2*ℓ - 2 = k - 2*j
    · rw [if_pos hcond]
      simp [hjl, hj]
    · rw [if_neg hcond]
      simp [hj]



/-- α_j : first laplacian scalar -/
def zh_alpha (k j : ℕ) : ℝ := ↑((k - 2*j) * (k - 2*j - 1))

/-- β_j : second laplacian scalar -/
def zh_beta (n k j : ℕ) : ℝ := ↑(2*j * (n + 2*j - 3))

/-- coefficient of the laplacian of one zonal term -/
lemma zh_coeff_lap_zterm (hn2 : 2 ≤ n) (k j ℓ : ℕ) :
    MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) (k - 2*ℓ - 2))
      (zh_lap (zh_zterm k j)) =
      zh_alpha k j * (if j = ℓ then (1:ℝ) else 0) +
      zh_beta n k j * (if j = ℓ + 1 then (1:ℝ) else 0) := by
  classical
  let b := k - 2*ℓ - 2
  let m : Fin n →₀ ℕ := zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) b
  dsimp [zh_zterm]
  rw [zh_lap_zterm (k - 2*j) j]
  -- coefficient of sum
  rw [MvPolynomial.coeff_add]
  -- first summand
  have h1 : MvPolynomial.coeff m
      (MvPolynomial.C ((((k - 2*j) * ((k - 2*j) - 1)) : ℕ) : ℝ) *
          (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ ((k - 2*j) - 2) * zh_Sq ^ j) =
      zh_alpha k j * MvPolynomial.coeff m
          ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ ((k - 2*j) - 2) * zh_Sq ^ j) := by
    rw [mul_assoc]
    rw [MvPolynomial.coeff_C_mul]
    rfl
  -- second summand
  have h2 : MvPolynomial.coeff m
      (MvPolynomial.C (((2*j * (n + 2*j - 3)) : ℕ) : ℝ) *
          (MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2*j) * zh_Sq ^ (j - 1)) =
      zh_beta n k j * MvPolynomial.coeff m
          ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2*j) * zh_Sq ^ (j - 1)) := by
    rw [mul_assoc]
    rw [MvPolynomial.coeff_C_mul]
    rfl
  rw [h1, h2]
  rw [zh_val1_eq hn2 k ℓ j]
  by_cases hj0 : j = 0
  · subst j
    have hb : zh_beta n k 0 = 0 := by simp [zh_beta]
    have hnot : ¬ (0 = ℓ + 1) := by omega
    rw [hb, if_neg hnot]
    simp
  · have hjl : 1 ≤ j := by omega
    rw [zh_val2_eq hn2 k ℓ j hjl]


/-- coefficient identity for the laplacian of the whole zonal sum -/
lemma zh_coeff_lap_zonal_sum (hn2 : 2 ≤ n) (k : ℕ) (c : ℕ → ℝ) (ℓ : ℕ)
    (hℓ : ℓ + 1 ≤ k / 2) :
    MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) (k - 2*ℓ - 2))
      (zh_lap (∑ j ∈ Finset.range (k/2 + 1), c j • zh_zterm k j)) =
      c ℓ * zh_alpha k ℓ + c (ℓ+1) * zh_beta n k (ℓ+1) := by
  classical
  let b := k - 2*ℓ - 2
  let m : Fin n →₀ ℕ := zh_E (zh_e1 hn2) (2*ℓ) + zh_E (0 : Fin n) b
  have hmemℓ : ℓ ∈ Finset.range (k/2 + 1) := by
    rw [Finset.mem_range]
    omega
  have hmemℓ1 : ℓ + 1 ∈ Finset.range (k/2 + 1) := by
    rw [Finset.mem_range]
    omega
  have hlin : MvPolynomial.coeff m (zh_lap (∑ j ∈ Finset.range (k/2+1), c j • zh_zterm k j))
      = ∑ j ∈ Finset.range (k/2+1), c j * MvPolynomial.coeff m (zh_lap (zh_zterm k j)) := by
    rw [show zh_lap (∑ j ∈ Finset.range (k/2+1), c j • zh_zterm k j) =
            (∑ j ∈ Finset.range (k/2+1), zh_lap (c j • zh_zterm k j)) by
            exact zh_lap_finset_sum (Finset.range (k/2+1)) (fun j => c j • zh_zterm k j)]
    rw [MvPolynomial.coeff_sum (Finset.range (k/2+1)) (fun j => zh_lap (c j • zh_zterm k j)) m]
    apply Finset.sum_congr rfl
    intro j hj
    rw [zh_lap_smul]
    rw [MvPolynomial.coeff_smul]
    simp
  rw [hlin]
  trans ∑ j ∈ Finset.range (k/2+1),
      c j * (zh_alpha k j * (if j = ℓ then (1:ℝ) else 0) + zh_beta n k j * (if j = ℓ + 1 then (1:ℝ) else 0))
  · apply Finset.sum_congr rfl
    intro j hj
    rw [zh_coeff_lap_zterm hn2 k j ℓ]
  · have hsplit : (∑ j ∈ Finset.range (k/2+1),
        c j * (zh_alpha k j * (if j = ℓ then (1:ℝ) else 0) + zh_beta n k j * (if j = ℓ + 1 then (1:ℝ) else 0)))
        = (∑ j ∈ Finset.range (k/2+1), c j * zh_alpha k j * (if j = ℓ then (1:ℝ) else 0))
        + (∑ j ∈ Finset.range (k/2+1), c j * zh_beta n k j * (if j = ℓ + 1 then (1:ℝ) else 0)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsplit]
    have hsumA : (∑ j ∈ Finset.range (k/2+1), c j * zh_alpha k j * (if j = ℓ then (1:ℝ) else 0)) =
        c ℓ * zh_alpha k ℓ := by
      calc
        (∑ j ∈ Finset.range (k/2+1), c j * zh_alpha k j * (if j = ℓ then (1:ℝ) else 0))
            = c ℓ * zh_alpha k ℓ * (if ℓ = ℓ then (1:ℝ) else 0) := by
              exact Finset.sum_eq_single_of_mem (s := Finset.range (k/2+1))
                (f := fun j => c j * zh_alpha k j * (if j = ℓ then (1:ℝ) else 0))
                ℓ hmemℓ (by
                  intro j hj hne
                  simp [hne])
        _ = c ℓ * zh_alpha k ℓ := by simp
    have hsumB : (∑ j ∈ Finset.range (k/2+1), c j * zh_beta n k j * (if j = ℓ + 1 then (1:ℝ) else 0)) =
        c (ℓ+1) * zh_beta n k (ℓ+1) := by
      calc
        (∑ j ∈ Finset.range (k/2+1), c j * zh_beta n k j * (if j = ℓ + 1 then (1:ℝ) else 0))
            = c (ℓ+1) * zh_beta n k (ℓ+1) * (if ℓ + 1 = ℓ + 1 then (1:ℝ) else 0) := by
              exact Finset.sum_eq_single_of_mem (s := Finset.range (k/2+1))
                (f := fun j => c j * zh_beta n k j * (if j = ℓ + 1 then (1:ℝ) else 0))
                (ℓ+1) hmemℓ1 (by
                  intro j hj hne
                  simp [hne])
        _ = c (ℓ+1) * zh_beta n k (ℓ+1) := by simp
    rw [hsumA, hsumB]


/-- if the first coefficient of a harmonic zonal sum vanishes, all do -/
lemma zh_zonal_all_zero (hn2 : 2 ≤ n) (k : ℕ) (c : ℕ → ℝ)
    (hlap : zh_lap (∑ j ∈ Finset.range (k/2+1), (c j • zh_zterm k j : MvPolynomial (Fin n) ℝ)) = 0)
    (hc0 : c 0 = 0) :
    ∀ j, j < k/2 + 1 → c j = 0 := by
  classical
  intro j
  induction j with
  | zero =>
      intro _
      exact hc0
  | succ j ih =>
      intro hsucc
      have hcj : c j = 0 := ih (by omega)
      have hℓ : j + 1 ≤ k / 2 := by omega
      have hri := zh_coeff_lap_zonal_sum hn2 k c j hℓ
      have hl0 : MvPolynomial.coeff (zh_E (zh_e1 hn2) (2*j) + zh_E (0 : Fin n) (k - 2*j - 2))
          (zh_lap (∑ j ∈ Finset.range (k/2+1), c j • zh_zterm k j)) = 0 := by
        rw [hlap]
        simp
      have hzero : 0 = c j * zh_alpha k j + c (j+1) * zh_beta n k (j+1) := by
        rw [← hri]
        exact hl0.symm
      have hz2 : 0 = c (j+1) * zh_beta n k (j+1) := by
        rw [hcj] at hzero
        simpa using hzero
      have hb : zh_beta n k (j+1) ≠ 0 := by
        have hnz1 : (2*(j+1) : ℕ) ≠ 0 := by omega
        have hnz2 : (n + 2*(j+1) - 3 : ℕ) ≠ 0 := by omega
        have hnz : (2*(j+1) * (n + 2*(j+1) - 3) : ℕ) ≠ 0 := mul_ne_zero hnz1 hnz2
        dsimp [zh_beta]
        exact_mod_cast hnz
      have hc' : c (j+1) = 0 := by
        exact (mul_eq_zero.mp (by simpa using hz2)).resolve_right hb
      exact hc'

end Core



section Main

/-- extension of a Fin-indexed family to naturals -/
def zh_extc (r : ℕ) (c : Fin (r+1) → ℝ) : ℕ → ℝ :=
  fun j => if h : j < r + 1 then c ⟨j, h⟩ else 0

/-- rewrite a Fin-indexed zonal sum as a range sum -/
lemma zh_fin_sum_range {n : ℕ} [NeZero n] (k : ℕ) (c : Fin (k/2 + 1) → ℝ) :
    (∑ j : Fin (k/2 + 1), (c j • zh_zterm k (j : ℕ) : MvPolynomial (Fin n) ℝ)) =
      ∑ j ∈ Finset.range (k/2 + 1), ((zh_extc (k/2) c j) • zh_zterm k j : MvPolynomial (Fin n) ℝ) := by
  classical
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < k/2 + 1 := Finset.mem_range.mp hj
  rw [dif_pos hj']
  dsimp [zh_extc]
  rw [dif_pos hj']

theorem zonal_harmonic_pair_linDep
    {n : ℕ} {k : ℕ} [NeZero n] (hn2 : 2 ≤ n)
    (P Q : MvPolynomial (Fin n) ℝ)
    (hP : ∃ c : Fin (k / 2 + 1) → ℝ,
      P = ∑ j : Fin (k / 2 + 1),
        (c j) • ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2 * (j : ℕ)) *
          ((∑ i : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ) ^ 2) ^ (j : ℕ))))
    (hQ : ∃ c : Fin (k / 2 + 1) → ℝ,
      Q = ∑ j : Fin (k / 2 + 1),
        (c j) • ((MvPolynomial.X (0 : Fin n) : MvPolynomial (Fin n) ℝ) ^ (k - 2 * (j : ℕ)) *
          ((∑ i : {i : Fin n // i ≠ 0}, (MvPolynomial.X (i : Fin n) : MvPolynomial (Fin n) ℝ) ^ 2) ^ (j : ℕ))))
    (hlapP : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i P)) = 0)
    (hlapQ : (∑ i : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)) = 0) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ a • P + b • Q = 0 := by
  classical
  rcases hP with ⟨c, hc⟩
  rcases hQ with ⟨d, hd⟩
  let r := k / 2
  let ce : ℕ → ℝ := zh_extc r c
  let de : ℕ → ℝ := zh_extc r d
  have hPr : P = ∑ j ∈ Finset.range (r+1), (ce j) • zh_zterm k j := by
    rw [hc]
    change (∑ j : Fin (k/2 + 1), (c j) • zh_zterm k (j : ℕ)) =
      ∑ j ∈ Finset.range (r+1), (ce j) • zh_zterm k j
    simpa [ce, r] using (zh_fin_sum_range k c)
  have hQr : Q = ∑ j ∈ Finset.range (r+1), (de j) • zh_zterm k j := by
    rw [hd]
    change (∑ j : Fin (k/2 + 1), (d j) • zh_zterm k (j : ℕ)) =
      ∑ j ∈ Finset.range (r+1), (de j) • zh_zterm k j
    simpa [de, r] using (zh_fin_sum_range k d)
  let c0 : ℝ := ce 0
  let d0 : ℝ := de 0
  by_cases h0 : c0 = 0 ∧ d0 = 0
  · have hce0 : ce 0 = 0 := by simpa [c0] using h0.1
    have hlapS : zh_lap (∑ j ∈ Finset.range (r+1), (ce j • zh_zterm k j : MvPolynomial (Fin n) ℝ)) = 0 := by
      rw [← hPr]
      simpa [zh_lap] using hlapP
    have hall : ∀ j, j < r + 1 → ce j = 0 := zh_zonal_all_zero hn2 k ce hlapS hce0
    have hP0 : P = 0 := by
      rw [hPr]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hall j (Finset.mem_range.mp hj)]
      simp
    refine ⟨1, 0, ?_, ?_⟩
    · left; norm_num
    · simp [hP0]
  · let a : ℝ := d0
    let b : ℝ := - c0
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_cases hd0z : d0 = 0
      · right
        have hc0nz : c0 ≠ 0 := by
          intro hc0
          apply h0
          exact ⟨hc0, hd0z⟩
        dsimp [b]
        exact neg_ne_zero.mpr hc0nz
      · left
        dsimp [a]
        exact hd0z
    let e : ℕ → ℝ := fun j => a * ce j + b * de j
    have he0 : e 0 = 0 := by
      dsimp [e, a, b, c0, d0]
      ring
    have hRe : a • P + b • Q = ∑ j ∈ Finset.range (r+1), (e j) • zh_zterm k j := by
      rw [hPr, hQr]
      rw [Finset.smul_sum, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [e]
      rw [smul_smul, smul_smul]
      rw [← add_smul]
    have hlapR : zh_lap (a • P + b • Q) = 0 := by
      rw [zh_lap_add, zh_lap_smul, zh_lap_smul]
      simp [zh_lap, hlapP, hlapQ]
    have hlapS : zh_lap (∑ j ∈ Finset.range (r+1), ((e j) • zh_zterm k j : MvPolynomial (Fin n) ℝ)) = 0 := by
      rw [← hRe]
      exact hlapR
    have hall : ∀ j, j < r + 1 → e j = 0 := zh_zonal_all_zero hn2 k e hlapS he0
    have hR0 : a • P + b • Q = 0 := by
      rw [hRe]
      apply Finset.sum_eq_zero
      intro j hj
      rw [hall j (Finset.mem_range.mp hj)]
      simp
    refine ⟨a, b, hab, hR0⟩

end Main

end Commons.Algebra.MvPolynomial
