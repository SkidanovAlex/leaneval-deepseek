import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-! ## Infrastructure for the relation lattice of a family of logarithms

For a number field `K`, an embedding `φ : K →+* ℂ`, non-zero `α : Fin m → K` and complex
logarithms `ℓ i` of `φ (α i)`, we study

  `Γ = {y : Fin m → ℤ | ∏ᵢ αᵢ^{yᵢ} ∈ μ(K)}`.

Everything in this file is *qualitative*: `Γ` is closed under `+`, `-`, `•`, and
`Γ = {y | θ(y) ∈ 2πiℚ}` where `θ(y) = ∑ᵢ yᵢℓᵢ`, with `Γ = ℤ^m ∩ Vrel ℓ` for the `ℚ`-subspace
`Vrel ℓ = {v ∈ ℚ^m | ∑ᵢ vᵢℓᵢ ∈ 2πiℚ}`.  The rank bound `dim_ℚ Vrel ℓ ≤ 2` (from the
non-degeneracy hypotheses) lives in `Submission.Work.BW.relation_lattice_Vrel_finrank_le_two`,
which imports this module. -/

/-- The log-form `θ(y) = ∑ᵢ yᵢ ℓᵢ`. -/
noncomputable def thetaC {m : ℕ} (ℓ : Fin m → ℂ) (y : Fin m → ℤ) : ℂ :=
  ∑ i, (y i : ℂ) * ℓ i

/-- `MuRelC α y` says `∏ᵢ αᵢ^{yᵢ}` is a root of unity, i.e. `y` lies in `Γ`. -/
def MuRelC {K : Type*} [Field K] {m : ℕ} (α : Fin m → K) (y : Fin m → ℤ) : Prop :=
  IsOfFinOrder (∏ i, α i ^ (y i : ℤ))

section ThetaAlg

variable {m : ℕ}

@[simp] lemma thetaC_zero (ℓ : Fin m → ℂ) : thetaC ℓ 0 = 0 := by
  simp [thetaC]

lemma thetaC_add (ℓ : Fin m → ℂ) (y z : Fin m → ℤ) :
    thetaC ℓ (y + z) = thetaC ℓ y + thetaC ℓ z := by
  simp only [thetaC, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

lemma thetaC_neg (ℓ : Fin m → ℂ) (y : Fin m → ℤ) : thetaC ℓ (-y) = -thetaC ℓ y := by
  simp only [thetaC, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

lemma thetaC_smul (ℓ : Fin m → ℂ) (k : ℤ) (y : Fin m → ℤ) :
    thetaC ℓ (k • y) = (k : ℂ) * thetaC ℓ y := by
  simp only [thetaC, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end ThetaAlg

section Structure

variable {K : Type*} [Field K] {m : ℕ}

/-- `0 ∈ Γ`. -/
lemma MuRelC_zero (α : Fin m → K) : MuRelC α 0 := by
  rw [MuRelC]
  simpa using isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, one_pow 1⟩

/-- `Γ` is closed under addition. -/
lemma MuRelC_add {α : Fin m → K} (hα : ∀ i, α i ≠ 0) {y z : Fin m → ℤ}
    (hy : MuRelC α y) (hz : MuRelC α z) : MuRelC α (y + z) := by
  rw [MuRelC] at hy hz ⊢
  obtain ⟨n, hn, hny⟩ := isOfFinOrder_iff_pow_eq_one.mp hy
  obtain ⟨n', hn', hn'z⟩ := isOfFinOrder_iff_pow_eq_one.mp hz
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨n * n', Nat.mul_pos hn hn', ?_⟩
  have hprod : (∏ i, α i ^ ((y + z) i : ℤ)) =
      (∏ i, α i ^ (y i : ℤ)) * (∏ i, α i ^ (z i : ℤ)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, zpow_add₀ (hα i)]
  have key : (∏ i, α i ^ (y i : ℤ)) ^ (n * n') = 1 := by rw [pow_mul, hny, one_pow]
  have key' : (∏ i, α i ^ (z i : ℤ)) ^ (n * n') = 1 := by
    rw [mul_comm, pow_mul, hn'z, one_pow]
  rw [hprod, mul_pow, key, key', one_mul]

/-- `Γ` is closed under negation. -/
lemma MuRelC_neg {α : Fin m → K} (hα : ∀ i, α i ≠ 0) {y : Fin m → ℤ}
    (hy : MuRelC α y) : MuRelC α (-y) := by
  rw [MuRelC] at hy ⊢
  obtain ⟨n, hn, hny⟩ := isOfFinOrder_iff_pow_eq_one.mp hy
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨n, hn, ?_⟩
  have hprod : (∏ i, α i ^ ((-y) i : ℤ)) = (∏ i, α i ^ (y i : ℤ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.neg_apply, zpow_neg]
  rw [hprod, inv_pow, hny, inv_one]

/-- `Γ` is closed under integer scaling. -/
lemma MuRelC_smul {α : Fin m → K} (hα : ∀ i, α i ≠ 0) (k : ℤ) {y : Fin m → ℤ}
    (hy : MuRelC α y) : MuRelC α (k • y) := by
  rw [MuRelC] at hy ⊢
  obtain ⟨n, hn, hny⟩ := isOfFinOrder_iff_pow_eq_one.mp hy
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨n, hn, ?_⟩
  have hprod : (∏ i, α i ^ ((k • y) i : ℤ)) = (∏ i, α i ^ (y i : ℤ)) ^ k := by
    rw [← Finset.prod_zpow]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.smul_apply, smul_eq_mul, zpow_mul']
  rw [hprod]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hny, one_zpow]

end Structure

section ExpChar

variable {K : Type*} [Field K] {m : ℕ}

/-- The exponential of the log-form is `φ` applied to the corresponding product. -/
lemma exp_thetaC (φ : K →+* ℂ) (α : Fin m → K) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) (y : Fin m → ℤ) :
    Complex.exp (thetaC ℓ y) = φ (∏ i, α i ^ (y i : ℤ)) := by
  rw [thetaC, Complex.exp_sum, map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [Complex.exp_int_mul, hℓ i, map_zpow₀]

/-- `φ x` is a root of unity iff `x` is. -/
lemma isOfFinOrder_map_iff (φ : K →+* ℂ) (x : K) :
    IsOfFinOrder (φ x) ↔ IsOfFinOrder x := by
  rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
  constructor
  · rintro ⟨n, hn, hxn⟩
    exact ⟨n, hn, φ.injective (by rw [map_pow, hxn, map_one])⟩
  · rintro ⟨n, hn, hxn⟩
    exact ⟨n, hn, by rw [← map_pow, hxn, map_one]⟩

/-- `exp (2πi q)` is a root of unity for every rational `q`. -/
lemma isOfFinOrder_exp_rat_two_pi_I (q : ℚ) :
    IsOfFinOrder (Complex.exp ((q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨q.den, q.den_pos, ?_⟩
  have hnum : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by
    have h : (q : ℚ) * (q.den : ℚ) = q.num := by
      have h2 := Rat.num_div_den q
      rw [div_eq_iff] at h2
      · linarith [h2]
      · exact_mod_cast q.den_nz
    exact_mod_cast h
  have hbase : Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) = 1 := by
    simp
  calc Complex.exp ((q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ^ q.den
      = Complex.exp ((q.den : ℂ) * ((q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) :=
        (Complex.exp_nat_mul _ q.den).symm
    _ = Complex.exp (((q : ℂ) * (q.den : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)) := by ring_nf
    _ = Complex.exp ((q.num : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by rw [hnum]
    _ = Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ^ q.num := by
        have hh := Complex.exp_int_mul ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) q.num
        rw [← hh]
    _ = 1 := by rw [hbase, one_zpow]

/-- `Γ`-membership is exactly the condition `θ(y) ∈ 2πiℚ`. -/
theorem muRelC_iff_exists_rat (φ : K →+* ℂ) (α : Fin m → K) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) (y : Fin m → ℤ) :
    MuRelC α y ↔ ∃ q : ℚ, thetaC ℓ y = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  constructor
  · intro hy
    rw [MuRelC] at hy
    have hφ : IsOfFinOrder (φ (∏ i, α i ^ (y i : ℤ))) := (isOfFinOrder_map_iff φ _).mpr hy
    rw [← exp_thetaC φ α ℓ hℓ y] at hφ
    obtain ⟨n, hn, hn1⟩ := isOfFinOrder_iff_pow_eq_one.mp hφ
    have hexp : Complex.exp ((n : ℂ) * thetaC ℓ y) = 1 := by
      rw [Complex.exp_nat_mul, hn1]
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
    refine ⟨(k : ℚ) / n, ?_⟩
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have h2 : thetaC ℓ y * (n : ℂ) = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [mul_comm]; exact hk
    have hcast : (((k : ℚ) / n : ℚ) : ℂ) = (k : ℂ) / (n : ℂ) := by push_cast; ring
    rw [hcast, div_mul_eq_mul_div, eq_div_iff hnC]
    exact h2
  · rintro ⟨q, hq⟩
    rw [MuRelC]
    have h : Complex.exp (thetaC ℓ y) = φ (∏ i, α i ^ (y i : ℤ)) := exp_thetaC φ α ℓ hℓ y
    rw [hq] at h
    have hqru := isOfFinOrder_exp_rat_two_pi_I q
    rw [h] at hqru
    exact (isOfFinOrder_map_iff φ _).mp hqru

end ExpChar

section Vrel

variable {m : ℕ}

/-- The `ℚ`-subspace `V = {v ∈ ℚ^m | ∑ᵢ vᵢℓᵢ ∈ 2πiℚ}`; `Γ` is `ℤ^m ∩ V`. -/
noncomputable def Vrel (ℓ : Fin m → ℂ) : Submodule ℚ (Fin m → ℚ) where
  carrier := {v | ∃ q : ℚ, (∑ i, (v i : ℂ) * ℓ i) = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro v w ⟨q, hq⟩ ⟨q', hq'⟩
    refine ⟨q + q', ?_⟩
    have h1 : (∑ i, ((v + w) i : ℂ) * ℓ i)
        = (∑ i, (v i : ℂ) * ℓ i) + (∑ i, (w i : ℂ) * ℓ i) := by
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [h1, hq, hq']
    push_cast; ring
  smul_mem' := by
    rintro c v ⟨q, hq⟩
    refine ⟨c * q, ?_⟩
    have h1 : (∑ i, ((c • v) i : ℂ) * ℓ i) = (c : ℂ) * (∑ i, (v i : ℂ) * ℓ i) := by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by push_cast; ring
    rw [h1, hq]
    push_cast; ring

end Vrel

section Saturation

variable {K : Type*} [Field K] {m : ℕ}

/-- `Γ` is exactly the set of lattice points of `Vrel ℓ`. -/
theorem muRelC_iff_mem_Vrel (φ : K →+* ℂ) (α : Fin m → K) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) (y : Fin m → ℤ) :
    MuRelC α y ↔ (fun i => (y i : ℚ)) ∈ Vrel ℓ := by
  rw [muRelC_iff_exists_rat φ α ℓ hℓ y]
  exact Iff.rfl

end Saturation

end Work.BW
