import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multigraded Hilbert functions along a ray: definitions

We set up the multigrading of the coordinate ring `MR N = ℂ[X_{i,j}]` of `(P¹)^{N+1}` by the
group `Fin (N+1) →₀ ℤ` (variable `(i,j)` has weight `e_i`), the notion of a compatible grading of
an `MR N`-module, and the "binomial kernel" function `kFun` which describes the Hilbert function
of a graded module (the `X^u`-coefficient of `P · ∏(1-X_i)^{-β_i}`).
-/

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

/-! ### The multigrading -/

/-- The weight of the variable `(i,j)`: the `i`-th basis vector of `Fin (N+1) →₀ ℤ`. -/
noncomputable def wZ (N : ℕ) : Fin (N + 1) × Fin 2 → (Fin (N + 1) →₀ ℤ) :=
  fun v => Finsupp.single v.1 1

/-- The graded piece of `MR N` of multidegree `u`. -/
noncomputable def pieceZ (N : ℕ) (u : Fin (N + 1) →₀ ℤ) : Submodule ℂ (MR N) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ (wZ N) u

theorem mem_pieceZ (N : ℕ) (u : Fin (N + 1) →₀ ℤ) (p : MR N) :
    p ∈ pieceZ N u ↔ p.IsWeightedHomogeneous (wZ N) u := Iff.rfl

/-- Cast a multidegree in `ℕ^{N+1}` to one in `ℤ^{N+1}`. -/
noncomputable def castF {N : ℕ} (D : Fin (N + 1) →₀ ℕ) : Fin (N + 1) →₀ ℤ :=
  D.mapRange Nat.cast (by simp)

@[simp]
theorem castF_apply {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (i : Fin (N + 1)) :
    castF D i = (D i : ℤ) := rfl

theorem castF_smul {N : ℕ} (t : ℕ) (D : Fin (N + 1) →₀ ℕ) :
    castF (t • D) = t • castF D := by
  ext i; simp [castF_apply]

/-- Dimension of the graded piece of a quotient by a multihomogeneous ideal. -/
noncomputable def hilbIdeal (N : ℕ) (J : Ideal (MR N)) (u : Fin (N + 1) →₀ ℤ) : ℕ :=
  Module.finrank ℂ ((pieceZ N u) ⧸
    Submodule.comap (pieceZ N u).subtype (J.restrictScalars ℂ))

/-! ### Gradings of modules -/

/-- A `ℤ^{N+1}`-grading of a module over `MR N`, compatible with the grading of the ring. -/
structure IsGrading (N : ℕ) {M : Type*} [AddCommGroup M] [Module ℂ M] [Module (MR N) M]
    (piece : (Fin (N + 1) →₀ ℤ) → Submodule ℂ M) : Prop where
  /-- the pieces form a direct sum decomposition -/
  isInternal : DirectSum.IsInternal piece
  /-- multiplication by a variable shifts the grading -/
  smul_mem : ∀ (v : Fin (N + 1) × Fin 2) (u : Fin (N + 1) →₀ ℤ) {m : M},
    m ∈ piece u → (MvPolynomial.X v : MR N) • m ∈ piece (u + wZ N v)
  /-- all pieces of negative multidegree vanish -/
  eq_bot_of_neg : ∀ u : Fin (N + 1) →₀ ℤ, (∃ i, u i < 0) → piece u = ⊥

/-! ### The binomial kernel -/

/-- `cbeta β k` = coefficient of `X^k` in `(1-X)^{-β}`, i.e. `binom (k+β-1) (β-1)` for `k ≥ 0`,
and `0` for `k < 0`. -/
noncomputable def cbeta (β : ℕ) (k : ℤ) : ℚ :=
  if k < 0 then 0
  else if β = 0 then (if k = 0 then 1 else 0)
  else (Nat.choose (k.toNat + β - 1) (β - 1) : ℚ)

theorem cbeta_of_neg {β : ℕ} {k : ℤ} (hk : k < 0) : cbeta β k = 0 := by
  rw [cbeta]; exact if_pos hk

/-- `cbeta β k` for `β > 0` and `k ≥ 0`. -/
theorem cbeta_pos {β : ℕ} (hβ : 0 < β) {k : ℤ} (hk : 0 ≤ k) :
    cbeta β k = (Nat.choose (k.toNat + β - 1) (β - 1) : ℚ) := by
  rw [cbeta, if_neg (not_lt.mpr hk), if_neg (ne_of_gt hβ)]

/-- `cbeta 0 k = 0` for `k ≠ 0`. -/
theorem cbeta_zero_of_ne_zero {k : ℤ} (hk : k ≠ 0) : cbeta 0 k = 0 := by
  rcases lt_or_gt_of_ne hk with h | h
  · exact cbeta_of_neg h
  · rw [cbeta, if_neg (not_lt.mpr (le_of_lt h)), if_pos rfl, if_neg (ne_of_gt h)]

theorem cbeta_zero_zero : cbeta 0 0 = 1 := by
  rw [cbeta, if_neg (by norm_num : ¬ ((0:ℤ) < 0)), if_pos rfl, if_pos rfl]

/-- The binomial identity behind the Hilbert–Serre recursion. -/
theorem cbeta_sub_cbeta {β : ℕ} (hβ : 1 ≤ β) (k : ℤ) :
    cbeta β k - cbeta β (k - 1) = cbeta (β - 1) k := by
  by_cases hk : k ≤ 0
  · rcases lt_or_eq_of_le hk with h | h
    · rw [cbeta_of_neg h, cbeta_of_neg (by omega : k - 1 < 0), cbeta_of_neg h, sub_zero]
    · subst h
      rw [cbeta_of_neg (by norm_num : (0:ℤ) - 1 < 0), sub_zero]
      rcases eq_or_lt_of_le hβ with h1 | h2
      · subst h1; rw [cbeta_zero_zero, cbeta_pos (by norm_num) (le_refl (0:ℤ))]; norm_num
      · rw [cbeta_pos (by omega) (le_refl (0:ℤ)), cbeta_pos (by omega) (le_refl (0:ℤ))]
        simp
  · push_neg at hk
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = (j : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    have hk1 : ((j : ℤ) + 1).toNat = j + 1 := by omega
    have hk2 : ((j : ℤ) + 1 - 1).toNat = j := by omega
    rcases eq_or_lt_of_le hβ with h1 | h2
    · subst h1
      rw [cbeta_pos (by norm_num : (0:ℕ) < 1) (by omega : (0:ℤ) ≤ (j:ℤ) + 1),
        cbeta_pos (by norm_num : (0:ℕ) < 1) (by omega : (0:ℤ) ≤ (j:ℤ) + 1 - 1),
        cbeta_zero_of_ne_zero (by omega : (j : ℤ) + 1 ≠ 0), hk1, hk2]
      simp
    · have hb2 : 2 ≤ β := by omega
      rw [cbeta_pos (by omega) (by omega : (0:ℤ) ≤ (j:ℤ) + 1),
        cbeta_pos (by omega) (by omega : (0:ℤ) ≤ (j:ℤ) + 1 - 1),
        cbeta_pos (by omega) (by omega : (0:ℤ) ≤ (j:ℤ) + 1), hk1, hk2]
      have e1 : j + 1 + β - 1 = j + β := by omega
      have e3 : j + 1 + (β - 1) - 1 = j + β - 1 := by omega
      have e4 : j + β - 1 + 1 = j + β := by omega
      have hb : β - 2 + 1 = β - 1 := by omega
      have hb2' : β - 1 - 1 = β - 2 := by omega
      rw [e1, e3, hb2', ← e4, ← hb, Nat.choose_succ_succ]
      push_cast
      ring

/-! ### `kFun` -/

/-- The "kernel" function attached to a finitely supported `P` and a multiplicity vector `β`:
the coefficient of `X^u` in `P(X) · ∏_i (1-X_i)^{-β_i}`, i.e. the (truncated) polynomial
function `u ↦ ∑_v P_v ∏_i binom(u_i - v_i + β_i - 1, β_i - 1)`. -/
noncomputable def kFun (N : ℕ) (β : Fin (N + 1) → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℚ) (u : Fin (N + 1) →₀ ℤ) : ℚ :=
  ∑ v ∈ P.support, P.coeff v * ∏ i, cbeta (β i) (u i - (v i : ℤ))

/-- The defining sum, over any finset containing the support. -/
theorem kFun_congr_support (N : ℕ) (β : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℚ)
    (u : Fin (N + 1) →₀ ℤ) {s : Finset (Fin (N + 1) →₀ ℕ)} (hs : P.support ⊆ s) :
    kFun N β P u = ∑ v ∈ s, P.coeff v * ∏ i, cbeta (β i) (u i - (v i : ℤ)) := by
  rw [kFun]
  have h := Finset.sum_subset (f := fun v => P.coeff v * ∏ i, cbeta (β i) (u i - (v i : ℤ))) hs
    (fun v _ hv => by rw [MvPolynomial.notMem_support_iff.mp hv, zero_mul])
  exact h

theorem kFun_zero (N : ℕ) (β : Fin (N + 1) → ℕ) (u : Fin (N + 1) →₀ ℤ) :
    kFun N β 0 u = 0 := by
  simp [kFun]

theorem kFun_add (N : ℕ) (β : Fin (N + 1) → ℕ) (P Q : MvPolynomial (Fin (N + 1)) ℚ)
    (u : Fin (N + 1) →₀ ℤ) : kFun N β (P + Q) u = kFun N β P u + kFun N β Q u := by
  classical
  have hPQ : (P + Q).support ⊆ P.support ∪ Q.support := MvPolynomial.support_add
  rw [kFun_congr_support N β (P + Q) u hPQ]
  have step1 : ∀ v ∈ P.support ∪ Q.support,
      (P + Q).coeff v * ∏ i, cbeta (β i) (u i - (v i : ℤ)) =
      P.coeff v * ∏ i, cbeta (β i) (u i - (v i : ℤ)) +
      Q.coeff v * ∏ i, cbeta (β i) (u i - (v i : ℤ)) := by
    intro v _
    rw [MvPolynomial.coeff_add, add_mul]
  rw [Finset.sum_congr rfl step1, Finset.sum_add_distrib]
  congr 1
  · rw [kFun_congr_support N β P u Finset.subset_union_left]
  · rw [kFun_congr_support N β Q u Finset.subset_union_right]

theorem kFun_neg (N : ℕ) (β : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℚ)
    (u : Fin (N + 1) →₀ ℤ) : kFun N β (-P) u = -kFun N β P u := by
  have h := kFun_add N β (-P) P u
  rw [neg_add_cancel, kFun_zero] at h
  linarith [h]

theorem kFun_sub (N : ℕ) (β : Fin (N + 1) → ℕ) (P Q : MvPolynomial (Fin (N + 1)) ℚ)
    (u : Fin (N + 1) →₀ ℤ) : kFun N β (P - Q) u = kFun N β P u - kFun N β Q u := by
  rw [sub_eq_add_neg, kFun_add, kFun_neg]
  ring

/-- If some coordinate of `u` is negative then `kFun β P u = 0`. -/
theorem kFun_eq_zero_of_neg (N : ℕ) (β : Fin (N + 1) → ℕ)
    (P : MvPolynomial (Fin (N + 1)) ℚ) (u : Fin (N + 1) →₀ ℤ) (i : Fin (N + 1))
    (hi : u i < 0) : kFun N β P u = 0 := by
  rw [kFun]
  refine Finset.sum_eq_zero fun v hv => ?_
  have hz : cbeta (β i) (u i - (v i : ℤ)) = 0 := by
    apply cbeta_of_neg
    have : (0:ℤ) ≤ (v i : ℤ) := Int.natCast_nonneg _
    omega
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hz, mul_zero]

/-- The recursion identity of the Hilbert–Serre argument: subtracting `e_i` from the argument and
subtracting one from `β i` agree. -/
theorem kFun_diff (N : ℕ) (β : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℚ)
    (u : Fin (N + 1) →₀ ℤ) (i : Fin (N + 1)) (hβ : 1 ≤ β i) :
    kFun N β P (u - Finsupp.single i 1) =
      kFun N β P u - kFun N (Function.update β i (β i - 1)) P u := by
  classical
  simp only [kFun]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hsub_i : (u - Finsupp.single i (1 : ℤ)) i = u i - 1 := by
    rw [Finsupp.sub_apply, Finsupp.single_eq_same]
  have hsub_j : ∀ j ≠ i, (u - Finsupp.single i (1 : ℤ)) j = u j := by
    intro j hj
    rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hj, sub_zero]
  have hupd_i : Function.update β i (β i - 1) i = β i - 1 := Function.update_self _ _ _
  have hupd_j : ∀ j ≠ i, Function.update β i (β i - 1) j = β j :=
    fun j hj => Function.update_of_ne hj _ _
  rw [← Finset.prod_erase_mul Finset.univ
        (fun j => cbeta (β j) ((u - Finsupp.single i (1 : ℤ)) j - (v j : ℤ)))
        (Finset.mem_univ i),
      ← Finset.prod_erase_mul Finset.univ
        (fun j => cbeta (β j) (u j - (v j : ℤ))) (Finset.mem_univ i),
      ← Finset.prod_erase_mul Finset.univ
        (fun j => cbeta (Function.update β i (β i - 1) j) (u j - (v j : ℤ)))
        (Finset.mem_univ i)]
  have hA : (∏ j ∈ Finset.univ.erase i,
        cbeta (β j) ((u - Finsupp.single i (1 : ℤ)) j - (v j : ℤ)))
      = ∏ j ∈ Finset.univ.erase i, cbeta (β j) (u j - (v j : ℤ)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hsub_j j (Finset.mem_erase.mp hj).1]
  have hA' : (∏ j ∈ Finset.univ.erase i,
        cbeta (Function.update β i (β i - 1) j) (u j - (v j : ℤ)))
      = ∏ j ∈ Finset.univ.erase i, cbeta (β j) (u j - (v j : ℤ)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hupd_j j (Finset.mem_erase.mp hj).1]
  rw [hA, hA', hsub_i, hupd_i]
  rw [← mul_sub]
  congr 1
  rw [← mul_sub]
  congr 1
  have harg : u i - 1 - (v i : ℤ) = u i - (v i : ℤ) - 1 := by ring
  rw [harg, ← cbeta_sub_cbeta hβ (u i - (v i : ℤ))]
  ring

end Work.BW
