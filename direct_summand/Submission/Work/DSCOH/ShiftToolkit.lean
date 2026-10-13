/-
Area DSCOH — toolkit for the explicit computation of the chart Čech complex of the shifts
`S(-d) = shift d` of the polynomial ring.

Everything in this file is about the *concrete* elements of the chart localizations: monomials
`x^α = ∏ Xᵢ^αᵢ`, the explicit form `m/X_S^k = LocalizedModule.mk m ⟨X_S^k⟩` of the generators of
`degZero`, and the "Laurent monomial" `x^β` (for `β : Fin n → ℤ`) of the top chart, which lets us
describe `degZero (shift d) univ` as the `A`-span of the `x^β` with `∑ β = -d`.
-/
import Mathlib
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.shift_gradedSMul
import Submission.Work.DSCOH.divPow_toLoc_mem

open MvPolynomial

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {n : ℕ}

/-! ## Monomials -/

/-- The monomial `∏ i, Xᵢ ^ αᵢ` of `A[X₀,…,X_{n-1}]`. -/
noncomputable def xpow (α : Fin n → ℕ) : Poly A n := ∏ i, (MvPolynomial.X i : Poly A n) ^ (α i)

lemma prod_X_eq_monomial_univ :
    (∏ i : Fin n, (MvPolynomial.X i : Poly A n)) = monomial (A := A) Finset.univ := by
  simp only [monomial, Var]

@[simp]
lemma xpow_zero : xpow (A := A) (fun _ : Fin n => 0) = 1 := by
  simp [xpow]

lemma xpow_add (α β : Fin n → ℕ) :
    xpow (A := A) (α + β) = xpow (A := A) α * xpow (A := A) β := by
  simp only [xpow, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

lemma xpow_one : xpow (A := A) (fun _ : Fin n => 1) = monomial (A := A) Finset.univ := by
  rw [xpow, ← prod_X_eq_monomial_univ]
  exact Finset.prod_congr rfl fun i _ => pow_one _

lemma xpow_const (j : ℕ) :
    xpow (A := A) (fun _ : Fin n => j) = (monomial (A := A) Finset.univ) ^ j := by
  have h : xpow (A := A) (fun _ : Fin n => j) = ∏ i, (MvPolynomial.X i : Poly A n) ^ j := rfl
  rw [h, ← prod_X_eq_monomial_univ, ← Finset.prod_pow]

lemma xpow_add_const (α : Fin n → ℕ) (j : ℕ) :
    xpow (A := A) (α + fun _ => j) =
      (monomial (A := A) Finset.univ) ^ j * xpow (A := A) α := by
  rw [xpow_add, xpow_const, mul_comm]

/-! ## The explicit form `m / X_S^k` of the generators of `degZero` -/

/-- The denominator `X_S^k = (∏_{i∈S} Xᵢ)^k`, as an element of the submonoid `subS S`. -/
noncomputable def den (S : Finset (Fin n)) (k : ℕ) : subS (A := A) S :=
  ⟨monomial (A := A) S ^ k,
    Submonoid.pow_mem (subS (A := A) S) (monomial_mem (A := A) S) k⟩

@[simp]
lemma den_coe (S : Finset (Fin n)) (k : ℕ) :
    ((den (A := A) S k : subS (A := A) S) : Poly A n) = monomial (A := A) S ^ k := rfl

/-- `m / X_S^k`, the generator of `degZero`, is the explicit fraction `mk m ⟨X_S^k⟩`. -/
lemma divPow_toLoc_eq_mk (S : Finset (Fin n)) (k : ℕ) (m : Poly A n) :
    divPow (A := A) (M := Poly A n) S k (toLoc (A := A) (M := Poly A n) S m) =
      LocalizedModule.mk m (den (A := A) S k) := by
  unfold divPow toLoc den
  simp only [LinearMap.restrictScalars_apply, LocalizedModule.mkLinearMap_apply,
    LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk, one_mul]

/-- Raising the index of the presentation of a generator: `m/X_S^k = (X_S^j·m)/X_S^{k+j}`. -/
lemma divPow_toLoc_smul_monomial_pow (S : Finset (Fin n)) (k j : ℕ) (m : Poly A n) :
    divPow (A := A) (M := Poly A n) S (k + j)
        (toLoc (A := A) (M := Poly A n) S ((monomial (A := A) S) ^ j * m)) =
      divPow (A := A) (M := Poly A n) S k (toLoc (A := A) (M := Poly A n) S m) := by
  rw [divPow_toLoc_eq_mk, divPow_toLoc_eq_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul, smul_eq_mul, den_coe]
  rw [← mul_assoc, ← pow_add]

/-- The structure map `resAt` on an explicit fraction: it only changes the submonoid. -/
lemma resAt_mk (S T : Finset (Fin n)) (h : S ⊆ T) (m : Poly A n) (s : subS (A := A) S) :
    resAt (A := A) (M := Poly A n) h (LocalizedModule.mk m s) =
      LocalizedModule.mk m ⟨(s : Poly A n), subS_mono (A := A) h s.2⟩ := by
  rw [IsLocalizedModule.mk_eq_mk', resAt, LocalizedModule.liftOfLE,
    IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

/-! ## Laurent monomials of the top chart -/

/-- In the top chart (`S = univ`, where all variables are inverted), the fraction
`(∏ i, Xᵢ^{βᵢ+k}) / X_univ^k`. -/
noncomputable def laurentAt (β : Fin n → ℤ) (k : ℕ) :
    locAt (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) :=
  divPow (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) k
    (toLoc (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n))
      (xpow (A := A) (n := n) fun i => (β i + (k : ℤ)).toNat))

/-- The canonical Laurent monomial `x^β` of the top chart, `β : Fin n → ℤ`. -/
noncomputable def laurent (β : Fin n → ℤ) :
    locAt (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) :=
  laurentAt (A := A) (n := n) β (∑ i, (-(β i)).toNat)

lemma le_sum_toNat (β : Fin n → ℤ) (i : Fin n) :
    -(β i) ≤ ((∑ j, (-(β j)).toNat : ℕ) : ℤ) := by
  have h2 : (-(β i)).toNat ≤ (∑ j, (-(β j)).toNat) :=
    Finset.single_le_sum (f := fun j => (-(β j)).toNat)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3 : (((-(β i)).toNat : ℕ) : ℤ) ≤ ((∑ j, (-(β j)).toNat : ℕ) : ℤ) := by
    exact_mod_cast h2
  rcases le_total (β i) 0 with hb | hb
  · rwa [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -(β i))] at h3
  · have hle : -(β i) ≤ 0 := by omega
    exact le_trans hle (Int.natCast_nonneg _)

/-- Adding `j` to the chosen index does not change an admissible Laurent presentation. -/
lemma laurentAt_add (β : Fin n → ℤ) {k : ℕ} (hk : ∀ i, -(β i) ≤ (k : ℤ)) (j : ℕ) :
    laurentAt (A := A) (n := n) β (k + j) = laurentAt (A := A) (n := n) β k := by
  unfold laurentAt
  have hft : ∀ i, (β i + (k : ℤ)).toNat + j = (β i + ((k + j : ℕ) : ℤ)).toNat := by
    intro i
    have h1 : (0 : ℤ) ≤ β i + (k : ℤ) := by linarith [hk i]
    have h2 : β i + ((k + j : ℕ) : ℤ) = (β i + (k : ℤ)) + (j : ℤ) := by push_cast; ring
    rw [h2, Int.toNat_add h1 (Int.natCast_nonneg j), Int.toNat_natCast]
  have hx : xpow (A := A) (n := n) (fun i => (β i + ((k + j : ℕ) : ℤ)).toNat) =
      (monomial (A := A) Finset.univ) ^ j *
        xpow (A := A) (n := n) (fun i => (β i + (k : ℤ)).toNat) := by
    have : (fun i => (β i + ((k + j : ℕ) : ℤ)).toNat) =
        (fun i => (β i + (k : ℤ)).toNat) + fun _ => j := by
      funext i; exact (hft i).symm
    rw [this, xpow_add_const]
  rw [hx, divPow_toLoc_smul_monomial_pow]

/-- **Independence of the chosen index**: any two admissible presentations of the same Laurent
monomial agree. -/
lemma laurentAt_eq (β : Fin n → ℤ) {k k' : ℕ}
    (hk : ∀ i, -(β i) ≤ (k : ℤ)) (hk' : ∀ i, -(β i) ≤ (k' : ℤ)) :
    laurentAt (A := A) (n := n) β k = laurentAt (A := A) (n := n) β k' := by
  rcases le_total k k' with h | h
  · obtain ⟨j, rfl⟩ : ∃ j, k' = k + j := ⟨k' - k, (Nat.add_sub_cancel' h).symm⟩
    exact (laurentAt_add (A := A) (n := n) β hk j).symm
  · obtain ⟨j, rfl⟩ : ∃ j, k = k' + j := ⟨k - k', (Nat.add_sub_cancel' h).symm⟩
    exact laurentAt_add (A := A) (n := n) β hk' j

lemma laurent_eq (β : Fin n → ℤ) {k : ℕ} (hk : ∀ i, -(β i) ≤ (k : ℤ)) :
    laurent (A := A) (n := n) β = laurentAt (A := A) (n := n) β k :=
  laurentAt_eq (A := A) (n := n) β (fun i => le_sum_toNat β i) hk

/-- **The Laurent monomial attached to `α` and `k`**: `laurent (α - k·1)` is the explicit
fraction `(∏ Xᵢ^{αᵢ}) / X_univ^k`. This is the form in which the elements of
`degZero (shift d) univ` are recognised as combinations of Laurent monomials. -/
lemma laurent_sub_one_eq (α : Fin n → ℕ) (k : ℕ) :
    laurent (A := A) (n := n) (fun i => (α i : ℤ) - k) =
      divPow (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) k
        (toLoc (A := A) (M := Poly A n) (Finset.univ : Finset (Fin n)) (xpow (A := A) α)) := by
  have hk : ∀ i, -(((fun i => (α i : ℤ) - k) i)) ≤ (k : ℤ) := by
    intro i; simp only; omega
  rw [laurent_eq (A := A) (n := n) (β := fun i => (α i : ℤ) - k) (k := k) hk]
  unfold laurentAt
  have hx : (fun i => (((fun i => (α i : ℤ) - k) i) + (k : ℤ)).toNat) = α := by
    funext i
    simp only
    rw [show ((α i : ℤ) - k + (k : ℤ)) = (α i : ℤ) by ring, Int.toNat_natCast]
  rw [hx]

/-! ## Homogeneity -/

lemma xpow_mem_homSub (α : Fin n → ℕ) : xpow (A := A) α ∈ homSub A n (∑ i, α i) := by
  rw [homSub, mem_homogeneousSubmodule, xpow]
  exact IsHomogeneous.prod Finset.univ (fun i => (MvPolynomial.X i : Poly A n) ^ (α i))
    (fun i => α i) (fun i _ => by simpa using (isHomogeneous_X A i).pow (α i))

/-- `MvPolynomial.monomial` and `xpow` agree. -/
lemma mvpoly_monomial_eq_xpow (v : Fin n →₀ ℕ) :
    (MvPolynomial.monomial v) (1 : A) = xpow (A := A) (fun i => v i) := by
  rw [← MvPolynomial.prod_X_pow_eq_monomial, xpow]
  exact Finset.prod_subset (Finset.subset_univ _) (fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx, pow_zero])

/-- The degree of the monomial `xpow (β + K)` is `n·K - d` when `∑ β = -d`. -/
lemma sum_toNat_eq (d : ℕ) (β : Fin n → ℤ) {K : ℕ} (hK : ∀ i, -(β i) ≤ (K : ℤ))
    (hβ : (∑ i, β i) = -(d : ℤ)) :
    (∑ i, (β i + (K : ℤ)).toNat) = K * n - d := by
  have h1 : ∀ i, (0 : ℤ) ≤ β i + (K : ℤ) := fun i => by linarith [hK i]
  have h2 : ∀ i, (((β i + (K : ℤ)).toNat : ℕ) : ℤ) = β i + (K : ℤ) :=
    fun i => Int.toNat_of_nonneg (h1 i)
  have hle : (d : ℤ) ≤ (K : ℤ) * n := by
    have hsum_neg : ∑ i, (-(β i)) = (d : ℤ) := by
      rw [Finset.sum_neg_distrib, hβ]; ring
    have hle' : ∑ i, (-(β i)) ≤ ∑ i, (K : ℤ) := Finset.sum_le_sum (fun i _ => hK i)
    rw [hsum_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle'
    linarith
  have h3 : ((∑ i, (β i + (K : ℤ)).toNat : ℕ) : ℤ) = -(d : ℤ) + (K : ℤ) * n := by
    push_cast
    rw [Finset.sum_congr rfl (fun i _ => h2 i), Finset.sum_add_distrib, Finset.sum_const, hβ,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hle' : d ≤ K * n := by exact_mod_cast hle
  have h6 : (-(d : ℤ) + (K : ℤ) * n).toNat = K * n - d := by
    rw [show (-(d : ℤ) + (K : ℤ) * n) = ((K * n - d : ℕ) : ℤ) from by
      rw [Nat.cast_sub hle']; push_cast; ring, Int.toNat_natCast]
  have h5 : (∑ i, (β i + (K : ℤ)).toNat) = (-(d : ℤ) + (K : ℤ) * n).toNat := by
    rw [← h3, Int.toNat_natCast]
  rw [h5, h6]

/-- **The Laurent monomial `x^β` lies in the degree-zero part when `∑ β = -d`.** -/
lemma laurent_mem_degZero {d : ℕ} {β : Fin n → ℤ} (hβ : (∑ i, β i) = -(d : ℤ)) :
    laurent (A := A) (n := n) β ∈
      degZero (A := A) (n := n) (M := Poly A n) (shift (A := A) (n := n) d)
        (Finset.univ : Finset (Fin n)) := by
  set K : ℕ := ∑ i, (-(β i)).toNat with hKdef
  have hK : ∀ i, -(β i) ≤ (K : ℤ) := fun i => le_sum_toNat β i
  have hleZ : (d : ℤ) ≤ (K : ℤ) * n := by
    have hsum_neg : ∑ i, (-(β i)) = (d : ℤ) := by
      rw [Finset.sum_neg_distrib, hβ]; ring
    have hle' : ∑ i, (-(β i)) ≤ ∑ i, (K : ℤ) := Finset.sum_le_sum (fun i _ => hK i)
    rw [hsum_neg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle'
    linarith
  have hle : d ≤ K * n := by exact_mod_cast hleZ
  have hsum := sum_toNat_eq d β hK hβ
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hmem : xpow (A := A) (fun i => (β i + (K : ℤ)).toNat) ∈
      shift (A := A) (n := n) d (K * (Finset.univ : Finset (Fin n)).card) := by
    rw [hcard, shift_of_le hle, ← hsum]
    exact xpow_mem_homSub (A := A) (n := n) _
  have hmain := divPow_toLoc_mem (A := A) (n := n) (M := Poly A n)
    (shift (A := A) (n := n) d) (Finset.univ : Finset (Fin n)) K hmem
  have hlaurent : laurent (A := A) (n := n) β = laurentAt (A := A) (n := n) β K := by
    rw [hKdef]; rfl
  rw [hlaurent]
  exact hmain

end Work.DSCOH
