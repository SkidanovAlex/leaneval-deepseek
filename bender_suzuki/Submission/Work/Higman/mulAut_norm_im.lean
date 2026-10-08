import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- **A telescoping product identity.**  For any sequence `a : ℕ → M` in a commutative group and
any `n`,
`(∏ i < n, (a (i+1)) ^ (n-1-i)) * (a 0) ^ n = (∏ i < n, a i) * (∏ i < n, (a i) ^ (n-1-i))`.

The weight `n-1-i` is chosen so that the `i = n-1` factor has exponent `0`; this makes the shifted
product `∏ i < n, (a (i+1)) ^ (n-1-i)` (the image of `∏ i < n, (a i) ^ (n-1-i)` under the shift)
directly comparable with the original one, without any hypothesis on `a`. -/
lemma prod_shift_pow {M : Type*} [CommGroup M] (a : ℕ → M) (n : ℕ) :
    (∏ i ∈ Finset.range n, (a (i + 1)) ^ (n - 1 - i)) * a 0 ^ n
      = (∏ i ∈ Finset.range n, a i) * (∏ i ∈ Finset.range n, (a i) ^ (n - 1 - i)) := by
  induction n with
  | zero => simp
  | succ n _ =>
    simp only [Nat.add_sub_cancel]
    have hA : (∏ i ∈ Finset.range (n + 1), (a (i + 1)) ^ (n - i))
        = (∏ i ∈ Finset.range n, (a (i + 1)) ^ (n - 1 - i))
            * (∏ i ∈ Finset.range n, a (i + 1)) := by
      rw [Finset.prod_range_succ]
      rw [show (a (n + 1)) ^ (n - n) = 1 by simp, mul_one]
      rw [Finset.prod_congr rfl (fun i hi => by
            have hi' : i < n := Finset.mem_range.mp hi
            have h : n - i = (n - 1 - i) + 1 := by omega
            rw [h, pow_succ]), Finset.prod_mul_distrib]
    have hD : (∏ i ∈ Finset.range n, a (i + 1))
        = (∏ i ∈ Finset.range (n + 1), a i) * (a 0)⁻¹ := by
      have h := Finset.prod_range_succ' a n
      rw [h]; group
    have hB : (∏ i ∈ Finset.range (n + 1), a i) = (∏ i ∈ Finset.range n, a i) * a n :=
      Finset.prod_range_succ a n
    have hC : (∏ i ∈ Finset.range (n + 1), (a i) ^ (n - i))
        = a 0 ^ n * (∏ i ∈ Finset.range n, (a (i + 1)) ^ (n - 1 - i)) := by
      rw [Finset.prod_range_succ' (fun j => (a j) ^ (n - j)) n, Nat.sub_zero,
        mul_comm (a 0 ^ n)]
      congr 1
      exact Finset.prod_congr rfl (fun j hj => by
        have hj' : j < n := Finset.mem_range.mp hj
        rw [show n - (j + 1) = n - 1 - j by omega])
    rw [hA, hD, hB, hC, pow_succ']
    group
    ac_rfl

/-- **The image of `σ - 1` on a finite abelian group.**

Let `Z` be a finite abelian group and `σ` an automorphism of `Z` whose order `m` is coprime to
`|Z|`.  If `z` lies in the kernel of the norm map `N = ∑_{i<m} σ^i`, i.e.
`∏ i < m, σ ^ i z = 1`, then `z = σ n · n⁻¹` for some `n : Z`.

Proof.  With `S = ∏ i < m, (σ ^ i c) ^ i` one has the telescoping identity
`σ S · S⁻¹ = c ^ m · (∏ i < m, σ ^ i c)⁻¹` (distribute and collect equal factors).  For `c` with
`N c = 1` this gives `σ S · S⁻¹ = c ^ m`; since the `m`-th power map on the finite abelian `Z` is
bijective (`gcd (m, |Z|) = 1`), write `S = n ^ m`; then `(σ n · n⁻¹) ^ m = c ^ m`, whence
`σ n · n⁻¹ = c` by injectivity. -/
theorem mulAut_norm_im {Z : Type} [CommGroup Z] [Finite Z] (σ : MulAut Z)
    (hcop : (orderOf σ).Coprime (Nat.card Z)) (z : Z)
    (hz : ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) z = 1) :
    ∃ n : Z, σ n * n⁻¹ = z := by
  classical
  set m := orderOf σ with hm
  have hcop' : (Nat.card Z).Coprime m := by rw [hm]; exact hcop.symm
  let a : ℕ → Z := fun i => (σ ^ i) z
  have ha0 : a 0 = z := by simp [a]
  have hprod : (∏ i ∈ Finset.range m, a i) = 1 := by simpa [a] using hz
  -- `T` is the "partial norm" `∏ i < m, (σ^i z) ^ (m-1-i)`.
  set T : Z := ∏ i ∈ Finset.range m, (a i) ^ (m - 1 - i) with hT
  -- Its `σ`-image is the shifted product.
  have hσT : σ T = ∏ i ∈ Finset.range m, (a (i + 1)) ^ (m - 1 - i) := by
    rw [hT, map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    rw [map_pow]
    congr 1
    simp [a, pow_succ', MulAut.mul_apply]
  -- Hence the telescoping identity specialises to `σ T * z^m = T`, using `N z = 1`.
  have hkey : σ T * z ^ m = T := by
    have hps := prod_shift_pow a m
    rw [← hσT, ha0, hprod, one_mul, ← hT] at hps
    exact hps
  -- Extract an `m`-th root of `T⁻¹` (the `m`-th power map is bijective).
  obtain ⟨n, hn⟩ := (Nat.Coprime.pow_left_bijective hcop').surjective T⁻¹
  change n ^ m = T⁻¹ at hn
  refine ⟨n, ?_⟩
  -- It remains to compare `m`-th powers.
  apply (Nat.Coprime.pow_left_bijective hcop').injective
  change (σ n * n⁻¹) ^ m = z ^ m
  rw [mul_pow, ← map_pow, inv_pow, hn, map_inv, inv_inv]
  exact inv_mul_eq_iff_eq_mul.mpr hkey.symm

end Work.Higman
