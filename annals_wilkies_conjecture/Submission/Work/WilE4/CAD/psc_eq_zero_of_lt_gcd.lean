import Mathlib
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.psc_entry
import Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C

set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open Polynomial Matrix

/-! ## The principal subresultant matrix as the matrix of the restricted Sylvester map

The entries of `pscMat f g m n i` are computed in `Submission.Work.WilE4.CAD.psc_entry`
(`pscMat_apply`).  Here we use that to identify the matrix with the matrix, in the standard
monomial bases, of the linear map `(A, B) ↦ (r ↦ (A * f + B * g).coeff (i + r))` on
`ℝ[X]_{< n - i} × ℝ[X]_{< m - i}`: the coordinates of `A` followed by those of `B` are sent to the
coefficients of `A * f + B * g` at the powers `X ^ i, …, X ^ (m + n - i - 1)`. -/

section MulVec

/-- The `k`-th summand of the expansion of `c • X ^ k * f` in powers of `X`, as a coefficient. -/
lemma pscZero_coeff_C_mul_X_mul (c : ℝ) (f : Polynomial ℝ) (k N : ℕ) :
    ((C c * X ^ k) * f).coeff N = c * (f * X ^ k).coeff N := by
  rw [← Polynomial.smul_eq_C_mul, smul_mul_assoc, Polynomial.coeff_smul, smul_eq_mul,
    mul_comm (X ^ k) f]

/-- Expanding `A` in monomials: the coefficient of `X ^ N` in `A * f` is the sum of the
contributions `A.coeff k * (f * X ^ k).coeff N` of its monomials. -/
lemma pscZero_coeff_mul_eq_sum_range {A f : Polynomial ℝ} {s N : ℕ} (hA : A.natDegree < s) :
    (A * f).coeff N = ∑ k ∈ Finset.range s, A.coeff k * (f * X ^ k).coeff N := by
  have hexp : A = ∑ k ∈ Finset.range s, C (A.coeff k) * X ^ k := by
    conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow A]
    exact Finset.sum_subset (s₁ := Finset.range (A.natDegree + 1)) (s₂ := Finset.range s)
      (f := fun k => C (A.coeff k) * X ^ k)
      (Finset.range_subset_range.mpr (by omega))
      (fun k hk hknot => by
        have hk1 : A.natDegree < k := by
          by_contra hcon
          exact hknot (Finset.mem_range.mpr (by omega))
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk1]
        simp)
  have step1 : (A * f).coeff N = ((∑ k ∈ Finset.range s, C (A.coeff k) * X ^ k) * f).coeff N := by
    conv_lhs => rw [hexp]
  have step2 : ((∑ k ∈ Finset.range s, C (A.coeff k) * X ^ k) * f).coeff N
      = (∑ k ∈ Finset.range s, (C (A.coeff k) * X ^ k) * f).coeff N := by
    rw [Finset.sum_mul]
  have step3 : (∑ k ∈ Finset.range s, (C (A.coeff k) * X ^ k) * f).coeff N
      = ∑ k ∈ Finset.range s, ((C (A.coeff k) * X ^ k) * f).coeff N :=
    map_sum (Polynomial.lcoeff ℝ N) _ _
  have step4 : ∑ k ∈ Finset.range s, ((C (A.coeff k) * X ^ k) * f).coeff N
      = ∑ k ∈ Finset.range s, A.coeff k * (f * X ^ k).coeff N :=
    Finset.sum_congr rfl (fun k _ => pscZero_coeff_C_mul_X_mul (A.coeff k) f k N)
  rw [step1, step2, step3, step4]

/-- The previous expansion, indexed by `Fin s` instead of `Finset.range s`. -/
lemma pscZero_coeff_mul_eq_sum_fin {A f : Polynomial ℝ} {s N : ℕ} (hA : A.natDegree < s) :
    (A * f).coeff N = ∑ k : Fin s, A.coeff (k : ℕ) * (f * X ^ (k : ℕ)).coeff N := by
  rw [pscZero_coeff_mul_eq_sum_range (N := N) hA]
  exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => A.coeff k * (f * X ^ k).coeff N) s).symm

/-- **The principal subresultant matrix is the matrix of the restricted Sylvester map.**

If `A.natDegree + i < n` and `B.natDegree + i < m`, the vector of the coordinates of `A` followed
by those of `B` is sent by `pscMat f g m n i` to the vector of coefficients of `A * f + B * g` at
the powers `X ^ i, …, X ^ (m + n - i - 1)`. -/
lemma pscZero_mulVec_eq_coeff (f g : Polynomial ℝ) {m n i : ℕ} (hf : f.natDegree ≤ m)
    (hg : g.natDegree ≤ n) (A B : Polynomial ℝ) (hA : A.natDegree + i < n)
    (hB : B.natDegree + i < m) (r : Fin (m + n - 2 * i)) :
    Matrix.mulVec (pscMat f g m n i)
        (fun k => if (k : ℕ) < n - i then A.coeff (k : ℕ) else B.coeff ((k : ℕ) - (n - i))) r
      = (A * f + B * g).coeff (i + (r : ℕ)) := by
  have hAs : A.natDegree < n - i := by omega
  have hBs : B.natDegree < m - i := by omega
  have hN : (n - i) + (m - i) = m + n - 2 * i := by omega
  set e : Fin (n - i) ⊕ Fin (m - i) ≃ Fin (m + n - 2 * i) :=
    finSumFinEquiv.trans (finCongr hN) with hedef
  have he_inl : ∀ a : Fin (n - i), ((e (Sum.inl a) : Fin (m + n - 2 * i)) : ℕ) = (a : ℕ) := by
    intro a; rw [hedef]; simp
  have he_inr : ∀ b : Fin (m - i),
      ((e (Sum.inr b) : Fin (m + n - 2 * i)) : ℕ) = (n - i) + (b : ℕ) := by
    intro b; rw [hedef]; simp
  rw [Matrix.mulVec_apply, dotProduct]
  rw [← Equiv.sum_comp e (fun k => (pscMat f g m n i).row r k *
      (fun k => if (k : ℕ) < n - i then A.coeff (k : ℕ) else B.coeff ((k : ℕ) - (n - i))) k)]
  rw [Fintype.sum_sum_type]
  rw [Polynomial.coeff_add, pscZero_coeff_mul_eq_sum_fin (N := i + (r : ℕ)) hAs,
    pscZero_coeff_mul_eq_sum_fin (A := B) (f := g) (N := i + (r : ℕ)) hBs]
  congr 1
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.row_apply, pscMat_apply f g hf hg r (e (Sum.inl a)), he_inl a]
    beta_reduce
    rw [ite_eq_left (show (a : ℕ) < n - i by omega),
      ite_eq_left (show (a : ℕ) < n - i by omega)]
    ring
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Matrix.row_apply, pscMat_apply f g hf hg r (e (Sum.inr b)), he_inr b]
    beta_reduce
    rw [ite_eq_right (show ¬((n - i) + (b : ℕ) < n - i) by omega),
        ite_eq_right (show ¬((n - i) + (b : ℕ) < n - i) by omega)]
    rw [show (n - i) + (b : ℕ) - (n - i) = (b : ℕ) by omega]
    ring

end MulVec

/-- **Vanishing of the principal subresultant coefficients below the degree of the gcd.**

`Work.WilE4.CAD.pscMat f g m n i` is the submatrix of `Polynomial.sylvester f g m n` on the rows
`pscRow m n i` (the powers `X^{2i}, …, X^{m+n-1}`) and the columns `pscCol m n i` (the multiples
`X^k f` for `i ≤ k ≤ n-1`, then `X^k g` for `i ≤ k ≤ m-1`), and `psc f g m n i` is its determinant.

MATHEMATICAL CONTENT.  That matrix is the matrix, in the standard bases, of the linear map
`Ψ_i : ℝ[X]_{< n-i} × ℝ[X]_{< m-i} → (Fin (m+n-2i) → ℝ)`, `(A,B) ↦ (r ↦ (A*f + B*g).coeff (i + (i + r)))`
(the coefficients of `A*f + B*g` at the powers `X^i, …, X^{m+n-i-1}`; note
`deg (A*f + B*g) ≤ (n-i-1) + m = m+n-i-1`, so only the *low* coefficients, those of `X^t` with
`t < i`, are not read).  Two spaces of the same dimension `m+n-2i`, so
`det (pscMat f g m n i) ≠ 0 ↔ Ψ_i injective`.  Also
`ker Ψ_i = {(A,B) : A*f + B*g ∈ ℝ[X]_{< i}}`.

Write `D = gcd f g`, `δ = D.natDegree`, `f = D * f₁`, `g = D * g₁` (so `f₁ = f / gcd f g`,
`g₁ = g / gcd f g` are coprime; see `gsc_deg_fst`, `gsc_deg_snd`, `gsc_range_kerIota` in
`Submission.Work.WilE4.CAD.gcd_spec_natDegree_const_on_C`, which do the same computation for the
full Sylvester map and are importable).  If `A*f + B*g ∈ ℝ[X]_{< i}` and `δ ≥ i`, then
`A*f₁ + B*g₁ = 0` (else its degree would be `≥ δ ≥ i`), hence `A = g₁ * s`, `B = -f₁ * s`, and
`deg (g₁*s) < n-i` gives `deg s < δ - i`.  So when `i < δ` the kernel contains the nonzero element
`(g₁ * X^(δ-i-1), -f₁ * X^(δ-i-1))`, the map is not injective, and the determinant vanishes. -/
theorem psc_eq_zero_of_lt_gcd {f g : Polynomial ℝ} (hf : f ≠ 0) (hg : g ≠ 0) {i : ℕ}
    (hi : i < (gcd f g).natDegree) :
    Work.WilE4.CAD.psc f g f.natDegree g.natDegree i = 0 := by
  set D : Polynomial ℝ := gcd f g with hDdef
  have hiD : i < D.natDegree := by rw [hDdef]; exact hi
  have hDne : D ≠ 0 := by rw [hDdef]; exact gcd_ne_zero_of_left hf
  have hDdvd_f : D ∣ f := by rw [hDdef]; exact gcd_dvd_left f g
  have hDdvd_g : D ∣ g := by rw [hDdef]; exact gcd_dvd_right f g
  have hδf : (f / D).natDegree + D.natDegree = f.natDegree := by
    rw [hDdef]; exact gsc_deg_fst f g hf
  have hδg : (g / D).natDegree + D.natDegree = g.natDegree := by
    rw [hDdef]; exact gsc_deg_snd f g hf hg
  have hle_f : D.natDegree ≤ f.natDegree := Polynomial.natDegree_le_of_dvd hDdvd_f hf
  have hle_g : D.natDegree ≤ g.natDegree := Polynomial.natDegree_le_of_dvd hDdvd_g hg
  -- `u = f / D`, `w = g / D`; the pair `(A, B) = (w, -u)` is in the kernel of `Ψ_i`.
  set u : Polynomial ℝ := f / D with hudef
  set w : Polynomial ℝ := g / D with hwdef
  have h1 : D * u = f := by rw [hudef]; exact EuclideanDomain.mul_div_cancel' hDne hDdvd_f
  have h2 : D * w = g := by rw [hwdef]; exact EuclideanDomain.mul_div_cancel' hDne hDdvd_g
  have hprod : w * f + (-u) * g = 0 := by rw [← h1, ← h2]; ring
  have hunat : u.natDegree = (f / D).natDegree := by rw [hudef]
  have hwnat : w.natDegree = (g / D).natDegree := by rw [hwdef]
  have hAdeg : w.natDegree + i < g.natDegree := by rw [hwnat]; omega
  have hBdeg : (-u).natDegree + i < f.natDegree := by
    rw [Polynomial.natDegree_neg, hunat]; omega
  -- the vector of coefficients of `(A, B)` is nonzero
  have hw0 : w ≠ 0 := by rw [hwdef]; exact right_div_gcd_ne_zero hg
  have hwcoeff : w.coeff w.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hw0
  have hlt : w.natDegree < g.natDegree - i := by rw [hwnat]; omega
  have hlt' : w.natDegree < f.natDegree + g.natDegree - 2 * i := by omega
  have hv : (fun k : Fin (f.natDegree + g.natDegree - 2 * i) =>
      if (k : ℕ) < g.natDegree - i then w.coeff (k : ℕ)
      else (-u).coeff ((k : ℕ) - (g.natDegree - i))) ≠ 0 := by
    intro h0
    have hcongr := congrFun h0 ⟨w.natDegree, hlt'⟩
    simp only [ite_eq_left hlt] at hcongr
    exact hwcoeff hcongr
  -- hence the matrix is singular
  by_contra hdet
  have hker : Matrix.mulVec (pscMat f g f.natDegree g.natDegree i)
      (fun k : Fin (f.natDegree + g.natDegree - 2 * i) =>
        if (k : ℕ) < g.natDegree - i then w.coeff (k : ℕ)
        else (-u).coeff ((k : ℕ) - (g.natDegree - i))) = 0 := by
    funext r
    rw [pscZero_mulVec_eq_coeff f g le_rfl le_rfl w (-u) hAdeg hBdeg r, hprod]
    simp
  exact hv (Matrix.eq_zero_of_mulVec_eq_zero hdet hker)

end Work.WilE4.CAD
