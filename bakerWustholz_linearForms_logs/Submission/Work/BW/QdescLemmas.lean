import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.applyDer_Qpoly_span
import Submission.Work.BW.QdescBase
import Submission.Work.BW.pderiv0_pow_aeval_scaled
import Submission.Work.BW.pderiv_succ_aeval_scaled
import Submission.Work.BW.Delta_mul_affine_pow_expansion
import Submission.Work.BW.sum_box_prod_beta_Delta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Calculus of the summands of the descended polynomial `Q^{(J)}` (BW §16, §20)

The descended auxiliary polynomial
`Qdesc φ b k L ι h D0 Dj p J μ t0 t = ∑_{lm} c_{lm} • (dy0part lm t0 * dymon lm)` is a sum
of `lm : AuxIdx` with `λ(lm)_j ≡ μ_j (mod 2^J)`.  Here we collect the two structural facts
that make `∂₀^{t₀}∏_m∂*_m^{t_m}` act on it:

* `eulerDer` is blind to the `Y₀`-part `dy0part` and scales the descended torus monomial
  `dymon` by `γ(⌊λ/2^J⌋)` (`eulerDer_dy0part`, `eulerDer_Qdescbase`, and the iterated
  `foldr` form);
* `∂/∂Y₀` on the descended `Y₀`-part is `k! (2^{-J})^k` times the Hasse derivative, by the
  scaled chain rule `pderiv0_pow_aeval_scaled` (`pderiv0_pow_Qdescbase_gen`).

Together with `Qdesc_eq_sum_Qdescbase` these reduce the span statement to the scalar identity
of `applyDer_Qdesc_span`. -/

namespace Work.BW

/-! ## `gam` is `gammaOf` of the `derVec` row -/

/-- `gam` depends only on the `derVec` row: it is `gammaOf` of that row (general exponents). -/
lemma gam_eq_gammaOf_apply {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (j : Fin n) (μ : Fin r → ℕ) :
    gam b k L j μ = gammaOf (fun i => (derVec b k L j i : ℚ)) μ := by
  simp only [gam, gammaOf]
  push_cast
  rfl

/-! ## The `ℚ`- and `ℂ`-actions agree -/

/-- `ℚ`-scalars and their images in `ℂ` act in the same way on `ℂ[Y₀,…,Y_r]`. -/
lemma rat_smul_eq_complex_smul {r : ℕ} (q : ℚ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    q • P = (q : ℂ) • P := by
  rw [show (q : ℂ) • P = (q • (1 : ℂ)) • P from by rw [Rat.smul_one_eq_cast],
    IsScalarTower.smul_assoc, one_smul]

/-! ## `eulerDer` on the descended summands -/

/-- `eulerDer` kills the descended `Y₀`-part `dy0part J h c₀ d t0`. -/
lemma eulerDer_dy0part {r : ℕ} (J h d t0 : ℕ) (c₀ : ℂ) (c : Fin r → ℚ) :
    eulerDer c (dy0part J h c₀ d t0) = 0 := by
  simp only [eulerDer, dy0part, pderiv_succ_aeval_scaled, mul_zero, Finset.sum_const_zero]

/-- The Euler derivation scales the descended torus monomial by `γ(⌊λ/2^J⌋)`, i.e. acts on
`Qdescbase` by the scalar `gammaOf c (fun j => λ_j / 2^J)`. -/
lemma eulerDer_Qdescbase_raw {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (J : ℕ)
    (lm : AuxIdx r h D0 Dj) (t0 : ℕ) (c : Fin r → ℚ) :
    eulerDer c (Qdescbase h D0 Dj J lm t0)
      = MvPolynomial.C (gammaOf c (fun j => (lm.2.2 j : ℕ) / 2 ^ J))
          * Qdescbase h D0 Dj J lm t0 := by
  rw [Qdescbase, eulerDer_mul, eulerDer_dy0part, zero_mul, zero_add, dymon, eulerDer_ymon]
  ring

/-- The same with the eigenvalue written as `gam b k L j (⌊λ/2^J⌋)`. -/
lemma eulerDer_Qdescbase {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (j : Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (J : ℕ) (lm : AuxIdx r h D0 Dj) (t0 : ℕ) :
    eulerDer (fun i => (derVec b k L j i : ℚ)) (Qdescbase h D0 Dj J lm t0)
      = MvPolynomial.C (gam b k L j (fun i => (lm.2.2 i : ℕ) / 2 ^ J))
          * Qdescbase h D0 Dj J lm t0 := by
  rw [eulerDer_Qdescbase_raw, gam_eq_gammaOf_apply]

/-- `eulerDer` on a `ℂ`-linear combination of descended summands. -/
lemma eulerDer_sum_smul_Qdescbase {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (J : ℕ) (t0 : ℕ) (hm : Fin (r - 1)) (a : AuxIdx r h D0 Dj → ℂ) :
    eulerDer (fun i => (derVec b k L (ι hm) i : ℚ))
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qdescbase h D0 Dj J lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * gam b k L (ι hm) (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) •
            Qdescbase h D0 Dj J lm t0 := by
  rw [eulerDer_sum]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [eulerDer_smul, eulerDer_Qdescbase, ← smul_mul_assoc, MvPolynomial.smul_eq_C_mul,
    ← MvPolynomial.C_mul, MvPolynomial.C_mul']

/-- Iterating the previous lemma. -/
lemma iterate_eulerDer_sum_smul_Qdescbase {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (J : ℕ) (t0 : ℕ) (hm : Fin (r - 1)) (kk : ℕ) (a : AuxIdx r h D0 Dj → ℂ) :
    ((eulerDer (fun i => (derVec b k L (ι hm) i : ℚ)))^[kk])
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qdescbase h D0 Dj J lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * (gam b k L (ι hm) (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ kk) •
            Qdescbase h D0 Dj J lm t0 := by
  induction kk with
  | zero => simp
  | succ kk ih =>
    rw [Function.iterate_succ_apply', ih, eulerDer_sum_smul_Qdescbase]
    refine Finset.sum_congr rfl fun lm _ => ?_
    rw [pow_succ, mul_assoc]

/-- Iterating along a list of indices: the `l`-fold Euler differentiation multiplies the
coefficient of `Qdescbase lm` by the product of the eigenvalues. -/
lemma foldr_eulerDer_sum_smul_Qdescbase {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (J : ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (l : List (Fin (r - 1)))
    (a : AuxIdx r h D0 Dj → ℂ) :
    l.foldr (fun m Q => (eulerDer (fun i => (derVec b k L (ι m) i : ℚ)))^[t m] Q)
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qdescbase h D0 Dj J lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * (l.map (fun m =>
              (gam b k L (ι m) (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t m))).prod) •
            Qdescbase h D0 Dj J lm t0 := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, ih,
      iterate_eulerDer_sum_smul_Qdescbase]
    refine Finset.sum_congr rfl fun lm _ => ?_
    congr 1
    ring

/-! ## `∂/∂Y₀` on the descended summands -/

/-- `∂/∂Y₀` is `ℂ`-linear on finite sums of scalar multiples. -/
lemma pderiv0_sum_smul {r : ℕ} {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (P : ι → MvPolynomial (Fin (r + 1)) ℂ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1))) (∑ i ∈ s, a i • P i)
      = ∑ i ∈ s, a i • (MvPolynomial.pderiv (0 : Fin (r + 1))) (P i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul])

/-- Iterated `∂/∂Y₀` on a finite sum of scalar multiples. -/
lemma pderiv0_pow_sum_smul {r : ℕ} (kk : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (P : ι → MvPolynomial (Fin (r + 1)) ℂ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[kk] (∑ i ∈ s, a i • P i)
      = ∑ i ∈ s, a i • (MvPolynomial.pderiv (0 : Fin (r + 1)))^[kk] (P i) := by
  induction kk with
  | zero => simp
  | succ kk ih =>
    rw [Function.iterate_succ_apply', ih, pderiv0_sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.iterate_succ_apply']

/-- The Hasse-derivative composition identity, evaluated at `Z` (the scalar is a natural
number cast to `ℂ`, so that it can be combined with the other complex coefficients). -/
lemma aeval_hasseDeriv_comp {r : ℕ} (Z : MvPolynomial (Fin (r + 1)) ℂ) (q : Polynomial ℚ)
    (kk l : ℕ) :
    Polynomial.aeval Z (Polynomial.hasseDeriv kk (Polynomial.hasseDeriv l q))
      = ((Nat.choose (kk + l) kk : ℕ) : ℂ) •
          Polynomial.aeval Z (Polynomial.hasseDeriv (kk + l) q) := by
  have hcomp : Polynomial.hasseDeriv kk (Polynomial.hasseDeriv l q)
      = ((Nat.choose (kk + l) kk : ℕ) : ℚ) • Polynomial.hasseDeriv (kk + l) q := by
    have h := DFunLike.congr_fun (Polynomial.hasseDeriv_comp (R := ℚ) kk l) q
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
    rw [h]
    exact (Nat.cast_smul_eq_nsmul ℚ ((kk + l).choose kk)
      (Polynomial.hasseDeriv (kk + l) q)).symm
  rw [hcomp, map_smul (Polynomial.aeval Z), rat_smul_eq_complex_smul]
  congr 1

/-- `∂/∂Y₀` iterated on a single descended summand: the two Hasse derivatives combine, and the
descended `Y₀`-variable contributes the factor `(2^{-J})^k`. -/
lemma pderiv0_pow_Qdescbase_gen {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (J : ℕ)
    (lm : AuxIdx r h D0 Dj) (t0'' kk : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[kk] (Qdescbase h D0 Dj J lm t0'')
      = ((kk.factorial : ℂ) * (((2 : ℂ) ^ J)⁻¹) ^ kk
            * ((Nat.choose (kk + t0'') kk : ℕ) : ℂ)) •
          Qdescbase h D0 Dj J lm (kk + t0'') := by
  have hM : (MvPolynomial.pderiv (0 : Fin (r + 1)))
      (dymon J (fun j => (lm.2.2 j : ℕ))) = 0 :=
    pderiv_zero_ymon _
  rw [Qdescbase, pderiv0_pow_mul_of_eq_zero kk hM, dy0part, pderiv0_pow_aeval_scaled,
    aeval_hasseDeriv_comp, smul_smul, smul_mul_assoc]
  simp only [Qdescbase, dy0part, dymon]

/-- Iterated `∂/∂Y₀` on a `ℂ`-linear combination of descended summands. -/
lemma pderiv0_pow_sum_smul_Qdescbase_gen {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (J : ℕ)
    (t0'' kk : ℕ) (a : AuxIdx r h D0 Dj → ℂ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[kk]
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qdescbase h D0 Dj J lm t0'')
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * ((kk.factorial : ℂ) * (((2 : ℂ) ^ J)⁻¹) ^ kk
            * ((Nat.choose (kk + t0'') kk : ℕ) : ℂ))) •
          Qdescbase h D0 Dj J lm (kk + t0'') := by
  rw [pderiv0_pow_sum_smul]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [pderiv0_pow_Qdescbase_gen, smul_smul]

/-! ## The eigenvalue as an affine function of `γ(λ)` -/

/-- If `λᵢ ≡ μᵢ (mod 2^J)` for every `i`, then `γ(⌊λ/2^J⌋) = (γ(λ) − γ(μ))/2^J`:  the eigenvalue
of the Euler operator on the descended monomial is an affine function of `γ(λ)` with
`λ`-independent coefficients. -/
lemma gam_div_pow_eq {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (j : Fin n) (μ lam : Fin r → ℕ) (J : ℕ) (hlam : ∀ i, lam i % 2 ^ J = μ i) :
    gam b k L j (fun i => lam i / 2 ^ J)
      = (gam b k L j lam - gam b k L j μ) * (((2 : ℂ) ^ J)⁻¹) := by
  have hterm : ∀ i : Fin r, (((lam i / 2 ^ J : ℕ)) : ℂ)
      = (((lam i : ℕ) : ℂ) - ((μ i : ℕ) : ℂ)) * (((2 : ℂ) ^ J)⁻¹) := by
    intro i
    have hd := Nat.div_add_mod (lam i) (2 ^ J)
    rw [hlam i] at hd
    have hcast : ((2 : ℂ) ^ J) * (((lam i / 2 ^ J : ℕ)) : ℂ) + ((μ i : ℕ) : ℂ)
        = ((lam i : ℕ) : ℂ) := by
      have h := congrArg (fun t : ℕ => (t : ℂ)) hd
      push_cast at h
      simpa using h
    have h2 : ((2 : ℂ) ^ J) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hsub : ((lam i : ℕ) : ℂ) - ((μ i : ℕ) : ℂ)
        = ((2 : ℂ) ^ J) * (((lam i / 2 ^ J : ℕ)) : ℂ) := by
      rw [← hcast]; ring
    rw [hsub, mul_comm (((2 : ℂ) ^ J)), mul_assoc, mul_inv_cancel₀ h2, mul_one]
  have hcoe : ∀ i : Fin r, (((derVec b k L j i : ℚ) : ℂ) * (((lam i / 2 ^ J : ℕ)) : ℂ))
      = ((((derVec b k L j i : ℚ) : ℂ) * ((lam i : ℕ) : ℂ)
          - ((derVec b k L j i : ℚ) : ℂ) * ((μ i : ℕ) : ℂ)) * (((2 : ℂ) ^ J)⁻¹)) := by
    intro i
    rw [hterm i]
    ring
  rw [gam_eq_gammaOf_apply, gam_eq_gammaOf_apply, gam_eq_gammaOf_apply]
  simp only [gammaOf]
  rw [Finset.sum_congr rfl (fun i _ => hcoe i)]
  rw [show (∑ i : Fin r, ((((derVec b k L j i : ℚ) : ℂ) * ((lam i : ℕ) : ℂ)
        - ((derVec b k L j i : ℚ) : ℂ) * ((μ i : ℕ) : ℂ)) * (((2 : ℂ) ^ J)⁻¹)))
      = ∑ i : Fin r, ((((derVec b k L j i : ℚ) : ℂ) * ((lam i : ℕ) : ℂ)) * (((2 : ℂ) ^ J)⁻¹)
        - (((derVec b k L j i : ℚ) : ℂ) * ((μ i : ℕ) : ℂ)) * (((2 : ℂ) ^ J)⁻¹))
    from Finset.sum_congr rfl (fun i _ => by ring)]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sub_mul]

/-! ## `Qdesc` as a combination of the `Qdescbase` -/

/-- `Qdesc` is the `ℂ`-linear combination of the `Qdescbase h D0 Dj J lm t0` over the `lm` whose
residue is `μ`, with coefficient `φ(p_lm)∏_m Δ(γ_m(λ);t_m)·u(h)^{t₀}`. -/
lemma Qdesc_eq_sum_Qdescbase {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ) :
    Qdesc φ b k L ι h D0 Dj p J μ t0 t
      = ∑ lm : AuxIdx r h D0 Dj,
          (if ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j then
            φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
              * (ulcm h : ℂ) ^ t0
           else 0) • Qdescbase h D0 Dj J lm t0 := by
  simp only [Qdesc, Qdescbase, dy0part, dymon, ymon, MvPolynomial.C_mul']
  refine Finset.sum_congr rfl fun lm _ => ?_
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [if_pos hc, if_pos hc, smul_mul_assoc]
  · rw [if_neg hc, if_neg hc, zero_smul]

end Work.BW
