import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.derVec_mem_span_iota
import Submission.Work.BW.applyDer_Qdesc_span
import Submission.Work.BW.QdescLemmas

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # `est21_l_vanish_n`: the `n`-operator family of the BW §16–17 chain rule

BW's chain rule `f^{(t')}(z;t'') = ∂₀^{t'_0}(b_n∂_1)^{t'_1}⋯(b_n∂_{n−1})^{t'_{n−1}} f` uses the
*`n`-operator* family `∂*_i = eulerDer (derVec b k L i)`, `i : Fin n`, whereas the descended
auxiliary polynomial `Q^{(J)}` is built from the `ι`-family `∂*_{ι m}`, `m : Fin (r-1)`
(`est21_l_vanish`).

Here we prove that the `lamP`-values of the `n`-family derivatives `∂₀^{a}∏_i(∂*_i)^{t'_i}Q^{(J)}`
vanish as soon as all twists of `Q^{(J)}` of order `≤ Tp + Tpp` do.

The mechanism: every `derVec b k L i` is a `ℚ`-combination of the `derVec b k L (ι m)`
(`derVec_mem_span_iota`). On a descended summand `Qdescbase J lm` the Euler operator `∂*_i` acts by
the scalar eigenvalue `γ_i(λ/2^J)`, and this eigenvalue is the corresponding `ℚ`-combination of the
`γ_{ι m}(λ/2^J)`. Expanding the resulting product of powers of linear forms in the monomial basis
(`linForm_pow_expand`) writes `∏_i (∂*_i)^{t'_i}` as a finite `ℂ`-combination of the `ι`-monomials
`∏_m (∂*_{ι m})^{d_m}` with `∑_m d_m ≤ ∑_i t'_i`; each of these is handled by
`est21_l_vanish_iota`, whose order hypothesis is implied by `hord`. -/

namespace Work.BW

open MvPolynomial

/-! ## The `n`-family of Euler derivations on the descended summands -/

/-- `eulerDer` on a `ℂ`-linear combination of descended summands, for an arbitrary row `i : Fin n`. -/
lemma eulerDer_sum_smul_Qdescbase_n {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (J : ℕ) (t0 : ℕ) (hm : Fin n) (a : AuxIdx r h D0 Dj → ℂ) :
    eulerDer (fun i => (derVec b k L hm i : ℚ))
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qdescbase h D0 Dj J lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * gam b k L hm (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) •
            Qdescbase h D0 Dj J lm t0 := by
  rw [eulerDer_sum]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [eulerDer_smul, eulerDer_Qdescbase, ← smul_mul_assoc, MvPolynomial.smul_eq_C_mul,
    ← MvPolynomial.C_mul, MvPolynomial.C_mul']

/-- Iterating the previous lemma. -/
lemma iterate_eulerDer_sum_smul_Qdescbase_n {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (J : ℕ) (t0 : ℕ) (hm : Fin n) (kk : ℕ) (a : AuxIdx r h D0 Dj → ℂ) :
    ((eulerDer (fun i => (derVec b k L hm i : ℚ)))^[kk])
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qdescbase h D0 Dj J lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * (gam b k L hm (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ kk) •
            Qdescbase h D0 Dj J lm t0 := by
  induction kk with
  | zero => simp
  | succ kk ih =>
    rw [Function.iterate_succ_apply', ih, eulerDer_sum_smul_Qdescbase_n]
    refine Finset.sum_congr rfl fun lm _ => ?_
    rw [pow_succ, mul_assoc]

/-- Iterating along a list of `n`-indices: the `l`-fold Euler differentiation multiplies the
coefficient of `Qdescbase lm` by the product of the eigenvalues. -/
lemma foldr_eulerDer_sum_smul_Qdescbase_n {n r : ℕ} (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (J : ℕ) (t0 : ℕ) (t : Fin n → ℕ) (l : List (Fin n)) (a : AuxIdx r h D0 Dj → ℂ) :
    l.foldr (fun i Q => (eulerDer (fun j => (derVec b k L i j : ℚ)))^[t i] Q)
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qdescbase h D0 Dj J lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * (l.map (fun i =>
              (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t i))).prod) •
            Qdescbase h D0 Dj J lm t0 := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, ih,
      iterate_eulerDer_sum_smul_Qdescbase_n]
    refine Finset.sum_congr rfl fun lm _ => ?_
    congr 1
    ring

/-! ## `gammaOf` is linear in the coefficient vector -/

/-- `gammaOf` is linear in the coefficient vector. -/
lemma gammaOf_sum_mul {r p : ℕ} (q : Fin p → ℚ) (E : Fin p → Fin r → ℚ) (e : Fin r → ℕ) :
    gammaOf (fun l => ∑ m, q m * E m l) e = ∑ m, (q m : ℂ) * gammaOf (E m) e := by
  simp only [gammaOf]
  push_cast
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The eigenvalue `γ_i(λ)` of `∂*_i` is the corresponding `ℚ`-combination of the eigenvalues
`γ_{ι m}(λ)` of the `ι`-family. -/
lemma gam_eq_sum_gam_of {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) (c : Fin n → Fin (r - 1) → ℚ) (i : Fin n) (e : Fin r → ℕ)
    (hc : ∀ l, (derVec b k L i l : ℚ) = ∑ m, c i m * (derVec b k L (ι m) l : ℚ)) :
    gam b k L i e = ∑ m, (c i m : ℂ) * gam b k L (ι m) e := by
  rw [gam_eq_gammaOf_apply]
  rw [show (fun l => (derVec b k L i l : ℚ))
        = fun l => ∑ m, c i m * (derVec b k L (ι m) l : ℚ) from funext hc]
  rw [gammaOf_sum_mul]
  exact Finset.sum_congr rfl fun m _ => by rw [gam_eq_gammaOf_apply]

/-! ## Multinomial expansion of a product of powers of linear forms -/

/-- Multinomial expansion of a product of powers of linear forms in the monomial basis of
`ℂ[x_0,…,x_{p-1}]`: there is a coefficient family `cc` on exponent vectors, supported in total
degree `≤ ∑ i, t i`, such that for every point `x : Fin p → ℂ` the product
`∏ i, (∑ m, q i m * x m)^{t i}` equals the finite monomial sum `∑ d, cc d * ∏ m, x m ^ (d m)`. -/
theorem linForm_pow_expand (p n : ℕ) (q : Fin n → Fin p → ℂ) (t : Fin n → ℕ) :
    ∃ cc : (Fin p → ℕ) → ℂ,
      (∀ d, ∑ i, t i < ∑ m, d m → cc d = 0) ∧
      ∀ x : Fin p → ℂ,
        ∏ i, (∑ m, q i m * x m) ^ (t i)
          = ∑ d ∈ Fintype.piFinset (fun _ : Fin p => Finset.range (∑ i, t i + 1)),
              cc d * ∏ m, (x m) ^ (d m) := by
  classical
  set Ψ : MvPolynomial (Fin p) ℂ :=
    ∏ i, (∑ m, MvPolynomial.C (q i m) * MvPolynomial.X m) ^ (t i) with hΨ
  -- `Ψ` is homogeneous of degree `∑ i, t i`
  have hhom : Ψ.IsHomogeneous (∑ i, t i) := by
    rw [hΨ, show (∑ i, t i) = ∑ i ∈ (Finset.univ : Finset (Fin n)), 1 * t i by simp]
    refine MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => ?_)
    exact (MvPolynomial.IsHomogeneous.sum _ _ 1
      (fun m _ => MvPolynomial.isHomogeneous_C_mul_X (q i m) m)).pow (t i)
  -- evaluating `Ψ` at `x` gives the left-hand side
  have hLHS : ∀ x : Fin p → ℂ,
      MvPolynomial.eval x Ψ = ∏ i, (∑ m, q i m * x m) ^ (t i) := by
    intro x
    rw [hΨ]
    simp only [map_prod, map_pow, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  refine ⟨fun d => Ψ.coeff (Finsupp.equivFunOnFinite.symm d), ?_, ?_⟩
  · -- the support condition is the total-degree bound
    intro d hd
    refine MvPolynomial.IsHomogeneous.coeff_eq_zero hhom ?_
    rw [Finsupp.degree_eq_sum]
    intro hc
    have h2 : (∑ m, (Finsupp.equivFunOnFinite.symm d) m) = ∑ m, d m :=
      Finset.sum_congr rfl fun m _ => by rw [Finsupp.coe_equivFunOnFinite_symm]
    omega
  · intro x
    rw [← hLHS x, MvPolynomial.eval_eq' x Ψ]
    set box : Finset (Fin p → ℕ) :=
      Fintype.piFinset (fun _ : Fin p => Finset.range (∑ i, t i + 1)) with hbox
    have himg : Ψ.support.image (⇑Finsupp.equivFunOnFinite) ⊆ box := by
      intro d hd
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      rw [hbox, Fintype.mem_piFinset]
      intro m
      have h4 : e m ≤ ∑ i, t i := by
        have h2 : e.degree ≤ Ψ.totalDegree := by
          have hsum : e.sum (fun _ e => e) = ∑ i, e i :=
            Finsupp.sum_fintype e (fun _ e => e) (fun i => rfl)
          rw [Finsupp.degree_eq_sum, ← hsum]
          exact MvPolynomial.le_totalDegree he
        calc e m ≤ e.degree := Finsupp.le_degree m e
          _ ≤ Ψ.totalDegree := h2
          _ ≤ ∑ i, t i := hhom.totalDegree_le
      have h5 : (Finsupp.equivFunOnFinite e) m = e m := Finsupp.equivFunOnFinite_apply e m
      exact Finset.mem_range.mpr (by omega)
    have hzero : ∀ d ∈ box, d ∉ Ψ.support.image (⇑Finsupp.equivFunOnFinite) →
        Ψ.coeff (Finsupp.equivFunOnFinite.symm d) * ∏ m, (x m) ^ (d m) = 0 := by
      intro d _ hd
      have hnot : Finsupp.equivFunOnFinite.symm d ∉ Ψ.support := by
        intro hmem
        exact hd (Finset.mem_image.mpr ⟨Finsupp.equivFunOnFinite.symm d, hmem,
          Finsupp.equivFunOnFinite.apply_symm_apply d⟩)
      rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]
    have hkey : (∑ e ∈ Ψ.support, Ψ.coeff e * ∏ m, (x m) ^ (e m))
        = ∑ e ∈ Ψ.support,
            Ψ.coeff (Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite e))
              * ∏ m, (x m) ^ ((Finsupp.equivFunOnFinite e) m) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finsupp.equivFunOnFinite.symm_apply_apply]
      refine congrArg (fun t : ℂ => Ψ.coeff e * t) ?_
      refine Finset.prod_congr rfl fun m _ => ?_
      exact congrArg (fun c : ℕ => (x m) ^ c) (Finsupp.equivFunOnFinite_apply e m).symm
    rw [hkey, ← Finset.sum_image (s := Ψ.support) (g := (⇑Finsupp.equivFunOnFinite))
      (f := fun d => Ψ.coeff (Finsupp.equivFunOnFinite.symm d) * ∏ m, (x m) ^ (d m))
      Finsupp.equivFunOnFinite.injective.injOn]
    exact Finset.sum_subset himg hzero

/-! ## `∂₀^{a}∏(∂*)^{t}` on the descended polynomial -/

/-- `∂₀^{a}∏_{i:Fin n}(∂*_i)^{t'_i} Q^{(J)}(·;t₀,t)` as an explicit `ℂ`-linear combination of the
descended summands `Qdescbase J lm (a+t₀)`: the eigenvalue of `∂*_i` on the `lm`-summand is
`γ_i(⌊λ/2^J⌋)`, and `∂₀^{a}` contributes `a!(2^{-J})^a·binom(a+t₀,a)` and raises `t₀` to `t₀+a`. -/
lemma applyDer_n_Qdesc_eq_sum {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (a : ℕ) (t' : Fin n → ℕ) :
    applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (Qdesc φ b k L ι h D0 Dj p J μ t0 t)
      = ∑ lm : AuxIdx r h D0 Dj,
          ((if ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j then
              φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
                * (ulcm h : ℂ) ^ t0 else 0)
            * (∏ i, (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i))
            * ((a.factorial : ℂ) * (((2 : ℂ) ^ J)⁻¹) ^ a * ((Nat.choose (a + t0) a : ℕ) : ℂ)))
          • Qdescbase h D0 Dj J lm (a + t0) := by
  rw [applyDer, Qdesc_eq_sum_Qdescbase, foldr_eulerDer_sum_smul_Qdescbase_n,
    pderiv0_pow_sum_smul_Qdescbase_gen]
  simp only [finRange_map_prod]

/-- The same for the `ι`-family. -/
lemma applyDer_iota_Qdesc_eq_sum {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (a : ℕ) (d : Fin (r - 1) → ℕ) :
    applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) a d (Qdesc φ b k L ι h D0 Dj p J μ t0 t)
      = ∑ lm : AuxIdx r h D0 Dj,
          ((if ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j then
              φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
                * (ulcm h : ℂ) ^ t0 else 0)
            * (∏ m, (gam b k L (ι m) (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (d m))
            * ((a.factorial : ℂ) * (((2 : ℂ) ^ J)⁻¹) ^ a * ((Nat.choose (a + t0) a : ℕ) : ℂ)))
          • Qdescbase h D0 Dj J lm (a + t0) := by
  rw [applyDer, Qdesc_eq_sum_Qdescbase, foldr_eulerDer_sum_smul_Qdescbase,
    pderiv0_pow_sum_smul_Qdescbase_gen]
  simp only [finRange_map_prod]

/-! ## The `n`-family as a combination of `ι`-monomials -/

/-- **The reduction of the `n`-family to the `ι`-family.**  With `c` the coefficients of the
`derVec b k L i` in the basis of the `derVec b k L (ι m)`, the `n`-derivative
`∂₀^{a}∏_i(∂*_i)^{t'_i}Q^{(J)}(·;t₀,t)` is a finite `ℂ`-combination of the `ι`-derivatives
`∂₀^{a}∏_m(∂*_{ι m})^{d_m}Q^{(J)}(·;t₀,t)` with `∑_m d_m ≤ ∑_i t'_i`. -/
lemma applyDer_n_Qdesc_eq_sum_iota {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (a : ℕ) (t' : Fin n → ℕ) (c : Fin n → Fin (r - 1) → ℚ)
    (hc : ∀ i l, (derVec b k L i l : ℚ) = ∑ m, c i m * (derVec b k L (ι m) l : ℚ)) :
    ∃ cc : (Fin (r - 1) → ℕ) → ℂ,
      (∀ d, ∑ i, t' i < ∑ m, d m → cc d = 0) ∧
      applyDer (fun i j => (derVec b k L i j : ℚ)) a t'
          (Qdesc φ b k L ι h D0 Dj p J μ t0 t)
        = ∑ d ∈ Fintype.piFinset (fun _ : Fin (r - 1) => Finset.range (∑ i, t' i + 1)),
            cc d • applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) a d
              (Qdesc φ b k L ι h D0 Dj p J μ t0 t) := by
  classical
  obtain ⟨cc, hcc0, hcc⟩ := linForm_pow_expand (r - 1) n (fun i m => (c i m : ℂ)) t'
  refine ⟨cc, hcc0, ?_⟩
  rw [applyDer_n_Qdesc_eq_sum φ b k L ι h D0 Dj p J μ t0 t a t']
  have hstep : ∀ d ∈ Fintype.piFinset (fun _ : Fin (r - 1) => Finset.range (∑ i, t' i + 1)),
      cc d • applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) a d
          (Qdesc φ b k L ι h D0 Dj p J μ t0 t)
        = ∑ lm : AuxIdx r h D0 Dj,
            (cc d * ((if ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j then
                φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m))
                  * (ulcm h : ℂ) ^ t0 else 0)
              * (∏ m, (gam b k L (ι m) (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (d m))
              * ((a.factorial : ℂ) * (((2 : ℂ) ^ J)⁻¹) ^ a
                  * ((Nat.choose (a + t0) a : ℕ) : ℂ)))) •
              Qdescbase h D0 Dj J lm (a + t0) := by
    intro d _
    rw [applyDer_iota_Qdesc_eq_sum φ b k L ι h D0 Dj p J μ t0 t a d, Finset.smul_sum]
    exact Finset.sum_congr rfl fun lm _ => by rw [smul_smul]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [← Finset.sum_smul]
  refine congrArg (fun t : ℂ => t • Qdescbase h D0 Dj J lm (a + t0)) ?_
  -- the scalar identity, summand by summand
  have hgam : ∏ i, (gam b k L i (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (t' i)
      = ∑ d ∈ Fintype.piFinset (fun _ : Fin (r - 1) => Finset.range (∑ i, t' i + 1)),
          cc d * ∏ m, (gam b k L (ι m) (fun j => (lm.2.2 j : ℕ) / 2 ^ J)) ^ (d m) := by
    rw [← hcc (fun m => gam b k L (ι m) (fun j => (lm.2.2 j : ℕ) / 2 ^ J))]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact congrArg (fun z : ℂ => z ^ (t' i)) (gam_eq_sum_gam_of b k L ι c i _ (hc i))
  rw [hgam, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => by ring

/-! ## `fAt` is linear in the polynomial -/

lemma fAt_sum_red {r : ℕ} (ℓ : Fin r → ℂ) (z : ℂ) {ι' : Type*} (s : Finset ι')
    (f : ι' → MvPolynomial (Fin (r + 1)) ℂ) :
    fAt ℓ (∑ i ∈ s, f i) z = ∑ i ∈ s, fAt ℓ (f i) z := by
  simp only [fAt, MvPolynomial.eval_sum]

lemma fAt_smul_red {r : ℕ} (ℓ : Fin r → ℂ) (z : ℂ) (w : ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) :
    fAt ℓ (w • P) z = w * fAt ℓ P z := by
  simp only [fAt, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]

/-! ## Vanishing for the `ι`-family -/

/-- BW §16/§17 (p. 47–49), `g^{(t')}(l;t'') = 0` for the `ι`-operator family: if all twists of
`Q^{(J)}` of order `≤ Tp + Tpp` vanish at the `lamP`-point `l`, then so does
`∂₀^{a}∏_{m}(∂*_{ι m})^{t'_m} Q^{(J)}(·;t₀,t)` whenever `t₀ + a + Σt' + Σt ≤ Tp + Tpp`.
`applyDer_Qdesc_span` writes the derivative as a `ℂ`-combination of the twists
`Q^{(J)}(·;t₀+a,t''')` with `Σt''' ≤ Σt + Σt'`; each of those is killed by `hvan`. -/
theorem est21_l_vanish_iota {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ) (Tp Tpp : ℝ) (l : ℂ)
    (hvan : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ), ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ Tp + Tpp →
      acg φ α b k L ι v σ p J μ t0' t' l = 0)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (a : ℕ) (t' : Fin (r - 1) → ℕ)
    (hord : ((t0 + a + ∑ m, t' m + ∑ m, t m : ℕ) : ℝ) ≤ Tp + Tpp) :
    fAt (fun j => lamP φ α v L j)
      (applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) l = 0 := by
  classical
  obtain ⟨cc, hcc⟩ := applyDer_Qdesc_span φ b k L ι (acH K b v) (pD0 r (dK K) σ)
    (pDj r (dK K) σ) p J μ a t' t0 t
  rw [hcc, fAt_sum_red]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [fAt_smul_red]
  have hle : (∑ m, (u m : ℕ)) ≤ ∑ m, t' m + ∑ m, t m := (Finset.mem_filter.mp hu).2
  have hbound : (((a + t0) + ∑ m, (u m : ℕ) : ℕ) : ℝ) ≤ Tp + Tpp := by
    have h2 : a + t0 + ∑ m, (u m : ℕ) ≤ t0 + a + ∑ m, t' m + ∑ m, t m := by omega
    exact le_trans (by exact_mod_cast h2) hord
  have hv : fAt (fun j => lamP φ α v L j)
      (QJ φ b k L ι v σ p J μ (a + t0) (fun m => (u m : ℕ))) l = 0 :=
    hvan (a + t0) (fun m => (u m : ℕ)) hbound
  rw [hv, mul_zero]

/-- BW (1993) §17, p. 49, the `n`-operator family: the `lamP`-value at `l` of
`∂₀^a ∏ᵢ (∂*_i)^{t'_i} Q^{(J)}(·;t0,t)` (`∂*_i = eulerDer (derVec b k L i ·)`, all `n` coordinate
operators, as produced by BW's chain rule) vanishes whenever the total order
`t0 + a + Σt' + Σt ≤ T' + T''`.  Reduction to the proved `est21_l_vanish` (the `ι`-family):
`derVec_mem_span_iota` writes each coefficient vector `derVec b k L i (·)` as a ℚ-combination of the
`r−1` vectors `derVec b k L (ι m) (·)`, so each `eulerDer (derVec b k L i ·)` is a ℂ-combination of
the `eulerDer (derVec b k L (ι m) ·)`; expanding the operator monomial gives a ℂ-linear combination
of `ι`-monomials of the same total order `Σt'`, each of which has `lamP`-value `0` by
`est21_l_vanish`.  (The sibling node `BW/est21_l_vanish_n` states the same thing and is proved, but
its module clashes with `Submission.Work.BW.taylorC_aux` on the declaration name `Work.BW.fAt_sum`,
so the live `est21_l` assembly uses this copy instead.) -/
theorem est21_l_vanish_n_red {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ) (Tp Tpp : ℝ) (l : ℂ)
    (hvan : ∀ (t0' : ℕ) (t' : Fin (r - 1) → ℕ), ((t0' + ∑ m, t' m : ℕ) : ℝ) ≤ Tp + Tpp →
      acg φ α b k L ι v σ p J μ t0' t' l = 0)
    (t0 : ℕ) (t : Fin (r - 1) → ℕ) (a : ℕ) (t' : Fin n → ℕ)
    (hord : ((t0 + a + ∑ i, t' i + ∑ m, t m : ℕ) : ℝ) ≤ Tp + Tpp) :
    fAt (fun j => lamP φ α v L j)
      (applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) l = 0 := by
  classical
  -- the coefficient vector of `derVec b k L i` in the span of the `derVec b k L (ι m)`
  have hspan : ∀ i : Fin n, ∃ c : Fin (r - 1) → ℚ,
      ∑ m, c m • (fun l => (derVec b k L (ι m) l : ℚ)) = (fun l => (derVec b k L i l : ℚ)) :=
    fun i => (Submodule.mem_span_range_iff_exists_fun ℚ).mp
      (derVec_mem_span_iota H.hBH H.hι H.hr i)
  choose c hc using hspan
  have hc' : ∀ i l, (derVec b k L i l : ℚ) = ∑ m, c i m * (derVec b k L (ι m) l : ℚ) := by
    intro i l
    have h := congrFun (hc i) l
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  obtain ⟨cc, hcc0, hmain⟩ := applyDer_n_Qdesc_eq_sum_iota φ b k L ι (acH K b v)
    (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t a t' c hc'
  have hgoal : fAt (fun j => lamP φ α v L j)
        (applyDer (fun i j => (derVec b k L i j : ℚ)) a t' (QJ φ b k L ι v σ p J μ t0 t)) l
      = ∑ d ∈ Fintype.piFinset (fun _ : Fin (r - 1) => Finset.range (∑ i, t' i + 1)),
          cc d * fAt (fun j => lamP φ α v L j)
            (applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) a d
              (QJ φ b k L ι v σ p J μ t0 t)) l := by
    rw [hmain, fAt_sum_red]
    exact Finset.sum_congr rfl fun d _ => fAt_smul_red _ _ _ _
  rw [hgoal]
  refine Finset.sum_eq_zero fun d hd => ?_
  by_cases hcd : cc d = 0
  · rw [hcd, zero_mul]
  · have hdle : (∑ m, d m) ≤ ∑ i, t' i := by
      by_contra hcon
      exact hcd (hcc0 d (not_le.mp hcon))
    have hord' : ((t0 + a + ∑ m, d m + ∑ m, t m : ℕ) : ℝ) ≤ Tp + Tpp := by
      have h2 : t0 + a + ∑ m, d m + ∑ m, t m ≤ t0 + a + ∑ i, t' i + ∑ m, t m := by omega
      exact le_trans (by exact_mod_cast h2) hord
    rw [est21_l_vanish_iota H J μ Tp Tpp l hvan t0 t a d hord', mul_zero]

end Work.BW
