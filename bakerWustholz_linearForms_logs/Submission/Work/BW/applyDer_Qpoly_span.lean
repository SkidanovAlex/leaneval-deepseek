import Mathlib
import Submission.Work.BW.ACBase
import Submission.Work.BW.sum_fin_box_eq_sum_piFinset
import Submission.Work.BW.X_succ_mul_pderiv_prod_X_succ_pow
import Submission.Work.BW.pderiv_succ_aeval_Y0
import Submission.Work.BW.pderiv0_pow_aeval_Y0
import Submission.Work.BW.Delta_pow_expansion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# BW §16 differential Lemma 6, span form

We show that `∂₀^{t₀} ∏_m ∂*_m^{t_m}` applied to the auxiliary polynomial `Q(·;0)` is a finite
ℂ-linear combination of the twists `Q(· ; t₀, t')` with `∑_m t'_m ≤ ∑_m t_m`.

The proof is a direct computation with the explicit shape of `Qpoly`:

* `Qpoly p 0 0 = ∑_λ φ(p_λ) • B_λ` where `B_λ = A_λ^{(0)}·∏_j Y_j^{λ_j}` and `A_λ^{(t₀)}` is the
  scalar `Y₀`-polynomial `(Θ(·; h, λ₀+1, t₀))`;
* each `eulerDer (c_m)` acts on `B_λ` by multiplication with `γ_m(λ) = ∑_i c_m i λ_i`, since the
  `eulerDer` are Euler derivations in the torus variables `Y_1,…,Y_r` and are blind to `Y₀`;
* `(pderiv 0)^{t₀}` acts on the `Y₀`-part by `t₀!·hasseDeriv t₀`, and kills the monomial part;
* the resulting coefficients `∏_m γ_m(λ)^{t_m}·t₀!` are rewritten as a ℂ-linear combination of
  products `∏_m Δ(γ_m(λ); t'_m)` (binomial-basis expansion of `z^k`, `Δ(z;j) = binom(z+j,j)`),
  which is exactly the coefficient of `Qpoly p t₀ t'`.
-/

namespace Work.BW

/-! ## The monomial and `Y₀`-parts of `Qpoly` -/

/-- The torus monomial `∏_{j} Y_j^{μ_j}`, with `Y_j = X (j+1)`. -/
noncomputable def ymon {r : ℕ} (μ : Fin r → ℕ) : MvPolynomial (Fin (r + 1)) ℂ :=
  ∏ j : Fin r, MvPolynomial.X j.succ ^ (μ j)

/-- The `Y₀`-part of a summand of `Qpoly`: the value at `Y₀ + c₀` of the ``d``-th power of
`deltaPoly h`, differentiated `t₀` times in the Hasse sense. -/
noncomputable def y0part {r : ℕ} (h : ℕ) (c₀ : ℂ) (d : ℕ) (t0 : ℕ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c₀)
    (Polynomial.hasseDeriv t0 (deltaPoly h ^ d))

/-- `γ(μ) = ∑_i c_i μ_i`, the factor by which the Euler derivation `eulerDer c` scales the torus
monomial `∏_j Y_j^{μ_j}`. -/
noncomputable def gammaOf {r : ℕ} (c : Fin r → ℚ) (μ : Fin r → ℕ) : ℂ :=
  ∑ i, (c i : ℂ) * (μ i : ℂ)

/-- The `λ`-summand of `Qpoly`: the `Y₀`-part times the torus monomial, as a bare polynomial. -/
noncomputable def Qbase {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ)
    (lm : AuxIdx r h D0 Dj) (t0 : ℕ) : MvPolynomial (Fin (r + 1)) ℂ :=
  y0part h ((lm.1 : ℕ) : ℂ) ((lm.2.1 : ℕ) + 1) t0 * ymon (fun j => (lm.2.2 j : ℕ))

/-- `Qpoly` is a ℂ-linear combination of the `Qbase h D0 Dj lm t0`. -/
lemma Qpoly_eq_sum_Qbase {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (t0 : ℕ) (t : Fin (r - 1) → ℕ) :
    Qpoly φ b k L ι α' h D0 Dj p t0 t
      = ∑ lm : AuxIdx r h D0 Dj,
          (φ (p lm) *
              (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
              (ulcm h : ℂ) ^ t0) • Qbase h D0 Dj lm t0 := by
  simp only [Qpoly, Qbase, ymon, y0part, MvPolynomial.C_mul']
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [smul_mul_assoc]

/-! ## Small facts about `Delta`, `ulcm` and `gam` -/

lemma Delta_zero (z : ℂ) : Delta z 0 = 1 := by
  simp [Delta, deltaPoly]

lemma ulcm_ne_zero (k : ℕ) : ulcm k ≠ 0 := by
  simp [ulcm, Finset.lcm_eq_zero_iff]

lemma gam_eq_gammaOf {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (lm : AuxIdx r h D0 Dj)
    (m : Fin (r - 1)) :
    gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))
      = gammaOf (fun i => (derVec b k L (ι m) i : ℚ)) (fun j => (lm.2.2 j : ℕ)) := by
  simp only [gam, gammaOf]
  push_cast
  rfl

lemma finRange_map_prod {q : ℕ} (g : Fin q → ℂ) :
    ((List.finRange q).map g).prod = ∏ m, g m := by
  rw [← List.prod_toFinset g (List.nodup_finRange q), List.toFinset_finRange]

/-! ## Basic calculus of `eulerDer` -/

lemma eulerDer_add {r : ℕ} (c : Fin r → ℚ) (P Q : MvPolynomial (Fin (r + 1)) ℂ) :
    eulerDer c (P + Q) = eulerDer c P + eulerDer c Q := by
  simp only [eulerDer, map_add, mul_add, Finset.sum_add_distrib]

lemma eulerDer_smul {r : ℕ} (c : Fin r → ℚ) (a : ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ) :
    eulerDer c (a • P) = a • eulerDer c P := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  simp only [eulerDer, MvPolynomial.pderiv_C_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma eulerDer_mul {r : ℕ} (c : Fin r → ℚ) (P Q : MvPolynomial (Fin (r + 1)) ℂ) :
    eulerDer c (P * Q) = eulerDer c P * Q + P * eulerDer c Q := by
  have h1 : ∀ i : Fin r,
      MvPolynomial.C ((c i : ℚ) : ℂ) * MvPolynomial.X i.succ *
          (MvPolynomial.pderiv i.succ) (P * Q)
        = (MvPolynomial.C ((c i : ℚ) : ℂ) * MvPolynomial.X i.succ *
              (MvPolynomial.pderiv i.succ) P * Q)
          + (MvPolynomial.C ((c i : ℚ) : ℂ) * MvPolynomial.X i.succ * P *
              (MvPolynomial.pderiv i.succ) Q) := by
    intro i; rw [MvPolynomial.pderiv_mul]; ring
  simp only [eulerDer, h1, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_mul]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

lemma eulerDer_sum {r : ℕ} (c : Fin r → ℚ) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial (Fin (r + 1)) ℂ) :
    eulerDer c (∑ i ∈ s, f i) = ∑ i ∈ s, eulerDer c (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [eulerDer]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, eulerDer_add, ih]

lemma eulerDer_ymon {r : ℕ} (c : Fin r → ℚ) (μ : Fin r → ℕ) :
    eulerDer c (ymon μ) = MvPolynomial.C (gammaOf c μ) * ymon μ := by
  have h : ∀ i : Fin r,
      MvPolynomial.C ((c i : ℚ) : ℂ) * MvPolynomial.X i.succ *
          (MvPolynomial.pderiv i.succ) (ymon μ)
        = MvPolynomial.C (((c i : ℚ) : ℂ) * ((μ i : ℕ) : ℂ)) * ymon μ := by
    intro i
    rw [ymon, mul_assoc, X_succ_mul_pderiv_prod_X_succ_pow, ← mul_assoc, ← MvPolynomial.C_mul]
  simp only [eulerDer, ymon] at h ⊢
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.sum_mul, ← map_sum]
  rfl

lemma eulerDer_y0part {r : ℕ} (h d t0 : ℕ) (c₀ : ℂ) (c : Fin r → ℚ) :
    eulerDer c (y0part h c₀ d t0) = 0 := by
  simp only [eulerDer, y0part, pderiv_succ_aeval_Y0, mul_zero, Finset.sum_const_zero]

lemma eulerDer_Qbase {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (lm : AuxIdx r h D0 Dj)
    (t0 : ℕ) (c : Fin r → ℚ) :
    eulerDer c (Qbase h D0 Dj lm t0)
      = MvPolynomial.C (gammaOf c (fun j => (lm.2.2 j : ℕ))) * Qbase h D0 Dj lm t0 := by
  rw [Qbase, eulerDer_mul, eulerDer_y0part, zero_mul, zero_add, eulerDer_ymon]
  ring

lemma eulerDer_sum_smul_Qbase {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (t0 : ℕ)
    (c : Fin r → ℚ) (a : AuxIdx r h D0 Dj → ℂ) :
    eulerDer c (∑ lm : AuxIdx r h D0 Dj, a lm • Qbase h D0 Dj lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * gammaOf c (fun j => (lm.2.2 j : ℕ))) • Qbase h D0 Dj lm t0 := by
  rw [eulerDer_sum]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [eulerDer_smul, eulerDer_Qbase, ← smul_mul_assoc, MvPolynomial.smul_eq_C_mul,
    ← MvPolynomial.C_mul, MvPolynomial.C_mul']

lemma iterate_eulerDer_sum_smul_Qbase {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (t0 : ℕ)
    (c : Fin r → ℚ) (k : ℕ) (a : AuxIdx r h D0 Dj → ℂ) :
    (eulerDer c)^[k] (∑ lm : AuxIdx r h D0 Dj, a lm • Qbase h D0 Dj lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * (gammaOf c (fun j => (lm.2.2 j : ℕ)))^k) • Qbase h D0 Dj lm t0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, eulerDer_sum_smul_Qbase]
    refine Finset.sum_congr rfl fun lm _ => ?_
    rw [pow_succ, mul_assoc]

/-- Iterating the Euler derivations along a list of indices multiplies the `λ`-coefficient by the
product of the corresponding `γ`'s. -/
lemma foldr_eulerDer_sum_smul_Qbase {r q : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (t0 : ℕ)
    (c : Fin q → Fin r → ℚ) (t : Fin q → ℕ) (l : List (Fin q))
    (a : AuxIdx r h D0 Dj → ℂ) :
    l.foldr (fun m Q => (eulerDer (c m))^[t m] Q)
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qbase h D0 Dj lm t0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (a lm * (l.map (fun m => (gammaOf (c m) (fun j => (lm.2.2 j : ℕ)))^(t m))).prod)
            • Qbase h D0 Dj lm t0 := by
  induction l with
  | nil => simp
  | cons m l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, ih,
      iterate_eulerDer_sum_smul_Qbase]
    refine Finset.sum_congr rfl fun lm _ => ?_
    congr 1
    ring

/-! ## Basic calculus of `pderiv 0` (the `Y₀`-variable) -/

lemma pderiv_zero_X_pow {r : ℕ} (j : Fin r) (e : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)) :
        MvPolynomial (Fin (r + 1)) ℂ → MvPolynomial (Fin (r + 1)) ℂ)
      (MvPolynomial.X j.succ ^ e) = 0 := by
  rw [MvPolynomial.pderiv_pow]
  simp [MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero j)]

lemma pderiv_zero_ymon {r : ℕ} (μ : Fin r → ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1))) (ymon μ) = 0 := by
  rw [ymon]
  induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, MvPolynomial.pderiv_mul, pderiv_zero_X_pow, ih]
    ring

lemma pderiv0_pow_mul_of_eq_zero {r : ℕ} (k : ℕ) {M : MvPolynomial (Fin (r + 1)) ℂ}
    (hM : (MvPolynomial.pderiv (0 : Fin (r + 1))) M = 0) (Y : MvPolynomial (Fin (r + 1)) ℂ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k] (Y * M)
      = (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k] Y * M := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', MvPolynomial.pderiv_mul,
      hM, mul_zero, add_zero]

lemma pderiv0_pow_Qbase {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (lm : AuxIdx r h D0 Dj) (k : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k] (Qbase h D0 Dj lm 0)
      = (k.factorial : ℂ) • Qbase h D0 Dj lm k := by
  rw [Qbase, pderiv0_pow_mul_of_eq_zero k (pderiv_zero_ymon _)]
  rw [y0part, pderiv0_pow_aeval_Y0, Polynomial.hasseDeriv_zero']
  rw [Qbase, y0part, ← smul_mul_assoc]

lemma pderiv0_pow_sum_smul_Qbase {r : ℕ} (h D0 : ℕ) (Dj : Fin r → ℕ) (k : ℕ)
    (a : AuxIdx r h D0 Dj → ℂ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
        (∑ lm : AuxIdx r h D0 Dj, a lm • Qbase h D0 Dj lm 0)
      = ∑ lm : AuxIdx r h D0 Dj, (a lm * (k.factorial : ℂ)) • Qbase h D0 Dj lm k := by
  have h1 : ∀ Y : AuxIdx r h D0 Dj → MvPolynomial (Fin (r + 1)) ℂ,
      (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k] (∑ lm, a lm • Y lm)
        = ∑ lm, a lm • (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k] (Y lm) := by
    intro Y
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, map_sum]
      exact Finset.sum_congr rfl (fun lm _ => by
        rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, MvPolynomial.pderiv_C_mul])
  rw [h1 (fun lm => Qbase h D0 Dj lm 0)]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [pderiv0_pow_Qbase, smul_smul]

/-! ## The coefficient computation -/

/-- The coefficient of the `λ`-summand of the span combination, evaluated at the chosen
coefficients `bb` of the binomial-basis expansion, equals `φ(p_λ)·t₀!·∏_m γ_m(λ)^{t_m}`. -/
lemma coeff_identity {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (bb : ℕ → ℕ → ℂ)
    (hbb : ∀ kk z, z ^ kk = ∑ j ∈ Finset.range (kk + 1), bb kk j * Delta z j)
    (lm : AuxIdx r h D0 Dj) :
    (∑ t' ∈ (Finset.univ : Finset (Fin (r - 1) → Fin ((∑ m, t m) + 1))).filter
        (fun t' => ∑ m, (t' m : ℕ) ≤ ∑ m, t m),
      (((ulcm h : ℂ) ^ t0)⁻¹ * (t0.factorial : ℂ) *
          (if ∀ m, (t' m : ℕ) ≤ t m then ∏ m, bb (t m) ((t' m : ℕ)) else 0)) *
        (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) ((t' m : ℕ))) *
          (ulcm h : ℂ) ^ t0))
      = φ (p lm) *
          (∏ m, (gammaOf (fun i => (derVec b k L (ι m) i : ℚ)) (fun j => (lm.2.2 j : ℕ))) ^ (t m)) *
        (t0.factorial : ℂ) := by
  classical
  have hule : ((ulcm h : ℂ) ^ t0) ≠ 0 := pow_ne_zero _ (by exact_mod_cast ulcm_ne_zero h)
  have hterm : ∀ t' : Fin (r - 1) → Fin ((∑ m, t m) + 1),
      (((ulcm h : ℂ) ^ t0)⁻¹ * (t0.factorial : ℂ) *
          (if ∀ m, (t' m : ℕ) ≤ t m then ∏ m, bb (t m) ((t' m : ℕ)) else 0)) *
        (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) ((t' m : ℕ))) *
          (ulcm h : ℂ) ^ t0)
      = φ (p lm) * (t0.factorial : ℂ) *
          (if ∀ m, (t' m : ℕ) ≤ t m then
            (∏ m, bb (t m) ((t' m : ℕ))) *
              (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) ((t' m : ℕ)))
          else 0) := by
    intro t'
    by_cases hb : ∀ m, (t' m : ℕ) ≤ t m
    · rw [if_pos hb, if_pos hb]
      field_simp
    · rw [if_neg hb, if_neg hb]
      ring
  rw [Finset.sum_congr rfl (fun t' _ => hterm t'), ← Finset.mul_sum, ← Finset.sum_filter]
  have hboxsub : ∀ t' : Fin (r - 1) → Fin ((∑ m, t m) + 1), (∀ m, (t' m : ℕ) ≤ t m) →
      ∑ m, (t' m : ℕ) ≤ ∑ m, t m := fun t' h' => Finset.sum_le_sum (fun m _ => h' m)
  have hSboxeq :
      ((Finset.univ : Finset (Fin (r - 1) → Fin ((∑ m, t m) + 1))).filter
          (fun t' => ∑ m, (t' m : ℕ) ≤ ∑ m, t m)).filter
          (fun t' => ∀ m, (t' m : ℕ) ≤ t m)
        = (Finset.univ : Finset (Fin (r - 1) → Fin ((∑ m, t m) + 1))).filter
          (fun t' => ∀ m, (t' m : ℕ) ≤ t m) := by
    ext t'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hboxsub t' h, h⟩⟩
  rw [hSboxeq]
  rw [sum_fin_box_eq_sum_piFinset t (∑ m, t m)
      (fun m => Finset.single_le_sum (fun i _ => Nat.zero_le (t i)) (Finset.mem_univ m))
      (fun n => (∏ m, bb (t m) (n m)) *
        ∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (n m))]
  simp only [← Finset.prod_mul_distrib]
  rw [(Finset.prod_univ_sum (fun m : Fin (r - 1) => Finset.range (t m + 1))
      (fun m j => bb (t m) j * Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) j)).symm]
  have hprod : (∏ m : Fin (r - 1),
        ∑ j ∈ Finset.range (t m + 1),
          bb (t m) j * Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) j)
      = ∏ m : Fin (r - 1),
          (gammaOf (fun i => (derVec b k L (ι m) i : ℚ)) (fun j => (lm.2.2 j : ℕ))) ^ (t m) := by
    refine Finset.prod_congr rfl (fun m _ => ?_)
    rw [← gam_eq_gammaOf b k L ι h D0 Dj lm m,
      ← hbb (t m) (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ)))]
  rw [hprod]
  ring

/-! ## BW §16 differential Lemma 6 -/

/-- BW §16 (differential Lemma 6): the derivative `∂₀^{t₀}∏_m ∂*_m^{t_m}` of the auxiliary
polynomial `Q(·;0)` (i.e. `Qpoly … p 0 0`) is a finite ℂ-linear combination of the twists
`Qpoly … p t₀ t'` with `∑ m, t' m ≤ ∑ m, t m`. -/
theorem applyDer_Qpoly_span {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (t0 : ℕ) (t : Fin (r - 1) → ℕ) :
    ∃ c : (Fin (r - 1) → Fin ((∑ m, t m) + 1)) → ℂ,
      applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) t0 t
          (Qpoly φ b k L ι α' h D0 Dj p 0 0)
        = ∑ t' ∈ (Finset.univ.filter
              (fun t' : Fin (r - 1) → Fin ((∑ m, t m) + 1) => ∑ m, (t' m : ℕ) ≤ ∑ m, t m)),
            c t' • Qpoly φ b k L ι α' h D0 Dj p t0 (fun m => (t' m : ℕ)) := by
  classical
  -- the expansion coefficients of `z^k` in the binomial basis
  have hexp : ∀ kk : ℕ, ∃ b : ℕ → ℂ, (∀ j, kk < j → b j = 0) ∧
      ∀ z : ℂ, z ^ kk = ∑ j ∈ Finset.range (kk + 1), b j * Delta z j :=
    fun kk => Delta_pow_expansion kk
  choose bb _ hbb using hexp
  -- the candidate coefficients
  let cc : (Fin (r - 1) → Fin ((∑ m, t m) + 1)) → ℂ := fun t' =>
    ((ulcm h : ℂ) ^ t0)⁻¹ * (t0.factorial : ℂ) *
      (if ∀ m, (t' m : ℕ) ≤ t m then ∏ m, bb (t m) ((t' m : ℕ)) else 0)
  refine ⟨cc, ?_⟩
  -- ### the left-hand side
  have hQ0 : Qpoly φ b k L ι α' h D0 Dj p 0 0
      = ∑ lm : AuxIdx r h D0 Dj, (φ (p lm)) • Qbase h D0 Dj lm 0 := by
    rw [Qpoly_eq_sum_Qbase]
    refine Finset.sum_congr rfl fun lm _ => ?_
    simp only [Delta_zero, Finset.prod_const_one, mul_one, pow_zero, Pi.zero_apply]
  have hfold : (List.finRange (r - 1)).foldr
        (fun m Q => (eulerDer (fun i => (derVec b k L (ι m) i : ℚ)))^[t m] Q)
        (∑ lm : AuxIdx r h D0 Dj, (φ (p lm)) • Qbase h D0 Dj lm 0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (φ (p lm) * (∏ m,
              (gammaOf (fun i => (derVec b k L (ι m) i : ℚ))
                (fun j => (lm.2.2 j : ℕ)))^(t m))) • Qbase h D0 Dj lm 0 := by
    rw [foldr_eulerDer_sum_smul_Qbase]
    refine Finset.sum_congr rfl fun lm _ => ?_
    rw [finRange_map_prod]
  have hpd : (MvPolynomial.pderiv (0 : Fin (r + 1)))^[t0]
        (∑ lm : AuxIdx r h D0 Dj,
          (φ (p lm) * (∏ m,
              (gammaOf (fun i => (derVec b k L (ι m) i : ℚ))
                (fun j => (lm.2.2 j : ℕ)))^(t m))) • Qbase h D0 Dj lm 0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (φ (p lm) * (∏ m,
              (gammaOf (fun i => (derVec b k L (ι m) i : ℚ))
                (fun j => (lm.2.2 j : ℕ)))^(t m)) * (t0.factorial : ℂ)) •
            Qbase h D0 Dj lm t0 := by
    rw [pderiv0_pow_sum_smul_Qbase]
  have hLHS : applyDer (fun m i => (derVec b k L (ι m) i : ℚ)) t0 t
        (Qpoly φ b k L ι α' h D0 Dj p 0 0)
      = ∑ lm : AuxIdx r h D0 Dj,
          (φ (p lm) * (∏ m,
              (gammaOf (fun i => (derVec b k L (ι m) i : ℚ))
                (fun j => (lm.2.2 j : ℕ)))^(t m)) * (t0.factorial : ℂ)) •
            Qbase h D0 Dj lm t0 := by
    rw [applyDer, hQ0, hfold, hpd]
  rw [hLHS]
  -- ### the right-hand side
  have hQ : ∀ t' : Fin (r - 1) → Fin ((∑ m, t m) + 1),
      cc t' • Qpoly φ b k L ι α' h D0 Dj p t0 (fun m => (t' m : ℕ))
        = ∑ lm : AuxIdx r h D0 Dj,
            (cc t' * (φ (p lm) *
                (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) ((t' m : ℕ))) *
                (ulcm h : ℂ) ^ t0)) • Qbase h D0 Dj lm t0 := by
    intro t'
    rw [Qpoly_eq_sum_Qbase, Finset.smul_sum]
    refine Finset.sum_congr rfl fun lm _ => ?_
    rw [smul_smul]
  have hRHS : (∑ t' ∈ (Finset.univ.filter
          (fun t' : Fin (r - 1) → Fin ((∑ m, t m) + 1) => ∑ m, (t' m : ℕ) ≤ ∑ m, t m)),
        cc t' • Qpoly φ b k L ι α' h D0 Dj p t0 (fun m => (t' m : ℕ)))
      = ∑ lm : AuxIdx r h D0 Dj,
          (φ (p lm) * (∏ m,
              (gammaOf (fun i => (derVec b k L (ι m) i : ℚ))
                (fun j => (lm.2.2 j : ℕ)))^(t m)) * (t0.factorial : ℂ)) •
            Qbase h D0 Dj lm t0 := by
    rw [Finset.sum_congr rfl (fun t' _ => hQ t'), Finset.sum_comm]
    refine Finset.sum_congr rfl fun lm _ => ?_
    rw [(Finset.sum_smul (s := (Finset.univ.filter
          (fun t' : Fin (r - 1) → Fin ((∑ m, t m) + 1) => ∑ m, (t' m : ℕ) ≤ ∑ m, t m)))
        (f := fun t' => cc t' * (φ (p lm) *
          (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) ((t' m : ℕ))) *
          (ulcm h : ℂ) ^ t0))
        (x := Qbase h D0 Dj lm t0)).symm]
    congr 1
    dsimp only [cc]
    exact coeff_identity φ b k L ι h D0 Dj p t0 t bb hbb lm
  exact hRHS.symm

end Work.BW
