import Submission.ZagierHoffmanProof.ABPKey

/-!
# The polynomial form of the key identity

The Frobenius twist of a polynomial (coefficients raised to `q ^ k`) and its compatibility with the
power-series twist, together with the polynomial version `keyProdPoly` of `keyProd` and the final
row vector `finalP`.
-/

set_option autoImplicit false
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {q : ℕ} [FrobPow K q]

/-- The `q ^ k`-th power (Frobenius) ring endomorphism of `K`. -/
noncomputable def frobPowHom (k : ℕ) : K →+* K where
  toFun x := x ^ (q ^ k)
  map_one' := one_pow _
  map_mul' a b := mul_pow a b _
  map_zero' := zero_pow (pow_ne_zero k (FrobPow.ne_zero K (q := q)))
  map_add' a b := (FrobPow.pow (R := K) (q := q) k).add_pow a b

@[simp] lemma frobPowHom_apply (k : ℕ) (x : K) : frobPowHom (q := q) k x = x ^ (q ^ k) := rfl

/-- The Frobenius twist `p ↦ ∑ aₖ^(q^k) tᵏ` of a polynomial, as a ring homomorphism. -/
noncomputable def polyTwistHom (k : ℕ) : Polynomial K →+* Polynomial K :=
  Polynomial.mapRingHom (frobPowHom (q := q) k)

lemma polyTwistHom_apply (k : ℕ) (p : Polynomial K) :
    polyTwistHom (q := q) k p = p.map (frobPowHom (q := q) k) := rfl

/-- The Frobenius twist of a polynomial. -/
noncomputable def polyTwist (k : ℕ) (p : Polynomial K) : Polynomial K :=
  polyTwistHom (q := q) k p

/-- The coefficientwise coercion `K[X] → K⟦t⟧` as a ring hom. -/
noncomputable def coeHom : Polynomial K →+* PowerSeries K :=
  Polynomial.coeToPowerSeries.ringHom

lemma coeHom_apply (p : Polynomial K) : coeHom (K := K) p = (p : PowerSeries K) := rfl

/-- The twisted polynomial, as a power series, is the twist of the power series. -/
lemma coe_polyTwist (k : ℕ) (p : Polynomial K) :
    coeHom (K := K) (polyTwist (q := q) k p)
      = frobTwist (R := K) (p := q) k (coeHom (K := K) p) := by
  ext n
  rw [coeHom_apply, coeHom_apply, Polynomial.coeff_coe, polyTwist, polyTwistHom_apply,
    Polynomial.coeff_map, frobPowHom_apply, frobTwist_coeff, Polynomial.coeff_coe]

/-- The coercion commutes with the twist, at the level of square matrices. -/
lemma coe_mapMatrix_polyTwist {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (A : Matrix n n (Polynomial K)) :
    (coeHom (K := K)).mapMatrix ((polyTwistHom (q := q) k).mapMatrix A)
      = frobTwistMat (q := q) k ((coeHom (K := K)).mapMatrix A) := by
  funext i j
  exact coe_polyTwist (q := q) k (A i j)

/-- The polynomial version of `keyProd`. -/
noncomputable def keyProdPoly {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)) :
    ℕ → Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)
  | 0 => 1
  | (M + 1) => (polyTwistHom (q := q) (M + 1)).mapMatrix Θ * keyProdPoly Θ M

@[simp] lemma keyProdPoly_zero {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)) :
    keyProdPoly (q := q) Θ 0 = 1 := rfl

@[simp] lemma keyProdPoly_succ {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)) (M : ℕ) :
    keyProdPoly (q := q) Θ (M + 1)
      = (polyTwistHom (q := q) (M + 1)).mapMatrix Θ * keyProdPoly (q := q) Θ M := rfl

lemma keyProdPoly_coe {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)) (M : ℕ) :
    (coeHom (K := K)).mapMatrix (keyProdPoly (q := q) Θ M)
      = keyProd (q := q) ((coeHom (K := K)).mapMatrix Θ) M := by
  induction M with
  | zero => rw [keyProdPoly_zero, keyProd_zero, map_one]
  | succ M ih =>
      rw [keyProdPoly_succ, map_mul, ih, coe_mapMatrix_polyTwist, keyProd_succ]

/-- The final row vector `P = h^{(M)} · keyProdPoly Θ M`. -/
noncomputable def finalP {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K))
    (h : Fin ℓ → Polynomial K) (M : ℕ) : Fin ℓ → Polynomial K :=
  fun j => ∑ i, polyTwist (q := q) M (h i) * (keyProdPoly (q := q) Θ M) i j

lemma coe_keyProdPoly {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)) (M : ℕ)
    (i j : Fin ℓ) :
    coeHom (K := K) (keyProdPoly (q := q) Θ M i j)
      = keyProd (q := q) ((coeHom (K := K)).mapMatrix Θ) M i j :=
  congrFun (congrFun (keyProdPoly_coe (q := q) Θ M) i) j

/-- A ring hom sends a scalar multiple of the identity to the corresponding scalar multiple. -/
lemma mapMatrix_smul_one {A B : Type*} [CommRing A] [CommRing B] {n : Type*} [Fintype n]
    [DecidableEq n] (f : A →+* B) (c : A) :
    f.mapMatrix (c • (1 : Matrix n n A)) = f c • (1 : Matrix n n B) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h]

lemma coe_finalP {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K))
    (h : Fin ℓ → Polynomial K) (M : ℕ) (j : Fin ℓ) :
    coeHom (K := K) (finalP (q := q) Θ h M j)
      = ∑ i, frobTwist (R := K) (p := q) M (coeHom (K := K) (h i))
          * keyProd (q := q) ((coeHom (K := K)).mapMatrix Θ) M i j := by
  rw [finalP, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, coe_polyTwist, coe_keyProdPoly]

/-- ★★★ **The final step of the ABP criterion.**  If `Θ` is an adjugate transpose of `Φ`
(`Θ * Φ = det Φ • 1`), `ψ` satisfies the twisted functional equation `ψ = Φ^{(1)} ψ^{(1)}` and
`E = ∑ᵢ hᵢ ψᵢ` vanishes, then the polynomial row vector `finalP Θ h M` annihilates `ψ`. -/
theorem finalP_spec {ℓ : ℕ} {Φ Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial K)}
    (hadj : Θ * Φ = Φ.det • 1) {ψ : Fin ℓ → PowerSeries K}
    (hfe : ψ = (frobTwistMat (q := q) 1 ((coeHom (K := K)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := q) 1 ψ))
    {h : Fin ℓ → Polynomial K} {M : ℕ}
    (hE : ∑ i, coeHom (K := K) (h i) * ψ i = 0) :
    ∑ j, coeHom (K := K) (finalP (q := q) Θ h M j) * ψ j = 0 := by
  classical
  have hadj' : ((coeHom (K := K)).mapMatrix Θ) * ((coeHom (K := K)).mapMatrix Φ)
      = ((coeHom (K := K)).mapMatrix Φ).det • 1 := by
    rw [← map_mul, hadj, mapMatrix_smul_one, ((coeHom (K := K)).map_det Φ).symm]
  have hkey := key_identity (q := q) (hadj := hadj') hfe M
  calc ∑ j, coeHom (K := K) (finalP (q := q) Θ h M j) * ψ j
      = ∑ j, (∑ i, frobTwist (R := K) (p := q) M (coeHom (K := K) (h i))
          * keyProd (q := q) ((coeHom (K := K)).mapMatrix Θ) M i j) * ψ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coe_finalP]
    _ = ∑ i, frobTwist (R := K) (p := q) M (coeHom (K := K) (h i))
          * ((keyProd (q := q) ((coeHom (K := K)).mapMatrix Θ) M).mulVec ψ) i := by
        simp only [Matrix.mulVec_apply_eq_sum, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, frobTwist (R := K) (p := q) M (coeHom (K := K) (h i))
          * ((∏ k ∈ Finset.Icc 1 M, frobTwist (R := K) (p := q) k
              ((coeHom (K := K)).mapMatrix Φ).det) * frobTwistVec (q := q) M ψ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hkey]
        rfl
    _ = (∏ k ∈ Finset.Icc 1 M, frobTwist (R := K) (p := q) k
            ((coeHom (K := K)).mapMatrix Φ).det)
          * ∑ i, frobTwist (R := K) (p := q) M (coeHom (K := K) (h i))
              * frobTwist (R := K) (p := q) M (ψ i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [frobTwistVec_apply]
        ring
    _ = (∏ k ∈ Finset.Icc 1 M, frobTwist (R := K) (p := q) k
            ((coeHom (K := K)).mapMatrix Φ).det)
          * frobTwist (R := K) (p := q) M
              (∑ i, coeHom (K := K) (h i) * ψ i) := by
        rw [frobTwist_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [frobTwist_mul]
    _ = 0 := by rw [hE, frobTwist_zero, mul_zero]

end ZagierHoffmanPositiveChar
