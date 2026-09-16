import Submission.ZagierHoffmanProof.ABPFuncEq
import Submission.Commons.LinearAlgebra.Matrix.exists_smul_of_mul_eq_zero
import Submission.Commons.RingTheory.PowerSeries.sum_divX_eq_zero
import Submission.Commons.Algebra.Polynomial.divX_natDegree_lt

/-!
# Step (C) of the ABP criterion: the zeros of the auxiliary function `E = ∑ᵢ hᵢ ψᵢ`

Given `h` from step (A) (raised auxiliary condition at the level `M`) and a solution `ψ` of the
functional equation, the *raised* key identity of `ABPKey` shows that

  `(∏_{k≤M} (det Φ)^{(k)}) · E^{(M)} = (h^{(M)} · keyProd Θ M) · ψ`,

so evaluating at `θ` and using `h^{(M)}(θ)·X_M(θ) = λρ`, `ρψ(θ) = 0` and
`∏_k det Φ(θ^{q^k}) ≠ 0` gives `E^{(M)}(θ) = 0`, hence `E(θ_M) = 0` by injectivity of the
`q^M`-th power map.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §1. The raised key identity in evaluated-along-`h` form -/

/-- **The identity at the heart of `finalP_spec`**, without the hypothesis `E = 0`. -/
lemma finalP_identity {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {ψ : Fin ℓ → PowerSeries (Ambient F)}
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    (h : Fin ℓ → Polynomial (Ambient F)) (M : ℕ) :
    ∑ j, coeHom (K := Ambient F) (finalP (q := Nat.card F) Φ.adjugate h M j) * ψ j
      = (∏ k ∈ Finset.Icc 1 M, frobTwist (R := Ambient F) (p := Nat.card F) k
            ((coeHom (K := Ambient F)).mapMatrix Φ).det)
          * frobTwist (R := Ambient F) (p := Nat.card F) M
              (∑ i, coeHom (K := Ambient F) (h i) * ψ i) := by
  classical
  have hadj' : ((coeHom (K := Ambient F)).mapMatrix Φ.adjugate)
      * ((coeHom (K := Ambient F)).mapMatrix Φ)
      = ((coeHom (K := Ambient F)).mapMatrix Φ).det • 1 := by
    rw [← map_mul, Matrix.adjugate_mul, mapMatrix_smul_one,
      ((coeHom (K := Ambient F)).map_det Φ).symm]
  have hkey := key_identity (q := Nat.card F) (hadj := hadj') hfe M
  calc ∑ j, coeHom (K := Ambient F) (finalP (q := Nat.card F) Φ.adjugate h M j) * ψ j
      = ∑ j, (∑ i, frobTwist (R := Ambient F) (p := Nat.card F) M
            (coeHom (K := Ambient F) (h i))
          * keyProd (q := Nat.card F) ((coeHom (K := Ambient F)).mapMatrix Φ.adjugate) M i j)
          * ψ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coe_finalP]
    _ = ∑ i, frobTwist (R := Ambient F) (p := Nat.card F) M (coeHom (K := Ambient F) (h i))
          * ((keyProd (q := Nat.card F)
              ((coeHom (K := Ambient F)).mapMatrix Φ.adjugate) M).mulVec ψ) i := by
        simp only [Matrix.mulVec_apply_eq_sum, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ =>
          Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, frobTwist (R := Ambient F) (p := Nat.card F) M (coeHom (K := Ambient F) (h i))
          * ((∏ k ∈ Finset.Icc 1 M, frobTwist (R := Ambient F) (p := Nat.card F) k
              ((coeHom (K := Ambient F)).mapMatrix Φ).det)
              * frobTwistVec (q := Nat.card F) M ψ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hkey]
        rfl
    _ = (∏ k ∈ Finset.Icc 1 M, frobTwist (R := Ambient F) (p := Nat.card F) k
            ((coeHom (K := Ambient F)).mapMatrix Φ).det)
          * ∑ i, frobTwist (R := Ambient F) (p := Nat.card F) M (coeHom (K := Ambient F) (h i))
              * frobTwist (R := Ambient F) (p := Nat.card F) M (ψ i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [frobTwistVec_apply]
        ring
    _ = (∏ k ∈ Finset.Icc 1 M, frobTwist (R := Ambient F) (p := Nat.card F) k
            ((coeHom (K := Ambient F)).mapMatrix Φ).det)
          * frobTwist (R := Ambient F) (p := Nat.card F) M
              (∑ i, coeHom (K := Ambient F) (h i) * ψ i) := by
        rw [frobTwist_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [frobTwist_mul]

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §2. Evaluations at `θ` -/

/-- `θ_k ≠ θ` for `k ≥ 1`. -/
lemma ambThetaNu_ne_ambTheta {k : ℕ} (hk : 1 ≤ k) : ambThetaNu F k ≠ ambTheta F := by
  intro h
  have hv : Valued.v (ambThetaNu F k) = Valued.v (ambTheta F) := by rw [h]
  rw [v_ambThetaNu, v_ambTheta, ambKappa] at hv
  rw [WithZero.exp_inj] at hv
  have hq1 : (1 : ℚ) < Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 1 < Nat.card F)
  have hqm1 : ((Nat.card F : ℚ) - 1) ≠ 0 := by linarith
  have hqk : (Nat.card F : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
  have hv' : ((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ k = ((Nat.card F : ℚ) - 1) / 1 := by
    rw [div_one]; exact hv
  rw [div_eq_div_iff hqk one_ne_zero] at hv'
  have h1 : (Nat.card F : ℚ) ^ k = 1 := by
    have h2 := mul_left_cancel₀ hqm1 hv'
    simpa using h2.symm
  have h3 : (1 : ℚ) < (Nat.card F : ℚ) ^ k := one_lt_pow₀ hq1 (by omega)
  rw [h1] at h3
  exact lt_irrefl 1 h3

/-- The map `M ↦ v (θ_M)` is injective. -/
lemma ambKappa_injective : Function.Injective (fun M : ℕ => ambKappa F M) := by
  intro a b hab
  have h2 : ((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ a
      = ((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ b := by
    have h3 := hab
    simp only [ambKappa] at h3
    rw [WithZero.exp_inj] at h3
    exact h3
  have hq1 : (1 : ℚ) < Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 1 < Nat.card F)
  have hqm1 : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by linarith
  have h3 : (Nat.card F : ℚ) ^ a = (Nat.card F : ℚ) ^ b := by
    have h4 : ((Nat.card F : ℚ) - 1) * ((Nat.card F : ℚ) ^ b)
        = ((Nat.card F : ℚ) - 1) * ((Nat.card F : ℚ) ^ a) := by
      rw [div_eq_div_iff (by positivity) (by positivity)] at h2
      exact h2
    exact (mul_left_cancel₀ (ne_of_gt hqm1) h4).symm
  have h5 : Nat.card F ^ a = Nat.card F ^ b := by
    have h6 := h3
    push_cast at h6
    exact_mod_cast h6
  exact Nat.pow_right_injective (by have := two_le_card_field F; omega) h5

/-- The determinant does not vanish at `θ_k`. -/
lemma det_eval_ne_zero {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {c : Ambient F} (hc : c ≠ 0) {s : ℕ}
    (hdet : Φ.det = Polynomial.C c * (Polynomial.X - Polynomial.C (ambTheta F)) ^ s)
    {k : ℕ} (hk : 1 ≤ k) : (Φ.det).eval (ambThetaNu F k) ≠ 0 := by
  rw [hdet, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_C]
  exact mul_ne_zero hc (pow_ne_zero _ (sub_ne_zero.mpr (ambThetaNu_ne_ambTheta F hk)))

/-- The evaluation of a twisted polynomial. -/
lemma eval_frobTwist_polynomial {γ : ℚᵐ⁰} (hγ : γ < 1) (hγ0 : 0 < γ)
    (p : Polynomial (Ambient F)) (k : ℕ) :
    evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) k (coeHom (K := Ambient F) p))
        (ambTheta F)
      = (p.eval (ambThetaNu F k)) ^ (Nat.card F ^ k) := by
  rw [coeHom_apply]
  rw [← ambThetaNu_pow F k]
  rw [evalSeriesGen_frobTwist hγ gammaArchimedean_rat (Nat.card F)
    (GSuperEntire.polynomial hγ0 hγ.le p) (ambThetaNu F k) k]
  rw [evalSeriesGen_polynomial]

/-- The evaluation of the product of the twisted determinants. -/
lemma eval_prod_det {γ : ℚᵐ⁰} (hγ : γ < 1) (hγ0 : 0 < γ)
    (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) (M : ℕ) :
    evalSeriesGen (∏ k ∈ Finset.Icc 1 M, frobTwist (R := Ambient F) (p := Nat.card F) k
        ((coeHom (K := Ambient F)).mapMatrix Φ).det) (ambTheta F)
      = ∏ k ∈ Finset.Icc 1 M, ((Φ.det).eval (ambThetaNu F k)) ^ (Nat.card F ^ k) := by
  have hdet : ((coeHom (K := Ambient F)).mapMatrix Φ).det = coeHom (K := Ambient F) (Φ.det) :=
    (RingHom.map_det (coeHom (K := Ambient F)) Φ).symm
  rw [hdet]
  rw [evalSeriesGen_prod hγ gammaArchimedean_rat (Finset.Icc 1 M)
    (fun k => frobTwist (R := Ambient F) (p := Nat.card F) k (coeHom (K := Ambient F) (Φ.det)))
    (fun k _ => (GSuperEntire.polynomial hγ0 hγ.le _).frobTwist hγ.le k) (ambTheta F)]
  exact Finset.prod_congr rfl fun k _ => eval_frobTwist_polynomial F hγ hγ0 (Φ.det) k

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §3. The vanishing of `E = ∑ᵢ hᵢψᵢ` at `θ_M` -/

/-- ★★★ **The auxiliary function vanishes at `θ_M`.**  Under the hypotheses of the ABP criterion
(the raised auxiliary condition at level `M ≥ 1`, the functional equation for `ψ`, the relation
`ρψ(θ) = 0` and `det Φ = c(t-θ)^s`), the auxiliary function `E = ∑ᵢ hᵢψᵢ` vanishes at
`θ_M = θ^{q^{-M}}`. -/
theorem eval_auxFun_thetaNu_eq_zero {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1) (hℓ : 2 ≤ ℓ)
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {ψ : Fin ℓ → PowerSeries (Ambient F)} (hse : ∀ i, GSuperEntire γ (ψ i))
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    {h : Fin ℓ → Polynomial (Ambient F)} {M : ℕ} (hM : 1 ≤ M)
    {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)}
    (hind : LinearIndependent (Ambient F) (fun i : Fin (ℓ - 1) => fun j : Fin ℓ => ϑ j i))
    {ρ : Fin ℓ → Ambient F} (hρ : Matrix.vecMul ρ ϑ = 0) (hρ0 : ρ ≠ 0)
    (hval : dotProduct ρ (fun i => evalSeriesGen (ψ i) (ambTheta F)) = 0)
    (haux : Matrix.vecMul (fun j => (finalP (q := Nat.card F) Φ.adjugate h M j).eval
      (ambTheta F)) ϑ = 0)
    {c : Ambient F} (hc : c ≠ 0) {s : ℕ}
    (hdet : Φ.det = Polynomial.C c * (Polynomial.X - Polynomial.C (ambTheta F)) ^ s) :
    evalSeriesGen (∑ i, coeHom (K := Ambient F) (h i) * ψ i) (ambThetaNu F M) = 0 := by
  classical
  set E : PowerSeries (Ambient F) := ∑ i, coeHom (K := Ambient F) (h i) * ψ i with hE
  have hEse : GSuperEntire γ E :=
    GSuperEntire.sum hγ.le _ _ (fun i _ => (GSuperEntire.polynomial hγ0 hγ.le _).mul hγ.le (hse i))
  have hTwse : GSuperEntire γ (frobTwist (R := Ambient F) (p := Nat.card F) M E) :=
    hEse.frobTwist hγ.le M
  have hprobse : GSuperEntire γ (∏ k ∈ Finset.Icc 1 M, frobTwist (R := Ambient F)
      (p := Nat.card F) k ((coeHom (K := Ambient F)).mapMatrix Φ).det) :=
    GSuperEntire.prod hγ.le _ _ (fun k _ => by
      rw [← RingHom.map_det]
      exact (GSuperEntire.polynomial hγ0 hγ.le (Φ.det)).frobTwist hγ.le k)
  -- the identity, evaluated at `θ`
  have hid := congrArg (fun x => evalSeriesGen x (ambTheta F)) (finalP_identity F hfe h M)
  rw [evalSeriesGen_finset_sum hγ gammaArchimedean_rat (Finset.univ)
      (fun j => coeHom (K := Ambient F) (finalP (q := Nat.card F) Φ.adjugate h M j) * ψ j)
      (fun j _ => (GSuperEntire.polynomial hγ0 hγ.le _).mul hγ.le (hse j)) (ambTheta F),
    evalSeriesGen_mul hγ gammaArchimedean_rat hprobse hTwse (ambTheta F)] at hid
  have hterm : ∀ j : Fin ℓ, evalSeriesGen (coeHom (K := Ambient F)
        (finalP (q := Nat.card F) Φ.adjugate h M j) * ψ j) (ambTheta F)
      = (finalP (q := Nat.card F) Φ.adjugate h M j).eval (ambTheta F)
        * evalSeriesGen (ψ j) (ambTheta F) := by
    intro j
    have hc : coeHom (K := Ambient F) (finalP (q := Nat.card F) Φ.adjugate h M j)
        = ((finalP (q := Nat.card F) Φ.adjugate h M j : Polynomial (Ambient F))
            : PowerSeries (Ambient F)) := rfl
    rw [hc, evalSeriesGen_mul hγ gammaArchimedean_rat
      (GSuperEntire.polynomial hγ0 hγ.le (finalP (q := Nat.card F) Φ.adjugate h M j)) (hse j)
      (ambTheta F), evalSeriesGen_polynomial]
  simp only [hterm] at hid
  -- the row vector is a multiple of `ρ`
  obtain ⟨lam, hlam⟩ :=
    Commons.LinearAlgebra.Matrix.exists_smul_of_mul_eq_zero hℓ hind hρ hρ0 haux
  have hzero : ∑ j, (finalP (q := Nat.card F) Φ.adjugate h M j).eval (ambTheta F)
      * evalSeriesGen (ψ j) (ambTheta F) = 0 := by
    have h1 : ∀ j : Fin ℓ, (finalP (q := Nat.card F) Φ.adjugate h M j).eval (ambTheta F)
        = lam * ρ j := by
      intro j
      rw [congrFun hlam j, Pi.smul_apply, smul_eq_mul]
    calc ∑ j, (finalP (q := Nat.card F) Φ.adjugate h M j).eval (ambTheta F)
          * evalSeriesGen (ψ j) (ambTheta F)
        = ∑ j, (lam * ρ j) * evalSeriesGen (ψ j) (ambTheta F) :=
          Finset.sum_congr rfl fun j _ => by rw [h1 j]
      _ = lam * ∑ j, ρ j * evalSeriesGen (ψ j) (ambTheta F) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = lam * dotProduct ρ (fun i => evalSeriesGen (ψ i) (ambTheta F)) := by
          have hdp : (∑ j, ρ j * evalSeriesGen (ψ j) (ambTheta F))
              = dotProduct ρ (fun i => evalSeriesGen (ψ i) (ambTheta F)) := rfl
          rw [hdp]
      _ = 0 := by rw [hval, mul_zero]
  -- the product factor does not vanish
  have hprod : evalSeriesGen (∏ k ∈ Finset.Icc 1 M, frobTwist (R := Ambient F)
      (p := Nat.card F) k ((coeHom (K := Ambient F)).mapMatrix Φ).det) (ambTheta F) ≠ 0 := by
    rw [eval_prod_det F hγ hγ0 Φ M]
    refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
    exact pow_ne_zero _ (det_eval_ne_zero F hc hdet (Finset.mem_Icc.mp hk).1)
  -- hence `(frobTwist M E)(θ) = 0`
  rw [hzero, zero_eq_mul] at hid
  have hmain : evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) M E) (ambTheta F) = 0 := by
    rcases hid with h | h
    · exact absurd h hprod
    · exact h
  -- transport to `θ_M`
  have h2 : (evalSeriesGen E (ambThetaNu F M)) ^ (Nat.card F ^ M) = 0 := by
    rw [← evalSeriesGen_frobTwist hγ gammaArchimedean_rat (Nat.card F) hEse (ambThetaNu F M) M,
      ambThetaNu_pow]
    exact hmain
  have h3 : evalSeriesGen E (ambThetaNu F M) = 0 :=
    (pow_eq_zero_iff (pow_ne_zero M (FrobPow.ne_zero (Ambient F) (q := Nat.card F)))).mp h2
  simpa only [hE] using h3

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]

/-! ## §4. Dividing the functional equation by powers of `t` -/

/-- If all the constant terms of a nontrivial solution of `∑_j b_j g_j = 0` vanish, the `b_j` are
divisible by `t` and the divided solution satisfies the same equation (with the same
`A_ν`-membership, coefficient bound and smaller degrees).  Iterating gives a solution with some
non-vanishing constant term. -/
lemma exists_no_t_factor {ι : Type*} [Fintype ι] {g : ι → PowerSeries (Ambient F)} {ν : ℕ}
    {Ab : ℚᵐ⁰} :
    ∀ S : ℕ, ∀ b : ι → Polynomial (Ambient F), (∑ j, (b j).natDegree) = S → b ≠ 0 →
      (∑ j, ((b j : Polynomial (Ambient F)) : PowerSeries (Ambient F)) * g j = 0) →
      (∀ j k, (b j).coeff k ∈ ambA F ν) → (∀ j k, Valued.v ((b j).coeff k) ≤ Ab) →
      ∃ b' : ι → Polynomial (Ambient F), b' ≠ 0 ∧ (∃ j, (b' j).coeff 0 ≠ 0) ∧
        (∑ j, ((b' j : Polynomial (Ambient F)) : PowerSeries (Ambient F)) * g j = 0) ∧
        (∀ j k, (b' j).coeff k ∈ ambA F ν) ∧ (∀ j k, Valued.v ((b' j).coeff k) ≤ Ab) ∧
        (∀ j, (b' j).natDegree ≤ (b j).natDegree) := by
  intro S
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    intro b hS hb heq hmem hsz
    by_cases hconst : ∃ j, (b j).coeff 0 ≠ 0
    · exact ⟨b, hb, hconst, heq, hmem, hsz, fun j => le_rfl⟩
    push Not at hconst
    -- all the `b j` are divisible by `t`
    set b' : ι → Polynomial (Ambient F) := fun j => (b j).divX with hb'
    have heq' : ∑ j, ((b' j : Polynomial (Ambient F)) : PowerSeries (Ambient F)) * g j = 0 :=
      Commons.RingTheory.PowerSeries.sum_divX_eq_zero (fun j => hconst j) heq
    have hb'0 : b' ≠ 0 := by
      intro h
      apply hb
      funext j
      have h1 : (b j).divX = 0 := congrFun h j
      have h2 := Polynomial.divX_mul_X_add (b j)
      rw [h1, zero_mul, hconst j, Polynomial.C_0, add_zero] at h2
      exact h2.symm
    have hle : ∀ j, (b' j).natDegree ≤ (b j).natDegree := fun j =>
      Polynomial.natDegree_divX_le
    have hlt : ∑ j, (b' j).natDegree < S := by
      obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
        by_contra h
        push Not at h
        exact hb (funext h)
      have hstrict : ∃ j ∈ Finset.univ, (b' j).natDegree < (b j).natDegree :=
        ⟨j, Finset.mem_univ j, (Commons.Algebra.Polynomial.divX_natDegree_lt (hconst j) hj).2⟩
      have hsum := Finset.sum_lt_sum (fun j _ => hle j) hstrict
      rw [hS] at hsum
      exact hsum
    have hmem' : ∀ j k, (b' j).coeff k ∈ ambA F ν := by
      intro j k
      rw [hb', Polynomial.coeff_divX]
      exact hmem j (k + 1)
    have hsz' : ∀ j k, Valued.v ((b' j).coeff k) ≤ Ab := by
      intro j k
      rw [hb', Polynomial.coeff_divX]
      exact hsz j (k + 1)
    obtain ⟨b'', hb'', hconst'', heq'', hmem'', hsz'', hdeg''⟩ :=
      ih _ hlt b' rfl hb'0 heq' hmem' hsz'
    exact ⟨b'', hb'', hconst'', heq'', hmem'', hsz'', fun j =>
      le_trans (hdeg'' j) (hle j)⟩

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §5. Non-vanishing of `finalP` at `θ` -/

/-- The determinant of the `M`-th key product is the product of the twisted determinants. -/
lemma det_keyProdPoly {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))} (M : ℕ) :
    (keyProdPoly (q := Nat.card F) Θ M).det
      = ∏ k ∈ Finset.Icc 1 M, polyTwist (q := Nat.card F) k Θ.det := by
  induction M with
  | zero =>
      rw [keyProdPoly_zero, Matrix.det_one,
        Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0), Finset.prod_empty]
  | succ M ih =>
      rw [keyProdPoly_succ, Matrix.det_mul, ih,
        show ((polyTwistHom (q := Nat.card F) (M + 1)).mapMatrix Θ).det
          = polyTwist (q := Nat.card F) (M + 1) Θ.det from by
          rw [polyTwist, ← RingHom.map_det]]
      rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ M + 1)]
      ring

/-- `X_M(θ) = keyEval Θ M` is invertible when the determinant of `Θ` does not vanish on the
Frobenius orbit. -/
lemma det_keyEval_ne_zero {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (h : ∀ k, 1 ≤ k → (Θ.det).eval (ambThetaNu F k) ≠ 0) {M : ℕ} (hM : 1 ≤ M) :
    (keyEval F Θ M).det ≠ 0 := by
  have h1 : (keyEval F Θ M).det = (keyProdPoly (q := Nat.card F) Θ M).det.eval (ambTheta F) := by
    rw [keyEval, evalMatHom]
    exact (RingHom.map_det (Polynomial.evalRingHom (ambTheta F)) _).symm
  rw [h1, det_keyProdPoly F (Θ := Θ) M, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
  rw [eval_polyTwist]
  exact pow_ne_zero _ (h k (Finset.mem_Icc.mp hk).1)

/-- A nonzero row vector times an invertible matrix is nonzero. -/
lemma vecMul_ne_zero_of_det_ne_zero {X : Matrix (Fin ℓ) (Fin ℓ) (Ambient F)}
    (hdet : X.det ≠ 0) {v : Fin ℓ → Ambient F} (hv : v ≠ 0) : Matrix.vecMul v X ≠ 0 := by
  intro h
  apply hv
  have h1 : Matrix.vecMul (Matrix.vecMul v X) X.adjugate = 0 := by rw [h, Matrix.zero_vecMul]
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one] at h1
  exact (smul_eq_zero.mp h1).resolve_left hdet

/-- **`finalP` does not vanish at `θ`.** -/
lemma finalP_eval_ne_zero {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (h : ∀ k, 1 ≤ k → (Θ.det).eval (ambThetaNu F k) ≠ 0)
    {h' : Fin ℓ → Polynomial (Ambient F)} {M : ℕ} (hM : 1 ≤ M)
    (hv : (fun i => (polyTwist (q := Nat.card F) M (h' i)).eval (ambTheta F)) ≠ 0) :
    (fun j => (finalP (q := Nat.card F) Θ h' M j).eval (ambTheta F)) ≠ 0 := by
  have h1 : (fun j => (finalP (q := Nat.card F) Θ h' M j).eval (ambTheta F))
      = Matrix.vecMul (fun i => (polyTwist (q := Nat.card F) M (h' i)).eval (ambTheta F))
          (keyEval F Θ M) := by
    funext j
    rw [finalP, Polynomial.eval_finsetSum, Matrix.vecMul_apply]
    simp only [dotProduct, Matrix.col_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, keyEval, evalMatHom_apply]
  rw [h1]
  exact vecMul_ne_zero_of_det_ne_zero F (det_keyEval_ne_zero F h hM) hv

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]

/-! ## §6. The coefficient subring `A_0` and the adjugate -/

/-- The subring of `L[t]` consisting of the polynomials all of whose coefficients lie in
`A_ν = F_q[θ_ν]`. -/
def polyA0 (ν : ℕ) : Subring (Polynomial (Ambient F)) where
  carrier := {p | ∀ m, p.coeff m ∈ ambASub F ν}
  mul_mem' := by
    intro p q hp hq m
    rw [Polynomial.coeff_mul]
    exact ambA_sum_mem F fun x _ => ambA_mul_mem F (hp x.1) (hq x.2)
  one_mem' := by
    intro m
    rw [Polynomial.coeff_one]
    split_ifs with h
    · exact ambA_one_mem F ν
    · exact (ambASub F ν).zero_mem
  add_mem' := by
    intro p q hp hq m
    rw [Polynomial.coeff_add]
    exact ambA_add_mem F (hp m) (hq m)
  zero_mem' := by
    intro m
    rw [Polynomial.coeff_zero]
    exact (ambASub F ν).zero_mem
  neg_mem' := by
    intro p hp m
    rw [Polynomial.coeff_neg]
    exact (ambASub F ν).neg_mem (hp m)

lemma mem_polyA0_iff (ν : ℕ) (p : Polynomial (Ambient F)) :
    p ∈ polyA0 F ν ↔ ∀ m, p.coeff m ∈ ambASub F ν := Iff.rfl

/-- The determinant of a matrix whose entries have all their coefficients in `A_0` again has all
its coefficients in `A_0`. -/
lemma det_mem {n ν : ℕ} {M : Matrix (Fin n) (Fin n) (Polynomial (Ambient F))}
    (h : ∀ i j, M i j ∈ polyA0 F ν) : M.det ∈ polyA0 F ν := by
  rw [Matrix.det_apply]
  refine (polyA0 F ν).sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact (polyA0 F ν).zsmul_mem ((polyA0 F ν).prod_mem fun i _ => h (σ i) i) ↑(Equiv.Perm.sign σ)

/-- The same for the adjugate. -/
lemma adjugate_mem {n ν : ℕ} {M : Matrix (Fin n) (Fin n) (Polynomial (Ambient F))}
    (h : ∀ i j, M i j ∈ polyA0 F ν) (i j : Fin n) : M.adjugate i j ∈ polyA0 F ν := by
  rw [Matrix.adjugate_apply]
  refine det_mem F fun a b => ?_
  rw [Matrix.updateRow_apply]
  by_cases h1 : a = j
  · rw [if_pos h1]
    by_cases h2 : b = i
    · subst h2
      rw [Pi.single_eq_same]
      exact (polyA0 F ν).one_mem
    · rw [Pi.single_eq_of_ne (by omega)]
      exact (polyA0 F ν).zero_mem
  · rw [if_neg h1]
    exact h a b

/-- **The adjugate of a matrix with `A_ν`-coefficients has `A_ν`-coefficients.** -/
lemma adjugate_coeff_mem {n ν : ℕ} {Φ : Matrix (Fin n) (Fin n) (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambASub F ν) (i j : Fin n) (m : ℕ) :
    (Φ.adjugate i j).coeff m ∈ ambASub F ν :=
  adjugate_mem F (fun i j => (mem_polyA0_iff F ν _).mpr (hΦ i j)) i j m

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]

/-- A nonzero element of `A_ν` has valuation at least `1`. -/
lemma one_le_v_of_mem_ambA {ν : ℕ} {x : Ambient F} (hx : x ∈ ambA F ν) (hx0 : x ≠ 0) :
    1 ≤ Valued.v x := by
  obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν x).mp hx
  have hp : p ≠ 0 := fun h0 => hx0 (by rw [h0]; simp)
  rw [v_eval₂_ambThetaNu F ν p hp]
  exact one_le_pow₀ (le_of_lt (one_lt_ambKappa F ν))

end

end ZagierHoffmanPositiveChar
