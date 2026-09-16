import Submission.ZagierHoffmanProof.ABPSiegel
import Submission.ZagierHoffmanProof.AmbRootLevel

/-!
# The auxiliary function of the ABP criterion

This module carries out step (A) of the proof of the ABP criterion
(`Anderson–Brownawell–Papanikolas`, Theorem 3.1.1; `Dac`, Theorem 4.2): the construction of the
auxiliary function `h` by Siegel's lemma (Thue–Siegel), over the ambient field `L = Ambient F`.

The system to be solved is, for each `M ∈ {N, …, 2N-1}` and each column `c` of `ϑ`,

  `∑_{j,e} h_{j,e} · θ_M^e · (Z_M(θ_M))_{j,c} = 0`,

where `Z_M = Θ^{(0)} ⋯ Θ^{(-(M-1))} ϑ^{(-M)}` and `θ_M` is the `q^M`-th root of `θ`.  Since
`(Z_M(θ_M))_{j,c}` is the `q^M`-th root of `(X_M(θ) ϑ)_{j,c}` (`X_M = Θ^{(M)} ⋯ Θ^{(1)}`), every
entry of the system lives in `A_M ⊆ A_ν`, and its size is bounded **independently of `N`**.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]

/-! ## §1. A level-reporting variant of the level-free Siegel lemma -/

/-- **The level-free Siegel lemma, reporting the level.**  Same as `ABPSiegel.siegel_union`, but
the level `ν` of the solution is returned and can be required to be at least `ν_min`. -/
theorem siegel_union_level {R S : Type*} [Fintype R] [Fintype S]
    (hcard : Fintype.card R < Fintype.card S) {c d : ℚ} (hc : 0 < c)
    (hcd : (Fintype.card R : ℚ) * c < ((Fintype.card S : ℚ) - Fintype.card R) * d)
    {ν_min : ℕ} (M : Matrix R S (Ambient F))
    (hMmem : ∀ i j, ∃ ν, M i j ∈ ambA F ν)
    (hMsize : ∀ i j, Valued.v (M i j) ≤ WithZero.exp c) :
    ∃ (ν : ℕ) (z : S → Ambient F), ν_min ≤ ν ∧ (∀ j, z j ∈ ambA F ν) ∧
      (∀ j, Valued.v (z j) ≤ WithZero.exp d) ∧ z ≠ 0 ∧ M.mulVec z = 0 := by
  classical
  have hq2 : (2 : ℚ) ≤ Nat.card F := by
    have := two_le_card_field F; exact_mod_cast this
  set k : ℚ := (Nat.card F : ℚ) - 1 with hkdef
  have hkpos : 0 < k := by rw [hkdef]; linarith
  set χ : R → S → ℕ := fun i j => Classical.choose (hMmem i j) with hχdef
  have hχspec : ∀ i j, M i j ∈ ambA F (χ i j) := fun i j => Classical.choose_spec (hMmem i j)
  set ν₀ : ℕ := Finset.univ.sup (fun i => Finset.univ.sup (fun j => χ i j)) with hν₀def
  have hχν₀ : ∀ i j, χ i j ≤ ν₀ := by
    intro i j
    rw [hν₀def]
    exact le_trans (Finset.le_sup (f := fun j => χ i j) (Finset.mem_univ j))
      (Finset.le_sup (f := fun i => Finset.univ.sup (fun j => χ i j)) (Finset.mem_univ i))
  set dC : ℚ := c / k with hdCdef
  set dD : ℚ := d / k with hdDdef
  have hΔpos : 0 < ((Fintype.card S : ℚ) - Fintype.card R) * dD - (Fintype.card R : ℚ) * dC := by
    have hsr : (Fintype.card R : ℚ) < (Fintype.card S : ℚ) := by exact_mod_cast hcard
    have h1 : (Fintype.card R : ℚ) * dC = (Fintype.card R : ℚ) * c / k := by
      rw [hdCdef]; ring
    have h2 : ((Fintype.card S : ℚ) - Fintype.card R) * dD
        = ((Fintype.card S : ℚ) - Fintype.card R) * d / k := by rw [hdDdef]; ring
    rw [h1, h2, sub_pos, div_lt_div_iff_of_pos_right hkpos]
    exact hcd
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fintype.card R : ℚ)
    / (((Fintype.card S : ℚ) - Fintype.card R) * dD - (Fintype.card R : ℚ) * dC))
  set ν : ℕ := max ν₀ (max N (max ν_min 1)) with hνdef
  have hν₀le : ν₀ ≤ ν := le_max_left ν₀ (max N (max ν_min 1))
  have hNle : N ≤ ν := le_trans (le_max_left N (max ν_min 1)) (le_max_right ν₀ (max N (max ν_min 1)))
  have hνminle : ν_min ≤ ν :=
    le_trans (le_max_left ν_min 1)
      (le_trans (le_max_right N (max ν_min 1)) (le_max_right ν₀ (max N (max ν_min 1))))
  set μ : ℕ := Nat.ceil (((Nat.card F : ℚ) ^ ν) * dC) with hμdef
  set mm : ℕ := Nat.floor (((Nat.card F : ℚ) ^ ν) * dD) with hmmdef
  have hμge : ((Nat.card F : ℚ) ^ ν) * dC ≤ (μ : ℚ) := by
    rw [hμdef]; exact Nat.le_ceil _
  have hsrq : (0 : ℚ) < (Fintype.card S : ℚ) - Fintype.card R := by
    have : (Fintype.card R : ℚ) < (Fintype.card S : ℚ) := by exact_mod_cast hcard
    linarith
  have hdpos : 0 < d := by nlinarith [hcd, hc, hsrq]
  have hmmle : (mm : ℚ) ≤ ((Nat.card F : ℚ) ^ ν) * dD := by
    rw [hmmdef]
    exact Nat.floor_le (by rw [hdDdef]; positivity)
  have hmmgt : ((Nat.card F : ℚ) ^ ν) * dD - 1 < (mm : ℚ) := by
    have h := Nat.lt_floor_add_one (((Nat.card F : ℚ) ^ ν) * dD)
    rw [hmmdef]
    push_cast
    linarith
  have hqpowN : (N : ℚ) ≤ (Nat.card F : ℚ) ^ ν := by
    have h1 : (N : ℚ) ≤ (ν : ℚ) := by exact_mod_cast hNle
    have h2 : (ν : ℚ) < (2 : ℚ) ^ ν := by
      have h : ν < 2 ^ ν := Nat.lt_two_pow_self
      exact_mod_cast h
    have h3 : (2 : ℚ) ^ ν ≤ (Nat.card F : ℚ) ^ ν :=
      pow_le_pow_left₀ (by norm_num) hq2 ν
    linarith
  have hkey : (Fintype.card R : ℚ)
      < ((Nat.card F : ℚ) ^ ν) * (((Fintype.card S : ℚ) - Fintype.card R) * dD
          - (Fintype.card R : ℚ) * dC) := by
    have hN' : (Fintype.card R : ℚ)
        < (N : ℚ) * (((Fintype.card S : ℚ) - Fintype.card R) * dD
            - (Fintype.card R : ℚ) * dC) := by
      have h := mul_lt_mul_of_pos_right hN hΔpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hΔpos)] at h
    have hNnn : (0 : ℚ) ≤ (N : ℚ) := Nat.cast_nonneg N
    nlinarith [hN', hqpowN, hΔpos]
  have hμlt : (μ : ℚ) < ((Nat.card F : ℚ) ^ ν) * dC + 1 := by
    have h := Nat.ceil_lt_add_one (a := ((Nat.card F : ℚ) ^ ν) * dC) (by positivity)
    simpa [hμdef] using h
  have hm : (mm + μ + 1) * Fintype.card R < (mm + 1) * Fintype.card S := by
    have hcast : ((mm : ℚ) + μ + 1) * (Fintype.card R : ℚ)
        < ((mm : ℚ) + 1) * (Fintype.card S : ℚ) := by
      nlinarith [hμlt, hmmgt, hkey, hsrq]
    exact_mod_cast hcast
  have hMν : ∀ i j, M i j ∈ ambA F ν ∧ Valued.v (M i j) ≤ (ambKappa F ν) ^ μ := by
    intro i j
    refine ⟨ambA_mono F (le_trans (hχν₀ i j) hν₀le) (hχspec i j), ?_⟩
    rw [ambKappa, expmul_rat, mul_comm]
    have h2 : (((Nat.card F : ℚ) ^ ν) * dC) * (k / (Nat.card F : ℚ) ^ ν) = c := by
      rw [hdCdef]; field_simp
    calc Valued.v (M i j) ≤ WithZero.exp c := hMsize i j
      _ = WithZero.exp ((((Nat.card F : ℚ) ^ ν) * dC) * (k / (Nat.card F : ℚ) ^ ν)) := by
          rw [h2]
      _ ≤ WithZero.exp ((μ : ℚ) * (k / (Nat.card F : ℚ) ^ ν)) := by
          refine WithZero.exp_le_exp.mpr ?_
          exact mul_le_mul_of_nonneg_right hμge
            (show (0 : ℚ) ≤ k / (Nat.card F : ℚ) ^ ν by positivity)
  obtain ⟨z, hz, hz0, hzM⟩ := siegel_one (F := F) (ν := ν) (μ := μ) (m := mm) hcard hm M hMν
  refine ⟨ν, z, hνminle, fun j => (hz j).1, fun j => ?_, hz0, hzM⟩
  have h2 : (((Nat.card F : ℚ) ^ ν) * dD) * (k / (Nat.card F : ℚ) ^ ν) = d := by
    rw [hdDdef]; field_simp
  have hz2 : Valued.v (z j) ≤ WithZero.exp ((mm : ℚ) * (k / (Nat.card F : ℚ) ^ ν)) := by
    have h := (hz j).2
    rw [ambKappa, expmul_rat, mul_comm] at h
    exact h
  refine le_trans hz2 (WithZero.exp_le_exp.mpr ?_)
  rw [← h2]
  exact mul_le_mul_of_nonneg_right hmmle (by positivity)

/-! ## §2. Evaluation at `θ` and membership in `A_0` -/

/-- **The level drops by `j` under the `q^j`-th power map**: for `x = p(θ_ν)` one has
`x^(q^j) = p(θ_{ν-j})`. -/
lemma ambA_pow_card_pow_mem_level {ν j : ℕ} (hj : j ≤ ν) {x : Ambient F}
    (hx : x ∈ ambA F ν) : x ^ (Nat.card F ^ j) ∈ ambA F (ν - j) := by
  obtain ⟨p, rfl⟩ := (mem_ambA_iff F ν x).mp hx
  haveI : FrobPow (Ambient F) (Nat.card F ^ j) := (frobPow_ambient F).pow j
  have hνj : ν - j ≤ ν := Nat.sub_le ν j
  have hsub : ν - (ν - j) = j := Nat.sub_sub_self hj
  have hgl : ambThetaNu F (ν - j) = ambThetaNu F ν ^ (Nat.card F ^ j) := by
    rw [ambThetaNu_eq_pow F hνj, hsub]
  have hpow : (p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F ν)) ^ (Nat.card F ^ j)
      = p.eval₂ (algebraMap F (Ambient F)) (ambThetaNu F (ν - j)) := by
    rw [Polynomial.eval₂_eq_sum_range, FrobPow.sum_pow_finset]
    rw [Polynomial.eval₂_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ← pow_mul, ← map_pow, pow_card_pow, show i * Nat.card F ^ j
      = Nat.card F ^ j * i by ring, pow_mul, ← hgl]
  rw [hpow]
  exact (mem_ambA_iff F (ν - j) _).mpr ⟨p, rfl⟩

/-- Evaluation of a Frobenius twist at `θ`. -/
lemma eval_polyTwist (j : ℕ) (p : Polynomial (Ambient F)) :
    (polyTwist (q := Nat.card F) j p).eval (ambTheta F)
      = (p.eval (ambThetaNu F j)) ^ (Nat.card F ^ j) := by
  haveI : FrobPow (Ambient F) (Nat.card F ^ j) := (frobPow_ambient F).pow j
  rw [polyTwist, polyTwistHom_apply, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range,
    Polynomial.eval_eq_sum_range, FrobPow.sum_pow_finset]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frobPowHom_apply, mul_pow]
  congr 1
  rw [← pow_mul, show i * Nat.card F ^ j = Nat.card F ^ j * i by ring, pow_mul,
    ← ambThetaNu_pow]

/-- The twist of a polynomial with `A_ν`-coefficients, evaluated at `θ`, lies in `A_ν`. -/
lemma eval_polyTwist_mem {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ m, p.coeff m ∈ ambA F ν) (j : ℕ) :
    (polyTwist (q := Nat.card F) j p).eval (ambTheta F) ∈ ambA F ν := by
  rw [eval_polyTwist]
  have h1 : p.eval (ambThetaNu F j) ∈ ambA F (ν + j) := by
    rw [Polynomial.eval_eq_sum_range]
    refine ambA_sum_mem F (fun m _ => ambA_mul_mem F ?_ ?_)
    · exact ambA_mono F (Nat.le_add_right ν j) (hp m)
    · exact ambA_mono F (Nat.le_add_left j ν) (ambThetaNu_pow_mem F j m)
  have h2 := ambA_pow_card_pow_mem_level F (ν := ν + j) (show j ≤ ν + j by omega) h1
  rwa [Nat.add_sub_cancel] at h2

/-- The evaluation-at-`θ` ring homomorphism on `ℓ × ℓ` matrices of polynomials. -/
def evalMatHom {ℓ : ℕ} :
    Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)) →+*
      Matrix (Fin ℓ) (Fin ℓ) (Ambient F) :=
  (Polynomial.evalRingHom (ambTheta F)).mapMatrix

lemma evalMatHom_apply {ℓ : ℕ} (A : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (i j : Fin ℓ) : evalMatHom F A i j = (A i j).eval (ambTheta F) := by
  rw [evalMatHom, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

/-- The `θ`-evaluation of the `M`-th key product `X_M = Θ^{(M)} ⋯ Θ^{(1)}`. -/
def keyEval {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) (M : ℕ) :
    Matrix (Fin ℓ) (Fin ℓ) (Ambient F) :=
  evalMatHom F (keyProdPoly (q := Nat.card F) Θ M)

lemma keyEval_zero {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) :
    keyEval F Θ 0 = 1 := by
  rw [keyEval, keyProdPoly_zero, map_one]

lemma keyEval_succ {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) (M : ℕ) :
    keyEval F Θ (M + 1)
      = evalMatHom F ((polyTwistHom (q := Nat.card F) (M + 1)).mapMatrix Θ) * keyEval F Θ M := by
  rw [keyEval, keyProdPoly_succ, map_mul, keyEval]

lemma keyEval_succ_apply {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) (M : ℕ)
    (i j : Fin ℓ) :
    keyEval F Θ (M + 1) i j
      = ∑ k : Fin ℓ, (polyTwist (q := Nat.card F) (M + 1) (Θ i k)).eval (ambTheta F)
          * keyEval F Θ M k j := by
  rw [keyEval_succ, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [evalMatHom_apply]
  rfl

/-- **Membership: `X_M(θ)` has entries in `A_ν` when `Θ` has `A_ν`-coefficients.** -/
lemma keyEval_mem {ℓ ν : ℕ} {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν) (M : ℕ) (i j : Fin ℓ) :
    keyEval F Θ M i j ∈ ambA F ν := by
  induction M generalizing i j with
  | zero =>
      rw [keyEval_zero, Matrix.one_apply]
      split_ifs with h
      · exact ambA_one_mem F ν
      · exact (ambASub F ν).zero_mem
  | succ M ih =>
      rw [keyEval_succ_apply]
      exact ambA_sum_mem F (fun k _ =>
        ambA_mul_mem F (eval_polyTwist_mem F (fun m => hΘ i k m) (M + 1)) (ih k j))

/-! ## §3. Size bounds (independent of `N`) -/

/-- The maximum `t`-degree of a finite family of polynomials. -/
def degSup {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) : ℕ :=
  Finset.univ.sup (fun i => (P i).natDegree)

lemma natDegree_le_degSup {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) (i : ι) :
    (P i).natDegree ≤ degSup F P :=
  Finset.le_sup (f := fun i => (P i).natDegree) (Finset.mem_univ i)

/-- The product of `max 1 (v c)` over the coefficients `c` of a finite family of polynomials:
a uniform upper bound for all of them, independent of any choice of maximum. -/
noncomputable def coeffProd {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) : WithZero (Multiplicative ℚ) :=
  ∏ im : ι × Fin (degSup F P + 1), max 1 (Valued.v ((P im.1).coeff (im.2 : ℕ)))

lemma coeffProd_ne_zero {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) :
    coeffProd F P ≠ 0 := by
  rw [coeffProd]
  refine Finset.prod_ne_zero_iff.mpr (fun im _ => ?_)
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

lemma val_coeff_le_coeffProd {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) (i : ι)
    (m : ℕ) : Valued.v ((P i).coeff m) ≤ coeffProd F P := by
  rcases eq_or_ne ((P i).coeff m) 0 with h0 | h0
  · rw [h0, map_zero]
    exact zero_le
  · have hm : m ≤ degSup F P :=
      le_trans (Polynomial.le_natDegree_of_ne_zero h0) (natDegree_le_degSup F P i)
    have hmem : (i, ⟨m, Nat.lt_succ_of_le hm⟩) ∈
        (Finset.univ : Finset (ι × Fin (degSup F P + 1))) := Finset.mem_univ _
    have hle := Finset.single_le_prod'
      (f := fun im : ι × Fin (degSup F P + 1) =>
        max 1 (Valued.v ((P im.1).coeff (im.2 : ℕ))))
      (fun im _ => le_max_left _ _) hmem
    rw [coeffProd]
    exact le_trans (le_max_right _ _) hle

/-- A positive rational bounding the logarithms of all the coefficient valuations of a finite
family of polynomials. -/
noncomputable def valBound {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) : ℚ :=
  max 1 (WithZero.log (coeffProd F P))

lemma valBound_pos {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) :
    0 < valBound F P := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma val_coeff_le_valBound {ι : Type*} [Fintype ι] (P : ι → Polynomial (Ambient F)) (i : ι)
    (m : ℕ) : Valued.v ((P i).coeff m) ≤ WithZero.exp (valBound F P) := by
  refine le_trans (val_coeff_le_coeffProd F P i m) ?_
  rw [valBound]
  calc coeffProd F P = WithZero.exp (WithZero.log (coeffProd F P)) :=
        (WithZero.exp_log (coeffProd_ne_zero F P)).symm
    _ ≤ WithZero.exp (max 1 (WithZero.log (coeffProd F P))) :=
        WithZero.exp_le_exp.mpr (le_max_right _ _)

/-- The valuation of a Frobenius twist evaluated at `θ`. -/
lemma v_eval_polyTwist_le {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (k : ℕ) (i j : Fin ℓ) :
    Valued.v ((polyTwist (q := Nat.card F) k (Θ i j)).eval (ambTheta F))
      ≤ WithZero.exp ((valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2)
          + ((Nat.card F : ℚ) - 1) * (degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) : ℚ)
            / (Nat.card F : ℚ) ^ k) * (Nat.card F : ℚ) ^ k) := by
  rw [eval_polyTwist, map_pow]
  have hq1 : (1 : ℚ) ≤ (Nat.card F : ℚ) := by
    have := two_le_card_field F
    exact_mod_cast (by omega : 1 ≤ Nat.card F)
  have hqpos : (0 : ℚ) < (Nat.card F : ℚ) := by linarith
  have hstep : Valued.v ((Θ i j).eval (ambThetaNu F k))
      ≤ WithZero.exp (valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2)
          + ((Nat.card F : ℚ) - 1)
              * (degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) : ℚ)
            / (Nat.card F : ℚ) ^ k) := by
    rw [Polynomial.eval_eq_sum_range]
    refine Valuation.map_sum_le _ (fun m hm => ?_)
    rw [map_mul, map_pow, v_ambThetaNu]
    have hPdeg : m ≤ degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) :=
      le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
        (natDegree_le_degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) (i, j))
    have h1 : Valued.v ((Θ i j).coeff m)
        ≤ WithZero.exp (valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2)) :=
      val_coeff_le_valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) (i, j) m
    have h2 : (ambKappa F k) ^ m ≤ WithZero.exp (((Nat.card F : ℚ) - 1)
        * (degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) : ℚ)
          / (Nat.card F : ℚ) ^ k) := by
      rw [ambKappa, expmul_rat, WithZero.exp_le_exp]
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (pow_pos hqpos k)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hPdeg) (by linarith [hq1])
    calc Valued.v ((Θ i j).coeff m) * (ambKappa F k) ^ m
        ≤ WithZero.exp (valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2))
          * WithZero.exp (((Nat.card F : ℚ) - 1)
              * (degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) : ℚ)
            / (Nat.card F : ℚ) ^ k) := mul_le_mul' h1 h2
      _ = WithZero.exp (valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2)
            + ((Nat.card F : ℚ) - 1)
                * (degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) : ℚ)
              / (Nat.card F : ℚ) ^ k) := (WithZero.exp_add _ _).symm
  calc Valued.v ((Θ i j).eval (ambThetaNu F k)) ^ (Nat.card F ^ k)
      ≤ (WithZero.exp (valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2)
            + ((Nat.card F : ℚ) - 1)
                * (degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) : ℚ)
              / (Nat.card F : ℚ) ^ k)) ^ (Nat.card F ^ k) := pow_le_pow_left₀ zero_le hstep _
    _ = WithZero.exp ((valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2)
            + ((Nat.card F : ℚ) - 1)
                * (degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) : ℚ)
              / (Nat.card F : ℚ) ^ k) * (Nat.card F : ℚ) ^ k) := by
        rw [expmul_rat]
        congr 1
        rw [Nat.cast_pow]

/-- **The size of `X_M(θ)` is bounded by `exp(B · q^M)`** with `B` independent of `M`. -/
lemma keyEval_bound {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) :
    ∃ B : ℚ, 0 < B ∧ ∀ M (i j : Fin ℓ),
      Valued.v (keyEval F Θ M i j) ≤ WithZero.exp (B * (Nat.card F : ℚ) ^ M) := by
  set q : ℚ := (Nat.card F : ℚ) with hqdef
  have hq2 : (2 : ℚ) ≤ q := by
    have := two_le_card_field F
    rw [hqdef]; exact_mod_cast this
  have hqpos : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hqm1 : 0 < q - 1 := by linarith
  set cΘ : ℚ := valBound F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) with hc
  set dΘ : ℕ := degSup F (fun p : Fin ℓ × Fin ℓ => Θ p.1 p.2) with hd
  have hcΘpos : 0 < cΘ := by rw [hc]; exact valBound_pos F _
  have hnum : 0 < cΘ * q + (q - 1) * (dΘ : ℚ) :=
    add_pos_of_pos_of_nonneg (mul_pos hcΘpos hqpos) (mul_nonneg hqm1.le (Nat.cast_nonneg dΘ))
  have hBpos : 0 < (cΘ * q + (q - 1) * (dΘ : ℚ)) / (q - 1) + 1 := by
    have := div_pos hnum hqm1; linarith
  refine ⟨(cΘ * q + (q - 1) * (dΘ : ℚ)) / (q - 1) + 1, hBpos, ?_⟩
  intro M
  induction M with
  | zero =>
      intro i j
      rw [keyEval_zero, Matrix.one_apply]
      split_ifs with h
      · simp only [map_one, pow_zero, mul_one]
        simpa [WithZero.exp_zero] using WithZero.exp_le_exp.mpr hBpos.le
      · rw [map_zero]
        exact zero_le
  | succ M ih =>
      intro i j
      rw [keyEval_succ_apply]
      refine Valuation.map_sum_le _ (fun k _ => ?_)
      rw [map_mul]
      set A : ℚ := cΘ * q + (q - 1) * (dΘ : ℚ) with hAdef
      set B : ℚ := A / (q - 1) + 1 with hBdef
      have hA' : Valued.v ((polyTwist (q := Nat.card F) (M + 1) (Θ i k)).eval (ambTheta F))
          ≤ WithZero.exp (A * q ^ M) := by
        refine le_trans (v_eval_polyTwist_le F Θ (M + 1) i k) ?_
        rw [WithZero.exp_le_exp]
        have hpow : (Nat.card F : ℚ) ^ (M + 1) = q ^ M * q := by
          rw [pow_succ]
          try rfl
        rw [hpow, hAdef]
        have h1 : (cΘ + (q - 1) * (dΘ : ℚ) / (q ^ M * q)) * (q ^ M * q)
            = cΘ * (q ^ M * q) + (q - 1) * (dΘ : ℚ) := by
          field_simp
          try ring
        rw [h1]
        have h3 : (cΘ * q + (q - 1) * (dΘ : ℚ)) * q ^ M
            = cΘ * (q ^ M * q) + (q - 1) * (dΘ : ℚ) * q ^ M := by ring
        rw [h3]
        exact add_le_add le_rfl
          (le_mul_of_one_le_right (mul_nonneg hqm1.le (Nat.cast_nonneg dΘ))
            (one_le_pow₀ hq1))
      have hB' : Valued.v (keyEval F Θ M k j) ≤ WithZero.exp (B * q ^ M) := by
        rw [hBdef, hAdef]
        exact ih k j
      have hkey : A + B ≤ B * q := by
        have h4 : B * q = B * (q - 1) + B := by ring
        rw [h4, hBdef]
        have h5 : (A / (q - 1) + 1) * (q - 1) = A + (q - 1) := by
          field_simp
          try ring
        rw [h5]
        linarith
      calc Valued.v ((polyTwist (q := Nat.card F) (M + 1) (Θ i k)).eval (ambTheta F))
            * Valued.v (keyEval F Θ M k j)
          ≤ WithZero.exp (A * q ^ M) * WithZero.exp (B * q ^ M) := mul_le_mul' hA' hB'
        _ = WithZero.exp ((A + B) * q ^ M) := by
            rw [← WithZero.exp_add]; congr 1; ring
        _ ≤ WithZero.exp (B * q ^ (M + 1)) := by
            refine WithZero.exp_le_exp.mpr ?_
            rw [pow_succ]
            calc (A + B) * q ^ M ≤ (B * q) * q ^ M :=
                  mul_le_mul_of_nonneg_right hkey (by positivity)
              _ = B * (q ^ M * q) := by ring
        _ = WithZero.exp (((cΘ * q + (q - 1) * (dΘ : ℚ)) / (q - 1) + 1) * q ^ (M + 1)) := by
            rw [hBdef, hAdef]
/-! ## §4. The auxiliary system: entries, membership, size -/

/-- `θ = θ_0`. -/
lemma ambThetaNu_zero : ambThetaNu F 0 = ambTheta F := by
  simpa using ambThetaNu_pow F 0

/-- `θ^e ∈ A_0`. -/
lemma ambTheta_pow_mem (e : ℕ) : (ambTheta F) ^ e ∈ ambA F 0 := by
  rw [← ambThetaNu_zero F]
  exact ambThetaNu_pow_mem F 0 e

/-- `θ_M ∈ A_M`. -/
lemma ambThetaNu_mem (M : ℕ) : ambThetaNu F M ∈ ambA F M := by
  simpa using ambThetaNu_pow_mem F M 1

/-- `A_ν` is closed under the twist by `j ≤ ν`. -/
lemma ambA_frobTwist_mem {ν j : ℕ} (hj : j ≤ ν) {x : Ambient F} (hx : x ∈ ambA F ν) :
    x ^ (Nat.card F ^ j) ∈ ambA F ν :=
  ambA_mono F (Nat.sub_le ν j) (ambA_pow_card_pow_mem_level F hj hx)

/-- The size of `θ_M^e` for `e ≤ M`. -/
lemma v_ambThetaNu_pow_le {M e : ℕ} (heM : e ≤ M) :
    Valued.v ((ambThetaNu F M) ^ e) ≤ WithZero.exp ((Nat.card F : ℚ) - 1) := by
  have hq : (0 : ℚ) < (Nat.card F : ℚ) := by
    have := two_le_card_field F
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) this)
  have hq2 : (2 : ℚ) ≤ Nat.card F := by
    have := two_le_card_field F; exact_mod_cast this
  rw [map_pow, v_ambThetaNu, ambKappa, expmul_rat, WithZero.exp_le_exp]
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hq M)]
  have he : (e : ℚ) ≤ (Nat.card F : ℚ) ^ M := by
    have h1 : ((M : ℕ) : ℚ) ≤ (2 : ℚ) ^ M := by
      exact_mod_cast (le_of_lt Nat.lt_two_pow_self)
    have h2 : (2 : ℚ) ^ M ≤ (Nat.card F : ℚ) ^ M := pow_le_pow_left₀ (by norm_num) hq2 M
    exact le_trans (by exact_mod_cast heM) (le_trans h1 h2)
  nlinarith

/-- The element of `A_0` underlying the `(M, e, j, c)`-entry of the auxiliary system. -/
noncomputable def auxK {ℓ : ℕ} (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (M : ℕ) (j : Fin ℓ) (c : Fin (ℓ - 1)) :
    Ambient F :=
  (keyEval F Θ M * ϑ) j c

lemma auxK_mem {ℓ ν : ℕ} {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)} (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    (M : ℕ) (j : Fin ℓ) (c : Fin (ℓ - 1)) : auxK F Θ ϑ M j c ∈ ambA F ν := by
  rw [auxK, Matrix.mul_apply]
  exact ambA_sum_mem F (fun k _ => ambA_mul_mem F (keyEval_mem F hΘ M j k) (hϑ k c))

/-- The `(M, e, j, c)`-entry of the auxiliary system: `θ_M^e · (Z_M(θ_M))_{j,c}`. -/
noncomputable def auxEntry {ℓ : ℕ} (ν : ℕ)
    (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (M e : ℕ) (j : Fin ℓ) (c : Fin (ℓ - 1)) :
    Ambient F := by
  classical
  exact if h : auxK F Θ ϑ M j c ∈ ambA F ν then
    (ambThetaNu F M) ^ e * ambRootAt F ν M (auxK F Θ ϑ M j c) h
  else 0

lemma auxEntry_eq {ℓ ν : ℕ} {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)} {M e : ℕ} {j : Fin ℓ} {c : Fin (ℓ - 1)}
    (h : auxK F Θ ϑ M j c ∈ ambA F ν) :
    auxEntry F ν Θ ϑ M e j c
      = (ambThetaNu F M) ^ e * ambRootAt F ν M (auxK F Θ ϑ M j c) h := by
  rw [auxEntry]
  exact dif_pos h

lemma auxEntry_mem {ℓ ν : ℕ} {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)} (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    (M e : ℕ) (j : Fin ℓ) (c : Fin (ℓ - 1)) : auxEntry F ν Θ ϑ M e j c ∈ ambA F (ν + M) := by
  have hK := auxK_mem F hΘ hϑ M j c
  rw [auxEntry_eq F hK]
  exact ambA_mul_mem F
    (ambA_mono F (Nat.le_add_left M ν) (ambA_pow_mem F M (ambThetaNu_mem F M) e))
    (ambRootAt_mem F ν M _ hK)

/-- **The raised entry**: the `q^M`-th power of the `(M,e,j,c)`-entry of the auxiliary system
is `θ^e · (X_M(θ) ϑ)_{j,c}`. -/
lemma auxEntry_pow {ℓ ν : ℕ} {Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    {ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)} (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    (M e : ℕ) (j : Fin ℓ) (c : Fin (ℓ - 1)) :
    (auxEntry F ν Θ ϑ M e j c) ^ (Nat.card F ^ M)
      = (ambTheta F) ^ e * auxK F Θ ϑ M j c := by
  rw [auxEntry_eq F (auxK_mem F hΘ hϑ M j c), mul_pow, ambRootAt_pow, auxK]
  congr 1
  rw [← pow_mul, show e * Nat.card F ^ M = Nat.card F ^ M * e by ring, pow_mul,
    ← ambThetaNu_pow]
/-! ## §5. The size of the entries of the auxiliary system -/

/-- The product of `max 1 (v x i)` over a finite family: a uniform upper bound. -/
noncomputable def boxProd {ι : Type*} [Fintype ι] (x : ι → Ambient F) : WithZero (Multiplicative ℚ) :=
  ∏ i, max 1 (Valued.v (x i))

lemma boxProd_ne_zero {ι : Type*} [Fintype ι] (x : ι → Ambient F) : boxProd F x ≠ 0 := by
  rw [boxProd]
  refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

lemma val_le_boxProd {ι : Type*} [Fintype ι] (x : ι → Ambient F) (i : ι) :
    Valued.v (x i) ≤ boxProd F x := by
  have hle := Finset.single_le_prod' (f := fun i => max 1 (Valued.v (x i)))
    (fun i _ => le_max_left _ _) (Finset.mem_univ i)
  rw [boxProd]
  exact le_trans (le_max_right _ _) hle

/-- A positive rational bounding the logarithms of a finite family of valuations. -/
noncomputable def boxBound {ι : Type*} [Fintype ι] (x : ι → Ambient F) : ℚ :=
  max 1 (WithZero.log (boxProd F x))

lemma boxBound_pos {ι : Type*} [Fintype ι] (x : ι → Ambient F) : 0 < boxBound F x :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma val_le_boxBound {ι : Type*} [Fintype ι] (x : ι → Ambient F) (i : ι) :
    Valued.v (x i) ≤ WithZero.exp (boxBound F x) := by
  refine le_trans (val_le_boxProd F x i) ?_
  rw [boxBound]
  calc boxProd F x = WithZero.exp (WithZero.log (boxProd F x)) :=
        (WithZero.exp_log (boxProd_ne_zero F x)).symm
    _ ≤ WithZero.exp (max 1 (WithZero.log (boxProd F x))) :=
        WithZero.exp_le_exp.mpr (le_max_right _ _)

/-- A uniform bound for a finite family of elements of the ambient field. -/
lemma exists_val_bound {ι : Type*} [Fintype ι] (x : ι → Ambient F) :
    ∃ c : ℚ, 0 < c ∧ ∀ i, Valued.v (x i) ≤ WithZero.exp c :=
  ⟨boxBound F x, boxBound_pos F x, val_le_boxBound F x⟩

/-- **The size of the auxiliary-system entries is `O(1)`** (independent of `N`). -/
lemma auxEntry_bound {ℓ : ℕ} (ν : ℕ) (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (hϑ : ∀ i j, ϑ i j ∈ ambA F ν) :
    ∃ c : ℚ, 0 < c ∧ ∀ (N D M e : ℕ), D ≤ N → N ≤ M → e < D →
      ∀ (j : Fin ℓ) (c' : Fin (ℓ - 1)),
        Valued.v (auxEntry F ν Θ ϑ M e j c') ≤ WithZero.exp c := by
  obtain ⟨B, hBpos, hB⟩ := keyEval_bound F Θ
  obtain ⟨cϑ, hcϑpos, hcϑ⟩ := exists_val_bound F (fun p : Fin ℓ × Fin (ℓ - 1) => ϑ p.1 p.2)
  have hq2 : (2 : ℚ) ≤ Nat.card F := by
    have := two_le_card_field F; exact_mod_cast this
  have hqpos : (0 : ℚ) < Nat.card F := by linarith
  have hq1 : (1 : ℚ) ≤ Nat.card F := by linarith
  refine ⟨((Nat.card F : ℚ) - 1) + B + cϑ, by positivity, ?_⟩
  intro N D M e hDN hNM heD j c'
  have hsum : (keyEval F Θ M * ϑ) j c'
      = ∑ k : Fin ℓ, keyEval F Θ M j k * ϑ k c' := Matrix.mul_apply ..
  have hK : Valued.v (auxK F Θ ϑ M j c')
      ≤ WithZero.exp (B * (Nat.card F : ℚ) ^ M + cϑ) := by
    rw [auxK, hsum]
    refine Valuation.map_sum_le _ (fun k _ => ?_)
    rw [map_mul]
    calc Valued.v (keyEval F Θ M j k) * Valued.v (ϑ k c')
        ≤ WithZero.exp (B * (Nat.card F : ℚ) ^ M) * WithZero.exp cϑ :=
          mul_le_mul' (hB M j k) (hcϑ (k, c'))
      _ = WithZero.exp (B * (Nat.card F : ℚ) ^ M + cϑ) := (WithZero.exp_add _ _).symm
  have hqM : (0 : ℚ) < (Nat.card F : ℚ) ^ M := pow_pos hqpos M
  have hroot : Valued.v (ambRootAt F ν M (auxK F Θ ϑ M j c') (auxK_mem F hΘ hϑ M j c'))
      ≤ WithZero.exp (B + cϑ / (Nat.card F : ℚ) ^ M) := by
    have hqMn : Nat.card F ^ M ≠ 0 := pow_ne_zero M (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
    refine (pow_le_pow_iff_left₀ (zero_le : (0 : WithZero (Multiplicative ℚ)) ≤ _)
      (zero_le : (0 : WithZero (Multiplicative ℚ)) ≤ _) hqMn).mp ?_
    rw [v_ambRootAt_pow]
    calc Valued.v (auxK F Θ ϑ M j c') ≤ WithZero.exp (B * (Nat.card F : ℚ) ^ M + cϑ) := hK
      _ = (WithZero.exp (B + cϑ / (Nat.card F : ℚ) ^ M)) ^ (Nat.card F ^ M) := by
          rw [expmul_rat]
          congr 1
          rw [Nat.cast_pow]
          field_simp
          try ring
  have heM : e ≤ M := le_trans (le_of_lt heD) (le_trans hDN hNM)
  have hθM := v_ambThetaNu_pow_le F heM
  rw [auxEntry_eq F (auxK_mem F hΘ hϑ M j c')]
  calc Valued.v ((ambThetaNu F M) ^ e
        * ambRootAt F ν M (auxK F Θ ϑ M j c') (auxK_mem F hΘ hϑ M j c'))
      = Valued.v ((ambThetaNu F M) ^ e)
        * Valued.v (ambRootAt F ν M (auxK F Θ ϑ M j c') (auxK_mem F hΘ hϑ M j c')) := map_mul ..
    _ ≤ WithZero.exp ((Nat.card F : ℚ) - 1)
          * WithZero.exp (B + cϑ / (Nat.card F : ℚ) ^ M) := mul_le_mul' hθM hroot
    _ = WithZero.exp (((Nat.card F : ℚ) - 1) + (B + cϑ / (Nat.card F : ℚ) ^ M)) :=
        (WithZero.exp_add _ _).symm
    _ ≤ WithZero.exp (((Nat.card F : ℚ) - 1) + B + cϑ) := by
        refine WithZero.exp_le_exp.mpr ?_
        have hle : cϑ / (Nat.card F : ℚ) ^ M ≤ cϑ := by
          rw [div_le_iff₀ hqM]
          nlinarith [hcϑpos, hq1, (one_le_pow₀ hq1 : (1:ℚ) ≤ (Nat.card F : ℚ) ^ M)]
        linarith
/-! ## §6. The auxiliary function: Siegel's lemma -/

/-- The number of `t`-powers of the auxiliary function: `N - N/(2ℓ)`. -/
def auxDeg (N ℓ : ℕ) : ℕ := N - N / (2 * ℓ)

lemma auxDeg_mul_ge {ℓ N : ℕ} : N * ℓ - N / 2 ≤ ℓ * auxDeg N ℓ := by
  rw [auxDeg, Nat.mul_sub_left_distrib]
  have h1 : ℓ * (N / (2 * ℓ)) ≤ N / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 2)]
    calc ℓ * (N / (2 * ℓ)) * 2 = 2 * ℓ * (N / (2 * ℓ)) := by ring
      _ ≤ N := Nat.mul_div_le N (2 * ℓ)
  have h2 := Nat.sub_le_sub_left h1 (ℓ * N)
  rw [Nat.mul_comm N ℓ]
  exact h2

lemma one_le_auxDeg {ℓ N : ℕ} (hℓ : 1 ≤ ℓ) (hN : 2 * ℓ ≤ N) : 1 ≤ auxDeg N ℓ := by
  have h1 : N / (2 * ℓ) ≤ N / 2 := Nat.div_le_div_left (by omega : 2 ≤ 2 * ℓ) (by norm_num)
  have h2 : N / 2 ≤ N := Nat.div_le_self N 2
  have h3 : ℓ ≤ N / 2 := by omega
  rw [auxDeg]
  omega

lemma auxDeg_main {ℓ N : ℕ} (hℓ : 1 ≤ ℓ) (hN : 2 * ℓ ≤ N) : N * (ℓ - 1) < ℓ * auxDeg N ℓ := by
  have hge := auxDeg_mul_ge (ℓ := ℓ) (N := N)
  have h1 : N * (ℓ - 1) = N * ℓ - N := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have h2 : N / 2 < N := Nat.div_lt_self (by omega) (by norm_num)
  have hpos : 0 < ℓ * auxDeg N ℓ := by
    have := one_le_auxDeg hℓ hN
    positivity
  rw [h1]
  omega

lemma auxDeg_big {ℓ N : ℕ} (hℓ : 1 ≤ ℓ) (hN : 2 * ℓ ≤ N) :
    N * (ℓ - 1) < 2 * ℓ * (ℓ * auxDeg N ℓ - N * (ℓ - 1)) := by
  have hge := auxDeg_mul_ge (ℓ := ℓ) (N := N)
  have hsub : N * (ℓ - 1) = N * ℓ - N := by rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hsub2 : N - N / 2 ≤ ℓ * auxDeg N ℓ - N * (ℓ - 1) := by
    rw [hsub]
    have hNle : N ≤ N * ℓ := by
      calc N = N * 1 := (Nat.mul_one N).symm
        _ ≤ N * ℓ := Nat.mul_le_mul_left N hℓ
    have hA : N / 2 ≤ N * ℓ := le_trans (Nat.div_le_self N 2) hNle
    have h3 := Nat.sub_le_sub_right hge (N * ℓ - N)
    have h4 : (N * ℓ - N / 2) - (N * ℓ - N) = N - N / 2 := by omega
    rwa [h4] at h3
  have hd : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  have h2 : N ≤ 2 * (N - N / 2) := by
    have hmul : 2 * (N - N / 2) = 2 * N - 2 * (N / 2) := Nat.mul_sub_left_distrib 2 N (N / 2)
    omega
  have hmain : ℓ * N ≤ 2 * ℓ * (N - N / 2) := by
    calc ℓ * N ≤ ℓ * (2 * (N - N / 2)) := Nat.mul_le_mul_left ℓ h2
      _ = 2 * ℓ * (N - N / 2) := by ring
  calc N * (ℓ - 1) = N * ℓ - N := hsub
    _ < ℓ * N := by
      have hle : N ≤ ℓ * N := by
        calc N = 1 * N := (one_mul N).symm
          _ ≤ ℓ * N := Nat.mul_le_mul_right N hℓ
      rw [Nat.mul_comm N ℓ]
      omega
    _ ≤ 2 * ℓ * (N - N / 2) := hmain
    _ ≤ 2 * ℓ * (ℓ * auxDeg N ℓ - N * (ℓ - 1)) := Nat.mul_le_mul_left (2 * ℓ) hsub2

/-- The size constant of the auxiliary system (independent of `N`). -/
noncomputable def auxC {ℓ : ℕ} (ν : ℕ) (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (hϑ : ∀ i j, ϑ i j ∈ ambA F ν) : ℚ :=
  Classical.choose (auxEntry_bound F ν Θ hΘ ϑ hϑ)

lemma auxC_pos {ℓ : ℕ} (ν : ℕ) (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (hϑ : ∀ i j, ϑ i j ∈ ambA F ν) :
    0 < auxC F ν Θ hΘ ϑ hϑ := (Classical.choose_spec (auxEntry_bound F ν Θ hΘ ϑ hϑ)).1

lemma auxEntry_le_auxC {ℓ : ℕ} (ν : ℕ) (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    {N D M e : ℕ} (hDN : D ≤ N) (hNM : N ≤ M) (heD : e < D) (j : Fin ℓ) (c' : Fin (ℓ - 1)) :
    Valued.v (auxEntry F ν Θ ϑ M e j c') ≤ WithZero.exp (auxC F ν Θ hΘ ϑ hϑ) :=
  (Classical.choose_spec (auxEntry_bound F ν Θ hΘ ϑ hϑ)).2 N D M e hDN hNM heD j c'

/-- The matrix of the auxiliary system. -/
noncomputable def auxMat {ℓ : ℕ} (ν : ℕ) (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (N D : ℕ) :
    Matrix (Fin N × Fin (ℓ - 1)) (Fin ℓ × Fin D) (Ambient F) :=
  fun p q => auxEntry F ν Θ ϑ (N + p.1) (q.2 : ℕ) q.1 p.2

/-- **The auxiliary function exists.**  For `N ≥ 4ℓ` there are `ν ≥ 2N` and a nonzero solution
of the auxiliary system in `A_ν^{ℓ × (N - N/(2ℓ))}` whose size is bounded by an explicit
constant, independent of `N`. -/
theorem aux_solution_exists {ℓ : ℕ} (ν : ℕ) (hℓ : 2 ≤ ℓ)
    (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    {N : ℕ} (hN : 4 * ℓ ≤ N) :
    ∃ (ν' : ℕ) (z : Fin ℓ × Fin (auxDeg N ℓ) → Ambient F),
      ν + 2 * N ≤ ν' ∧ (∀ q, z q ∈ ambA F ν') ∧
        (∀ q, Valued.v (z q) ≤ WithZero.exp (2 * ℓ * auxC F ν Θ hΘ ϑ hϑ)) ∧ z ≠ 0 ∧
        (auxMat F ν Θ ϑ N (auxDeg N ℓ)).mulVec z = 0 := by
  set C : ℚ := auxC F ν Θ hΘ ϑ hϑ with hCdef
  have hCpos : 0 < C := by rw [hCdef]; exact auxC_pos F ν Θ hΘ ϑ hϑ
  have hNpos : 0 < N := by omega
  have hℓ1 : 1 ≤ ℓ := by omega
  have hNl : ℓ < N := by omega
  have h2l : 2 * ℓ ≤ N := le_trans (Nat.mul_le_mul_right ℓ (by norm_num : 2 ≤ 4)) hN
  have hcard : Fintype.card (Fin N × Fin (ℓ - 1)) < Fintype.card (Fin ℓ × Fin (auxDeg N ℓ)) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    exact auxDeg_main hℓ1 h2l
  have hD := auxDeg_main hℓ1 h2l
  have hB := auxDeg_big hℓ1 h2l
  have hle : N * (ℓ - 1) ≤ ℓ * auxDeg N ℓ := le_of_lt hD
  have hcastD : ((N * (ℓ - 1) : ℕ) : ℚ) < ((ℓ * auxDeg N ℓ : ℕ) : ℚ) := by exact_mod_cast hD
  have hcastB : ((N * (ℓ - 1) : ℕ) : ℚ)
      < 2 * (ℓ : ℚ) * (((ℓ * auxDeg N ℓ : ℕ) : ℚ) - ((N * (ℓ - 1) : ℕ) : ℚ)) := by
    calc ((N * (ℓ - 1) : ℕ) : ℚ)
        < ((2 * ℓ * (ℓ * auxDeg N ℓ - N * (ℓ - 1)) : ℕ) : ℚ) := by exact_mod_cast hB
      _ = 2 * (ℓ : ℚ) * (((ℓ * auxDeg N ℓ : ℕ) : ℚ) - ((N * (ℓ - 1) : ℕ) : ℚ)) := by
          push_cast [Nat.cast_sub hle]
          ring
  have hcd : (Fintype.card (Fin N × Fin (ℓ - 1)) : ℚ) * C
      < ((Fintype.card (Fin ℓ × Fin (auxDeg N ℓ)) : ℚ)
          - Fintype.card (Fin N × Fin (ℓ - 1))) * (2 * ℓ * C) := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    nlinarith [hcastD, hcastB, hCpos]
  obtain ⟨ν', z, hν', hzmem, hzsize, hz0, hzmul⟩ :=
    siegel_union_level (F := F) hcard (c := C) (d := 2 * ℓ * C) hCpos hcd (ν_min := ν + 2 * N)
      (M := auxMat F ν Θ ϑ N (auxDeg N ℓ))
      (fun p q => ⟨ν + (N + p.1), by
        rw [auxMat]; exact auxEntry_mem F hΘ hϑ (N + p.1) (q.2 : ℕ) q.1 p.2⟩)
      (fun p q => by
        rw [auxMat]
        exact auxEntry_le_auxC F ν Θ hΘ ϑ hϑ (Nat.sub_le N (N / (2 * ℓ)))
          (Nat.le_add_right N p.1) q.2.isLt q.1 p.2)
  exact ⟨ν', z, hν', hzmem, hzsize, hz0, hzmul⟩
/-! ## §7. From the Siegel solution to the auxiliary function and its raised system -/

/-- The polynomial row vector associated with a solution vector of the auxiliary system. -/
noncomputable def auxPoly {ℓ D : ℕ} (z : Fin ℓ × Fin D → Ambient F) (j : Fin ℓ) :
    Polynomial (Ambient F) :=
  ∑ e : Fin D, Polynomial.monomial (e : ℕ) (z (j, e))

lemma auxPoly_coeff {ℓ D : ℕ} (z : Fin ℓ × Fin D → Ambient F) (j : Fin ℓ) (k : ℕ) :
    (auxPoly F z j).coeff k = if h : k < D then z (j, ⟨k, h⟩) else 0 :=
  Commons.Algebra.Polynomial.coeff_sum_monomial (fun e => z (j, e)) k

lemma auxPoly_mem {ℓ D ν : ℕ} (z : Fin ℓ × Fin D → Ambient F) (j : Fin ℓ)
    (hz : ∀ q, z q ∈ ambA F ν) : ∀ k, (auxPoly F z j).coeff k ∈ ambA F ν := by
  intro k
  rw [auxPoly_coeff F]
  split_ifs with h
  · exact hz _
  · exact (ambASub F ν).zero_mem

lemma auxPoly_natDegree_lt {ℓ D : ℕ} (hD : 0 < D) (z : Fin ℓ × Fin D → Ambient F)
    (j : Fin ℓ) : (auxPoly F z j).natDegree < D := by
  refine lt_of_le_of_lt (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
    (Nat.sub_one_lt (ne_of_gt hD))
  rw [auxPoly_coeff F]
  exact dif_neg (by omega)

lemma auxPoly_ne_zero {ℓ D : ℕ} (z : Fin ℓ × Fin D → Ambient F) (hz : z ≠ 0) :
    ∃ j, auxPoly F z j ≠ 0 := by
  by_contra h
  push Not at h
  refine hz (funext fun q => ?_)
  obtain ⟨j, e⟩ := q
  exact (Commons.Algebra.Polynomial.sum_monomial_eq_zero_iff (fun e => z (j, e))).mp
    (h j) e

/-- The evaluation of the associated polynomial. -/
lemma auxPoly_eval {ℓ D : ℕ} (z : Fin ℓ × Fin D → Ambient F) (j : Fin ℓ) (c : Ambient F) :
    (auxPoly F z j).eval c = ∑ e : Fin D, z (j, e) * c ^ (e : ℕ) := by
  have h : auxPoly F z j = ∑ e : Fin D, Polynomial.monomial (e : ℕ) (z (j, e)) := rfl
  rw [h, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun e _ => by rw [Polynomial.eval_monomial]

/-- **The raised auxiliary condition.**  A solution of the auxiliary system, read as a polynomial
row vector, satisfies the raised auxiliary condition at every level
`M = N + p.1 ∈ {N, …, 2N-1}`. -/
theorem auxPoly_haux {ℓ : ℕ} (ν : ℕ) (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    {N D : ℕ} {z : Fin ℓ × Fin D → Ambient F}
    (hzmul : (auxMat F ν Θ ϑ N D).mulVec z = 0) (p : Fin N) :
    Matrix.vecMul (fun j => (finalP (q := Nat.card F) Θ (auxPoly F z) (N + p.1) j).eval
      (ambTheta F)) ϑ = 0 := by
  classical
  set M : ℕ := N + p.1 with hMdef
  haveI : FrobPow (Ambient F) (Nat.card F ^ M) := (frobPow_ambient F).pow M
  have hqM : Nat.card F ^ M ≠ 0 := pow_ne_zero _ (FrobPow.ne_zero (Ambient F) (q := Nat.card F))
  have hpoly : ∀ j, (finalP (q := Nat.card F) Θ (auxPoly F z) M j).eval (ambTheta F)
      = ∑ i : Fin ℓ, (polyTwist (q := Nat.card F) M (auxPoly F z i)).eval (ambTheta F)
          * keyEval F Θ M i j := by
    intro j
    rw [finalP, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.eval_mul, keyEval, evalMatHom_apply]
  have hfinal : ∀ j, (finalP (q := Nat.card F) Θ (auxPoly F z) M j).eval (ambTheta F)
      = ∑ i : Fin ℓ, (∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M) * (ambTheta F) ^ (e : ℕ))
          * keyEval F Θ M i j := by
    intro j
    rw [hpoly j]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [eval_polyTwist, auxPoly_eval F, FrobPow.sum_pow_finset]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [mul_pow, ← pow_mul, show (e : ℕ) * Nat.card F ^ M = Nat.card F ^ M * (e : ℕ) by ring,
      pow_mul, ← ambThetaNu_pow]
  funext c
  -- the raised system
  have hsys : ∑ q : Fin ℓ × Fin D,
      (z q) ^ (Nat.card F ^ M) * (auxEntry F ν Θ ϑ M (q.2 : ℕ) q.1 c) ^ (Nat.card F ^ M) = 0 := by
    have h0 : ∑ q : Fin ℓ × Fin D, (auxMat F ν Θ ϑ N D) (p, c) q * z q = 0 := by
      have h := congrFun hzmul (p, c)
      rwa [Matrix.mulVec_apply_eq_sum] at h
    have h1 := congrArg (fun x : Ambient F => x ^ (Nat.card F ^ M)) h0
    rw [FrobPow.sum_pow_finset, zero_pow hqM] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hA : (auxMat F ν Θ ϑ N D) (p, c) q = auxEntry F ν Θ ϑ M (q.2 : ℕ) q.1 c := rfl
    rw [mul_pow, hA, auxEntry_pow F hΘ hϑ]
    exact mul_comm _ _
  -- rearrange
  have hL : ∑ j : Fin ℓ, (∑ i : Fin ℓ, (∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M)
        * (ambTheta F) ^ (e : ℕ)) * keyEval F Θ M i j) * ϑ j c
      = ∑ i : Fin ℓ, ∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M)
        * ((ambTheta F) ^ (e : ℕ) * (keyEval F Θ M * ϑ) i c) := by
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_mul Finset.univ
      (fun i => (∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M) * (ambTheta F) ^ (e : ℕ))
        * keyEval F Θ M i j) (ϑ j c))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ j : Fin ℓ, ((∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M)
            * (ambTheta F) ^ (e : ℕ)) * keyEval F Θ M i j) * ϑ j c
        = ∑ j : Fin ℓ, ∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M)
            * (ambTheta F) ^ (e : ℕ) * (keyEval F Θ M i j * ϑ j c) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_assoc]
          exact Finset.sum_mul Finset.univ _ _
      _ = ∑ e : Fin D, ∑ j : Fin ℓ, (z (i, e)) ^ (Nat.card F ^ M)
            * (ambTheta F) ^ (e : ℕ) * (keyEval F Θ M i j * ϑ j c) := Finset.sum_comm
      _ = ∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M) * (ambTheta F) ^ (e : ℕ)
            * ((keyEval F Θ M) * ϑ) i c := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [← Finset.mul_sum, Matrix.mul_apply]
      _ = ∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M)
            * ((ambTheta F) ^ (e : ℕ) * ((keyEval F Θ M) * ϑ) i c) := by
          refine Finset.sum_congr rfl fun e _ => by ring
  have hR : (∑ q : Fin ℓ × Fin D,
      (z q) ^ (Nat.card F ^ M) * (auxEntry F ν Θ ϑ M (q.2 : ℕ) q.1 c) ^ (Nat.card F ^ M))
      = ∑ i : Fin ℓ, ∑ e : Fin D, (z (i, e)) ^ (Nat.card F ^ M)
        * ((ambTheta F) ^ (e : ℕ) * (keyEval F Θ M * ϑ) i c) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [auxEntry_pow F hΘ hϑ, auxK]
    try ring
  rw [Matrix.vecMul_apply]
  simp only [dotProduct, Matrix.col_apply, Pi.zero_apply]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hfinal j])]
  rw [← hsys]
  exact hL.trans hR.symm
/-! ## §8. The auxiliary function (final form) -/

/-- The points `θ_M` are distinct. -/
lemma ambThetaNu_injective : Function.Injective (fun M : ℕ => ambThetaNu F M) := by
  intro M M' h
  have h' : ambThetaNu F M = ambThetaNu F M' := h
  have hv : ambKappa F M = ambKappa F M' := by
    rw [← v_ambThetaNu F M, ← v_ambThetaNu F M', h']
  rw [ambKappa, ambKappa, WithZero.exp_inj] at hv
  have hk : ((Nat.card F : ℚ) - 1) ≠ 0 := by
    have h2 : (2 : ℚ) ≤ Nat.card F := by
      have := two_le_card_field F; exact_mod_cast this
    linarith
  have hq : (Nat.card F : ℚ) ^ M = (Nat.card F : ℚ) ^ M' := by
    field_simp at hv
    have hinv := congrArg Inv.inv hv
    simpa using hinv
  have hq' : Nat.card F ^ M = Nat.card F ^ M' := by
    have := hq
    push_cast at this
    exact_mod_cast this
  exact Nat.pow_right_injective (by have := two_le_card_field F; omega) hq'

/-- A nonzero polynomial of degree `< D` cannot vanish at the `N > D` points
`θ_N, θ_{N+1}, …, θ_{2N-1}`. -/
lemma auxPoly_eval_eq_zero {D N : ℕ} (hDN : D < N) {p : Polynomial (Ambient F)}
    (hp : p.natDegree < D) (h : ∀ m : Fin N, p.eval (ambThetaNu F (N + m.1)) = 0) : p = 0 := by
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun m : Fin N => ambThetaNu F (N + ↑m)) ?_ h ?_
  · intro a b hab
    have h : N + (a : ℕ) = N + (b : ℕ) := ambThetaNu_injective F hab
    omega
  · simpa using lt_trans hp hDN

/-- Some component of the associated polynomial does not vanish at one of the points. -/
lemma exists_auxPoly_eval_ne_zero {ℓ D N : ℕ} (hD : 0 < D) (hDN : D < N)
    {z : Fin ℓ × Fin D → Ambient F} (hz : z ≠ 0) :
    ∃ p : Fin N, ∃ j : Fin ℓ, (auxPoly F z j).eval (ambThetaNu F (N + p.1)) ≠ 0 := by
  obtain ⟨j, hj⟩ := auxPoly_ne_zero F z hz
  by_contra h
  push Not at h
  exact hj (auxPoly_eval_eq_zero F hDN (auxPoly_natDegree_lt F hD z j) (fun m => h m j))

/-- `N - N/(2ℓ) < N`. -/
lemma auxDeg_lt {ℓ N : ℕ} (hℓ : 1 ≤ ℓ) (hN : 2 * ℓ ≤ N) : auxDeg N ℓ < N := by
  have hpos : 0 < N / (2 * ℓ) := by
    rw [Nat.div_pos_iff]
    exact ⟨by omega, hN⟩
  have hNpos : 0 < N := by omega
  rw [auxDeg]
  exact Nat.sub_lt hNpos hpos

/-- **The auxiliary function of the ABP criterion exists.**  There are `ν ≥ 2N` and a nonzero
polynomial row vector `h ∈ A_ν[t]^{1×ℓ}` of `t`-degree `< N - N/(2ℓ)` and of size `O(1)`
(bounded by `exp (2ℓC)`, `C` independent of `N`), satisfying the raised auxiliary condition at
every level `M = N, …, 2N-1`, and not vanishing identically at one of the points
`θ_N, …, θ_{2N-1}`. -/
theorem aux_function_exists {ℓ : ℕ} (ν : ℕ) (hℓ : 2 ≤ ℓ)
    (Θ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (hΘ : ∀ i j m, (Θ i j).coeff m ∈ ambA F ν)
    (ϑ : Matrix (Fin ℓ) (Fin (ℓ - 1)) (Ambient F)) (hϑ : ∀ i j, ϑ i j ∈ ambA F ν)
    {N : ℕ} (hN : 4 * ℓ ≤ N) :
    ∃ (ν' : ℕ) (h : Fin ℓ → Polynomial (Ambient F)),
      ν + 2 * N ≤ ν' ∧ (∃ j, h j ≠ 0) ∧
      (∀ j k, (h j).coeff k ∈ ambA F ν') ∧
      (∀ j, (h j).natDegree < auxDeg N ℓ) ∧
      (∀ j k, Valued.v ((h j).coeff k) ≤ WithZero.exp (2 * ℓ * auxC F ν Θ hΘ ϑ hϑ)) ∧
      (∀ p : Fin N,
        Matrix.vecMul (fun j => (finalP (q := Nat.card F) Θ h (N + p.1) j).eval (ambTheta F))
          ϑ = 0) ∧
      (∃ p : Fin N, ∃ j : Fin ℓ, (h j).eval (ambThetaNu F (N + p.1)) ≠ 0) := by
  obtain ⟨ν', z, hν', hzmem, hzsize, hz0, hzmul⟩ := aux_solution_exists F ν hℓ Θ hΘ ϑ hϑ hN
  have hℓ1 : 1 ≤ ℓ := by omega
  have hDpos : 0 < auxDeg N ℓ := one_le_auxDeg hℓ1 (by omega)
  have hDN : auxDeg N ℓ < N := auxDeg_lt hℓ1 (by omega)
  refine ⟨ν', auxPoly F z, hν', auxPoly_ne_zero F z hz0, fun j k => auxPoly_mem F z j hzmem k,
    fun j => auxPoly_natDegree_lt F hDpos z j, fun j k => ?_, fun p => ?_,
    exists_auxPoly_eval_ne_zero F hDpos hDN hz0⟩
  · rw [auxPoly_coeff F]
    split_ifs with h
    · exact hzsize _
    · rw [map_zero]
      exact le_of_lt (WithZero.exp_pos)
  · exact auxPoly_haux F ν Θ hΘ ϑ hϑ hzmul p

end

end ZagierHoffmanPositiveChar
