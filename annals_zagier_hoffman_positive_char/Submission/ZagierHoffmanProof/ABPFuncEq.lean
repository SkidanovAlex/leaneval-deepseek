import Submission.ZagierHoffmanProof.ABPAux

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial Matrix
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §1. The product `Φ^{(j+1)} ⋯ Φ^{(ℓ)}` and the iterated functional equation -/

/-- `Φ^{(j+1)} Φ^{(j+2)} ⋯ Φ^{(ℓ)}`, as a matrix of polynomials. -/
noncomputable def phiProd (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) :
    ℕ → Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))
  | j => if _h : j < ℓ then
      (polyTwistHom (q := Nat.card F) (j + 1)).mapMatrix Φ * phiProd Φ (j + 1)
    else 1
termination_by j => ℓ - j
decreasing_by omega

lemma phiProd_of_not_lt (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) {j : ℕ}
    (hj : ¬ j < ℓ) : phiProd F Φ j = 1 := by
  rw [phiProd]
  simp only [hj, ↓reduceDIte]

lemma phiProd_succ (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) {j : ℕ} (hj : j < ℓ) :
    phiProd F Φ j
      = (polyTwistHom (q := Nat.card F) (j + 1)).mapMatrix Φ * phiProd F Φ (j + 1) := by
  rw [phiProd]
  simp only [hj, ↓reduceDIte]

/-- The coercion of `phiProd` satisfies the same recursion. -/
lemma phiProd_coe_succ (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) {j : ℕ}
    (hj : j < ℓ) :
    (coeHom (K := Ambient F)).mapMatrix (phiProd F Φ j)
      = frobTwistMat (q := Nat.card F) (j + 1) ((coeHom (K := Ambient F)).mapMatrix Φ)
        * (coeHom (K := Ambient F)).mapMatrix (phiProd F Φ (j + 1)) := by
  rw [phiProd_succ F Φ hj, map_mul]
  congr 1
  exact coe_mapMatrix_polyTwist (K := Ambient F) (q := Nat.card F) (j + 1) Φ

/-- **The iterated functional equation**: `ψ^{(j)} = Φ^{(j+1)} ⋯ Φ^{(ℓ)} ψ^{(ℓ)}`. -/
lemma frobTwistVec_iter {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {ψ : Fin ℓ → PowerSeries (Ambient F)}
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ)) :
    ∀ n {j : ℕ}, ℓ = j + n → frobTwistVec (q := Nat.card F) j ψ
      = ((coeHom (K := Ambient F)).mapMatrix (phiProd F Φ j)).mulVec
          (frobTwistVec (q := Nat.card F) ℓ ψ) := by
  intro n
  induction n with
  | zero =>
      intro j hj
      rw [phiProd_of_not_lt F Φ (by omega : ¬ j < ℓ), map_one, Matrix.one_mulVec,
        show j = ℓ by omega]
  | succ n ih =>
      intro j hj
      rw [frobTwistVec_functional hfe j, ih (by omega : ℓ = (j + 1) + n),
        Matrix.mulVec_mulVec, ← phiProd_coe_succ F Φ (by omega : j < ℓ)]

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §2. Membership and size of the entries of the system -/

/-- The coefficients of a twisted polynomial with `A_ν`-coefficients stay in `A_ν`. -/
lemma polyTwist_coeff_mem {ν : ℕ} {p : Polynomial (Ambient F)}
    (hp : ∀ m, p.coeff m ∈ ambA F ν) (k : ℕ) :
    ∀ m, (polyTwist (q := Nat.card F) k p).coeff m ∈ ambA F ν := by
  intro m
  rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply]
  exact ambA_pow_card_pow_mem F (hp m) k

/-- The coefficients of `Φ^{(j+1)} ⋯ Φ^{(ℓ)}` lie in `A_ν` when `Φ` has `A_ν`-coefficients. -/
lemma phiProd_coeff_mem {ν : ℕ}
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambA F ν) :
    ∀ j (i c : Fin ℓ) (m : ℕ), (phiProd F Φ j i c).coeff m ∈ ambA F ν := by
  have key : ∀ n, ∀ j, ℓ - j = n → ∀ (i c : Fin ℓ) (m : ℕ),
      (phiProd F Φ j i c).coeff m ∈ ambA F ν := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hjn i c m
      by_cases hj : j < ℓ
      · rw [phiProd_succ F Φ hj, Matrix.mul_apply, Polynomial.finsetSum_coeff]
        refine ambA_sum_mem F (fun k _ => ?_)
        rw [Polynomial.coeff_mul]
        refine ambA_sum_mem F (fun x _ => ?_)
        refine ambA_mul_mem F
          (polyTwist_coeff_mem F (fun m => hΦ i k m) (j + 1) x.1) ?_
        exact ih (ℓ - (j + 1)) (by omega) (j + 1) rfl k c x.2
      · rw [phiProd_of_not_lt F Φ hj, Matrix.one_apply]
        split_ifs with h
        · rw [Polynomial.coeff_one]
          split_ifs with h2
          · exact ambA_one_mem F ν
          · exact (ambASub F ν).zero_mem
        · rw [Polynomial.coeff_zero]
          exact (ambASub F ν).zero_mem
  intro j i c m
  exact key (ℓ - j) j rfl i c m

/-- The coefficients of `phiProd` are bounded, uniformly in `j ≤ ℓ`. -/
noncomputable def phiProdBound (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) : ℚ :=
  (Finset.univ : Finset (Fin (ℓ + 1))).sup' (Finset.univ_nonempty)
    (fun j => valBound F (fun p : Fin ℓ × Fin ℓ => phiProd F Φ (j : ℕ) p.1 p.2))

lemma phiProdBound_pos (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) :
    0 < phiProdBound F Φ := by
  rw [phiProdBound]
  refine lt_of_lt_of_le
    (valBound_pos F (fun p : Fin ℓ × Fin ℓ => phiProd F Φ 0 p.1 p.2)) ?_
  exact Finset.le_sup'
    (fun j : Fin (ℓ + 1) => valBound F (fun p : Fin ℓ × Fin ℓ => phiProd F Φ (j : ℕ) p.1 p.2))
    (Finset.mem_univ 0)

lemma phiProd_coeff_bound (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) {j : ℕ}
    (hj : j ≤ ℓ) (i c : Fin ℓ) (m : ℕ) :
    Valued.v ((phiProd F Φ j i c).coeff m) ≤ WithZero.exp (phiProdBound F Φ) := by
  have h1 := val_coeff_le_valBound F (fun p : Fin ℓ × Fin ℓ => phiProd F Φ j p.1 p.2) (i, c) m
  have h2 : valBound F (fun p : Fin ℓ × Fin ℓ => phiProd F Φ j p.1 p.2) ≤ phiProdBound F Φ := by
    rw [phiProdBound]
    exact Finset.le_sup'
      (fun j' : Fin (ℓ + 1) => valBound F (fun p : Fin ℓ × Fin ℓ => phiProd F Φ (j' : ℕ) p.1 p.2))
      (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (ℓ + 1)))
  exact le_trans h1 (WithZero.exp_le_exp.mpr h2)

/-- The size bound for a twisted polynomial. -/
lemma polyTwist_coeff_bound {c : ℚ} {p : Polynomial (Ambient F)}
    (hp : ∀ m, Valued.v (p.coeff m) ≤ WithZero.exp c) (k : ℕ) (m : ℕ) :
    Valued.v ((polyTwist (q := Nat.card F) k p).coeff m) ≤ WithZero.exp (c * (Nat.card F : ℚ) ^ k) := by
  rw [polyTwist, polyTwistHom_apply, Polynomial.coeff_map, frobPowHom_apply, map_pow]
  calc (Valued.v (p.coeff m)) ^ (Nat.card F ^ k) ≤ (WithZero.exp c) ^ (Nat.card F ^ k) :=
        pow_le_pow_left₀ zero_le (hp m) _
    _ = WithZero.exp (c * (Nat.card F : ℚ) ^ k) := by
        rw [expmul_rat, Nat.cast_pow]

/-- The size bound for a product (coefficientwise). -/
lemma coeff_mul_bound {cA cB : ℚ} {A B : Polynomial (Ambient F)}
    (hA : ∀ m, Valued.v (A.coeff m) ≤ WithZero.exp cA)
    (hB : ∀ m, Valued.v (B.coeff m) ≤ WithZero.exp cB) (m : ℕ) :
    Valued.v ((A * B).coeff m) ≤ WithZero.exp (cA + cB) := by
  rw [Polynomial.coeff_mul]
  refine Valuation.map_sum_le _ (fun x _ => ?_)
  rw [map_mul]
  calc Valued.v (A.coeff x.1) * Valued.v (B.coeff x.2)
      ≤ WithZero.exp cA * WithZero.exp cB := mul_le_mul' (hA x.1) (hB x.2)
    _ = WithZero.exp (cA + cB) := (WithZero.exp_add _ _).symm

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §3. The matrix of the system -/

/-- The matrix of the system whose kernel gives the functional equation of `E = ∑ᵢ hᵢ ψᵢ`:
its `(c,j)` entry is the `c`-th component of `h^{(j)} Φ^{(j+1)} ⋯ Φ^{(ℓ)}`. -/
noncomputable def funcEqMat (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (h : Fin ℓ → Polynomial (Ambient F)) : Matrix (Fin ℓ) (Fin (ℓ + 1)) (Polynomial (Ambient F)) :=
  fun c j => ∑ i, polyTwist (q := Nat.card F) (j : ℕ) (h i) * phiProd F Φ (j : ℕ) i c

/-- The size constant of the functional-equation system. -/
noncomputable def funcEqC (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) (c : ℚ) : ℚ :=
  2 * (ℓ : ℚ) * c * (Nat.card F : ℚ) ^ ℓ + phiProdBound F Φ

lemma funcEqMat_coeff_mem {ν : ℕ}
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambA F ν)
    {h : Fin ℓ → Polynomial (Ambient F)} (hh : ∀ j k, (h j).coeff k ∈ ambA F ν)
    (c : Fin ℓ) (j : Fin (ℓ + 1)) (m : ℕ) :
    (funcEqMat F Φ h c j).coeff m ∈ ambA F ν := by
  rw [funcEqMat, Polynomial.finsetSum_coeff]
  refine ambA_sum_mem F (fun i _ => ?_)
  rw [Polynomial.coeff_mul]
  refine ambA_sum_mem F (fun x _ => ?_)
  refine ambA_mul_mem F (polyTwist_coeff_mem F (hh i) (j : ℕ) x.1) ?_
  exact phiProd_coeff_mem F hΦ (j : ℕ) i c x.2

lemma funcEqMat_coeff_bound {c : ℚ} (hc : 0 < c) (hℓ1 : 1 ≤ ℓ)
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {h : Fin ℓ → Polynomial (Ambient F)}
    (hh : ∀ j k, Valued.v ((h j).coeff k) ≤ WithZero.exp c)
    (c' : Fin ℓ) (j : Fin (ℓ + 1)) (m : ℕ) :
    Valued.v ((funcEqMat F Φ h c' j).coeff m)
      ≤ WithZero.exp (funcEqC F Φ c) := by
  have hq1 : (1 : ℚ) ≤ Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 1 ≤ Nat.card F)
  have hpow : (Nat.card F : ℚ) ^ (j : ℕ) ≤ (Nat.card F : ℚ) ^ ℓ :=
    pow_le_pow_right₀ hq1 (Nat.lt_succ_iff.mp j.isLt)
  have htw : ∀ (i : Fin ℓ) (m : ℕ),
      Valued.v ((polyTwist (q := Nat.card F) (j : ℕ) (h i)).coeff m)
        ≤ WithZero.exp (c * (Nat.card F : ℚ) ^ ℓ) := fun i m =>
    le_trans (polyTwist_coeff_bound F (fun m => hh i m) (j : ℕ) m)
      (WithZero.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow hc.le))
  rw [funcEqMat, Polynomial.finsetSum_coeff]
  have hph := phiProd_coeff_bound F Φ (Nat.lt_succ_iff.mp j.isLt)
  refine Valuation.map_sum_le _ (fun i _ => ?_)
  refine le_trans (coeff_mul_bound F (cA := c * (Nat.card F : ℚ) ^ ℓ)
    (cB := phiProdBound F Φ) (htw i) (hph i c') m) ?_
  rw [funcEqC]
  refine WithZero.exp_le_exp.mpr ?_
  have h2 : c * (Nat.card F : ℚ) ^ ℓ ≤ 2 * (ℓ : ℚ) * c * (Nat.card F : ℚ) ^ ℓ := by
    have hle1 : (1 : ℚ) ≤ 2 * (ℓ : ℚ) := by
      have : (1 : ℚ) ≤ (ℓ : ℚ) := by exact_mod_cast hℓ1
      linarith
    calc c * (Nat.card F : ℚ) ^ ℓ = 1 * (c * (Nat.card F : ℚ) ^ ℓ) := (one_mul _).symm
      _ ≤ (2 * (ℓ : ℚ)) * (c * (Nat.card F : ℚ) ^ ℓ) :=
          mul_le_mul_of_nonneg_right hle1
            (mul_nonneg hc.le (pow_nonneg (Nat.cast_nonneg (Nat.card F)) ℓ))
      _ = 2 * (ℓ : ℚ) * c * (Nat.card F : ℚ) ^ ℓ := by ring
  linarith

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §4. Siegel's lemma for the functional-equation system -/

/-- The degree bound of the entries of the functional-equation system. -/
noncomputable def funcEqDeg (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F)))
    (h : Fin ℓ → Polynomial (Ambient F)) : ℕ :=
  degSup F (fun p : Fin ℓ × Fin (ℓ + 1) => funcEqMat F Φ h p.1 p.2)

/-- The level-`ν` size exponent of the entries of the functional-equation system. -/
noncomputable def funcEqMu (Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))) (c : ℚ)
    (ν : ℕ) : ℕ :=
  Nat.ceil ((Nat.card F : ℚ) ^ ν * funcEqC F Φ c / ((Nat.card F : ℚ) - 1))

/-- ★★ **Siegel's lemma for the functional-equation system.**  There is a nonzero
`b ∈ A_ν[t]^{ℓ+1}`, of coefficient size `≤ κ_ν ^ (2ℓ·μ)` and `t`-degree `≤ (2ℓ+1)·d`, with
`funcEqMat · b = 0`. -/
theorem func_eq_solution {ν : ℕ} (hℓ1 : 1 ≤ ℓ)
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambA F ν)
    {h : Fin ℓ → Polynomial (Ambient F)} (hh : ∀ j k, (h j).coeff k ∈ ambA F ν)
    {c : ℚ} (hc : 0 < c) (hhsz : ∀ j k, Valued.v ((h j).coeff k) ≤ WithZero.exp c) :
    ∃ b : Fin (ℓ + 1) → Polynomial (Ambient F), b ≠ 0 ∧
      (funcEqMat F Φ h).mulVec b = 0 ∧
      (∀ j k, (b j).coeff k ∈ ambA F ν ∧
        Valued.v ((b j).coeff k) ≤ (ambKappa F ν) ^ (2 * ℓ * funcEqMu F Φ c ν)) ∧
      (∀ j, (b j).natDegree ≤ (2 * ℓ + 1) * funcEqDeg F Φ h) := by
  have hq : (0 : ℚ) < Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 0 < Nat.card F)
  have hq1 : (1 : ℚ) < Nat.card F := by
    have := two_le_card_field F; exact_mod_cast (by omega : 1 < Nat.card F)
  set d : ℕ := funcEqDeg F Φ h with hd
  set μ : ℕ := funcEqMu F Φ c ν with hμ
  have hμge : (Nat.card F : ℚ) ^ ν * funcEqC F Φ c / ((Nat.card F : ℚ) - 1) ≤ (μ : ℚ) := by
    rw [hμ]; exact Nat.le_ceil _
  -- the inequality
  have hm : ((2 * ℓ * μ) + μ + 1) * (ℓ * (d + ((2 * ℓ + 1) * d) + 1))
      < ((2 * ℓ * μ) + 1) * ((ℓ + 1) * (((2 * ℓ + 1) * d) + 1)) := by
    have hdiff : ((2 * ℓ * μ) + 1) * ((ℓ + 1) * (((2 * ℓ + 1) * d) + 1))
        = ((2 * ℓ * μ) + μ + 1) * (ℓ * (d + ((2 * ℓ + 1) * d) + 1))
          + (d * (ℓ + 1) + ℓ * μ + 1) := by
      ring
    rw [hdiff]
    exact Nat.lt_add_of_pos_right (Nat.succ_pos _)
  have hm' : ((2 * ℓ * μ) + μ + 1) * (Fintype.card (Fin ℓ)
        * (d + (2 * ℓ + 1) * d + 1))
      < ((2 * ℓ * μ) + 1) * (Fintype.card (Fin (ℓ + 1)) * ((2 * ℓ + 1) * d + 1)) := by
    rw [Fintype.card_fin, Fintype.card_fin]
    exact hm
  obtain ⟨b, hb0, hbmul, hbmem, hbdeg⟩ :=
    siegel_two (F := F) (R := Fin ℓ) (S := Fin (ℓ + 1)) (ν := ν)
      (d := d) (e := (2 * ℓ + 1) * d) (μ := μ) (m := 2 * ℓ * μ)
      (by simp) hm' (funcEqMat F Φ h)
      (fun i j k => ⟨funcEqMat_coeff_mem F hΦ hh i j k, by
        have h := funcEqMat_coeff_bound F (Φ := Φ) hc hℓ1 hhsz i j k
        have hκ : WithZero.exp (funcEqC F Φ c) ≤ ambKappa F ν ^ μ := by
          have h3 : ambKappa F ν ^ μ
              = WithZero.exp ((((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν)
                  * ((μ : ℕ) : ℚ)) := by
            rw [ambKappa]
            exact expmul_rat _ _
          rw [h3]
          refine WithZero.exp_le_exp.mpr ?_
          have hqm1 : ((Nat.card F : ℚ) - 1) ≠ 0 := by linarith
          have hqν : (Nat.card F : ℚ) ^ ν ≠ 0 := pow_ne_zero _ (ne_of_gt hq)
          have h2 : funcEqC F Φ c
              = (((Nat.card F : ℚ) - 1) / (Nat.card F : ℚ) ^ ν)
                  * ((Nat.card F : ℚ) ^ ν * funcEqC F Φ c / ((Nat.card F : ℚ) - 1)) := by
            field_simp
            try ring
          rw [h2]
          exact mul_le_mul_of_nonneg_left hμge (by positivity)
        exact le_trans h hκ⟩)
      (fun i j => natDegree_le_degSup F
        (fun p : Fin ℓ × Fin (ℓ + 1) => funcEqMat F Φ h p.1 p.2) (i, j))
  exact ⟨b, hb0, hbmul, fun j k => ⟨(hbmem j k).1, (hbmem j k).2⟩, fun j => hbdeg j⟩

end

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

noncomputable section

variable (F : Type*) [Field F] [Finite F]
variable {ℓ : ℕ}

/-! ## §5. The functional equation for `E = ∑ᵢ hᵢ ψᵢ` -/

/-- `frobTwist` of the auxiliary function. -/
lemma frobTwist_auxFun {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    {ψ : Fin ℓ → PowerSeries (Ambient F)}
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    {h : Fin ℓ → Polynomial (Ambient F)} (j : Fin (ℓ + 1)) :
    frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ) (∑ i, (h i : PowerSeries (Ambient F)) * ψ i)
      = ∑ c : Fin ℓ, ((funcEqMat F Φ h c j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
          * frobTwistVec (q := Nat.card F) ℓ ψ c := by
  have hjle : (j : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp j.isLt
  rw [frobTwist_sum]
  -- the `i`-th summand
  have hterm : ∀ i : Fin ℓ, frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ)
        ((h i : PowerSeries (Ambient F)) * ψ i)
      = ∑ c : Fin ℓ, ((coeHom (K := Ambient F) (polyTwist (q := Nat.card F) (j : ℕ) (h i)))
            : PowerSeries (Ambient F))
          * ((coeHom (K := Ambient F) (phiProd F Φ (j : ℕ) i c)) : PowerSeries (Ambient F))
          * frobTwistVec (q := Nat.card F) ℓ ψ c := by
    intro i
    rw [frobTwist_mul,
      show frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ) (h i : PowerSeries (Ambient F))
        = (coeHom (K := Ambient F) (polyTwist (q := Nat.card F) (j : ℕ) (h i))
            : PowerSeries (Ambient F)) from (coe_polyTwist (K := Ambient F) (q := Nat.card F) _ _).symm,
      ← frobTwistVec_apply (q := Nat.card F) (j : ℕ) ψ i]
    rw [frobTwistVec_iter F hfe (ℓ - (j : ℕ)) (by omega : ℓ = (j : ℕ) + (ℓ - (j : ℕ)))]
    simp only [Matrix.mulVec_apply_eq_sum, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- rearrange
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  rw [show (((funcEqMat F Φ h c j : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
      = (coeHom (K := Ambient F)) (funcEqMat F Φ h c j) from rfl, funcEqMat, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  try rfl

/-- ★★★ **The functional equation for the auxiliary function.** -/
theorem func_eq_exists {ν : ℕ} (hℓ1 : 1 ≤ ℓ)
    {Φ : Matrix (Fin ℓ) (Fin ℓ) (Polynomial (Ambient F))}
    (hΦ : ∀ i j m, (Φ i j).coeff m ∈ ambA F ν)
    {ψ : Fin ℓ → PowerSeries (Ambient F)}
    (hfe : ψ = (frobTwistMat (q := Nat.card F) 1 ((coeHom (K := Ambient F)).mapMatrix Φ)).mulVec
      (frobTwistVec (q := Nat.card F) 1 ψ))
    {h : Fin ℓ → Polynomial (Ambient F)} (hh : ∀ j k, (h j).coeff k ∈ ambA F ν)
    {c : ℚ} (hc : 0 < c) (hhsz : ∀ j k, Valued.v ((h j).coeff k) ≤ WithZero.exp c) :
    ∃ b : Fin (ℓ + 1) → Polynomial (Ambient F), b ≠ 0 ∧
      (∀ j k, (b j).coeff k ∈ ambA F ν ∧
        Valued.v ((b j).coeff k) ≤ (ambKappa F ν) ^ (2 * ℓ * funcEqMu F Φ c ν)) ∧
      (∑ j, ((b j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
          * frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ)
              (∑ i, (h i : PowerSeries (Ambient F)) * ψ i) = 0) := by
  obtain ⟨b, hb0, hbmul, hbmem, _⟩ := func_eq_solution F hℓ1 hΦ hh hc hhsz
  refine ⟨b, hb0, hbmem, ?_⟩
  have hkey : ∀ j : Fin (ℓ + 1),
      frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ) (∑ i, (h i : PowerSeries (Ambient F)) * ψ i)
        = ∑ c : Fin ℓ, ((funcEqMat F Φ h c j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
            * frobTwistVec (q := Nat.card F) ℓ ψ c := fun j => frobTwist_auxFun F hfe j
  calc ∑ j, ((b j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
        * frobTwist (R := Ambient F) (p := Nat.card F) (j : ℕ) (∑ i, (h i : PowerSeries (Ambient F)) * ψ i)
      = ∑ j, ∑ c, (((b j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
            * ((funcEqMat F Φ h c j : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
            * frobTwistVec (q := Nat.card F) ℓ ψ c := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hkey j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ c, (∑ j, ((funcEqMat F Φ h c j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
            * ((b j : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
            * frobTwistVec (q := Nat.card F) ℓ ψ c := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        have h0 : ∑ j, (funcEqMat F Φ h c j) * b j = 0 := by
          have h := congrFun hbmul c
          rwa [Matrix.mulVec_apply_eq_sum] at h
        have h2 : ∀ j : Fin (ℓ + 1),
            (((funcEqMat F Φ h c j : Polynomial (Ambient F)) : PowerSeries (Ambient F))
              * ((b j : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
            = (((funcEqMat F Φ h c j) * b j : Polynomial (Ambient F))
                : PowerSeries (Ambient F)) := by
          intro j
          rw [show (((funcEqMat F Φ h c j * b j : Polynomial (Ambient F))
                : PowerSeries (Ambient F)))
              = (coeHom (K := Ambient F)) (funcEqMat F Φ h c j * b j) from rfl, map_mul]
          rfl
        have hsum : (∑ j : Fin (ℓ + 1), (((funcEqMat F Φ h c j) * b j : Polynomial (Ambient F))
              : PowerSeries (Ambient F))) = 0 := by
          show (∑ j : Fin (ℓ + 1), (coeHom (K := Ambient F))
            ((funcEqMat F Φ h c j) * b j)) = 0
          rw [← map_sum (coeHom (K := Ambient F))
            (fun j : Fin (ℓ + 1) => (funcEqMat F Φ h c j) * b j) Finset.univ, h0, map_zero]
        rw [Finset.sum_congr rfl fun j _ => h2 j, hsum, zero_mul]

end

end ZagierHoffmanPositiveChar
