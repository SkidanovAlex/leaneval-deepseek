/-
# Assembling the polynomial growth bound for the entries of `σ_R`

Combining the continued fraction expansion of `Expansion.lean` with the explicit power bound
for the matrices `σ(T)`, `σ(T)⁻¹` (`sigmaT_pow_bound`) and the submultiplicativity of the
squared Frobenius norm (`frob2C_mul`) yields the CKMRV Lemma `lem:polynomiallybounded` for
the representation `σ_R`.
-/
import Mathlib
import Submission.Work.Rigidity.SigmaEntryBound.Defs
import Submission.Work.Rigidity.SigmaEntryBound.Expansion
import Submission.Work.Rigidity.SigmaEntryBound.frob2C_mul
import Submission.Work.Rigidity.SigmaEntryBound.sigmaT_pow_bound

noncomputable section

open Matrix
open scoped MatrixGroups MonoidAlgebra

namespace Work.Rigidity.SigmaEntryBound

/-! ## `T^q` and `S` as explicit elements of `SL(2,ℤ)` -/

/-- The element `T^q` of `SL(2,ℤ)`, defined through the explicit matrix `!![1,q;0,1]`. -/
def gT (q : ℤ) : SL(2,ℤ) := ⟨Tpow q, by simp [Tpow, Matrix.det_fin_two]⟩

/-- The element `S` of `SL(2,ℤ)`, defined through the explicit matrix `!![0,-1;1,0]`. -/
def gS : SL(2,ℤ) := ⟨Smat, by simp [Smat, Matrix.det_fin_two]⟩

theorem coe_gT (q : ℤ) : ((gT q : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = Tpow q := rfl

theorem coe_gS : ((gS : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = Smat := rfl

theorem coe_gT_zero : ((gT 0 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  rw [coe_gT]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tpow]

theorem gT_zero : gT 0 = 1 := Subtype.ext coe_gT_zero

theorem gT_add (a b : ℤ) : gT (a + b) = gT a * gT b := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_gT]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tpow, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem coe_gT_one : ((gT 1 : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) := rfl

theorem gT_eq_T : gT 1 = ModularGroup.T := Subtype.ext coe_gT_one

theorem coe_SL_S : ((ModularGroup.S : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = Smat := rfl

theorem gS_eq_S : gS = ModularGroup.S := Subtype.ext rfl

theorem gT_zpow_nat (n : ℕ) : gT (n : ℤ) = ModularGroup.T ^ (n : ℤ) := by
  have h : gT (n : ℤ) = (gT 1) ^ n := by
    induction n with
    | zero => simpa using gT_zero
    | succ k ih => rw [Nat.cast_succ, gT_add, ih, pow_succ]
  rw [h, gT_eq_T, zpow_natCast]

theorem gT_zpow (q : ℤ) : gT q = ModularGroup.T ^ q := by
  rcases lt_or_ge q 0 with hq | hq
  · have h1 : gT (-q) * gT q = 1 := by
      rw [← gT_add, neg_add_cancel, gT_zero]
    have h2 : gT q = (gT (-q))⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hm : (((-q).toNat : ℕ) : ℤ) = -q := Int.toNat_of_nonneg (by omega)
    have h3 : ModularGroup.T ^ (-q) * ModularGroup.T ^ q = 1 := by
      rw [← _root_.zpow_add, neg_add_cancel, zpow_zero]
    have h4 : (ModularGroup.T ^ (-q))⁻¹ = ModularGroup.T ^ q :=
      (eq_inv_of_mul_eq_one_right h3).symm
    calc gT q = (gT (-q))⁻¹ := h2
      _ = (ModularGroup.T ^ (-q))⁻¹ := by rw [← hm, gT_zpow_nat]
      _ = ModularGroup.T ^ q := h4
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    exact gT_zpow_nat n

/-- `W (T⁻¹) = σ(T)⁻¹`, the explicit inverse matrix. -/
theorem W_Tinv : W (ModularGroup.T⁻¹) = Work.Modular.sigmaTinv := by
  have h1 : W ModularGroup.T * W (ModularGroup.T⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  calc W (ModularGroup.T⁻¹) = 1 * W (ModularGroup.T⁻¹) := (one_mul _).symm
    _ = (Work.Modular.sigmaTinv * Work.Modular.sigmaT) * W (ModularGroup.T⁻¹) := by
          rw [Work.Modular.sigmaTinv_mul_sigmaT, one_mul]
    _ = Work.Modular.sigmaTinv * (Work.Modular.sigmaT * W (ModularGroup.T⁻¹)) := by
          rw [mul_assoc]
    _ = Work.Modular.sigmaTinv * 1 := by rw [← W_T, h1]
    _ = Work.Modular.sigmaTinv := mul_one _

/-- The group level version of `recon`: `gprod l` is the group element whose matrix is
`recon l`. -/
def gprod : List ℤ → SL(2,ℤ)
  | [] => 1
  | [q] => gT q
  | q :: q' :: rest => gT q * gS * gprod (q' :: rest)

/-- `W` of a product of `T^q`'s and `S`'s: the matrix identity `coe_gprod`. -/
theorem coe_gprod (l : List ℤ) :
    ((gprod l : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = recon l := by
  induction l using List.recOn with
  | nil => simp [gprod, recon]
  | cons q t ih =>
    cases t with
    | nil => simp [gprod, recon, coe_gT]
    | cons q' rest =>
      simp only [gprod, recon, Matrix.SpecialLinearGroup.coe_mul, coe_gT, coe_gS, ih]

/-! ## Bounds for the factors -/

theorem frob2C_nonneg (A : Matrix (Fin 6) (Fin 6) ℂ) : 0 ≤ frob2C A := by
  simp only [frob2C]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

theorem frob2C_W_gS : frob2C (W gS) = 6 := by
  rw [gS_eq_S, W_S]
  simp only [frob2C]
  rw [Fin.sum_univ_six]
  simp only [Fin.sum_univ_six]
  simp [Work.Modular.sigmaS]
  norm_num

theorem frob2C_W_gT (K : ℝ)
    (hKT : ∀ m : ℕ, frob2C (Work.Modular.sigmaT ^ m) ≤ K * (1 + (m : ℝ)) ^ 4)
    (hKTi : ∀ m : ℕ, frob2C (Work.Modular.sigmaTinv ^ m) ≤ K * (1 + (m : ℝ)) ^ 4)
    (q : ℤ) :
    frob2C (W (gT q)) ≤ K * (1 + (q.natAbs : ℝ)) ^ 4 := by
  rcases lt_or_ge q 0 with hq | hq
  · have hq' : ModularGroup.T ^ q = (ModularGroup.T⁻¹) ^ ((-q).toNat) := by
      have hm : (((-q).toNat : ℕ) : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      conv_lhs => rw [show q = -(((-q).toNat : ℕ) : ℤ) from by rw [hm]; ring]
      rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    have hc : (((-q).toNat : ℕ) : ℝ) = ((q.natAbs : ℕ) : ℝ) := by
      have h1 : (((-q).toNat : ℕ) : ℤ) = -q := Int.toNat_of_nonneg (by omega)
      have h2 : ((q.natAbs : ℕ) : ℤ) = -q := by
        rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hq)]
      exact_mod_cast (h1.trans h2.symm)
    rw [gT_zpow, hq', map_pow, W_Tinv]
    have h := hKTi (-q).toNat
    rw [hc] at h
    exact h
  · have hq' : ModularGroup.T ^ q = ModularGroup.T ^ q.toNat := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hq]
    have hc : ((q.toNat : ℕ) : ℝ) = ((q.natAbs : ℕ) : ℝ) := by
      have h2 : ((q.natAbs : ℕ) : ℤ) = q := by rw [Int.natAbs_of_nonneg hq]
      exact_mod_cast ((Int.toNat_of_nonneg hq).trans h2.symm)
    rw [gT_zpow, hq', map_pow, W_T]
    have h := hKT q.toNat
    rw [hc] at h
    exact h

theorem frob2C_gprod_le (K : ℝ) (hK1 : 1 ≤ K)
    (hKT : ∀ m : ℕ, frob2C (Work.Modular.sigmaT ^ m) ≤ K * (1 + (m : ℝ)) ^ 4)
    (hKTi : ∀ m : ℕ, frob2C (Work.Modular.sigmaTinv ^ m) ≤ K * (1 + (m : ℝ)) ^ 4)
    (l : List ℤ) (hl : l ≠ []) :
    frob2C (W (gprod l)) ≤ (6 * K) ^ (l.length) * ((prod1p l : ℕ) : ℝ) ^ 4 := by
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  induction l with
  | nil => exact absurd rfl hl
  | cons q t ih =>
    cases t with
    | nil =>
      have h1 : frob2C (W (gprod [q])) ≤ K * (1 + (q.natAbs : ℝ)) ^ 4 := by
        simpa [gprod] using frob2C_W_gT K hKT hKTi q
      have h2 : ((prod1p [q] : ℕ) : ℝ) = 1 + (q.natAbs : ℝ) := by simp [prod1p]
      have h6K : 1 ≤ 6 * K := by nlinarith
      rw [h2]
      calc frob2C (W (gprod [q])) ≤ K * (1 + (q.natAbs : ℝ)) ^ 4 := h1
        _ ≤ (6 * K) ^ 1 * (1 + (q.natAbs : ℝ)) ^ 4 := by
            rw [pow_one]
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    | cons q' rest =>
      have hsplit : gprod (q :: q' :: rest) = gT q * gS * gprod (q' :: rest) := rfl
      have h1 : frob2C (W (gprod (q :: q' :: rest)))
          ≤ frob2C (W (gT q)) * frob2C (W gS) * frob2C (W (gprod (q' :: rest))) := by
        rw [hsplit, map_mul, map_mul]
        calc frob2C ((W (gT q) * W gS) * W (gprod (q' :: rest)))
            ≤ frob2C (W (gT q) * W gS) * frob2C (W (gprod (q' :: rest))) := frob2C_mul _ _
          _ ≤ (frob2C (W (gT q)) * frob2C (W gS)) * frob2C (W (gprod (q' :: rest))) :=
              mul_le_mul_of_nonneg_right (frob2C_mul _ _) (frob2C_nonneg _)
      have h2 : frob2C (W (gT q)) ≤ K * (1 + (q.natAbs : ℝ)) ^ 4 := frob2C_W_gT K hKT hKTi q
      have h3 : frob2C (W gS) = 6 := frob2C_W_gS
      have ih' : frob2C (W (gprod (q' :: rest)))
          ≤ (6 * K) ^ ((q' :: rest).length) * ((prod1p (q' :: rest) : ℕ) : ℝ) ^ 4 :=
        ih (by simp)
      have hA0 : 0 ≤ (1 + (q.natAbs : ℝ)) ^ 4 := by positivity
      have hM0 : 0 ≤ ((prod1p (q' :: rest) : ℕ) : ℝ) ^ 4 := by positivity
      have hP0 : 0 ≤ (6 * K) ^ ((q' :: rest).length) := by positivity
      have hC0 : 0 ≤ (6 * K) ^ ((q' :: rest).length) * ((prod1p (q' :: rest) : ℕ) : ℝ) ^ 4 :=
        mul_nonneg hP0 hM0
      have hstep : (K * (1 + (q.natAbs : ℝ)) ^ 4) * 6
            * ((6 * K) ^ ((q' :: rest).length) * ((prod1p (q' :: rest) : ℕ) : ℝ) ^ 4)
          ≤ (6 * K) ^ ((q :: q' :: rest).length)
            * ((1 + (q.natAbs : ℝ)) * ((prod1p (q' :: rest) : ℕ) : ℝ)) ^ 4 := by
        rw [show (q :: q' :: rest).length = (q' :: rest).length + 1 from rfl, pow_succ, mul_pow]
        exact le_of_eq (by ring)
      have hprod : ((prod1p (q :: q' :: rest) : ℕ) : ℝ)
          = (1 + (q.natAbs : ℝ)) * ((prod1p (q' :: rest) : ℕ) : ℝ) := by
        rw [prod1p_cons]
        push_cast
        ring
      rw [hprod]
      calc frob2C (W (gprod (q :: q' :: rest)))
          ≤ frob2C (W (gT q)) * frob2C (W gS) * frob2C (W (gprod (q' :: rest))) := h1
        _ ≤ (K * (1 + (q.natAbs : ℝ)) ^ 4) * 6
              * ((6 * K) ^ ((q' :: rest).length) * ((prod1p (q' :: rest) : ℕ) : ℝ) ^ 4) := by
            rw [h3]
            have h6 : (0 : ℝ) ≤ 6 := by norm_num
            calc frob2C (W (gT q)) * 6 * frob2C (W (gprod (q' :: rest)))
                ≤ (K * (1 + (q.natAbs : ℝ)) ^ 4) * 6 * frob2C (W (gprod (q' :: rest))) :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h6)
                    (frob2C_nonneg _)
              _ ≤ (K * (1 + (q.natAbs : ℝ)) ^ 4) * 6
                  * ((6 * K) ^ ((q' :: rest).length) * ((prod1p (q' :: rest) : ℕ) : ℝ) ^ 4) :=
                  mul_le_mul_of_nonneg_left ih' (mul_nonneg (mul_nonneg hK0 hA0) h6)
        _ ≤ (6 * K) ^ ((q :: q' :: rest).length)
            * ((1 + (q.natAbs : ℝ)) * ((prod1p (q' :: rest) : ℕ) : ℝ)) ^ 4 := hstep

/-! ## The Frobenius norm of the entries -/

/-- The absolute value of an integer, as a real number. -/
def entR (x : ℤ) : ℝ := |(x : ℝ)|

lemma natAbs_cast_entR (x : ℤ) : ((x.natAbs : ℕ) : ℝ) = entR x := by
  have h : (((x.natAbs : ℕ) : ℝ)) = ((((x.natAbs : ℕ) : ℤ)) : ℝ) := by simp
  rw [h, Int.natCast_natAbs, Int.cast_abs]
  rfl

theorem frob2Z_cast_entR (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (frob2Z M : ℝ) = entR (M 0 0) ^ 2 + entR (M 0 1) ^ 2
      + entR (M 1 0) ^ 2 + entR (M 1 1) ^ 2 := by
  simp only [frob2Z, Nat.cast_add, Nat.cast_pow, natAbs_cast_entR]

theorem uZ_cast_entR (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (uZ M : ℝ) = entR (M 0 0) + entR (M 1 0) := by
  simp only [uZ, Nat.cast_add, natAbs_cast_entR]

theorem entry_sq_sum (γ : SL(2,ℤ)) (i j : Fin 2) :
    ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2 ≤
      ∑ i : Fin 2, ∑ j : Fin 2, ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2 := by
  have h1 : ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2
      ≤ ∑ j : Fin 2, ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2 :=
    Finset.single_le_sum
      (f := fun j : Fin 2 => ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ j)
  have h2 : (∑ j : Fin 2, ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2)
      ≤ ∑ i : Fin 2, ∑ j : Fin 2, ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2 :=
    Finset.single_le_sum
      (f := fun i : Fin 2 => ∑ j : Fin 2, ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j : ℝ)) ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)
  linarith

theorem entry_le_Frob (γ : SL(2,ℤ)) (i j : Fin 2) :
    ((((γ : Matrix (Fin 2) (Fin 2) ℤ)) i j).natAbs : ℝ) ≤ Work.Asymptotics.Frob γ := by
  rw [natAbs_cast_entR, Work.Asymptotics.Frob]
  refine Real.le_sqrt_of_sq_le ?_
  simp only [entR, sq_abs]
  have h := entry_sq_sum γ i j
  simp only [Fin.sum_univ_two] at h
  linarith [h]

theorem frob2C_entry_le (A : Matrix (Fin 6) (Fin 6) ℂ) (i j : Fin 6) :
    ‖A i j‖ ≤ 1 + frob2C A := by
  have h1 : ‖A i j‖ ^ 2 ≤ frob2C A := by
    have hinner : ‖A i j‖ ^ 2 ≤ ∑ j : Fin 6, ‖A i j‖ ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin 6 => ‖A i j‖ ^ 2) (fun j _ => by positivity)
        (Finset.mem_univ j)
    have houter : (∑ j : Fin 6, ‖A i j‖ ^ 2) ≤ frob2C A := by
      simp only [frob2C]
      exact Finset.single_le_sum (f := fun i : Fin 6 => ∑ j : Fin 6, ‖A i j‖ ^ 2)
        (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)
    linarith
  have h2 : ‖A i j‖ ≤ Real.sqrt (frob2C A) := Real.le_sqrt_of_sq_le h1
  have h3 : Real.sqrt (frob2C A) ≤ 1 + frob2C A := by
    rw [Real.sqrt_le_iff]
    refine ⟨add_nonneg zero_le_one (frob2C_nonneg A), ?_⟩
    nlinarith [frob2C_nonneg A]
  linarith

/-! ## The main bound -/

theorem frob2C_W_bound :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ γ : SL(2,ℤ),
      frob2C (W γ) ≤ C * (1 + Work.Asymptotics.Frob γ) ^ N := by
  obtain ⟨K0, hK00, hKT0, hKTi0⟩ := sigmaT_pow_bound
  set K : ℝ := K0 + 1 with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith
  have hK0 : 0 ≤ K := le_trans zero_le_one hK1
  have hKT : ∀ m : ℕ, frob2C (Work.Modular.sigmaT ^ m) ≤ K * (1 + (m : ℝ)) ^ 4 := by
    intro m
    refine le_trans (hKT0 m) ?_
    have hnn : 0 ≤ (1 + (m : ℝ)) ^ 4 := by positivity
    have hle : K0 ≤ K := by rw [hKdef]; linarith
    exact mul_le_mul_of_nonneg_right hle hnn
  have hKTi : ∀ m : ℕ, frob2C (Work.Modular.sigmaTinv ^ m) ≤ K * (1 + (m : ℝ)) ^ 4 := by
    intro m
    refine le_trans (hKTi0 m) ?_
    have hnn : 0 ≤ (1 + (m : ℝ)) ^ 4 := by positivity
    have hle : K0 ≤ K := by rw [hKdef]; linarith
    exact mul_le_mul_of_nonneg_right hle hnn
  obtain ⟨M, hM⟩ := exists_nat_gt (max (6 * K) 1)
  have hMx : 6 * K ≤ (2 : ℝ) ^ M := by
    have h1 : (M : ℝ) < (2 : ℝ) ^ M := by
      exact_mod_cast (Nat.lt_two_pow_self (n := M))
    have h2 : 6 * K < (M : ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
    linarith
  refine ⟨4 ^ M * 2048 ^ 4, ((M + 48 : ℕ) : ℝ), by positivity, by positivity, ?_⟩
  intro γ
  let M0 : Matrix (Fin 2) (Fin 2) ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ)
  have hdet : detZ M0 = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    exact h
  let k := kZ M0
  let l := LZ M0 (k + 1)
  have hmin : ∀ j < k, (stateZ M0 j) 1 0 ≠ 0 := fun j hj => kZ_min M0 hj
  have hterm : (stateZ M0 k) 1 0 = 0 := kZ_spec M0
  have hrecon : recon l = M0 ∨ recon l = -M0 := recon_LZ k M0 hmin hterm hdet
  have hcoe : ((gprod l : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = recon l := coe_gprod l
  have hgp : gprod l = γ ∨ gprod l = -γ := by
    rcases hrecon with h | h
    · exact Or.inl (Subtype.ext (by rw [hcoe, h]))
    · exact Or.inr (Subtype.ext (by rw [hcoe, h]; rfl))
  have hW : W (gprod l) = W γ := by
    rcases hgp with h | h
    · rw [h]
    · rw [h, W_neg]
  have hlen : l.length = k + 1 := by simp [l, LZ]
  set F : ℝ := 1 + Work.Asymptotics.Frob γ with hFdef
  have hF1 : 1 ≤ F := by
    have := Work.Asymptotics.Frob_nonneg γ
    rw [hFdef]; linarith
  have hF0 : 0 ≤ F := le_trans zero_le_one hF1
  have hFrob0 : 0 ≤ Work.Asymptotics.Frob γ := Work.Asymptotics.Frob_nonneg γ
  have hentry : ∀ i j : Fin 2, entR (M0 i j) ≤ Work.Asymptotics.Frob γ := by
    intro i j
    have h := entry_le_Frob γ i j
    rw [natAbs_cast_entR] at h
    exact h
  have huZ : (uZ M0 : ℝ) ≤ 2 * F := by
    rw [uZ_cast_entR, hFdef]
    have h1 := hentry 0 0
    have h2 := hentry 1 0
    linarith
  have hfZ : (frob2Z M0 : ℝ) ≤ F ^ 2 := by
    have hS : (frob2Z M0 : ℝ) = (Work.Asymptotics.Frob γ) ^ 2 := by
      rw [Work.Asymptotics.Frob, Real.sq_sqrt (by positivity)]
      simp only [frob2Z_cast_entR, entR, sq_abs]
      rfl
    rw [hS, hFdef]
    nlinarith [hFrob0]
  have h2k : (2 : ℝ) ^ k ≤ 2 * F := by
    have h := len_bound M0 k hmin
    have hcast : ((2 : ℕ) ^ k : ℝ) ≤ 2 * (max ((M0 1 0).natAbs) 1 : ℝ) := by
      exact_mod_cast h
    have hmax : (max (((M0 1 0).natAbs : ℕ) : ℝ) 1) ≤ F := by
      refine max_le ?_ ?_
      · rw [natAbs_cast_entR, hFdef]
        exact le_trans (hentry 1 0) (le_add_of_nonneg_left zero_le_one)
      · rw [hFdef]; linarith
    calc (2 : ℝ) ^ k = ((2 : ℕ) ^ k : ℝ) := by push_cast; ring
      _ ≤ 2 * (max (((M0 1 0).natAbs : ℕ) : ℝ) 1) := hcast
      _ ≤ 2 * F := by linarith
  have htd := terminal_data (M := stateZ M0 k) hterm
    (by rw [detZ_stateZ]; exact hdet)
  have hPk : ((prod1p (LZ M0 k) : ℕ) : ℝ) ≤ 8 * F ^ 3 := by
    have h1 : prod1p (LZ M0 k) ≤ 3 ^ k * uZ M0 := by
      have hh := prod_bound M0 k hmin
      rw [htd.1, mul_one] at hh
      exact hh
    have h1' : ((prod1p (LZ M0 k) : ℕ) : ℝ) ≤ (3 : ℝ) ^ k * (uZ M0 : ℝ) := by
      exact_mod_cast h1
    have h3k : (3 : ℝ) ^ k ≤ (2 * F) ^ 2 := by
      have h4 : (3 : ℝ) ^ k ≤ (4 : ℝ) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
      have h5 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * k = k * 2 by ring, pow_mul]
      rw [h5] at h4
      exact le_trans h4 (pow_le_pow_left₀ (by positivity) h2k 2)
    calc ((prod1p (LZ M0 k) : ℕ) : ℝ) ≤ (3 : ℝ) ^ k * (uZ M0 : ℝ) := h1'
      _ ≤ (2 * F) ^ 2 * (2 * F) := mul_le_mul h3k huZ (by positivity) (by positivity)
      _ = 8 * F ^ 3 := by ring
  have hfk : (frob2Z (stateZ M0 k) : ℝ) ≤ 128 * F ^ 9 := by
    have h1 := frob2Z_bound M0 k hmin
    have h1' : (frob2Z (stateZ M0 k) : ℝ)
        ≤ (2 : ℝ) ^ k * ((prod1p (LZ M0 k) : ℕ) : ℝ) ^ 2 * (frob2Z M0 : ℝ) := by
      exact_mod_cast h1
    have hPk2 : ((prod1p (LZ M0 k) : ℕ) : ℝ) ^ 2 ≤ (8 * F ^ 3) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hPk 2
    calc (frob2Z (stateZ M0 k) : ℝ)
        ≤ (2 : ℝ) ^ k * ((prod1p (LZ M0 k) : ℕ) : ℝ) ^ 2 * (frob2Z M0 : ℝ) := h1'
      _ ≤ (2 * F) * (8 * F ^ 3) ^ 2 * F ^ 2 :=
          mul_le_mul (mul_le_mul h2k hPk2 (by positivity) (by positivity)) hfZ
            (by positivity) (by positivity)
      _ = 128 * F ^ 9 := by ring
  have hqk : 1 + ((quo (stateZ M0 k)).natAbs : ℝ) ≤ 256 * F ^ 9 := by
    have h1 : ((quo (stateZ M0 k)).natAbs : ℝ) ≤ (frob2Z (stateZ M0 k) : ℝ) := by
      exact_mod_cast htd.2.2
    have h2 : (1 : ℝ) ≤ F ^ 9 := by
      calc (1 : ℝ) = 1 ^ 9 := by norm_num
        _ ≤ F ^ 9 := pow_le_pow_left₀ (by norm_num) hF1 9
    have h3 : (0 : ℝ) ≤ F ^ 9 := by positivity
    linarith
  have hPl : ((prod1p l : ℕ) : ℝ) ≤ 2048 * F ^ 12 := by
    have hsplit : prod1p l = prod1p (LZ M0 k) * (1 + (quo (stateZ M0 k)).natAbs) := by
      rw [show l = LZ M0 (k + 1) from rfl, prod1p_LZ_succ]
    rw [hsplit]
    push_cast
    calc ((prod1p (LZ M0 k) : ℕ) : ℝ) * (1 + ((quo (stateZ M0 k)).natAbs : ℝ))
        ≤ (8 * F ^ 3) * (256 * F ^ 9) :=
          mul_le_mul hPk hqk (by positivity) (by positivity)
      _ = 2048 * F ^ 12 := by ring
  have h6K : (6 * K) ^ (l.length) ≤ (4 * F) ^ M := by
    rw [hlen]
    have h2p : ((2 : ℝ) ^ M) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ M := by
      rw [← pow_mul, ← pow_mul]; ring_nf
    have h2k1 : (2 : ℝ) ^ (k + 1) ≤ 4 * F := by
      rw [pow_succ']
      linarith
    calc (6 * K) ^ (k + 1) ≤ ((2 : ℝ) ^ M) ^ (k + 1) :=
          pow_le_pow_left₀ (by positivity) hMx (k + 1)
      _ = ((2 : ℝ) ^ (k + 1)) ^ M := h2p
      _ ≤ (4 * F) ^ M := pow_le_pow_left₀ (by positivity) h2k1 M
  have hbound : frob2C (W γ) ≤ (4 * F) ^ M * 2048 ^ 4 * F ^ 48 := by
    have hl : l ≠ [] := by
      intro h0
      have h1 : l.length = 0 := by rw [h0]; rfl
      rw [hlen] at h1
      exact Nat.succ_ne_zero k h1
    have h := frob2C_gprod_le K hK1 hKT hKTi l hl
    have hPl4 : ((prod1p l : ℕ) : ℝ) ^ 4 ≤ (2048 * F ^ 12) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hPl 4
    calc frob2C (W γ) = frob2C (W (gprod l)) := by rw [hW]
      _ ≤ (6 * K) ^ (l.length) * ((prod1p l : ℕ) : ℝ) ^ 4 := h
      _ ≤ (4 * F) ^ M * (2048 * F ^ 12) ^ 4 := by
          apply mul_le_mul h6K hPl4 (by positivity) (by positivity)
      _ = (4 * F) ^ M * 2048 ^ 4 * F ^ 48 := by ring
  calc frob2C (W γ) ≤ (4 * F) ^ M * 2048 ^ 4 * F ^ 48 := hbound
    _ = (4 ^ M * 2048 ^ 4) * F ^ (M + 48) := by rw [mul_pow, pow_add]; ring
    _ = (4 ^ M * 2048 ^ 4) * (1 + Work.Asymptotics.Frob γ) ^ ((M + 48 : ℕ) : ℝ) := by
        rw [hFdef, Real.rpow_natCast]

end Work.Rigidity.SigmaEntryBound
