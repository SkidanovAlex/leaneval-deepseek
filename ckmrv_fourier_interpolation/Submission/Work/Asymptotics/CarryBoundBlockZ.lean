/-
# Carries for the blocks `T^k` and `S T^k` with `k : ℤ`

`Work.Asymptotics.carryTpow` gives the carries of `T^n` for `n ≥ 0` (the *flat* formula
`∑_{m<n} ∑_j σ(T^{n-1-m})_{ij} • (carryAtomT j · T^m)`) together with the defining equation
`carryComb (carryTpow n i) = rowDiff (of (T^n)) i` and the polynomial bound
`CB (carryTpow n i) (60 (1+n)^3) (300 (1+n))`.

Here we extend this to all integer exponents (`carryT`) by inverting, using the cocycle identity
`rowDiff (x * y) i = ∑_j σ(x)_{ij} • rowDiff y j + rowDiff x i * y` with `x = of (T^k)`,
`y = of (T^{-k})` and `of (T^k) * of (T^{-k}) = 1`, and to the blocks `S T^k` (`carryST`) by the
same cocycle identity with `x = of S`, `y = of (T^k)`.

All the carries satisfy a bound of the shape
`CB (carry k i) (2000000 * (1+|k|)^5) (1000 * (1+|k|)^2)`.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryBoundBlock

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels
open Work.Residues

/-- `carryComb` on an opaque `triSum` (so that `rw` can use it). -/
lemma carryComb_triSum' {ι : Type*} (s : Finset ι) (f : ι → R × R × R) :
    carryComb (triSum s f).1 (triSum s f).2.1 (triSum s f).2.2
      = ∑ i ∈ s, carryComb (f i).1 (f i).2.1 (f i).2.2 := by
  simp only [triSum_fst, triSum_snd, triSum_thd]
  exact carryComb_triSum s f

/-! ## `σ_R(T^k)` for all integer `k` -/

/-- `σ_R(T^k)`, written as the power of the explicit matrix `σ(T)` (`k ≥ 0`) or of its
explicit inverse `σ(T)⁻¹` (`k < 0`). -/
noncomputable def sigmaOfT (k : ℤ) : Matrix (Fin 6) (Fin 6) ℂ :=
  if 0 ≤ k then Work.Modular.sigmaT ^ k.toNat else Work.Modular.sigmaTinv ^ (-k).toNat

lemma sigmaOfT_of_nonneg {k : ℤ} (h : 0 ≤ k) :
    sigmaOfT k
      = Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) := by
  rw [sigmaOfT, if_pos h]
  have hT : ((ModularGroup.T : SL(2, ℤ)) ^ k) = ModularGroup.T ^ k.toNat := by
    rw [← _root_.zpow_natCast, Int.toNat_of_nonneg h]
  rw [hT, (sigmaR_of_T_pow k.toNat).symm]

lemma sigmaOfT_of_neg {k : ℤ} (h : ¬ 0 ≤ k) :
    sigmaOfT k
      = Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) := by
  rw [sigmaOfT, if_neg h]
  have hpos : (0 : ℤ) ≤ -k := by omega
  have hT : ((ModularGroup.T : SL(2, ℤ)) ^ k)
      = ModularGroup.T ^ (-(((-k).toNat : ℕ) : ℤ)) := by
    rw [Int.toNat_of_nonneg hpos, neg_neg]
  rw [hT, (sigmaR_of_T_neg (-k).toNat).symm]

lemma sigmaOfT_eq (k : ℤ) :
    sigmaOfT k
      = Work.Residues.sigmaR
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) := by
  by_cases h : 0 ≤ k
  · exact sigmaOfT_of_nonneg h
  · exact sigmaOfT_of_neg h

lemma sigmaOfT_entry_bound (k : ℤ) (i j : Fin 6) :
    ‖sigmaOfT k i j‖ ≤ 10 * (1 + |(k : ℝ)|) ^ 2 := by
  by_cases h : 0 ≤ k
  · rw [sigmaOfT, if_pos h]
    refine le_trans (sigmaT_pow_entry_norm k.toNat i j) ?_
    have hk : (((k.toNat : ℕ)) : ℝ) = |(k : ℝ)| := by
      have h1 : (((k.toNat : ℕ)) : ℝ) = (k : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg h : (((k.toNat : ℕ)) : ℤ) = k)
      rw [h1, abs_of_nonneg (by exact_mod_cast h)]
    rw [hk]
  · rw [sigmaOfT, if_neg h]
    refine le_trans (sigmaTinv_pow_entry_norm ((-k).toNat) i j) ?_
    have hk : ((((-k).toNat : ℕ)) : ℝ) = |(k : ℝ)| := by
      have h1 : ((((-k).toNat : ℕ)) : ℝ) = ((-k : ℤ) : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -k)
          : ((((-k).toNat : ℕ)) : ℤ) = -k)
      rw [h1, Int.cast_neg, abs_of_nonpos (by exact_mod_cast le_of_lt (not_le.mp h))]
    rw [hk]

/-! ## The carries of `T^k` -/

/-- The carries of the block `T^k`, for every `k : ℤ`.  For `k ≥ 0` this is `carryTpow`; for
`k < 0` we use the cocycle identity for `x = of (T^k)`, `y = of (T^{-k})`. -/
noncomputable def carryT (k : ℤ) (i : Fin 6) : R × R × R :=
  if 0 ≤ k then carryTpow k.toNat i
  else triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
    (fun j => triSmul ((sigmaOfT k) i j) (carryTpow (-k).toNat j)))) (ModularGroup.T ^ k)

lemma carryT_of_pos {k : ℤ} (h : 0 ≤ k) : carryT k = carryTpow k.toNat := by
  funext i
  rw [carryT, if_pos h]

lemma carryT_of_neg {k : ℤ} (h : ¬ 0 ≤ k) (m : ℕ) (hm : m = (-k).toNat) :
    carryT k = fun i => triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul ((sigmaOfT k) i j) (carryTpow m j)))) (ModularGroup.T ^ k) := by
  funext i
  rw [carryT, if_neg h, hm]

/-- The defining equation for `carryT`. -/
theorem carryT_spec (k : ℤ) (i : Fin 6) :
    carryComb (carryT k i).1 (carryT k i).2.1 (carryT k i).2.2
      = Work.Residues.rowDiff
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) i := by
  by_cases h : 0 ≤ k
  · rw [carryT_of_pos h]
    have hT : ((ModularGroup.T : SL(2, ℤ)) ^ k) = ModularGroup.T ^ k.toNat := by
      rw [← _root_.zpow_natCast, Int.toNat_of_nonneg h]
    rw [hT]
    exact carryTpow_spec k.toNat i
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (-k).toNat := ⟨_, rfl⟩
    have hmZ : ((m : ℕ) : ℤ) = -k := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hkey : carryT k i
        = triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
            (fun j => triSmul ((sigmaOfT k) i j) (carryTpow m j)))) (ModularGroup.T ^ k) := by
      rw [carryT_of_neg h m hm]
    rw [hkey, carryComb_triMulOf, carryComb_triSmul, carryComb_triSum']
    have hinner : ∀ j : Fin 6,
        carryComb (triSmul ((sigmaOfT k) i j) (carryTpow m j)).1
          (triSmul ((sigmaOfT k) i j) (carryTpow m j)).2.1
          (triSmul ((sigmaOfT k) i j) (carryTpow m j)).2.2
        = (Work.Residues.sigmaR
              (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k))) i j
            • Work.Residues.rowDiff
                (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
                  (ModularGroup.T ^ m)) j := fun j => by
      rw [carryComb_triSmul, sigmaOfT_of_neg h, carryTpow_spec m j]
    rw [show (∑ j : Fin 6, carryComb (triSmul ((sigmaOfT k) i j) (carryTpow m j)).1
          (triSmul ((sigmaOfT k) i j) (carryTpow m j)).2.1
          (triSmul ((sigmaOfT k) i j) (carryTpow m j)).2.2)
        = ∑ j : Fin 6, (Work.Residues.sigmaR
              (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k))) i j
            • Work.Residues.rowDiff
                (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
                  (ModularGroup.T ^ m)) j from Finset.sum_congr rfl (fun j _ => hinner j)]
    set S : R := ∑ j : Fin 6, (Work.Residues.sigmaR
              (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k))) i j
            • Work.Residues.rowDiff
                (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
                  (ModularGroup.T ^ m)) j with hS
    have hTmul : (ModularGroup.T : SL(2, ℤ)) ^ k * ModularGroup.T ^ m = 1 := by
      rw [← _root_.zpow_natCast (ModularGroup.T) m, ← _root_.zpow_add, hmZ,
        add_neg_cancel, zpow_zero]
    have h1 : MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)
        * MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ m)
        = 1 := by rw [← map_mul, hTmul, map_one]
    have h2 : MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ m)
        * MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)
        = 1 := by
      rw [← map_mul,
        show ((ModularGroup.T : SL(2, ℤ)) ^ m * ModularGroup.T ^ k) = 1 from by
          rw [← _root_.zpow_natCast (ModularGroup.T) m, ← _root_.zpow_add, hmZ,
            neg_add_cancel, zpow_zero], map_one]
    have hcyc := Work.Residues.rowDiff_mul
      (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k))
      (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ m)) i
    rw [h1, Work.Residues.rowDiff_one] at hcyc
    have hzero : S + Work.Residues.rowDiff
            (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) i
          * MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ m)
        = 0 := hcyc.symm
    have hr : Work.Residues.rowDiff
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) i
          * MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ m)
        = -S := by
      have hz := hzero
      rw [add_comm] at hz
      exact eq_neg_of_add_eq_zero_left hz
    rw [show ((-1 : ℂ) • S) = -S from by rw [_root_.neg_smul, one_smul]]
    rw [← hr]
    rw [mul_assoc, h2, mul_one]

/-! ## The carries of `S T^k` -/

/-- The carries of the block `S T^k`, for every `k : ℤ`, from the cocycle identity applied to
`S` and `T^k`. -/
noncomputable def carryST (k : ℤ) (i : Fin 6) : R × R × R :=
  triAdd (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul (Work.Modular.sigmaS i j) (carryT k j)))
    (triMulOf (carryAtomS i) (ModularGroup.T ^ k))

lemma sigmaR_of_S_eq : Work.Residues.sigmaR
      (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) ModularGroup.S)
    = Work.Modular.sigmaS := by
  simpa [Work.Kernels.R_S] using Work.Residues.sigmaR_R_S

lemma sigmaR_of_ST_zpow (k : ℤ) :
    Work.Residues.sigmaR
        (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
          (ModularGroup.S * ModularGroup.T ^ k))
      = Work.Modular.sigmaS * sigmaOfT k := by
  have h1 : MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (ModularGroup.S * ModularGroup.T ^ k)
      = MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) ModularGroup.S
        * MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k) :=
    map_mul _ _ _
  rw [h1, map_mul, sigmaR_of_S_eq, ← sigmaOfT_eq k]

/-- The defining equation for `carryST`. -/
theorem carryST_spec (k : ℤ) (i : Fin 6) :
    carryComb (carryST k i).1 (carryST k i).2.1 (carryST k i).2.2
      = Work.Residues.rowDiff
          (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ)
            (ModularGroup.S * ModularGroup.T ^ k)) i := by
  unfold carryST
  rw [carryComb_triAdd, carryComb_triMulOf, carryComb_triSum']
  have hinner : ∀ j : Fin 6,
      carryComb (triSmul (Work.Modular.sigmaS i j) (carryT k j)).1
        (triSmul (Work.Modular.sigmaS i j) (carryT k j)).2.1
        (triSmul (Work.Modular.sigmaS i j) (carryT k j)).2.2
      = (Work.Residues.sigmaR
            (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) ModularGroup.S)) i j
          • Work.Residues.rowDiff
              (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) j :=
    fun j => by rw [carryComb_triSmul, carryT_spec k j, ← sigmaR_of_S_eq]
  rw [show (∑ j : Fin 6, carryComb (triSmul (Work.Modular.sigmaS i j) (carryT k j)).1
        (triSmul (Work.Modular.sigmaS i j) (carryT k j)).2.1
        (triSmul (Work.Modular.sigmaS i j) (carryT k j)).2.2)
      = ∑ j : Fin 6, (Work.Residues.sigmaR
            (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) ModularGroup.S)) i j
          • Work.Residues.rowDiff
              (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) j
      from Finset.sum_congr rfl (fun j _ => hinner j)]
  rw [carryAtomS_spec i]
  have hcyc := Work.Residues.rowDiff_mul
    (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) ModularGroup.S)
    (MonoidAlgebra.of ℂ (Matrix.SpecialLinearGroup (Fin 2) ℤ) (ModularGroup.T ^ k)) i
  rw [← map_mul] at hcyc
  exact hcyc.symm

/-! ## The bounds -/

/-- The component bound for the block `T^k`. -/
noncomputable def cbT (k : ℤ) : ℝ := 300000 * (1 + |(k : ℝ)|) ^ 5

/-- The component bound for the block `S T^k`. -/
noncomputable def cbST (k : ℤ) : ℝ := 2000000 * (1 + |(k : ℝ)|) ^ 5

/-- The (uniform) support bound for the block `T^k` / `S T^k` with parameter `k`. -/
noncomputable def kbu (k : ℤ) : ℝ := 1000 * (1 + |(k : ℝ)|) ^ 2

lemma one_add_abs_nonneg (k : ℤ) : (0 : ℝ) ≤ 1 + |(k : ℝ)| := by
  have h := abs_nonneg (k : ℝ); linarith

lemma one_le_one_add_abs (k : ℤ) : (1 : ℝ) ≤ 1 + |(k : ℝ)| := by
  have h := abs_nonneg (k : ℝ); linarith

lemma abs_add_two_le_three (k : ℤ) : |(k : ℝ)| + 2 ≤ 3 * (1 + |(k : ℝ)|) := by
  have h := abs_nonneg (k : ℝ); linarith

lemma Frob_T_zpow_le (k : ℤ) : Frob (ModularGroup.T ^ k) ≤ |(k : ℝ)| + 2 := by
  rw [Frob_T_zpow, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs (k : ℝ), abs_nonneg (k : ℝ)]

lemma Frob_ST_zpow_le (k : ℤ) : Frob (ModularGroup.S * ModularGroup.T ^ k) ≤ |(k : ℝ)| + 2 := by
  rw [Frob_ST_zpow, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs (k : ℝ), abs_nonneg (k : ℝ)]

theorem carryT_bound (k : ℤ) (i : Fin 6) : CB (carryT k i) (cbT k) (kbu k) := by
  by_cases h : 0 ≤ k
  · rw [carryT_of_pos h]
    have hk : (((k.toNat : ℕ)) : ℝ) = |(k : ℝ)| := by
      have h1 : (((k.toNat : ℕ)) : ℝ) = (k : ℝ) := by
        exact_mod_cast (Int.toNat_of_nonneg h : (((k.toNat : ℕ)) : ℤ) = k)
      rw [h1, abs_of_nonneg (by exact_mod_cast h)]
    have h1 := carryTpow_bound k.toNat i
    rw [hk] at h1
    refine CB_mono h1 ?_ ?_
    · rw [cbT]
      have ha := one_le_one_add_abs k
      have hp : (1 + |(k : ℝ)|) ^ (3 : ℕ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) :=
        pow_le_pow_right₀ ha (by norm_num)
      have h0 : (0 : ℝ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) := pow_nonneg (one_add_abs_nonneg k) 5
      nlinarith [hp, h0]
    · rw [kbu]
      have ha := one_le_one_add_abs k
      have hp : (1 + |(k : ℝ)|) ^ (1 : ℕ) ≤ (1 + |(k : ℝ)|) ^ (2 : ℕ) :=
        pow_le_pow_right₀ ha (by norm_num)
      nlinarith [hp]
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, m = (-k).toNat := ⟨_, rfl⟩
    rw [carryT_of_neg h m hm]
    have hmZ : ((m : ℕ) : ℤ) = -k := by rw [hm]; exact Int.toNat_of_nonneg (by omega)
    have hmR : ((m : ℕ) : ℝ) = |(k : ℝ)| := by
      have h1 : (((m : ℕ)) : ℝ) = ((-k : ℤ) : ℝ) := by exact_mod_cast hmZ
      rw [h1, Int.cast_neg, abs_of_nonpos (by exact_mod_cast le_of_lt (not_le.mp h))]
    have hinner : ∀ j : Fin 6,
        CB (triSmul ((sigmaOfT k) i j) (carryTpow m j))
          (10 * (1 + |(k : ℝ)|) ^ 2 * (60 * (1 + (m : ℝ)) ^ 3)) (300 * (1 + (m : ℝ))) := by
      intro j
      refine CB_mono (CB_triSmul ((sigmaOfT k) i j) (carryTpow_bound m j)) ?_ (le_refl _)
      have hb := sigmaOfT_entry_bound k i j
      have h0 : (0 : ℝ) ≤ 60 * (1 + (m : ℝ)) ^ 3 := by positivity
      calc ‖(sigmaOfT k) i j‖ * (60 * (1 + (m : ℝ)) ^ 3)
          ≤ (10 * (1 + |(k : ℝ)|) ^ 2) * (60 * (1 + (m : ℝ)) ^ 3) :=
            mul_le_mul_of_nonneg_right hb h0
        _ = 10 * (1 + |(k : ℝ)|) ^ 2 * (60 * (1 + (m : ℝ)) ^ 3) := by ring
    have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((sigmaOfT k) i j) (carryTpow m j)))
        (6 * (10 * (1 + |(k : ℝ)|) ^ 2 * (60 * (1 + (m : ℝ)) ^ 3))) (300 * (1 + (m : ℝ))) :=
      CB_triSum (Finset.univ : Finset (Fin 6)) _ (fun j _ => hinner j)
    have hgoal : CB (triMulOf (triSmul (-1) (triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul ((sigmaOfT k) i j) (carryTpow m j)))) (ModularGroup.T ^ k))
        (6 * (10 * (1 + |(k : ℝ)|) ^ 2 * (60 * (1 + (m : ℝ)) ^ 3)))
        (300 * (1 + (m : ℝ)) * Frob (ModularGroup.T ^ k)) := by
      have hh := CB_triMulOf (ModularGroup.T ^ k) (CB_triSmul (-1) hsum)
      simpa using hh
    refine CB_mono hgoal ?_ ?_
    · rw [cbT, hmR]
      have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := one_add_abs_nonneg k
      have h5 : (0 : ℝ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) := pow_nonneg ha 5
      have hp : (1 + |(k : ℝ)|) ^ (3 : ℕ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) :=
        pow_le_pow_right₀ (one_le_one_add_abs k) (by norm_num)
      nlinarith [h5, hp]
    · rw [kbu, hmR]
      have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := one_add_abs_nonneg k
      have hF := Frob_T_zpow_le k
      have h2 := abs_add_two_le_three k
      have h4 : (0 : ℝ) ≤ 300 * (1 + |(k : ℝ)|) := by linarith
      calc 300 * (1 + |(k : ℝ)|) * Frob (ModularGroup.T ^ k)
          ≤ 300 * (1 + |(k : ℝ)|) * (|(k : ℝ)| + 2) :=
            mul_le_mul_of_nonneg_left hF h4
        _ ≤ 300 * (1 + |(k : ℝ)|) * (3 * (1 + |(k : ℝ)|)) :=
            mul_le_mul_of_nonneg_left h2 h4
        _ = 900 * (1 + |(k : ℝ)|) ^ 2 := by ring
        _ ≤ 1000 * (1 + |(k : ℝ)|) ^ 2 := by
            nlinarith [pow_nonneg ha 2]

theorem carryST_bound (k : ℤ) (i : Fin 6) : CB (carryST k i) (cbST k) (kbu k) := by
  have hσ : ∀ j : Fin 6, ‖Work.Modular.sigmaS i j‖ ≤ 1 := by
    intro j
    fin_cases i <;> fin_cases j <;>
      simp [Work.Modular.sigmaS, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one]
  have hT := carryT_bound k
  have hcbT0 : (0 : ℝ) ≤ cbT k := by rw [cbT]; positivity
  have hsum : CB (triSum (Finset.univ : Finset (Fin 6))
      (fun j => triSmul (Work.Modular.sigmaS i j) (carryT k j))) (6 * cbT k) (kbu k) := by
    refine CB_triSum (Finset.univ : Finset (Fin 6)) _ (Cb := cbT k) (K := kbu k) ?_
    intro j _
    have h1 : ‖Work.Modular.sigmaS i j‖ * cbT k ≤ cbT k := by
      simpa using mul_le_mul_of_nonneg_right (hσ j) hcbT0
    exact CB_mono (CB_triSmul (Work.Modular.sigmaS i j) (hT j)) h1 (le_refl _)
  have htail : CB (triMulOf (carryAtomS i) (ModularGroup.T ^ k)) 1 (100 * (|(k : ℝ)| + 2)) := by
    refine CB_mono (CB_triMulOf (ModularGroup.T ^ k) (carryAtomS_bound i)) ?_ ?_
    · norm_num
    · have hF := Frob_T_zpow_le k
      nlinarith [hF]
  have hgoal := CB_triAdd hsum htail
  rw [carryST]
  refine CB_mono hgoal ?_ ?_
  · rw [cbST, cbT]
    have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := one_add_abs_nonneg k
    have h5 : (1 : ℝ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) := one_le_pow₀ (one_le_one_add_abs k)
    have h5n : (0 : ℝ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) := le_trans zero_le_one h5
    nlinarith [h5, h5n]
  · rw [kbu]
    refine max_le (by norm_num) ?_
    have ha : (0 : ℝ) ≤ 1 + |(k : ℝ)| := one_add_abs_nonneg k
    have h2 := abs_add_two_le_three k
    have h52 : (1 + |(k : ℝ)|) ^ (2 : ℕ) ≤ (1 + |(k : ℝ)|) ^ (5 : ℕ) :=
      pow_le_pow_right₀ (one_le_one_add_abs k) (by norm_num)
    nlinarith [h2, h52, ha]

end Work.Asymptotics
