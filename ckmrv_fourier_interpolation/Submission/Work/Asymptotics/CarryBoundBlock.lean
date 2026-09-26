/-
# Carries for the blocks `T^k` and `S T^k`

The global argument decomposes `γ` into `O(log ‖γ‖)` blocks of the form `T^k` or `S T^k`
(`Work.Asymptotics.block_factorization`).  This file provides the carries of those blocks.

For `T^n` (`n ≥ 0`) we use the *flat* formula
`carryTpow n i = ∑_{m < n} ∑_j σ(T^{n-1-m})_{ij} • (carryAtomT j · T^m)`, which is exactly the
sum `∑_t σ(T^t)·carry(T)·T^{n-1-t}` produced by the cocycle recursion.  It satisfies the
recursion `carry (T^{n+1}) i = σ(T^n)·carry(T) + carry(T^n)·T` (so the defining equation follows
from `carryAtomT_spec` and `Work.Residues.rowDiff_mul`), and -- unlike the recursion -- it can be
bounded directly, because `σ(T^m)` grows only polynomially in `m`.

Negative powers are handled by `rowDiff (T^{-m}) i = -(σ(T^{-m}) · rowDiff (T^m)) · T^{-m}`, and
the blocks `S T^k` by the cocycle identity applied to `S` and `T^k`.
-/
import Mathlib
import Submission.Work.Asymptotics.CarryBoundAtom
import Submission.Work.Asymptotics.sigma_T_zpow_growth

set_option maxHeartbeats 800000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups MonoidAlgebra ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels
open Work.Residues

/-! ## A generic "component map" -/

/-- A map on carries which is compatible with all the componentwise operations.  The three
projections are the canonical examples. -/
structure Comp where
  /-- The underlying map. -/
  toFun : R × R × R → R
  add : ∀ p q : R × R × R, toFun (triAdd p q) = toFun p + toFun q
  smul : ∀ (c : ℂ) (p : R × R × R), toFun (triSmul c p) = c • toFun p
  mul : ∀ (p : R × R × R) (g : SL(2,ℤ)),
    toFun (triMulOf p g) = toFun p * MonoidAlgebra.of ℂ (SL(2,ℤ)) g
  sum : ∀ {J : Type} (s : Finset J) (g : J → R × R × R), toFun (triSum s g) = ∑ i ∈ s, toFun (g i)

/-- The first projection. -/
def Comp.fst : Comp where
  toFun := Prod.fst
  add := fun p q => rfl
  smul := fun c p => rfl
  mul := fun p g => rfl
  sum := fun s g => rfl

/-- The second projection. -/
def Comp.snd : Comp where
  toFun := fun p => p.2.1
  add := fun p q => rfl
  smul := fun c p => rfl
  mul := fun p g => rfl
  sum := fun s g => rfl

/-- The third projection. -/
def Comp.thd : Comp where
  toFun := fun p => p.2.2
  add := fun p q => rfl
  smul := fun c p => rfl
  mul := fun p g => rfl
  sum := fun s g => rfl

lemma tri_ext {p q : R × R × R} (h1 : Comp.fst.toFun p = Comp.fst.toFun q)
    (h2 : Comp.snd.toFun p = Comp.snd.toFun q) (h3 : Comp.thd.toFun p = Comp.thd.toFun q) :
    p = q := by
  obtain ⟨a, b, c⟩ := p
  obtain ⟨a', b', c'⟩ := q
  have e1 : a = a' := h1
  have e2 : b = b' := h2
  have e3 : c = c' := h3
  subst e1 e2 e3
  rfl

/-! ## The flat carries of `T^n` -/

/-- The carries of `T^n`, `n ≥ 0`, given by the flat sum
`∑_{m < n} ∑_j σ(T^{n-1-m})_{ij} • (carryAtomT j · T^m)`. -/
noncomputable def carryTpow (n : ℕ) (i : Fin 6) : R × R × R :=
  triSum (Finset.univ : Finset (Fin n)) (fun m =>
    triSum (Finset.univ : Finset (Fin 6)) (fun j =>
      triSmul ((Work.Modular.sigmaT ^ (n - 1 - (m : ℕ))) i j)
        (triMulOf (carryAtomT j) (ModularGroup.T ^ (m : ℕ)))))

/-- The `m = 0` term of `carryTpow`. -/
noncomputable def tpowHead (n : ℕ) (i : Fin 6) : R × R × R :=
  triSum (Finset.univ : Finset (Fin 6))
    (fun j => triSmul ((Work.Modular.sigmaT ^ n) i j) (carryAtomT j))

/-- The recursion step of `carryTpow`, transported by a component map. -/
lemma carryTpow_succ_comp (cc : Comp) (n : ℕ) (i : Fin 6) :
    cc.toFun (carryTpow (n + 1) i)
      = cc.toFun (triAdd (tpowHead n i) (triMulOf (carryTpow n i) ModularGroup.T)) := by
  classical
  have hL : carryTpow (n + 1) i = triSum (Finset.univ : Finset (Fin (n + 1))) (fun m =>
      triSum (Finset.univ : Finset (Fin 6)) (fun j =>
        triSmul ((Work.Modular.sigmaT ^ (n + 1 - 1 - (m : ℕ))) i j)
          (triMulOf (carryAtomT j) (ModularGroup.T ^ (m : ℕ))))) := rfl
  rw [hL, cc.sum, Fin.sum_univ_succ, cc.add]
  have hhead : cc.toFun (triSum (Finset.univ : Finset (Fin 6)) (fun j =>
        triSmul ((Work.Modular.sigmaT ^ (n + 1 - 1 - ((0 : Fin (n + 1)) : ℕ))) i j)
          (triMulOf (carryAtomT j) (ModularGroup.T ^ ((0 : Fin (n + 1)) : ℕ)))))
      = cc.toFun (tpowHead n i) := by
    rw [show tpowHead n i = triSum (Finset.univ : Finset (Fin 6))
        (fun j => triSmul ((Work.Modular.sigmaT ^ n) i j) (carryAtomT j)) from rfl]
    simp only [cc.sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hexp : n + 1 - 1 - ((0 : Fin (n + 1)) : ℕ) = n := by
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel]
    rw [hexp, cc.smul, cc.mul, cc.smul]
    rw [show (ModularGroup.T : SL(2,ℤ)) ^ ((0 : Fin (n + 1)) : ℕ) = 1 from by
      rw [show ((0 : Fin (n + 1)) : ℕ) = 0 from Fin.val_zero _, pow_zero], map_one, mul_one]
  have htail : (∑ m ∈ (Finset.univ : Finset (Fin n)),
        cc.toFun (triSum (Finset.univ : Finset (Fin 6)) (fun j =>
          triSmul ((Work.Modular.sigmaT ^ (n + 1 - 1 - ((Fin.succ m : Fin (n + 1)) : ℕ))) i j)
            (triMulOf (carryAtomT j) (ModularGroup.T ^ ((Fin.succ m : Fin (n + 1)) : ℕ))))))
      = cc.toFun (triMulOf (carryTpow n i) ModularGroup.T) := by
    rw [cc.mul]
    rw [show carryTpow n i = triSum (Finset.univ : Finset (Fin n)) (fun m =>
        triSum (Finset.univ : Finset (Fin 6)) (fun j =>
          triSmul ((Work.Modular.sigmaT ^ (n - 1 - (m : ℕ))) i j)
            (triMulOf (carryAtomT j) (ModularGroup.T ^ (m : ℕ))))) from rfl]
    simp only [cc.sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cc.smul, cc.mul, cc.smul, cc.mul]
    have hexp : n + 1 - 1 - ((Fin.succ m : Fin (n + 1)) : ℕ) = n - 1 - (m : ℕ) := by
      simp only [Fin.val_succ]; omega
    rw [hexp]
    have hg : (ModularGroup.T : SL(2,ℤ)) ^ (((Fin.succ m : Fin (n + 1)) : ℕ))
        = ModularGroup.T ^ (m : ℕ) * ModularGroup.T := by
      rw [Fin.val_succ, pow_succ]
    rw [hg, map_mul, smul_mul_assoc, mul_assoc]
  rw [← hhead, ← htail]

lemma carryTpow_succ (n : ℕ) (i : Fin 6) :
    carryTpow (n + 1) i = triAdd (tpowHead n i) (triMulOf (carryTpow n i) ModularGroup.T) := by
  have h1 := carryTpow_succ_comp Comp.fst n i
  have h2 := carryTpow_succ_comp Comp.snd n i
  have h3 := carryTpow_succ_comp Comp.thd n i
  exact tri_ext h1 h2 h3


/-! ## The defining equation for `carryTpow` -/

theorem carryTpow_spec (n : ℕ) : ∀ i : Fin 6,
    carryComb (carryTpow n i).1 (carryTpow n i).2.1 (carryTpow n i).2.2
      = Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ n)) i := by
  induction n with
  | zero =>
    intro i
    have h0 : carryTpow 0 i = ((0, 0, 0) : R × R × R) := by
      refine tri_ext ?_ ?_ ?_ <;> simp [carryTpow, triSum]
    rw [h0, show (ModularGroup.T : SL(2,ℤ)) ^ (0 : ℕ) = 1 from pow_zero _,
      show MonoidAlgebra.of ℂ (SL(2,ℤ)) (1 : SL(2,ℤ)) = 1 from map_one _,
      Work.Residues.rowDiff_one]
    simp [carryComb]
  | succ n ih =>
    intro i
    rw [carryTpow_succ, carryComb_triAdd]
    have hhead : carryComb (tpowHead n i).1 (tpowHead n i).2.1 (tpowHead n i).2.2
        = ∑ j : Fin 6, ((Work.Modular.sigmaT ^ n) i j)
            • carryComb (carryAtomT j).1 (carryAtomT j).2.1 (carryAtomT j).2.2 := by
      rw [show tpowHead n i = triSum (Finset.univ : Finset (Fin 6))
          (fun j => triSmul ((Work.Modular.sigmaT ^ n) i j) (carryAtomT j)) from rfl]
      simp only [triSum_fst, triSum_snd, triSum_thd]
      rw [carryComb_triSum]
      exact Finset.sum_congr rfl fun j _ => carryComb_triSmul _ _
    rw [hhead, carryComb_triMulOf]
    rw [show (∑ j : Fin 6, ((Work.Modular.sigmaT ^ n) i j)
          • carryComb (carryAtomT j).1 (carryAtomT j).2.1 (carryAtomT j).2.2)
        = ∑ j : Fin 6, ((Work.Modular.sigmaT ^ n) i j)
          • Work.Residues.rowDiff (MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T)) j from
      Finset.sum_congr rfl fun j _ => by rw [carryAtomT_spec j]]
    rw [ih i]
    rw [show ((Work.Modular.sigmaT ^ n) : Matrix (Fin 6) (Fin 6) ℂ)
        = Work.Residues.sigmaR (MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ n)) from
      (sigmaR_of_T_pow n).symm]
    rw [← Work.Residues.rowDiff_mul]
    rw [show MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ n)
          * MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T)
        = MonoidAlgebra.of ℂ (SL(2,ℤ)) (ModularGroup.T ^ (n + 1)) from by
      rw [← map_mul, ← pow_succ]]

/-! ## The bounds for `carryTpow` -/

lemma Frob_T_pow_nat_le (m : ℕ) : Frob (ModularGroup.T ^ m) ≤ (m : ℝ) + 2 := by
  rw [show (ModularGroup.T : SL(2,ℤ)) ^ m = ModularGroup.T ^ ((m : ℤ)) from
      (zpow_natCast _ _).symm, Frob_T_zpow]
  simp only [Int.cast_natCast]
  have h : ((m : ℝ)) ^ 2 + 2 ≤ (((m : ℝ) + 2)) ^ 2 := by nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m]
  calc Real.sqrt (((m : ℝ)) ^ 2 + 2) ≤ Real.sqrt ((((m : ℝ) + 2)) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = (m : ℝ) + 2 := Real.sqrt_sq (by positivity)

theorem carryTpow_bound (n : ℕ) (i : Fin 6) :
    CB (carryTpow n i) (60 * (1 + (n : ℝ)) ^ 3) (300 * (1 + (n : ℝ))) := by
  classical
  have hF : ∀ m ∈ (Finset.univ : Finset (Fin n)),
      CB (triSum (Finset.univ : Finset (Fin 6)) (fun j =>
          triSmul ((Work.Modular.sigmaT ^ (n - 1 - (m : ℕ))) i j)
            (triMulOf (carryAtomT j) (ModularGroup.T ^ (m : ℕ)))))
        (6 * (10 * (1 + (n : ℝ)) ^ 2)) (100 * ((n : ℝ) + 2)) := by
    intro m _
    refine CB_triSum (Finset.univ : Finset (Fin 6)) _
      (Cb := 10 * (1 + (n : ℝ)) ^ 2) (K := 100 * ((n : ℝ) + 2)) ?_
    intro j _
    refine CB_mono (CB_triSmul ((Work.Modular.sigmaT ^ (n - 1 - (m : ℕ))) i j)
      (CB_triMulOf (ModularGroup.T ^ (m : ℕ)) (carryAtomT_bound j))) ?_ ?_
    · have h1 := sigmaT_pow_entry_norm (n - 1 - (m : ℕ)) i j
      have h2 : ((n - 1 - (m : ℕ) : ℕ) : ℝ) ≤ (n : ℝ) := by
        have : n - 1 - (m : ℕ) ≤ n := by omega
        exact_mod_cast this
      calc ‖((Work.Modular.sigmaT ^ (n - 1 - (m : ℕ))) i j)‖ * 1
          ≤ 10 * (1 + (((n - 1 - (m : ℕ) : ℕ) : ℝ))) ^ 2 := by rw [mul_one]; exact h1
        _ ≤ 10 * (1 + (n : ℝ)) ^ 2 := by
            have hbase : (1 + (((n - 1 - (m : ℕ) : ℕ) : ℝ))) ≤ 1 + (n : ℝ) := by linarith
            have hnn : (0 : ℝ) ≤ 1 + (((n - 1 - (m : ℕ) : ℕ) : ℝ)) := by positivity
            have hpow : (1 + (((n - 1 - (m : ℕ) : ℕ) : ℝ))) ^ 2 ≤ (1 + (n : ℝ)) ^ 2 :=
              pow_le_pow_left₀ hnn hbase 2
            exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    · have h3 : Frob (ModularGroup.T ^ (m : ℕ)) ≤ (n : ℝ) + 2 := by
        refine le_trans (Frob_T_pow_nat_le (m : ℕ)) ?_
        have : ((m : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt m.isLt
        linarith
      calc 100 * Frob (ModularGroup.T ^ (m : ℕ)) ≤ 100 * ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 100 * ((n : ℝ) + 2) := rfl
  rw [show carryTpow n i = triSum (Finset.univ : Finset (Fin n)) (fun m =>
      triSum (Finset.univ : Finset (Fin 6)) (fun j =>
        triSmul ((Work.Modular.sigmaT ^ (n - 1 - (m : ℕ))) i j)
          (triMulOf (carryAtomT j) (ModularGroup.T ^ (m : ℕ))))) from rfl]
  refine CB_mono (CB_triSum (Finset.univ : Finset (Fin n)) _
    (Cb := 6 * (10 * (1 + (n : ℝ)) ^ 2)) (K := 100 * ((n : ℝ) + 2)) hF) ?_ ?_
  · rw [Finset.card_univ, Fintype.card_fin]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg (1 + (n : ℝ)), hn]
  · linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

end Work.Asymptotics
