import Mathlib
import Submission.Work.Resample.defs

/-!
# Tensor factorisation of the multidimensional DFT (`dftTensor`)

`dftMulti ts (-1)` (the normalised multidimensional DFT of `HvdH`) is the tensor
(Kronecker) product of the one-dimensional normalised DFT matrices `dftMat tᵢ`
along the mixed-radix axes of the flat lexicographic layout `HvdH.digits`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- Unfolding of the tensor product over the head of the index list. -/
lemma digitProd_cons (ts : List ℕ) (t : ℕ) (f : ℕ → ℕ → ℕ → ℂ) (J K : ℕ) :
    digitProd (t :: ts) (t :: ts) f J K =
      f 0 ((digits (t :: ts) J).getD 0 0) ((digits (t :: ts) K).getD 0 0) *
        digitProd ts ts (fun i => f (i+1)) (J % ts.prod) (K % ts.prod) := by
  simp only [digitProd, List.length_cons, List.range_succ_eq_map, List.map_cons, List.prod_cons]
  congr 1
  rw [List.map_map]
  congr 1

/-- Unbundled entry of the normalised DFT matrix, in the shape of the multidimensional
phase `(a·b)/n`. -/
lemma dE_apply' {n a b : ℕ} (ha : a < n) (hb : b < n) :
    dE n a b = (1/(n:ℂ)) * Complex.exp (((-1:ℤ):ℂ) * 2 * Real.pi * Complex.I *
      ((((a*b:ℕ):ℝ)/(n:ℝ) : ℝ):ℂ)) := by
  rw [dE, unb_apply (dftMat n) ha hb, dftMat]
  congr 2
  push_cast
  ring

/-- The tensor-product entry is the normalised exponential of the multidimensional phase. -/
lemma digitProd_dE_digits (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (J K : ℕ) :
    digitProd ts ts (fun i => dE (ts.getD i 0)) J K =
      (1 / (ts.prod : ℂ)) * Complex.exp (((-1 : ℤ) : ℂ) * 2 * Real.pi * Complex.I *
        (phase ts (digits ts J) (digits ts K) : ℂ)) := by
  induction ts generalizing J K with
  | nil => simp [digitProd, HvdH.digits, HvdH.phase]
  | cons t ts ih =>
    have ht : 0 < t := hpos t (by simp)
    have hpos' : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
    have hprod : (0:ℕ) < ts.prod := List.prod_pos hpos'
    rw [digitProd_cons]
    simp only [HvdH.digits, HvdH.phase, List.getD_cons_zero, List.getD_cons_succ,
      List.prod_cons]
    rw [ih hpos' (J % ts.prod) (K % ts.prod)]
    rw [dE_apply' (Nat.mod_lt _ ht) (Nat.mod_lt _ ht)]
    have hc : (↑(-1:ℤ) : ℂ) * 2 * ↑Real.pi * Complex.I *
        (((↑(J / ts.prod % t * (K / ts.prod % t)) / ↑t : ℝ) : ℂ) +
          (phase ts (digits ts (J % ts.prod)) (digits ts (K % ts.prod)) : ℂ))
        = (↑(-1:ℤ) : ℂ) * 2 * ↑Real.pi * Complex.I *
            (((↑(J / ts.prod % t * (K / ts.prod % t)) / ↑t : ℝ) : ℂ))
          + (↑(-1:ℤ) : ℂ) * 2 * ↑Real.pi * Complex.I *
            ((phase ts (digits ts (J % ts.prod)) (digits ts (K % ts.prod)) : ℂ)) := by ring
    have hconst : (1:ℂ)/↑t * (1/↑ts.prod) = 1/↑((t*ts.prod:ℕ):ℂ) := by
      rw [Nat.cast_mul]; field_simp
    rw [Complex.ofReal_add, hc, Complex.exp_add, ← hconst]
    ring

theorem dftTensor (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) (u : Fin ts.prod → ℂ) :
    HvdH.dftMulti ts (-1) u = Work.Resample.dftOp ts u := by
  funext j
  rw [Work.Resample.dftOp, Work.Resample.tensorLin_apply]
  simp only [HvdH.dftMulti, Work.Resample.tensorFun]
  rw [show (∑ K : Fin ts.prod, digitProd ts ts (fun i => dE (ts.getD i 0)) ↑j ↑K * u K)
        = ∑ K : Fin ts.prod, ((1/(ts.prod:ℂ)) * Complex.exp (((-1:ℤ):ℂ) * 2 * Real.pi *
            Complex.I * (phase ts (digits ts (↑j)) (digits ts (↑K)) : ℂ))) * u K from by
      apply Finset.sum_congr rfl
      intro K _
      rw [digitProd_dE_digits ts hpos (↑j) (↑K)]]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K _
  ring

end Work.Resample
