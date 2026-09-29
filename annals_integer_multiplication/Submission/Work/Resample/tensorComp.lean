import Mathlib
import Submission.Work.Resample.defs
import Submission.Work.Resample.digitsSum
import Submission.Work.Resample.sumProdSwap

/-!
# Composition of tensors (Kronecker products) of matrix families

`Work.Resample.tensorComp` is the "matrix multiplication" law for the tensor (Kronecker
product) construction `Work.Resample.tensorLin ss ts f` of a family of matrices given by
their scalar entries `f i j k`:

the tensor of the entrywise products `i ↦ (∑ l, M i j l * N i l k)` is the composition of
the tensors of `M` and of `N`.

The proof is entrywise.  For fixed output index `J` and input index `K` one has to show

`∏ i, ∑ l, M i (dJ i) l * N i l (dK i) = ∑ J', ∏ i, M i (dJ i) (dJ' i) * N i (dJ' i) (dK i)`,

i.e. the mixed-radix "Fubini" identity `Work.Resample.digitsSum` (the map
`J' ↦ ((digits b J')ᵢ)ᵢ` is the standard bijection `Fin b.prod ≃ ∏ i, Fin (bᵢ)`), together
with a routine rearrangement of sums and products, `Work.Resample.sumProdSwap`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- A `List` product over a mapped range, written as a `Finset` product. -/
theorem listProd_range_map (f : ℕ → ℂ) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
    simp

/-- `digitProd` as a `Finset` product over the digit positions. -/
theorem digitProd_eq (ss ts : List ℕ) (f : ℕ → ℕ → ℕ → ℂ) (J K : ℕ) :
    digitProd ss ts f J K =
      ∏ i ∈ Finset.range ss.length, f i ((digits ts J).getD i 0) ((digits ss K).getD i 0) := by
  simp only [digitProd, listProd_range_map]

set_option linter.unusedVariables false in
theorem tensorComp (a b c : List ℕ) (hab : a.length = b.length) (hbc : b.length = c.length)
    (M N : ℕ → ℕ → ℕ → ℂ) (u : Fin a.prod → ℂ) :
    Work.Resample.tensorLin a c (fun i j k => ∑ l : Fin (b.getD i 0), M i j l * N i l k) u =
      Work.Resample.tensorLin b c M (Work.Resample.tensorLin a b N u) := by
  funext J
  simp only [Work.Resample.tensorLin_apply, Work.Resample.tensorFun, digitProd_eq]
  rw [hab]
  -- rearrange the right-hand side: swap the two sums and split the product of sums
  simp only [sumProdSwap]
  -- the inner sum over `Fin b.prod` is the mixed-radix Fubini identity
  have hkey : ∀ y : Fin a.prod,
      (∑ x : Fin b.prod, ∏ i ∈ Finset.range b.length,
          M i ((HvdH.digits c (J : ℕ)).getD i 0) ((HvdH.digits b (x : ℕ)).getD i 0)
            * N i ((HvdH.digits b (x : ℕ)).getD i 0) ((HvdH.digits a (y : ℕ)).getD i 0))
        = ∏ i ∈ Finset.range b.length, ∑ l : Fin (b.getD i 0),
            M i ((HvdH.digits c (J : ℕ)).getD i 0) (l : ℕ) * N i (l : ℕ) ((HvdH.digits a (y : ℕ)).getD i 0) :=
    fun y => digitsSum b (fun i (l : ℕ) =>
      M i ((HvdH.digits c (J : ℕ)).getD i 0) l * N i l ((HvdH.digits a (y : ℕ)).getD i 0))
  rw [Finset.sum_congr rfl (fun y _ => congrArg (fun z => z * u y) (hkey y))]

end Work.Resample
