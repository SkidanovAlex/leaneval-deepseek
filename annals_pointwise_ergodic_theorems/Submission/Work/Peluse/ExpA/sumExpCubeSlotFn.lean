import Mathlib
import Submission.Work.Peluse.ExpA.expCubeSlotIdentity

namespace Work.Peluse.ExpA

open scoped BigOperators

/-! ## Summation bookkeeping for finitely supported functions -/

/-- Outside `symIcc N` the absolute value of an integer exceeds `N`. -/
private lemma lt_natAbs_of_not_mem_symIcc {N : ℕ} {x : ℤ} (hx : x ∉ Work.Peluse.symIcc N) :
    N < x.natAbs := by
  have hx' : ¬ (( -(N : ℤ) ≤ x) ∧ (x ≤ (N : ℤ))) := by
    intro hcon
    exact hx (by rw [Work.Peluse.symIcc]; exact Finset.mem_Icc.mpr hcon)
  have hDx : ((N : ℕ) : ℤ) < |x| := by
    rcases not_and_or.mp hx' with h | h
    · have h2 : ((N : ℕ) : ℤ) < -x := by have := not_le.mp h; linarith
      linarith [neg_le_abs x]
    · have hlt : (N : ℤ) < x := not_le.mp h
      linarith [le_abs_self x]
  have hcast := hDx
  rw [Int.abs_eq_natAbs] at hcast
  exact_mod_cast hcast

/-- Translating the summation variable over `ℤ` is harmless because addition by a constant is a
bijection of `ℤ`.  (No summability is needed -- `Equiv.tsum_eq` is unconditional.) -/
private lemma tsum_eq_tsum_sub (g : ℤ → ℂ) (d : ℤ) :
    (∑' x : ℤ, g x) = ∑' x : ℤ, g (x - d) := by
  have h := Equiv.tsum_eq (Equiv.addRight (-d)) g
  simp only [Equiv.coe_addRight] at h
  rw [← h]
  exact tsum_congr fun x => by simp only [sub_eq_add_neg]

/-! ## The main identity -/

/-- **The `a`-average of the cube terms is the multilinear average over the slots.**  Summing the
cube terms of `Holds.ExpPET` over the arithmetic-progression directions `c·a + b`, `a ∈ [M₂]`, and
translating each summation variable by the corresponding all-false corner produces the phase-free
factor `f x` times the sum over `a` of the product of the `2^s - 1` slot functions of `ExpA.Defs`.

The pointwise input is the public lemma `ExpA.expCubeSlotIdentity`; the only content here is the
transport of the translation of the summation variable (valid because `f` is finitely supported,
so every integrand below is finitely supported and hence summable) and the interchange of the
finite `a`-sum with the `tsum` over `x`. -/
theorem sumExpCubeSlotFn {s : ℕ} (c : ℤ) (b n n' : Fin s → ℤ) (f : ℤ → ℂ)
    (M₂ : ℕ) (hfin : Work.Peluse.FinSuppZ f) :
    (∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
        Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i) n n' f x)
      = ∑' x : ℤ, f x * ∑ a ∈ Finset.Icc 1 M₂,
          ∏ i : Fin (2 ^ s - 1),
            Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
              (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * (a : ℤ)) := by
  rcases hfin with ⟨N, hN⟩
  -- For each `a`, translate the summation variable by the all-false corner and expand.
  have hstep : ∀ a ∈ Finset.Icc 1 M₂,
      (∑' x : ℤ, Work.Peluse.Holds.ExpPET.expCube
          (fun i : Fin s => c * (a : ℤ) + b i) n n' f x)
      = ∑' x : ℤ, f x * ∏ i : Fin (2 ^ s - 1),
          Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
            (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * (a : ℤ)) := by
    intro a _
    exact (tsum_eq_tsum_sub
        (fun x => Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i) n n' f x)
        (∑ i : Fin s, n' i * (c * (a : ℤ) + b i))).trans
      (tsum_congr fun x => expCubeSlotIdentity c b n n' f (a : ℤ) x)
  -- The integrands are supported in the finite window `symIcc N`, hence summable.
  have hsumm : ∀ a ∈ Finset.Icc 1 M₂,
      Summable (fun x : ℤ => f x * ∏ i : Fin (2 ^ s - 1),
          Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
            (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * (a : ℤ))) := by
    intro a _
    refine summable_of_ne_finset_zero (s := Work.Peluse.symIcc N) (fun x hx => ?_)
    rw [hN x (lt_natAbs_of_not_mem_symIcc hx), zero_mul]
  calc (∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ,
          Work.Peluse.Holds.ExpPET.expCube (fun i : Fin s => c * (a : ℤ) + b i) n n' f x)
      = ∑ a ∈ Finset.Icc 1 M₂, ∑' x : ℤ, f x * ∏ i : Fin (2 ^ s - 1),
          Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
            (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * (a : ℤ)) :=
        Finset.sum_congr rfl hstep
    _ = ∑' x : ℤ, ∑ a ∈ Finset.Icc 1 M₂, f x * ∏ i : Fin (2 ^ s - 1),
          Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
            (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * (a : ℤ)) :=
        (Summable.tsum_finsetSum hsumm).symm
    _ = ∑' x : ℤ, f x * ∑ a ∈ Finset.Icc 1 M₂, ∏ i : Fin (2 ^ s - 1),
          Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
            (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * (a : ℤ)) :=
        tsum_congr fun x => (Finset.mul_sum (Finset.Icc 1 M₂)
          (fun a => ∏ i : Fin (2 ^ s - 1),
            Work.Peluse.ExpA.slotFn s b (fun j => n j - n' j) f i.succ
              (x + Work.Peluse.ExpA.cSlot s c (fun j => n j - n' j) i.succ * (a : ℤ))) (f x)).symm

end Work.Peluse.ExpA
