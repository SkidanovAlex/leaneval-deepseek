import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

namespace Commons.Analysis.Walsh
open Finset BigOperators
theorem chi_symmDiff (n : ℕ) (S T : Finset (Fin n)) (x : Fin n → ZMod 2) :
    (∏ i ∈ S, ZMod.stdAddChar (x i)) * (∏ i ∈ T, ZMod.stdAddChar (x i)) =
      ∏ i ∈ (S \ T) ∪ (T \ S), ZMod.stdAddChar (x i) := by
  -- Each character value on `ZMod 2` is its own inverse.
  have hf : ∀ i, ZMod.stdAddChar (x i) * ZMod.stdAddChar (x i) = 1 := fun i => by
    have h : x i + x i = 0 := CharTwo.add_self_eq_zero (x i)
    rw [← AddChar.map_add_eq_mul, h, AddChar.map_zero_eq_one]
  -- Hence any subproduct is its own inverse.
  have hsq (A : Finset (Fin n)) :
      (∏ i ∈ A, ZMod.stdAddChar (x i)) * (∏ i ∈ A, ZMod.stdAddChar (x i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun i _ => hf i)
  have hdisj : Disjoint (S \ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_sdiff] at ha hb
    exact ha.2 hb.1
  -- Split each product over a set into the part outside the other set and the intersection.
  have hS : (∏ i ∈ S, ZMod.stdAddChar (x i)) =
      (∏ i ∈ S \ T, ZMod.stdAddChar (x i)) * (∏ i ∈ S ∩ T, ZMod.stdAddChar (x i)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter S T]
    rw [Finset.prod_union (Finset.disjoint_sdiff_inter S T)]
  have hT : (∏ i ∈ T, ZMod.stdAddChar (x i)) =
      (∏ i ∈ T \ S, ZMod.stdAddChar (x i)) * (∏ i ∈ S ∩ T, ZMod.stdAddChar (x i)) := by
    conv_lhs => rw [← Finset.sdiff_union_inter T S]
    rw [Finset.prod_union (Finset.disjoint_sdiff_inter T S), Finset.inter_comm]
  have hD : (∏ i ∈ (S \ T) ∪ (T \ S), ZMod.stdAddChar (x i)) =
      (∏ i ∈ S \ T, ZMod.stdAddChar (x i)) * (∏ i ∈ T \ S, ZMod.stdAddChar (x i)) :=
    Finset.prod_union hdisj
  rw [hS, hT, hD]
  -- The double occurrence of the common intersection cancels.
  rw [mul_mul_mul_comm, hsq, mul_one]

end Commons.Analysis.Walsh