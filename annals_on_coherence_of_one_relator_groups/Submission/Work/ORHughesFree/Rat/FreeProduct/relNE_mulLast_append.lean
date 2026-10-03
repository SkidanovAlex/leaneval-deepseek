import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NU
import Submission.Work.ORHughesFree.Rat.FreeProduct.shiftPad_append_right

namespace Work.ORHughesFree.Rat.FreeProduct

open Work.ORHughesFree

variable {U : Type} [Group U]

/-- `shiftPad` with the parameters `1, …, 1, u⁻¹` absorbs the trailing `u⁻¹` of `mulLast`:
the word `mulLast l u` is shifted back to `l`. -/
private theorem shiftPad_replicate_mulLast_self (u : U) (l : List (RatU U)) :
    shiftPad (List.replicate l.length (1 : U) ++ [u⁻¹]) (mulLast l u) = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil =>
      have hpar : (List.replicate ([x] : List (RatU U)).length (1 : U) ++ [u⁻¹])
          = [1, u⁻¹] := rfl
      have hml : mulLast ([x] : List (RatU U)) u = [actR u x] := rfl
      rw [hpar, hml]
      simp only [shiftPad_cons, shiftPad_nil, actR, RatU.ofGroup_one, inv_inv, mul_one]
      congr 1
      rw [← mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel, RatU.ofGroup_one, one_mul]
    | cons y ys =>
      have hrep : List.replicate (x :: y :: ys).length (1 : U)
          = 1 :: (1 :: List.replicate ys.length (1 : U)) := by
        conv_lhs => rw [List.length_cons, List.length_cons]
        rw [List.replicate_succ, List.replicate_succ]
      have htail : (1 : U) :: (List.replicate ys.length (1 : U) ++ [u⁻¹])
          = List.replicate (y :: ys).length (1 : U) ++ [u⁻¹] := by
        conv_rhs => rw [List.length_cons, List.replicate_succ]
        simp only [List.cons_append]
      rw [hrep]
      simp only [List.cons_append]
      rw [show mulLast (x :: y :: ys) u = x :: mulLast (y :: ys) u from rfl]
      rw [shiftPad_cons, htail, ih]
      simp

/-- `shiftPad` with the parameters `u⁻¹, 1, …, 1` computes `mulFirst u`: only the first letter
is conjugated, by `u⁻¹` on the right. -/
private theorem shiftPad_inv_cons_replicate_self (u : U) (l : List (RatU U)) :
    shiftPad (u⁻¹ :: List.replicate l.length (1 : U)) l = mulFirst u l := by
  cases l with
  | nil => simp [mulFirst]
  | cons y ys =>
    have hrep : List.replicate (y :: ys).length (1 : U)
        = 1 :: List.replicate ys.length (1 : U) := by
      conv_lhs => rw [List.length_cons]
      rw [List.replicate_succ]
    rw [hrep]
    simp only [shiftPad_cons, mulFirst_cons, actL, RatU.ofGroup_one, inv_one, one_mul]
    congr 1
    rw [show (1 : U) :: List.replicate ys.length (1 : U)
        = List.replicate (ys.length + 1) (1 : U) from
      (List.replicate_succ (n := ys.length) (a := (1 : U))).symm,
      shiftPad_replicate_one]

theorem relNE_mulLast_append {U : Type} [Group U] (L M : Work.ORHughesFree.Rat.FreeProduct.NEL (U := U)) (u : U) :
    Work.ORHughesFree.Rat.FreeProduct.relNE
      ⟨Work.ORHughesFree.Rat.FreeProduct.mulLast L.1 u ++ M.1,
        by intro h; exact M.2 (List.append_eq_nil_iff.mp h).2⟩
      ⟨L.1 ++ Work.ORHughesFree.Rat.FreeProduct.mulFirst u M.1,
        by intro h; exact L.2 (List.append_eq_nil_iff.mp h).1⟩ := by
  have hL : 0 < L.1.length := List.length_pos_iff.mpr L.2
  have hM : 0 < M.1.length := List.length_pos_iff.mpr M.2
  refine ⟨List.replicate (L.1.length - 1) (1 : U) ++ [u⁻¹]
      ++ List.replicate (M.1.length - 1) (1 : U), ?_, ?_⟩
  · show (List.replicate (L.1.length - 1) (1 : U) ++ [u⁻¹]
        ++ List.replicate (M.1.length - 1) (1 : U)).length + 1
      = (mulLast L.1 u ++ M.1).length
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    rw [mulLast_length]
    omega
  · have h1 : List.replicate L.1.length (1 : U)
        = 1 :: List.replicate (L.1.length - 1) (1 : U) := by
      conv_lhs => rw [show L.1.length = (L.1.length - 1) + 1 from by omega]
      rw [List.replicate_succ]
    have h2 : List.replicate M.1.length (1 : U)
        = List.replicate (M.1.length - 1) (1 : U) ++ [1] := by
      conv_lhs => rw [show M.1.length = (M.1.length - 1) + 1 from by omega]
      rw [List.replicate_succ']
    have hkey : (1 : U) :: ((List.replicate (L.1.length - 1) (1 : U) ++ [u⁻¹]
          ++ List.replicate (M.1.length - 1) (1 : U)) ++ [1])
        = List.replicate L.1.length (1 : U) ++ [u⁻¹] ++ List.replicate M.1.length (1 : U) := by
      conv_rhs => rw [h1, h2]
      simp only [List.cons_append, List.append_assoc]
    have hlen : (List.replicate L.1.length (1 : U) ++ [u⁻¹]).length
        = (mulLast L.1 u).length + 1 := by
      simp only [List.length_append, List.length_replicate, List.length_singleton]
      rw [mulLast_length]
    rw [hkey,
      shiftPad_append_split (List.replicate L.1.length (1 : U) ++ [u⁻¹])
        (List.replicate M.1.length (1 : U)) (mulLast L.1 u) M.1 hlen]
    rw [shiftPad_replicate_mulLast_self u L.1, List.getLastD_concat,
      shiftPad_inv_cons_replicate_self u M.1]

end Work.ORHughesFree.Rat.FreeProduct
