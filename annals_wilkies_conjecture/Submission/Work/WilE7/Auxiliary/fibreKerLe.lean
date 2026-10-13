import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic

namespace Work.WilE7.Aux

theorem fibreKerLe {p q : ℕ} {j j' r r' : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (c' : WilkiesDesign.E.EAChain (p + q) r') (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r)
    (h' : Fin j' → WilkiesDesign.E.EAPoly (p + q) r') (z : Fin (p + q) → ℝ)
    (hrow : ∀ a : Fin j, ∃ lam : Fin j' → ℝ, ∀ l : Fin q,
        WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z
      = ∑ b, lam b * WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z) :
    ∀ v : Fin q → ℝ,
      (∀ b, ∑ l, WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z * v l = 0) →
      (∀ a, ∑ l, WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z * v l = 0) := by
  intro v hv a
  obtain ⟨lam, hlam⟩ := hrow a
  calc ∑ l, WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z * v l
      = ∑ l, (∑ b, lam b * WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z) * v l := by
          exact Finset.sum_congr rfl (fun l _ => by rw [hlam l])
    _ = ∑ l, ∑ b, (lam b * WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z) * v l := by
          exact Finset.sum_congr rfl (fun l _ => by rw [Finset.sum_mul])
    _ = ∑ b, ∑ l, (lam b * WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z) * v l :=
          Finset.sum_comm
    _ = ∑ b, lam b * ∑ l, WilkiesDesign.E.eaEval c' (WilkiesDesign.E.eaD c' (Work.WilE5.yDir p l) (h' b)) z * v l := by
          refine Finset.sum_congr rfl (fun b _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun l _ => by ring)
    _ = 0 := by
          refine Finset.sum_eq_zero (fun b _ => ?_)
          rw [hv b, mul_zero]

end Work.WilE7.Aux
