import Mathlib
import Submission.Work.ORHughesFree.Rat.FreeProduct.NUMonoid

namespace Work.ORHughesFree.Rat

theorem Xgen_actR_actL_mul {U : Type} [Group U] (v : U) (x y : Work.ORHughesFree.RatU U) :
    Work.ORHughesFree.Rat.FreeProduct.NU.Xgen (Work.ORHughesFree.Rat.FreeProduct.actR v x) *
        Work.ORHughesFree.Rat.FreeProduct.NU.Xgen (Work.ORHughesFree.Rat.FreeProduct.actL v⁻¹ y) =
      Work.ORHughesFree.Rat.FreeProduct.NU.Xgen x *
        Work.ORHughesFree.Rat.FreeProduct.NU.Xgen y := by
  rw [Work.ORHughesFree.Rat.FreeProduct.NU.Xgen_mul_Xgen,
    Work.ORHughesFree.Rat.FreeProduct.NU.Xgen_mul_Xgen]
  refine congrArg Sum.inr ?_
  refine (Quotient.sound ?_).symm
  refine ⟨[v], by simp, ?_⟩
  simp [Work.ORHughesFree.Rat.FreeProduct.shiftPad,
    Work.ORHughesFree.Rat.FreeProduct.actR, Work.ORHughesFree.Rat.FreeProduct.actL]

end Work.ORHughesFree.Rat
