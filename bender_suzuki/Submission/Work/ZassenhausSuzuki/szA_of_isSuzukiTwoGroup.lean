import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem szA_of_isSuzukiTwoGroup (hHig : Submission.Blueprint.HigmanProp)
    {P : Type} [Group P] [Finite P] (hP : Submission.Blueprint.IsSuzukiTwoGroup P)
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 2) :
    ∃ (n : ℕ) (θ : GaloisField 2 n ≃+* GaloisField 2 n),
      θ ≠ 1 ∧ Odd (orderOf θ) ∧ Nat.card (Subgroup.center P) = 2 ^ n ∧
      Nonempty (P ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 n) θ) := by
  -- Higman's classification: for the order-`q²` type the group is `A(n,θ) = SzA (GF(2ⁿ)) θ`,
  -- exhibited by a bijection `e : P ≃ GF(2ⁿ) × GF(2ⁿ)` whose transported multiplication is
  -- exactly the law of `SzA`, namely `(a,b)*(c,d) = (a+c, b+d+a·θ c)`.
  have h := hHig P hP
  obtain ⟨n, e, θ, hc, hne, hodd, hmul⟩ := h.2.2.2.2 hcard
  refine ⟨n, θ, hne, hodd, hc, ⟨?_⟩⟩
  -- `e` is a multiplicative equivalence once the target pair is read as an element of `SzA`.
  refine {
    toEquiv := {
      toFun := fun x => ⟨(e x).1, (e x).2⟩
      invFun := fun y => e.symm (y.a, y.b)
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
    map_mul' := fun x y => by
      apply Work.ZassenhausSuzuki.SzA.ext <;> simp [hmul] }

end Work.ZassenhausSuzuki
