import Mathlib
import Submission.Work.Tate.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The connecting map `Ĥ⁻¹(G, C) → Ĥ⁰(G, A)` sends the zero class to the zero class.

Concretely, a lift of `0 ∈ C` lies in the kernel of `g`, hence is the image under `f` of some
`a : A`; then `norm G B (sec 0) = f (norm G A a)`, so `preimage 0 = norm G A a` is a norm and
therefore dies in `Ĥ⁰(G, A) = A^G / N(A)`. -/
theorem deltaLiftFun_zero {G : Type*} {A : Type*} {B : Type*} {C : Type*} [Group G]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A]
    [DistribMulAction G B] [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) :
    S.deltaLiftFun 0 = 0 := by
  rw [Work.Tate.deltaLiftFun_apply, Work.Tate.H0π_eq_zero_iff]
  have hsec : S.sec (0 : (Work.Tate.norm G C).ker) ∈ S.g.ker := by
    rw [AddMonoidHom.mem_ker]
    exact S.sec_spec 0
  obtain ⟨a, ha⟩ := S.exists_of_g_eq_zero hsec
  -- the norm of a lift of `0` is `f (norm G A a)`, so `preimage 0 = norm G A a`
  refine ⟨a, Subtype.ext ?_⟩
  show Work.Tate.norm G A a = S.preimage 0
  apply S.f_injective
  rw [S.f_preimage, ← ha, Work.Tate.norm_map S.f S.f_equiv]

end Work.Tate
