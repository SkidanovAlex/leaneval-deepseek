import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.isChar_resFun
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- **Restriction of a virtual character is a virtual character**
-- (`Work.CharCore.IsVChar φ` is `φ ∈ AddSubgroup.closure (Irr G)`, i.e. an integral combination
-- of irreducible characters).  Proof: `hφ` gives `φ = ∑_{χ ∈ Irr G} (c χ : ℂ) • χ` with
-- `c : ↥(Irr G) → ℤ` (`Work.CharCore.isVChar_iff_exists_int_coeffs`); `resFun` is additive and
-- ℂ-linear, and restricts each irreducible character to a character of `H`
-- (`Work.Induction.isChar_resFun`), hence to a virtual character; integral linear combinations
-- of virtual characters are virtual (`Work.CharCore.IsVChar.zsmul`, `Work.CharCore.IsVChar.sum`).
theorem isVChar_resFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} {φ : G → ℂ}
    (hφ : Work.CharCore.IsVChar φ) : Work.CharCore.IsVChar (Work.Induction.resFun H φ) := by
  classical
  -- The restriction of each irreducible character of `G` is a virtual character of `H`.
  have hχV : ∀ χ : G → ℂ, χ ∈ Work.CharCore.Irr G →
      Work.CharCore.IsVChar (resFun H χ) := by
    intro χ hχ
    exact Work.CharCore.IsChar.toVChar (isChar_resFun (Work.CharCore.IsChar.of_mem_Irr hχ))
  -- The set of `ψ` whose restriction is a virtual character is an additive subgroup of `G → ℂ`
  -- containing `Irr G`, hence contains the closure of `Irr G`.
  let T : AddSubgroup (G → ℂ) :=
    { carrier := {ψ | Work.CharCore.IsVChar (resFun H ψ)}
      zero_mem' := by
        change Work.CharCore.IsVChar (resFun H 0)
        rw [resFun_zero]
        exact Work.CharCore.IsVChar.zero
      add_mem' := by
        intro f g hf hg
        change Work.CharCore.IsVChar (resFun H (f + g))
        rw [resFun_add]
        exact Work.CharCore.IsVChar.add hf hg
      neg_mem' := by
        intro f hf
        change Work.CharCore.IsVChar (resFun H (-f))
        rw [resFun_neg]
        exact Work.CharCore.IsVChar.neg hf }
  have hle : AddSubgroup.closure ((Work.CharCore.Irr G : Finset (G → ℂ)) : Set (G → ℂ)) ≤ T := by
    rw [AddSubgroup.closure_le]
    intro χ hχ
    exact hχV χ hχ
  exact hle hφ

end Work.Induction
