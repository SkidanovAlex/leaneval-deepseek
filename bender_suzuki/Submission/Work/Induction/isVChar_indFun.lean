import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.Basic
import Submission.Work.Induction.isChar_indFun
import Submission.Work.CharCore.isVChar_iff_exists_int_coeffs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- **Induction of a virtual character is a virtual character**.  Proof: `hφ` gives
-- `φ = ∑_{θ ∈ Irr H} (c θ : ℂ) • θ` with `c : ↥(Irr H) → ℤ`
-- (`Work.CharCore.isVChar_iff_exists_int_coeffs`); `indFun` is additive and ℂ-linear
-- (`Work.Induction.indFun_sum`, `Work.Induction.indFun_smul`), and sends each irreducible
-- character of `H` to a character of `G` (`Work.Induction.isChar_indFun`), hence to a virtual
-- character; integral linear combinations of virtual characters are virtual
-- (`Work.CharCore.IsVChar.zsmul`, `Work.CharCore.IsVChar.sum`).
theorem isVChar_indFun {G : Type*} [Group G] [Fintype G] {H : Subgroup G} {φ : H → ℂ}
    (hφ : Work.CharCore.IsVChar φ) : Work.CharCore.IsVChar (Work.Induction.indFun H φ) := by
  classical
  -- `hφ` writes `φ` as an integral combination of the irreducible characters of `H`.
  obtain ⟨c, hc⟩ := (Work.CharCore.isVChar_iff_exists_int_coeffs (G := H)).mp hφ
  -- `indFun` is additive and ℂ-linear, so it distributes over the integral combination.
  rw [hc, indFun_sum]
  refine Work.CharCore.IsVChar.sum (fun θ _ => ?_)
  rw [indFun_smul]
  -- each `indFun H θ` with `θ ∈ Irr H` is a character of `G`, hence a virtual character,
  -- and integral multiples of virtual characters are virtual.
  simpa only [Int.cast_smul_eq_zsmul] using
    Work.CharCore.IsVChar.zsmul
      (Work.CharCore.IsChar.toVChar (isChar_indFun_irr θ.2)) (c θ)

end Work.Induction
