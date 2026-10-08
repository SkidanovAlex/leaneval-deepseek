import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical
open scoped Pointwise

-- For a self-normalizing TI subgroup `H` and `1 ≠ h ∈ H`, every `x : G` with `x * h * x⁻¹ = h`
-- lies in `H`.  Indeed `x * h * x⁻¹ = h ∈ H` with `h ≠ 1` forces `x ∈ N_G(H)` (otherwise
-- `h ∈ H ⊓ (MulAut.conj x • H) = ⊥` by TI, i.e. `h = 1`), and `N_G(H) = H`.
-- Equivalently: `Subgroup.centralizer ({h} : Set G) ≤ H` for `1 ≠ h ∈ H`.
theorem mem_of_conj_eq_self_of_isTI {G : Type*} [Group G] (H : Subgroup G)
    (hTI : Work.Induction.IsTI H) (hN : Work.Induction.normalizer H = H) {h : H} (hh : h ≠ 1)
    {x : G} (hx : x * (h : G) * x⁻¹ = (h : G)) : x ∈ H := by
  rw [← hN]
  by_contra hxN
  have hmem : (h : G) ∈ H ⊓ (MulAut.conj x • H) := by
    refine ⟨h.2, ?_⟩
    rw [show (MulAut.conj x • H : Subgroup G) = H.map (MulAut.conj x).toMonoidHom from rfl]
    refine Subgroup.mem_map.mpr ⟨(h : G), h.2, ?_⟩
    change x * (h : G) * x⁻¹ = (h : G)
    exact hx
  rw [hTI x hxN] at hmem
  exact hh (Subtype.ext (by simpa using hmem))

end Work.Induction
