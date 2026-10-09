/-
Copyright (c) 2025. All rights reserved.

# The difference of two lifts is a `1`-cocycle

For an embedding problem with abelian kernel in the abstract setting `Work.Properness.Setup`
(`H`, `E`, `Q = E/A`, `π : E ↠ Q`, `ρ : H ↠ Q`, `A = ker π` abelian), the difference of two
lifts (`solutions`)

`c(h) = ψ h * (ψ₀ h)⁻¹ ∈ A`   (`Setup.cocycleOfLiftFun ψ₀ ψ`)

is a `1`-cocycle for the canonical conjugation action of `H` on the kernel `A`:
`c (g * h) = g • c h + c g`.  This is the formal content of the statement that the set of lifts is
a torsor under `Z¹(H, A)` (Proposition 11 of Schmidt–Wingberg, arXiv:math/9809211).

## Proof

Write `x_h = ψ h * (ψ₀ h)⁻¹ ∈ A`.  The pointwise identity
`x_{g h} = (ψ g) x_h (ψ g)⁻¹ * x_g` holds in `E` (`group`), i.e.

`x_{g h} = conjKernelMul π (ψ g) x_h * x_g`.

The canonical action of `g` on `A = ker π` is conjugation by `normSection (ρ g)`, and the two
conjugating elements `ψ g` and `normSection (ρ g)` have the same image under `π`, hence differ by
an element of the kernel; conjugation by an element of the (abelian) kernel is trivial, so the two
conjugations agree on `A`.  Combining the two identities gives the cocycle condition.

## Main declarations

* the private auxiliary lemma `conjKernelMul_congr_of_map_eq` — conjugation inside `ker π` only
  depends on the image under `π`;
* `Work.Properness.cocycleOfLiftFun_mem_Z1` — the difference of two lifts is a `1`-cocycle.
-/
import Mathlib
import Submission.Work.Properness.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- `autoImplicit` is needed for the universe binder `{u v w : Universe}` of the statement below,
-- exactly as in the sibling files of this directory.
set_option autoImplicit true

universe u v w

namespace Work.Properness

open Work.AbsoluteGalois
open scoped Classical

/-- **Conjugation inside the kernel of `π` depends only on the image under `π`** (when the kernel
is abelian): if `π x = π y` then `conjKernelMul π x a = conjKernelMul π y a` for every `a ∈ ker π`.

Indeed `x = y · t` with `t = y⁻¹ x ∈ ker π`, and conjugation by `t ∈ ker π` is trivial because the
kernel is abelian. -/
private theorem conjKernelMul_congr_of_map_eq {G Q : Type*} [Group G] [Group Q] (π : G →* Q)
    (hcomm : ∀ a b : π.ker, a * b = b * a) {x y : G} (hxy : π x = π y) (a : π.ker) :
    conjKernelMul π x a = conjKernelMul π y a := by
  have ht : y⁻¹ * x ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hxy' : x = y * (⟨y⁻¹ * x, ht⟩ : π.ker) := by
    rw [Subtype.coe_mk]; group
  rw [hxy', conjKernelMul_mul_eq, conjKernelMul_of_mem_ker π hcomm]

theorem cocycleOfLiftFun_mem_Z1 {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} (ψ₀ ψ : S.Lift) : S.cocycleOfLiftFun ψ₀ ψ ∈ Work.GroupCohomology.Z1 S.H (Additive S.A) := by
  rw [Work.GroupCohomology.mem_Z1_iff]
  intro g h
  -- the canonical action of `g` is conjugation by `normSection (ρ g)`, which agrees on `A` with
  -- conjugation by `ψ g` (both map to `ρ g` under `π`)
  have hsmul : g • S.cocycleOfLiftFun ψ₀ ψ h
      = Additive.ofMul
          (conjKernelMul S.π (ψ.1 g) (S.cocycleOfLiftFun ψ₀ ψ h).toMul) := by
    rw [show g • S.cocycleOfLiftFun ψ₀ ψ h
          = Additive.ofMul (conjKernelMul S.π (S.normSection (S.ρ g))
              (S.cocycleOfLiftFun ψ₀ ψ h).toMul) from rfl]
    congr 1
    exact conjKernelMul_congr_of_map_eq S.π S.ker_comm
      (by rw [S.normSection_spec, ← MonoidHom.comp_apply, ψ.2]) _
  rw [hsmul]
  -- the pointwise identity `x_{g h} = (ψ g) x_h (ψ g)⁻¹ · x_g` in `E`
  refine Additive.toMul.injective ?_
  rw [toMul_add, toMul_ofMul]
  refine Subtype.ext ?_
  simp only [Setup.cocycleOfLiftFun, toMul_ofMul, Subgroup.coe_mul, Subgroup.coe_mk,
    conjKernelMul, map_mul]
  group

end Work.Properness
