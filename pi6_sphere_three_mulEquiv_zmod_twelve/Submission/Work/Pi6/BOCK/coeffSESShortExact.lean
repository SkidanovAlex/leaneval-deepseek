import Mathlib
import Submission.Work.Pi6.EMZ.BocksteinCore
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# AREA BOCK — short exactness of the coefficient sequence `0 → ℤ --·p--> ℤ → ℤ/p → 0`

The coefficient short complex `Work.Pi6.EMZ.coeffSES p` of the mod-`p` Bockstein long exact
sequence is short exact for every prime `p`: multiplication by `p` on `ℤ` is injective, reduction
`ℤ ↠ ℤ/p` is surjective, and its kernel is exactly the range of multiplication by `p` (the
divisibility criterion `p ∣ x ↔ (x : ℤ/p) = 0`).

The objects `X₁ = X₂ = zZ = ℤ` and `X₃ = Mp p` of `coeffSES p` are definitionally `ℤ` and `ℤ/p`,
so the linear maps can be read off as the maps `x ↦ p * x` and `x ↦ (x : ℤ/p)` by function
extensionality; the proofs are then the elementary `ℤ`-statements.
-/

namespace Work.Pi6.BOCK

open CategoryTheory CategoryTheory.Limits HomologicalComplex

theorem coeffSESShortExact (p : ℕ) (hp : p.Prime) :
    (Work.Pi6.EMZ.coeffSES p).ShortExact := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hf : ⇑(ConcreteCategory.hom (Work.Pi6.EMZ.coeffSES p).f) =
      fun x : ℤ => (p : ℤ) * x := by
    funext x
    exact Work.Pi6.EMZ.mulP_hom_apply p x
  have hg : ⇑(ConcreteCategory.hom (Work.Pi6.EMZ.coeffSES p).g) =
      fun y : ℤ => (y : ZMod p) := by
    funext y
    exact Work.Pi6.EMZ.redP_hom_apply p y
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, hf, hg]
    show ∀ y : ℤ, ((y : ZMod p) = 0) ↔ ∃ x : ℤ, (p : ℤ) * x = y
    intro y
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro h
      obtain ⟨x, hx⟩ := dvd_def.mp h
      exact ⟨x, hx.symm⟩
    · rintro ⟨x, hx⟩
      exact dvd_def.mpr ⟨x, hx.symm⟩
  · rw [ModuleCat.mono_iff_injective]
    change Function.Injective (fun x : ℤ => (p : ℤ) * x)
    intro x y h
    exact mul_left_cancel₀ hpz h
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨x, hx⟩ := ZMod.intCast_surjective (n := p) y
    exact ⟨x, by rw [← hx]; exact Work.Pi6.EMZ.redP_hom_apply p x⟩

end Work.Pi6.BOCK
