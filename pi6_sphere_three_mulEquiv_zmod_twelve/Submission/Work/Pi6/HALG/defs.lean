import Mathlib
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# HALG: vocabulary for the mod-2 (Bockstein) analysis of the tower

The Bockstein analysis of the tower `Z → Y → E → S³` uses, for an abelian group `M` (written as an
object of `ModuleCat ℤ`, e.g. an integral homology group `H_n(−;ℤ)`), the two groups

* `twoKer M = M[2] = {x ∈ M | 2 x = 0}`, the 2-torsion subgroup of `M`, and
* `twoCok M = M/2M`, the quotient of `M` by the subgroup of twice-elements,

together with the short exact sequence `0 → M/2M → H_n(−;𝔽₂) → H_{n-1}(−;ℤ)[2] → 0` obtained from
the short exact sequence of chain complexes `0 → C_ℤ → C_ℤ → C_ℤ ⊗ 𝔽₂ → 0`
(`Work.Pi6.HALG.bockstein`).
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.HALG

noncomputable section

/-- Multiplication by `2` on an object of `ModuleCat ℤ`, as an endomorphism. -/
def mulTwo (M : ModuleCat ℤ) : M ⟶ M := (2 : ℤ) • 𝟙 M

/-- The 2-torsion subgroup `M[2]` of an abelian group `M` (an object of `ModuleCat ℤ`), as an
object of `ModuleCat ℤ`. -/
def twoKer (M : ModuleCat ℤ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (LinearMap.ker (mulTwo M).hom)

/-- The quotient `M/2M` of an abelian group `M` (an object of `ModuleCat ℤ`), as an object of
`ModuleCat ℤ`. -/
def twoCok (M : ModuleCat ℤ) : ModuleCat ℤ :=
  ModuleCat.of ℤ (↥M ⧸ LinearMap.range (mulTwo M).hom)

/-- **The mod-2 Bockstein short exact sequence** (the interface used by the area-HALG stages): for every
space `X` and degree `n` there are `ℤ`-linear maps
`H_{n+1}(X;ℤ)/2H_{n+1}(X;ℤ) → H_{n+1}(X;𝔽₂) → H_n(X;ℤ)[2]` making the sequence short exact. -/
def BocksteinTwo : Prop :=
  ∃ (i : ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        ↥(twoCok (HR ℤ X (n + 1))) →ₗ[ℤ] ↥(HR (ZMod 2) X (n + 1)))
    (p : ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        ↥(HR (ZMod 2) X (n + 1)) →ₗ[ℤ] ↥(twoKer (HR ℤ X n))),
    ∀ (X : Type) [TopologicalSpace X] (n : ℕ),
      Function.Injective (i X n) ∧ Function.Exact (i X n) (p X n) ∧ Function.Surjective (p X n)

end

end Work.Pi6.HALG
