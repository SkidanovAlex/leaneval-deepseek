import Mathlib
import Submission.Work.CFTLib.fiveTerm_setup

/-!
# The transgression `candFun` is a `2`-cocycle

For a surjective homomorphism `π : G' →* G` with kernel `N = ker π` and an invariant character
`t : Hom(N, 𝔽_p)^{G'}` (model of `H¹(N,𝔽_p)^{G'}`), the transgression `2`-cochain

`candFun π hπ t (x, y) = - t (σ x * σ y * (σ (x*y))⁻¹)`

attached to a set-theoretic section `σ` of `π` is a `2`-cocycle with values in the trivial
`G`-module `𝔽_p`:

`candFun (x*y, z) + candFun (x, y) = candFun (y, z) + candFun (x, y*z)`.

The proof is the standard one: with `a(x,y) = σ x * σ y * (σ (x*y))⁻¹ ∈ N` the identity

`a(x,y) * a(x*y, z) = (σ x * a(y,z) * (σ x)⁻¹) * a(x, y*z)`

holds in `G'` (the "cocycle identity" of a section), and `t` is conjugation invariant.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

variable {p : ℕ} {G G' : Type} [Group G] [Group G']

/-- Conjugation of an element of `ker π` by an element of `G'`: `n ↦ g⁻¹ n g`.  The convention
`g⁻¹ n g` is chosen to match the conjugation action used in the definition of
`invCharSubmodule`. -/
def fiveTerm_conjKer (π : G' →* G) (g : G') (n : π.ker) : π.ker :=
  ⟨g⁻¹ * (n : G') * g, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp n.2]
    simp⟩

@[simp] lemma fiveTerm_conjKer_coe (π : G' →* G) (g : G') (n : π.ker) :
    (fiveTerm_conjKer π g n : G') = g⁻¹ * (n : G') * g := rfl

/-- An invariant character of `N = ker π` is invariant under conjugation by any element of `G'`. -/
lemma fiveTerm_invChar_conjKer (π : G' →* G) (t : invCharSubmodule p π.ker) (g : G')
    (n : π.ker) :
    t.1 (Additive.ofMul (fiveTerm_conjKer π g n)) = t.1 (Additive.ofMul n) := by
  have h := t.2 g n
  convert h using 1
  · rfl

/-- **The cocycle identity of the section `σ`**, in the kernel of `π`:
`a(x,y) * a(x*y, z) = (σ x · a(y,z) · (σ x)⁻¹) · a(x, y*z)` where
`a(x,y) = σ x * σ y * (σ (x*y))⁻¹`. -/
lemma fiveTerm_factor_conj_relation (π : G' →* G) (hπ : Function.Surjective π) (x y z : G) :
    (factor π hπ x y) * (factor π hπ (x * y) z)
      = fiveTerm_conjKer π (sectionOf π hπ x)⁻¹ (factor π hπ y z)
        * (factor π hπ x (y * z)) := by
  apply Subtype.ext
  show (factor π hπ x y : G') * (factor π hπ (x * y) z : G')
      = (fiveTerm_conjKer π (sectionOf π hπ x)⁻¹ (factor π hπ y z) : G')
        * (factor π hπ x (y * z) : G')
  rw [fiveTerm_conjKer_coe, factor_coe, factor_coe, factor_coe, factor_coe]
  rw [show x * (y * z) = x * y * z from (mul_assoc x y z).symm]
  group

/-- **The transgression is a `2`-cocycle**:  for an invariant character `t` of `N = ker π` and a
section `σ` of `π`, the cochain `candFun π hπ t` satisfies the cocycle identity with trivial
coefficients. -/
lemma fiveTerm_candFun_cocycle (π : G' →* G) (hπ : Function.Surjective π)
    (t : invCharSubmodule p π.ker) (x y z : G) :
    candFun π hπ t (x * y, z) + candFun π hπ t (x, y)
      = candFun π hπ t (y, z) + candFun π hπ t (x, y * z) := by
  simp only [candFun_apply]
  have hmain : (t.1 (Additive.ofMul (factor π hπ x y))
        + t.1 (Additive.ofMul (factor π hπ (x*y) z)))
      = t.1 (Additive.ofMul (factor π hπ y z))
        + t.1 (Additive.ofMul (factor π hπ x (y*z))) := by
    calc t.1 (Additive.ofMul (factor π hπ x y))
          + t.1 (Additive.ofMul (factor π hπ (x*y) z))
        = t.1 (Additive.ofMul (factor π hπ x y * factor π hπ (x*y) z)) := by simp
      _ = t.1 (Additive.ofMul (fiveTerm_conjKer π (sectionOf π hπ x)⁻¹ (factor π hπ y z)
            * factor π hπ x (y*z))) := by
            rw [fiveTerm_factor_conj_relation π hπ x y z]
      _ = t.1 (Additive.ofMul (fiveTerm_conjKer π (sectionOf π hπ x)⁻¹ (factor π hπ y z)))
            + t.1 (Additive.ofMul (factor π hπ x (y*z))) := by simp
      _ = t.1 (Additive.ofMul (factor π hπ y z))
            + t.1 (Additive.ofMul (factor π hπ x (y*z))) := by
            rw [fiveTerm_invChar_conjKer]
  linear_combination (-1 : ZMod p) * hmain

theorem fiveTerm_candFun_mem_Z2 {p : ℕ} [Fact p.Prime] {G G' : Type} [Group G] [Group G']
    (π : G' →* G) (hπ : Function.Surjective π) (t : Work.CFTLib.invCharSubmodule p π.ker) :
    Work.CFTLib.candFun π hπ t ∈ Work.CFTLib.Z2 p G := by
  rw [Work.CFTLib.Z2, groupCohomology.mem_cocycles₂_iff]
  intro x y z
  rw [Representation.isTrivial_apply]
  exact fiveTerm_candFun_cocycle π hπ t x y z

end

end Work.CFTLib
