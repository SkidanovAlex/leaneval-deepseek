import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.RatHurewicz.SphereConnectivity

/-!
# Area SPHEREFG: `π_{j+2}(Sⁿ)` is finitely generated (`n ≥ 2`)

Given Serre's theorem that a simply connected space whose integral homology is finitely generated in
every degree has finitely generated homotopy groups (`Work.PiS.SerreFGTheorem`), we apply it to the
sphere `Sⁿ`:

* `Sⁿ` is path connected and simply connected for `n ≥ 2` — this is the connectivity of spheres
  `Work.RatHurewicz.sphereConnected` (in its `j = 0, 1` cases);
* `H_i(Sⁿ; ℤ)` is ℤ for `i = 0`, ℤ for `i = n` and `0` otherwise, hence finitely generated in every
  degree: `Work.Cohomology.sphereHomologyTop` for the top degree, `Work.Cohomology.sphereVanishing`
  off it, and the augmentation `H₀(X;ℤ) → ℤ` for degree `0` (an isomorphism for path connected
  spaces).
-/

set_option autoImplicit false

open CategoryTheory Limits

namespace Work.FGThm

noncomputable section

/-- **A trivial module is finitely generated.**  A `ModuleCat ℤ` object isomorphic to `0` has
`⊤ = ⊥` among its submodules, hence `⊤` is finitely generated. -/
theorem module_finite_of_isZero {M : ModuleCat ℤ} (h : CategoryTheory.Limits.IsZero M) :
    Module.Finite ℤ ↥M := by
  have hsub : Subsingleton ↥M := ModuleCat.subsingleton_of_isZero h
  refine ⟨?_⟩
  rw [show (⊤ : Submodule ℤ ↥M) = ⊥ from
    (Submodule.eq_bot_iff _).2 (fun x _ => Subsingleton.elim x 0)]
  exact Submodule.fg_bot

/-- **`H₀` of a path connected space is finitely generated** (indeed `≅ ℤ`, via the augmentation
`ε : H₀(X;ℤ) ⟶ ℤ`, an isomorphism for path connected `X`). -/
theorem module_finite_H0 (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    Module.Finite ℤ ↥(Work.PiS.HZ X 0) := by
  haveI : IsIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := inferInstance
  exact Module.Finite.equiv
    (asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv.symm

/-- **`Sⁿ` is path connected for `n ≥ 2`.**  Derived from the connectivity of spheres
(`π₀(Sⁿ) = *`): `ZerothHomotopy` is the set of path components. -/
theorem pathConnectedSpace_sph (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace (Work.PiS.Sph n) := by
  haveI hsub : Subsingleton (HomotopyGroup.Pi 0 (Work.PiS.Sph n) (Work.PiS.pt n)) :=
    Work.RatHurewicz.sphereConnected n (by omega) (Work.PiS.pt n) 0 (by omega)
  haveI hz : Subsingleton (ZerothHomotopy (Work.PiS.Sph n)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := (HomotopyGroup.pi0EquivZerothHomotopy (x := Work.PiS.pt n)).surjective a
    obtain ⟨b', rfl⟩ := (HomotopyGroup.pi0EquivZerothHomotopy (x := Work.PiS.pt n)).surjective b
    rw [Subsingleton.elim a' b']
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨ZerothHomotopy.mk (Work.PiS.pt n)⟩, inferInstance⟩

/-- **The integral homology of `Sⁿ` is finitely generated in every degree** (`n ≥ 2`):
`H_i(Sⁿ;ℤ)` is `ℤ` for `i = 0` and `i = n`, and `0` for all other `i`. -/
theorem fgUpTo_sph (n : ℕ) (hn : 2 ≤ n) : ∀ N : ℕ, Work.PiS.FGUpTo (Work.PiS.Sph n) N := by
  intro N i hi
  haveI : PathConnectedSpace (Work.PiS.Sph n) := pathConnectedSpace_sph n hn
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact module_finite_H0 (Work.PiS.Sph n)
  · by_cases hin : i = n
    · rw [hin]
      obtain ⟨e⟩ := Work.Cohomology.sphereHomologyTop n (by omega)
      exact Module.Finite.equiv e.toLinearEquiv.symm
    · exact module_finite_of_isZero
        (Work.Cohomology.sphereVanishing n i (by omega) (by omega) hin)

/-- **Area SPHEREFG.**  `π_{j+2}(Sⁿ)` is finitely generated for `n ≥ 2`, by Serre's theorem applied
to the sphere (a simply connected space with finitely generated integral homology). -/
theorem sphereFG (hFG : Work.PiS.SerreFGTheorem) : Work.PiS.SphereFG := by
  intro n hn j
  have hconn := Work.RatHurewicz.sphereConnected n (by omega) (Work.PiS.pt n)
  exact hFG (Work.PiS.Sph n) (Work.PiS.pt n) ⟨hconn 0 (by omega), hconn 1 (by omega)⟩
    (fgUpTo_sph n hn) j

end

end Work.FGThm
