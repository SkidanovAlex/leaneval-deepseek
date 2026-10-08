import Mathlib
import Submission.Work.Hering.AppVII.brauer_setup
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Lifting irreducible character values into `ℤ[ζ_|A|]`

For a finite group `A`, an irreducible complex character `χ` of `A` and an element `g : A`,
the value `χ g` is a sum of eigenvalues of the linear map `ρ g`, where `ρ` is an irreducible
representation affording `χ`.  Since `g` has finite order dividing `|A|`, each such eigenvalue
is a root of unity of order dividing `|A|`, hence lies in the image of the canonical map
`iota : ℤ[ζ_|A|] → ℂ` (`ζ_|A| = exp(2πi/|A|)`).  This file constructs explicitly such a lift.

The proof uses that `Work.CharCore.Irr A` consists of characters of the simple submodules of
the regular module `ℂ[A]`, so that `χ = (submoduleRep N).character` for some such submodule `N`.
-/

noncomputable section

open Classical Module.End

open scoped BigOperators

namespace Work.Hering.AppVII

theorem exists_charLift {A : Type*} [Group A] [Fintype A] (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) (g : A) :
    ∃ x : Work.Hering.AppVII.CycloRing (Nat.card A),
      Work.Hering.AppVII.iota (Nat.card A) x = χ g := by
  -- `χ` is the character of some simple submodule of the regular module `ℂ[A]`.
  obtain ⟨N, _hN, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
  let ρ : Representation ℂ A N := Work.CharCore.submoduleRep N
  let roots : Multiset ℂ := (LinearMap.charpoly (ρ g)).roots
  -- `χ g` is the trace of `ρ g`, which is the sum of the roots of its characteristic polynomial.
  have hchar : χ g = (LinearMap.trace ℂ N) (ρ g) := by
    rw [← hNχ]; rfl
  have htrace : (LinearMap.trace ℂ N) (ρ g) = roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)
  -- `ζ = iota (root) = exp(2πi/|A|)` is a primitive `|A|`-th root of unity.
  have hζ : IsPrimitiveRoot
      (iota (Nat.card A) (AdjoinRoot.root (Polynomial.cyclotomic (Nat.card A) ℤ)))
      (Nat.card A) := by
    have h : iota (Nat.card A) (AdjoinRoot.root (Polynomial.cyclotomic (Nat.card A) ℤ))
        = Complex.exp (2 * Real.pi * Complex.I / (Nat.card A)) := by
      unfold Work.Hering.AppVII.iota
      exact AdjoinRoot.lift_root _
    rw [h]
    exact Complex.isPrimitiveRoot_exp _ (NeZero.ne _)
  -- Every root of the characteristic polynomial of `ρ g` is a `|A|`-th root of unity.
  have hxpow : ∀ x ∈ roots, x ^ Nat.card A = 1 := by
    intro x hx
    have hroot : (LinearMap.charpoly (ρ g)).IsRoot x := Polynomial.isRoot_of_mem_roots hx
    have hae : Module.End.HasEigenvalue (ρ g) x :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 hroot
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hae
    have hxm : x ^ orderOf g = 1 := by
      refine smul_left_injective ℂ hv.2 ?_
      simp [← hv.pow_apply, ← map_pow]
    obtain ⟨k, hk⟩ := orderOf_dvd_natCard g
    rw [hk, pow_mul, hxm, one_pow]
  classical
  -- Choose, for each root `x` of the characteristic polynomial, an exponent `e x` with
  -- `ζ ^ (e x) = x`.
  let e : ℂ → ℕ := fun x => if hx : x ∈ roots then
      Classical.choose (hζ.eq_pow_of_pow_eq_one (hxpow x hx)) else 0
  have he : ∀ x ∈ roots,
      (iota (Nat.card A) (AdjoinRoot.root (Polynomial.cyclotomic (Nat.card A) ℤ))) ^ (e x) = x := by
    intro x hx
    simp only [e, dite_eq_left hx]
    exact (Classical.choose_spec (hζ.eq_pow_of_pow_eq_one (hxpow x hx))).2
  -- The lift: `∑_x root ^ (e x)`.
  refine ⟨(roots.map (fun x =>
    (AdjoinRoot.root (Polynomial.cyclotomic (Nat.card A) ℤ)) ^ e x)).sum, ?_⟩
  rw [map_multiset_sum]
  have hkey : Multiset.map (iota (Nat.card A))
        (roots.map (fun x =>
          (AdjoinRoot.root (Polynomial.cyclotomic (Nat.card A) ℤ)) ^ e x))
      = Multiset.map id roots := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun x hx => ?_)
    rw [Function.comp_apply, map_pow]
    exact he x hx
  rw [hkey, Multiset.map_id, ← hchar.trans htrace]

end Work.Hering.AppVII
