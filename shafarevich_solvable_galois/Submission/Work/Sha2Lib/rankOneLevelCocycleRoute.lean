import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.PTdualControl.C6_rankOneBrick
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank-one brick of node `C6`, reduced to a single level-cocycle datum

`Work.SSGRoute.Sha2Lib.unramifiedDetector_indNormal_rankOne` (the last arithmetic brick of node
`C6`) is the detector for the permutation module `Ind_N^Γ 𝔽_p`, `Γ = Gal(K/k)`, `N ⊴ Γ` containing
the inertia at `q ∤ p` and fixing `ζ : K` with `IsPrimitiveRoot ζ p`.

This file records the *sharp form* of the remaining obligation, using the already proved
cohomological bookkeeping rather than re-deriving it:

* the module is carried in the **coinduced** model `Rep.coind N.subtype 𝔽_p`, which is isomorphic to
  the induced one for the finite group `Γ` (`Rep.indCoindIso`), and the detector is invariant under
  a coefficient isomorphism (`Sha2Lib.isUnramifiedDetector_of_iso` /
  `rankOne_isUnramifiedDetector_of_iso` in `Sha2Lib/rankOneBrickWork.lean`);
* every nonzero `φ ∈ Ext¹_{D_w}(res M, ℤ)` is `δ μ` for a nonzero `D_w`-equivariant functional
  `μ` (`Work.E7cOmega.functional_of_ext_nonzero`, resp. `SSGStage.divRep_detecting_class`);
* for such a `μ` it *remains* to exhibit a level `L ⊇ K`, a place `q' | q` with `p ∤ e(q'|q)`, and
  a `1`-cocycle `z ∈ H¹(Gal(L/k), res M)` which vanishes on the inertia at `q'` and takes a value
  that `μ` does not kill — the datum
  `Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq M μ`;
* the datum implies the detector at `δ μ` by the *proved*
  `Work.SSGRoute.PTdualControl.detectsAt_of_levelCocycleDatum` (whose own proof is the pairing
  computation through `SSGStage.levelPair_eCoh_cocycles_ne_zero` and
  `E7cOmega.levelPair_ratDivSES_mk0_ne_zero_iff`).

So the whole brick is: *produce the level-cocycle datum for every nonzero `μ` on the coinduced
permutation module*.  Nothing else about `Ext`, the pairing, or the level `ℚ/ℤ`-criterion is left.

The arithmetic content of the datum is the Shapiro/Frobenius construction: `z` is the Shapiro
cocycle of a character `χ` of the coefficient group `Gal(K^N/k)` — equivalently of
`Gal(L/K^N)` — which is unramified above `q` and whose value at the Frobenius of the selected place
is prescribed (so that one term of the coset sum `μ (z d) = Σ_u c_u χ(Frob_u)` is nonzero, the
coefficients `c_u` being the double-coset components of `μ`).  The workspace already has the
group-theoretic half on disk: `Sha2Lib.shapiroCocycle_mem` (the cocycle),
`Sha2Lib.telescoping_pow` and `Sha2Lib.shapiro_frobenius_telescope` (the orbit telescope),
`Sha2Lib.coindValueFormula_singleOrbit` and `C6ValueFormula.{coset_sum,detection_value}` (the value
formula).

## Warning on the ambient field

The datum must be produced **inside `Ω`**: the interface carries only `[IsAlgClosed Ω]` (no
`IsAlgClosure k Ω`; see `Sha2Lib/PING_ambient_Omega_not_algClosure.md`), so the levels have to be
built by adjoining `p`-th roots of elements of `K^N` inside `Ω` (Kummer), and the local input has to
be the Kummer/weak-approximation form
(`NK.UchidaKummer.IsKummerSurjective`, `NK.UchidaKummer.IsKummerLocalDichotomy`,
`Sha2Lib.exists_unramified_character_with_p_dvd_residueDeg`,
`Sha2Lib.extH_class_of_character`) rather than the `IsAlgClosure`-spelled Grünwald theorems.
-/

namespace Work.Sha2Lib

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1

noncomputable section

set_option linter.style.haveILetI false

/-- The coinduced model of the permutation module `Ind_N^Γ 𝔽_p` is finite: it is a submodule of the
functions `Γ → 𝔽_p`. -/
instance coindPerm_finite (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) :
    Finite (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The coinduced model of the permutation module is killed by `p`. -/
theorem coindPerm_psmul (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) :
    ∀ m : (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))).V, p • m = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro m
  rw [← Nat.cast_smul_eq_nsmul SSGRoute.PTExt.Coeff]
  apply Subtype.ext
  rw [Submodule.coe_smul, Submodule.coe_zero]
  funext g
  rw [Pi.smul_apply]
  show ((p : ℤ) • ((m : (K ≃ₐ[k] K) → ZMod p) g) : ZMod p) = 0
  rw [zsmul_eq_mul]
  push_cast
  rw [ZMod.natCast_self, zero_mul]

/-- **The rank-one brick, reduced to the level-cocycle datum.**

If for every nonzero `D_w`-equivariant functional `μ` on the restriction of the coinduced
permutation module `M = coInd_N^Γ 𝔽_p` there is a level-cocycle datum
`LevelCocycleDatum p k K Ω w q hwq M μ`, then the detector holds at each of the classes
`δ μ ∈ Ext¹_{D_w}(res M, ℤ)`, `μ ≠ 0`.

Together with `Work.E7cOmega.functional_of_ext_nonzero` (every nonzero `φ` is such a `δ μ`) this is
the whole remaining obligation of the rank-one brick. -/
theorem rankOne_functionalDetection_of_levelCocycleDatum (p : ℕ) [Fact p.Prime] (k K : Type)
    [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (N : Subgroup (K ≃ₐ[k] K))
    (h : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 →
      Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ) :
    ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
          (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 →
      Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
        ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
              (G := SSGRoute.PTExt.decompK (k := k) (K := K) w))) (zero_add 1)) := by
  classical
  haveI := coindPerm_finite (p := p) (k := k) (K := K) N
  intro μ hμ
  exact Work.SSGRoute.PTdualControl.detectsAt_of_levelCocycleDatum p k K Ω w q hwq
    (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p)))
    (coindPerm_psmul (p := p) (k := k) (K := K) N) μ (h μ hμ)

end

end Work.Sha2Lib
