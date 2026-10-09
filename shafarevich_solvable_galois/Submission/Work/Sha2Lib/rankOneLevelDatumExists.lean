import Mathlib
import Submission.Work.Sha2Lib.noninvWiring
import Submission.Work.SSGcrux.concentratedLevelDataExists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `rankOneLevelDatumExists`: the level-cocycle datum of the rank-one brick (`C6`)

This file holds the assignment's target: for
`M = Rep.coind N.subtype (Rep.trivial Coeff N (ZMod p))` (the coinduced model of the permutation
module `Ind_N^Γ 𝔽_p`, `Γ = Gal(K/k)`, `N ⊴ Γ` containing the inertia at `q ∤ p` and fixing a
primitive `p`-th root of unity `ζ ∈ K`) and every nonzero `D_w`-equivariant functional
`μ : res_{D_w} M ⟶ ℚ/ℤ`, produce a level-cocycle datum
`LevelCocycleDatum p k K Ω w q hwq M μ`.

**Wiring (measured 2026-10-07).**  The proof is a three-line assembly of two *proved*,
axiom-clean inputs, and it needs no case split at all:

1. `Work.Sha2Lib.C6Wiring.exists_coindDirac_apply_ne_zero`
   (`Submission/Work/Sha2Lib/noninvWiring.lean`, the local copy of the former
   `Submission/Work/SSGRoute/C6Detector/wiringNoninvariant.lean`): a nonzero `D_w`-equivariant
   functional detects some coset Dirac `δ_{Nγ₀}` of the coinduced permutation module.  This is the
   coset-selection step — it does *not* require `μ` to vanish on the constant vector, the constant
   case being the special case in which the detected coset is `N`.
2. `Work.SSGcrux.concentratedLevelDataExists`
   (`Submission/Work/SSGcrux/concentratedLevelDataExists.lean`, **proved and axiom-clean**): for that
   `γ₀` it produces the *concentrated level data* — a finite Galois level `L ⊇ K` inside the ambient
   `Ω`, a place `q' | w` with `p ∤ e(q'|q)`, the Frobenius-type element `d ∈ D_{q'}` generating
   `D_{q'}` modulo `H = galRes⁻¹ N` with minimal exponent `f`, and a character
   `y : H →* 𝔽_p` killing the normal closure of the inertia at `q'`, concentrated on the block of
   `γ₀` (`y (cfunc H x (d^f)) = 1 ↔ galRes x ∉ concSet k K w N γ₀`).  Its proof is the Grünwald
   construction (level `E/K₁` unramified over `l`, the Shapiro cocycle, the telescoping at the
   Frobenius) together with the normal-closure inertia argument
   (`Work.SSGate.inertia_eq_bot_of_concentrated_level`).
3. `Work.Sha2Lib.C6Wiring.levelCocycleDatum_of_concentrated`
   (same file as 1., **proved**): the cohomological wiring, `TPatom.levelCocycleDatum_of_blockData`
   plus the Mackey/Dirac comparison `SSGcrux.mackeyInvDirac`, which turns 1. and 2. into
   `LevelCocycleDatum p k K Ω w q hwq M μ`.

Because the ambient field is an arbitrary `[IsAlgClosed Ω]`, no transport of the datum from the
canonical field `AlgebraicClosure K` is needed: `concentratedLevelDataExists` is stated directly at
`Ω`.  (Earlier sessions routed the constant-detected case through
`Work.Sha2Lib.levelCocycleDatum_of_constant` and transported along `IsAlgClosed.lift`; that branch
is now subsumed, since 1. applies to *every* nonzero `μ`.)

-/

namespace Work.Sha2Lib

theorem rankOneLevelDatumExists (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) (hNζ : ∀ σ ∈ N, σ ζ = ζ)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ := by
  classical
  -- 1. a nonzero `μ` detects a coset Dirac `δ_{Nγ₀}`
  obtain ⟨γ₀, hγ₀⟩ :=
    Work.Sha2Lib.C6Wiring.exists_coindDirac_apply_ne_zero (K := K) (k := k) p N w μ hμ
  -- 2./3. the concentrated level data at `γ₀`, wired into the level-cocycle datum
  exact Work.Sha2Lib.C6Wiring.levelCocycleDatum_of_concentrated p k K Ω w q hwq N hNI μ γ₀
    hγ₀ (Work.SSGcrux.concentratedLevelDataExists p k K Ω w q hwq hpq N hNI ζ hζ hNζ γ₀)

end Work.Sha2Lib
