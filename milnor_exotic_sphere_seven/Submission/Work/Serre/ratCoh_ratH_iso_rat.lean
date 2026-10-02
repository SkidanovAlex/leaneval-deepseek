import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Cohomology.DualComplex
import Submission.Work.StemsB.FieldDualUCT

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Hⁿ(X;ℚ)` is a line iff `Hₙ(X;ℚ)` is a line

This file proves `Work.Serre.ratCoh_ratH_iso_rat`: for a topological space `X` and a degree `n`,

  `Hⁿ(X;ℚ) ≅ ℚ  ⟺  Hₙ(X;ℚ) ≅ ℚ`   (as `ℚ`-vector spaces).

Neither implication is formal, although both are true and the work is standard: the bridge between
the two sides is the universal coefficient theorem over the field `ℚ`,
`Work.StemsB.ratDualUCT`,

  `Hⁿ(X;ℚ) ≅ Hom_ℚ(Hₙ(X;ℚ), ℚ)`,

together with the pure linear algebra fact that a `ℚ`-vector space is a line exactly when its dual
is.  (Note that this last statement is *not* dimension counting in the naive sense — the
double dual is only an isomorphism onto the double dual for finite dimensional spaces — but it is
still true, and the clean proof is to characterise "being a line" by `finrank = 1`.)

## The linear algebra

* `Work.Serre.nonempty_linearEquiv_rat_iff_finrank` — a `ℚ`-module `M` satisfies `M ≃ₗ[ℚ] ℚ` iff
  `finrank ℚ M = 1`.  The forward direction is `LinearEquiv.finrank_eq`; the backward direction
  uses `finrank_eq_one_iff'` (`finrank = 1` produces a generator `v ≠ 0` of `M`), whence
  `c ↦ c • v` is a bijective linear map `ℚ → M`.
* `Work.Serre.nonempty_iso_rat_iff_finrank` — the same statement phrased with `ModuleCat ℚ`
  isomorphisms, via `CategoryTheory.Iso.toLinearEquiv` and `LinearEquiv.toModuleIso`.
* `Subspace.dual_finrank_eq` (`finrank K (Dual K V) = finrank K V`) is what makes the duality
  *invisible* to the invariant `finrank = 1`.

## Main result

* `Work.Serre.ratCoh_ratH_iso_rat`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **A `ℚ`-module is a line iff its finrank is one.**  The backward direction uses the generator
produced by `finrank_eq_one_iff'`: if `v ≠ 0` spans a `ℚ`-module `M` then `c ↦ c • v` is a linear
bijection `ℚ ≃ₗ M`. -/
theorem nonempty_linearEquiv_rat_iff_finrank (M : Type) [AddCommGroup M] [Module ℚ M] :
    Nonempty (M ≃ₗ[ℚ] ℚ) ↔ Module.finrank ℚ M = 1 := by
  constructor
  · rintro ⟨e⟩
    rw [e.finrank_eq, CommSemiring.finrank_self]
  · intro h
    obtain ⟨v, hv, hsurj⟩ := (finrank_eq_one_iff' (K := ℚ) (V := M)).mp h
    refine ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℚ M v) ?_).symm⟩
    refine ⟨?_, ?_⟩
    · -- injectivity: `a • v = b • v` forces `a = b` because `v ≠ 0`
      intro a b hab
      rw [LinearMap.toSpanSingleton_apply, LinearMap.toSpanSingleton_apply] at hab
      have h0 : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hv)
    · -- surjectivity is the hypothesis that `v` generates
      intro w
      obtain ⟨c, hc⟩ := hsurj w
      exact ⟨c, by rw [LinearMap.toSpanSingleton_apply, hc]⟩

/-- The `ModuleCat ℚ` form of `nonempty_linearEquiv_rat_iff_finrank`. -/
theorem nonempty_iso_rat_iff_finrank (N : ModuleCat ℚ) :
    Nonempty (N ≅ ModuleCat.of ℚ ℚ) ↔ Module.finrank ℚ ↥N = 1 := by
  constructor
  · rintro ⟨i⟩
    rw [i.toLinearEquiv.finrank_eq, CommSemiring.finrank_self]
  · intro h
    obtain ⟨e⟩ := (nonempty_linearEquiv_rat_iff_finrank ↥N).mpr h
    exact ⟨e.toModuleIso⟩

/-- **Rational cohomology is a line in degree `n` iff rational homology is.**

Combined with the universal coefficient theorem `Work.StemsB.ratDualUCT`
(`Hⁿ(X;ℚ) ≅ Hom_ℚ(Hₙ(X;ℚ), ℚ)`), both sides are equivalent to `finrank ℚ = 1` of the
corresponding space, using `Subspace.dual_finrank_eq` for the passage to the dual. -/
theorem ratCoh_ratH_iso_rat (X : TopCat) (n : ℕ) :
    Nonempty (Work.Serre.ratCoh X n ≅ ModuleCat.of ℚ ℚ) ↔
      Nonempty (Work.Serre.ratH X n ≅ ModuleCat.of ℚ ℚ) := by
  -- `ratCoh X n` *is* the degree-`n` cohomology of the dual of the rational singular chain
  -- complex, so the universal coefficient theorem applies to it verbatim.
  have hfin : Module.finrank ℚ ↥(Work.Serre.ratCoh X n) =
      Module.finrank ℚ ↥(Work.Serre.ratH X n) := by
    obtain ⟨e⟩ := Work.StemsB.ratDualUCT (Work.Serre.ratChains X) n
    calc Module.finrank ℚ ↥(Work.Serre.ratCoh X n)
        = Module.finrank ℚ ↥(ModuleCat.of ℚ (↥(Work.Serre.ratH X n) →ₗ[ℚ] ℚ)) :=
          e.toLinearEquiv.finrank_eq
      _ = Module.finrank ℚ ↥(Work.Serre.ratH X n) := Subspace.dual_finrank_eq
  rw [nonempty_iso_rat_iff_finrank (Work.Serre.ratCoh X n),
    nonempty_iso_rat_iff_finrank (Work.Serre.ratH X n), hfin]

end

end Work.Serre
