/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion

/-!
# Surjectivity of the local norm on local units at an unramified place

Let `L / K` be a finite Galois extension of number fields, `Q` a nonzero prime of `𝓞 K` and `q` a
nonzero prime of `𝓞 L` lying over `Q` with ramification index one.  Then the local norm
`N_{L_q/K_Q} : L_qˣ → K_Qˣ` maps the group `𝒪_{L_q}ˣ` of local units *onto* the group `𝒪_{K_Q}ˣ`
of local units.

This is the classical fact that an unramified extension has norm-surjective unit groups.  The
proof here is the elementary valuation argument used in `Commons`: for `a ∈ 𝒪_{K_Q}ˣ`, i.e.
`v a = 1`, the commons lemma
`Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one`
produces `x ∈ L_q` with `N x = a`; the norm identity
`v (algebraMap (N x)) = (v x) ^ [L_q : K_Q]` (with `algebraMap` preserving the valuation because
`e = 1`, and `[L_q : K_Q] = f ≠ 0`) forces `v x = 1`, so that `x` is a unit of `𝒪_{L_q}`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped NumberField WithZero
open NumberField IsDedekindDomain

namespace NK.NUV2.ArtinBridge

theorem localUnits_le_image_localNormFinite_of_ramificationIdx_eq_one {K L : Type*} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hunr : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    ∀ a ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q),
      ∃ u ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q),
        NK.GlobalCFT.Place.localNormFinite q Q hq u = a := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  intro a ha
  have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (a : Q.adicCompletion K) = 1 :=
    (NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one (K := K) (q := Q)).mp ha
  obtain ⟨x, hx⟩ :=
    Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
      Q q hq hunr (a : Q.adicCompletion K) hval
  have hxne : x ≠ 0 := by
    intro h0
    have h1 : Algebra.norm (Q.adicCompletion K) x = (0 : Q.adicCompletion K) := by
      rw [h0, Algebra.norm_zero]
    rw [h1] at hx
    exact Units.ne_zero a hx.symm
  -- the valuation of `x` is `1`
  have hvx : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x = 1 := by
    have h1 := Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow Q q hq x
    have h2 := Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q hq
      (Algebra.norm (Q.adicCompletion K) x)
    have halg : (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (Algebra.norm (Q.adicCompletion K) x)) =
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
          (Algebra.norm (Q.adicCompletion K) x) := rfl
    have hfin : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) =
        q.asIdeal.inertiaDeg (𝓞 K) := by
      have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        (K := K) (L := L) Q q hq
      rw [hunr, one_mul] at h
      exact h.symm
    have hvpow : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x ^
        (q.asIdeal.inertiaDeg (𝓞 K)) = 1 := by
      rw [← hfin, ← h1, halg, h2, hx, hval, hunr]
      simp
    have hvne : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr hxne
    have hlog : (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) *
        WithZero.log (Valued.v (R := q.adicCompletion L)
          (Γ₀ := WithZero (Multiplicative ℤ)) x) = 0 := by
      have h := WithZero.log_pow (Valued.v (R := q.adicCompletion L)
        (Γ₀ := WithZero (Multiplicative ℤ)) x) (q.asIdeal.inertiaDeg (𝓞 K))
      rw [hvpow, WithZero.log_one] at h
      simpa [nsmul_eq_mul] using h.symm
    have hfne : (q.asIdeal.inertiaDeg (𝓞 K) : ℤ) ≠ 0 := by
      haveI : q.asIdeal.IsPrime := q.isPrime
      haveI : Module.Finite (𝓞 K) (𝓞 L) := inferInstance
      exact_mod_cast (Ideal.inertiaDeg_pos q.asIdeal (𝓞 K)).ne'
    have hlog0 : WithZero.log (Valued.v (R := q.adicCompletion L)
        (Γ₀ := WithZero (Multiplicative ℤ)) x) = 0 :=
      (mul_eq_zero.mp hlog).resolve_left hfne
    rw [← WithZero.exp_log hvne, hlog0, WithZero.exp_zero]
  refine ⟨Units.mk0 x hxne, ?_, ?_⟩
  · rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
    exact hvx
  · rw [NK.GlobalCFT.Place.localNormFinite]
    refine Units.ext ?_
    rw [Units.coe_map, Units.val_mk0]
    exact hx

end NK.NUV2.ArtinBridge
