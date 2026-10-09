import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Prelude
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A `p`-th root in the completion at a completely split prime

If `L / K` is a finite extension of number fields, `a ∈ Kˣ` and `α ∈ L` with `α ^ p = a`, and the
prime `q` of `𝓞 K` splits completely in `L`, then the image of `a` in the local field `K_q` is a
`p`-th power.

The point is that for every prime `Q` of `𝓞 L` above `q` the local degree is `e · f = 1`, so the
natural map `K_q → L_Q` is an isomorphism of `K_q`-algebras; applying its inverse to `α` gives the
required `p`-th root.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- A prime of `𝓞 L` above a given prime of `𝓞 K`. -/
lemma exists_heightOneSpectrum_liesOver
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      Q.asIdeal.LiesOver q.asIdeal := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (q.asIdeal.primesOver
    (NumberField.RingOfIntegers L)))
  exact ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver q.ne_bot P.2⟩, P.2.2⟩

theorem exists_adicCompletion_units_pow_eq_of_splitsCompletely
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] {p : ℕ} {a : K} (ha : a ≠ 0) {α : L}
    (hα : α ^ p = algebraMap K L a)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hspl : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      Q.asIdeal.LiesOver q.asIdeal →
        Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) :
    ∃ c : (q.adicCompletion K)ˣ,
      algebraMap K (q.adicCompletion K) a = ((c : (q.adicCompletion K)ˣ) : q.adicCompletion K) ^ p := by
  classical
  obtain ⟨Q, hQ⟩ := exists_heightOneSpectrum_liesOver (K := K) (L := L) q
  haveI hQL : Q.asIdeal.LiesOver q.asIdeal := hQ
  -- The `q.adicCompletion K`-algebra structure on `Q.adicCompletion L`.
  letI : Algebra (q.adicCompletion K) (Q.adicCompletion L) :=
    (Commons.RingTheory.Henselian.adicCompletionMap q Q hQ).toAlgebra
  let f : (q.adicCompletion K) →+* (Q.adicCompletion L) :=
    Commons.RingTheory.Henselian.adicCompletionMap q Q hQ
  have hf_eq : (algebraMap (q.adicCompletion K) (Q.adicCompletion L)) = f :=
    RingHom.algebraMap_toAlgebra f
  -- The local degree is `e · f = 1` by hypothesis.
  obtain ⟨he, hf⟩ := hspl Q hQ
  have hfr : Module.finrank (q.adicCompletion K) (Q.adicCompletion L) = 1 := by
    have h :=
      Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
        (K := K) (L := L) q Q hQ
    rw [he, hf, mul_one] at h
    exact h.symm
  -- `f` is a bijection: injective as a map of fields, surjective by the dimension count.
  have hinj : Function.Injective f := f.injective
  have hbij : Function.Bijective f := by
    refine ⟨hinj, ?_⟩
    haveI hfin : Module.Finite (q.adicCompletion K) (Q.adicCompletion L) :=
      Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion q Q hQ
    have hdim : Module.finrank (q.adicCompletion K) (q.adicCompletion K) =
        Module.finrank (q.adicCompletion K) (Q.adicCompletion L) := by
      rw [Module.finrank_self, hfr]
    have hlin : ⇑(Algebra.linearMap (q.adicCompletion K) (Q.adicCompletion L)) = ⇑f := by
      funext x
      rw [Algebra.linearMap_apply, hf_eq]
    have hinjlin : Function.Injective
        (Algebra.linearMap (q.adicCompletion K) (Q.adicCompletion L)) := by
      rw [hlin]; exact hinj
    have hsurjlin := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinjlin
    rw [hlin] at hsurjlin
    exact hsurjlin
  -- The inverse isomorphism `Q.adicCompletion L ≃+* q.adicCompletion K`.
  let e : (Q.adicCompletion L) ≃+* (q.adicCompletion K) :=
    (RingEquiv.ofBijective f hbij).symm
  have hef : ∀ y : (q.adicCompletion K), e (f y) = y := by
    intro y
    have h1 : RingEquiv.ofBijective f hbij y = f y := RingEquiv.ofBijective_apply f hbij y
    change (RingEquiv.ofBijective f hbij).symm (f y) = y
    rw [← h1]
    exact RingEquiv.symm_apply_apply _ y
  -- The compatible map `L →+* q.adicCompletion K`.
  let φ : L →+* (q.adicCompletion K) :=
    e.toRingHom.comp (algebraMap L (Q.adicCompletion L))
  have hstep : ∀ x : K, algebraMap L (Q.adicCompletion L) (algebraMap K L x) =
      f (algebraMap K (q.adicCompletion K) x) := by
    intro x
    have hL : ∀ y : L, algebraMap L (Q.adicCompletion L) y = (y : Q.adicCompletion L) :=
      fun y => congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
        (v := Q) (S := L) (K := L)) y
    have hK : ∀ y : K, algebraMap K (q.adicCompletion K) y = (y : q.adicCompletion K) :=
      fun y => congrFun (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
        (v := q) (S := K) (K := K)) y
    rw [hL (algebraMap K L x), hK x]
    exact (Commons.RingTheory.Henselian.adicCompletionMap_apply q Q hQ x).symm
  have hφ : ∀ x : K, φ (algebraMap K L x) = algebraMap K (q.adicCompletion K) x := by
    intro x
    change e (algebraMap L (Q.adicCompletion L) (algebraMap K L x)) =
      algebraMap K (q.adicCompletion K) x
    rw [hstep x]
    exact hef (algebraMap K (q.adicCompletion K) x)
  rcases Nat.eq_zero_or_pos p with hp0 | hp
  · -- `p = 0`: then `a = 1` (as `α ^ 0 = 1`) and the unit `1` works.
    subst hp0
    refine ⟨1, ?_⟩
    have ha1 : a = 1 := by
      refine RingHom.injective (algebraMap K L) ?_
      rw [map_one, ← hα, pow_zero]
    rw [ha1, map_one]
    simp
  · -- `p > 0`: the image of `α` is a `p`-th root of the image of `a`.
    have hc0 : (φ α) ^ p = algebraMap K (q.adicCompletion K) a :=
      calc (φ α) ^ p = φ (α ^ p) := (map_pow φ α p).symm
        _ = φ (algebraMap K L a) := by rw [hα]
        _ = algebraMap K (q.adicCompletion K) a := hφ a
    have hane : algebraMap K (q.adicCompletion K) a ≠ 0 := by
      intro h0
      refine ha (RingHom.injective (algebraMap K (q.adicCompletion K)) ?_)
      rw [h0, map_zero]
    have hcne : φ α ≠ 0 := by
      intro hz
      rw [hz, zero_pow hp.ne'] at hc0
      exact hane hc0.symm
    exact ⟨Units.mk0 (φ α) hcne, by rw [Units.val_mk0]; exact hc0.symm⟩

end NK.GlobalCFTdeep.SecondInequality.KummerCase
