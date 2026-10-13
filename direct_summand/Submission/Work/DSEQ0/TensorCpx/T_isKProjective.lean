import Mathlib
import Submission.Work.DSEQ0.TensorCpx.Basic

/-!
# The tensor square of a bounded-above free complex is K-projective

Let `F` be a cochain complex of `A`-modules all of whose terms are free, and suppose
that `F` is bounded above (`F.X i = 0` for `i > N`).  Then the explicit tensor square
`T F` of `TensorCpx/Basic.lean` is K-projective.

The proof is the two ingredients of `CochainComplex.isKProjective_of_projective`:

* every term `(T F).X n = ⨁_{i+j=n} F.X i ⊗ F.X j` is a direct sum of tensor products of
  free modules, hence free, hence projective;
* `T F` is strictly bounded above by `2 * N`: if `i + j = n > 2 * N` then `i > N` or
  `j > N`, so the corresponding summand `F.X i ⊗ F.X j` is zero.

No boundedness below and no finiteness assumption on `F` is needed: the direct sum
indexing a term of `T F` is infinite, but `Module.Free` (and hence `Projective`) is closed
under arbitrary direct sums of free modules.
-/

namespace Work.DSEQ0.TensorCpx

universe a

variable {A : Type a} [CommRing A] (F : CochainComplex (ModuleCat.{a} A) ℤ)

/-- Every term of the tensor square of a complex with free terms is free: it is a direct sum of
tensor products of free modules. -/
lemma T_X_free [∀ i : ℤ, Module.Free A (F.X i)] (n : ℤ) :
    Module.Free A (TX F n) :=
  inferInstance

/-- Every term of the tensor square of a complex with free terms is projective (indeed free). -/
lemma T_X_projective [∀ i : ℤ, Module.Free A (F.X i)] (n : ℤ) :
    CategoryTheory.Projective ((T F).X n) :=
  ModuleCat.projective_of_free (Module.Free.chooseBasis A (TX F n))

/-- The tensor square of a bounded above complex of modules is strictly bounded above:
`T F` vanishes in degrees `> 2 * N` as soon as `F` vanishes in degrees `> N`. -/
lemma T_isStrictlyLE (N : ℤ)
    (hN : ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (F.X i)) :
    (T F).IsStrictlyLE (2 * N) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  rw [ModuleCat.isZero_iff_subsingleton]
  -- every summand of `TX F n` has a zero tensor factor
  have hc : ∀ p : TIdx n, Subsingleton (TFam F p.1.1 p.1.2) := by
    intro p
    have hp : N < p.1.1 ∨ N < p.1.2 := by
      by_contra hcon
      push Not at hcon
      have h2 : p.1.1 + p.1.2 ≤ 2 * N := by linarith [hcon.1, hcon.2]
      omega
    rcases hp with hp | hp
    · have : Subsingleton ↥(F.X p.1.1) :=
        ModuleCat.subsingleton_of_isZero (hN _ hp)
      infer_instance
    · have : Subsingleton ↥(F.X p.1.2) :=
        ModuleCat.subsingleton_of_isZero (hN _ hp)
      infer_instance
  have hsub : Subsingleton (TX F n) := by
    have := hc
    infer_instance
  exact hsub

theorem T_isKProjective (A : Type a) [CommRing A] (F : CochainComplex (ModuleCat.{a} A) ℤ)
    [∀ i : ℤ, Module.Free A (F.X i)]
    (hFb : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (F.X i)) :
    (Work.DSEQ0.TensorCpx.T F).IsKProjective := by
  obtain ⟨N, hN⟩ := hFb
  have hproj : ∀ n : ℤ, CategoryTheory.Projective ((T F).X n) :=
    fun n => T_X_projective F n
  have hbdd : (T F).IsStrictlyLE (2 * N) := T_isStrictlyLE F N hN
  exact CochainComplex.isKProjective_of_projective (T F) (2 * N)

end Work.DSEQ0.TensorCpx
