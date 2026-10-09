import Mathlib.RingTheory.PicardGroup
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_mem_integers
import Submission.Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers
import Submission.Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

theorem module_finite_adicCompletionIntegers {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
      RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
          (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
    Module.Finite (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) := by
  classical
  let A := Q.adicCompletionIntegers K
  let B := q.adicCompletionIntegers L
  let KQ := Q.adicCompletion K
  let Lq := q.adicCompletion L
  haveI hAcomp : CompactSpace A :=
    Commons.NumberTheory.NumberField.Completion.compactSpace_adicCompletionIntegers K Q
  let φ : A →+* B :=
    (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
          (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
  letI : Algebra A B := RingHom.toAlgebra φ
  have hval : ∀ a : A, ((algebraMap A B a : B) : Lq) =
      Commons.RingTheory.Henselian.adicCompletionMap Q q hq (a : KQ) := by
    intro a
    show (((RingHom.toAlgebra φ).algebraMap a : B) : Lq) = _
    rw [RingHom.algebraMap_toAlgebra]
    rfl
  have halg : Continuous (algebraMap A B) := by
    have h1 : Continuous (fun a : A =>
        (Commons.RingTheory.Henselian.adicCompletionMap Q q hq (a : KQ) : Lq)) :=
      (Commons.RingTheory.Henselian.adicCompletionMap_continuous Q q hq).comp continuous_subtype_val
    have h2 : (algebraMap A B) = fun a : A =>
        (⟨Commons.RingTheory.Henselian.adicCompletionMap Q q hq (a : KQ),
          Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq a.2⟩ : B) := by
      funext a
      rw [RingHom.algebraMap_toAlgebra]
      rfl
    rw [h2]
    exact Continuous.subtype_mk h1 _
  have key : ∀ c : 𝓞 K,
      ((algebraMap A B (algebraMap (𝓞 K) A c) : B) : Lq) =
        algebraMap L Lq (algebraMap (𝓞 K) L c) := by
    intro c
    rw [hval]
    have h1 : ((algebraMap (𝓞 K) A c : A) : KQ) = ((c : K) : KQ) :=
      HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply ..
    rw [h1, Commons.RingTheory.Henselian.adicCompletionMap_apply]
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K L c]
    rfl
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 K) (𝓞 L)
  let u : Fin n → 𝓞 L := fun i => f (Pi.single i 1)
  have hdecomp : ∀ v : Fin n → 𝓞 K, f v = ∑ i, v i • u i := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsingle : Pi.single i (v i) = v i • (Pi.single i (1 : 𝓞 K)) := by
      ext j
      rw [Pi.smul_apply]
      by_cases h : j = i
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [hsingle, map_smul]
  let β : Fin n → B := fun i => algebraMap (𝓞 L) B (u i)
  have hbeta : ∀ i, ((β i : B) : Lq) = algebraMap L Lq (algebraMap (𝓞 L) L (u i)) := by
    intro i
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    rfl
  let g : (Fin n → A) →ₗ[A] B :=
    { toFun := fun a => ∑ i, algebraMap A B (a i) * β i
      map_add' := by
        intro a b
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, map_add, add_mul]
      map_smul' := by
        intro c a
        conv_rhs => rw [Algebra.smul_def]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (c • a) i = c * a i by simp, map_mul, RingHom.id_apply, mul_assoc] }
  have hgc : Continuous (fun a : Fin n → A => (g a : Lq)) := by
    have hfun : (fun a : Fin n → A => (g a : Lq)) =
        fun a => ∑ i, (algebraMap A B (a i) : Lq) * ((β i : B) : Lq) := by
      funext a
      show (((∑ i, algebraMap A B (a i) * β i : B)) : Lq) = _
      rw [show ((∑ i, algebraMap A B (a i) * β i : B) : Lq)
        = ∑ i, ((algebraMap A B (a i) * β i : B) : Lq) from map_sum B.subtype _ Finset.univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact map_mul B.subtype _ _
    rw [hfun]
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_subtype_val.comp (halg.comp (continuous_apply i))).mul continuous_const
  have hsurj : Function.Surjective g := by
    intro b
    set S : Set Lq := {y | ∃ r : 𝓞 L, algebraMap L Lq (algebraMap (𝓞 L) L r) = y} with hSdef
    have hbcl : (b : Lq) ∈ closure S := by
      have h := Commons.NumberTheory.NumberField.Completion.ringOfIntegers_dense_in_adicIntegers L q b
      simpa [S] using h
    have hSsub : S ⊆ Set.range (fun a : Fin n → A => (g a : Lq)) := by
      rintro y ⟨r, hr⟩
      rw [← hr]
      obtain ⟨v, hv⟩ := hf r
      refine ⟨fun i => algebraMap (𝓞 K) A (v i), ?_⟩
      change (g (fun i => algebraMap (𝓞 K) A (v i)) : Lq) =
        algebraMap L Lq (algebraMap (𝓞 L) L r)
      have step1 : (g (fun i => algebraMap (𝓞 K) A (v i)) : Lq) =
          ∑ i, (algebraMap A B (algebraMap (𝓞 K) A (v i)) : Lq) * ((β i : B) : Lq) := by
        show (((∑ i, algebraMap A B (algebraMap (𝓞 K) A (v i)) * β i : B)) : Lq) = _
        rw [show ((∑ i, algebraMap A B (algebraMap (𝓞 K) A (v i)) * β i : B) : Lq)
          = ∑ i, ((algebraMap A B (algebraMap (𝓞 K) A (v i)) * β i : B) : Lq) from
            map_sum B.subtype _ Finset.univ]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact map_mul B.subtype _ _
      rw [step1]
      rw [show (∑ i, (algebraMap A B (algebraMap (𝓞 K) A (v i)) : Lq) * ((β i : B) : Lq))
          = ∑ i, algebraMap L Lq (algebraMap (𝓞 K) L (v i)) *
              algebraMap L Lq (algebraMap (𝓞 L) L (u i)) from
          Finset.sum_congr rfl fun i _ => by rw [key, hbeta]]
      rw [show (∑ i, algebraMap L Lq (algebraMap (𝓞 K) L (v i)) *
              algebraMap L Lq (algebraMap (𝓞 L) L (u i)))
          = ∑ i, algebraMap L Lq (algebraMap (𝓞 K) L (v i) *
              algebraMap (𝓞 L) L (u i)) from
          Finset.sum_congr rfl fun i _ => (map_mul _ _ _).symm]
      rw [← map_sum]
      congr 1
      rw [← hv, hdecomp, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L (v i)]
    have hclosed : IsClosed (Set.range (fun a : Fin n → A => (g a : Lq))) :=
      (isCompact_range hgc).isClosed
    have hmem : (b : Lq) ∈ Set.range (fun a : Fin n → A => (g a : Lq)) :=
      closure_minimal hSsub hclosed hbcl
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, Subtype.ext ha⟩
  exact Module.Finite.of_surjective g hsurj

end Commons.NumberTheory.NumberField.Completion