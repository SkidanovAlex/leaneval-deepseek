import Mathlib
import Submission.Work.SSGRoute.PTembedding.exists_galois_degree_pow_dvd_of_uniformizer
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-!
# Superlevels of finite Galois levels of a finite extension of a `p`-adic field with
`p`-divisible index

Let `K` be a number field, `Q` a finite place of `K`, `F` a finite extension of the `Q`-adic
completion `K_Q` and `L / F` a finite Galois level.  Then `L` has a finite Galois superlevel `L'`
whose relative degree `[L' : L]` is divisible by `p`; equivalently
`[L : F] * p ∣ [L' : F]`.

For the construction one needs *some* element `π ∈ F` and valuation `w` of `F` with values in
`WithZero (Multiplicative ℤ)` such that `w π = exp (-1)` — the lemma
`Work.SSGRoute.PTembedding.exists_galois_degree_pow_dvd_of_uniformizer` uses nothing else about
`(w, π)`.  Since the hypotheses give no valuation of `F`, we realise `F` as the completion
`L_q` of a number field `L` (`exists_algEquiv_adicCompletion_of_finiteDimensional`) and pull back
the `q`-adic valuation and a uniformizer of `L_q` along the resulting isomorphism.

For `N = v_p ([L : F]) + 1` that lemma produces a finite Galois `E / F` with `p ^ N ∣ [E : F]`;
then `L' = L ⊔ E` satisfies `[L : F] ∣ [L' : F]` and `p ^ (v_p([L:F]) + 1) ∣ [E : F] ∣ [L' : F]`,
which forces `[L : F] * p ∣ [L' : F]`.
-/

namespace Work.SSGRoute.PTfin

/-- Arithmetic: if `n ≠ 0`, `n ∣ m` and `p ^ (v_p n + 1) ∣ m`, then `n * p ∣ m`. -/
private lemma mul_prime_dvd_of_dvd_of_pow_padicValNat_succ_dvd {p n m : ℕ} [Fact p.Prime]
    (hn : n ≠ 0) (h1 : n ∣ m) (h2 : p ^ (padicValNat p n + 1) ∣ m) : n * p ∣ m := by
  by_cases hm : m = 0
  · rw [hm]; exact dvd_zero _
  obtain ⟨c, rfl⟩ := h1
  have hc : c ≠ 0 := fun h => hm (by rw [h, mul_zero])
  have hval : padicValNat p (n * c) = padicValNat p n + padicValNat p c :=
    padicValNat.mul hn hc
  have hle : padicValNat p n + 1 ≤ padicValNat p (n * c) :=
    (padicValNat_dvd_iff_le hm).mp h2
  rw [hval] at hle
  exact Nat.mul_dvd_mul_left n (dvd_of_one_le_padicValNat (by omega))

/-- **Enlarging a finite Galois level of a finite extension of a `p`-adic field.** -/
theorem exists_superlevel_p_dvd_index_finiteExtension (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    [NumberField K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F : Type} [Field F] [Algebra (Q.adicCompletion K) F] [FiniteDimensional (Q.adicCompletion K) F]
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    ∃ L' : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      (L : IntermediateField F (AlgebraicClosure F)) ≤ (L' : IntermediateField F (AlgebraicClosure F)) ∧
      Module.finrank F ↥L * p ∣ Module.finrank F ↥L' := by
  classical
  haveI hk : CharZero (Q.adicCompletion K) :=
    charZero_of_injective_algebraMap
      (RingHom.injective (algebraMap ℚ (Q.adicCompletion K)))
  have hInj : Function.Injective (algebraMap (Q.adicCompletion K) F) :=
    RingHom.injective (algebraMap (Q.adicCompletion K) F)
  haveI hFc : CharZero F :=
    CharZero.of_addMonoidHom (algebraMap (Q.adicCompletion K) F).toAddMonoidHom (by simp) hInj
  -- realise `F` as the completion `L₀_q` of a number field
  obtain ⟨L₀ : Type, hL₀f, hL₀n, hL₀a, q, hq, ⟨e⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
      (Q := Q) (B := F)
  letI : Field L₀ := hL₀f
  letI : NumberField L₀ := hL₀n
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L₀) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- a uniformizer of the local field `L₀_q`, and the valuation of `F` and the element of `F` with
  -- value `exp (-1)` obtained by pulling both back along the isomorphism `F ≃ L₀_q`
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer L₀ q
  have hπ' : Valued.v (π : q.adicCompletion L₀) = WithZero.exp (-1) := by
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe, hπ]
  let f : F →+* q.adicCompletion L₀ :=
    { toFun := ⇑e
      map_one' := map_one e
      map_mul' := map_mul e
      map_zero' := map_zero e
      map_add' := map_add e }
  have hf : f (e.symm (π : q.adicCompletion L₀)) = (π : q.adicCompletion L₀) :=
    AlgEquiv.apply_symm_apply e (π : q.adicCompletion L₀)
  let w : Valuation F (WithZero (Multiplicative ℤ)) :=
    Valuation.comap f (Valued.v : Valuation (q.adicCompletion L₀) (WithZero (Multiplicative ℤ)))
  have hw : w (e.symm (π : q.adicCompletion L₀)) = WithZero.exp (-1) := by
    simp only [w, Valuation.comap_apply, hf, hπ']
  -- a finite Galois extension of `F` of degree divisible by `p ^ (v_p [L : F] + 1)`
  obtain ⟨E, hEfin, hEgal, hEdvd⟩ :=
    Work.SSGRoute.PTembedding.exists_galois_degree_pow_dvd_of_uniformizer p
      (padicValNat p (Module.finrank F ↥L) + 1) w (e.symm (π : q.adicCompletion L₀)) hw
  let E' : FiniteGaloisIntermediateField F (AlgebraicClosure F) :=
    { toIntermediateField := E, finiteDimensional := hEfin, isGalois := hEgal }
  refine ⟨L ⊔ E', (FiniteGaloisIntermediateField.le_iff L (L ⊔ E')).mp le_sup_left, ?_⟩
  have hle2 : E ≤ ((L ⊔ E' : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
      IntermediateField F (AlgebraicClosure F)) := le_sup_right
  have hdvd : Module.finrank F ↥L ∣ Module.finrank F ↥(L ⊔ E') :=
    IntermediateField.finrank_dvd_of_le_right
      ((FiniteGaloisIntermediateField.le_iff L (L ⊔ E')).mp le_sup_left)
  have hdvdE : Module.finrank F ↥E ∣ Module.finrank F ↥(L ⊔ E') :=
    IntermediateField.finrank_dvd_of_le_right hle2
  have hn : Module.finrank F ↥L ≠ 0 :=
    ne_of_gt ((Module.finrank_pos_iff_of_free F ↥L).mpr inferInstance)
  exact mul_prime_dvd_of_dvd_of_pow_padicValNat_succ_dvd hn hdvd (hEdvd.trans hdvdE)

end Work.SSGRoute.PTfin
