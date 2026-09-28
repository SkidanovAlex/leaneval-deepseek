import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.HP.ballCount_le_pow_rk

/-!
# `Work.Q44Geom.latW_count`

For `f : ℚ[X₀,…,X₄]` whose invariance subspace
`invSub f = {w | ∀ x t, f (x + t • w) = f x}` has `ℚ`-dimension at most `3`, the number of
integral vectors `v ∈ ℤ⁵` lying in the invariance lattice `latW f` (those `v` with
`toRatLM v ∈ invSub f`) and of Euclidean norm at most `T` grows at most like `(1+T)³`.

The two ingredients are

* `latW_rank_le`: the `ℤ`-rank of `latW f` is at most the `ℚ`-dimension of `invSub f`
  (a `ℤ`-linearly independent family of integral vectors stays `ℚ`-linearly independent);
* `Work.HP.ballCount_le_pow_rk`: the uniform lattice point bound
  `#(L ∩ B(T)) ≤ K (T+1)^(rk L)`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

open MvPolynomial

/-- The coefficientwise coercion `ℤ^5 → ℚ^5` is injective. -/
private lemma toRatLM_injective : Function.Injective toRatLM := by
  intro u v h
  funext i
  have h' : ((u i : ℤ) : ℚ) = ((v i : ℤ) : ℚ) := congrFun h i
  exact Int.cast_injective h'

/-- The integral invariance lattice `latW f` has `ℤ`-rank at most the `ℚ`-dimension of the
invariance subspace `invSub f`.

Indeed, a `ℤ`-basis of `latW f` is `ℤ`-linearly independent, hence (being integral) also
`ℚ`-linearly independent after coercion to `ℚ⁵`; its spanned `ℚ`-subspace lies in `invSub f`,
so its cardinality is at most `finrank ℚ (invSub f)`. -/
theorem latW_rank_le (f : MvPolynomial (Fin 5) ℚ) :
    Work.HP.rk (latW f) ≤ Module.finrank ℚ (invSub f) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin 5)) (latW f)
  have hn : Work.HP.rk (latW f) = n := by
    rw [Work.HP.rk, Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hb : LinearIndependent ℤ (fun i : Fin n => (b i : Fin 5 → ℤ)) :=
    b.linearIndependent.map' (Submodule.subtype (latW f)) (Submodule.ker_subtype _)
  have hz : LinearIndependent ℤ (fun i : Fin n => toRatLM ((b i : Fin 5 → ℤ))) :=
    hb.map' toRatLM ((LinearMap.ker_eq_bot).mpr toRatLM_injective)
  have hq : LinearIndependent ℚ (fun i : Fin n => toRatLM ((b i : Fin 5 → ℤ))) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp hz
  have hmem : ∀ i : Fin n, toRatLM ((b i : Fin 5 → ℤ)) ∈ invSub f :=
    fun i => mem_latW_iff.mp (b i).2
  have hspan : Submodule.span ℚ (Set.range (fun i : Fin n => toRatLM ((b i : Fin 5 → ℤ))))
      ≤ invSub f :=
    Submodule.span_le.mpr (by rintro x ⟨i, rfl⟩; exact hmem i)
  have hfin : Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun i : Fin n => toRatLM ((b i : Fin 5 → ℤ))))) = n :=
    by rw [finrank_span_eq_card hq, Fintype.card_fin]
  calc Work.HP.rk (latW f) = n := hn
    _ = Module.finrank ℚ
          (Submodule.span ℚ (Set.range (fun i : Fin n => toRatLM ((b i : Fin 5 → ℤ))))) :=
        hfin.symm
    _ ≤ Module.finrank ℚ (invSub f) := Submodule.finrank_mono hspan

theorem latW_count (f : MvPolynomial (Fin 5) ℚ)
    (hf : Module.finrank ℚ (Work.Q44Geom.invSub f) ≤ 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (({v : Fin 5 → ℤ | v ∈ Work.Q44Geom.latW f ∧ Work.HP.eNorm v ≤ T} : Set (Fin 5 → ℤ)).ncard : ℝ)
        ≤ C * (1 + T) ^ 3 := by
  obtain ⟨K, hKpos, hK⟩ := Work.HP.ballCount_le_pow_rk (ι := Fin 5)
  refine ⟨K, hKpos, ?_⟩
  intro T hT1
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT1
  have hb := hK (latW f) T hT0
  have hrk : Work.HP.rk (latW f) ≤ 3 := le_trans (latW_rank_le f) hf
  have hball : Work.HP.ballCount (latW f) T
      = ({v : Fin 5 → ℤ | v ∈ Work.Q44Geom.latW f ∧ Work.HP.eNorm v ≤ T} :
          Set (Fin 5 → ℤ)).ncard := rfl
  rw [← hball]
  refine le_trans hb ?_
  have h1 : (1 : ℝ) ≤ T + 1 := by linarith
  have hpow : (T + 1) ^ (Work.HP.rk (latW f)) ≤ (T + 1) ^ 3 :=
    pow_le_pow_right₀ h1 hrk
  calc K * (T + 1) ^ (Work.HP.rk (latW f)) ≤ K * (T + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow hKpos.le
    _ = K * (1 + T) ^ 3 := by rw [add_comm]

end Work.Q44Geom
