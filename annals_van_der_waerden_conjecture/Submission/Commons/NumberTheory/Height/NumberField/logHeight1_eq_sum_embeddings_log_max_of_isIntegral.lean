import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.NumberTheory.Height.NumberField

open scoped Classical NumberField

namespace Commons.NumberTheory.Height.NumberField

/-- The sum over the complex embeddings `σ : K →+* ℂ` of `g ‖σ x‖` equals the sum over the
infinite places `w` of `K`, weighted by the multiplicity `w.mult`, of `g (w x)`.

This is because the complex embeddings are partitioned by `σ ↦ InfinitePlace.mk σ`, whose fibers
are of cardinality `w.mult` (`InfinitePlace.card_filter_mk_eq`), and on each fiber the norm
`‖σ x‖` is constantly equal to `w x` (`InfinitePlace.apply`). -/
theorem sum_embeddings_eq_sum_infinitePlace_mult {K : Type*} [Field K] [NumberField K]
    (x : K) (g : ℝ → ℝ) :
    (∑ σ : K →+* ℂ, g ‖σ x‖)
      = ∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * g (w x) := by
  classical
  rw [← Fintype.sum_fiberwise (fun σ : K →+* ℂ => NumberField.InfinitePlace.mk σ)
        (fun σ => g ‖σ x‖)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hterm : ∀ σ : {σ : K →+* ℂ // NumberField.InfinitePlace.mk σ = w},
      g ‖σ.1 x‖ = g (w x) := by
    intro σ
    congr 1
    rw [← NumberField.InfinitePlace.apply σ.1 x, σ.2]
  rw [Finset.sum_congr rfl (fun σ (_ : σ ∈ Finset.univ) => hterm σ), Finset.sum_const,
    Finset.card_univ, Fintype.card_subtype, NumberField.InfinitePlace.card_filter_mk_eq,
    nsmul_eq_mul]

/-- The value of every finite place of a number field at an element integral over `ℤ` is at
most `1`. -/
lemma finitePlace_apply_le_one_of_isIntegral {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : IsIntegral ℤ x) (v : NumberField.FinitePlace K) : v x ≤ 1 := by
  have h := NumberField.FinitePlace.norm_le_one K v.maximalIdeal (⟨x, hx⟩ : 𝓞 K)
  have hxK : (algebraMap (𝓞 K) K (⟨x, hx⟩ : 𝓞 K)) = x := rfl
  rw [hxK] at h
  rwa [← NumberField.FinitePlace.norm_embedding_eq v x]

/-- For an element `x` of a number field that is integral over `ℤ`, the logarithmic height
`logHeight₁ x` is the sum over all complex embeddings `σ` of `log (max 1 ‖σ x‖)`: the contribution
of the finite places vanishes, and the archimedean contribution is the sum over the infinite
places weighted by multiplicity. -/
theorem logHeight1_eq_sum_embeddings_log_max_of_isIntegral {K : Type*} [Field K] [NumberField K]
    {x : K} (hx : IsIntegral ℤ x) :
    Height.logHeight₁ x = ∑ σ : K →+* ℂ, Real.log (max 1 ‖σ x‖) := by
  classical
  rw [NumberField.logHeight₁_eq]
  have hfin : (∑ᶠ v : NumberField.FinitePlace K, (v x).posLog) = 0 := by
    refine finsum_eq_zero_of_forall_eq_zero (fun v => ?_)
    rw [Real.posLog_eq_zero_iff]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ v x from v.1.nonneg x)]
    exact finitePlace_apply_le_one_of_isIntegral hx v
  rw [hfin, add_zero]
  rw [sum_embeddings_eq_sum_infinitePlace_mult x (fun y => Real.log (max 1 y))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  have hw : (w x).posLog = Real.log (max 1 (w x)) := Real.posLog_eq_log_max_one (w.1.nonneg x)
  rw [hw]

end Commons.NumberTheory.Height.NumberField