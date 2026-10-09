import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionExtension
import Submission.Work.LocalFields.nonempty_galois_completion_equiv
import Submission.Work.LocalFields.completion_algebraMap_mem_intRing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero Topology

theorem hasExtension_completion {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    Valuation.HasExtension (Valued.v (R := Work.LocalFields.Completion K v))
      (Valued.v (R := Work.LocalFields.Completion L w)) := by
  classical
  -- The value of the `v`-adic valuation on elements of `K ⊂ K_v`, and likewise for `L_w`.
  have hvalK : ∀ k : K,
      Valued.v (R := Completion K v) (algebraMap K (Completion K v) k) = v.valuation K k := by
    intro k
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K v k
  have hvalL : ∀ k : K,
      Valued.v (R := Completion L w) (algebraMap K (Completion L w) k)
        = w.valuation L (algebraMap K L k) := by
    intro k
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe L w (algebraMap K L k)
  -- The two valuations agree (up to equivalence) on the dense subfield `K`.
  have hisoK : ∀ k : K,
      (v.valuation K k ≤ 1 ↔ (w.valuation L) (algebraMap K L k) ≤ 1) :=
    fun k => (Valuation.isEquiv_iff_val_le_one.mp (valuation_isEquiv_of_liesOver v w))
  refine Valuation.HasExtension.mk ?_
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [Valuation.comap_apply]
  constructor
  · -- `x ∈ 𝒪_{K_v}` implies `φ x ∈ 𝒪_{L_w}`
    intro hx
    exact completion_algebraMap_mem_intRing v w x hx
  · -- conversely, if `φ x ∈ 𝒪_{L_w}` then `x ∈ 𝒪_{K_v}`
    intro hx
    by_contra hcon
    have hcon' : (1 : ℤᵐ⁰) < Valued.v (R := Completion K v) x := lt_of_not_ge hcon
    -- Density of `K` in `K_v`: approximate `x` by an element of `K` inside the open unit ball.
    have hDense : DenseRange (algebraMap K (Completion K v)) :=
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v
    have hT : {y : Completion K v | Valued.v (R := Completion K v) (y - x) < 1} ∈ 𝓝 x := by
      rw [Valued.mem_nhds]
      refine ⟨1, ?_⟩
      intro y hy
      simp only [Set.mem_ofPred_eq] at hy ⊢
      rw [Valuation.restrict_lt_iff_lt_embedding] at hy
      simpa using hy
    obtain ⟨k, hk⟩ := hDense.mem_nhds hT
    simp only [Set.mem_ofPred_eq] at hk
    -- `v_K (ι k) = v_K x > 1`
    have hkx : Valued.v (R := Completion K v) (algebraMap K (Completion K v) k)
        = Valued.v (R := Completion K v) x := by
      have h : algebraMap K (Completion K v) k
          = x + (algebraMap K (Completion K v) k - x) := by ring
      rw [h]
      exact Valuation.map_add_eq_of_lt_left _ (lt_trans hk hcon')
    have hkx' : (1 : ℤᵐ⁰) < Valued.v (R := Completion K v) (algebraMap K (Completion K v) k) := by
      rw [hkx]; exact hcon'
    -- hence `v_L (φ (ι k)) = w(algebraMap L k) > 1`
    have hLk : (1 : ℤᵐ⁰) < Valued.v (R := Completion L w) (algebraMap K (Completion L w) k) := by
      have hvK : ¬ ((v.valuation K) k ≤ 1) := by
        rw [← hvalK k, hkx]; exact not_le.mpr hcon'
      have hvL : ¬ ((w.valuation L) (algebraMap K L k) ≤ 1) := fun h => hvK ((hisoK k).mpr h)
      rw [hvalL k]
      exact not_le.mp hvL
    -- identify the two copies of `ι k`
    have hcomp : algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k)
        = algebraMap K (Completion L w) k :=
      (IsScalarTower.algebraMap_apply K (Completion K v) (Completion L w) k).symm
    have hLk' : (1 : ℤᵐ⁰) < Valued.v (R := Completion L w)
        (algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k)) := by
      rw [hcomp]; exact hLk
    -- `φ (ι k - x)` is integral, so `φ x` and `φ (ι k)` have the same valuation `> 1`
    have hsub : Valued.v (R := Completion L w)
        (algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k - x)) ≤ 1 :=
      completion_algebraMap_mem_intRing v w _ (le_of_lt hk)
    have hdiff : Valued.v (R := Completion L w)
        (algebraMap (Completion K v) (Completion L w) x
          - algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k)) ≤ 1 := by
      have key : algebraMap (Completion K v) (Completion L w) x
          - algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k)
          = - (algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k - x)) := by
        rw [← map_sub, show x - algebraMap K (Completion K v) k
            = - (algebraMap K (Completion K v) k - x) from by ring, map_neg]
      rw [key, Valuation.map_neg]
      exact hsub
    have hxval : Valued.v (R := Completion L w) (algebraMap (Completion K v) (Completion L w) x)
        = Valued.v (R := Completion L w)
            (algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k)) := by
      rw [show algebraMap (Completion K v) (Completion L w) x
            = algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k)
              + (algebraMap (Completion K v) (Completion L w) x
                 - algebraMap (Completion K v) (Completion L w) (algebraMap K (Completion K v) k))
            from by ring]
      exact Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hdiff hLk')
    exact absurd hx (not_le.mpr (hxval ▸ hLk'))

end Work.LocalFields
