import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.CompactDefs
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_unit_logEmbedding_bound
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_unitLattice_approx
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_principalIdele_unit_ofFinite_norm_one
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_normOne_archimedean_sum

/-!
# The archimedean adjustment of a norm-one idèle by a unit

Let `K` be a number field, `S` a finite set of nonarchimedean places and `C₀ ≥ 1`.  The purpose
of this file is the following step of the proof that the norm-one idèle class group `C¹_K` is
compact: every norm-one idèle `y` which is *bounded-integral* for `(S, C₀)` (a local unit outside
`S`, integral at every finite place, bounded below by `C₀⁻¹` on `S`) can be multiplied by a
principal idèle coming from the **global units** `(𝓞 K)ˣ` in such a way that all its archimedean
components land in a fixed annulus `[C⁻¹, C]`, with `C` depending only on `S` and `C₀`.

The finite components are untouched by this operation (a global unit is a local unit everywhere,
so the corresponding principal idèle has norm `1` at every finite place), and the possibility of
adjusting the archimedean components is Dirichlet's unit theorem in its covering-radius form:
the logarithmic image of `(𝓞 K)ˣ` is a lattice of full rank in the hyperplane
`{b : ∑_w b_w = 0}` of `∏_w ℝ`, so there is a constant `R` such that every vector of that
hyperplane is within distance `R` of the logarithmic image of a unit
(`NK.GlobalCFT.IdeleClassGroup.globalCFT_unitLattice_approx`).

The archimedean logarithmic sum of `y` itself is controlled by the content formula: for `y` of
content one and bounded-integral for `(S, C₀)` it equals `-∑_{q ∈ S} log ‖y_q‖`, hence lies in
`[0, |S| log C₀]` (`NK.GlobalCFT.IdeleClassGroup.globalCFT_normOne_archimedean_sum`).

## Main result

* `NK.GlobalCFT.IdeleClassGroup.globalCFT_exists_unit_archimedean`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.IdeleClassGroup

variable {K : Type*} [Field K] [NumberField K]

/-- The norm of the image of `x : K` in the completion at an infinite place `w` is the infinite
absolute value `w x`. -/
lemma norm_algebraMap_completion (w : InfinitePlace K) (x : K) :
    ‖(algebraMap K w.Completion x : w.Completion)‖ = w x := by
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
  simpa [WithAbs.toAbs] using
    (NumberField.InfinitePlace.Completion.norm_coe (v := w) (WithAbs.toAbs w.1 x))

/-- The archimedean component of a principal idèle is the corresponding global absolute value. -/
lemma norm_principalIdele_infinite (k : Kˣ) (w : InfinitePlace K) :
    ‖(NK.GlobalCFT.Idele.principalIdele K k (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖
      = w (k : K) := by
  rw [NK.GlobalCFT.Idele.principalIdele_apply, Units.coe_map]
  exact norm_algebraMap_completion w (k : K)

/-- **The real-analytic core of the archimedean adjustment.**  If the logarithmic archimedean
sum `T = ∑_w mult_w log ‖y_w‖` of an idèle is nonnegative and bounded by `M`, then any unit whose
logarithmic vector is within `R` (in the `w₀`-coordinate) of the vector
`T/N - (mult_w log ‖y_w‖)_w` puts every archimedean component of the product in the annulus
`[exp (-(R + M/N)), exp (R + M/N)]`. -/
private lemma arch_bound {T M R a : ℝ} {m N : ℕ} {z : ℝ}
    (hTM : T ≤ M) (hT0 : 0 ≤ T) (hN : 0 < N) (hm : 1 ≤ (m:ℝ))
    (ha : |a - T / (N:ℝ)| ≤ R) (hz : 0 < z) (ha_def : a = (m:ℝ) * Real.log z) :
    Real.exp (-(R + M / N)) ≤ z ∧ z ≤ Real.exp (R + M / N) := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hTn : T / (N:ℝ) ≤ M / N := div_le_div_of_nonneg_right hTM (le_of_lt hN0)
  have hTn0 : 0 ≤ T / (N:ℝ) := div_nonneg hT0 (le_of_lt hN0)
  have habs : |a| ≤ R + M / N := by
    have h2 : |a| = |(a - T/(N:ℝ)) + T/(N:ℝ)| := by rw [sub_add_cancel]
    have h : |a| ≤ |a - T/(N:ℝ)| + |T/(N:ℝ)| := by
      rw [h2]; exact abs_add_le _ _
    rw [abs_of_nonneg hTn0] at h
    linarith
  have hm0 : (0:ℝ) < m := by positivity
  have hlog : |Real.log z| ≤ R + M / N := by
    have hz' : Real.log z = a / (m:ℝ) := by rw [ha_def]; field_simp
    rw [hz', abs_div, abs_of_nonneg (le_of_lt hm0)]
    calc |a| / (m:ℝ) ≤ |a| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos hm
      _ = |a| := by rw [div_one]
      _ ≤ R + M / N := habs
  obtain ⟨h1, h2⟩ := abs_le.mp hlog
  refine ⟨?_, ?_⟩
  · have hh := Real.exp_le_exp.mpr h1
    rw [Real.exp_log hz] at hh
    simpa [Real.exp_neg] using hh
  · rw [← Real.exp_log hz]; exact Real.exp_le_exp.mpr h2

theorem globalCFT_exists_unit_archimedean {K : Type*} [Field K] [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ y : NK.GlobalCFT.Idele K, y ∈ NK.GlobalCFT.Idele.normOne K →
      NK.GlobalCFT.IdeleClassGroup.IsBoundedIntegral K S C₀ y →
      ∃ k : Kˣ,
        (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          ‖((NK.GlobalCFT.Idele.principalIdele K k) (NK.GlobalCFT.Place.ofFinite q) :
            q.adicCompletion K)‖ = 1) ∧
        ∀ w : NumberField.InfinitePlace K,
          C⁻¹ ≤ ‖((NK.GlobalCFT.Idele.principalIdele K k * y)
            (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ ∧
          ‖((NK.GlobalCFT.Idele.principalIdele K k * y)
            (NK.GlobalCFT.Place.ofInfinite w) : w.Completion)‖ ≤ C := by
  classical
  -- Dirichlet's unit theorem in covering-radius form.
  obtain ⟨R, hR0, hR⟩ := globalCFT_unitLattice_approx (K := K)
  have hNpos : 0 < Fintype.card (InfinitePlace K) :=
    Fintype.card_pos_iff.mpr ⟨NumberField.Units.dirichletUnitTheorem.w₀ (K := K)⟩
  -- The annulus radius: it only involves the size of `S`, the constant `C₀` and the number of
  -- archimedean places.
  refine ⟨Real.exp (R + (S.card : ℝ) * Real.log C₀ / (Fintype.card (InfinitePlace K) : ℝ)),
    ?_, ?_⟩
  · rw [← Real.exp_zero]; apply Real.exp_le_exp.mpr
    have h1 : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
    have h2 : (0:ℝ) ≤ (S.card : ℝ) * Real.log C₀ / (Fintype.card (InfinitePlace K) : ℝ) := by
      positivity
    linarith
  · intro y hy hbd
    -- The logarithmic archimedean sum `T` of `y` and its bounds.
    obtain ⟨hsum, hT0raw, hTMraw⟩ := globalCFT_normOne_archimedean_sum S hC₀ hy hbd
    set T : ℝ := ∑ w : InfinitePlace K,
      (w.mult : ℝ) * Real.log ‖(y (Place.ofInfinite w) : w.Completion)‖ with hT
    have hT0 : 0 ≤ T := by rw [hT]; exact hT0raw
    have hTM : T ≤ (S.card : ℝ) * Real.log C₀ := by rw [hT]; exact hTMraw
    -- The vector to be approximated has vanishing coordinate sum.
    have hb : ∑ w : InfinitePlace K,
        (T / (Fintype.card (InfinitePlace K) : ℝ)
          - (w.mult : ℝ) * Real.log ‖(y (Place.ofInfinite w) : w.Completion)‖) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hT]
      have hN0 : ((Fintype.card (InfinitePlace K) : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_gt hNpos
      field_simp
      ring
    obtain ⟨u, hu⟩ := hR (fun w => T / (Fintype.card (InfinitePlace K) : ℝ)
        - (w.mult : ℝ) * Real.log ‖(y (Place.ofInfinite w) : w.Completion)‖) hb
    set k : Kˣ := Units.map (algebraMap (𝓞 K) K) u with hk
    refine ⟨k, ?_, ?_⟩
    · -- The finite components are those of a global unit: they have norm one.
      intro q
      rw [hk]
      exact globalCFT_principalIdele_unit_ofFinite_norm_one u q
    · -- The archimedean components land in the annulus.
      intro w
      set z : w.Completionˣ := (NK.GlobalCFT.Idele.principalIdele K k * y) (Place.ofInfinite w)
        with hzdef
      have hznorm : ‖(z : w.Completion)‖
          = ‖(NK.GlobalCFT.Idele.principalIdele K k (Place.ofInfinite w) : w.Completion)‖
            * ‖(y (Place.ofInfinite w) : w.Completion)‖ := by
        show ‖((NK.GlobalCFT.Idele.principalIdele K k * y) (Place.ofInfinite w) :
          w.Completion)‖ = _
        rw [NK.GlobalCFT.Idele.mul_apply, Units.val_mul, norm_mul]
      have hknorm : ‖(NK.GlobalCFT.Idele.principalIdele K k (Place.ofInfinite w) : w.Completion)‖
          = w (u : K) := by
        rw [hk, NK.GlobalCFT.Idele.principalIdele_apply, Units.coe_map]
        exact norm_algebraMap_completion w (algebraMap (𝓞 K) K (u:𝓞 K))
      have hpos1 : 0 < w (u : K) := by
        rw [← hknorm]; exact norm_pos_iff.mpr (Units.ne_zero _)
      have hpos2 : 0 < ‖(y (Place.ofInfinite w) : w.Completion)‖ :=
        norm_pos_iff.mpr (Units.ne_zero _)
      have hadef : (w.mult : ℝ) * Real.log ‖(z : w.Completion)‖
          = (w.mult : ℝ) * Real.log (w (u : K))
            + (w.mult : ℝ) * Real.log ‖(y (Place.ofInfinite w) : w.Completion)‖ := by
        rw [hznorm, hknorm, Real.log_mul (ne_of_gt hpos1) (ne_of_gt hpos2)]
        ring
      have hab : |(w.mult : ℝ) * Real.log ‖(z : w.Completion)‖
            - T / (Fintype.card (InfinitePlace K) : ℝ)| ≤ R := by
        have huw := hu w
        have hEq : (w.mult : ℝ) * Real.log ‖(z : w.Completion)‖
              - T / (Fintype.card (InfinitePlace K) : ℝ)
            = - ((T / (Fintype.card (InfinitePlace K) : ℝ)
                - (w.mult : ℝ) * Real.log ‖(y (Place.ofInfinite w) : w.Completion)‖)
              - (w.mult : ℝ) * Real.log (w (u : K))) := by
          rw [hadef]; ring
        rw [hEq, abs_neg]
        exact huw
      have hmain := arch_bound (R := R) (a := (w.mult : ℝ) * Real.log ‖(z : w.Completion)‖)
        (m := w.mult) (N := Fintype.card (InfinitePlace K)) (z := ‖(z : w.Completion)‖)
        hTM hT0 hNpos (NumberField.InfinitePlace.one_le_mult (w := w)) hab
        (norm_pos_iff.mpr (Units.ne_zero z)) rfl
      refine ⟨?_, ?_⟩
      · rw [← Real.exp_neg]; exact hmain.1
      · exact hmain.2

end NK.GlobalCFT.IdeleClassGroup
