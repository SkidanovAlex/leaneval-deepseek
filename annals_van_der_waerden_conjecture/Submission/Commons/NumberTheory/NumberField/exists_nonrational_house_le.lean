import Mathlib
import Submission.Commons.Lattice.Minkowski.exists_short_independent
import Submission.Commons.NumberTheory.NumberField.relationLattice_covolume_bound
import Submission.Commons.NumberTheory.NumberField.exists_uniform_ringOfIntegers_basis_house_le

open scoped NumberField BigOperators Classical NNReal ENNReal
attribute [local instance] Classical.propDecidable
open MeasureTheory

/-!
# A small non-rational algebraic integer

For a number field `K` of degree `n ≥ 2` we produce a nonzero algebraic integer `a ∈ 𝓞 K`
which is not rational and whose house is at most `2 ^ (n + 5) · |disc K| ^ (1/(2(n-1)))`.

Strategy: view `𝓞 K` as the lattice `L` in the Euclidean mixed space `E = ℝ^{r₁} × ℂ^{r₂}`.
Minkowski's theorem in the form `Commons.Lattice.Minkowski.exists_short_independent`, applied
with `j = 2` and `V = √|disc K|`, yields two `ℝ`-linearly independent lattice vectors of norm
at most

  `(4 ^ n · V / vol)^{1/(n-1)} + 1`,

where the covolume of `L` is `2^{-r₂} √|disc K|`
(`Commons.NumberTheory.NumberField.covolume_euclidean_integerLattice`) and the volume `vol` of
the unit ball of `E` is at least `2^{r₁} π^{r₂} n^{-n/2}`: indeed the product of the disks and
intervals `mixedEmbedding.convexBodyLT` with all radii `n^{-1/2}` has precisely this volume and
is contained in the unit ball.  Two independent vectors cannot both be rational multiples of
`1`, so one of them is non-rational, and its house is bounded by its Euclidean norm.
The numerical estimate `(4 ^ n / vol)^{1/(n-1)} ≤ (4√n)^{n/(n-1)} ≤ (4√n)^2 = 16n ≤ 2^{n+4}`
finishes the proof.
-/

namespace Commons.NumberTheory.NumberField

noncomputable section

/-- The Euclidean mixed space of `K`. -/
abbrev EuMix (K : Type*) [Field K] [NumberField K] : Type _ :=
  NumberField.mixedEmbedding.euclidean.mixedSpace K

/-- The image of the ring of integers in the Euclidean mixed space. -/
abbrev EuInt (K : Type*) [Field K] [NumberField K] : Submodule ℤ (EuMix K) :=
  NumberField.mixedEmbedding.euclidean.integerLattice K

/-- The identifications of the Euclidean mixed space with the mixed space. -/
abbrev toMix (K : Type*) [Field K] [NumberField K] : EuMix K ≃L[ℝ] NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.mixedEmbedding.euclidean.toMixed K

/-- The unit ball of the Euclidean mixed space has volume at least
`2 ^ r₁ * π ^ r₂ / (√n)^n` (in the multiplicative form used below). -/
lemma two_rpow_mul_pi_rpow_le_volume_mul_sqrt_pow (K : Type*) [Field K] [NumberField K] :
    (2 : ℝ) ^ (NumberField.InfinitePlace.nrRealPlaces K) *
        Real.pi ^ (NumberField.InfinitePlace.nrComplexPlaces K) ≤
      (volume (Metric.closedBall (0 : EuMix K) 1)).toReal *
        (Real.sqrt (Module.finrank ℚ K : ℝ)) ^ (Module.finrank ℚ K) := by
  classical
  set n : ℕ := Module.finrank ℚ K with hn
  have hnposR : (0:ℝ) < (n:ℝ) := by
    rw [hn]; exact_mod_cast Module.finrank_pos
  have hsqrtpos : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnposR
  let c : ℝ≥0 := ⟨(Real.sqrt (n:ℝ))⁻¹, by positivity⟩
  let f : NumberField.InfinitePlace K → ℝ≥0 := fun _ => c
  have hfval : ∀ w : NumberField.InfinitePlace K, ((f w : ℝ≥0) : ℝ) = (Real.sqrt (n:ℝ))⁻¹ :=
    fun _ => rfl
  -- volume of the convex body
  have hfactorR : ((NumberField.mixedEmbedding.convexBodyLTFactor K : ℝ≥0) : ℝ) =
      (2:ℝ)^(NumberField.InfinitePlace.nrRealPlaces K) *
        Real.pi^(NumberField.InfinitePlace.nrComplexPlaces K) := by
    rw [NumberField.mixedEmbedding.convexBodyLTFactor, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_pow]
    norm_cast
  have hprodR : ((∏ w : NumberField.InfinitePlace K, (f w) ^ w.mult : ℝ≥0) : ℝ) =
      ((Real.sqrt (n:ℝ))⁻¹)^n := by
    rw [NNReal.coe_prod]
    simp only [NNReal.coe_pow, hfval]
    rw [Finset.prod_pow_eq_pow_sum, NumberField.InfinitePlace.sum_mult_eq, ← hn]
  have hvol : volume (NumberField.mixedEmbedding.convexBodyLT K f) =
      ENNReal.ofReal ((2:ℝ)^(NumberField.InfinitePlace.nrRealPlaces K) *
        Real.pi^(NumberField.InfinitePlace.nrComplexPlaces K) *
        ((Real.sqrt (n:ℝ))⁻¹)^n) := by
    rw [NumberField.mixedEmbedding.convexBodyLT_volume]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ _)]
    congr 1
    rw [hprodR, hfactorR]
  -- the preimage is contained in the unit ball
  have hsub : (toMix K) ⁻¹'
        (NumberField.mixedEmbedding.convexBodyLT K f) ⊆
      Metric.closedBall (0 : EuMix K) 1 := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsup : ‖(toMix K) x‖ ≤ (Real.sqrt (n:ℝ))⁻¹ := by
      rw [NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace]
      refine Finset.sup'_le Finset.univ_nonempty
        (fun w : NumberField.InfinitePlace K =>
          NumberField.mixedEmbedding.normAtPlace w ((toMix K) x)) ?_
      intro w _
      rcases w.isReal_or_isComplex with hwr | hwc
      · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isReal hwr]
        have hmem : ((toMix K) x).1 ⟨w, hwr⟩ ∈ Metric.ball (0:ℝ) (f w : ℝ) :=
          (Set.mem_pi.mp (Set.mem_prod.mp hx).1) ⟨w, hwr⟩ (Set.mem_univ _)
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
        calc ‖((toMix K) x).1 ⟨w, hwr⟩‖
            = |(((toMix K) x).1 ⟨w, hwr⟩ : ℝ)| := Real.norm_eq_abs _
          _ ≤ (f w : ℝ) := le_of_lt hmem
          _ = (Real.sqrt (n:ℝ))⁻¹ := hfval w
      · rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex hwc]
        have hmem : ((toMix K) x).2 ⟨w, hwc⟩ ∈ Metric.ball (0:ℂ) (f w : ℝ) :=
          (Set.mem_pi.mp (Set.mem_prod.mp hx).2) ⟨w, hwc⟩ (Set.mem_univ _)
        rw [Metric.mem_ball, dist_zero_right] at hmem
        calc ‖((toMix K) x).2 ⟨w, hwc⟩‖ ≤ (f w : ℝ) := le_of_lt hmem
          _ = (Real.sqrt (n:ℝ))⁻¹ := hfval w
    calc ‖x‖ ≤ Real.sqrt (↑(SmallBasis.deg K)) * ‖(toMix K) x‖ :=
          SmallBasis.euc_norm_le_sqrt_mul_sup K x
      _ ≤ Real.sqrt (↑(SmallBasis.deg K)) * (Real.sqrt (n:ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
      _ = 1 := by
          rw [show (↑(SmallBasis.deg K) : ℝ) = (n:ℝ) by simp [SmallBasis.deg, hn]]
          exact mul_inv_cancel₀ (ne_of_gt hsqrtpos)
  have hmeas : MeasurableSet (NumberField.mixedEmbedding.convexBodyLT K f) := by
    rw [NumberField.mixedEmbedding.convexBodyLT]
    refine MeasurableSet.prod ?_ ?_
    · exact MeasurableSet.pi Set.countable_univ (fun w _ => measurableSet_ball)
    · exact MeasurableSet.pi Set.countable_univ (fun w _ => measurableSet_ball)
  have hmp : volume ((toMix K) ⁻¹' (NumberField.mixedEmbedding.convexBodyLT K f)) =
      volume (NumberField.mixedEmbedding.convexBodyLT K f) := by
    have h1 := (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed K).map_eq
    rw [← h1]
    exact (Measure.map_apply (toMix K).continuous.measurable hmeas).symm
  have hone : ENNReal.ofReal ((2:ℝ)^(NumberField.InfinitePlace.nrRealPlaces K) *
        Real.pi^(NumberField.InfinitePlace.nrComplexPlaces K) *
        ((Real.sqrt (n:ℝ))⁻¹)^n) ≤
      volume (Metric.closedBall (0 : EuMix K) 1) := by
    rw [← hvol, ← hmp]
    exact measure_mono hsub
  have htoReal := ENNReal.toReal_mono (measure_closedBall_lt_top.ne) hone
  rw [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ _)] at htoReal
  have hmul := mul_le_mul_of_nonneg_right htoReal
    (by positivity : (0:ℝ) ≤ (Real.sqrt (n:ℝ)) ^ n)
  have hA : ((2:ℝ)^(NumberField.InfinitePlace.nrRealPlaces K) *
        Real.pi^(NumberField.InfinitePlace.nrComplexPlaces K) *
        ((Real.sqrt (n:ℝ))⁻¹)^n) * (Real.sqrt (n:ℝ)) ^ n =
      (2:ℝ)^(NumberField.InfinitePlace.nrRealPlaces K) *
        Real.pi^(NumberField.InfinitePlace.nrComplexPlaces K) := by
    rw [mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero n (ne_of_gt hsqrtpos)), mul_one]
  rw [hA] at hmul
  exact hmul


/-- **Existence of a small non-rational algebraic integer.**

For a number field `K` of degree `n ≥ 2` there is a nonzero algebraic integer
`a ∈ 𝓞 K` which is not rational and whose house is at most
`2 ^ (n + 5) · |disc K| ^ (1 / (2 (n - 1)))`. -/
theorem exists_nonrational_house_le (K : Type*) [Field K] [NumberField K]
    (hn : 2 ≤ Module.finrank ℚ K) :
    ∃ a : NumberField.RingOfIntegers K, a ≠ 0 ∧
      ((a : NumberField.RingOfIntegers K) : K) ∉ Set.range (algebraMap ℚ K) ∧
      NumberField.house (((a : NumberField.RingOfIntegers K) : K)) ≤
        2 ^ (Module.finrank ℚ K + 5) *
          |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((Module.finrank ℚ K : ℝ) - 1))) := by
  classical
  set n : ℕ := Module.finrank ℚ K with hn'
  have hn2 : 2 ≤ n := by rw [hn']; exact hn
  have hn2R : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hd : 0 < n := by omega
  set V : ℝ := Real.sqrt |(((NumberField.discr K : ℤ)) : ℝ)| with hV
  set volU : ℝ := (volume (Metric.closedBall (0 : EuMix K) 1)).toReal with hvolU
  have hVnn : 0 ≤ V := by rw [hV]; positivity
  -- the covolume of the Euclidean lattice of integers
  have hfin : Module.finrank ℤ (EuInt K) = n := by
    rw [hn']
    simpa [EuInt, SmallBasis.EucLattice, SmallBasis.deg] using SmallBasis.finrank_EucLattice K
  have hcov : ZLattice.covolume (EuInt K) volume ≤ V := by
    rw [hV, EuInt, covolume_euclidean_integerLattice]
    have h1 : (2:ℝ)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces K) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    calc (2:ℝ)⁻¹ ^ (NumberField.InfinitePlace.nrComplexPlaces K) *
          Real.sqrt |(((NumberField.discr K : ℤ)) : ℝ)|
        ≤ 1 * Real.sqrt |(((NumberField.discr K : ℤ)) : ℝ)| :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      _ = Real.sqrt |(((NumberField.discr K : ℤ)) : ℝ)| := one_mul _
  -- nonzero lattice vectors have norm at least one
  have hmin : 1 ≤ Commons.Lattice.SuccessiveMinima.successiveMinimum (EuInt K) 1 := by
    refine Commons.Lattice.SuccessiveMinima.successiveMinimum_ge_of_forall_ne_zero_norm_ge
      (EuInt K) 1 le_rfl ?_ ?_
    · exact Commons.Lattice.SuccessiveMinima.nonempty_successiveMinimumSet (EuInt K) 1
        (by rw [hfin]; omega)
    · intro v hv
      set a : 𝓞 K := SmallBasis.ofEuc K v with ha
      have hv' : SmallBasis.eucOf K a = v := by rw [ha]; exact SmallBasis.eucOf_ofEuc K v
      have ha0 : a ≠ 0 := by
        intro h
        apply hv
        apply Subtype.ext
        have h1 : (toMix K) ((v : ↥(EuInt K)) : EuMix K) = 0 := by
          rw [← SmallBasis.ofEuc_spec K v, ← ha, h]
          simp
        have h2 : ((v : ↥(EuInt K)) : EuMix K) = 0 := by
          refine (toMix K).injective ?_
          rw [h1, map_zero]
        show ((v : ↥(EuInt K)) : EuMix K) = ((0 : ↥(EuInt K)) : EuMix K)
        rw [h2]
        rfl
      have haK : ((a : 𝓞 K) : K) ≠ 0 := fun h => ha0 (Subtype.ext h)
      have hhouse1 : (1:ℝ) ≤ NumberField.house (((a : 𝓞 K) : K)) :=
        NumberField.one_le_house_of_isIntegral a.2 haK
      have hhouse2 : NumberField.house (((a : 𝓞 K) : K)) ≤ ‖(v : EuMix K)‖ := by
        have h3 := SmallBasis.house_le_sup_mixed K (((a : 𝓞 K) : K))
        have h4 : NumberField.mixedEmbedding K (((a : 𝓞 K) : K)) = (toMix K) (v : EuMix K) := by
          rw [ha]; exact SmallBasis.ofEuc_spec K v
        rw [h4] at h3
        exact h3.trans (SmallBasis.sup_norm_le_euc_norm K (v : EuMix K))
      exact hhouse1.trans hhouse2
  -- two short independent lattice vectors
  obtain ⟨v, hvind, hvnorm⟩ := Commons.Lattice.Minkowski.exists_short_independent
    (d := n) hd (E := EuMix K) (L := EuInt K) hfin hcov hVnn hmin 2
    (by norm_num) (by omega)
  -- the associated algebraic integers have small house
  have hhouse : ∀ i : Fin 2, NumberField.house (((SmallBasis.ofEuc K (v i) : 𝓞 K) : K)) ≤
      ‖(v i : EuMix K)‖ := by
    intro i
    have h3 := SmallBasis.house_le_sup_mixed K (((SmallBasis.ofEuc K (v i) : 𝓞 K) : K))
    have h4 : NumberField.mixedEmbedding K (((SmallBasis.ofEuc K (v i) : 𝓞 K) : K)) =
        (toMix K) (v i : EuMix K) := SmallBasis.ofEuc_spec K (v i)
    rw [h4] at h3
    exact h3.trans (SmallBasis.sup_norm_le_euc_norm K (v i : EuMix K))
  -- at least one of the two is irrational
  have hnonrat : ∃ i : Fin 2,
      (((SmallBasis.ofEuc K (v i) : 𝓞 K) : K)) ∉ Set.range (algebraMap ℚ K) := by
    by_contra hcon
    push Not at hcon
    have key : ∀ (a : 𝓞 K) (q : ℚ), ((a : 𝓞 K) : K) = algebraMap ℚ K q →
        (SmallBasis.eucOf K a : EuMix K) =
          (q : ℝ) • ((toMix K).symm (1 : NumberField.mixedEmbedding.mixedSpace K)) := by
      intro a q hq
      have h1 : (toMix K) ((SmallBasis.eucOf K a : EuInt K) : EuMix K) =
          algebraMap ℚ (NumberField.mixedEmbedding.mixedSpace K) q := by
        rw [SmallBasis.eucOf_coe, (toMix K).apply_symm_apply, hq]
        exact (RingHom.toRatAlgHom (NumberField.mixedEmbedding K)).commutes q
      calc (SmallBasis.eucOf K a : EuMix K)
          = (toMix K).symm ((toMix K) ((SmallBasis.eucOf K a : EuInt K) : EuMix K)) := by
            rw [ContinuousLinearEquiv.symm_apply_apply]
        _ = (toMix K).symm (algebraMap ℚ (NumberField.mixedEmbedding.mixedSpace K) q) := by
            rw [h1]
        _ = (toMix K).symm ((q : ℝ) • (1 : NumberField.mixedEmbedding.mixedSpace K)) := by
            congr 1
            rw [Algebra.algebraMap_eq_smul_one, Algebra.smul_def, Algebra.smul_def, mul_one,
              mul_one]
            exact DFunLike.congr_fun (IsScalarTower.algebraMap_eq ℚ ℝ _) q
        _ = (q : ℝ) • ((toMix K).symm (1 : NumberField.mixedEmbedding.mixedSpace K)) := by
            rw [map_smul]
    obtain ⟨q0, hq0⟩ := Set.mem_range.mp (hcon 0)
    obtain ⟨q1, hq1⟩ := Set.mem_range.mp (hcon 1)
    have hv0 : (v 0 : EuMix K) =
        (q0 : ℝ) • ((toMix K).symm (1 : NumberField.mixedEmbedding.mixedSpace K)) := by
      have h := key (SmallBasis.ofEuc K (v 0)) q0 hq0.symm
      rwa [SmallBasis.eucOf_ofEuc] at h
    have hv1 : (v 1 : EuMix K) =
        (q1 : ℝ) • ((toMix K).symm (1 : NumberField.mixedEmbedding.mixedSpace K)) := by
      have h := key (SmallBasis.ofEuc K (v 1)) q1 hq1.symm
      rwa [SmallBasis.eucOf_ofEuc] at h
    obtain ⟨hv1ne, hv1span⟩ := linearIndependent_fin2.mp hvind
    rcases eq_or_ne (q1 : ℝ) 0 with hq1 | hq1
    · exact hv1ne (by rw [hv1, hq1, zero_smul])
    · refine hv1span ((q0 : ℝ) * ((q1 : ℝ))⁻¹) ?_
      rw [hv0, hv1, smul_smul, mul_assoc, inv_mul_cancel₀ hq1, mul_one]
  -- the numeric bounds
  have hvolineq : (1:ℝ) ≤ volU * (Real.sqrt (n:ℝ))^n := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^(NumberField.InfinitePlace.nrRealPlaces K) *
        Real.pi^(NumberField.InfinitePlace.nrComplexPlaces K) := by
      have h2 : (1:ℝ) ≤ (2:ℝ)^(NumberField.InfinitePlace.nrRealPlaces K) :=
        one_le_pow₀ (by norm_num)
      have h3 : (1:ℝ) ≤ Real.pi^(NumberField.InfinitePlace.nrComplexPlaces K) :=
        one_le_pow₀ (le_trans (by norm_num : (1:ℝ) ≤ 2) Real.two_le_pi)
      nlinarith [h2, h3]
    have h2 := two_rpow_mul_pi_rpow_le_volume_mul_sqrt_pow K
    rw [← hn', ← hvolU] at h2
    exact h1.trans h2
  have hvolUpos : 0 < volU := by
    have h1 : (0:ℝ) < (Real.sqrt (n:ℝ))^n := by positivity
    nlinarith [hvolineq, h1]
  have hstep : ((4:ℝ)^n / volU) ^ (1 / ((n:ℝ) - 1)) ≤ (2:ℝ)^(n+4) := by
    have h4n : (0:ℝ) < (4:ℝ)^n := by positivity
    have hn1pos : (0:ℝ) < (n:ℝ) - 1 := by linarith
    have hbase1 : (4:ℝ)^n / volU ≤ (4 * Real.sqrt (n:ℝ))^n := by
      have h1 : 1 / volU ≤ (Real.sqrt (n:ℝ))^n := by
        rw [div_le_iff₀ hvolUpos]
        linarith [hvolineq]
      calc (4:ℝ)^n / volU = (4:ℝ)^n * (1 / volU) := by ring
        _ ≤ (4:ℝ)^n * (Real.sqrt (n:ℝ))^n := mul_le_mul_of_nonneg_left h1 h4n.le
        _ = (4 * Real.sqrt (n:ℝ))^n := by rw [mul_pow]
    have hb : (0:ℝ) ≤ 4 * Real.sqrt (n:ℝ) := by positivity
    have hb1 : (1:ℝ) ≤ 4 * Real.sqrt (n:ℝ) := by
      have h := Real.one_le_sqrt.mpr (by linarith : (1:ℝ) ≤ (n:ℝ))
      linarith
    have hexp2 : (n:ℝ) * (1 / ((n:ℝ) - 1)) ≤ ((2:ℕ) : ℝ) := by
      rw [mul_one_div, div_le_iff₀ hn1pos]
      push_cast
      linarith
    calc ((4:ℝ)^n / volU) ^ (1 / ((n:ℝ) - 1))
        ≤ ((4 * Real.sqrt (n:ℝ))^n) ^ (1 / ((n:ℝ) - 1)) :=
          Real.rpow_le_rpow (by positivity) hbase1 (by positivity)
      _ = (4 * Real.sqrt (n:ℝ)) ^ ((n:ℝ) * (1 / ((n:ℝ) - 1))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
      _ ≤ (4 * Real.sqrt (n:ℝ)) ^ (((2:ℕ)) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 hexp2
      _ = 16 * (n:ℝ) := by
          rw [Real.rpow_natCast, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (n:ℝ))]
          norm_num
      _ ≤ (2:ℝ)^(n+4) := by
          have hnle : (n:ℝ) ≤ (2:ℝ)^n := by
            have : n ≤ 2^n := le_of_lt Nat.lt_two_pow_self
            exact_mod_cast this
          have h24 : (2:ℝ)^(n+4) = 16 * (2:ℝ)^n := by
            rw [pow_add]; norm_num; ring
          rw [h24]
          linarith [mul_le_mul_of_nonneg_left hnle (by norm_num : (0:ℝ) ≤ 16)]
  -- the final bound
  have hD1 : (1:ℝ) ≤ |(((NumberField.discr K : ℤ)) : ℝ)| := by
    have h : (1:ℤ) ≤ |NumberField.discr K| := Int.one_le_abs (NumberField.discr_ne_zero K)
    have h' : ((1:ℤ) : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by exact_mod_cast h
    simpa [Int.cast_abs] using h'
  refine ⟨SmallBasis.ofEuc K (v (Classical.choose hnonrat)), ?_, ?_, ?_⟩
  · intro hzero
    exact (Classical.choose_spec hnonrat) (by rw [hzero]; exact ⟨0, by simp⟩)
  · exact Classical.choose_spec hnonrat
  · have hN := hvnorm (Classical.choose hnonrat)
    simp only [← hvolU] at hN
    have hexp : ((n + 1 - 2 : ℕ) : ℝ) = (n:ℝ) - 1 := by
      have h1 : n + 1 - 2 = n - 1 := by omega
      rw [h1, Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    rw [hexp] at hN
    have hn1ne : (n:ℝ) - 1 ≠ 0 := by linarith
    have hVpow : V ^ (1 / ((n:ℝ) - 1)) =
        |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) := by
      rw [hV, Real.sqrt_eq_rpow, ← Real.rpow_mul (abs_nonneg _)]
      congr 1
      field_simp
    have hD0 : (0:ℝ) ≤ |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) :=
      Real.rpow_nonneg (abs_nonneg _) _
    have hfinal : (2:ℝ)^(n+4) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) + 1
        ≤ (2:ℝ)^(n+5) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) := by
      have hexpnn : (0:ℝ) ≤ 1 / (2 * ((n:ℝ) - 1)) := by
        have hn1pos : (0:ℝ) < (n:ℝ) - 1 := by linarith
        positivity
      have hD1' : (1:ℝ) ≤ |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) :=
        Real.one_le_rpow hD1 hexpnn
      have hpow : (2:ℝ)^(n+4) + 1 ≤ (2:ℝ)^(n+5) := by
        have h3 : (1:ℝ) ≤ (2:ℝ)^(n+4) := one_le_pow₀ (by norm_num)
        have h4 : (2:ℝ)^(n+5) = 2 * (2:ℝ)^(n+4) := by
          rw [show n + 5 = (n+4) + 1 by omega, pow_succ]; ring
        linarith
      calc (2:ℝ)^(n+4) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) + 1
          ≤ (2:ℝ)^(n+4) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1)))
              + |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) := by linarith
        _ = ((2:ℝ)^(n+4) + 1) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) := by
              ring
        _ ≤ (2:ℝ)^(n+5) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) :=
              mul_le_mul_of_nonneg_right hpow hD0
    calc NumberField.house (((SmallBasis.ofEuc K (v (Classical.choose hnonrat)) : 𝓞 K) : K))
        ≤ ‖(v (Classical.choose hnonrat) : EuMix K)‖ := hhouse _
      _ ≤ ((4:ℝ)^n * V / volU) ^ (1 / ((n:ℝ) - 1)) + 1 := hN
      _ = (((4:ℝ)^n / volU) * V) ^ (1 / ((n:ℝ) - 1)) + 1 := by
          rw [show (4:ℝ)^n * V / volU = ((4:ℝ)^n / volU) * V by ring]
      _ = ((4:ℝ)^n / volU) ^ (1 / ((n:ℝ) - 1)) * V ^ (1 / ((n:ℝ) - 1)) + 1 := by
          rw [Real.mul_rpow (by positivity) hVnn]
      _ = ((4:ℝ)^n / volU) ^ (1 / ((n:ℝ) - 1)) *
            |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) + 1 := by rw [hVpow]
      _ ≤ (2:ℝ)^(n+4) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) + 1 :=
          add_le_add_left (mul_le_mul_of_nonneg_right hstep hD0) 1
      _ ≤ (2:ℝ)^(n+5) * |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((n:ℝ) - 1))) := hfinal
      _ = 2 ^ (Module.finrank ℚ K + 5) *
            |(((NumberField.discr K : ℤ)) : ℝ)| ^ (1 / (2 * ((Module.finrank ℚ K : ℝ) - 1))) := by
          rw [hn']


end

end Commons.NumberTheory.NumberField
