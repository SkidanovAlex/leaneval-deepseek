import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic
import Submission.Commons.Lattice.SuccessiveMinima.realisation_linearIndependent
import Submission.Commons.Lattice.SuccessiveMinima.positive
import Submission.Commons.Lattice.Counting.lattice_count_int
import Submission.Commons.Lattice.Minkowski.minkowski_second_upper

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Metric Module Filter
open scoped ENNReal Topology Pointwise BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

namespace Commons.Lattice.Minkowski

/-- Haar-measure ratio invariance: for two additive Haar measures the quotient
`μ.real s / covolume L μ` does not depend on the normalisation of the measure. -/
lemma haar_ratio_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ ν : Measure E} [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (s : Set E) (hs_comp : IsCompact s) (hs_int : (interior s).Nonempty) :
    μ.real s / ZLattice.covolume L μ = ν.real s / ZLattice.covolume L ν := by
  classical
  let K₀ : TopologicalSpace.PositiveCompacts E := ⟨⟨s, hs_comp⟩, hs_int⟩
  let H : Measure E := MeasureTheory.Measure.addHaarMeasure K₀
  let b : Basis (Module.Free.ChooseBasisIndex ℤ L) ℤ L := Module.Free.chooseBasis ℤ L
  let bR : Basis (Module.Free.ChooseBasisIndex ℤ L) ℝ E := b.ofZLatticeBasis ℝ L
  let FD : Set E := ZSpan.fundamentalDomain bR
  have hFDμ : ZLattice.covolume L μ = μ.real FD := by
    exact ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)
  have hFDν : ZLattice.covolume L ν = ν.real FD := by
    exact ZLattice.covolume_eq_measure_fundamentalDomain L ν (ZLattice.isAddFundamentalDomain b ν)
  have hμ : μ = μ s • H := by
    dsimp [H]
    exact MeasureTheory.Measure.addHaarMeasure_unique μ K₀
  have hν : ν = ν s • H := by
    dsimp [H]
    exact MeasureTheory.Measure.addHaarMeasure_unique ν K₀
  let a : ℝ≥0∞ := μ s
  let c : ℝ≥0∞ := ν s
  have hμa : μ = a • H := by simpa [a] using hμ
  have hνc : ν = c • H := by simpa [c] using hν
  have ha_pos : 0 < a.toReal := by
    dsimp [a]
    exact ENNReal.toReal_pos (ne_of_gt (measure_pos_of_nonempty_interior μ hs_int))
      (ne_of_lt (hs_comp.measure_lt_top))
  have hc_pos : 0 < c.toReal := by
    dsimp [c]
    exact ENNReal.toReal_pos (ne_of_gt (measure_pos_of_nonempty_interior ν hs_int))
      (ne_of_lt (hs_comp.measure_lt_top))
  let X : ℝ := (H FD).toReal
  have hμs : μ.real s = a.toReal := by
    dsimp [a]
    rw [measureReal_def]
  have hμFD : μ.real FD = a.toReal * X := by
    calc
      μ.real FD = (μ FD).toReal := by rw [measureReal_def]
      _ = ((a • H) FD).toReal := by rw [hμa]
      _ = (a * (H FD)).toReal := by rw [Measure.smul_apply]; rfl
      _ = a.toReal * (H FD).toReal := by rw [ENNReal.toReal_mul]
      _ = a.toReal * X := by rfl
  have hνs : ν.real s = c.toReal := by
    dsimp [c]
    rw [measureReal_def]
  have hνFD : ν.real FD = c.toReal * X := by
    calc
      ν.real FD = (ν FD).toReal := by rw [measureReal_def]
      _ = ((c • H) FD).toReal := by rw [hνc]
      _ = (c * (H FD)).toReal := by rw [Measure.smul_apply]; rfl
      _ = c.toReal * (H FD).toReal := by rw [ENNReal.toReal_mul]
      _ = c.toReal * X := by rfl
  have hX : X ≠ 0 := by
    have hcov : ZLattice.covolume L ν ≠ 0 := ZLattice.covolume_ne_zero L ν
    rw [hFDν, hνFD] at hcov
    exact (mul_ne_zero_iff.mp hcov).2
  calc
    μ.real s / ZLattice.covolume L μ = a.toReal / (a.toReal * X) := by
      rw [hμs, hFDμ, hμFD]
    _ = 1 / X := by
      field_simp [ne_of_gt ha_pos, hX]
    _ = c.toReal / (c.toReal * X) := by
      field_simp [ne_of_gt hc_pos, hX]
    _ = ν.real s / ZLattice.covolume L ν := by
      rw [hνs, hFDν, hνFD]

/-- Counting asymptotics for lattice points in a ball, with an arbitrary additive Haar
measure: `card{v ∈ L | ‖v‖ ≤ N}/N^dim → μ(closedBall 0 1)/covolume μ L`.  This is the
normed-space (non-inner-product), arbitrary-Haar-measure version of
`ZLattice.covolume.tendsto_card_div_pow'`; the proof transports to coordinates through
a `ℤ`-basis of `L` (`tendsto_card_div_pow''`) and applies Haar-measure normalisation
invariance (`haar_ratio_eq`). -/
lemma card_inter_closedBall_tendsto_haar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    Tendsto (fun N : ℕ => (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℝ) / (N : ℝ) ^ Module.finrank ℝ E)
      atTop (nhds ((μ (Metric.closedBall (0 : E) 1)).toReal / ZLattice.covolume L μ)) := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let b : Basis ι ℤ L := Module.Free.chooseBasis ℤ L
  let bR : Basis ι ℝ E := b.ofZLatticeBasis ℝ L
  let φ : E ≃ₗ[ℝ] (ι → ℝ) := bR.equivFun
  let B : Set E := Metric.closedBall (0 : E) 1
  let ν : Measure E := Measure.map (⇑φ.symm) (volume : Measure (ι → ℝ))
  have hfront0 : (volume : Measure (ι → ℝ)) (frontier (φ '' B)) = 0 := by
    have hconv : Convex ℝ (φ '' B) := by
      exact (convex_closedBall (0 : E) (1 : ℝ)).linear_image (φ : E →ₗ[ℝ] (ι → ℝ))
    simpa using (Convex.addHaar_frontier (E := (ι → ℝ)) (μ := volume) (s := φ '' B) hconv)
  have hlim0 : Tendsto (fun N : ℕ =>
      (Nat.card ((B ∩ (N : ℝ)⁻¹ • (L : Set E) : Set E) : Set E) : ℝ) / (N : ℝ) ^ Fintype.card ι)
      atTop (nhds ((volume : Measure (ι → ℝ)).real (φ '' B))) := by
    exact ZLattice.covolume.tendsto_card_div_pow'' (E := E) b (s := B)
      Metric.isBounded_closedBall Metric.isClosed_closedBall.measurableSet hfront0
  have hlim0' : Tendsto (fun N : ℕ =>
      (Nat.card ((B ∩ (N : ℝ)⁻¹ • (L : Set E) : Set E) : Set E) : ℝ) /
        (N : ℝ) ^ Module.finrank ℝ E)
      atTop (nhds ((volume : Measure (ι → ℝ)).real (φ '' B))) := by
    have hcard : Fintype.card ι = Module.finrank ℝ E := by
      dsimp [ι]
      rw [← Module.finrank_eq_card_basis bR]
    simpa [hcard] using hlim0
  have hBcomp : IsCompact B := by
    dsimp [B]
    exact ProperSpace.isCompact_closedBall (0 : E) 1
  have hBint : (interior B).Nonempty := by
    dsimp [B]
    refine ⟨0, ?_⟩
    rw [interior_closedBall (0 : E) (by norm_num : (1 : ℝ) ≠ 0)]
    simp
  have hφL_meas : Measurable (⇑φ.symm) := by
    dsimp [φ]
    exact Continuous.measurable bR.equivFunL.symm.continuous
  have hmap_real : ∀ (s : Set E), MeasurableSet s →
      ν.real s = (volume : Measure (ι → ℝ)).real (φ '' s) := by
    intro s hs
    have hνs : ν s = (volume : Measure (ι → ℝ)) (φ '' s) := by
      dsimp [ν]
      rw [Measure.map_apply]
      · congr 1
        ext u
        constructor
        · intro hu
          refine ⟨φ.symm u, ?_, ?_⟩
          · simpa using hu
          · simp
        · rintro ⟨x, hx, rfl⟩
          simp [hx]
      · exact hφL_meas
      · exact hs
    calc
      ν.real s = (ν s).toReal := by rw [measureReal_def]
      _ = ((volume : Measure (ι → ℝ)) (φ '' s)).toReal := by rw [hνs]
      _ = (volume : Measure (ι → ℝ)).real (φ '' s) := by rw [measureReal_def]
  have hνhaar : IsAddHaarMeasure ν := by
    dsimp [ν]
    simpa using (MeasureTheory.Measure.MapLinearEquiv.isAddHaarMeasure
      (μ := (volume : Measure (ι → ℝ))) (e := φ.symm) :
      IsAddHaarMeasure ((volume : Measure (ι → ℝ)).map (⇑φ.symm)))
  have hνball : ν.real B = (volume : Measure (ι → ℝ)).real (φ '' B) := by
    exact hmap_real B (by dsimp [B]; exact isClosed_closedBall.measurableSet)
  have hcovν : ZLattice.covolume L ν = 1 := by
    have hFDmeas : MeasurableSet (ZSpan.fundamentalDomain bR) :=
      ZSpan.fundamentalDomain_measurableSet bR
    have hc := ZLattice.covolume_eq_measure_fundamentalDomain L ν
      (ZLattice.isAddFundamentalDomain b ν)
    rw [hc]
    rw [hmap_real (ZSpan.fundamentalDomain bR) hFDmeas]
    have hyrepr : ∀ (x : ι → ℝ) (i : ι), (bR.repr (φ.symm x)) i = x i := by
      intro x i
      have hsum : φ.symm x = ∑ j : ι, x j • bR j := bR.equivFun_symm_apply x
      rw [hsum]
      have hrs := congrFun (bR.repr_sum_self x) i
      simpa using hrs
    have hFDset : φ '' (ZSpan.fundamentalDomain bR) =
        Set.pi Set.univ (fun _ : ι => Set.Ico (0 : ℝ) 1) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        intro i
        have hmem := hy i
        simpa [φ] using hmem
      · intro hx
        refine ⟨φ.symm x, ?_, ?_⟩
        · intro i
          rw [hyrepr x i]
          exact hx i (Set.mem_univ i)
        · change bR.equivFun (bR.equivFun.symm x) = x
          exact bR.equivFun.apply_symm_apply x
    rw [hFDset]
    rw [measureReal_def]
    rw [Real.volume_pi_Ico_toReal (a := fun _ : ι => (0 : ℝ)) (b := fun _ : ι => (1 : ℝ))]
    · simp
    · intro i
      norm_num
  have hratio : μ.real B / ZLattice.covolume L μ = ν.real B / ZLattice.covolume L ν := by
    exact haar_ratio_eq (E := E) (μ := μ) (ν := ν) L B hBcomp hBint
  have hconv : (volume : Measure (ι → ℝ)).real (φ '' B) = μ.real B / ZLattice.covolume L μ := by
    calc
      (volume : Measure (ι → ℝ)).real (φ '' B) = ν.real B := hνball.symm
      _ = ν.real B / ZLattice.covolume L ν := by rw [hcovν]; simp
      _ = μ.real B / ZLattice.covolume L μ := hratio.symm
  have hlimμ : Tendsto (fun N : ℕ =>
      (Nat.card ((B ∩ (N : ℝ)⁻¹ • (L : Set E) : Set E) : Set E) : ℝ) /
        (N : ℝ) ^ Module.finrank ℝ E)
      atTop (nhds (μ.real B / ZLattice.covolume L μ)) := by
    simpa [hconv] using hlim0'
  have hreindex : (fun N : ℕ => (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℝ) /
        (N : ℝ) ^ Module.finrank ℝ E) =ᶠ[atTop]
      (fun N : ℕ => (Nat.card (B ∩ (N : ℝ)⁻¹ • (L : Set E) : Set E) : ℝ) /
        (N : ℝ) ^ Module.finrank ℝ E) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hc := lattice_ball_card_eq_smulSet (E := E) L hN
    congr 1
    exact_mod_cast hc
  have hlim : Tendsto (fun N : ℕ =>
      (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℝ) / (N : ℝ) ^ Module.finrank ℝ E)
      atTop (nhds (μ.real B / ZLattice.covolume L μ)) := by
    exact Tendsto.congr' hreindex.symm hlimμ
  simpa [B, measureReal_def] using hlim

/-- Intermediate counting bound with an arbitrary additive Haar measure: the product of the
successive minima times the measure of the unit ball is at most `2^(2d-1)` times the covolume.
This is the measure-version of `product_upper_bound` (no inner product needed). -/
lemma product_upper_bound_measure {d : ℕ} (hd : 0 < d) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsAddHaarMeasure μ]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℤ L = d) :
    (∏ i : Fin d, Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1)) *
        ENNReal.toReal (μ (Metric.closedBall (0 : E) 1)) ≤
      (2 : ℝ) ^ (2 * d - 1) * ZLattice.covolume L μ := by
  classical
  let lam : Fin d → ℝ := fun i => Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1)
  have hlam_pos : ∀ i : Fin d, 0 < lam i := by
    intro i
    dsimp [lam]
    exact Commons.Lattice.SuccessiveMinima.positive L (i.val + 1) (by omega) (by rw [hfin]; omega)
  have hcov_pos : 0 < ZLattice.covolume L μ := ZLattice.covolume_pos L μ
  have hfdim : Module.finrank ℝ E = d := by
    exact (ZLattice.rank ℝ L).symm.trans hfin
  let cN : ℕ → ℕ := fun N => Nat.card {v : L // ‖(v : E)‖ ≤ N}
  let qN : ℕ → Fin d → ℕ := fun N i => (Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1
  let f : ℕ → ℝ := fun N => (cN N : ℝ) / (N : ℝ) ^ d
  let h : ℕ → ℝ := fun N => (∏ i : Fin d, (qN N i : ℝ)) / (N : ℝ) ^ d
  let g : ℕ → ℝ := fun N => (2 : ℝ) ^ (d - 1) * h N
  let A : ℝ := ENNReal.toReal (μ (Metric.closedBall (0 : E) 1)) / ZLattice.covolume L μ
  let B : ℝ := (2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)
  have hlimf : Tendsto f atTop (nhds A) := by
    have hgen := card_inter_closedBall_tendsto_haar (E := E) μ L
    dsimp [f, cN, A]
    simpa [hfdim] using hgen
  have hlimh : Tendsto h atTop (nhds (∏ i : Fin d, 2 / lam i)) := by
    have hQ := tendsto_prodQ lam hlam_pos
    dsimp [h, qN]
    have heq : (fun N : ℕ =>
        ∏ i : Fin d, (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ) / (N : ℝ))
        =ᶠ[atTop] (fun N : ℕ => (∏ i : Fin d, (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ)) / (N : ℝ) ^ d) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      exact (prod_div_pow (fun i : Fin d => (((Int.floor ((2 * (N : ℝ)) / lam i)).toNat + 1 : ℕ) : ℝ)) N hN).symm
    exact hQ.congr' heq
  have hlimg : Tendsto g atTop (nhds B) := by
    have hc : Tendsto (fun _ : ℕ => (2 : ℝ) ^ (d - 1)) atTop
        (nhds ((2 : ℝ) ^ (d - 1))) := tendsto_const_nhds
    dsimp [g, B]
    exact hc.mul hlimh
  have hev : ∀ᶠ N : ℕ in atTop, f N ≤ g N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hcnt : (Nat.card {v : L // ‖(v : E)‖ ≤ N} : ℕ) ≤
        2 ^ (d - 1) * ∏ i : Fin d,
          ((Int.floor ((2 * (N : ℝ)) / Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1))).toNat + 1) := by
      exact Commons.Lattice.Counting.lattice_count_int (E := E) L hfin hd N hN
    have hcntR : (cN N : ℝ) ≤ (2 : ℝ) ^ (d - 1) * (∏ i : Fin d, (qN N i : ℝ)) := by
      dsimp [cN, qN, lam]
      exact_mod_cast hcnt
    have hNpow : 0 ≤ (N : ℝ) ^ d := pow_nonneg (by exact_mod_cast (Nat.zero_le N)) d
    have hdiv := div_le_div_of_nonneg_right hcntR hNpow
    dsimp [f, g, h]
    rw [mul_div_assoc] at hdiv
    exact hdiv
  have hlim := le_of_tendsto_of_tendsto hlimf hlimg hev
  have hvol : ENNReal.toReal (μ (Metric.closedBall (0 : E) 1)) ≤
      ((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L μ := by
    dsimp [A, B] at hlim
    exact (div_le_iff₀ hcov_pos).mp hlim
  let P : ℝ := ∏ i : Fin d, lam i
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos (s := Finset.univ) (fun i _ => hlam_pos i)
  have hper : ∀ i : Fin d, lam i * (2 / lam i) = 2 := by
    intro i
    field_simp [ne_of_gt (hlam_pos i)]
  have hPQ : P * (∏ i : Fin d, 2 / lam i) = (2 : ℝ) ^ d := by
    dsimp [P]
    rw [← Finset.prod_mul_distrib]
    rw [show (∏ i : Fin d, lam i * (2 / lam i)) = ∏ i : Fin d, (2 : ℝ) by
      exact Finset.prod_congr rfl (fun i hi => hper i)]
    simp [Finset.prod_const, Fintype.card_fin]
  have hA_pow : (2 : ℝ) ^ (d - 1) * (2 : ℝ) ^ d = (2 : ℝ) ^ (2 * d - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hstep1 : P * ENNReal.toReal (μ (Metric.closedBall (0 : E) 1)) ≤
      P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L μ) := by
    exact mul_le_mul_of_nonneg_left hvol (le_of_lt hPpos)
  have hstep2 : P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L μ)
      = (2 : ℝ) ^ (2 * d - 1) * ZLattice.covolume L μ := by
    have hmm : P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L μ)
        = ((2 : ℝ) ^ (d - 1) * (P * ∏ i : Fin d, (2 / lam i))) * ZLattice.covolume L μ := by
          ac_rfl
    calc
      P * (((2 : ℝ) ^ (d - 1) * ∏ i : Fin d, (2 / lam i)) * ZLattice.covolume L μ)
          = ((2 : ℝ) ^ (d - 1) * (P * ∏ i : Fin d, (2 / lam i))) * ZLattice.covolume L μ := hmm
      _ = ((2 : ℝ) ^ (d - 1) * (2 : ℝ) ^ d) * ZLattice.covolume L μ := by rw [hPQ]
      _ = (2 : ℝ) ^ (2 * d - 1) * ZLattice.covolume L μ := by rw [hA_pow]
  exact le_trans hstep1 (le_of_eq hstep2)

/-- **Minkowski's second theorem (upper bound), measure form**: if `L` is a full `ℤ`-lattice
of rank `d` in a finite-dimensional real normed space `E` and `λᵢ = successiveMinimum L i`
are the successive minima of the closed unit ball of the ambient norm with respect to `L`,
then `λ₁·…·λ_d · volume (closedBall 0 1) ≤ (2·2)^d · covolume L`, where `volume` is any
additive Haar measure on `E` and the covolume is taken with respect to the same measure.
(The statement is normalisation-invariant; no inner product is needed — cf. the companion
`minkowski_second_upper`, which assumes an inner-product-normalised measure.) -/
theorem minkowski_second_upper_measure {d : ℕ} (hd : 0 < d) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hfin : Module.finrank ℤ L = d) :
    (∏ i : Fin d, Commons.Lattice.SuccessiveMinima.successiveMinimum L (i.val + 1)) *
        ENNReal.toReal ((volume : Measure E) (Metric.closedBall (0 : E) 1)) ≤
      (2 : ℝ) ^ (2 * d) * ZLattice.covolume (μ := (volume : Measure E)) L := by
  have hup := product_upper_bound_measure (E := E) (d := d) hd (volume : Measure E) L hfin
  have hcov_nonneg : 0 ≤ ZLattice.covolume (μ := (volume : Measure E)) L :=
    le_of_lt (ZLattice.covolume_pos (μ := (volume : Measure E)) L)
  have hpow : (2 : ℝ) ^ (2 * d - 1) ≤ (2 : ℝ) ^ (2 * d) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 2 * d - 1 ≤ 2 * d)
  exact le_trans hup (mul_le_mul_of_nonneg_right hpow hcov_nonneg)

end Commons.Lattice.Minkowski
