import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.Q2Gram.chiSq_fourier_sum
import Submission.Work.BoseB7AK.W1rows.integrable_norm_mul_W1fun
import Submission.Work.BoseBogFS.continuous_chat
import Submission.Work.BoseBoxFock.exists_jointGramLab
import Submission.Work.BoseBoxFock.integral_toLp
import Submission.Work.BoseBoxFock.kinFT_comp_smul
import Submission.Work.BoseFixR.LatGreen.FoldAux
import Submission.Work.BoseFixR.Rb5Lin.honest_sum_le_full_lattice
import Submission.Work.BoseFixR.Rb5Lin.latticeSum_scaling
import Submission.Work.BoseFixR.farLatFourier
import Submission.Work.BoseFixR.farLatParseval
import Submission.Work.BoseGateFS.chat_W1fun_lipschitz
import Submission.Work.SmallBoxA0.PolarSphere.aemeasurable_sphAvg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.lattice_W1sq_over_tau_le_sharp`

The **sharp** weighted lattice-to-continuum sampling bound for the far-leg kernel `W₁`:

  `Σ_{k∈Lab N, k≠0} Ŵ₁(q_k)²/(2‖q_k‖²) ≤ (6/5)·(2π)⁻³·ℓ³·∫ Ŵ₁(q)²/(2‖q‖²) dq`

in the small-support regime `100 R ≤ ℓ` (and `R ≤ ℓ·chiR0`).

## Route (no Madelung-sign input beyond the existing nearest-image bound)

The proof is a chain of *existing, sorry-free* lemmas of the workspace, glued here at a generic
`ℓ`:

1. **The cube row into the lattice row.**  `kmomLab ℓ N k = ℓ⁻¹ • vec (labVec N k)` with
   `vec m = 2πm` and `labVec N` injective, so the honest cube row is (half) the finite sum of the
   lattice row over the image of `labVec N`; since `labVec N` misses `0`, that finite sum is a
   `Summable.sum_le_tsum` sub-sum of the full-lattice row `Σ'_{k≠0} Ŵ₁(q_k)²/‖q_k‖²`.
2. `LatGreen.LatGreenParsevalB` — the cell-Parseval identity
   `Σ'_{k≠0} Ŵ₁(q_k)²/‖q_k‖² = ∬_{cell²} P(x)P(y)·ℓ²·latGreen(ℓ⁻¹(x−y))`, `P` the
   `ℓ`-periodisation, `latGreen` the `ℤ³` Coulomb Green's function with neutralising background.
3. `FarLat.latGreen_le_latDistL_pair` — the pointwise nearest-image bound
   `ℓ²·latGreen(ℓ⁻¹z) ≤ (ℓ³/4π)·dist(z,ℓℤ³)⁻¹`, integrated.
4. **The new step.**  On `supp P ⊆ B(0,R)` one has `dist(z,ℓℤ³) = ‖z‖` (because `ℓℤ³` meets
   `B(0,ℓ/2)` only in `0` and `2R ≤ ℓ/50`), and `P = W₁` on the cell; hence the cell integral of
   the nearest-image kernel is *exactly* the Coulomb pair integral of `W₁` over `ℝ³ × ℝ³`.
5. `LatGreen.coulomb_pair_eq_autocorr_integral` + `Work.BoseFixR.coulomb_autocorr_eq` — the
   Coulomb pair energy is `8π·(2π)⁻³·∫Ŵ₁²/(2q²)` (autocorrelation form, no `L²` hypothesis).

The result is the sharp constant `1`: the target's `6/5` has 20 % of room.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators

namespace Work.BoseFixR

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary lattice facts -/

/-- For `n ≠ 0` the lattice point `ℓ • n` is at distance at least `ℓ` from the origin. -/
lemma lwsq_le_norm_lat {ℓ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    ℓ ≤ ‖lat ℓ n‖ := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
    by_contra hcon
    exact hn (funext fun i => by simpa using not_not.mp (not_exists.mp hcon i))
  have h1 : |(lat ℓ n) i| ≤ ‖lat ℓ n‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (β := fun _ : Fin 3 => ℝ) (lat ℓ n) i
  have h2 : (1 : ℝ) ≤ |((n i : ℤ) : ℝ)| := by
    have h3 : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|n i| : ℤ) : ℝ) := by exact_mod_cast h3
      _ = |((n i : ℤ) : ℝ)| := by rw [Int.cast_abs]
  have h3 : ℓ * |((n i : ℤ) : ℝ)| ≤ ‖lat ℓ n‖ := by
    calc ℓ * |((n i : ℤ) : ℝ)| = |ℓ * ((n i : ℤ) : ℝ)| := by rw [abs_mul, abs_of_pos hℓ]
      _ = |(lat ℓ n) i| := by simp
      _ ≤ ‖lat ℓ n‖ := h1
  calc ℓ = ℓ * 1 := (mul_one ℓ).symm
    _ ≤ ℓ * |((n i : ℤ) : ℝ)| := mul_le_mul_of_nonneg_left h2 hℓ.le
    _ ≤ ‖lat ℓ n‖ := h3

/-- On the half-cell `‖z‖ ≤ ℓ/2` the distance to the `ℓ`-lattice is the norm: the origin is the
closest lattice point. -/
lemma lwsq_latDistL_eq_norm_of_le {ℓ : ℝ} (hℓ : 0 < ℓ) {z : E3} (hz : ‖z‖ ≤ ℓ / 2) :
    latDistL ℓ z = ‖z‖ := by
  have hmem : (0 : E3) ∈ Set.range (fun n : Fin 3 → ℤ => lat ℓ n) := ⟨0, lat_zero ℓ⟩
  have hne : (Set.range (fun n : Fin 3 → ℤ => lat ℓ n)).Nonempty := ⟨0, hmem⟩
  refine le_antisymm ?_ ?_
  · calc latDistL ℓ z = Metric.infDist z (Set.range (fun n : Fin 3 → ℤ => lat ℓ n)) := rfl
      _ ≤ dist z 0 := Metric.infDist_le_dist_of_mem hmem
      _ = ‖z‖ := by simp
  · rw [latDistL]
    rw [Metric.le_infDist hne]
    rintro y ⟨n, rfl⟩
    simp only []
    rw [dist_eq_norm]
    by_cases hn : n = 0
    · subst hn
      simp [lat_zero]
    · have h1 : ℓ ≤ ‖lat ℓ n‖ := lwsq_le_norm_lat hℓ hn
      have h2 : ‖lat ℓ n‖ - ‖z‖ ≤ ‖z - lat ℓ n‖ := by
        calc ‖lat ℓ n‖ - ‖z‖ ≤ |‖lat ℓ n‖ - ‖z‖| := le_abs_self _
          _ ≤ ‖lat ℓ n - z‖ := abs_norm_sub_norm_le _ _
          _ = ‖z - lat ℓ n‖ := norm_sub_rev _ _
      linarith

/-- The periodisation of a charge supported in `B(0,R)` with `100 R ≤ ℓ` equals the charge on the
cell. -/
lemma lwsq_period_eq_of_mem_cell {ℓ R : ℝ} (hℓ : 0 < ℓ) (hreg : 100 * R ≤ ℓ)
    {W : E3 → ℝ} (hvan : ∀ x : E3, R ≤ ‖x‖ → W x = 0) {x : E3} (hx : x ∈ cell ℓ) :
    LatGreen.period W ℓ x = W x := by
  have hxle : ‖x‖ ≤ 9 / 10 * ℓ := by
    have h2 : ‖x‖ ^ 2 ≤ (9 / 10 * ℓ) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have h3 : ∀ i : Fin 3, (x i) ^ 2 ≤ (ℓ / 2) ^ 2 := by
        intro i
        have hi := hx i
        nlinarith [abs_nonneg (x i), sq_abs (x i)]
      calc ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 := Finset.sum_le_sum fun i _ => h3 i
        _ = 3 * (ℓ / 2) ^ 2 := by norm_num
        _ ≤ (9 / 10 * ℓ) ^ 2 := by nlinarith [hℓ]
    have h4 := sq_le_sq.mp h2
    rwa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (by positivity)] at h4
  have hzero : ∀ n : Fin 3 → ℤ, n ≠ 0 → W (x - lat ℓ n) = 0 := by
    intro n hn
    refine hvan (x - lat ℓ n) ?_
    have hlat : ℓ ≤ ‖lat ℓ n‖ := lwsq_le_norm_lat hℓ hn
    have h2 : ‖lat ℓ n‖ - ‖x‖ ≤ ‖x - lat ℓ n‖ := by
      calc ‖lat ℓ n‖ - ‖x‖ ≤ |‖lat ℓ n‖ - ‖x‖| := le_abs_self _
        _ ≤ ‖lat ℓ n - x‖ := abs_norm_sub_norm_le _ _
        _ = ‖x - lat ℓ n‖ := norm_sub_rev _ _
    have h3 : R ≤ ℓ / 10 := by linarith
    linarith
  rw [LatGreen.period, tsum_eq_single (0 : Fin 3 → ℤ) hzero]
  simp [lat_zero]

/-- `W₁` vanishes off the cell when `100 R ≤ ℓ`. -/
lemma lwsq_W1fun_eq_zero_of_not_mem_cell {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R ℓ : ℝ}
    (hℓ : 0 < ℓ) (hreg : 100 * R ≤ ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {x : E3} (hx : x ∉ cell ℓ) :
    W1fun v h ℓ x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, ¬ |x i| ≤ ℓ / 2 := by
    by_contra hcon
    exact hx fun i => by simpa using not_not.mp (not_exists.mp hcon i)
  push_neg at hi
  have h1 : |x i| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (β := fun _ : Fin 3 => ℝ) x i
  have h2 : R ≤ ‖x‖ := by
    have h3 : ℓ / 2 ≤ ‖x‖ := le_trans hi.le h1
    linarith
  exact LatGreen.W1fun_eq_zero_of_le_norm h hv_supp h2

/-! ## 2. The sharp full-lattice row -/

/-- **The sharp full-lattice row.**  At the small-support regime `100 R ≤ ℓ`,

`Σ'_{k≠0} Ŵ₁(q_k)²/‖q_k‖² ≤ 2·(2π)⁻³·ℓ³·∫ Ŵ₁(q)²/(2‖q‖²)`.

(The factor `2` is the `1/2` in the summand `1/(2q²)`.) -/
theorem lwsq_lattice_row_sharp {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hreg : 100 * R ≤ ℓ)
    (hW : MeasureTheory.Integrable (W1fun v h ℓ)) (hWnn : 0 ≤ W1fun v h ℓ) :
    (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (chat (W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2 / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : E3, (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
  classical
  have hWae : 0 ≤ᵐ[(MeasureTheory.volume : Measure E3)] (W1fun v h ℓ) :=
    Filter.Eventually.of_forall hWnn
  have hWev : ∀ x : E3, W1fun v h ℓ (-x) = W1fun v h ℓ x := isEven_W1fun h hvrad ℓ
  have hWper : ∀ x : E3, Summable (fun n : Fin 3 → ℤ => W1fun v h ℓ (x - lat ℓ n)) :=
    LatGreen.W1funPeriodSummable h hR hℓ hv_supp
  have hsum := chat_sq_div_summable h hv hvrad hR hℓ hv_supp hRℓ
  have hint : MeasureTheory.Integrable
      (fun q : E3 => (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
    IntegrableChatW1sq h hv hvrad hR hℓ hv_supp hRℓ
  -- ## 2.1 the finiteness of the `(latDistL)⁻¹` pair integral on the cell
  have hφm : Measurable (fun z : E3 => (latDistL ℓ z)⁻¹) := measurable_infDist.inv
  have hφnn : 0 ≤ᵐ[(MeasureTheory.volume : Measure E3)] (fun z : E3 => (latDistL ℓ z)⁻¹) :=
    Filter.Eventually.of_forall fun z => inv_nonneg.mpr (latDistL_nonneg ℓ z)
  have hφper : ∀ (z : E3) (n : Fin 3 → ℤ),
      (fun z : E3 => (latDistL ℓ z)⁻¹) (z + lat ℓ n)
        = (fun z : E3 => (latDistL ℓ z)⁻¹) z := by
    intro z n
    simp only
    rw [latDistL_period]
  have hfold := FarLat.fold_periodic_lintegral hℓ hW hWae hWper
    (φ := fun z : E3 => (latDistL ℓ z)⁻¹) hφm hφnn hφper
  have hcmp : (fun q : E3 × E3 => ENNReal.ofReal (W1fun v h ℓ q.1 * W1fun v h ℓ q.2
        * (latDistL ℓ (q.1 - q.2))⁻¹))
      ≤ᵐ[(MeasureTheory.volume : Measure (E3 × E3))]
      (fun q : E3 × E3 => ENNReal.ofReal (W1fun v h ℓ q.1 * W1fun v h ℓ q.2
        * (∑ p ∈ latFin9, (‖q.1 - q.2 - lat ℓ p‖)⁻¹))) := by
    filter_upwards with q
    by_cases h2 : ‖q.1 - q.2‖ ≤ 2 * ℓ
    · exact ofReal_mul_le_ofReal_mul (inv_nonneg.mpr (latDistL_nonneg ℓ _))
        (FarLat.inv_latDistL_le_latFin9 hℓ h2)
    · have hlt : 2 * ℓ < ‖q.1 - q.2‖ := lt_of_not_ge h2
      have hzero : W1fun v h ℓ q.1 = 0 ∨ W1fun v h ℓ q.2 = 0 := by
        by_contra hc
        push_neg at hc
        have hsuppW := tsupport_W1fun_subset h hv_supp ℓ
        have h3 : ‖q.1‖ < R := by
          have := hsuppW (subset_tsupport _ (Function.mem_support.mpr hc.1))
          simpa [Metric.mem_ball, dist_zero_right] using this
        have h4 : ‖q.2‖ < R := by
          have := hsuppW (subset_tsupport _ (Function.mem_support.mpr hc.2))
          simpa [Metric.mem_ball, dist_zero_right] using this
        have h5 : ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
        linarith
      rcases hzero with hz | hz <;> simp [hz]
  have hfin : (∫⁻ p in (cell ℓ ×ˢ cell ℓ),
      ENNReal.ofReal (LatGreen.period (W1fun v h ℓ) ℓ p.1
        * LatGreen.period (W1fun v h ℓ) ℓ p.2
        * (latDistL ℓ (p.1 - p.2))⁻¹)) < ⊤ := by
    rw [hfold]
    exact lt_of_le_of_lt (lintegral_mono_ae hcmp)
      (W1fun_pairKernel_latFin9_lintegral_lt_top h hv hvrad hR hℓ hv_supp hRℓ)
  -- ## 2.2 the two consumers of `hfin`
  have hB := FarLat.latGreen_period_integrable hℓ hW hWae hWper hfin
  have hmono := FarLat.latGreen_le_latDistL_pair hℓ hW hWae hWper hB hfin
  have hP := LatGreen.LatGreenParsevalB hℓ hW hWev hWper hsum hB
  -- ## 2.3 the cell integral of the Green kernel equals the full-space Coulomb pair integral
  have hPcell : ∀ x : E3, x ∈ cell ℓ → LatGreen.period (W1fun v h ℓ) ℓ x = W1fun v h ℓ x :=
    fun x hx => lwsq_period_eq_of_mem_cell hℓ hreg
      (fun y hy => LatGreen.W1fun_eq_zero_of_le_norm h hv_supp hy) hx
  have hmeas_cell : MeasurableSet (cell ℓ ×ˢ cell ℓ) :=
    (LatGreen.measurableSet_cell ℓ).prod (LatGreen.measurableSet_cell ℓ)
  -- (i) on the support of the periodisation the lattice distance is the norm
  have hstep5 : (∫ p in (cell ℓ ×ˢ cell ℓ),
        LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
          * (latDistL ℓ (p.1 - p.2))⁻¹)
      = ∫ p in (cell ℓ ×ˢ cell ℓ),
        LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
          * (‖p.1 - p.2‖)⁻¹ := by
    refine MeasureTheory.setIntegral_congr_fun hmeas_cell fun p hp => ?_
    rw [hPcell p.1 hp.1, hPcell p.2 hp.2]
    by_cases h1 : W1fun v h ℓ p.1 = 0
    · simp [h1]
    by_cases h2 : W1fun v h ℓ p.2 = 0
    · simp [h2]
    have hnorm : ‖p.1 - p.2‖ ≤ ℓ / 2 := by
      have hsuppW := tsupport_W1fun_subset h hv_supp ℓ
      have h3 : ‖p.1‖ < R := by
        have := hsuppW (subset_tsupport _ (Function.mem_support.mpr h1))
        simpa [Metric.mem_ball, dist_zero_right] using this
      have h4 : ‖p.2‖ < R := by
        have := hsuppW (subset_tsupport _ (Function.mem_support.mpr h2))
        simpa [Metric.mem_ball, dist_zero_right] using this
      have h5 : ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
      linarith
    rw [lwsq_latDistL_eq_norm_of_le hℓ hnorm]
  -- (ii) the periodisation equals the charge on the cell
  have hstep6a : (∫ p in (cell ℓ ×ˢ cell ℓ),
        LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
          * (‖p.1 - p.2‖)⁻¹)
      = ∫ p in (cell ℓ ×ˢ cell ℓ),
        W1fun v h ℓ p.1 * W1fun v h ℓ p.2 * (‖p.1 - p.2‖)⁻¹ :=
    MeasureTheory.setIntegral_congr_fun hmeas_cell fun p hp => by
      rw [hPcell p.1 hp.1, hPcell p.2 hp.2]
  -- (iii) the charge vanishes off the cell, so the cell integral is the full integral
  have hstep6b : (∫ p in (cell ℓ ×ˢ cell ℓ),
        W1fun v h ℓ p.1 * W1fun v h ℓ p.2 * (‖p.1 - p.2‖)⁻¹)
      = ∫ p : E3 × E3, W1fun v h ℓ p.1 * W1fun v h ℓ p.2 * (‖p.1 - p.2‖)⁻¹ := by
    refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · rw [lwsq_W1fun_eq_zero_of_not_mem_cell h hℓ hreg hv_supp hp]; ring
    · rw [lwsq_W1fun_eq_zero_of_not_mem_cell h hℓ hreg hv_supp hp]; ring
  -- (iv) the iterated cell integral is the product cell integral (Fubini)
  have hμc : MeasureTheory.volume.restrict (cell ℓ ×ˢ cell ℓ)
      = ((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (cell ℓ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod E3 E3]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hfub : (∫ x in cell ℓ, ∫ y in cell ℓ,
        LatGreen.period (W1fun v h ℓ) ℓ x * LatGreen.period (W1fun v h ℓ) ℓ y
          * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (x - y))))
      = ∫ p in (cell ℓ ×ˢ cell ℓ),
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) := by
    have hPae : AEMeasurable (LatGreen.period (W1fun v h ℓ) ℓ)
        ((MeasureTheory.volume : Measure E3).restrict (cell ℓ)) :=
      (LatGreen.integrableOn_period hℓ hW hWper).1.aemeasurable
    have hasm : AEStronglyMeasurable
        (fun p : E3 × E3 =>
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
        (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
          ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
      have h1 : AEMeasurable (fun p : E3 × E3 => LatGreen.period (W1fun v h ℓ) ℓ p.1)
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := hPae.comp_fst
      have h2 : AEMeasurable (fun p : E3 × E3 => LatGreen.period (W1fun v h ℓ) ℓ p.2)
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := hPae.comp_snd
      have h3 : AEMeasurable
          (fun p : E3 × E3 => ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
        refine ((LatGreen.measurable_latGreen.comp
          ((measurable_fst.sub measurable_snd).const_smul (ℓ⁻¹ : ℝ))).const_mul _).aemeasurable
      exact ((h1.mul h2).mul h3).aestronglyMeasurable
    have hint' : MeasureTheory.Integrable
        (fun p : E3 × E3 =>
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))))
        (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
          ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
      have hB' : MeasureTheory.Integrable
          (fun p : E3 × E3 =>
            |LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
              * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))|)
          (((MeasureTheory.volume : Measure E3).restrict (cell ℓ)).prod
            ((MeasureTheory.volume : Measure E3).restrict (cell ℓ))) := by
        rw [← hμc]
        exact hB
      exact hB'.mono' hasm (Filter.Eventually.of_forall fun p => le_of_eq (by
        rw [Real.norm_eq_abs]))
    have h := MeasureTheory.integral_prod
      (fun p : E3 × E3 =>
        LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
          * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2)))) hint'
    rw [hμc]
    exact h.symm
  -- ## 2.4 the two Coulomb identities
  have hpair := LatGreen.coulomb_pair_eq_autocorr_integral hW hWnn hWev hint
  have hcoul := coulomb_autocorr_eq hW hWae hWev hint
  -- ## 2.5 the chain
  calc (∑' k : Fin 3 → ℤ, if k = 0 then 0 else
        (chat (W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec k)) ^ 2
          / ‖ℓ⁻¹ • Work.BoseB4.vec k‖ ^ 2)
      = ∫ x in cell ℓ, ∫ y in cell ℓ,
          LatGreen.period (W1fun v h ℓ) ℓ x * LatGreen.period (W1fun v h ℓ) ℓ y
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (x - y))) := hP
    _ = ∫ p in (cell ℓ ×ˢ cell ℓ),
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (ℓ ^ 2 * LatGreen.latGreen (ℓ⁻¹ • (p.1 - p.2))) := hfub
    _ ≤ (ℓ ^ 3 / (4 * Real.pi)) * ∫ p in (cell ℓ ×ˢ cell ℓ),
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (latDistL ℓ (p.1 - p.2))⁻¹ := hmono
    _ = (ℓ ^ 3 / (4 * Real.pi)) * ∫ p in (cell ℓ ×ˢ cell ℓ),
          LatGreen.period (W1fun v h ℓ) ℓ p.1 * LatGreen.period (W1fun v h ℓ) ℓ p.2
            * (‖p.1 - p.2‖)⁻¹ := by rw [hstep5]
    _ = (ℓ ^ 3 / (4 * Real.pi)) * ∫ p in (cell ℓ ×ˢ cell ℓ),
          W1fun v h ℓ p.1 * W1fun v h ℓ p.2 * (‖p.1 - p.2‖)⁻¹ := by rw [hstep6a]
    _ = (ℓ ^ 3 / (4 * Real.pi)) *
          ∫ p : E3 × E3, W1fun v h ℓ p.1 * W1fun v h ℓ p.2 * (‖p.1 - p.2‖)⁻¹ := by
        rw [hstep6b]
    _ = (ℓ ^ 3 / (4 * Real.pi)) *
          ∫ u : E3, (∫ x : E3, W1fun v h ℓ x * W1fun v h ℓ (x + u)) / ‖u‖ := by
        rw [← hpair]
        refine congrArg (fun t => (ℓ ^ 3 / (4 * Real.pi)) * t) ?_
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    _ = (ℓ ^ 3 / (4 * Real.pi)) *
          (8 * Real.pi * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ q : E3, (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2))) := by rw [hcoul]
    _ = 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : E3, (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
        have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
        field_simp
        ring

/-! ## 3. The target -/

theorem lattice_W1sq_over_tau_le_sharp {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v) {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hreg : 100 * R ≤ ℓ)
    (hW : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ))
    (hWnn : 0 ≤ Work.BoseFixR.W1fun v h ℓ) (N : ℕ) :
    (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      ≤ (6 / 5) * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3),
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
  classical
  have hsum := chat_sq_div_summable h hv hvrad hR hℓ hv_supp hRℓ
  have hkey := lwsq_lattice_row_sharp h hv hvrad hR hℓ hv_supp hRℓ hreg hW hWnn
  set F : (Fin 3 → ℤ) → ℝ := fun m => if m = 0 then 0
      else (chat (W1fun v h ℓ) (ℓ⁻¹ • Work.BoseB4.vec m)) ^ 2
        / ‖ℓ⁻¹ • Work.BoseB4.vec m‖ ^ 2 with hF
  set T : Finset (Fin 3 → ℤ) :=
    ((Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0).image
      (Work.BoseBoxFock.labVec N) with hT
  have hFnn : ∀ m : Fin 3 → ℤ, 0 ≤ F m := by
    intro m
    rw [hF]
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, if_false]
      exact div_nonneg (sq_nonneg _) (by positivity)
  have hlabVec_zero : Work.BoseBoxFock.labVec N (0 : Work.BoseBoxFock.Lab N) = 0 := by
    funext i
    simp [Work.BoseBoxFock.labVec]
  have hT0 : (0 : Fin 3 → ℤ) ∉ T := by
    rw [hT, Finset.mem_image]
    rintro ⟨k, hk, hk0⟩
    rw [Finset.mem_erase] at hk
    exact hk.1 (Work.BoseFixR.labVec_injective N (by rw [hk0, hlabVec_zero]))
  have hsumF : Summable F := by rw [hF]; exact hsum
  have hTsummand : ∀ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
      (chat (W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2)
        = (1 / 2) * F (Work.BoseBoxFock.labVec N k) := by
    intro k hk
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
    have hlv : Work.BoseBoxFock.labVec N k ≠ 0 := by
      intro hh
      exact hk0 (Work.BoseFixR.labVec_injective N (by rw [hh, hlabVec_zero]))
    rw [hF]
    simp only [hlv, if_false]
    rw [Work.BoseBoxFock.GramLab.kmomLab_eq_smul_vec]
    ring
  have hcube : (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (chat (W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      = (1 / 2) * ∑ m ∈ T, F m := by
    rw [hT, Finset.mul_sum]
    rw [Finset.sum_image (f := fun m => (1 / 2) * F m)
      (g := Work.BoseBoxFock.labVec N)
      (fun x _ y _ hxy => Work.BoseFixR.labVec_injective N hxy)]
    exact Finset.sum_congr rfl fun k hk => hTsummand k hk
  have hle : (∑ m ∈ T, F m) ≤ ∑' m : Fin 3 → ℤ, F m :=
    Summable.sum_le_tsum T (fun i _ => hFnn i) hsumF
  have hInt : 0 ≤ ∫ q : EuclideanSpace ℝ (Fin 3),
      (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) :=
    integral_nonneg fun q => div_nonneg (sq_nonneg _) (by positivity)
  have hkey' : (∑' m : Fin 3 → ℤ, F m) ≤ 2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
      ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
    rw [hF]; exact hkey
  calc (∑ k ∈ (Finset.univ : Finset (Work.BoseBoxFock.Lab N)).erase 0,
        (chat (W1fun v h ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
          / (2 * ‖Work.BoseBoxFock.kmomLab ℓ N k‖ ^ 2))
      = (1 / 2) * ∑ m ∈ T, F m := hcube
    _ ≤ (1 / 2) * ∑' m : Fin 3 → ℤ, F m :=
        mul_le_mul_of_nonneg_left hle (by norm_num)
    _ ≤ (1 / 2) * (2 * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey' (by norm_num)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by ring
    _ ≤ (6 / 5) * ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3 *
          ∫ q : EuclideanSpace ℝ (Fin 3), (chat (W1fun v h ℓ) q) ^ 2 / (2 * ‖q‖ ^ 2) := by
        nlinarith [hInt, mul_nonneg (by positivity : (0:ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3) hInt]

end Work.BoseFixR
