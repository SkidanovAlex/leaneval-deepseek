import Mathlib
import Mathlib.Order.Filter.CountableInter
import Submission.Commons.Analysis.Order.iSup_strictMono_chain_eq
import Submission.Commons.Analysis.Fourier.grid_cell_average_eq_triangular
import Submission.Commons.Analysis.Fourier.grid_shift_kernel_eq_triangular
import Submission.Commons.Analysis.Probability.martingale_variation_l2
import Submission.Commons.Analysis.Fourier.triangular_average_eq_grid_shift_average
import Submission.Commons.Analysis.Fourier.aemeasurable_grid_cell_integral_fixed_x
import Submission.Commons.Analysis.Fourier.aemeasurable_grid_shift_average_uncurry
import Submission.Commons.Analysis.Inequalities.finset_lp_minkowski
import Submission.Commons.Analysis.Integral.ellp_integral_minkowski
import Submission.Commons.Analysis.MeasureTheory.sq_lintegral_mul_le_mul_lintegral_mul_sq
import Submission.Commons.Analysis.MeasureTheory.minkowski_lintegral_sum

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Commons.Analysis.Fourier

noncomputable section

/-!
## The shifted dyadic grid on `ℝ`

`gridIdx k θ x = ⌊(x - θ)·2^k⌋` is the index of the level-`k` dyadic cell (resolution `2^{-k}`,
phase `θ`) that contains `x`.  `gridSigma k θ` is the σ-algebra of unions of those cells, and
`gridAvg k θ g x` is the average of `g` over the cell of `x`.
-/

/-- Index of the level-`k` dyadic grid cell of phase `θ` containing `x`. -/
def gridIdx (k : ℤ) (θ x : ℝ) : ℤ := ⌊(x - θ) * (2:ℝ)^k⌋

/-- The σ-algebra of the level-`k` dyadic grid of phase `θ`. -/
def gridSigma (k : ℤ) (θ : ℝ) : MeasurableSpace ℝ :=
  MeasurableSpace.comap (fun x : ℝ => gridIdx k θ x) ⊤

/-- Lower endpoint of the level-`k` grid cell of phase `θ` containing `x`. -/
def gridLo (k : ℤ) (θ x : ℝ) : ℝ := θ + (gridIdx k θ x : ℝ) * (2:ℝ)^(-k)

/-- The level-`k` grid cell of phase `θ` containing `x` (a half-open interval of length `2^{-k}`). -/
def gridCell (k : ℤ) (θ x : ℝ) : Set ℝ :=
  Set.Ioc (gridLo k θ x) (gridLo k θ x + (2:ℝ)^(-k))

/-- Average of `g` over the level-`k` grid cell of phase `θ` containing `x`. -/
def gridAvg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℤ) (θ : ℝ)
    (g : ℝ → E) (x : ℝ) : E :=
  ((2:ℝ)^k) • ∫ y in gridCell k θ x, g y

/-- The triangular (Fejér) averaging operator at scale `2^{-k}`. -/
def triOp (k : ℤ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, g y * ((2:ℝ)^k * max 0 (1 - (2:ℝ)^k * |x - y|))

/-! ## Elementary grid computations -/

lemma floor_div_pow (A : ℝ) (d : ℕ) : ⌊A / (2:ℝ)^d⌋ = ⌊(⌊A⌋ : ℝ) / (2:ℝ)^d⌋ := by
  have hp : (2:ℝ)^d = ((2^d : ℕ) : ℝ) := by push_cast; ring
  rw [hp, Int.floor_div_natCast, Int.floor_div_natCast, Int.floor_intCast]

lemma gridIdx_add_nat (k : ℤ) (d : ℕ) (θ x : ℝ) :
    gridIdx (k + d) θ x = ⌊(x - θ) * ((2:ℝ)^k * (2:ℝ)^d)⌋ := by
  unfold gridIdx
  have : (k + (d:ℤ)) = (k + d) := by simp
  rw [← this, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  simp

lemma gridIdx_factor (k : ℤ) (d : ℕ) (θ x : ℝ) :
    gridIdx k θ x = ⌊(gridIdx (k + d) θ x : ℝ) / (2:ℝ)^d⌋ := by
  have hB : (gridIdx (k + d) θ x : ℝ) = (⌊(x - θ) * ((2:ℝ)^k * (2:ℝ)^d)⌋ : ℝ) :=
    congrArg (fun z : ℤ => (z : ℝ)) (gridIdx_add_nat k d θ x)
  rw [hB]
  unfold gridIdx
  rw [show (x - θ) * (2:ℝ)^k = (x - θ) * ((2:ℝ)^k * (2:ℝ)^d) / (2:ℝ)^d by field_simp]
  rw [floor_div_pow]

lemma gridSigma_le_borel (k : ℤ) (θ : ℝ) : gridSigma k θ ≤ borel ℝ := by
  rw [gridSigma, ← measurable_iff_comap_le]
  exact Measurable.floor (by fun_prop)

lemma gridSigma_le_add (k : ℤ) (d : ℕ) (θ : ℝ) : gridSigma k θ ≤ gridSigma (k + d) θ := by
  rw [gridSigma, gridSigma, ← measurable_iff_comap_le]
  rw [measurable_iff_comap_le]
  have hf : gridIdx k θ = (fun m : ℤ => ⌊(m : ℝ) / (2:ℝ)^d⌋) ∘ (gridIdx (k + d) θ) := by
    funext x; exact gridIdx_factor k d θ x
  rw [hf, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono le_top

/-- Characterisation of the level-`k` grid cell of phase `θ` via its index. -/
lemma gridIdx_eq_iff (k : ℤ) (θ : ℝ) (m : ℤ) (y : ℝ) :
    gridIdx k θ y = m ↔
      θ + (m:ℝ) * (2:ℝ)^(-k) ≤ y ∧ y < θ + ((m:ℝ)+1) * (2:ℝ)^(-k) := by
  rw [gridIdx, Int.floor_eq_iff]
  have hpos : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
  have hneg : (0:ℝ) < (2:ℝ)^(-k) := zpow_pos (by norm_num) (-k)
  have hk : (2:ℝ)^k * (2:ℝ)^(-k) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), show k + -k = (0:ℤ) by ring, zpow_zero]
  have hk' : (2:ℝ)^(-k) * (2:ℝ)^k = 1 := by
    rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), show -k + k = (0:ℤ) by ring, zpow_zero]
  have hmul : ∀ a : ℝ, a * (2:ℝ)^(-k) * (2:ℝ)^k = a := by
    intro a; rw [mul_assoc, hk', mul_one]
  have hmul2 : ∀ a : ℝ, a * (2:ℝ)^k * (2:ℝ)^(-k) = a := by
    intro a; rw [mul_assoc, hk, mul_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_right h1 hneg.le
      rw [hmul2] at h
      linarith
    · have h := mul_lt_mul_of_pos_right h2 hneg
      have he : ((m:ℝ)+1) * (2:ℝ)^(-k) = (m:ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k) := by ring
      rw [hmul2, he] at h
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h := mul_le_mul_of_nonneg_right h1 hpos.le
      have hm : ((m:ℝ) * (2:ℝ)^(-k)) * (2:ℝ)^k = (m:ℝ) := hmul _
      have hy : (y - θ) * (2:ℝ)^k = y * (2:ℝ)^k - θ * (2:ℝ)^k := by ring
      rw [add_mul, hm] at h
      rw [hy]; linarith
    · have h := mul_lt_mul_of_pos_right h2 hpos
      have hm : (((m:ℝ)+1) * (2:ℝ)^(-k)) * (2:ℝ)^k = (m:ℝ)+1 := hmul _
      have hy : (y - θ) * (2:ℝ)^k = y * (2:ℝ)^k - θ * (2:ℝ)^k := by ring
      rw [add_mul, hm] at h
      rw [hy]; linarith

/-- `gridAvg` depends on `x` only through the grid index. -/
lemma gridAvg_eq_of_gridIdx_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℤ) (θ : ℝ) (g : ℝ → E) {x y : ℝ}
    (h : gridIdx k θ x = gridIdx k θ y) : gridAvg k θ g x = gridAvg k θ g y := by
  unfold gridAvg gridCell gridLo
  rw [h]

/-! ## The grid fibres and their measures -/

/-- `gridIdx` is Borel measurable. -/
lemma measurable_gridIdx (k : ℤ) (θ : ℝ) : Measurable (gridIdx k θ) :=
  Measurable.floor (by fun_prop)

/-- The level-`k` grid fibre of phase `θ` with index `m`. -/
def gridFiber (k : ℤ) (θ : ℝ) (m : ℤ) : Set ℝ := {y | gridIdx k θ y = m}

lemma measurableSet_gridFiber (k : ℤ) (θ : ℝ) (m : ℤ) : MeasurableSet (gridFiber k θ m) :=
  (measurable_gridIdx k θ) (measurableSet_singleton m)

lemma measurableSet_gridFiber_gridSigma (k : ℤ) (θ : ℝ) (m : ℤ) :
    MeasurableSet[gridSigma k θ] (gridFiber k θ m) := by
  show MeasurableSet[MeasurableSpace.comap (gridIdx k θ) ⊤] (gridIdx k θ ⁻¹' {m})
  exact MeasurableSpace.measurableSet_comap.mpr ⟨{m}, trivial, rfl⟩

lemma gridFiber_eq_Ico (k : ℤ) (θ : ℝ) (m : ℤ) :
    gridFiber k θ m = Set.Ico (θ + (m:ℝ) * (2:ℝ)^(-k)) (θ + ((m:ℝ)+1) * (2:ℝ)^(-k)) := by
  ext y
  rw [gridFiber, Set.mem_ofPred_eq, Set.mem_Ico, gridIdx_eq_iff]

lemma volume_gridFiber (k : ℤ) (θ : ℝ) (m : ℤ) :
    volume (gridFiber k θ m) = ENNReal.ofReal ((2:ℝ)^(-k)) := by
  rw [gridFiber_eq_Ico, Real.volume_Ico]
  congr 1
  ring

lemma volume_gridFiber_ne_top (k : ℤ) (θ : ℝ) (m : ℤ) :
    volume (gridFiber k θ m) ≠ ⊤ := by
  rw [volume_gridFiber]; exact ENNReal.ofReal_ne_top

lemma volumeReal_gridFiber (k : ℤ) (θ : ℝ) (m : ℤ) :
    (volume (gridFiber k θ m)).toReal = (2:ℝ)^(-k) := by
  rw [volume_gridFiber, ENNReal.toReal_ofReal (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-k))]

lemma iUnion_gridFiber (k : ℤ) (θ : ℝ) : (⋃ m : ℤ, gridFiber k θ m) = Set.univ := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨gridIdx k θ y, rfl⟩

lemma pairwiseDisjoint_gridFiber (k : ℤ) (θ : ℝ) :
    Pairwise (fun m m' => Disjoint (gridFiber k θ m) (gridFiber k θ m')) := by
  intro m m' h
  rw [Set.disjoint_left]
  intro y hy hy'
  exact h (hy.symm.trans hy')

lemma gridAvg_eq_fiberIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℤ) (θ : ℝ) (g : ℝ → E) {m : ℤ} {x : ℝ} (hx : x ∈ gridFiber k θ m) :
    gridAvg k θ g x = ((2:ℝ)^k) • ∫ y in gridFiber k θ m, g y := by
  have hxc : gridIdx k θ x = m := hx
  rw [gridAvg, gridCell, gridLo, hxc, gridFiber_eq_Ico,
    show θ + (m:ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k) = θ + ((m:ℝ)+1) * (2:ℝ)^(-k) by ring,
    integral_Ioc_eq_integral_Ioo, integral_Ico_eq_integral_Ioo]

lemma setIntegral_gridAvg_gridFiber {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (k : ℤ) (θ : ℝ) (g : ℝ → E) (m : ℤ) :
    ∫ y in gridFiber k θ m, gridAvg k θ g y = ∫ y in gridFiber k θ m, g y := by
  rw [setIntegral_congr_fun (measurableSet_gridFiber k θ m)
    (fun y hy => gridAvg_eq_fiberIntegral k θ g hy), setIntegral_const, smul_smul,
    Measure.real_def, volumeReal_gridFiber,
    show (2:ℝ)^(-k) * (2:ℝ)^k = 1 by
      rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), show -k + k = (0:ℤ) by ring, zpow_zero],
    one_smul]

/-- The grid average is bounded by the (a.e.) bound on `g`. -/
lemma gridAvg_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℤ) (θ : ℝ) (g : ℝ → E) (C : ℝ) (hC : ∀ᵐ x ∂volume, ‖g x‖ ≤ C) :
    ∀ᵐ x ∂volume, ‖gridAvg k θ g x‖ ≤ C := by
  filter_upwards [hC] with x hx
  have hx' : x ∈ gridFiber k θ (gridIdx k θ x) := rfl
  rw [gridAvg_eq_fiberIntegral k θ g hx']
  haveI : IsFiniteMeasure (volume.restrict (gridFiber k θ (gridIdx k θ x))) :=
    isFiniteMeasure_restrict.mpr (volume_gridFiber_ne_top k θ _)
  have hnorm : ‖∫ y in gridFiber k θ (gridIdx k θ x), g y‖
      ≤ C * (volume (gridFiber k θ (gridIdx k θ x))).toReal := by
    have h1 := norm_integral_le_of_norm_le_const
      (μ := volume.restrict (gridFiber k θ (gridIdx k θ x))) (f := g) (C := C)
      (ae_restrict_of_ae hC)
    have h2 : (volume.restrict (gridFiber k θ (gridIdx k θ x))).real Set.univ
        = (volume (gridFiber k θ (gridIdx k θ x))).toReal := by
      rw [Measure.real_def, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rwa [h2] at h1
  calc ‖(2:ℝ)^k • ∫ y in gridFiber k θ (gridIdx k θ x), g y‖
      = (2:ℝ)^k * ‖∫ y in gridFiber k θ (gridIdx k θ x), g y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)]
    _ ≤ (2:ℝ)^k * (C * (volume (gridFiber k θ (gridIdx k θ x))).toReal) :=
        mul_le_mul_of_nonneg_left hnorm (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) k)
    _ = C := by
        rw [volumeReal_gridFiber, ← mul_assoc, mul_comm ((2:ℝ)^k) C, mul_assoc,
          show (2:ℝ)^k * (2:ℝ)^(-k) = 1 by
            rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), show k + -k = (0:ℤ) by ring,
              zpow_zero],
          mul_one]

/-- `gridAvg` is measurable for the grid σ-algebra. -/
lemma measurable_gridAvg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (k : ℤ) (θ : ℝ) (g : ℝ → E) : Measurable[gridSigma k θ] (gridAvg k θ g) := by
  have hfac : gridAvg k θ g
      = fun x => ((2:ℝ)^k) • ∫ y in gridFiber k θ (gridIdx k θ x), g y := by
    funext x; exact gridAvg_eq_fiberIntegral k θ g rfl
  rw [hfac]
  have hG : Measurable (fun m : ℤ => ((2:ℝ)^k) • ∫ y in gridFiber k θ m, g y) :=
    fun s _ => trivial
  exact hG.comp (measurable_iff_comap_le.mpr le_rfl)

lemma sigmaFinite_trim_gridSigma (k : ℤ) (θ : ℝ) :
    SigmaFinite (volume.trim (gridSigma_le_borel k θ)) := by
  refine Measure.sigmaFinite_of_countable (Set.countable_range (gridFiber k θ)) ?_ ?_
  · rintro u ⟨m, rfl⟩
    rw [trim_measurableSet_eq _ (measurableSet_gridFiber_gridSigma k θ m), volume_gridFiber]
    exact ENNReal.ofReal_lt_top
  · rw [Set.sUnion_range]; exact iUnion_gridFiber k θ

/-- The level-indexed filtration of shifted dyadic grids with a common phase `θ`. -/
def gridFiltration (K : ℤ) (θ : ℝ) : Filtration ℕ (borel ℝ) where
  seq n := gridSigma (K + n) θ
  mono' i j hij := by
    change gridSigma (K + (i:ℤ)) θ ≤ gridSigma (K + (j:ℤ)) θ
    have h : K + (i:ℤ) + (((j:ℤ) - i).toNat : ℤ) = K + j := by
      have h0 : ((j:ℤ) - i).toNat = (j:ℤ) - i := Int.toNat_of_nonneg (by omega)
      omega
    rw [← h]
    exact gridSigma_le_add (K + (i:ℤ)) (((j:ℤ)-i).toNat) θ
  le' n := gridSigma_le_borel (K + n) θ

lemma sigmaFiniteFiltration_gridFiltration (K : ℤ) (θ : ℝ) :
    SigmaFiniteFiltration volume (gridFiltration K θ) :=
  ⟨fun n => sigmaFinite_trim_gridSigma (K + n) θ⟩

lemma iSup_Vtr_eq (g : ℕ → ℝ → ℝ) (s : ℝ) (x : ℝ) :
    (⨆ N : ℕ, Commons.Analysis.Probability.Vtr g s N x) =
      ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        ENNReal.ofReal ((∑ j ∈ Finset.range J, |g (u.1 (j+1)) x - g (u.1 j) x| ^ s) ^ (1/s)) := by
  apply le_antisymm
  · refine iSup_le fun N => ?_
    rw [Commons.Analysis.Probability.Vtr]
    refine iSup_le fun u => iSup_le fun J => ?_
    split_ifs with h
    · exact le_iSup_of_le u (le_iSup_of_le J le_rfl)
    · exact bot_le
  · refine iSup_le fun u => iSup_le fun J => ?_
    have h1 : ENNReal.ofReal ((∑ j ∈ Finset.range J,
          |g (u.1 (j+1)) x - g (u.1 j) x| ^ s) ^ (1/s))
        ≤ Commons.Analysis.Probability.Vtr g s (u.1 J) x := by
      rw [Commons.Analysis.Probability.Vtr]
      exact le_iSup_of_le u (le_iSup_of_le J (by simp))
    exact h1.trans (le_iSup (fun N => Commons.Analysis.Probability.Vtr g s N x) (u.1 J))

/-- The grid-average of `g` over the level-`k`, phase-`θ` grid is a version of the conditional
expectation of `g` on `gridSigma k θ`. -/
theorem gridAvg_ae_eq_condExp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (k : ℤ) (θ : ℝ) (g : ℝ → E) (hgi : Integrable g volume)
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂volume, ‖g x‖ ≤ C)
    (hmeasSig : AEStronglyMeasurable[gridSigma k θ] (gridAvg k θ g)) :
    gridAvg k θ g =ᵐ[volume] condExp (gridSigma k θ) volume g := by
  obtain ⟨C, hC⟩ := hbd
  haveI : SigmaFinite (volume.trim (gridSigma_le_borel k θ)) := sigmaFinite_trim_gridSigma k θ
  have hmeas : AEStronglyMeasurable (gridAvg k θ g) volume :=
    hmeasSig.mono (gridSigma_le_borel k θ)
  refine ae_eq_condExp_of_forall_setIntegral_eq (gridSigma_le_borel k θ) hgi ?_ ?_ hmeasSig
  · intro s _ hfin
    exact Measure.integrableOn_of_bounded hfin.ne hmeas
      (ae_restrict_of_ae (gridAvg_norm_le k θ g C hC))
  · intro s hs hfin
    have hs' : MeasurableSet[MeasurableSpace.comap (gridIdx k θ) ⊤] s := hs
    obtain ⟨t, htmeas, ht⟩ :=
      (MeasurableSpace.measurableSet_comap (f := gridIdx k θ) (m := ⊤)).mp hs'
    rw [← ht] at hfin ⊢
    have hUi : (⋃ m : ℤ, (gridIdx k θ ⁻¹' t ∩ gridFiber k θ m)) = gridIdx k θ ⁻¹' t := by
      rw [← Set.inter_iUnion, iUnion_gridFiber, Set.inter_univ]
    have hdisj : Pairwise (fun m m' => Disjoint (gridIdx k θ ⁻¹' t ∩ gridFiber k θ m)
        (gridIdx k θ ⁻¹' t ∩ gridFiber k θ m')) := by
      intro m m' h
      exact (pairwiseDisjoint_gridFiber k θ h).mono Set.inter_subset_right Set.inter_subset_right
    have hmeasible : ∀ m : ℤ, MeasurableSet (gridIdx k θ ⁻¹' t ∩ gridFiber k θ m) :=
      fun m => (measurable_gridIdx k θ htmeas).inter (measurableSet_gridFiber k θ m)
    rw [← hUi]
    rw [integral_iUnion hmeasible hdisj (Measure.integrableOn_of_bounded
      (by rw [hUi]; exact hfin.ne) hmeas
      (ae_restrict_of_ae (gridAvg_norm_le k θ g C hC)))]
    rw [integral_iUnion hmeasible hdisj hgi.integrableOn]
    refine tsum_congr (fun m => ?_)
    by_cases hne : (gridIdx k θ ⁻¹' t ∩ gridFiber k θ m).Nonempty
    · obtain ⟨y, hy⟩ := hne
      have hsub : gridFiber k θ m ⊆ gridIdx k θ ⁻¹' t := by
        intro z hz
        show gridIdx k θ z ∈ t
        rw [show gridIdx k θ z = m from hz, ← show gridIdx k θ y = m from hy.2]
        exact hy.1
      rw [Set.inter_eq_right.mpr hsub]
      exact setIntegral_gridAvg_gridFiber k θ g m
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne, setIntegral_empty, setIntegral_empty]

/-- Complex-valued form of `gridAvg_ae_eq_condExp`. -/
theorem gridAvgC_ae_eq_condExp (k : ℤ) (θ : ℝ) (g : ℝ → ℂ)
    (hgi : Integrable g volume) (hbd : ∃ C : ℝ, ∀ᵐ x ∂volume, ‖g x‖ ≤ C) :
    gridAvg k θ g =ᵐ[volume] condExp (gridSigma k θ) volume g :=
  gridAvg_ae_eq_condExp k θ g hgi hbd
    ((measurable_gridAvg k θ g).stronglyMeasurable.aestronglyMeasurable)

/-- Real-valued form of `gridAvg_ae_eq_condExp`. -/
theorem gridAvgR_ae_eq_condExp (k : ℤ) (θ : ℝ) (f : ℝ → ℝ)
    (hgi : Integrable f volume) (hbd : ∃ C : ℝ, ∀ᵐ x ∂volume, ‖f x‖ ≤ C) :
    gridAvg k θ f =ᵐ[volume] condExp (gridSigma k θ) volume f :=
  gridAvg_ae_eq_condExp k θ f hgi hbd
    ((measurable_gridAvg k θ f).stronglyMeasurable.aestronglyMeasurable)

/-- The `L²` martingale variation bound for the shifted dyadic grid averages, at a fixed phase
`θ`, for a real-valued function. -/
lemma gridAvg_variation_bound (K : ℤ) (θ : ℝ) (f : ℝ → ℝ) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hfi : Integrable f (volume : Measure ℝ))
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ ≤ C) :
    eLpNorm (fun x => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
      ENNReal.ofReal ((∑ j ∈ Finset.range J,
        ‖gridAvg (K + (u.1 (j+1) : ℤ)) θ f x - gridAvg (K + (u.1 j : ℤ)) θ f x‖ ^ s)
        ^ (1/s))) 2 (volume : Measure ℝ)
      ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 (volume : Measure ℝ) := by
  haveI := sigmaFiniteFiltration_gridFiltration K θ
  have hmain := Commons.Analysis.Probability.mv_eLpNorm_Vinf_le'
    (gridFiltration K θ) f hf hs hs3
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ∀ n : ℕ,
      condExp (gridSigma (K + n) θ) (volume : Measure ℝ) f x = gridAvg (K + n) θ f x := by
    rw [_root_.eventually_countable_forall]
    intro n
    exact (gridAvgR_ae_eq_condExp (K + n) θ f hfi hbd).symm
  have hae2 : (fun x => ⨆ N : ℕ,
        Commons.Analysis.Probability.Vtr
          (fun n => condExp (gridSigma (K + n) θ) (volume : Measure ℝ) f) s N x)
      =ᵐ[(volume : Measure ℝ)]
      (fun x => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        ENNReal.ofReal ((∑ j ∈ Finset.range J,
          ‖gridAvg (K + (u.1 (j+1) : ℤ)) θ f x - gridAvg (K + (u.1 j : ℤ)) θ f x‖ ^ s)
          ^ (1/s))) := by
    filter_upwards [hae] with x hx
    rw [iSup_Vtr_eq]
    refine iSup_congr fun u => iSup_congr fun J => ?_
    refine congrArg (fun t => ENNReal.ofReal (t ^ (1/s))) ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hx (u.1 (j+1)), hx (u.1 j), Real.norm_eq_abs]
  rw [← MeasureTheory.eLpNorm_congr_ae hae2]
  exact hmain

/-- The `s`-variation of the shifted dyadic grid averages at phase `θ`, as a function of `x`
(countably-indexed: the chains are `Fin (J+1) → ℕ`). -/
def GV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ℤ) (θ : ℝ) (f : ℝ → E)
    (s : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (k : Fin (J+1) → ℕ) (_ : StrictMono k),
    ENNReal.ofReal ((∑ j : Fin J,
      ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ f x
        - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ f x‖ ^ s) ^ (1/s))

/-- The martingale `L²` bound for the grid variation. -/
lemma GV_eLpNorm_le (K : ℤ) (θ : ℝ) (f : ℝ → ℝ) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hfi : Integrable f (volume : Measure ℝ))
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂(volume : Measure ℝ), ‖f x‖ ≤ C) :
    eLpNorm (fun x => GV K θ f s x) 2 (volume : Measure ℝ)
      ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm f 2 (volume : Measure ℝ) := by
  have h1 : (fun x => GV K θ f s x)
      = fun x => ⨆ (u : {u : ℕ → ℕ // StrictMono u}) (J : ℕ),
        ENNReal.ofReal ((∑ j ∈ Finset.range J,
          ‖gridAvg (K + (u.1 (j+1) : ℤ)) θ f x
            - gridAvg (K + (u.1 j : ℤ)) θ f x‖ ^ s) ^ (1/s)) := by
    funext x
    simp only [GV]
    rw [← Commons.Analysis.Order.iSup_strictMono_chain_eq (fun J (k : Fin (J+1) → ℕ) =>
      ENNReal.ofReal ((∑ j : Fin J,
        ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ f x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ f x‖ ^ s) ^ (1/s)))]
    refine iSup_congr fun u => iSup_congr fun J => ?_
    refine congrArg (fun t => ENNReal.ofReal (t ^ (1/s))) ?_
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      ‖gridAvg (K + (u.1 (j+1) : ℤ)) θ f x - gridAvg (K + (u.1 j : ℤ)) θ f x‖ ^ s) J]
  rw [h1]
  exact gridAvg_variation_bound K θ f s hs hs3 hf hfi hbd


/-- The `s`-variation of the triangular averages, as in the target statement. -/
def TV (g : ℝ → ℂ) (s : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (k : Fin (J+1) → ℤ) (_ : StrictMono k),
    ENNReal.ofReal ((∑ j : Fin J,
      ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s))

/-- The same variation restricted to chains whose first index is at least `K`. -/
def TVK (K : ℤ) (g : ℝ → ℂ) (s : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (J : ℕ) (k : Fin (J+1) → ℤ) (_ : StrictMono k) (_ : K ≤ k 0),
    ENNReal.ofReal ((∑ j : Fin J,
      ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s))

lemma TV_eq_iSup_TVK (g : ℝ → ℂ) (s : ℝ) (x : ℝ) :
    TV g s x = ⨆ K : ℤ, TVK K g s x := by
  apply le_antisymm
  · refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    refine le_trans ?_ (le_iSup (fun K : ℤ => TVK K g s x) (k 0))
    refine le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk
      (le_iSup_of_le (le_rfl : k 0 ≤ k 0) le_rfl)))
  · refine iSup_le fun K => ?_
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => iSup_le fun hK => ?_
    exact le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))

/-! ## Auxiliary lemmas for the Fejér/dyadic variation estimate -/

set_option maxHeartbeats 8000000

/-- The Fejér/triangular average rewritten as the shift-average of grid averages. -/
lemma triOp_eq_gridAvg_interval (K k : ℤ) (hKk : K ≤ k) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    triOp k g x = (1 / (2:ℝ)^(-K)) * ∫ θ in (0:ℝ)..((2:ℝ)^(-K)), gridAvg k θ g x := by
  rw [triOp, triangular_average_eq_grid_shift_average K k hKk g hg x]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [gridAvg, gridCell, gridLo, gridIdx]
  rw [← Complex.ofReal_zpow]
  exact Complex.real_smul.symm

lemma gridAvg_norm_le_L1 (k : ℤ) (θ x : ℝ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ‖gridAvg k θ g x‖ ≤ (2:ℝ)^k * ∫ y, ‖g y‖ := by
  have hstep : ‖gridAvg k θ g x‖ ≤ (2:ℝ)^k * ∫ y in gridCell k θ x, ‖g y‖ := by
    rw [gridAvg, norm_smul, Real.norm_of_nonneg (zpow_nonneg (by norm_num) k)]
    exact mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _)
      (zpow_nonneg (by norm_num) k)
  refine hstep.trans ?_
  have h2 : ∫ y in gridCell k θ x, ‖g y‖ ≤ ∫ y, ‖g y‖ :=
    MeasureTheory.setIntegral_le_integral hg.norm (ae_of_all _ fun y => norm_nonneg _)
  exact mul_le_mul_of_nonneg_left h2 (zpow_nonneg (by norm_num) k)

lemma gridAvg_re (k : ℤ) (θ : ℝ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    (gridAvg k θ g x).re = gridAvg k θ (fun y => (g y).re) x := by
  rw [gridAvg, gridAvg, Complex.smul_re]
  congr 1
  exact (integral_re (μ := MeasureTheory.volume.restrict (gridCell k θ x)) hg.integrableOn).symm

lemma gridAvg_im (k : ℤ) (θ : ℝ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    (gridAvg k θ g x).im = gridAvg k θ (fun y => (g y).im) x := by
  rw [gridAvg, gridAvg, Complex.smul_im]
  congr 1
  exact (integral_im (μ := MeasureTheory.volume.restrict (gridCell k θ x)) hg.integrableOn).symm

lemma aemeasurable_gridAvg_theta (k : ℤ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    AEMeasurable (fun θ : ℝ => gridAvg k θ g x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have h := aemeasurable_grid_cell_integral_fixed_x k g hg x
  have h2 : (fun θ : ℝ => gridAvg k θ g x)
      = fun θ => ((2:ℝ)^k) • ∫ y in Set.Ioc
          (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
          (θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y := by
    funext θ
    rw [gridAvg, gridCell, gridLo, gridIdx]
  rw [h2]
  exact h.const_smul ((2:ℝ)^k)

lemma intervalIntegrable_gridAvg (k : ℤ) (A : ℝ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    IntervalIntegrable (fun θ : ℝ => gridAvg k θ g x) MeasureTheory.volume 0 A := by
  rw [intervalIntegrable_iff]
  refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ ((2:ℝ)^k * ∫ y, ‖g y‖) ?_
  · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
  · exact ((aemeasurable_gridAvg_theta k g hg x).mono_measure Measure.restrict_le_self).aestronglyMeasurable
  · refine ae_of_all _ fun θ => ?_
    exact gridAvg_norm_le_L1 k θ x g hg

lemma enorm_eq_ofReal_norm_aux {E : Type*} [SeminormedAddCommGroup E] (z : E) :
    ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [← enorm_norm z, Real.enorm_eq_ofReal (norm_nonneg z)]

/-- The chain sum of a single `Fin`-chain of grid averages is bounded by `GV`. -/
lemma grid_chain_le_GV (K : ℤ) (θ x : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (J : ℕ) (k : Fin (J+1) → ℤ) (hmono : StrictMono k) (hK : K ≤ k 0) :
    (∑ j : Fin J, ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ ^ s) ^ (1/s)
      ≤ GV K θ g s x := by
  set k' : Fin (J+1) → ℕ := fun j => (k j - K).toNat with hk'def
  have hkj : ∀ j : Fin (J+1), (0:ℤ) ≤ k j - K := by
    intro j
    have h0 : (k 0 : ℤ) ≤ k j := hmono.monotone (Fin.zero_le j)
    omega
  have hk' : ∀ j : Fin (J+1), K + ((k' j : ℕ) : ℤ) = k j := by
    intro j
    rw [hk'def]; simp only
    rw [Int.toNat_of_nonneg (hkj j)]; ring
  have hmono' : StrictMono k' := by
    intro i j hij
    have h1 : k i < k j := hmono hij
    have h4 : (k 0 : ℤ) ≤ k i := hmono.monotone (Fin.zero_le i)
    have h2 : (0:ℤ) < k j - K := by omega
    have h3 : k i - K < k j - K := by omega
    simp only [hk'def]
    rw [Int.toNat_lt_toNat h2]
    exact h3
  have hnormeq : ∀ j : Fin J,
      ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖
        = ‖gridAvg (K + ((k' (Fin.succ j) : ℕ) : ℤ)) θ g x
            - gridAvg (K + ((k' (Fin.castSucc j) : ℕ) : ℤ)) θ g x‖ := by
    intro j
    rw [← hk' (Fin.succ j), ← hk' (Fin.castSucc j)]
    exact norm_sub_rev _ _
  have hterm : ∀ j : Fin J,
      ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ ^ s
        = ENNReal.ofReal (‖gridAvg (K + ((k' (Fin.succ j) : ℕ) : ℤ)) θ g x
            - gridAvg (K + ((k' (Fin.castSucc j) : ℕ) : ℤ)) θ g x‖ ^ s) := by
    intro j
    rw [enorm_eq_ofReal_norm_aux, hnormeq j, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs.le]
  calc (∑ j : Fin J, ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ ^ s) ^ (1/s)
      = (∑ j : Fin J, ENNReal.ofReal (‖gridAvg (K + ((k' (Fin.succ j) : ℕ) : ℤ)) θ g x
            - gridAvg (K + ((k' (Fin.castSucc j) : ℕ) : ℤ)) θ g x‖ ^ s)) ^ (1/s) := by
        rw [Finset.sum_congr rfl fun j _ => hterm j]
    _ = (ENNReal.ofReal (∑ j : Fin J, ‖gridAvg (K + ((k' (Fin.succ j) : ℕ) : ℤ)) θ g x
            - gridAvg (K + ((k' (Fin.castSucc j) : ℕ) : ℤ)) θ g x‖ ^ s)) ^ (1/s) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) s)]
    _ = ENNReal.ofReal ((∑ j : Fin J, ‖gridAvg (K + ((k' (Fin.succ j) : ℕ) : ℤ)) θ g x
            - gridAvg (K + ((k' (Fin.castSucc j) : ℕ) : ℤ)) θ g x‖ ^ s) ^ (1/s)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg
          (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) (by positivity)]
    _ ≤ GV K θ g s x := le_iSup_of_le J (le_iSup_of_le k' (le_iSup_of_le hmono' le_rfl))

lemma aux_smul_sub (K : ℤ) (X Y : ℂ) :
    (1 / (2:ℝ)^(-K)) * X - (1 / (2:ℝ)^(-K)) * Y = ((2:ℝ)^K) • (X - Y) := by
  rw [Complex.real_smul, mul_sub]
  congr 1
  · rw [one_div, ← zpow_neg, neg_neg, ← Complex.ofReal_zpow]
  · rw [one_div, ← zpow_neg, neg_neg, ← Complex.ofReal_zpow]

/-- **Chainwise transference.**  For a single (`Fin`-indexed) chain of levels `k`, the `ℓ^s` norm of
the successive differences of the triangular averages at `x` is bounded by the average over the
shift `θ ∈ (0, 2^{-K})` of the grid variation `GV`. -/
lemma chain_bound (K : ℤ) (s : ℝ) (hs : 1 ≤ s) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (J : ℕ) (k : Fin (J+1) → ℤ) (hmono : StrictMono k) (hK : K ≤ k 0) (x : ℝ) :
    ENNReal.ofReal ((∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s))
      ≤ ENNReal.ofReal ((2:ℝ)^K) * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), GV K θ g s x := by
  have hs0 : (0:ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hApos : (0:ℝ) < (2:ℝ)^(-K) := zpow_pos (by norm_num) _
  have hKpos : (0:ℝ) < (2:ℝ)^K := zpow_pos (by norm_num) _
  have hinv : (1:ℝ) / (2:ℝ)^(-K) = (2:ℝ)^K := by rw [one_div, ← zpow_neg, neg_neg]
  have hle : ∀ j : Fin (J+1), K ≤ k j := fun j => hK.trans (hmono.monotone (Fin.zero_le j))
  -- (1) each difference is the interval integral of the grid-average differences
  have hD : ∀ j : Fin J,
      triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x
        = ((2:ℝ)^K) • ∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
            (gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x) := by
    intro j
    rw [triOp_eq_gridAvg_interval K _ (hle _) g hg x, triOp_eq_gridAvg_interval K _ (hle _) g hg x]
    rw [intervalIntegral.integral_sub (intervalIntegrable_gridAvg _ _ g hg x)
      (intervalIntegrable_gridAvg _ _ g hg x)]
    exact aux_smul_sub K _ _
  -- (2) norm bound in `ℝ≥0∞` for each difference
  have hbound : ∀ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ₑ
      ≤ ENNReal.ofReal ((2:ℝ)^K) * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
          ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ := by
    intro j
    rw [hD j, enorm_smul, Real.enorm_eq_ofReal (le_of_lt hKpos)]
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [show ‖∫ θ in (0:ℝ)..((2:ℝ)^(-K)),
          (gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x)‖ₑ
        = ‖∫ θ, (gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x)
            ∂(MeasureTheory.volume.restrict (Set.Ioc 0 ((2:ℝ)^(-K))))‖ₑ from by
      rw [intervalIntegral.integral_of_le hApos.le]]
    exact enorm_integral_le_lintegral_enorm _
  -- (3) Minkowski's integral inequality in `ℓ^s`
  have hmink : (∑ j : Fin J, (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
        ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ) ^ s) ^ (1/s)
      ≤ ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (∑ j : Fin J,
          ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ ^ s) ^ (1/s) := by
    have h := Commons.Analysis.MeasureTheory.minkowski_lintegral_sum
      (μ := MeasureTheory.volume.restrict (Set.Ioc 0 ((2:ℝ)^(-K)))) Finset.univ
      (fun j θ => ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ)
      s hs (fun j => ((aemeasurable_gridAvg_theta _ g hg x).sub
        (aemeasurable_gridAvg_theta _ g hg x)).enorm.mono_measure Measure.restrict_le_self)
    simpa using h
  -- (4) the algebraic combination
  have hsum : (∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ₑ ^ s) ^ (1/s)
      ≤ ENNReal.ofReal ((2:ℝ)^K) * (∑ j : Fin J, (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
          ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ) ^ s) ^ (1/s) := by
    have h1 : (∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ₑ ^ s)
        ≤ ∑ j : Fin J, (ENNReal.ofReal ((2:ℝ)^K) * (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
            ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ)) ^ s :=
      Finset.sum_le_sum fun j _ => ENNReal.rpow_le_rpow (hbound j) hs0.le
    have h2 : (∑ j : Fin J, (ENNReal.ofReal ((2:ℝ)^K) * (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
            ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ)) ^ s)
        = (ENNReal.ofReal ((2:ℝ)^K)) ^ s * ∑ j : Fin J, (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
            ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ) ^ s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => ENNReal.mul_rpow_of_nonneg _ _ hs0.le
    calc (∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ₑ ^ s) ^ (1/s)
        ≤ (∑ j : Fin J, (ENNReal.ofReal ((2:ℝ)^K) * (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
            ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ)) ^ s) ^ (1/s) :=
          ENNReal.rpow_le_rpow h1 (by positivity)
      _ = ((ENNReal.ofReal ((2:ℝ)^K)) ^ s * ∑ j : Fin J, (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
            ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ) ^ s) ^ (1/s) := by
          rw [h2]
      _ = ENNReal.ofReal ((2:ℝ)^K) * (∑ j : Fin J, (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
            ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ) ^ s) ^ (1/s) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1/s), ← ENNReal.rpow_mul,
            mul_one_div_cancel hs0.ne', ENNReal.rpow_one]
  have hLHSkey : ENNReal.ofReal ((∑ j : Fin J,
        ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s))
      = (∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ₑ ^ s) ^ (1/s) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg
          (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) (by positivity),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) s)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by
      rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hs0.le, ← enorm_eq_ofReal_norm_aux]
  rw [hLHSkey]
  calc (∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ₑ ^ s) ^ (1/s)
      ≤ ENNReal.ofReal ((2:ℝ)^K) * (∑ j : Fin J, (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
          ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ) ^ s) ^ (1/s) := hsum
    _ ≤ ENNReal.ofReal ((2:ℝ)^K) * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (∑ j : Fin J,
          ‖gridAvg (k (Fin.castSucc j)) θ g x - gridAvg (k (Fin.succ j)) θ g x‖ₑ ^ s) ^ (1/s) :=
        mul_le_mul_of_nonneg_left hmink zero_le
    _ ≤ ENNReal.ofReal ((2:ℝ)^K) * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), GV K θ g s x :=
        mul_le_mul_of_nonneg_left (MeasureTheory.lintegral_mono fun θ => grid_chain_le_GV K θ x g s hs0 J k hmono hK) zero_le

lemma eLpNorm_sq_ennreal {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    (G : α → ℝ≥0∞) (hG : AEStronglyMeasurable G μ) :
    (eLpNorm G (2:ℝ≥0∞) μ) ^ (2:ℝ) = ∫⁻ x, (G x) ^ (2:ℝ) ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hG]
  rw [show (1 / (2:ℝ≥0∞).toReal) = (1/2:ℝ) by norm_num, show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num]
  rw [← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  exact lintegral_congr fun x => by rw [enorm_eq_self]

lemma eLpNorm_sq_real {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    (f : α → ℝ) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f (2:ℝ≥0∞) μ) ^ (2:ℝ) = ∫⁻ x, ENNReal.ofReal ((f x) ^ 2) ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  rw [show (1 / (2:ℝ≥0∞).toReal) = (1/2:ℝ) by norm_num, show (2:ℝ≥0∞).toReal = (2:ℝ) by norm_num]
  rw [← ENNReal.rpow_mul, show (1/2:ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
  congr 1
  funext x
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  congr 1
  rw [Real.rpow_two, sq_abs]

/-- Minkowski's inequality in `ℓ^s` for sums of nonnegative real vectors. -/
lemma finset_rpow_add_le {ι : Type*} [Fintype ι] {s : ℝ} (hs : 1 ≤ s) (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, (a i + b i) ^ s) ^ (1/s) ≤ (∑ i, a i ^ s) ^ (1/s) + (∑ i, b i ^ s) ^ (1/s) := by
  have h := Commons.Analysis.Inequalities.finset_lp_minkowski (ι := ι) (κ := Bool) s hs
    (fun _ : Bool => (1:ℝ)) (fun _ : Bool => by norm_num)
    (fun (j : Bool) (i : ι) => bif j then b i else a i)
  have h1 : ∀ i : ι, (∑ j : Bool, (1:ℝ) * bif j then b i else a i) = a i + b i := by
    intro i
    rw [Fintype.sum_bool]
    simp only [one_mul, cond_false, cond_true]
    ring
  have h2 : ∀ i : ι, |a i + b i| = a i + b i := fun i => abs_of_nonneg (add_nonneg (ha i) (hb i))
  have h3 : ∀ i : ι, |a i| = a i := fun i => abs_of_nonneg (ha i)
  have h4 : ∀ i : ι, |b i| = b i := fun i => abs_of_nonneg (hb i)
  calc (∑ i, (a i + b i) ^ s) ^ (1/s)
      = (∑ i, |∑ j : Bool, (1:ℝ) * bif j then b i else a i| ^ s) ^ (1/s) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h1 i, h2 i]
    _ ≤ ∑ j : Bool, (1:ℝ) * (∑ i, |bif j then b i else a i| ^ s) ^ (1/s) := h
    _ = (∑ i, a i ^ s) ^ (1/s) + (∑ i, b i ^ s) ^ (1/s) := by
        have hA : (∑ i, |a i| ^ s) ^ (1/s) = (∑ i, a i ^ s) ^ (1/s) := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [h3 i]
        have hB : (∑ i, |b i| ^ s) ^ (1/s) = (∑ i, b i ^ s) ^ (1/s) := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => by rw [h4 i]
        rw [Fintype.sum_bool]
        simp only [one_mul, cond_false, cond_true]
        rw [hA, hB]
        ring

/-! ## Measurability of the grid averages and the variations -/

lemma aemeasurable_finset_norm_rpow {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {ι : Type*} [Fintype ι] (a b : ι → α → E) (s : ℝ) (hs : 0 ≤ s)
    (ha : ∀ i, AEMeasurable (a i) μ) (hb : ∀ i, AEMeasurable (b i) μ) :
    AEMeasurable (fun x : α => ∑ i, ‖a i x - b i x‖ ^ s) μ := by
  have h := Finset.aemeasurable_sum Finset.univ (f := fun i x => ‖a i x - b i x‖ ^ s)
    (fun i _ => (Real.continuous_rpow_const hs).measurable.comp_aemeasurable ((ha i).sub (hb i)).norm)
  rwa [Finset.sum_fn] at h

lemma aemeasurable_ofReal_rpow {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    (F : α → ℝ) (q : ℝ) (hq : 0 ≤ q) (hF0 : ∀ x, 0 ≤ F x) (hF : AEMeasurable F μ) :
    AEMeasurable (fun x : α => ENNReal.ofReal ((F x) ^ q)) μ := by
  refine ((ENNReal.continuous_rpow_const (y := q)).measurable.comp_aemeasurable hF.ennreal_ofReal).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact ENNReal.ofReal_rpow_of_nonneg (hF0 x) hq

lemma aemeasurable_gridAvg_x {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (k : ℤ) (θ : ℝ) (g : ℝ → E)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => gridAvg k θ g x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hc : (0:ℝ) < (2:ℝ)^(-k) := zpow_pos (by norm_num) (-k)
  have hQcont : Continuous (fun t : ℝ => ∫ y in (0:ℝ)..t, g y) := hg.continuous_primitive 0
  have ha : Measurable (fun x : ℝ => θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k)) := by
    have hfloor : Measurable (fun x : ℝ => (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ)) :=
      ((continuous_of_discreteTopology : Continuous (Int.cast : ℤ → ℝ)).measurable).comp
        (Int.measurable_floor.comp ((measurable_id.sub measurable_const).mul measurable_const))
    exact measurable_const.add (hfloor.mul measurable_const)
  have hb : Measurable (fun x : ℝ =>
      θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)) := ha.add measurable_const
  have h_eq : (fun x : ℝ => gridAvg k θ g x) = fun x : ℝ =>
      ((2:ℝ)^k) • ((∫ y in (0:ℝ)..(θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y)
          - (∫ y in (0:ℝ)..(θ + (⌊(x - θ) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k)), g y)) := by
    funext x
    rw [gridAvg, gridCell, gridLo, gridIdx]
    rw [intervalIntegral_Ioc_eq_primitive_sub hg (le_add_of_nonneg_right hc.le)]
  rw [h_eq]
  exact ((((hQcont.measurable.comp hb).sub (hQcont.measurable.comp ha)).const_smul
    ((2:ℝ)^k))).aemeasurable

lemma aemeasurable_gridAvg_uncurry (k : ℤ) (g : ℝ → ℂ)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun p : ℝ × ℝ => gridAvg k p.1 g p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have h := aemeasurable_grid_shift_average_uncurry k g hg
  have h2 : (fun p : ℝ × ℝ => gridAvg k p.1 g p.2)
      = fun p : ℝ × ℝ => ((2:ℝ)^k) • ∫ y in Set.Ioc
          (p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k))
          (p.1 + (⌊(p.2 - p.1) * (2:ℝ)^k⌋ : ℝ) * (2:ℝ)^(-k) + (2:ℝ)^(-k)), g y := by
    funext p
    rw [gridAvg, gridCell, gridLo, gridIdx]
  rw [h2]
  exact h

lemma aemeasurable_triOp_x (k : ℤ) (g : ℝ → ℂ)
    (hg : AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => triOp k g x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hker : Measurable (fun p : ℝ × ℝ =>
      (((2:ℝ)^k * max 0 (1 - (2:ℝ)^k * |p.1 - p.2|)) : ℂ)) := by
    fun_prop
  have hF : AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.2 * (((2:ℝ)^k * max 0 (1 - (2:ℝ)^k * |p.1 - p.2|)) : ℂ))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
    (hg.comp_snd).mul hker.aestronglyMeasurable
  have := hF.integral_prod_right'
  refine this.aemeasurable.congr (Filter.Eventually.of_forall fun x => ?_)
  rfl

lemma aemeasurable_GV_x {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : ℤ) (θ : ℝ) (g : ℝ → E) (s : ℝ) (hs : 0 < s)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => GV K θ g s x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have h1s : (0:ℝ) ≤ 1/s := by positivity
  have hterm : ∀ (J : ℕ) (k : Fin (J+1) → ℕ),
      AEMeasurable (fun x : ℝ => ENNReal.ofReal ((∑ j : Fin J,
        ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x‖ ^ s) ^ (1/s)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro J k
    refine aemeasurable_ofReal_rpow _ _ h1s (fun x => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) s) ?_
    have hA : ∀ j : Fin J, AEMeasurable
        (fun x : ℝ => gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_gridAvg_x (K + (k (Fin.succ j) : ℤ)) θ g hg
    have hB : ∀ j : Fin J, AEMeasurable
        (fun x : ℝ => gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_gridAvg_x (K + (k (Fin.castSucc j) : ℤ)) θ g hg
    exact aemeasurable_finset_norm_rpow
        (fun j => fun x : ℝ => gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x)
        (fun j => fun x : ℝ => gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x)
        s hs.le hA hB
  have hsup : AEMeasurable (fun x : ℝ => ⨆ (J : ℕ) (k : Fin (J+1) → ℕ) (_ : StrictMono k),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x‖ ^ s) ^ (1/s)))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    apply AEMeasurable.iSup
    intro J
    apply AEMeasurable.iSup
    intro k
    apply AEMeasurable.iSup
    intro hk
    exact hterm J k
  exact hsup

lemma aemeasurable_GV_uncurry (K : ℤ) (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun p : ℝ × ℝ => GV K p.1 g s p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  have h1s : (0:ℝ) ≤ 1/s := by positivity
  have hterm : ∀ (J : ℕ) (k : Fin (J+1) → ℕ),
      AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal ((∑ j : Fin J,
        ‖gridAvg (K + (k (Fin.succ j) : ℤ)) p.1 g p.2
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) p.1 g p.2‖ ^ s) ^ (1/s)))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    intro J k
    refine aemeasurable_ofReal_rpow _ _ h1s (fun p => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) s) ?_
    exact aemeasurable_finset_norm_rpow
        (fun j => fun p : ℝ × ℝ => gridAvg (K + (k (Fin.succ j) : ℤ)) p.1 g p.2)
        (fun j => fun p : ℝ × ℝ => gridAvg (K + (k (Fin.castSucc j) : ℤ)) p.1 g p.2)
        s hs.le (fun j => aemeasurable_gridAvg_uncurry _ g hg)
        (fun j => aemeasurable_gridAvg_uncurry _ g hg)
  have hsup : AEMeasurable (fun p : ℝ × ℝ => ⨆ (J : ℕ) (k : Fin (J+1) → ℕ) (_ : StrictMono k),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖gridAvg (K + (k (Fin.succ j) : ℤ)) p.1 g p.2
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) p.1 g p.2‖ ^ s) ^ (1/s)))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
    apply AEMeasurable.iSup
    intro J
    apply AEMeasurable.iSup
    intro k
    apply AEMeasurable.iSup
    intro hk
    exact hterm J k
  exact hsup

lemma GV_le_re_add_im (K : ℤ) (θ : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 1 ≤ s)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (x : ℝ) :
    GV K θ g s x ≤ GV K θ (fun y => (g y).re) s x + GV K θ (fun y => (g y).im) s x := by
  have hs0 : (0:ℝ) ≤ s := le_trans zero_le_one hs
  refine iSup_le fun J => iSup_le fun k => iSup_le fun hmono => ?_
  have hnorm : ∀ j : Fin J,
      ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x‖
        ≤ ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ (fun y => (g y).re) x
              - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ (fun y => (g y).re) x‖
          + ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ (fun y => (g y).im) x
              - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ (fun y => (g y).im) x‖ := by
    intro j
    have h1 : (gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x).re
        = gridAvg (K + (k (Fin.succ j) : ℤ)) θ (fun y => (g y).re) x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ (fun y => (g y).re) x := by
      rw [Complex.sub_re, gridAvg_re _ θ g hg x, gridAvg_re _ θ g hg x]
    have h2 : (gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x).im
        = gridAvg (K + (k (Fin.succ j) : ℤ)) θ (fun y => (g y).im) x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ (fun y => (g y).im) x := by
      rw [Complex.sub_im, gridAvg_im _ θ g hg x, gridAvg_im _ θ g hg x]
    calc ‖_‖ ≤ |(gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x).re|
        + |(gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = _ := by rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]
  have hmain : (∑ j : Fin J, ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
        - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x‖ ^ s) ^ (1/s)
      ≤ (∑ j : Fin J, ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ (fun y => (g y).re) x
            - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ (fun y => (g y).re) x‖ ^ s) ^ (1/s)
        + (∑ j : Fin J, ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ (fun y => (g y).im) x
            - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ (fun y => (g y).im) x‖ ^ s) ^ (1/s) :=
    le_trans (Real.rpow_le_rpow (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s)
      (Finset.sum_le_sum fun j _ => Real.rpow_le_rpow (norm_nonneg _) (hnorm j) hs0)
      (by positivity))
      (finset_rpow_add_le hs _ _ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
  refine le_trans (ENNReal.ofReal_le_ofReal hmain) ?_
  rw [ENNReal.ofReal_add
    (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) _)
    (Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg _) s) _)]
  exact add_le_add (le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hmono le_rfl)))
    (le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hmono le_rfl)))

lemma eLpNorm_sq_eq_lintegral_enorm_sq {α : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α}
    {E : Type*} [NormedAddCommGroup E] (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f (2:ℝ≥0∞) μ) ^ (2:ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂μ := by
  have hfe : AEStronglyMeasurable (fun x => ‖f x‖ₑ) μ :=
    continuous_enorm.comp_aestronglyMeasurable hf
  have heq : eLpNorm f (2:ℝ≥0∞) μ = eLpNorm (fun x => ‖f x‖ₑ) (2:ℝ≥0∞) μ := by
    refine le_antisymm (eLpNorm_mono_enorm hf fun x => ?_) (eLpNorm_mono_enorm hfe fun x => ?_)
    · rw [enorm_eq_self]
    · exact le_of_eq (enorm_eq_self _).symm
  rw [heq, eLpNorm_sq_ennreal _ hfe]

lemma eLpNorm_sq_eq_lintegral_ofReal_norm_sq {α : Type*} {m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} {E : Type*} [NormedAddCommGroup E] (f : α → E)
    (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f (2:ℝ≥0∞) μ) ^ (2:ℝ) = ∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ := by
  rw [eLpNorm_sq_eq_lintegral_enorm_sq f hf]
  refine lintegral_congr fun x => ?_
  rw [enorm_eq_ofReal_norm_aux, ← Real.rpow_two,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]

lemma aemeasurable_GV_rpow_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (K : ℤ) (θ : ℝ) (g : ℝ → E) (s : ℝ) (hs : 0 < s)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (GV K θ g s x) ^ (2:ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp_aemeasurable
    (aemeasurable_GV_x K θ g s hs hg)

lemma eLpNorm_GV_le_add (K : ℤ) (θ : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 1 ≤ s)
    (hgi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    eLpNorm (fun x : ℝ => GV K θ g s x) (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).re) s x
          + GV K θ (fun y => (g y).im) s x) (2:ℝ≥0∞)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  refine eLpNorm_mono_enorm (f := fun x : ℝ => GV K θ g s x)
    (g := fun x : ℝ => GV K θ (fun y => (g y).re) s x + GV K θ (fun y => (g y).im) s x)
    (aemeasurable_GV_x K θ g s (by linarith) hgi).aestronglyMeasurable ?_
  intro x
  rw [enorm_eq_self, enorm_eq_self]
  exact GV_le_re_add_im K θ g s hs hgi x

lemma eLpNorm_GV_add_le (K : ℤ) (θ : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hgi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).re) s x + GV K θ (fun y => (g y).im) s x)
        (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).re) s x) (2:ℝ≥0∞)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        + eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).im) s x) (2:ℝ≥0∞)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  refine eLpNorm_add_le (f := fun x : ℝ => GV K θ (fun y => (g y).re) s x)
    (g := fun x : ℝ => GV K θ (fun y => (g y).im) s x) (by norm_num)

lemma eLpNorm_GV_real_le (K : ℤ) (θ : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
    (hg2 : MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hgi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ‖g x‖ ≤ C) :
    eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).re) s x) (2:ℝ≥0∞)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      + eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).im) s x) (2:ℝ≥0∞)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ ENNReal.ofReal (2*10^6/(s-2))
        * eLpNorm g (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  obtain ⟨C, hC⟩ := hbd
  have hbdr : ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ‖(g x).re‖ ≤ C := ⟨C, by filter_upwards [hC] with x hx; exact le_trans (Complex.abs_re_le_norm _) hx⟩
  have hbdi : ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ‖(g x).im‖ ≤ C := ⟨C, by filter_upwards [hC] with x hx; exact le_trans (Complex.abs_im_le_norm _) hx⟩
  have hle_re : eLpNorm (fun x : ℝ => (g x).re) (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ eLpNorm g (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine eLpNorm_mono_enorm (f := fun x : ℝ => (g x).re) (g := g)
      (Complex.continuous_re.comp_aestronglyMeasurable hg2.aestronglyMeasurable) ?_
    intro x
    rw [Real.enorm_eq_ofReal_abs, enorm_eq_ofReal_norm_aux]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm (g x))
  have hle_im : eLpNorm (fun x : ℝ => (g x).im) (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ eLpNorm g (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    refine eLpNorm_mono_enorm (f := fun x : ℝ => (g x).im) (g := g)
      (Complex.continuous_im.comp_aestronglyMeasurable hg2.aestronglyMeasurable) ?_
    intro x
    rw [Real.enorm_eq_ofReal_abs, enorm_eq_ofReal_norm_aux]
    exact ENNReal.ofReal_le_ofReal (Complex.abs_im_le_norm (g x))
  have hRe : eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).re) s x) (2:ℝ≥0∞)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm g (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    (GV_eLpNorm_le K θ _ s hs hs3 hg2.re hgi.re hbdr).trans
      (mul_le_mul_of_nonneg_left hle_re zero_le)
  have hIm : eLpNorm (fun x : ℝ => GV K θ (fun y => (g y).im) s x) (2:ℝ≥0∞)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ ENNReal.ofReal (10^6/(s-2)) * eLpNorm g (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
    (GV_eLpNorm_le K θ _ s hs hs3 hg2.im hgi.im hbdi).trans
      (mul_le_mul_of_nonneg_left hle_im zero_le)
  refine (add_le_add hRe hIm).trans ?_
  have hc : (0:ℝ) ≤ 10^6/(s-2) := by positivity
  rw [← add_mul, ← two_mul, show (2:ℝ≥0∞) * ENNReal.ofReal (10^6/(s-2))
      = ENNReal.ofReal (2 * (10^6/(s-2))) from by
    rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]]
  congr 1
  rw [show (2:ℝ) * (10^6/(s-2)) = 2*10^6/(s-2) by ring]

lemma eLpNorm_GV_complex_le (K : ℤ) (θ : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
    (hg2 : MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hgi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ‖g x‖ ≤ C) :
    eLpNorm (fun x : ℝ => GV K θ g s x) (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
      ≤ ENNReal.ofReal (2*10^6/(s-2))
        * eLpNorm g (2:ℝ≥0∞) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  exact ((eLpNorm_GV_le_add K θ g s hs1 hgi).trans
    (eLpNorm_GV_add_le K θ g s hs0 hgi)).trans (eLpNorm_GV_real_le K θ g s hs hs3 hg2 hgi hbd)

/-- The `L²` bound for the complex-valued grid variation. -/
lemma GV_sq_lintegral_le (K : ℤ) (θ : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
    (hg2 : MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hgi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ‖g x‖ ≤ C) :
    ∫⁻ x, (GV K θ g s x) ^ (2:ℝ) ≤ ENNReal.ofReal ((2*10^6/(s-2))^2)
      * ∫⁻ x, ENNReal.ofReal (‖g x‖^2) := by
  rw [← eLpNorm_sq_ennreal _ (aemeasurable_GV_x K θ g s (by linarith) hgi).aestronglyMeasurable]
  calc (eLpNorm (fun x : ℝ => GV K θ g s x) (2:ℝ≥0∞)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ (2:ℝ)
      ≤ (ENNReal.ofReal (2*10^6/(s-2)) * eLpNorm g (2:ℝ≥0∞)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow (eLpNorm_GV_complex_le K θ g s hs hs3 hg2 hgi hbd) (by norm_num)
    _ = (ENNReal.ofReal (2*10^6/(s-2))) ^ (2:ℝ) * (eLpNorm g (2:ℝ≥0∞)
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) ^ (2:ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ = ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x, ENNReal.ofReal (‖g x‖^2) := by
        rw [eLpNorm_sq_eq_lintegral_ofReal_norm_sq g hg2.aestronglyMeasurable]
        congr 1
        rw [← Real.rpow_two, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]

/-- Square of a supremum of `ℝ≥0∞`-valued functions is bounded by the supremum of the squares. -/
lemma sq_iSup_le {ι : Type*} (f : ι → ℝ≥0∞) :
    (⨆ i, f i) ^ (2:ℝ) ≤ ⨆ i, (f i) ^ (2:ℝ) := by
  have hrw : ∀ x : ℝ≥0∞, x ^ (2:ℝ) = x * x := fun x => by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, pow_two]
  simp only [hrw]
  calc (⨆ i, f i) * (⨆ i, f i) = ⨆ i, f i * (⨆ j, f j) := ENNReal.iSup_mul _ _
    _ = ⨆ i, ⨆ j, f i * f j := by simp only [ENNReal.mul_iSup]
    _ ≤ ⨆ i, f i * f i := by
        refine iSup_le fun i => iSup_le fun j => ?_
        rcases le_total (f i) (f j) with h | h
        · exact le_iSup_of_le j (mul_le_mul h le_rfl zero_le zero_le)
        · exact le_iSup_of_le i (mul_le_mul le_rfl h zero_le zero_le)

/-- For fixed `x`, the grid variation is a.e. measurable as a function of the phase `θ`. -/
lemma aemeasurable_GV_theta (K : ℤ) (x : ℝ) (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun θ : ℝ => GV K θ g s x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have h1s : (0:ℝ) ≤ 1/s := by positivity
  have hterm : ∀ (J : ℕ) (k : Fin (J+1) → ℕ),
      AEMeasurable (fun θ : ℝ => ENNReal.ofReal ((∑ j : Fin J,
        ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x‖ ^ s) ^ (1/s)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro J k
    refine aemeasurable_ofReal_rpow _ _ h1s (fun θ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) s) ?_
    have hA : ∀ j : Fin J, AEMeasurable
        (fun θ : ℝ => gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_gridAvg_theta (K + (k (Fin.succ j) : ℤ)) g hg x
    have hB : ∀ j : Fin J, AEMeasurable
        (fun θ : ℝ => gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_gridAvg_theta (K + (k (Fin.castSucc j) : ℤ)) g hg x
    exact aemeasurable_finset_norm_rpow
        (fun j => fun θ : ℝ => gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x)
        (fun j => fun θ : ℝ => gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x)
        s hs.le hA hB
  have hsup : AEMeasurable (fun θ : ℝ => ⨆ (J : ℕ) (k : Fin (J+1) → ℕ) (_ : StrictMono k),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖gridAvg (K + (k (Fin.succ j) : ℤ)) θ g x
          - gridAvg (K + (k (Fin.castSucc j) : ℤ)) θ g x‖ ^ s) ^ (1/s)))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    apply AEMeasurable.iSup
    intro J
    apply AEMeasurable.iSup
    intro k
    apply AEMeasurable.iSup
    intro hk
    exact hterm J k
  exact hsup

lemma aemeasurable_TVK_x (K : ℤ) (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hg : AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => TVK K g s x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have h1s : (0:ℝ) ≤ 1/s := by positivity
  have hterm : ∀ (J : ℕ) (k : Fin (J+1) → ℤ),
      AEMeasurable (fun x : ℝ => ENNReal.ofReal ((∑ j : Fin J,
        ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro J k
    refine aemeasurable_ofReal_rpow _ _ h1s (fun x => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) s) ?_
    have hA : ∀ j : Fin J, AEMeasurable (fun x : ℝ => triOp (k (Fin.castSucc j)) g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_triOp_x (k (Fin.castSucc j)) g hg
    have hB : ∀ j : Fin J, AEMeasurable (fun x : ℝ => triOp (k (Fin.succ j)) g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_triOp_x (k (Fin.succ j)) g hg
    exact aemeasurable_finset_norm_rpow
        (fun j => fun x : ℝ => triOp (k (Fin.castSucc j)) g x)
        (fun j => fun x : ℝ => triOp (k (Fin.succ j)) g x)
        s hs.le hA hB
  have hsup : AEMeasurable (fun x : ℝ => ⨆ (J : ℕ) (k : Fin (J+1) → ℤ) (_ : StrictMono k)
      (_ : K ≤ k 0), ENNReal.ofReal ((∑ j : Fin J,
        ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s)))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    apply AEMeasurable.iSup
    intro J
    apply AEMeasurable.iSup
    intro k
    apply AEMeasurable.iSup
    intro hk
    apply AEMeasurable.iSup
    intro hKk
    exact hterm J k
  exact hsup

lemma aemeasurable_TVK_rpow_two (K : ℤ) (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hg : AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (TVK K g s x) ^ (2:ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp_aemeasurable
    (aemeasurable_TVK_x K g s hs hg)

lemma ofReal_zpow_mul_inv (K : ℤ) :
    ENNReal.ofReal ((2:ℝ)^K) * ENNReal.ofReal ((2:ℝ)^(-K)) = 1 := by
  rw [← ENNReal.ofReal_mul (zpow_nonneg (by norm_num : (0:ℝ) ≤ 2) K),
    ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), show K + (-K) = (0:ℤ) by ring, zpow_zero]
  norm_num

lemma rpow_two_eq_sq (x : ℝ≥0∞) : x ^ (2:ℝ) = x ^ 2 := by
  rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]

lemma ofReal_zpow_sq_mul (K : ℤ) :
    (ENNReal.ofReal ((2:ℝ)^K)) ^ (2:ℝ) * ENNReal.ofReal ((2:ℝ)^(-K))
      = ENNReal.ofReal ((2:ℝ)^K) := by
  have hc : (0:ℝ) < (2:ℝ)^K := zpow_pos (by norm_num) _
  rw [rpow_two_eq_sq, ← ENNReal.ofReal_pow (le_of_lt hc) 2,
    ← ENNReal.ofReal_mul (by positivity), zpow_neg]
  congr 1
  field_simp

/-- The `L²` bound for the restricted variation `TVK`. -/
lemma TVK_sq_lintegral_le (K : ℤ) (g : ℝ → ℂ) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
    (hg2 : MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hgi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ‖g x‖ ≤ C) :
    ∫⁻ x, (TVK K g s x) ^ (2:ℝ) ≤ ENNReal.ofReal ((2*10^6/(s-2))^2)
      * ∫⁻ x, ENNReal.ofReal (‖g x‖^2) := by
  have hs1 : 1 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hApos : (0:ℝ) < (2:ℝ)^(-K) := zpow_pos (by norm_num) _
  -- chainwise bound + Cauchy-Schwarz, pointwise in `x`
  have hCS : ∀ x : ℝ, (TVK K g s x) ^ (2:ℝ) ≤ ENNReal.ofReal ((2:ℝ)^K)
      * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (GV K θ g s x) ^ (2:ℝ) := by
    intro x
    have h1 : TVK K g s x ≤ ENNReal.ofReal ((2:ℝ)^K)
        * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), GV K θ g s x := by
      refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => iSup_le fun hKk => ?_
      exact chain_bound K s hs1 g hgi J k hk hKk x
    have h2 : (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), GV K θ g s x) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((2:ℝ)^(-K))
          * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (GV K θ g s x) ^ (2:ℝ) := by
      have h := Commons.Analysis.MeasureTheory.sq_lintegral_mul_le_mul_lintegral_mul_sq
        (μ := MeasureTheory.volume.restrict (Set.Ioc 0 ((2:ℝ)^(-K))))
        (f := fun _ : ℝ => (1:ℝ≥0∞)) (h := fun θ : ℝ => GV K θ g s x)
        aemeasurable_const
        ((aemeasurable_GV_theta K x g s hs0 hgi).mono_measure Measure.restrict_le_self)
      simp only [one_mul] at h
      rw [← ENNReal.rpow_natCast] at h
      have hone : ∫⁻ θ : ℝ, (1:ℝ≥0∞)
          ∂(MeasureTheory.volume.restrict (Set.Ioc 0 ((2:ℝ)^(-K)))) = ENNReal.ofReal ((2:ℝ)^(-K)) := by
        rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
          sub_zero]
      rw [hone] at h
      simpa using h
    calc (TVK K g s x) ^ (2:ℝ)
        ≤ (ENNReal.ofReal ((2:ℝ)^K) * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), GV K θ g s x) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = (ENNReal.ofReal ((2:ℝ)^K)) ^ (2:ℝ)
            * (∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), GV K θ g s x) ^ (2:ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ (ENNReal.ofReal ((2:ℝ)^K)) ^ (2:ℝ)
            * (ENNReal.ofReal ((2:ℝ)^(-K))
              * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (GV K θ g s x) ^ (2:ℝ)) :=
          mul_le_mul_of_nonneg_left h2 zero_le
      _ = ENNReal.ofReal ((2:ℝ)^K) * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (GV K θ g s x) ^ (2:ℝ) := by
          rw [← mul_assoc, ofReal_zpow_sq_mul]
  -- Tonelli
  have hswap : ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), ∫⁻ x : ℝ, (GV K θ g s x) ^ (2:ℝ)
      = ∫⁻ x : ℝ, ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (GV K θ g s x) ^ (2:ℝ) := by
    refine lintegral_lintegral_swap (μ := MeasureTheory.volume.restrict (Set.Ioc 0 ((2:ℝ)^(-K))))
      (ν := MeasureTheory.volume) ?_
    have hjoint := (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp_aemeasurable
      (aemeasurable_GV_uncurry K g s hs0 hgi)
    have hmeas : AEMeasurable
        (fun p : ℝ × ℝ => (GV K p.1 g s p.2) ^ (2:ℝ))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := hjoint
    refine hmeas.mono_measure ?_
    have hsplit : (MeasureTheory.volume.restrict (Set.Ioc 0 ((2:ℝ)^(-K)))).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        = (MeasureTheory.volume.restrict (Set.Ioc 0 ((2:ℝ)^(-K)))).prod
            ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict Set.univ) := by
      rw [Measure.restrict_univ]
    rw [hsplit, Measure.prod_restrict]
    exact Measure.restrict_le_self
  calc ∫⁻ x, (TVK K g s x) ^ (2:ℝ)
      ≤ ∫⁻ x, ENNReal.ofReal ((2:ℝ)^K)
          * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (GV K θ g s x) ^ (2:ℝ) := lintegral_mono hCS
    _ = ENNReal.ofReal ((2:ℝ)^K)
          * ∫⁻ x, ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), (GV K θ g s x) ^ (2:ℝ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((2:ℝ)^K)
          * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), ∫⁻ x : ℝ, (GV K θ g s x) ^ (2:ℝ) := by rw [hswap]
    _ ≤ ENNReal.ofReal ((2:ℝ)^K) * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)),
          ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x, ENNReal.ofReal (‖g x‖^2) :=
        mul_le_mul_of_nonneg_left
          (lintegral_mono fun θ => GV_sq_lintegral_le K θ g s hs hs3 hg2 hgi hbd) zero_le
    _ = ENNReal.ofReal ((2:ℝ)^K) * (ENNReal.ofReal ((2*10^6/(s-2))^2)
          * ∫⁻ θ in Set.Ioc 0 ((2:ℝ)^(-K)), ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((2:ℝ)^K) * (ENNReal.ofReal ((2*10^6/(s-2))^2)
          * (ENNReal.ofReal ((2:ℝ)^(-K)) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2))) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
          mul_comm (∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2)) (ENNReal.ofReal ((2:ℝ)^(-K)))]
    _ = ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2) := by
        calc ENNReal.ofReal ((2:ℝ)^K) * (ENNReal.ofReal ((2*10^6/(s-2))^2)
              * (ENNReal.ofReal ((2:ℝ)^(-K)) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2)))
            = (ENNReal.ofReal ((2:ℝ)^K) * ENNReal.ofReal ((2:ℝ)^(-K)))
              * (ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2)) := by
              ring
          _ = ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^2) := by
              rw [ofReal_zpow_mul_inv, one_mul]

lemma antitone_TVK (g : ℝ → ℂ) (s : ℝ) (x : ℝ) : Antitone (fun K : ℤ => TVK K g s x) := by
  intro K K' hKK'
  refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => iSup_le fun hK' => ?_
  exact le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk
    (le_iSup_of_le (le_trans hKK' hK') le_rfl)))

lemma iSup_int_eq_iSup_neg_nat {β : Type*} [CompleteLattice β] (f : ℤ → β) (hf : Antitone f) :
    (⨆ k : ℤ, f k) = ⨆ n : ℕ, f (-(n : ℤ)) := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    rcases lt_or_ge k 0 with hk | hk
    · refine le_iSup_of_le ((-k).toNat) ?_
      rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -k)]
      simp
    · refine le_iSup_of_le 0 ?_
      simpa using hf hk
  · exact iSup_le fun n => le_iSup (fun k : ℤ => f k) (-(n : ℤ))

/-- The `L²` bound for the full variation `TV` (for integrable and a.e. bounded `g`). -/
lemma TV_sq_lintegral_le (g : ℝ → ℂ) (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3)
    (hg2 : MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hgi : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (hbd : ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ‖g x‖ ≤ C) :
    ∫⁻ x, (TV g s x) ^ (2:ℝ) ≤ ENNReal.ofReal ((2*10^6/(s-2))^2)
      * ∫⁻ x, ENNReal.ofReal (‖g x‖^2) := by
  have hs0 : 0 < s := by linarith
  have hpt : ∀ x : ℝ, (TV g s x) ^ (2:ℝ) ≤ ⨆ K : ℤ, (TVK K g s x) ^ (2:ℝ) := by
    intro x
    rw [TV_eq_iSup_TVK g s x]
    exact sq_iSup_le (fun K : ℤ => TVK K g s x)
  have hreindex : ∀ x : ℝ, (⨆ K : ℤ, (TVK K g s x) ^ (2:ℝ))
      = ⨆ n : ℕ, (TVK (-(n : ℤ)) g s x) ^ (2:ℝ) := by
    intro x
    exact iSup_int_eq_iSup_neg_nat (fun K : ℤ => (TVK K g s x) ^ (2:ℝ))
      (fun K K' h => ENNReal.rpow_le_rpow (antitone_TVK g s x h) (by norm_num))
  have hmono : Monotone (fun n : ℕ => fun x : ℝ => (TVK (-(n : ℤ)) g s x) ^ (2:ℝ)) := by
    intro n m hnm x
    refine ENNReal.rpow_le_rpow (antitone_TVK g s x ?_) (by norm_num)
    simp only [neg_le_neg_iff]; exact_mod_cast hnm
  calc ∫⁻ x, (TV g s x) ^ (2:ℝ)
      ≤ ∫⁻ x, ⨆ K : ℤ, (TVK K g s x) ^ (2:ℝ) := lintegral_mono hpt
    _ = ∫⁻ x, ⨆ n : ℕ, (TVK (-(n : ℤ)) g s x) ^ (2:ℝ) := by
        refine lintegral_congr fun x => ?_
        rw [hreindex x]
    _ = ⨆ n : ℕ, ∫⁻ x, (TVK (-(n : ℤ)) g s x) ^ (2:ℝ) := by
        refine lintegral_iSup' (fun n => aemeasurable_TVK_rpow_two _ g s hs0
          hg2.aestronglyMeasurable) ?_
        filter_upwards with x n m hnm
        exact hmono hnm x
    _ ≤ ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x, ENNReal.ofReal (‖g x‖^2) :=
        iSup_le fun n => TVK_sq_lintegral_le _ g s hs hs3 hg2 hgi hbd

lemma aemeasurable_TV_x (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hg : AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => TV g s x) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  have h1s : (0:ℝ) ≤ 1/s := by positivity
  have hterm : ∀ (J : ℕ) (k : Fin (J+1) → ℤ),
      AEMeasurable (fun x : ℝ => ENNReal.ofReal ((∑ j : Fin J,
        ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro J k
    refine aemeasurable_ofReal_rpow _ _ h1s (fun x => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) s) ?_
    have hA : ∀ j : Fin J, AEMeasurable (fun x : ℝ => triOp (k (Fin.castSucc j)) g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_triOp_x (k (Fin.castSucc j)) g hg
    have hB : ∀ j : Fin J, AEMeasurable (fun x : ℝ => triOp (k (Fin.succ j)) g x)
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
      fun j => aemeasurable_triOp_x (k (Fin.succ j)) g hg
    exact aemeasurable_finset_norm_rpow
        (fun j => fun x : ℝ => triOp (k (Fin.castSucc j)) g x)
        (fun j => fun x : ℝ => triOp (k (Fin.succ j)) g x)
        s hs.le hA hB
  have hsup : AEMeasurable (fun x : ℝ => ⨆ (J : ℕ) (k : Fin (J+1) → ℤ) (_ : StrictMono k),
      ENNReal.ofReal ((∑ j : Fin J,
        ‖triOp (k (Fin.castSucc j)) g x - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s)))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    apply AEMeasurable.iSup
    intro J
    apply AEMeasurable.iSup
    intro k
    apply AEMeasurable.iSup
    intro hk
    exact hterm J k
  exact hsup

lemma aemeasurable_TV_rpow_two (g : ℝ → ℂ) (s : ℝ) (hs : 0 < s)
    (hg : AEStronglyMeasurable g (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    AEMeasurable (fun x : ℝ => (TV g s x) ^ (2:ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
  (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp_aemeasurable
    (aemeasurable_TV_x g s hs hg)

lemma triOp_indicator_eq (k : ℤ) (g : ℝ → ℂ) (x : ℝ) {n : ℝ}
    (hn : |x| + (2:ℝ)^(-k) ≤ n) :
    triOp k (Set.indicator (Set.Icc (-n) n) g) x = triOp k g x := by
  unfold triOp
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hkpos : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) _
  by_cases hy : y ∈ Set.Icc (-n) n
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy]
    have hxy : (2:ℝ)^(-k) < |x - y| := by
      rw [Set.mem_Icc, not_and_or] at hy
      rcases hy with hy | hy
      · push Not at hy
        have h2 : x - y > (2:ℝ)^(-k) := by
          have h1 : -|x| ≤ x := neg_abs_le x
          linarith
        exact lt_of_lt_of_le h2 (le_abs_self _)
      · push Not at hy
        have h2 : y - x > (2:ℝ)^(-k) := by
          have h1 : x ≤ |x| := le_abs_self x
          linarith
        have h3 : y - x ≤ |x - y| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        exact lt_of_lt_of_le h2 h3
    have hzero : max 0 (1 - (2:ℝ)^k * |x - y|) = 0 := by
      rw [max_eq_left]
      have h : (1:ℝ) < (2:ℝ)^k * |x - y| := by
        have h1 := mul_lt_mul_of_pos_left hxy hkpos
        rwa [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), show k + (-k) = (0:ℤ) by ring,
          zpow_zero] at h1
      linarith
    rw [hzero]
    simp

set_option maxHeartbeats 1600000 in
theorem fejer_handle_main :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3) (g : ℝ → ℂ),
      MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.MemLp g ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ x : ℝ, (⨆ (J : ℕ) (k : Fin (J + 1) → ℤ), ⨆ (_ : StrictMono k),
        ENNReal.ofReal ((∑ j : Fin J,
          ‖(∫ y : ℝ, g y * ((2:ℝ) ^ (k (Fin.castSucc j)) * max 0 (1 - (2:ℝ) ^ (k (Fin.castSucc j)) * |x - y|)))
           - (∫ y : ℝ, g y * ((2:ℝ) ^ (k (Fin.succ j)) * max 0 (1 - (2:ℝ) ^ (k (Fin.succ j)) * |x - y|)))‖ ^ s) ^ (1/s)))^ (2:ℝ)
        ≤ ENNReal.ofReal ((C / (s - 2)) ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^ 2) := by
  refine ⟨2*10^6, by norm_num, ?_⟩
  intro s hs hs3 g hg2 hgt
  have hs0 : 0 < s := by linarith
  set M : ℝ := MeasureTheory.lpNorm g ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) with hMdef
  have hM : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), ‖g x‖ ≤ M := by
    rw [hMdef]; exact MeasureTheory.ae_le_lpNorm_exponent_top hgt
  have hMnn : 0 ≤ M := by rw [hMdef]; exact MeasureTheory.lpNorm_nonneg
  set gN : ℕ → ℝ → ℂ := fun n => Set.indicator (Set.Icc (-(n:ℝ)) (n:ℝ)) g with hgNdef
  have hNle : ∀ n y, ‖gN n y‖ ≤ ‖g y‖ := by
    intro n y
    simp only [hgNdef]
    by_cases hy : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ)
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, norm_zero]
      exact norm_nonneg _
  have hN2 : ∀ n, MemLp (gN n) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro n
    refine MemLp.of_le hg2 (by simp only [hgNdef]; exact hg2.aestronglyMeasurable.indicator measurableSet_Icc) ?_
    · filter_upwards with y
      exact hNle n y
  have hNb : ∀ n, ∃ C : ℝ, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ‖gN n x‖ ≤ C := by
    intro n
    exact ⟨M, by filter_upwards [hM] with x hx; exact le_trans (hNle n x) hx⟩
  have hNi : ∀ n, MeasureTheory.Integrable (gN n) (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
    intro n
    have hfin : MeasureTheory.volume (Set.Icc (-(n:ℝ)) (n:ℝ)) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hdom : MeasureTheory.Integrable
        ((Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => M)) MeasureTheory.volume :=
      MeasureTheory.IntegrableOn.integrable_indicator
        (MeasureTheory.IntegrableOn.of_bound hfin aestronglyMeasurable_const M
          (ae_of_all _ fun _ => le_of_eq (Real.norm_of_nonneg hMnn))) measurableSet_Icc
    refine MeasureTheory.Integrable.mono' hdom
      (by simp only [hgNdef]; exact hg2.aestronglyMeasurable.indicator measurableSet_Icc) ?_
    filter_upwards [hM] with y hy
    simp only [hgNdef]
    by_cases h : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      exact hy
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      simp
  -- the per-truncation bound
  have hbnd : ∀ n, ∫⁻ x : ℝ, (TV (gN n) s x) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^ 2) := by
    intro n
    refine (TV_sq_lintegral_le (gN n) s hs hs3 (hN2 n) (hNi n) (hNb n)).trans ?_
    refine mul_le_mul_of_nonneg_left (MeasureTheory.lintegral_mono fun x => ?_) zero_le
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hNle n x) 2)
  -- the chain-term functions agree eventually
  have hev : ∀ (x : ℝ) (J : ℕ) (k : Fin (J+1) → ℤ), StrictMono k →
      ∀ᶠ n : ℕ in Filter.atTop,
        ENNReal.ofReal ((∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) (gN n) x
            - triOp (k (Fin.succ j)) (gN n) x‖ ^ s) ^ (1/s))
          = ENNReal.ofReal ((∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x
            - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s)) := by
    intro x J k hk
    refine Filter.eventually_atTop.2 ⟨⌈|x| + (2:ℝ)^(-(k 0))⌉₊, fun n hn => ?_⟩
    have hn' : |x| + (2:ℝ)^(-(k 0)) ≤ (n:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have hkj : ∀ j : Fin (J+1), |x| + (2:ℝ)^(-(k j)) ≤ (n:ℝ) := by
      intro j
      have h1 : k 0 ≤ k j := hk.monotone (Fin.zero_le j)
      have h2 : (2:ℝ)^(-(k j)) ≤ (2:ℝ)^(-(k 0)) := by
        apply zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2)
        omega
      linarith
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [triOp_indicator_eq (k (Fin.castSucc j)) g x (hkj (Fin.castSucc j)),
      triOp_indicator_eq (k (Fin.succ j)) g x (hkj (Fin.succ j))]
  -- liminf comparison
  have hle : ∀ x : ℝ, TV g s x ≤ Filter.liminf (fun n => TV (gN n) s x) Filter.atTop := by
    intro x
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    have h1 : ENNReal.ofReal ((∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x
          - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s))
        ≤ Filter.liminf (fun n => ENNReal.ofReal ((∑ j : Fin J,
            ‖triOp (k (Fin.castSucc j)) (gN n) x - triOp (k (Fin.succ j)) (gN n) x‖ ^ s) ^ (1/s)))
          Filter.atTop := by
      have hlim : Filter.liminf (fun n => ENNReal.ofReal ((∑ j : Fin J,
            ‖triOp (k (Fin.castSucc j)) (gN n) x - triOp (k (Fin.succ j)) (gN n) x‖ ^ s) ^ (1/s)))
          Filter.atTop
          = ENNReal.ofReal ((∑ j : Fin J, ‖triOp (k (Fin.castSucc j)) g x
            - triOp (k (Fin.succ j)) g x‖ ^ s) ^ (1/s)) := by
        rw [Filter.liminf_congr (hev x J k hk), Filter.liminf_const]
      rw [hlim]
    refine h1.trans ?_
    refine liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
    exact le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
  -- square the liminf
  have hsq : ∀ x : ℝ, (TV g s x) ^ (2:ℝ)
      ≤ Filter.liminf (fun n => (TV (gN n) s x) ^ (2:ℝ)) Filter.atTop := by
    intro x
    refine (ENNReal.rpow_le_rpow (hle x) (by norm_num)).trans ?_
    rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
    refine le_trans (sq_iSup_le (fun n => ⨅ i, ⨅ (_ : i ≥ n), TV (gN i) s x)) ?_
    refine iSup_le fun n => ?_
    refine le_trans ?_ (le_iSup (fun n => ⨅ i, ⨅ (_ : i ≥ n), (TV (gN i) s x) ^ (2:ℝ)) n)
    refine le_iInf fun i => le_iInf fun hi => ?_
    exact ENNReal.rpow_le_rpow (le_trans (iInf_le _ i) (iInf_le _ hi)) (by norm_num)
  change ∫⁻ x : ℝ, (TV g s x) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^ 2)
  calc ∫⁻ x : ℝ, (TV g s x) ^ (2:ℝ)
      ≤ ∫⁻ x : ℝ, Filter.liminf (fun n => (TV (gN n) s x) ^ (2:ℝ)) Filter.atTop :=
        MeasureTheory.lintegral_mono hsq
    _ ≤ Filter.liminf (fun n => ∫⁻ x : ℝ, (TV (gN n) s x) ^ (2:ℝ)) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le'
          (fun n => aemeasurable_TV_rpow_two (gN n) s hs0 (hN2 n).aestronglyMeasurable)
    _ ≤ ENNReal.ofReal ((2*10^6/(s-2))^2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖^ 2) := by
        refine (Filter.liminf_le_liminf (Filter.Eventually.of_forall hbnd)).trans ?_
        rw [Filter.liminf_const]

theorem fejer_handle_dyadic_variation_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 2 < s) (hs3 : s ≤ 3) (g : ℝ → ℂ),
      MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.MemLp g ⊤ (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      ∫⁻ x : ℝ, (⨆ (J : ℕ) (k : Fin (J + 1) → ℤ), ⨆ (_ : StrictMono k),
        ENNReal.ofReal ((∑ j : Fin J,
          ‖(∫ y : ℝ, g y * ((2:ℝ) ^ (k (Fin.castSucc j)) * max 0 (1 - (2:ℝ) ^ (k (Fin.castSucc j)) * |x - y|)))
           - (∫ y : ℝ, g y * ((2:ℝ) ^ (k (Fin.succ j)) * max 0 (1 - (2:ℝ) ^ (k (Fin.succ j)) * |x - y|)))‖ ^ s) ^ (1/s)))^ (2:ℝ)
        ≤ ENNReal.ofReal ((C / (s - 2)) ^ 2) * ∫⁻ x : ℝ, ENNReal.ofReal (‖g x‖ ^ 2) := fejer_handle_main

end

end Commons.Analysis.Fourier
