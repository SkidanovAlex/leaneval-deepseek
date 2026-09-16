import Mathlib
import Submission.SieveSplitKey
import Submission.Commons.MeasureTheory.Integral.marginal_set_error_le
import Submission.Commons.Analysis.Integral.volume_orthant_slab_card

open scoped BigOperators Topology
open Filter Finset MeasureTheory

set_option maxHeartbeats 2000000

/-!
# §5.3, second half: `hkey` from the marginal decomposition and the `J₂`-loss

`Submission/SieveSplitKey.lean` proves the identity

  `tpBetaSplit S c f i = J̃_i - 𝔏_i`

with `J̃_i = ∫ (tenP G c i univ)² · 1_{t ∈ marginalSet k i cc}` the radius-`cc` marginal
functional of the full tensor sum and `𝔏_i` the same functional of the `J₂`-part.

This module supplies

* `hkey_of_loss_marg` — the criterion's `hkey` from `Σ_i J̃_i > A + margin`,
  `Σ_i 𝔏_i < margin` and `α < A`;
* `margLoss_le` — the slab bound `𝔏_i ≤ Bm² · vol{cc - 6η(k-1) ≤ Σ t ≤ cc}` for the
  `J₂`-part, using the thin support of the components.

The remaining quantitative input is the certificate `MkEps 50 (1/25) > 4`, which provides
`Σ_i JFunc k i cc F > IFuncOrth k F + margin` for the variational test function `F`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **`hkey` from the marginal decomposition.**  If (i) the radius-`cc` marginal functionals
`J̃_i` of the tensor sum beat a threshold `A` by `margin`, (ii) the `J₂`-losses `𝔏_i` sum to less
than `margin`, and (iii) `α < A`, then the criterion's key inequality holds. -/
theorem hkey_of_loss_marg {k J : ℕ} (Sf : Fin k → Finset (Fin J)) (c : Fin J → ℝ)
    (f : Fin J → Fin k → ℝ → ℝ) (Jt Lt : Fin k → ℝ) {A margin : ℝ}
    (hsplit : ∀ i, tpBetaSplit (Sf i) c f i = Jt i - Lt i)
    (hJ : A + margin < ∑ i : Fin k, Jt i)
    (hL : (∑ i : Fin k, Lt i) < margin)
    (hα : tpAlpha c f < A) :
    tpAlpha c f < ∑ i : Fin k, tpBetaSplit (Sf i) c f i := by
  have hsum : (∑ i : Fin k, tpBetaSplit (Sf i) c f i) = (∑ i : Fin k, Jt i) - ∑ i : Fin k, Lt i := by
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib]
  rw [hsum]
  linarith

/-- **The `J₂`-loss slab bound.**  If every component family in `T` has marginal support radius
summing to at least `cc`, and the marginal tensor sum over `T` is bounded by `Bm` on the orthant,
then the radius-`cc` marginal functional of the `T`-part is at most `Bm²` times the volume of the
slab `{cc - 6η(k-1) ≤ Σ t ≤ cc}` of the marginal simplex. -/
theorem margLoss_le {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ)
    (hGc : ∀ j i, Continuous (G j i)) (hGcs : ∀ j i, HasCompactSupport (G j i))
    (c : Fin J → ℝ) (i : Fin k) (T : Finset (Fin J)) (β : Fin J → Fin k → ℝ)
    {η cc aa Bm : ℝ}
    (hη : 0 ≤ η) (hk : 1 ≤ k)
    (hthin : ∀ j l u, 0 ≤ u → G j l u ≠ 0 → β j l - 6 * η < u ∧ u < β j l)
    (hβlow : ∀ j ∈ T, aa + 6 * η * (k - 1) ≤ ∑ l : {l : Fin k // l ≠ i}, β j (l : Fin k))
    (hBm : ∀ t : ({l : Fin k // l ≠ i} → ℝ), (∀ l, 0 ≤ t l) → |tenP G c i T t| ≤ Bm)
    (hBm0 : 0 ≤ Bm)
    (hvol : (volume {t : ({l : Fin k // l ≠ i} → ℝ) |
        (∀ l, 0 ≤ t l) ∧ aa ≤ ∑ l, t l ∧ ∑ l, t l ≤ cc}).toReal
      = (cc ^ (k - 1) - aa ^ (k - 1)) / (Nat.factorial (k - 1) : ℝ)) :
    (∫ t : ({l : Fin k // l ≠ i} → ℝ), (tenP G c i T t) ^ 2 * margInd k i cc t)
      ≤ Bm ^ 2 * ((cc ^ (k - 1) - aa ^ (k - 1)) /
          (Nat.factorial (k - 1) : ℝ)) := by
  classical
  set S : Set ({l : Fin k // l ≠ i} → ℝ) :=
    {t | (∀ l, 0 ≤ t l) ∧ aa ≤ ∑ l, t l ∧ ∑ l, t l ≤ cc} with hS
  have hSmeas : MeasurableSet S := by
    have h1 : S = marginalSet k i cc ∩
        {t : ({l : Fin k // l ≠ i} → ℝ) | aa ≤ ∑ l, t l} := by
      rw [hS]
      ext t
      simp only [marginalSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto
    rw [h1]
    exact (measurableSet_marginalSet k i cc).inter
      (measurableSet_le measurable_const
        (Finset.measurable_sum _ (fun l _ => measurable_pi_apply l)))
  -- the pointwise bound by the slab indicator
  have hpt : ∀ t : ({l : Fin k // l ≠ i} → ℝ),
      (tenP G c i T t) ^ 2 * margInd k i cc t
        ≤ Bm ^ 2 * S.indicator (fun _ => (1 : ℝ)) t := by
    intro t
    by_cases ht : t ∈ marginalSet k i cc
    · have h1 : margInd k i cc t = 1 := Set.indicator_of_mem ht _
      rw [h1, mul_one]
      have horth : ∀ l, 0 ≤ t l := (Set.mem_ofPred_eq.mp ht).1
      have hsum : (∑ l, t l) ≤ cc := (Set.mem_ofPred_eq.mp ht).2
      by_cases hbig : aa ≤ ∑ l, t l
      · have htS : t ∈ S := ⟨horth, hbig, hsum⟩
        have h2 : S.indicator (fun _ => (1 : ℝ)) t = 1 := Set.indicator_of_mem htS _
        rw [h2, mul_one]
        have hP2 : (tenP G c i T t) ^ 2 ≤ Bm ^ 2 := by
          rw [← sq_abs (tenP G c i T t)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hBm t horth) 2
        linarith
      · have hz : tenP G c i T t = 0 := by
          rw [tenP]
          refine Finset.sum_eq_zero fun j hj => ?_
          by_cases hne : c j * (∫ x in Set.Ioi (0:ℝ), G j i x) *
              ∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l) = 0
          · rw [hne]
          · exfalso
            have hprod : (∏ l : {l : Fin k // l ≠ i}, G j (l : Fin k) (t l)) ≠ 0 := fun h0 =>
              hne (by rw [h0, mul_zero])
            have hlt : ∀ l : {l : Fin k // l ≠ i}, β j (l : Fin k) - 6 * η < t l := fun l =>
              (hthin j (l : Fin k) (t l) (horth l)
                (fun h0 => hprod (Finset.prod_eq_zero (Finset.mem_univ l) h0))).1
            have hsum' : (∑ l : {l : Fin k // l ≠ i}, (β j (l : Fin k) - 6 * η))
                ≤ ∑ l : {l : Fin k // l ≠ i}, t l :=
              Finset.sum_le_sum fun l _ => le_of_lt (hlt l)
            have hcard : (Fintype.card {l : Fin k // l ≠ i} : ℝ) = (k : ℝ) - 1 := by
              rw [card_subtype_ne, Nat.cast_sub hk]
              norm_num
            have hsplit : (∑ l : {l : Fin k // l ≠ i}, (β j (l : Fin k) - 6 * η))
                = (∑ l : {l : Fin k // l ≠ i}, β j (l : Fin k))
                  - (Fintype.card {l : Fin k // l ≠ i} : ℝ) * (6 * η) := by
              rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            have hlow := hβlow j hj
            have hnot : (∑ l : {l : Fin k // l ≠ i}, t l) < aa := lt_of_not_ge hbig
            rw [hsplit, hcard] at hsum'
            -- `Σ t ≥ Σ β - 6η(k-1) ≥ aa + 6η(k-1) - 6η(k-1) = aa`
            nlinarith [hsum', hlow, hnot, hη, Nat.cast_nonneg (α := ℝ) k]
        rw [hz]
        have hnn : (0:ℝ) ≤ Bm ^ 2 * S.indicator (fun _ => (1:ℝ)) t :=
          mul_nonneg (sq_nonneg Bm) (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
        simpa using hnn
    · have h0 : margInd k i cc t = 0 := Set.indicator_of_notMem ht _
      rw [h0, mul_zero]
      exact mul_nonneg (sq_nonneg Bm) (Set.indicator_nonneg (fun _ _ => zero_le_one) t)
  -- finiteness of the slab measure
  have hfin : (volume : Measure ({l : Fin k // l ≠ i} → ℝ)) S ≠ ⊤ := by
    have hsub : S ⊆ Set.univ.pi (fun _ : {l : Fin k // l ≠ i} => Set.Icc (0:ℝ) cc) := by
      intro t ht
      refine Set.mem_univ_pi.mpr fun l => ⟨ht.1 l, ?_⟩
      exact le_trans (Finset.single_le_sum (fun l' _ => ht.1 l') (Finset.mem_univ l)) ht.2.2
    have hle : (volume : Measure ({l : Fin k // l ≠ i} → ℝ)) S
        ≤ (ENNReal.ofReal cc) ^ (Fintype.card {l : Fin k // l ≠ i}) := by
      calc (volume : Measure ({l : Fin k // l ≠ i} → ℝ)) S
          ≤ volume (Set.univ.pi (fun _ : {l : Fin k // l ≠ i} => Set.Icc (0:ℝ) cc)) :=
            measure_mono hsub
        _ = ∏ _l : {l : Fin k // l ≠ i}, (volume : Measure ℝ) (Set.Icc (0:ℝ) cc) := by
            rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
        _ = (ENNReal.ofReal cc) ^ (Fintype.card {l : Fin k // l ≠ i}) := by
            rw [Finset.prod_const, Finset.card_univ, Real.volume_Icc, sub_zero]
    intro htop
    rw [htop] at hle
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top (top_le_iff.mp hle)
  have hIntg : Integrable (fun t : ({l : Fin k // l ≠ i} → ℝ) =>
      Bm ^ 2 * S.indicator (fun _ => (1 : ℝ)) t) := by
    have hI : Integrable (S.indicator (fun _ : ({l : Fin k // l ≠ i} → ℝ) => (1:ℝ))) := by
      rw [MeasureTheory.integrable_indicator_iff hSmeas]
      exact integrableOn_const (C := (1:ℝ)) hfin
    exact hI.const_mul _
  calc (∫ t : ({l : Fin k // l ≠ i} → ℝ), (tenP G c i T t) ^ 2 * margInd k i cc t)
      ≤ ∫ t : ({l : Fin k // l ≠ i} → ℝ),
          Bm ^ 2 * S.indicator (fun _ => (1 : ℝ)) t :=
        integral_mono (integrable_tenP_sq_margInd G hGc hGcs c i T cc) hIntg hpt
    _ = Bm ^ 2 * (volume S).toReal := by
        rw [integral_const_mul, integral_indicator_const (1:ℝ) hSmeas]
        simp only [smul_eq_mul, MeasureTheory.Measure.real, mul_one]
    _ = Bm ^ 2 * ((cc ^ (k - 1) - aa ^ (k - 1)) /
          (Nat.factorial (k - 1) : ℝ)) := by rw [hvol]

/-! ## The marginal functional of the tensor sum approximates `JFunc` -/

/-- **The radius-`cc` marginal functional of the tensor sum is close to `JFunc`.**  If the tensor
sum `Σ_j c_j ∏_l G_{j,l}` approximates `F` uniformly by `el`, both vanish beyond the coordinate
bound `Bg`, and `F` is supported in the orthant, then the marginal functional of the tensor sum
agrees with `JFunc k i₀ cc F` up to the error of the commons lemma `marginal_set_error_le`. -/
theorem margTensor_near_JFunc {k J : ℕ} (G : Fin J → Fin k → ℝ → ℝ)
    (hGc : ∀ j i, Continuous (G j i)) (hGcs : ∀ j i, HasCompactSupport (G j i))
    (hGi : ∀ j i, Integrable (G j i))
    (c : Fin J → ℝ) (i₀ : Fin k) (cc : ℝ)
    {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F) {CF R Bg el : ℝ}
    (hCF0 : 0 ≤ CF) (hCF : ∀ s, |F s| ≤ CF) (hBg0 : 0 ≤ Bg) (hRB : R ≤ Bg) (hel : 0 ≤ el)
    (hFcoord : ∀ s : Fin k → ℝ, (∃ i, R < s i) → F s = 0)
    (hGcoord : ∀ s : Fin k → ℝ, (∃ i, Bg < s i) → (∑ j : Fin J, c j * ∏ l, G j l (s l)) = 0)
    (happrox : ∀ s : Fin k → ℝ, |(∑ j : Fin J, c j * ∏ l, G j l (s l)) - F s| ≤ el)
    (hF0 : ∀ s : Fin k → ℝ, F s ≠ 0 → ∀ i, 0 ≤ s i) :
    |(∫ t : ({l : Fin k // l ≠ i₀} → ℝ), (tenP G c i₀ Finset.univ t) ^ 2 * margInd k i₀ cc t)
      - JFunc k i₀ cc F|
      ≤ el * Bg * (2 * CF * Bg + el * Bg) * Bg ^ (k - 1) := by
  classical
  set Gtf : (Fin k → ℝ) → ℝ := fun s => ∑ j : Fin J, c j * ∏ l, G j l (s l) with hGtf
  have hGtfc : Continuous Gtf := by
    rw [hGtf]
    refine continuous_finsetSum _ fun j _ => Continuous.const_mul ?_ _
    exact continuous_finsetProd _ fun l _ => (hGc j l).comp (continuous_apply l)
  have horth1 : ∀ t : ({l : Fin k // l ≠ i₀} → ℝ), t ∈ marginalSet k i₀ cc →
      orthInd t = 1 :=
    fun t ht => orthInd_eq_one_of_nonneg fun l => (Set.mem_ofPred_eq.mp ht).1 l
  have hIoiF : ∀ t : ({l : Fin k // l ≠ i₀} → ℝ),
      (∫ x : ℝ, F (extendAt i₀ x t)) = ∫ x in Set.Ioi (0:ℝ), F (extendAt i₀ x t) := by
    intro t
    have hzero : ∀ x ∈ Set.Iio (0:ℝ), F (extendAt i₀ x t) = 0 := by
      intro x hx
      by_contra hne
      have h1 := hF0 _ hne i₀
      have h2 : (extendAt i₀ x t) i₀ = x := by simp [extendAt]
      rw [h2] at h1
      exact absurd h1 (not_le.mpr hx)
    have h1 : (∫ x : ℝ, F (extendAt i₀ x t))
        = ∫ x, (Set.Ici (0:ℝ)).indicator (fun x => F (extendAt i₀ x t)) x := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ Set.Ici (0:ℝ)
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact hzero x (by rw [Set.mem_Iio]; exact lt_of_not_ge hx)
    rw [h1, MeasureTheory.integral_indicator measurableSet_Ici]
    exact (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm
  have hstep1 : (∫ t : ({l : Fin k // l ≠ i₀} → ℝ),
        (tenP G c i₀ Finset.univ t) ^ 2 * margInd k i₀ cc t)
      = ∫ t in marginalSet k i₀ cc,
          (∫ x in Set.Ioi (0:ℝ), Gtf (extendAt i₀ x t)) ^ 2 * orthInd t := by
    rw [← MeasureTheory.integral_indicator (measurableSet_marginalSet k i₀ cc)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    have hmarg : (∫ x in Set.Ioi (0:ℝ), Gtf (extendAt i₀ x t))
        = tenP G c i₀ Finset.univ t := by
      simp only [hGtf]
      exact integral_tensorSum_extendAt G hGi c i₀ t
    by_cases ht : t ∈ marginalSet k i₀ cc
    · have h1 : margInd k i₀ cc t = 1 := Set.indicator_of_mem ht _
      have h2 : orthInd t = 1 := horth1 t ht
      simp only [Set.indicator_of_mem ht, hmarg, h1, h2]
      try ring
    · have h0' : margInd k i₀ cc t = 0 := Set.indicator_of_notMem ht _
      simp only [Set.indicator_of_notMem ht, h0']
      try ring
  have hstep2 : JFunc k i₀ cc F
      = ∫ t in marginalSet k i₀ cc,
          (∫ x in Set.Ioi (0:ℝ), F (extendAt i₀ x t)) ^ 2 * orthInd t := by
    rw [JFunc, ← MeasureTheory.integral_indicator (measurableSet_marginalSet k i₀ cc)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    by_cases ht : t ∈ marginalSet k i₀ cc
    · have h1 : orthInd t = 1 := horth1 t ht
      simp only [hIoiF t, Set.indicator_of_mem ht, if_pos ht, h1]
      try ring
    · simp only [Set.indicator_of_notMem ht, if_neg ht]
      try ring
  rw [hstep1, hstep2]
  exact Commons.MeasureTheory.Integral.marginal_set_error_le hCF0 hCF hBg0 hRB hel hFcoord
    hGcoord happrox hGtfc hFc i₀ (measurableSet_marginalSet k i₀ cc)

/-- Summing a family of marginal functionals that beat a constant by `Mg`, against individual
approximation errors bounded by `eJ`. -/
theorem sum_margTensor_gt {k : ℕ} {Jt Ft : Fin k → ℝ} {I Mg eJ : ℝ}
    (hcert : I + Mg < ∑ i : Fin k, Ft i)
    (herr : ∀ i, |Jt i - Ft i| ≤ eJ)
    (hbud : (k : ℝ) * eJ ≤ Mg / 2) :
    I + Mg / 2 < ∑ i : Fin k, Jt i := by
  have h1 : (∑ i : Fin k, Ft i) - (∑ i : Fin k, Jt i) ≤ (k : ℝ) * eJ := by
    rw [← Finset.sum_sub_distrib]
    calc (∑ i : Fin k, (Ft i - Jt i)) ≤ ∑ i : Fin k, |Ft i - Jt i| :=
          Finset.sum_le_sum fun i _ => le_abs_self _
      _ = ∑ i : Fin k, |Jt i - Ft i| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_sub_comm]
      _ ≤ ∑ _i : Fin k, eJ := Finset.sum_le_sum fun i _ => herr i
      _ = (k : ℝ) * eJ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-- Summing a family of losses bounded by `eL`. -/
theorem sum_margLoss_lt {k : ℕ} {Lt : Fin k → ℝ} {margin eL : ℝ}
    (h : ∀ i, Lt i ≤ eL) (hbud : (k : ℝ) * eL < margin) :
    (∑ i : Fin k, Lt i) < margin := by
  calc (∑ i : Fin k, Lt i) ≤ ∑ _i : Fin k, eL := Finset.sum_le_sum fun i _ => h i
    _ = (k : ℝ) * eL := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < margin := hbud

/-- **The §5.3 `hkey` from the split tensor data and the variational certificate.**

This assembles the whole `J₁/J₂` split: the marginal identity `tpBetaSplit = J̃_i - 𝔏_i`, the
approximation `J̃_i ≈ JFunc k i cc F` (via `margTensor_near_JFunc`), the variational input
`Σ_i JFunc k i cc F > IFuncOrth k F + M` (the certificate `MkEps 50 (1/25) > 4`), the constraint
`tpAlpha c f < IFuncOrth k F + ef`, and the slab bound `𝔏_i ≤ Bm² · vol(slab)`. -/
theorem hkey_of_split_tensorData {J k : ℕ} {ψ : ℝ → ℝ} (hψ0 : ψ 0 = 1)
    (hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1)
    (G : Fin J → Fin k → ℝ → ℝ) (hGc : ∀ j i, Continuous (G j i))
    (hGcs : ∀ j i, HasCompactSupport (G j i)) (hGi : ∀ j i, Integrable (G j i))
    (hGv : ∀ j i, ∃ R : ℝ, ∀ x : ℝ, R ≤ x → G j i x = 0)
    (c : Fin J → ℝ) (Mr β : Fin J → Fin k → ℝ) (Sf : Fin k → Finset (Fin J))
    {F : (Fin k → ℝ) → ℝ}
    {η cc aa ef eJ Bm Mg : ℝ}
    (hη : 0 ≤ η) (hk : 1 ≤ k) (hk2 : 2 ≤ k)
    (hthin : ∀ j l u, 0 ≤ u → G j l u ≠ 0 → β j l - 6 * η < u ∧ u < β j l)
    (hβM : ∀ j l, β j l ≤ Mr j l)
    (hSf : ∀ i (j : Fin J), j ∈ Sf i →
      ∑ l : {l : Fin k // l ≠ i}, Mr j (l : Fin k) < cc)
    (hβlow : ∀ i (j : Fin J), j ∉ Sf i →
      aa + 6 * η * (k - 1) ≤ ∑ l : {l : Fin k // l ≠ i}, β j (l : Fin k))
    (hBm : ∀ i, ∀ t : ({l : Fin k // l ≠ i} → ℝ), (∀ l, 0 ≤ t l) →
      |tenP G c i (Finset.univ \ Sf i) t| ≤ Bm)
    (haa : 0 ≤ aa) (hac : aa ≤ cc)
    (hJapprox : ∀ i, |(∫ t : ({l : Fin k // l ≠ i} → ℝ),
        (tenP G c i Finset.univ t) ^ 2 * margInd k i cc t) - JFunc k i cc F| ≤ eJ)
    (hcert : IFuncOrth k F + ef + Mg < ∑ i : Fin k, JFunc k i cc F)
    (hbudJ : (k : ℝ) * eJ ≤ Mg / 2)
    (hBm0 : 0 ≤ Bm)
    (hbudL : (k : ℝ) * (Bm ^ 2 * ((cc ^ (k - 1) - aa ^ (k - 1)) /
        (Nat.factorial (k - 1) : ℝ))) < Mg / 2)
    (hα : tpAlpha c (fun j i => anti ψ (G j) i) < IFuncOrth k F + ef) :
    tpAlpha c (fun j i => anti ψ (G j) i)
      < ∑ i : Fin k, tpBetaSplit (Sf i) c (fun j i => anti ψ (G j) i) i := by
  classical
  have hvol : ∀ i, (volume {t : ({l : Fin k // l ≠ i} → ℝ) |
      (∀ l, 0 ≤ t l) ∧ aa ≤ ∑ l, t l ∧ ∑ l, t l ≤ cc}).toReal
      = (cc ^ (k - 1) - aa ^ (k - 1)) / (Nat.factorial (k - 1) : ℝ) := by
    intro i
    have h := Commons.Analysis.Integral.volume_orthant_slab_card
      (ι := {l : Fin k // l ≠ i}) aa cc haa hac
      (by rw [card_subtype_ne]; omega)
    rw [card_subtype_ne] at h
    exact h
  set Jt : Fin k → ℝ := fun i => ∫ t : ({l : Fin k // l ≠ i} → ℝ),
    (tenP G c i Finset.univ t) ^ 2 * margInd k i cc t with hJt
  set Lt : Fin k → ℝ := fun i => ∫ t : ({l : Fin k // l ≠ i} → ℝ),
    (tenP G c i (Finset.univ \ Sf i) t) ^ 2 * margInd k i cc t with hLt
  have hsplit : ∀ i, tpBetaSplit (Sf i) c (fun j i => anti ψ (G j) i) i = Jt i - Lt i := by
    intro i
    simpa only [hJt, hLt] using
      tpBetaSplit_eq_marginal hψ0 hψ1 G hGc hGcs hGi hGv c (Sf i) i Mr β
        (hSf i) hβM hthin
  have hJ : (IFuncOrth k F + ef) + Mg / 2 < ∑ i : Fin k, Jt i :=
    sum_margTensor_gt (k := k) (Jt := Jt) (Ft := fun i => JFunc k i cc F)
      (I := IFuncOrth k F + ef) (Mg := Mg) (eJ := eJ) hcert hJapprox hbudJ
  have hLt_le : ∀ i, Lt i ≤ Bm ^ 2 * ((cc ^ (k - 1) - aa ^ (k - 1)) /
      (Nat.factorial (k - 1) : ℝ)) := by
    intro i
    have h := margLoss_le G hGc hGcs c i (Finset.univ \ Sf i) β hη hk hthin
      (fun j hj => hβlow i j (Finset.mem_sdiff.mp hj).2) (hBm i) hBm0 (hvol i)
    simpa only [hLt] using h
  have hL : (∑ i : Fin k, Lt i) < Mg / 2 := sum_margLoss_lt hLt_le hbudL
  exact hkey_of_loss_marg Sf c (fun j i => anti ψ (G j) i) Jt Lt hsplit hJ hL hα

end Commons.NumberTheory.MaynardSieve
