import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.volume_rNorm_ball
import Submission.Work.HP.rNorm_smul
import Submission.Work.HP.evaldefs
import Submission.Work.HP.veronese_first
import Submission.Work.HP.vol_shell_le
import Submission.Work.HP.vol_slab_measurable
import Submission.Work.HP.vol_gradVec_lipschitz

namespace Work.HP

open MeasureTheory MvPolynomial
open scoped ENNReal

/-- A Lipschitz constant for `gradVec` on the ball of radius `2` (see
`Work.HP.vol_gradVec_lipschitz`). -/
def volBL (d n : ℕ) : ℝ := (n + 1 : ℝ) * (NN d n : ℝ) * (2 : ℝ) ^ (3 * d)

/-! ### Local wrapper for the Lipschitz bound, stated with `volBL` -/

/-- `volBL` is the explicit constant of `Work.HP.vol_gradVec_lipschitz`. -/
lemma vol_gradVec_lipschitz_BL (d n : ℕ) (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ)
    (hx : rNorm x ≤ 2) (hy : rNorm y ≤ 2) :
    rNorm (gradVec d n a y - gradVec d n a x) ≤ volBL d n * rNorm a * rNorm (y - x) := by
  rw [volBL]
  exact vol_gradVec_lipschitz d n a x y hx hy

/-! ### The geometry: a ball inside the slab of a form in `Bset` -/

set_option maxHeartbeats 800000 in
lemma ball_subset_slab (d n : ℕ) (hn : 3 ≤ n) {C : ℝ} (hC : 0 < C)
    (htay : ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
      |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
        ≤ C * rNorm a * (rNorm (y - x)) ^ 2)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    {a : Mon d n → ℝ} (ha : a ∈ Bset d n lam) :
    ∃ x : Fin (n + 1) → ℝ, rNorm x = 1 ∧
      ∀ z : Fin (n + 1) → ℝ, rNorm (z - (1 + lam / 4) • x) ≤ lam / 4 →
        1 ≤ rNorm z ∧ rNorm z ≤ 1 + lam / 2 ∧
        |formEvalR d n a z| ≤ (1 + C / 4) * lam ^ 2 ∧
        ∀ j : Fin (n + 1), |gradVec d n a z j| ≤ (2 + volBL d n / 2) * lam := by
  obtain ⟨ha1, -, x, hx1, hx0, -, hle⟩ := ha
  have hlam_nn : 0 ≤ lam := le_of_lt hlam0
  refine ⟨x, hx1, ?_⟩
  intro z hz
  have hx2 : rNorm x ≤ 2 := by rw [hx1]; norm_num
  have hsub : (1 + lam / 4) • x - x = (lam / 4) • x := by
    rw [add_smul, one_smul]; abel
  have hcx : rNorm ((1 + lam / 4) • x - x) = lam / 4 := by
    rw [hsub, rNorm_smul_of_pos _ _ (by linarith), hx1, mul_one]
  have hzx : rNorm (z - x) ≤ lam / 2 := by
    have h1 : z - x = (z - (1 + lam / 4) • x) + ((1 + lam / 4) • x - x) := by abel
    calc rNorm (z - x) = rNorm ((z - (1 + lam / 4) • x) + ((1 + lam / 4) • x - x)) := by rw [h1]
      _ ≤ rNorm (z - (1 + lam / 4) • x) + rNorm ((1 + lam / 4) • x - x) := rNorm_add_le _ _
      _ ≤ lam / 4 + lam / 4 := add_le_add hz (le_of_eq hcx)
      _ = lam / 2 := by ring
  have hnorm_mid : rNorm ((1 + lam / 4) • x) = 1 + lam / 4 := by
    rw [rNorm_smul_of_pos _ _ (by linarith), hx1, mul_one]
  have hrz_ge : 1 ≤ rNorm z := by
    have h1 : rNorm ((1 + lam / 4) • x) ≤ rNorm z + rNorm (z - (1 + lam / 4) • x) :=
      calc rNorm ((1 + lam / 4) • x) = rNorm (z + ((1 + lam / 4) • x - z)) := by
            congr 1; abel
        _ ≤ rNorm z + rNorm ((1 + lam / 4) • x - z) := rNorm_add_le _ _
        _ = rNorm z + rNorm (z - (1 + lam / 4) • x) := by rw [rNorm_sub_comm]
    rw [hnorm_mid] at h1
    linarith [hz]
  have hrz_le : rNorm z ≤ 1 + lam / 2 := by
    have h1 := rNorm_le_add_sub z ((1 + lam / 4) • x)
    rw [hnorm_mid] at h1
    linarith [hz]
  have hz2 : rNorm z ≤ 2 := by linarith [hrz_le, hlam1]
  refine ⟨hrz_ge, hrz_le, ?_, ?_⟩
  · have hdot : |dotR (gradVec d n a x) (z - x)| ≤ (2 * lam) * rNorm (z - x) := by
      have h1 : rNorm (gradVec d n a x) ≤ 2 * lam := by
        calc rNorm (gradVec d n a x) ≤ 2 * lam * rNorm a := hle
          _ ≤ 2 * lam * 1 := mul_le_mul_of_nonneg_left ha1 (by linarith)
          _ = 2 * lam := by ring
      calc |dotR (gradVec d n a x) (z - x)| ≤ rNorm (gradVec d n a x) * rNorm (z - x) :=
            abs_dotR_le _ _
        _ ≤ (2 * lam) * rNorm (z - x) :=
            mul_le_mul_of_nonneg_right h1 (rNorm_nonneg _)
    have ht := htay a x z hx2 hz2
    have hdec : formEvalR d n a z =
        (formEvalR d n a z - formEvalR d n a x - dotR (gradVec d n a x) (z - x))
          + dotR (gradVec d n a x) (z - x) + formEvalR d n a x := by ring
    have hCnn : 0 ≤ C := le_of_lt hC
    have hrem : |formEvalR d n a z - formEvalR d n a x - dotR (gradVec d n a x) (z - x)|
        ≤ C * (lam / 2) ^ 2 := by
      refine ht.trans ?_
      have hs : (rNorm (z - x)) ^ 2 ≤ (lam / 2) ^ 2 :=
        pow_le_pow_left₀ (rNorm_nonneg _) hzx 2
      calc C * rNorm a * (rNorm (z - x)) ^ 2 ≤ C * 1 * (lam / 2) ^ 2 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left ha1 hCnn
            · exact hs
            · positivity
            · positivity
          _ = C * (lam / 2) ^ 2 := by ring
    have htri : |(formEvalR d n a z - formEvalR d n a x - dotR (gradVec d n a x) (z - x))
          + dotR (gradVec d n a x) (z - x) + formEvalR d n a x|
        ≤ |formEvalR d n a z - formEvalR d n a x - dotR (gradVec d n a x) (z - x)|
          + |dotR (gradVec d n a x) (z - x)| + |formEvalR d n a x| := by
      have h2 := abs_add_le (formEvalR d n a z - formEvalR d n a x
            - dotR (gradVec d n a x) (z - x) + dotR (gradVec d n a x) (z - x))
            (formEvalR d n a x)
      have h3 := abs_add_le (formEvalR d n a z - formEvalR d n a x
            - dotR (gradVec d n a x) (z - x)) (dotR (gradVec d n a x) (z - x))
      linarith
    have hfx0 : |formEvalR d n a x| = 0 := by rw [hx0]; simp
    calc |formEvalR d n a z|
        = |(formEvalR d n a z - formEvalR d n a x - dotR (gradVec d n a x) (z - x))
            + dotR (gradVec d n a x) (z - x) + formEvalR d n a x| :=
          congrArg (fun t => |t|) hdec
      _ ≤ |formEvalR d n a z - formEvalR d n a x - dotR (gradVec d n a x) (z - x)|
            + |dotR (gradVec d n a x) (z - x)| + |formEvalR d n a x| := htri
      _ ≤ C * (lam / 2) ^ 2 + (2 * lam) * (lam / 2) + 0 := by
            have hdot2 : |dotR (gradVec d n a x) (z - x)| ≤ (2 * lam) * (lam / 2) :=
              hdot.trans (mul_le_mul_of_nonneg_left hzx (by linarith))
            rw [hfx0]
            linarith [hrem, hdot2]
      _ = (1 + C / 4) * lam ^ 2 := by ring
  · have hgrad : rNorm (gradVec d n a z) ≤ (2 + volBL d n / 2) * lam := by
      have hsplit : gradVec d n a z = gradVec d n a x + (gradVec d n a z - gradVec d n a x) := by abel
      have h1 : rNorm (gradVec d n a z) ≤ rNorm (gradVec d n a x)
          + rNorm (gradVec d n a z - gradVec d n a x) :=
        calc rNorm (gradVec d n a z)
            = rNorm (gradVec d n a x + (gradVec d n a z - gradVec d n a x)) :=
              congrArg rNorm hsplit
          _ ≤ rNorm (gradVec d n a x) + rNorm (gradVec d n a z - gradVec d n a x) := rNorm_add_le _ _
      have h2 := vol_gradVec_lipschitz_BL d n a x z hx2 hz2
      have h3 : rNorm (gradVec d n a x) ≤ 2 * lam := by
        calc rNorm (gradVec d n a x) ≤ 2 * lam * rNorm a := hle
          _ ≤ 2 * lam * 1 := mul_le_mul_of_nonneg_left ha1 (by linarith)
          _ = 2 * lam := by ring
      have h4 : volBL d n * rNorm a * rNorm (z - x) ≤ volBL d n * (lam / 2) := by
        have hBL : 0 ≤ volBL d n := by
          rw [volBL]; positivity
        calc volBL d n * rNorm a * rNorm (z - x) ≤ volBL d n * 1 * rNorm (z - x) := by
              apply mul_le_mul_of_nonneg_right _ (rNorm_nonneg _)
              exact mul_le_mul_of_nonneg_left ha1 hBL
          _ ≤ volBL d n * 1 * (lam / 2) := by
              apply mul_le_mul_of_nonneg_left hzx
              exact mul_nonneg hBL zero_le_one
          _ = volBL d n * (lam / 2) := by ring
      linarith
    intro j
    exact (abs_apply_le_rNorm (gradVec d n a z) j).trans hgrad


/-! ### Bounding the shell -/

/-- The slab over `X × ℝ^{n+1}` whose `a`-slices are the sets
`{a : rNorm a ≤ 1, |f_a(x)| ≤ eps, |∂_j f_a(x)| ≤ del}`. -/
def volSlab (d n : ℕ) (t eps del : ℝ) : Set ((Mon d n → ℝ) × (Fin (n + 1) → ℝ)) :=
  {p | rNorm p.1 ≤ 1 ∧ 1 ≤ rNorm p.2 ∧ rNorm p.2 ≤ 1 + t ∧
    |formEvalR d n p.1 p.2| ≤ eps ∧ ∀ j : Fin (n + 1), |gradVec d n p.1 p.2 j| ≤ del}

/-- The shell `{1 ≤ rNorm z ≤ 1 + t}` of `ℝ^{n+1}`. -/
def volShell (n : ℕ) (t : ℝ) : Set (Fin (n + 1) → ℝ) := {z | 1 ≤ rNorm z ∧ rNorm z ≤ 1 + t}

lemma volBL_nonneg (d n : ℕ) : 0 ≤ volBL d n := by rw [volBL]; positivity

lemma vol_continuous_rNorm (n : ℕ) : Continuous (fun v : Fin (n + 1) → ℝ => rNorm v) := by
  rw [show (fun v : Fin (n + 1) → ℝ => rNorm v) = (fun v => Real.sqrt (∑ i, v i ^ 2)) from rfl]
  fun_prop

lemma vol_norm_le_rNorm (n : ℕ) (v : Fin (n + 1) → ℝ) : ‖v‖ ≤ rNorm v := by
  refine (pi_norm_le_iff_of_nonneg (rNorm_nonneg v)).mpr fun i => ?_
  simpa [Real.norm_eq_abs] using abs_apply_le_rNorm v i

lemma volShell_measurable (n : ℕ) (t : ℝ) : MeasurableSet (volShell n t) := by
  rw [volShell]
  exact (isClosed_le continuous_const (vol_continuous_rNorm n)).measurableSet.inter
    (isClosed_le (vol_continuous_rNorm n) continuous_const).measurableSet

set_option maxHeartbeats 1600000 in
theorem vol_Bset (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n)
    (hslab : ∃ K, 0 < K ∧ ∀ (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (A ε δ : ℝ),
      1 / (n + 1 : ℝ) ≤ |x i| → rNorm x ≤ 2 → 0 ≤ A → 0 ≤ ε → 0 ≤ δ →
      volume {a : Mon d n → ℝ | rNorm a ≤ A ∧ |formEvalR d n a x| ≤ ε ∧
          (∀ j : Fin (n + 1), |gradVec d n a x j| ≤ δ)}
        ≤ ENNReal.ofReal (K * ε * δ ^ n * A ^ (NN d n - n - 1)))
    (htay : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ C * rNorm a * (rNorm (y - x)) ^ 2)
    (hball : ∀ (r : ℝ) (x : Mon d n → ℝ), 0 ≤ r →
        volume {w : Mon d n → ℝ | rNorm (w - x) ≤ r}
          = ENNReal.ofReal (r ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1}) :
    ∃ K : ℝ, 0 < K ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      volume (Bset d n lam) ≤ ENNReal.ofReal (K * lam ^ 2) := by
  obtain ⟨Ks, hKs, hslab'⟩ := hslab
  obtain ⟨C, hC, htay'⟩ := htay
  refine ⟨max 1 (Ks * (4:ℝ)^(n+1) * (2:ℝ)^n * (1 + C/4) * (2 + volBL d n / 2)^n),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro lam hlam0 hlam1
  have hlam_nn : 0 ≤ lam := le_of_lt hlam0
  set eps : ℝ := (1 + C / 4) * lam ^ 2 with heps
  set del : ℝ := (2 + volBL d n / 2) * lam with hdel
  set V : ℝ≥0∞ := volume {z : Fin (n + 1) → ℝ | rNorm z ≤ 1} with hV
  set A : ℝ := (lam / 4) ^ (n + 1) with hA
  have hApos : 0 < A := by rw [hA]; positivity
  have heps_pos : 0 < eps := by rw [heps]; positivity
  have hdel_pos : 0 < del := by
    rw [hdel]
    exact mul_pos (by linarith [volBL_nonneg d n]) hlam0
  have hVpos : 0 < V := by
    rw [hV]
    have hopen : IsOpen {z : Fin (n + 1) → ℝ | rNorm z < 1} :=
      isOpen_lt (vol_continuous_rNorm n) continuous_const
    have hne : ({z : Fin (n + 1) → ℝ | rNorm z < 1}).Nonempty := ⟨0, by simp [rNorm]⟩
    refine lt_of_lt_of_le (IsOpen.measure_pos volume hopen hne) (measure_mono ?_)
    intro z hz
    exact le_of_lt (by simpa using hz)
  have hVtop : V ≠ ⊤ := by
    rw [hV]
    have hsub : {z : Fin (n + 1) → ℝ | rNorm z ≤ 1} ⊆
        Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      exact le_trans (vol_norm_le_rNorm n z) hz
    refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
    rw [Real.volume_pi_closedBall (0 : Fin (n + 1) → ℝ) (by norm_num : (0:ℝ) ≤ 1)]
    exact ENNReal.ofReal_lt_top
  -- the product slab
  have hP : MeasurableSet (volSlab d n (lam / 2) eps del) :=
    vol_slab_measurable d n (lam / 2) eps del
  -- the set `M` of good coefficient vectors
  set M : Set (Mon d n → ℝ) :=
    {a | ENNReal.ofReal A * V ≤ volume (Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del)} with hM
  have hMmeas : MeasurableSet M :=
    measurableSet_le measurable_const (measurable_measure_prodMk_left hP)
  have hsubset : Bset d n lam ⊆ M := by
    intro a ha
    show ENNReal.ofReal A * V ≤ volume (Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del)
    obtain ⟨x, hx1, hxconcl⟩ := ball_subset_slab d n hn hC htay' hlam0 hlam1 ha
    have hb_sub : {z : Fin (n + 1) → ℝ | rNorm (z - (1 + lam / 4) • x) ≤ lam / 4} ⊆
        Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del := by
      intro z hz
      obtain ⟨hz1, hz2, hz3, hz4⟩ := hxconcl z hz
      exact ⟨ha.1, hz1, hz2, hz3, hz4⟩
    have hbvol : volume {z : Fin (n + 1) → ℝ | rNorm (z - (1 + lam / 4) • x) ≤ lam / 4}
        = ENNReal.ofReal A * V := by
      rw [volume_rNorm_ball ((1 + lam / 4) • x) (lam / 4) (by positivity), Fintype.card_fin,
        hA, hV]
    calc ENNReal.ofReal A * V
        = volume {z : Fin (n + 1) → ℝ | rNorm (z - (1 + lam / 4) • x) ≤ lam / 4} := hbvol.symm
      _ ≤ volume (Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del) := measure_mono hb_sub
  -- pointwise comparison on `M`
  have hpt : ∀ a : Mon d n → ℝ,
      (ENNReal.ofReal A * V) * M.indicator (1 : (Mon d n → ℝ) → ℝ≥0∞) a
        ≤ volume (Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del) := by
    intro a
    by_cases haM : a ∈ M
    · rw [Set.indicator_of_mem haM]
      simp only [Pi.one_apply, mul_one]
      exact haM
    · rw [Set.indicator_of_notMem haM]
      rw [mul_zero]
      exact bot_le
  have hchain1 : volume M * (ENNReal.ofReal A * V)
      ≤ ∫⁻ a, volume (Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del) := by
    rw [← lintegral_indicator_one hMmeas]
    calc (∫⁻ a, M.indicator (1 : (Mon d n → ℝ) → ℝ≥0∞) a) * (ENNReal.ofReal A * V)
        = (ENNReal.ofReal A * V) * (∫⁻ a, M.indicator (1 : (Mon d n → ℝ) → ℝ≥0∞) a) :=
          mul_comm _ _
      _ = ∫⁻ a, (ENNReal.ofReal A * V) * M.indicator (1 : (Mon d n → ℝ) → ℝ≥0∞) a :=
          (lintegral_const_mul _ (measurable_const.indicator hMmeas)).symm
      _ ≤ ∫⁻ a, volume (Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del) := lintegral_mono hpt
  have hchain2 : ∫⁻ a, volume (Prod.mk a ⁻¹' volSlab d n (lam / 2) eps del)
      = ∫⁻ z, volume ((fun a => (a, z)) ⁻¹' volSlab d n (lam / 2) eps del) := by
    rw [← Measure.prod_apply (μ := (volume : Measure (Mon d n → ℝ)))
        (ν := (volume : Measure (Fin (n + 1) → ℝ))) hP,
      Measure.prod_apply_symm (μ := (volume : Measure (Mon d n → ℝ)))
        (ν := (volume : Measure (Fin (n + 1) → ℝ))) hP]
  have hchain3 : ∫⁻ z, volume ((fun a => (a, z)) ⁻¹' volSlab d n (lam / 2) eps del)
      ≤ ENNReal.ofReal (Ks * eps * del ^ n) *
          (ENNReal.ofReal ((2:ℝ)^(n+1) * (lam/2)) * V) := by
    have hpt2 : ∀ z : Fin (n + 1) → ℝ,
        volume ((fun a => (a, z)) ⁻¹' volSlab d n (lam / 2) eps del)
          ≤ ENNReal.ofReal (Ks * eps * del ^ n) *
              (volShell n (lam/2)).indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) z := by
      intro z
      by_cases hz : z ∈ volShell n (lam/2)
      · have hz1 : 1 ≤ rNorm z := hz.1
        have hz2 : rNorm z ≤ 1 + lam / 2 := hz.2
        have hzr2 : rNorm z ≤ 2 := by linarith [hz2, hlam1]
        have hni : ∃ i : Fin (n + 1), 1 / (n + 1 : ℝ) ≤ |z i| := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (n + 1)))
            (fun i => (z i) ^ 2) ⟨0, Finset.mem_univ 0⟩
          have hsum_le : ∑ j, (z j) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) * (z i) ^ 2 := by
            calc ∑ j, (z j) ^ 2 ≤ ∑ _j : Fin (n + 1), (z i) ^ 2 :=
                  Finset.sum_le_sum (fun j _ => hi j (Finset.mem_univ j))
              _ = ((n + 1 : ℕ) : ℝ) * (z i) ^ 2 := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hge : 1 ≤ ∑ j, (z j) ^ 2 := by rw [← rNorm_sq]; nlinarith [hz1]
          have hsqi : 1 / (n + 1 : ℝ) ≤ (z i) ^ 2 := by
            have h1 : 1 ≤ ((n : ℝ) + 1) * (z i) ^ 2 := by
              have h3 : 1 ≤ ((n + 1 : ℕ) : ℝ) * (z i) ^ 2 := le_trans hge hsum_le
              simpa using h3
            rw [div_le_iff₀ (by positivity), mul_comm]
            exact h1
          have hc : (0:ℝ) < 1 / (n + 1) := by positivity
          have hc1 : 1 / (n + 1 : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
          have hcontra : |z i| < 1 / (n + 1) := hcon i
          have h2 : (z i) ^ 2 < (1 / (n + 1)) ^ 2 := by
            have hlt := abs_lt.mp hcontra
            have hpos : 0 < (1 / (n + 1) - z i) * (1 / (n + 1) + z i) :=
              mul_pos (by linarith [hlt.2]) (by linarith [hlt.1])
            nlinarith [hpos]
          have hc2 : (1 / (n + 1 : ℝ)) ^ 2 ≤ 1 / (n + 1) := by
            have h := mul_le_mul hc1 le_rfl hc.le (by norm_num : (0:ℝ) ≤ 1)
            simpa [sq] using h
          linarith [hsqi, h2, hc2]
        obtain ⟨i, hi⟩ := hni
        have hsl := hslab' z i 1 eps del hi hzr2 (by norm_num) (le_of_lt heps_pos)
          (le_of_lt hdel_pos)
        have hsub : (fun a => (a, z)) ⁻¹' volSlab d n (lam / 2) eps del ⊆
            {a : Mon d n → ℝ | rNorm a ≤ 1 ∧ |formEvalR d n a z| ≤ eps ∧
              ∀ j : Fin (n + 1), |gradVec d n a z j| ≤ del} := by
          intro a ha
          exact ⟨ha.1, ha.2.2.2.1, ha.2.2.2.2⟩
        rw [Set.indicator_of_mem hz, Pi.one_apply, mul_one]
        calc volume ((fun a => (a, z)) ⁻¹' volSlab d n (lam / 2) eps del)
            ≤ volume {a : Mon d n → ℝ | rNorm a ≤ 1 ∧ |formEvalR d n a z| ≤ eps ∧
                ∀ j : Fin (n + 1), |gradVec d n a z j| ≤ del} := measure_mono hsub
          _ ≤ ENNReal.ofReal (Ks * eps * del ^ n * 1 ^ (NN d n - n - 1)) := hsl
          _ = ENNReal.ofReal (Ks * eps * del ^ n) := by rw [one_pow, mul_one]
      · have hempty : (fun a => (a, z)) ⁻¹' volSlab d n (lam / 2) eps del = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro a ha
          exact hz ⟨ha.2.1, ha.2.2.1⟩
        rw [Set.indicator_of_notMem hz, mul_zero, hempty, measure_empty]
    calc ∫⁻ z, volume ((fun a => (a, z)) ⁻¹' volSlab d n (lam / 2) eps del)
        ≤ ∫⁻ z, ENNReal.ofReal (Ks * eps * del ^ n) *
            (volShell n (lam/2)).indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) z :=
          lintegral_mono hpt2
      _ = ENNReal.ofReal (Ks * eps * del ^ n) * volume (volShell n (lam/2)) := by
          rw [show (∫⁻ z, ENNReal.ofReal (Ks * eps * del ^ n) *
                (volShell n (lam / 2)).indicator (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) z)
              = ENNReal.ofReal (Ks * eps * del ^ n) *
                ∫⁻ z, (volShell n (lam / 2)).indicator
                  (1 : (Fin (n + 1) → ℝ) → ℝ≥0∞) z from
            lintegral_const_mul _
              (measurable_const.indicator (volShell_measurable n (lam/2)))]
          rw [lintegral_indicator_one (volShell_measurable n (lam/2))]
      _ ≤ ENNReal.ofReal (Ks * eps * del ^ n) *
            (ENNReal.ofReal ((2:ℝ)^(n+1) * (lam/2)) * V) := by
          apply mul_le_mul_right
          simpa [volShell, hV] using
            (vol_shell_le n (lam / 2) (by positivity) (by linarith))
  -- cancel `V`
  have hW : volume (Bset d n lam) * (ENNReal.ofReal A * V)
      ≤ ENNReal.ofReal (Ks * eps * del ^ n * ((2:ℝ)^(n+1) * (lam/2))) * V := by
    have h1 : volume (Bset d n lam) * (ENNReal.ofReal A * V) ≤ volume M * (ENNReal.ofReal A * V) :=
      mul_le_mul_left (measure_mono hsubset) _
    have h5 : ENNReal.ofReal (Ks * eps * del ^ n) *
            (ENNReal.ofReal ((2:ℝ)^(n+1) * (lam/2)) * V)
        = ENNReal.ofReal (Ks * eps * del ^ n * ((2:ℝ)^(n+1) * (lam/2))) * V := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine h1.trans (le_trans (le_trans hchain1 (le_of_eq hchain2)) ?_)
    exact le_trans hchain3 (le_of_eq h5)
  have h7 : volume (Bset d n lam) * ENNReal.ofReal A
      ≤ ENNReal.ofReal (Ks * eps * del ^ n * ((2:ℝ)^(n+1) * (lam/2))) :=
    (ENNReal.mul_le_mul_iff_left (ne_of_gt hVpos) hVtop).mp (by
      nth_rewrite 1 [mul_assoc]
      exact hW)
  have h8 : volume (Bset d n lam)
      ≤ ENNReal.ofReal (Ks * eps * del ^ n * ((2:ℝ)^(n+1) * (lam/2)) / A) := by
    have hA0 : ENNReal.ofReal A ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hApos)
    have hAtop : ENNReal.ofReal A ≠ ⊤ := ENNReal.ofReal_ne_top
    have h := mul_le_mul_left h7 ((ENNReal.ofReal A)⁻¹)
    rw [mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, mul_one] at h
    rw [← ENNReal.ofReal_inv_of_pos hApos, ← ENNReal.ofReal_mul (by positivity)] at h
    rw [div_eq_mul_inv]
    exact h
  have key : Ks * eps * del ^ n * ((2:ℝ)^(n+1) * (lam/2)) / A
      = Ks * (4:ℝ)^(n+1) * (2:ℝ)^n * (1 + C/4) * (2 + volBL d n / 2)^n * lam^2 := by
    rw [heps, hdel, hA, mul_pow, div_pow,
      show (2:ℝ)^(n+1) * (lam/2) = (2:ℝ)^n * lam from by rw [pow_succ]; ring,
      pow_succ' lam n]
    field_simp
    try ring
  have h9 : Ks * eps * del ^ n * ((2:ℝ)^(n+1) * (lam/2)) / A
      ≤ Ks * (4:ℝ)^(n+1) * (2:ℝ)^n * (1 + C/4) * (2 + volBL d n / 2)^n * lam ^ 2 := by
    rw [key]
  have h10 : Ks * (4:ℝ)^(n+1) * (2:ℝ)^n * (1 + C/4) * (2 + volBL d n / 2)^n * lam^2
      ≤ max 1 (Ks * (4:ℝ)^(n+1) * (2:ℝ)^n * (1 + C/4) * (2 + volBL d n / 2)^n) * lam^2 :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg lam)
  exact h8.trans (ENNReal.ofReal_le_ofReal (h9.trans h10))

end Work.HP
