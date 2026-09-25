import Mathlib
import Submission.Work.NN.Core.TelTwoDF.changeOrigin_norm_le_of_bound
import Submission.Work.CR.Flat.Cauchy.norm_continuousMultilinearMap_le_of_diagonal
import Submission.Work.CR.Flat.Cauchy.analyticOn_real_of_differentiableAt_complex

/-!
# A uniform Taylor bound for real analytic functions on compact sets

If `F : X → ℂ` is real analytic on an open set `U` and `K ⊆ U` is compact, then there are
`R > 0` and `C > 0` such that for every `p ∈ K` the Taylor series of `F` at `p` converges to
`F (p + y)` for `‖y‖ < R`, and such that the Taylor coefficients are uniformly bounded:
`‖(k!)⁻¹ • D^k F p‖ * R^k ≤ C` for all `k`.

The proof uses a finite cover of `K` by balls on which a power series for `F` is available with
a uniform radius, the change-of-origin formula for formal multilinear series (with an explicit
coefficient bound), and the polarization bound for symmetric multilinear maps.
-/

namespace Work.NN.Core.TelTwoDF

open Set Metric Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ### The change-of-origin coefficient bound

`Work.NN.Core.TelTwoDF.changeOrigin_norm_le_of_bound` is imported above. -/

/-! ### Analyticity at a point of an open set -/

lemma taylorBound_analyticAt {U : Set X} (hU : IsOpen U) {F : X → ℂ} (hF : AnalyticOn ℝ F U)
    {x : X} (hx : x ∈ U) : AnalyticAt ℝ F x := by
  obtain ⟨g, -, hEqOn, hgan⟩ := (hF x hx).exists_analyticAt
  refine hgan.congr (Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU.mem_nhds hx, fun y hy => ?_⟩)
  exact (hEqOn (Or.inr hy)).symm

/-- At each point of `U` there is a power series with a positive (real) radius of convergence. -/
lemma taylorBound_exists_witness {U : Set X} (hU : IsOpen U) {F : X → ℂ}
    (hF : AnalyticOn ℝ F U) {x : X} (hx : x ∈ U) :
    ∃ w : FormalMultilinearSeries ℝ X ℂ × ℝ≥0,
      0 < w.2 ∧ HasFPowerSeriesOnBall F w.1 x ((w.2 : ℝ≥0∞)) := by
  obtain ⟨Q, r, hQ⟩ := taylorBound_analyticAt hU hF hx
  obtain ⟨q, hq0, hqr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hQ.r_pos
  exact ⟨(Q, q), by exact_mod_cast hq0, hQ.mono hq0 (le_of_lt hqr)⟩

/-- A choice, for every `x ∈ U`, of a witnessing power series and a radius. -/
noncomputable def taylorBound_wit {U : Set X} (hU : IsOpen U) {F : X → ℂ}
    (hF : AnalyticOn ℝ F U) (x : X) : FormalMultilinearSeries ℝ X ℂ × ℝ≥0 := by
  classical
  exact if h : x ∈ U then Classical.choose (taylorBound_exists_witness hU hF h) else (0, 1)

lemma taylorBound_wit_pos {U : Set X} (hU : IsOpen U) {F : X → ℂ} (hF : AnalyticOn ℝ F U)
    {x : X} (hx : x ∈ U) : 0 < (taylorBound_wit hU hF x).2 := by
  simp only [taylorBound_wit, dif_pos hx]
  exact (Classical.choose_spec (taylorBound_exists_witness hU hF hx)).1

lemma taylorBound_wit_series {U : Set X} (hU : IsOpen U) {F : X → ℂ} (hF : AnalyticOn ℝ F U)
    {x : X} (hx : x ∈ U) :
    HasFPowerSeriesOnBall F (taylorBound_wit hU hF x).1 x ((taylorBound_wit hU hF x).2 : ℝ≥0∞) := by
  simpa only [taylorBound_wit, dif_pos hx] using
    (Classical.choose_spec (taylorBound_exists_witness hU hF hx)).2

/-- A bound for the coefficients of the witnessing series at half the radius. -/
lemma taylorBound_exists_bound {U : Set X} (hU : IsOpen U) {F : X → ℂ}
    (hF : AnalyticOn ℝ F U) {x : X} (hx : x ∈ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ‖(taylorBound_wit hU hF x).1 k‖ ≤ C / (((taylorBound_wit hU hF x).2 : ℝ) / 2) ^ k := by
  have hr : (0 : ℝ≥0) < (taylorBound_wit hU hF x).2 := taylorBound_wit_pos hU hF hx
  have hlt : (((taylorBound_wit hU hF x).2 / 2 : ℝ≥0) : ℝ≥0∞) <
      (taylorBound_wit hU hF x).1.radius := by
    refine lt_of_lt_of_le ?_ (taylorBound_wit_series hU hF hx).r_le
    rw [ENNReal.coe_lt_coe]
    exact half_lt_self hr
  obtain ⟨C, hC, hCb⟩ := FormalMultilinearSeries.norm_le_div_pow_of_pos_of_lt_radius
    (taylorBound_wit hU hF x).1 (r := (taylorBound_wit hU hF x).2 / 2) (half_pos hr) hlt
  exact ⟨C, hC, fun k => by simpa [NNReal.coe_div] using hCb k⟩

noncomputable def taylorBound_C {U : Set X} (hU : IsOpen U) {F : X → ℂ}
    (hF : AnalyticOn ℝ F U) (x : X) : ℝ := by
  classical
  exact if h : x ∈ U then Classical.choose (taylorBound_exists_bound hU hF h) else 1

lemma taylorBound_C_pos {U : Set X} (hU : IsOpen U) {F : X → ℂ} (hF : AnalyticOn ℝ F U)
    {x : X} (hx : x ∈ U) : 0 < taylorBound_C hU hF x := by
  simp only [taylorBound_C, dif_pos hx]
  exact (Classical.choose_spec (taylorBound_exists_bound hU hF hx)).1

lemma taylorBound_C_le {U : Set X} (hU : IsOpen U) {F : X → ℂ} (hF : AnalyticOn ℝ F U)
    {x : X} (hx : x ∈ U) (k : ℕ) :
    ‖(taylorBound_wit hU hF x).1 k‖ ≤
      taylorBound_C hU hF x / (((taylorBound_wit hU hF x).2 : ℝ) / 2) ^ k := by
  simp only [taylorBound_C, dif_pos hx]
  exact (Classical.choose_spec (taylorBound_exists_bound hU hF hx)).2 k

/-! ### The polarization bound -/

/-- The polarization bound for the `k`-th derivative of an analytic function, in the form needed
here: the operator norm is controlled by the diagonal values, with the classical loss `k^k/k!`. -/
theorem norm_factorial_inv_iteratedFDeriv_le {F : X → ℂ} {p : X}
    (hF : ContDiffAt ℝ (⊤ : WithTop ℕ∞) F p) {k : ℕ} {D : ℝ}
    (hD : ∀ u : X, ‖u‖ ≤ 1 →
      ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p (fun _ => u)‖ ≤ D) :
    ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p‖ ≤
      (k : ℝ) ^ k / (k.factorial : ℝ) * D := by
  have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hD' : ∀ u : X, ‖u‖ ≤ 1 → ‖iteratedFDeriv ℝ k F p (fun _ => u)‖ ≤
      (k.factorial : ℝ) * D := by
    intro u hu
    have h1 : (k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k F p (fun _ => u)‖ ≤ D := by
      simpa only [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hkpos.le)] using hD u hu
    exact (inv_mul_le_iff₀ hkpos).mp h1
  have hsym : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → X),
      iteratedFDeriv ℝ k F p (v ∘ σ) = iteratedFDeriv ℝ k F p v :=
    fun σ v => hF.iteratedFDeriv_comp_perm v σ
  have hpoli := Work.CR.Flat.Cauchy.norm_continuousMultilinearMap_le_of_diagonal
    (T := iteratedFDeriv ℝ k F p) hsym (D := (k.factorial : ℝ) * D) hD'
  calc ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p‖
      = (k.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ k F p‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hkpos.le)]
    _ ≤ (k.factorial : ℝ)⁻¹ *
          ((k : ℝ) ^ k / (k.factorial : ℝ) * ((k.factorial : ℝ) * D)) := by
        gcongr
    _ = (k : ℝ) ^ k / (k.factorial : ℝ) * D := by
        field_simp

/-! ### The main theorem -/

theorem analytic_uniform_taylor_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : Set X} (hU : IsOpen U) {F : X → ℂ} (hF : AnalyticOn ℝ F U)
    {K : Set X} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ R > 0, ∃ C > 0,
      (∀ p ∈ K, ∀ y : X, ‖y‖ < R →
        HasSum (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p (fun _ => y))
          (F (p + y))) ∧
      (∀ p ∈ K, ∀ k : ℕ, ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p‖ * R ^ k ≤ C) := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · rw [hKe]
    exact ⟨1, one_pos, 1, one_pos, by simp, by simp⟩
  · -- a finite cover of `K` by balls of radius `r x / 16`
    obtain ⟨b', hb'sub, hb'fin, hcover⟩ := hK.elim_finite_subcover_image
      (b := K) (c := fun i : X => Metric.ball i (((taylorBound_wit hU hF i).2 : ℝ) / 16))
      (fun i _ => isOpen_ball)
      (fun x hx => by
        refine mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hx, ?_⟩⟩
        have hpos : (0 : ℝ) < ((taylorBound_wit hU hF x).2 : ℝ) / 16 := by
          have := taylorBound_wit_pos hU hF (hKU hx)
          positivity
        simpa [Metric.mem_ball] using hpos)
    let t : Finset X := hb'fin.toFinset
    have htmem : ∀ i : X, i ∈ t ↔ i ∈ b' := fun i => by
      simp only [t]
      exact hb'fin.mem_toFinset
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      obtain ⟨i, hi, -⟩ := by simpa only [Set.mem_iUnion₂] using hcover hx
      exact ⟨i, (htmem i).mpr hi⟩
    let fR : X → ℝ := fun x => ((taylorBound_wit hU hF x).2 : ℝ)
    let fC : X → ℝ := fun x => taylorBound_C hU hF x
    set R : ℝ := (t.inf' htne fR) / 16 with hRdef
    set C : ℝ := 2 * (t.sup' htne fC) with hCdef
    have hRpos : 0 < R := by
      rw [hRdef]
      have hinf : 0 < t.inf' htne fR := by
        rw [Finset.lt_inf'_iff (s := t) htne]
        intro i hi
        have hiU : i ∈ U := hKU (hb'sub ((htmem i).mp hi))
        exact_mod_cast taylorBound_wit_pos hU hF hiU
      positivity
    have hCpos : 0 < C := by
      have hsup : 0 < t.sup' htne fC := by
        rw [Finset.lt_sup'_iff (s := t) htne]
        obtain ⟨i, hi⟩ := htne
        exact ⟨i, hi, taylorBound_C_pos hU hF (hKU (hb'sub ((htmem i).mp hi)))⟩
      rw [hCdef]
      linarith
    refine ⟨R, hRpos, C, hCpos, ?_, ?_⟩
    · -- first conjunct: the Taylor series converges to `F (p + y)`
      intro p hp y hy
      obtain ⟨i, hi, hpi⟩ := by simpa only [Set.mem_iUnion₂] using hcover hp
      have hiU : i ∈ U := hKU (hb'sub hi)
      have hri : (0 : ℝ) < fR i := by
        simp only [fR]
        exact_mod_cast taylorBound_wit_pos hU hF hiU
      have hRle : R ≤ fR i / 16 := by
        rw [hRdef, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 16)]
        exact Finset.inf'_le fR ((htmem i).mpr hi)
      have hd : ‖p - i‖ < fR i / 16 := by
        have := hpi
        rw [Metric.mem_ball, dist_eq_norm] at this
        simpa only [fR] using this
      have hdrad_nn : ‖p - i‖₊ < (taylorBound_wit hU hF i).2 := by
        rw [← NNReal.coe_lt_coe]
        rw [show (‖p - i‖₊ : ℝ) = ‖p - i‖ from rfl,
          show ((taylorBound_wit hU hF i).2 : ℝ) = fR i from rfl]
        have h2 : fR i / 16 ≤ fR i := by linarith
        linarith
      have hdrad : (‖p - i‖₊ : ℝ≥0∞) < ((taylorBound_wit hU hF i).2 : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.mpr hdrad_nn
      have hchg : HasFPowerSeriesOnBall F ((taylorBound_wit hU hF i).1.changeOrigin (p - i)) p
          (((taylorBound_wit hU hF i).2 : ℝ≥0∞) - ‖p - i‖₊) := by
        have h1 := (taylorBound_wit_series hU hF hiU).changeOrigin hdrad
        rwa [show i + (p - i) = p from by abel] at h1
      have hycond : y ∈ Metric.eball (0 : X) (((taylorBound_wit hU hF i).2 : ℝ≥0∞) - ‖p - i‖₊) := by
        rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_tsub_iff_right, enorm_eq_nnnorm,
          ← ENNReal.coe_add, ENNReal.coe_lt_coe]
        rw [← NNReal.coe_lt_coe, NNReal.coe_add]
        rw [show (‖y‖₊ : ℝ) = ‖y‖ from rfl, show (‖p - i‖₊ : ℝ) = ‖p - i‖ from rfl,
          show ((taylorBound_wit hU hF i).2 : ℝ) = fR i from rfl]
        have hy' : ‖y‖ < fR i / 16 := lt_of_lt_of_le hy hRle
        linarith
      exact hchg.hasSum_iteratedFDeriv hycond
    · -- second conjunct: uniform bounds on the Taylor coefficients
      intro p hp k
      obtain ⟨i, hi, hpi⟩ := by simpa only [Set.mem_iUnion₂] using hcover hp
      have hiU : i ∈ U := hKU (hb'sub hi)
      have hri : (0 : ℝ) < fR i := by
        simp only [fR]
        exact_mod_cast taylorBound_wit_pos hU hF hiU
      have hRle : R ≤ fR i / 16 := by
        rw [hRdef, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 16)]
        exact Finset.inf'_le fR ((htmem i).mpr hi)
      have hd : ‖p - i‖ < fR i / 16 := by
        have := hpi
        rw [Metric.mem_ball, dist_eq_norm] at this
        simpa only [fR] using this
      -- the coefficient bound for the translated series
      have hcoef : ∀ j : ℕ,
          ‖((taylorBound_wit hU hF i).1.changeOrigin (p - i)) j‖ ≤
            2 * taylorBound_C hU hF i * (4 / fR i) ^ j := by
        intro j
        have hmain := changeOrigin_norm_le_of_bound (p := (taylorBound_wit hU hF i).1)
          (C := taylorBound_C hU hF i) (r := fR i / 2) (d := p - i)
          (taylorBound_C_pos hU hF hiU) (by linarith)
          (fun m => by simpa only [fR] using taylorBound_C_le hU hF hiU m)
          (by
            have hh : fR i / 2 / 8 = fR i / 16 := by ring
            rw [hh]
            exact le_of_lt hd) j
        have hrw : 2 * taylorBound_C hU hF i * (2 / (fR i / 2)) ^ j =
            2 * taylorBound_C hU hF i * (4 / fR i) ^ j := by
          rw [show (2:ℝ) / (fR i / 2) = 4 / fR i by field_simp; ring]
        rwa [hrw] at hmain
      -- the translated series is a witness at `p`
      have hdrad_nn : ‖p - i‖₊ < (taylorBound_wit hU hF i).2 := by
        rw [← NNReal.coe_lt_coe]
        rw [show (‖p - i‖₊ : ℝ) = ‖p - i‖ from rfl,
          show ((taylorBound_wit hU hF i).2 : ℝ) = fR i from rfl]
        have h2 : fR i / 16 ≤ fR i := by linarith
        linarith
      have hdrad : (‖p - i‖₊ : ℝ≥0∞) < ((taylorBound_wit hU hF i).2 : ℝ≥0∞) :=
        ENNReal.coe_lt_coe.mpr hdrad_nn
      have hchg : HasFPowerSeriesOnBall F ((taylorBound_wit hU hF i).1.changeOrigin (p - i)) p
          (((taylorBound_wit hU hF i).2 : ℝ≥0∞) - ‖p - i‖₊) := by
        have h1 := (taylorBound_wit_series hU hF hiU).changeOrigin hdrad
        rwa [show i + (p - i) = p from by abel] at h1
      -- diagonal bound for the `k`-th derivative
      have hdiag : ∀ u : X, ‖u‖ ≤ 1 →
          ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p (fun _ => u)‖ ≤
            2 * taylorBound_C hU hF i * (4 / fR i) ^ k := by
        intro u hu
        have hfs := hchg.factorial_smul u k
        have hkey : ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p (fun _ => u) =
            ((taylorBound_wit hU hF i).1.changeOrigin (p - i)) k (fun _ => u) := by
          have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
          have hfs' : (k.factorial : ℝ) •
              (((taylorBound_wit hU hF i).1.changeOrigin (p - i)) k (fun _ => u)) =
              iteratedFDeriv ℝ k F p (fun _ => u) := by
            rw [Nat.cast_smul_eq_nsmul]
            exact hfs
          rw [← hfs', smul_smul, inv_mul_cancel₀ hk, one_smul]
        rw [hkey]
        have hop := ContinuousMultilinearMap.le_opNorm
          (((taylorBound_wit hU hF i).1.changeOrigin (p - i)) k) (fun _ : Fin k => u)
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hop
        refine le_trans ?_ (hcoef k)
        calc ‖(((taylorBound_wit hU hF i).1.changeOrigin (p - i)) k) (fun _ : Fin k => u)‖
            ≤ ‖((taylorBound_wit hU hF i).1.changeOrigin (p - i)) k‖ * ‖u‖ ^ k := hop
          _ ≤ ‖((taylorBound_wit hU hF i).1.changeOrigin (p - i)) k‖ * 1 := by
              have huk : ‖u‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg u) hu
              exact mul_le_mul_of_nonneg_left huk (norm_nonneg _)
          _ = ‖((taylorBound_wit hU hF i).1.changeOrigin (p - i)) k‖ := mul_one _
      have hcont : ContDiffAt ℝ (⊤ : WithTop ℕ∞) F p :=
        (taylorBound_analyticAt hU hF (hKU hp)).contDiffAt
      have hpol := norm_factorial_inv_iteratedFDeriv_le (k := k) hcont hdiag
      have hkpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have hpow3 : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ 3 ^ k := by
        rw [div_le_iff₀ hkpos]
        calc (k : ℝ) ^ k ≤ (k.factorial : ℝ) * 3 ^ k :=
              Work.CR.Flat.Cauchy.pow_self_le_factorial_mul_three_pow k
          _ = 3 ^ k * (k.factorial : ℝ) := by ring
      have hstep : (k : ℝ) ^ k / (k.factorial : ℝ) * ((4 / fR i) ^ k * R ^ k) ≤ 1 := by
        have h1 : (4 / fR i) ^ k * R ^ k = (4 * R / fR i) ^ k := by
          rw [← mul_pow]; ring
        rw [h1]
        have h2 : 4 * R / fR i ≤ 1 / 4 := by
          rw [div_le_iff₀ hri]
          linarith
        calc (k : ℝ) ^ k / (k.factorial : ℝ) * (4 * R / fR i) ^ k
            ≤ 3 ^ k * (1 / 4 : ℝ) ^ k := by
              have h24 : (4 * R / fR i) ^ k ≤ (1 / 4 : ℝ) ^ k :=
                pow_le_pow_left₀ (by positivity) h2 k
              exact mul_le_mul hpow3 h24 (by positivity) (by positivity)
          _ = (3 / 4 : ℝ) ^ k := by rw [← mul_pow]; norm_num
          _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      calc ‖((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k F p‖ * R ^ k
          ≤ ((k : ℝ) ^ k / (k.factorial : ℝ) *
              (2 * taylorBound_C hU hF i * (4 / fR i) ^ k)) * R ^ k := by
            exact mul_le_mul_of_nonneg_right hpol (by positivity)
        _ = 2 * taylorBound_C hU hF i *
              ((k : ℝ) ^ k / (k.factorial : ℝ) * ((4 / fR i) ^ k * R ^ k)) := by ring
        _ ≤ 2 * taylorBound_C hU hF i * 1 := by
            have hCnn : (0:ℝ) ≤ 2 * taylorBound_C hU hF i := by
              have := taylorBound_C_pos hU hF hiU
              linarith
            exact mul_le_mul_of_nonneg_left hstep hCnn
        _ = 2 * taylorBound_C hU hF i := by ring
        _ ≤ C := by
            rw [hCdef]
            have := Finset.le_sup' fC ((htmem i).mpr hi)
            simp only [fC] at this
            linarith

end Work.NN.Core.TelTwoDF
