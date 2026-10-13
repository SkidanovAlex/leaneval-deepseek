import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AgmonSlice.CutDefs
import Submission.Work.FTS.EllipticEst.AgmonFts.cut_IBP
import Submission.Work.FTS.EllipticEst.AgmonFts.abs_deriv_cutU_mul_le
import Submission.Work.FTS.EllipticEst.AgmonSlice.Blocks
import Submission.Work.FTS.EllipticEst.zHardyCutDefs
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_props
import Submission.Work.Stability.Cutoff
import Submission.Work.R1G7.chi_deriv_bound
import Submission.Work.ChiExplicit.chi_antitoneOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AgmonSlice (cutRho cutRho_nonneg cutU cutF cutHs cutH cutQs)

namespace Work.FTS.EllipticEst.AgmonFts

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Elementary inequalities -/

/-- `a² ≤ 1` for `|a| ≤ 1`. -/
private lemma sq_le_one_of_abs_le_one {a : ℝ} (h : |a| ≤ 1) : a ^ 2 ≤ 1 := by
  nlinarith only [h, abs_nonneg a, sq_abs a]

/-- `3Wp²XY ≤ (1/4)Wp²X² + 9WY²` for `W, p, X, Y ≥ 0`, `p ≤ 1`. -/
private lemma young_3W (W p X Y : ℝ) (hW : 0 ≤ W) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    3 * W * p ^ 2 * X * Y ≤ (1 / 4) * (W * p ^ 2 * X ^ 2) + 9 * (W * Y ^ 2) := by
  have h1 : 12 * p * X * Y ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by
    have h := sq_nonneg (p * X - 6 * Y)
    nlinarith only [h]
  have h2 : 12 * p ^ 2 * X * Y ≤ p * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left h1 hp0
    nlinarith only [h]
  have hbnn : 0 ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by nlinarith only [sq_nonneg X, sq_nonneg Y]
  have h1mp : 0 ≤ 1 - p := by linarith only [hp1]
  have h3 : p * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) ≤ p ^ 2 * X ^ 2 + 36 * Y ^ 2 := by
    nlinarith only [hbnn, h1mp, hp0]
  have h4 : 12 * W * p ^ 2 * X * Y ≤ W * (p ^ 2 * X ^ 2 + 36 * Y ^ 2) := by
    have h := mul_le_mul_of_nonneg_left (le_trans h2 h3) hW
    nlinarith only [h]
  nlinarith only [h4]

/-- `2cWpXY ≤ (1/12)Wp²X² + 12c(c+1)WY²` for `W, p, X, Y, c ≥ 0`. -/
private lemma young_2cW (W p X Y c : ℝ) (hW : 0 ≤ W) (hc : 0 ≤ c) :
    2 * c * W * p * X * Y ≤ (1 / 12) * (W * p ^ 2 * X ^ 2)
      + 12 * c * (c + 1) * (W * Y ^ 2) := by
  have h1 : 24 * c * p * X * Y ≤ p ^ 2 * X ^ 2 + 144 * c ^ 2 * Y ^ 2 := by
    have h := sq_nonneg (p * X - 12 * c * Y)
    nlinarith only [h]
  have h1' : 24 * c * p * X * Y ≤ p ^ 2 * X ^ 2 + 144 * c * (c + 1) * Y ^ 2 := by
    nlinarith only [h1, hc, sq_nonneg Y]
  have h2 : 2 * c * p * X * Y ≤ (1 / 12) * (p ^ 2 * X ^ 2) + 12 * c * (c + 1) * Y ^ 2 := by
    nlinarith only [h1']
  have h3 : W * (2 * c * p * X * Y)
      ≤ W * ((1 / 12) * (p ^ 2 * X ^ 2) + 12 * c * (c + 1) * Y ^ 2) :=
    mul_le_mul_of_nonneg_left h2 hW
  nlinarith only [h3]

/-- `2ν·Wp²(X+Z)Y ≤ ν²Wp²X² + ν²Wp²Z² + 2WY²` for `W, p, X, Z, Y, ν ≥ 0`, `p ≤ 1`. -/
private lemma young_split_clear (W p X Z Y ν : ℝ) (hW : 0 ≤ W) (hν : 0 ≤ ν) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    2 * ν * (W * p ^ 2 * (X + Z) * Y)
      ≤ ν ^ 2 * (W * p ^ 2 * X ^ 2) + ν ^ 2 * (W * p ^ 2 * Z ^ 2) + 2 * (W * Y ^ 2) := by
  have h1 : 2 * ν * X * Y ≤ ν ^ 2 * X ^ 2 + Y ^ 2 := by
    have h := sq_nonneg (ν * X - Y)
    nlinarith only [h]
  have h2 : 2 * ν * W * p * X * Y ≤ ν ^ 2 * W * p * X ^ 2 + W * p * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h1 (mul_nonneg hW hp0)
    nlinarith only [h]
  have h3 : 2 * ν * W * p ^ 2 * X * Y ≤ ν ^ 2 * W * p ^ 2 * X ^ 2 + W * p ^ 2 * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h2 hp0
    nlinarith only [h]
  have h4 : W * p ^ 2 * Y ^ 2 ≤ W * Y ^ 2 := by
    have hp2 : p ^ 2 ≤ 1 := by nlinarith only [hp0, hp1]
    have h := mul_le_mul_of_nonneg_right hp2 hW
    have h' := mul_le_mul_of_nonneg_right h (sq_nonneg Y)
    nlinarith only [h']
  have h5 : 2 * ν * W * p ^ 2 * X * Y ≤ ν ^ 2 * W * p ^ 2 * X ^ 2 + W * Y ^ 2 := by
    linarith only [h3, h4]
  have h6 : 2 * ν * Z * Y ≤ ν ^ 2 * Z ^ 2 + Y ^ 2 := by
    have h := sq_nonneg (ν * Z - Y)
    nlinarith only [h]
  have h7 : 2 * ν * W * p ^ 2 * Z * Y ≤ ν ^ 2 * W * p ^ 2 * Z ^ 2 + W * Y ^ 2 := by
    have h := mul_le_mul_of_nonneg_left h6 (mul_nonneg hW (sq_nonneg p))
    have hz : W * p ^ 2 * Y ^ 2 ≤ W * Y ^ 2 := h4
    nlinarith only [h, hz]
  have h8 : 2 * ν * (W * p ^ 2 * (X + Z) * Y)
      = 2 * ν * W * p ^ 2 * X * Y + 2 * ν * W * p ^ 2 * Z * Y := by ring
  rw [h8]
  linarith only [h5, h7]

/-- The pointwise assembly (cleared of denominators): all variables nonnegative. -/
private lemma pointwise_final {α Kc W p A Z B D : ℝ} (hα : 0 < α) (hKc : 0 ≤ Kc)
    (hW : 0 ≤ W) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hD : D ≤ 3 * W * p ^ 2 * A + 2 * Kc * W * p * A + W * p ^ 2 * (A + Z)) :
    12 * (α ^ 2 * (D * B))
      ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (W * p ^ 2 * A ^ 2)))
        + 12 * (((9 + 12 * Kc * (Kc + 1)) * α ^ 2 + 2) * (W * B ^ 2))
        + 12 * ((α ^ 4 / 4) * (W * p ^ 2 * Z ^ 2)) := by
  have hν : 0 ≤ α ^ 2 / 2 := by positivity
  have h1 := young_3W W p A B hW hp0 hp1
  have h2 := young_2cW W p A B Kc hW hKc
  have h3 := young_split_clear W p A Z B (α ^ 2 / 2) hW hν hp0 hp1
  have h4 : D * B ≤ (3 * W * p ^ 2 * A + 2 * Kc * W * p * A + W * p ^ 2 * (A + Z)) * B :=
    mul_le_mul_of_nonneg_right hD hB
  have hgoal : α ^ 2 * (D * B)
      ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * (W * p ^ 2 * A ^ 2))
        + ((9 + 12 * Kc * (Kc + 1)) * α ^ 2 + 2) * (W * B ^ 2)
        + (α ^ 4 / 4) * (W * p ^ 2 * Z ^ 2) := by
    nlinarith only [h1, h2, h3, h4, hα, hKc, hW, hp0, hp1]
  linarith only [hgoal]

/-- The final arithmetic: from `α²X ≤ (1/3+α²/4)(α²X) + (c α² + 2)P + (α⁴/4)Q` with
`c ≤ c₀`, `0 < α ≤ 1`, `X, P, Q ≥ 0`, `c, c₀ ≥ 0` and `C₀ = 100 + 100 c₀(c₀+1)`,
conclude `α²X ≤ C₀ (P + α⁴Q)`. -/
private lemma arith_final {α X P Q c c0 C0 : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hX : 0 ≤ X) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hc : 0 ≤ c) (hc0 : 0 ≤ c0) (hcc : c ≤ c0)
    (hC1 : (12 / 5) * (c0 + 2) ≤ C0) (hC2 : (12 / 5 : ℝ) ≤ C0)
    (h1 : α ^ 2 * X ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * X) + (c * α ^ 2 + 2) * P
      + (α ^ 4 / 4) * Q) :
    α ^ 2 * X ≤ C0 * (P + α ^ 4 * Q) := by
  have hα2 : 0 < α ^ 2 := pow_pos hα 2
  have hα2le : α ^ 2 ≤ 1 := by nlinarith only [hα, hα1]
  have hα4 : 0 ≤ α ^ 4 := by positivity
  have h2 : (5 / 12) * (α ^ 2 * X) ≤ (c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
    have hle : (5 / 12 : ℝ) * (α ^ 2 * X) ≤ (2 / 3 - α ^ 2 / 4) * (α ^ 2 * X) := by
      have h56 : (5 / 12 : ℝ) ≤ 2 / 3 - α ^ 2 / 4 := by linarith only [hα2le]
      exact mul_le_mul_of_nonneg_right h56 (by positivity)
    have h1' : (2 / 3 - α ^ 2 / 4) * (α ^ 2 * X)
        ≤ (c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
      nlinarith only [h1]
    linarith only [hle, h1']
  have h3 : α ^ 2 * X ≤ (12 / 5) * ((c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q) := by
    linarith only [h2]
  have h4 : c * α ^ 2 ≤ c0 := by nlinarith only [hcc, hα2le, hc, hc0]
  have h5 : (c * α ^ 2 + 2) * P ≤ (c0 + 2) * P := by nlinarith only [h4, hP]
  have h6 : (α ^ 4 / 4) * Q ≤ α ^ 4 * Q := by nlinarith only [hQ, hα4]
  have h7 : (12 / 5) * ((c * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q)
      ≤ (12 / 5) * ((c0 + 2) * P + α ^ 4 * Q) := by nlinarith only [h5, h6]
  have h8a : (12 / 5) * ((c0 + 2) * P) ≤ C0 * P := by
    have h := mul_le_mul_of_nonneg_right hC1 hP
    linarith only [h]
  have h8b : (12 / 5) * (α ^ 4 * Q) ≤ C0 * (α ^ 4 * Q) := by
    have hPQ : 0 ≤ α ^ 4 * Q := mul_nonneg hα4 hQ
    have h := mul_le_mul_of_nonneg_right hC2 hPQ
    linarith only [h]
  have h8 : (12 / 5) * ((c0 + 2) * P + α ^ 4 * Q) ≤ C0 * (P + α ^ 4 * Q) := by
    linarith only [h8a, h8b]
  linarith only [h3, h7, h8]

/-- `rDzIter 2 h z = z h'(z) + z² h''(z)` on `(0,∞)`. -/
private lemma rDzIter_two_eq {h : ℝ → ℝ} (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) {z : ℝ}
    (hz : 0 < z) : rDzIter 2 h z = z * deriv h z + z ^ 2 * deriv (deriv h) z := by
  have hd1 : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) := hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdiff : DifferentiableAt ℝ (deriv h) z :=
    (hd1.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz)
  have hprod : HasDerivAt (fun y : ℝ => y * deriv h y) (deriv h z + z * deriv (deriv h) z) z := by
    have h := (hasDerivAt_id z).mul hdiff.hasDerivAt
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  change z * deriv (fun y : ℝ => y * deriv h y) z = _
  rw [hprod.deriv]
  ring

/-! ## 2. The cut-off family `psiFun chi k` -/

/-- The cut-offs `psiFun chi k` are nondecreasing in `k` at every `z > 0`. -/
private lemma chi_psiFun_mono {z : ℝ} (hz : 0 < z) :
    ∀ k l : ℕ, 2 ≤ k → k ≤ l →
      Work.FTS.EllipticEst.psiFun Work.Stability.chi k z
        ≤ Work.FTS.EllipticEst.psiFun Work.Stability.chi l z := by
  have hpsi : ∀ k : ℕ, 0 < Real.log (k : ℝ) →
      Work.FTS.EllipticEst.psiFun Work.Stability.chi k z
        = Work.Stability.chi (|Real.log z| / Real.log (k : ℝ)) := by
    intro k hlog
    rw [Work.FTS.EllipticEst.psiFun]
    rcases lt_or_ge (Real.log z) 0 with h | h
    · have hlogz : Real.log z = -|Real.log z| := by rw [abs_of_neg h, neg_neg]
      have h2 : Real.log z / Real.log (k : ℝ) = -(|Real.log z| / Real.log (k : ℝ)) := by
        conv_lhs => rw [hlogz, neg_div]
      rw [h2, Work.Stability.chi_neg]
    · rw [abs_of_nonneg h]
  intro k l hk hkl
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (by omega : 1 < l)
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hlogl : 0 < Real.log (l : ℝ) := Real.log_pos hl1
  rw [hpsi k hlogk, hpsi l hlogl]
  rcases eq_or_ne z 1 with rfl | hz1
  · simp
  · have hlogz : Real.log z ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hz hz1
    have habs : 0 < |Real.log z| := abs_pos.mpr hlogz
    have hlogkl : Real.log (k : ℝ) ≤ Real.log (l : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hkl)
    refine Work.ChiExplicit.chi_antitoneOn (le_of_lt (div_pos habs hlogl))
      (le_of_lt (div_pos habs hlogk)) ?_
    exact div_le_div_of_nonneg_left habs.le hlogk hlogkl

/-- The cut-offs tend to `1` as `k → ∞` at every fixed `z > 0`. -/
private lemma chi_psiFun_tendsto_one {z : ℝ} (hz : 0 < z) :
    Filter.Tendsto (fun k : ℕ => Work.FTS.EllipticEst.psiFun Work.Stability.chi k z)
      Filter.atTop (nhds 1) := by
  have hlog : Filter.Tendsto (fun k : ℕ => Real.log z / Real.log (k : ℝ)) Filter.atTop
      (nhds 0) :=
    Filter.Tendsto.const_div_atTop
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))) (Real.log z)
  have h1 : Filter.Tendsto (fun k : ℕ => Work.Stability.chi (Real.log z / Real.log (k : ℝ)))
      Filter.atTop (nhds (Work.Stability.chi 0)) :=
    Work.Stability.chi_continuous.continuousAt.tendsto.comp hlog
  rw [Work.Stability.chi_zero] at h1
  simpa only [Work.FTS.EllipticEst.psiFun] using h1

/-! ## 3. The unconditional `ℝ≥0∞` Agmon inequality -/

/-- **The unconditional `ℝ≥0∞` weighted Agmon inequality.**  For `w z = (1+z)²/z²`,
`ρ = w²`, `rDz h = z h'`, every `0 < α ≤ 1` and every `h` which is `C^∞` on `(0,∞)`,

  `α² ∫⁻_{[0,∞)} ρ (rDz h)² ≤ C ((∫⁻_{[0,∞)} ρ h²) + α⁴ (∫⁻_{[0,∞)} ρ (z²h'')²))`

with `C` universal. -/
theorem rDz_agmon_lintegral_fts : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (h : ℝ → ℝ), ContDiffOn ℝ Work.Stability.smoothOrder h (Set.Ioi 0) →
    ENNReal.ofReal (α ^ 2) * (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (rDz h z) ^ 2))
      ≤ ENNReal.ofReal C * ((∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2))
          + ENNReal.ofReal (α ^ 4) * (∫⁻ z in Work.Spaces.Iz,
            ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))) := by
  obtain ⟨K, hK0, hKb, -, -⟩ := Work.R1G7.chi_deriv_bound
  have hφcd : ContDiff ℝ Work.Stability.smoothOrder Work.Stability.chi := by
    simpa only [Work.Stability.smoothOrder] using Work.Stability.chi_contDiff
  have hφ0z : ∀ t : ℝ, 2 ≤ |t| → Work.Stability.chi t = 0 := fun t ht =>
    Work.Stability.chi_eq_zero ht
  have hφbdd : ∀ t : ℝ, 0 ≤ Work.Stability.chi t ∧ Work.Stability.chi t ≤ 1 := fun t =>
    ⟨Work.Stability.chi_nonneg t, Work.Stability.chi_le_one t⟩
  have hφcont : ContinuousAt Work.Stability.chi 0 := Work.Stability.chi_continuous.continuousAt
  have hφzero : Work.Stability.chi 0 = 1 := Work.Stability.chi_zero
  have hφanti : AntitoneOn Work.Stability.chi (Set.Ici 0) := Work.ChiExplicit.chi_antitoneOn
  set Kc0 : ℝ := K / Real.log 2 with hKc0def
  have hKc0 : 0 ≤ Kc0 := by
    rw [hKc0def]; exact div_nonneg hK0 (Real.log_pos (by norm_num)).le
  set C0 : ℝ := 100 + 100 * (Kc0 * (Kc0 + 1)) with hC0def
  have hC0 : 0 < C0 := by
    rw [hC0def]
    nlinarith only [hKc0, sq_nonneg Kc0]
  refine ⟨C0, hC0, ?_⟩
  intro α hα hα1 h hh
  have hα2pos : 0 < α ^ 2 := pow_pos hα 2
  have hα4pos : 0 < α ^ 4 := pow_pos hα 4
  -- trivial cases: one of the two sibling integrals is `⊤`
  by_cases hPtop : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)) = ⊤
  · rw [hPtop, top_add, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC0))]
    exact le_top
  by_cases hQtop : (∫⁻ z in Work.Spaces.Iz,
      ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)) = ⊤
  · have h4 : ENNReal.ofReal (α ^ 4) * ⊤ = ⊤ :=
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hα4pos))
    rw [hQtop, h4, add_top, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hC0))]
    exact le_top
  -- ## the honest case
  have hIoi_eq_Ici : volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict (Set.Ici (0 : ℝ)) :=
    MeasureTheory.restrict_Ioi_eq_restrict_Ici
  have hPf : (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)
      ∂volume.restrict (Set.Ioi (0 : ℝ))) ≠ ⊤ := by
    simpa only [Work.Spaces.Iz, hIoi_eq_Ici] using hPtop
  have hQf : (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2
      * (z ^ 2 * deriv (deriv h) z) ^ 2) ∂volume.restrict (Set.Ioi (0 : ℝ))) ≠ ⊤ := by
    simpa only [Work.Spaces.Iz, hIoi_eq_Ici] using hQtop
  have hw2cont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h : ContinuousOn (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) :=
      ContinuousOn.pow (ContinuousOn.div (by fun_prop) (by fun_prop)
        (fun z hz => pow_ne_zero 2 (ne_of_gt hz))) 2
    simpa only [Work.Spaces.w] using h
  have hhcont : ContinuousOn h (Set.Ioi 0) := hh.continuousOn
  have hd1 : ContDiffOn ℝ Work.Stability.smoothOrder (deriv h) (Set.Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen (𝕜 := ℝ) (f := h) isOpen_Ioi).1 hh).2
  have hd2 : ContDiffOn ℝ Work.Stability.smoothOrder (deriv (deriv h)) (Set.Ioi 0) :=
    ((contDiffOn_infty_iff_deriv_of_isOpen (𝕜 := ℝ) (f := deriv h) isOpen_Ioi).1 hd1).2
  have hQcont : ContinuousOn (fun z : ℝ => (z ^ 2 * deriv (deriv h) z) ^ 2) (Set.Ioi 0) :=
    ((continuousOn_id.pow 2).mul hd2.continuousOn).pow 2
  have hPint : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2) (Set.Ioi 0) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((hw2cont.mul (hhcont.pow 2)).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall
        (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).1 hPf
  have hQint : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)
      (Set.Ioi 0) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      ((hw2cont.mul hQcont).aestronglyMeasurable measurableSet_Ioi)
      (Filter.Eventually.of_forall
        (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)))).1 hQf
  -- `P`, `Q` are the honest integrals over the whole half-line
  set P : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (h z) ^ 2 with hPdef
  set Q : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2
    with hQdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact setIntegral_nonneg measurableSet_Ici (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh2 : ContDiffOn ℝ 2 h (Set.Ioi 0) := hh.of_le (by simp [Work.Stability.smoothOrder])
  -- ## the estimate at cut-off level
  have hkey : ∀ n : ℕ,
      IntegrableOn (cutF h (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2)))
        (Set.Ioi 0) ∧
      α ^ 2 * (∫ z in Set.Ioi 0,
          cutF h (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2)) z)
        ≤ C0 * (P + α ^ 4 * Q) := by
    intro n
    set k : ℕ := n + 2 with hkdef
    set ψ : ℝ → ℝ := Work.FTS.EllipticEst.psiFun Work.Stability.chi k with hψdef
    set Kc : ℝ := K / Real.log (k : ℝ) with hKcdef
    set cK : ℝ := 9 + 12 * Kc * (Kc + 1) with hcKdef
    have hk : 2 ≤ k := by omega
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
    have hKc : 0 ≤ Kc := by
      rw [hKcdef]; exact div_nonneg hK0 hlogk_pos.le
    have hcle : Kc ≤ Kc0 := by
      rw [hKcdef, hKc0def]
      exact div_le_div_of_nonneg_left hK0 (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) hkR)
    have hcK0 : 0 ≤ cK := by rw [hcKdef]; positivity
    have hψsm : ContDiffOn ℝ Work.Stability.smoothOrder ψ (Set.Ioi 0) := by
      rw [hψdef]
      exact Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφcd hk
    have hψ2sm : ContDiffOn ℝ 2 ψ (Set.Ioi 0) :=
      hψsm.of_le (by simp [Work.Stability.smoothOrder])
    have hψK : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv ψ z| ≤ Kc := by
      intro z hz
      rw [hKcdef, hψdef]
      exact Work.FTS.EllipticEst.ZCuts.abs_mul_deriv_psiFun_le hφcd hKb hk hz
    have hψsupp : ∀ z : ℝ, 0 < z → z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z → ψ z = 0 := by
      intro z hz h
      rw [hψdef]
      exact Work.FTS.EllipticEst.ZCuts.psiFun_eq_zero (k := k) hφ0z hk hz h
    have hψle1 : ∀ z : ℝ, |ψ z| ≤ 1 := by
      intro z
      have hmem := Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc (k := k) hφbdd z
      rw [hψdef]
      exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    have ha : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := by positivity
    have hab : 1 / (k : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
      have hk2 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hkR]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) ^ 2)]
      nlinarith only [hk2]
    obtain ⟨hFint, hGint, hIBPeq⟩ :=
      cut_IBP h ψ (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2) ha hab hh2 hψ2sm hψsupp
    -- integrability of the two siblings
    have hH_int : IntegrableOn (cutH h) (Set.Ioi 0) := by
      have hfun : cutH h = fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2 := by
        funext z
        simp only [cutH, cutRho]
      rw [hfun]
      exact hPint
    have hcont_Qs : ContinuousOn (cutQs h ψ) (Set.Ioi 0) :=
      ((hw2cont.mul (hψsm.continuousOn.pow 2)).mul hQcont)
    have hQs_int : IntegrableOn (cutQs h ψ) (Set.Ioi 0) := by
      refine Integrable.mono' hQint (hcont_Qs.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      have hnn : 0 ≤ cutQs h ψ z := by
        simp only [cutQs, cutRho]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      simp only [cutQs, cutRho]
      have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
      have hψ2 : ψ z ^ 2 ≤ 1 := sq_le_one_of_abs_le_one (hψle1 z)
      have hZ : (0 : ℝ) ≤ (z ^ 2 * deriv (deriv h) z) ^ 2 := sq_nonneg _
      have hprod : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 :=
        mul_nonneg hw hZ
      have h := mul_le_mul_of_nonneg_left hψ2 hprod
      linarith only [h]
    -- the (cleared) pointwise bound
    have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
        12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|)
          ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
            + 12 * ((cK * α ^ 2 + 2) * cutH h z)
            + 12 * ((α ^ 4 / 4) * cutQs h ψ z) := by
      intro z hz
      have hD := abs_deriv_cutU_mul_le h ψ Kc hh2 hψ2sm hψle1 hψK z hz
      have hr : rDzIter 2 h z = z * deriv h z + z ^ 2 * deriv (deriv h) z :=
        rDzIter_two_eq hh2 hz
      have hD' : |deriv (cutU h ψ) z|
          ≤ 3 * cutRho z * |ψ z| ^ 2 * |z * deriv h z|
            + 2 * Kc * cutRho z * |ψ z| * |z * deriv h z|
            + cutRho z * |ψ z| ^ 2 * (|z * deriv h z| + |z ^ 2 * deriv (deriv h) z|) := by
        rw [hr] at hD
        have h2 : |z * deriv h z + z ^ 2 * deriv (deriv h) z|
            ≤ |z * deriv h z| + |z ^ 2 * deriv (deriv h) z| := abs_add_le _ _
        have h3 : ψ z ^ 2 = |ψ z| ^ 2 := (sq_abs (ψ z)).symm
        rw [h3] at hD
        have hcut : cutRho z * |ψ z| ^ 2 * |z * deriv h z + z ^ 2 * deriv (deriv h) z|
            ≤ cutRho z * |ψ z| ^ 2
              * (|z * deriv h z| + |z ^ 2 * deriv (deriv h) z|) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (cutRho_nonneg z) (sq_nonneg _))
        linarith only [hD, hcut]
      have hkey' := pointwise_final (α := α) (Kc := Kc) (W := cutRho z) (p := |ψ z|)
        (A := |z * deriv h z|) (Z := |z ^ 2 * deriv (deriv h) z|) (B := |h z|)
        (D := |deriv (cutU h ψ) z|) hα hKc (cutRho_nonneg z) (abs_nonneg _) (hψle1 z)
        (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) hD'
      have hp2 : |ψ z| ^ 2 = ψ z ^ 2 := sq_abs (ψ z)
      have hA2 : |z * deriv h z| ^ 2 = (z * deriv h z) ^ 2 := sq_abs _
      have hZ2 : |z ^ 2 * deriv (deriv h) z| ^ 2 = (z ^ 2 * deriv (deriv h) z) ^ 2 := sq_abs _
      have hB2 : |h z| ^ 2 = (h z) ^ 2 := sq_abs (h z)
      have habs : |deriv (cutU h ψ) z * h z| = |deriv (cutU h ψ) z| * |h z| := abs_mul _ _
      simp only [cutF, cutH, cutQs]
      rw [hcKdef, habs, ← hp2, ← hA2, ← hZ2, ← hB2]
      exact hkey'
    -- the absorption (cleared by 12)
    set G : ℝ → ℝ := fun z => 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
        + 12 * ((cK * α ^ 2 + 2) * cutH h z) + 12 * ((α ^ 4 / 4) * cutQs h ψ z) with hGdef
    have hcombo_int : IntegrableOn G (Set.Ioi 0) := by
      rw [hGdef]
      have hA : IntegrableOn (fun z => (1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)) (Set.Ioi 0) :=
        (hFint.const_mul (α ^ 2)).const_mul _
      have hB : IntegrableOn (fun z => (cK * α ^ 2 + 2) * cutH h z) (Set.Ioi 0) :=
        hH_int.const_mul _
      have hC : IntegrableOn (fun z => (α ^ 4 / 4) * cutQs h ψ z) (Set.Ioi 0) :=
        hQs_int.const_mul _
      exact ((hA.const_mul 12).add (hB.const_mul 12)).add (hC.const_mul 12)
    have hXleAbs : 12 * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
        ≤ ∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|) := by
      have hcut : (∫ z in Set.Ioi 0, cutF h ψ z)
          = -(∫ z in Set.Ioi 0, deriv (cutU h ψ) z * h z) := hIBPeq
      have hnorm := MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (fun z => deriv (cutU h ψ) z * h z)
      rw [Real.norm_eq_abs] at hnorm
      simp_rw [Real.norm_eq_abs] at hnorm
      have h1 : -(∫ z in Set.Ioi 0, deriv (cutU h ψ) z * h z)
          ≤ ∫ z in Set.Ioi 0, |deriv (cutU h ψ) z * h z| := (neg_le_abs _).trans hnorm
      have h2 : 12 * (α ^ 2 * (∫ z in Set.Ioi 0, |deriv (cutU h ψ) z * h z|))
          = ∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|) := by
        rw [integral_const_mul, integral_const_mul]
      rw [hcut, ← h2]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (le_of_lt hα2pos))
        (by norm_num)
    have hAbsLe : (∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|))
        ≤ ∫ z in Set.Ioi 0, G z := by
      rw [hGdef]
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall
          (fun z => mul_nonneg (by norm_num) (mul_nonneg (le_of_lt hα2pos) (abs_nonneg _))))
        hcombo_int ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
      exact hpt z hz
    have hsplit : (∫ z in Set.Ioi 0, G z)
        = 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)))
          + 12 * ((cK * α ^ 2 + 2) * (∫ z in Set.Ioi 0, cutH h z))
          + 12 * ((α ^ 4 / 4) * (∫ z in Set.Ioi 0, cutQs h ψ z)) := by
      rw [hGdef]
      have hA : IntegrableOn (fun z => (1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)) (Set.Ioi 0) :=
        (hFint.const_mul (α ^ 2)).const_mul _
      have hB : IntegrableOn (fun z => (cK * α ^ 2 + 2) * cutH h z) (Set.Ioi 0) :=
        hH_int.const_mul _
      have hC : IntegrableOn (fun z => (α ^ 4 / 4) * cutQs h ψ z) (Set.Ioi 0) :=
        hQs_int.const_mul _
      have hA' : IntegrableOn (fun z => 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)))
          (Set.Ioi 0) := hA.const_mul 12
      have hB' : IntegrableOn (fun z => 12 * ((cK * α ^ 2 + 2) * cutH h z)) (Set.Ioi 0) :=
        hB.const_mul 12
      have hC' : IntegrableOn (fun z => 12 * ((α ^ 4 / 4) * cutQs h ψ z)) (Set.Ioi 0) :=
        hC.const_mul 12
      have e1 : (∫ z in Set.Ioi 0, (12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
            + 12 * ((cK * α ^ 2 + 2) * cutH h z) + 12 * ((α ^ 4 / 4) * cutQs h ψ z)))
          = (∫ z in Set.Ioi 0, (12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
                + 12 * ((cK * α ^ 2 + 2) * cutH h z)))
            + (∫ z in Set.Ioi 0, 12 * ((α ^ 4 / 4) * cutQs h ψ z)) := by
        have h := integral_add (μ := volume.restrict (Set.Ioi (0 : ℝ)))
          (hA'.add hB') hC'
        simpa using h
      have e2 : (∫ z in Set.Ioi 0, (12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z))
              + 12 * ((cK * α ^ 2 + 2) * cutH h z)))
          = (∫ z in Set.Ioi 0, 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)))
            + (∫ z in Set.Ioi 0, 12 * ((cK * α ^ 2 + 2) * cutH h z)) := by
        have h := integral_add (μ := volume.restrict (Set.Ioi (0 : ℝ))) hA' hB'
        simpa using h
      have e3 : (∫ z in Set.Ioi 0, 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * cutF h ψ z)))
          = 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))) := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul]
      have e4 : (∫ z in Set.Ioi 0, 12 * ((cK * α ^ 2 + 2) * cutH h z))
          = 12 * ((cK * α ^ 2 + 2) * (∫ z in Set.Ioi 0, cutH h z)) := by
        rw [integral_const_mul, integral_const_mul]
      have e5 : (∫ z in Set.Ioi 0, 12 * ((α ^ 4 / 4) * cutQs h ψ z))
          = 12 * ((α ^ 4 / 4) * (∫ z in Set.Ioi 0, cutQs h ψ z)) := by
        rw [integral_const_mul, integral_const_mul]
      rw [e1, e2, e3, e4, e5]
    have hHval : (∫ z in Set.Ioi 0, cutH h z) = P := by
      have hfun : cutH h = fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2 := by
        funext z
        simp only [cutH, cutRho]
      rw [hfun, hPdef, Work.Spaces.Iz, ← MeasureTheory.integral_Ici_eq_integral_Ioi]
    have hQsle : (∫ z in Set.Ioi 0, cutQs h ψ z) ≤ Q := by
      have hQeq : Q = ∫ z in Set.Ioi 0,
          (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 := by
        rw [hQdef, Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
      rw [hQeq]
      refine integral_mono_of_nonneg ?_ hQint ?_
      · filter_upwards with z
        simp only [cutQs, cutRho]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      · filter_upwards with z
        simp only [cutQs, cutRho]
        have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have hψ2 : ψ z ^ 2 ≤ 1 := sq_le_one_of_abs_le_one (hψle1 z)
        have hZ : (0 : ℝ) ≤ (z ^ 2 * deriv (deriv h) z) ^ 2 := sq_nonneg _
        have hprod : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2 :=
          mul_nonneg hw hZ
        have h := mul_le_mul_of_nonneg_left hψ2 hprod
        linarith only [h]
    have hmain : α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z) ≤ C0 * (P + α ^ 4 * Q) := by
      have h12 : 12 * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
          ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)))
            + 12 * ((cK * α ^ 2 + 2) * P) + 12 * ((α ^ 4 / 4) * Q) := by
        calc 12 * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
            ≤ ∫ z in Set.Ioi 0, 12 * (α ^ 2 * |deriv (cutU h ψ) z * h z|) := hXleAbs
          _ ≤ ∫ z in Set.Ioi 0, G z := hAbsLe
          _ = _ := hsplit
          _ ≤ 12 * ((1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)))
              + 12 * ((cK * α ^ 2 + 2) * P) + 12 * ((α ^ 4 / 4) * Q) := by
            rw [hHval]
            exact add_le_add (add_le_add le_rfl le_rfl)
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hQsle (by positivity)) (by norm_num))
      have hstep : α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z)
          ≤ (1 / 3 + α ^ 2 / 4) * (α ^ 2 * (∫ z in Set.Ioi 0, cutF h ψ z))
            + (cK * α ^ 2 + 2) * P + (α ^ 4 / 4) * Q := by
        linarith only [h12]
      have hcc : cK ≤ 9 + 12 * Kc0 * (Kc0 + 1) := by
        rw [hcKdef]
        nlinarith only [hKc, hcle, hKc0, sq_nonneg Kc, sq_nonneg Kc0]
      have hXn : 0 ≤ ∫ z in Set.Ioi 0, cutF h ψ z := by
        refine integral_nonneg (fun z => ?_)
        simp only [cutF, cutRho]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)
      have hC1 : (12 / 5) * ((9 + 12 * Kc0 * (Kc0 + 1)) + 2) ≤ C0 := by
        rw [hC0def]
        nlinarith only [hKc0, sq_nonneg Kc0]
      have hC2 : (12 / 5 : ℝ) ≤ C0 := by
        rw [hC0def]
        nlinarith only [hKc0, sq_nonneg Kc0]
      exact arith_final (α := α) (X := ∫ z in Set.Ioi 0, cutF h ψ z) (P := P) (Q := Q)
        (c := cK) (c0 := 9 + 12 * Kc0 * (Kc0 + 1)) (C0 := C0) hα hα1 hXn hPnn hQnn hcK0
        (by nlinarith only [hKc0, sq_nonneg Kc0]) hcc hC1 hC2 hstep
    exact ⟨hFint, hmain⟩
  -- ## monotone convergence
  have hmeas : ∀ n : ℕ, AEMeasurable
      (fun z => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
    intro n
    have hpsi : ContDiffOn ℝ Work.Stability.smoothOrder
        (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2)) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.ZCuts.psiFun_contDiffOn hφcd (by omega)
    have hdh : ContinuousOn (deriv h) (Set.Ioi 0) := hd1.continuousOn
    have hcont : ContinuousOn (fun z => (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2) (Set.Ioi 0) :=
      (hw2cont.mul (hpsi.continuousOn.pow 2)).mul ((continuousOn_id.mul hdh).pow 2)
    exact ((ENNReal.continuous_ofReal.comp_continuousOn hcont).aestronglyMeasurable
      measurableSet_Ioi).aemeasurable
  have hmono : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), Monotone
      (fun n : ℕ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    intro n m hnm
    have h1 : Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z
        ≤ Work.FTS.EllipticEst.psiFun Work.Stability.chi (m + 2) z :=
      chi_psiFun_mono hz (n + 2) (m + 2) (by omega) (by omega)
    have h0n : 0 ≤ Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z :=
      (Work.FTS.EllipticEst.ZCuts.psiFun_mem_Icc (k := n + 2) hφbdd z).1
    have h3 : (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        ≤ (Work.FTS.EllipticEst.psiFun Work.Stability.chi (m + 2) z) ^ 2 := by
      have h := mul_self_le_mul_self h0n h1
      simpa only [sq] using h
    refine ENNReal.ofReal_le_ofReal ?_
    have hw : (0 : ℝ) ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hz : (0 : ℝ) ≤ (z * deriv h z) ^ 2 := sq_nonneg _
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hw) hz
    nlinarith only [h]
  have htendsto : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal ((Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with z hz
    have h1 : Filter.Tendsto
        (fun n : ℕ => Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z)
        Filter.atTop (nhds 1) :=
      (chi_psiFun_tendsto_one hz).comp (Filter.tendsto_add_atTop_nat 2)
    have h2 : Filter.Tendsto
        (fun n : ℕ => (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2)
        Filter.atTop (nhds 1) := by simpa using h1.pow 2
    have h3 : Filter.Tendsto
        (fun n : ℕ => (Work.Spaces.w z) ^ 2
          * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
          * (z * deriv h z) ^ 2) Filter.atTop
        (nhds ((Work.Spaces.w z) ^ 2 * 1 * (z * deriv h z) ^ 2)) :=
      (tendsto_const_nhds.mul h2).mul tendsto_const_nhds
    have h4 := ENNReal.continuous_ofReal.tendsto _ |>.comp h3
    simpa only [Function.comp_def, mul_one] using h4
  have hconv := MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htendsto
  -- the `α²`-weighted bound for the uncut integrand
  have hFatou : ENNReal.ofReal (α ^ 2)
      * (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ioi (0 : ℝ))) ≤ ENNReal.ofReal (C0 * (P + α ^ 4 * Q)) := by
    have hcontmul := (ENNReal.continuous_const_mul
      (ENNReal.ofReal_ne_top (r := α ^ 2))).tendsto
      (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
        ∂volume.restrict (Set.Ioi (0 : ℝ)))
    refine le_of_tendsto (hcontmul.comp hconv) (Filter.Eventually.of_forall ?_)
    intro n
    have hInt : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2) (Set.Ioi 0) := (hkey n).1
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] (fun z => (Work.Spaces.w z) ^ 2
        * (Work.FTS.EllipticEst.psiFun Work.Stability.chi (n + 2) z) ^ 2
        * (z * deriv h z) ^ 2) :=
      Filter.Eventually.of_forall
        (fun z => mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))
    simp only [Function.comp_apply]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    rw [← ENNReal.ofReal_mul (le_of_lt hα2pos)]
    refine ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr ?_
    have h2 := (hkey n).2
    simp only [cutF, cutRho] at h2
    exact h2
  -- back to `Iz` and to the two honest integrals
  have hgoal_eq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (rDz h z) ^ 2))
      = ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ioi (0 : ℝ)) := by
    show (∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ici (0 : ℝ)))
        = ∫⁻ z, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z * deriv h z) ^ 2)
          ∂volume.restrict (Set.Ioi (0 : ℝ))
    rw [← hIoi_eq_Ici]
  have hPeq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (h z) ^ 2)) = ENNReal.ofReal P := by
    have h := Work.FTS.EllipticEst.ofReal_integral_eq_lintegral_Iz
      (g := fun z => (Work.Spaces.w z) ^ 2 * (h z) ^ 2)
      (hw2cont.mul (hhcont.pow 2))
      (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hPtop
    rw [hPdef, h]
  have hQeq : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2))
      = ENNReal.ofReal Q := by
    have h := Work.FTS.EllipticEst.ofReal_integral_eq_lintegral_Iz
      (g := fun z => (Work.Spaces.w z) ^ 2 * (z ^ 2 * deriv (deriv h) z) ^ 2)
      (hw2cont.mul hQcont)
      (fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hQtop
    rw [hQdef, h]
  rw [hgoal_eq, hPeq, hQeq]
  refine hFatou.trans (le_of_eq ?_)
  have h1 : ENNReal.ofReal (C0 * (P + α ^ 4 * Q))
      = ENNReal.ofReal C0 * ENNReal.ofReal (P + α ^ 4 * Q) :=
    ENNReal.ofReal_mul (le_of_lt hC0)
  have h2 : ENNReal.ofReal (P + α ^ 4 * Q)
      = ENNReal.ofReal P + ENNReal.ofReal (α ^ 4) * ENNReal.ofReal Q := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (le_of_lt hα4pos)]
  rw [h1, h2]

end Work.FTS.EllipticEst.AgmonFts
