import Mathlib
import Submission.Work.ZeroDensity.LogFree.CrossLine
import Submission.Work.ZeroDensity.LogFree.Ssm_bound_D
import Submission.Work.LinnikAreas2.hb11_offdiag_pair_bound
import Submission.Commons.Analysis.Complex.vertical_contour_shift
import Submission.Work.LinnikAreas.Density4.rect_edge_tendsto_zero

/-!
# `Work.ZeroDensity.LogFree.CrossShift` — the contour shift for the cross Gram entry

`CrossDefs.crossGram q W X U' ψ σ = Ssm q 1 W W X ψ σ - Ssm q 1 W W U' ψ σ` is the integral of
`Ptw q 1 W W X U' ψ σ` on `Re s = 1` (`LinnikAreas2.Ssm_sub_eq_Ptw_line`).  Here the contour is
moved to the line `Re (σ+s) = 0`, i.e. `Re s = -σ.re`:

* `rpow_max_le`, `norm_Ptw_cross_edge`: the horizontal-edge bound
  `‖Ptw‖ ≤ C e^{-π|v|/2}|v|^{2+η}` on the rectangle `[-σ.re, 1] × [-|v|,|v|]`, from the strip bound
  `boundD_lfunc_strip_two` (`0 ≤ Re ≤ 2`), `boundD_gamma_edge`, `dslope_diff_cpow_norm_le` and
  `norm_crossQ_le`;
* `crossGram_edge_tendsto`: the edge integrals tend to `0`;
* `crossGram_eq_Ptw_line_shifted`: the shift identity, no residue being picked up at `s = 0`
  because `X^0 = U'^0`.
-/

open DirichletCharacter Complex MeasureTheory Filter
open Work.LinnikAreas.Density4
open scoped Classical BigOperators Topology
noncomputable section

set_option maxHeartbeats 1200000

namespace Work.ZeroDensity.LogFree

/-- For `0 < X`, `-1 < r ≤ 1`: `max 1 (X^r) ≤ max 1 X + max 1 X⁻¹`. -/
lemma rpow_max_le {X r : ℝ} (hX : 0 < X) (hr1 : -1 < r) (hr2 : r ≤ 1) :
    max 1 (X ^ r) ≤ max 1 X + max 1 X⁻¹ := by
  have h1X : (0 : ℝ) ≤ max 1 X := le_trans zero_le_one (le_max_left _ _)
  have h1Xi : (0 : ℝ) ≤ max 1 X⁻¹ := le_trans zero_le_one (le_max_left _ _)
  by_cases h1 : (1 : ℝ) ≤ X
  · have hb : X ^ r ≤ X := by
      rcases le_total 0 r with h0 | h0
      · calc X ^ r ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hr2
          _ = X := Real.rpow_one X
      · exact le_trans (Real.rpow_le_one_of_one_le_of_nonpos h1 h0) h1
    exact max_le (by linarith [le_max_left (1:ℝ) X, le_max_left (1:ℝ) X⁻¹])
      (by linarith [le_max_right (1:ℝ) X])
  · have hX1 : X < 1 := lt_of_not_ge h1
    have hb : X ^ r ≤ X⁻¹ := by
      have h := (Real.rpow_le_rpow_left_iff_of_base_lt_one hX hX1).mpr (show (-1 : ℝ) ≤ r by linarith)
      rwa [Real.rpow_neg_one X] at h
    exact max_le (by linarith [le_max_left (1:ℝ) X, le_max_left (1:ℝ) X⁻¹])
      (by linarith [le_max_right (1:ℝ) X⁻¹])

/-- The horizontal-edge bound for the regularised cross kernel on the rectangle
`[-σ.re, 1] × [-|v|,|v|]`: `‖Ptw‖ ≤ C e^{-π|v|/2}|v|^{2+η}`. -/
theorem norm_Ptw_cross_edge (q : ℕ) [NeZero q] (η : ℝ) (hη : 0 < η) {W X U' : ℝ} (hW : 1 < W)
    (hX : 0 < X) (hU' : 0 < U') (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hq : 2 ≤ q)
    (σ : ℂ) (hσ0 : 0 < σ.re) (hσ1 : σ.re < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc (-σ.re) 1, ∀ v : ℝ, 1 ≤ |v| →
      ‖Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((x : ℂ) + (v : ℂ) * Complex.I)‖
        ≤ C * Real.exp (-(Real.pi / 2) * |v|) * |v| ^ (2 + η) := by
  obtain ⟨CL, hCLpos, hCL⟩ := boundD_lfunc_strip_two η hη
  obtain ⟨Cge, hCgepos, hCge⟩ := boundD_gamma_edge
  set D1 : ℝ := (|Real.log X| + |Real.log U'|)
    * (max 1 X + max 1 X⁻¹ + (max 1 U' + max 1 U'⁻¹)) with hD1def
  have hD1nn : 0 ≤ D1 := by rw [hD1def]; positivity
  set CL2 : ℝ := CL * (2 * ((q : ℝ) * (2 + |σ.im|))) ^ ((1 : ℝ) / 2 + η) with hCL2def
  have hCL2nn : 0 ≤ CL2 := by rw [hCL2def]; positivity
  refine ⟨Cge * 16 * D1 * CL2 * (2 * W) ^ 2 + 1, by positivity, ?_⟩
  intro x hx v hv
  set s : ℂ := (x : ℂ) + (v : ℂ) * Complex.I with hs
  have hsr : s.re = x := by simp [hs]
  have hsi : s.im = v := by simp [hs]
  have hsr1 : -1 < s.re := by rw [hsr]; linarith [hx.1, hσ1]
  have hsr2 : s.re ≤ 1 := by rw [hsr]; exact hx.2
  have hs0 : 0 ≤ (σ + s).re := by
    rw [Complex.add_re, hsr]
    linarith [hx.1]
  have hs2 : (σ + s).re ≤ 2 := by
    rw [Complex.add_re, hsr]
    linarith [hx.2, hσ1]
  have hsim : (σ + s).im = σ.im + v := by rw [Complex.add_im, hsi]
  -- (1) the L-function: absorb the height into `|v|`
  have hLb : ‖DirichletCharacter.LFunction ψ (σ + s)‖ ≤ CL2 * |v| ^ ((1 : ℝ) / 2 + η) := by
    have h := hCL q ψ hq hψ (σ + s).re (σ + s).im hs0 hs2
    rw [show ((σ + s).re : ℂ) + ((σ + s).im : ℂ) * Complex.I = σ + s from by
      apply Complex.ext <;> simp] at h
    rw [show 2 + |(σ + s).im| = 2 + |σ.im + v| by rw [hsim]] at h
    refine h.trans ?_
    rw [hCL2def]
    have hbase : (q : ℝ) * (2 + |σ.im + v|) ≤ 2 * ((q : ℝ) * (2 + |σ.im|)) * |v| := by
      have h1 : |σ.im + v| ≤ |σ.im| + |v| := abs_add_le _ _
      have h2 : 2 + |σ.im + v| ≤ 2 * (2 + |σ.im|) * |v| := by
        have hv1 : (1 : ℝ) ≤ |v| := hv
        nlinarith [h1, hv1, abs_nonneg σ.im, abs_nonneg v]
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      calc (q : ℝ) * (2 + |σ.im + v|) ≤ (q : ℝ) * (2 * (2 + |σ.im|) * |v|) :=
            mul_le_mul_of_nonneg_left h2 hq0
        _ = 2 * ((q : ℝ) * (2 + |σ.im|)) * |v| := by ring
    calc CL * ((q : ℝ) * (2 + |σ.im + v|)) ^ ((1 : ℝ) / 2 + η)
        ≤ CL * (2 * ((q : ℝ) * (2 + |σ.im|)) * |v|) ^ ((1 : ℝ) / 2 + η) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase (by positivity))
            hCLpos.le
      _ = CL * (2 * ((q : ℝ) * (2 + |σ.im|))) ^ ((1 : ℝ) / 2 + η)
            * |v| ^ ((1 : ℝ) / 2 + η) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          ring
  -- (2) the Γ-factor
  set e : ℝ := Real.exp (-(Real.pi / 2) * |v|) with he
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have hΓb : ‖Complex.Gamma (s + 1)‖ ≤ Cge * (1 + |v|) ^ ((3 : ℝ) / 2) * e := by
    have harg : s + 1 = (((x + 1 : ℝ)) : ℂ) + (v : ℂ) * Complex.I := by
      rw [hs]; push_cast; ring
    rw [harg]
    have h := hCge σ.re hσ0 hσ1 x hx.1 hx.2 v hv
    rwa [show Real.exp (-(Real.pi / 2 * |v|)) = e by rw [he]; congr 1; ring] at h
  have hΓ4 : (1 + |v|) ^ ((3 : ℝ) / 2) ≤ 4 * |v| ^ ((3 : ℝ) / 2) := by
    have h2 : (1 + |v|) ^ ((3 : ℝ) / 2) ≤ (2 * |v|) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) (by linarith [hv]) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
    have h3 : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 := by
      have h4 : (2 : ℝ) ^ ((3 : ℝ) / 2) ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rwa [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num1] at h4
    have h5 : 0 ≤ |v| ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (abs_nonneg v) _
    calc (1 + |v|) ^ ((3 : ℝ) / 2) ≤ 2 ^ ((3 : ℝ) / 2) * |v| ^ ((3 : ℝ) / 2) := h2
      _ ≤ 4 * |v| ^ ((3 : ℝ) / 2) := by nlinarith [h3, h5]
  have hΓb' : ‖Complex.Gamma (s + 1)‖ ≤ Cge * 4 * |v| ^ ((3 : ℝ) / 2) * e := by
    refine hΓb.trans ?_
    calc Cge * (1 + |v|) ^ ((3 : ℝ) / 2) * e ≤ Cge * (4 * |v| ^ ((3 : ℝ) / 2)) * e := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΓ4 hCgepos.le) he0
      _ = Cge * 4 * |v| ^ ((3 : ℝ) / 2) * e := by ring
  -- (3) the dslope kernel
  have hds : ‖dslope (fun u : ℂ => (X : ℂ) ^ u - (U' : ℂ) ^ u) 0 s‖ ≤ D1 := by
    have h := Work.LinnikAreas2.dslope_diff_cpow_norm_le hX hU' s
    have hXb := rpow_max_le hX hsr1 hsr2
    have hUb := rpow_max_le hU' hsr1 hsr2
    rw [hD1def]
    have hlogX : 0 ≤ |Real.log X| := abs_nonneg _
    have hlogU : 0 ≤ |Real.log U'| := abs_nonneg _
    refine h.trans ?_
    calc |Real.log X| * max 1 (X ^ s.re) + |Real.log U'| * max 1 (U' ^ s.re)
        ≤ |Real.log X| * (max 1 X + max 1 X⁻¹) + |Real.log U'| * (max 1 U' + max 1 U'⁻¹) :=
          add_le_add (mul_le_mul_of_nonneg_left hXb hlogX)
            (mul_le_mul_of_nonneg_left hUb hlogU)
      _ ≤ (|Real.log X| + |Real.log U'|) * (max 1 X + max 1 X⁻¹ + (max 1 U' + max 1 U'⁻¹)) := by
          have h1 : 0 ≤ max 1 X + max 1 X⁻¹ := by positivity
          have h2 : 0 ≤ max 1 U' + max 1 U'⁻¹ := by positivity
          nlinarith [hlogX, hlogU, h1, h2]
  -- (4) the lcm-weight
  have hlcm : ‖lcmF q 1 W W ψ (σ + s)‖ ≤ (2 * W) ^ 2 := by
    rw [lcmF_one_eq_crossQ q hW ψ (σ + s)]
    exact norm_crossQ_le q hW ψ hs0
  rw [show Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ s
      = Complex.Gamma (s + 1) * dslope (fun u : ℂ => (X : ℂ) ^ u - (U' : ℂ) ^ u) 0 s
        * DirichletCharacter.LFunction ψ (σ + s) * lcmF q 1 W W ψ (σ + s) from rfl]
  rw [norm_mul, norm_mul, norm_mul]
  -- combine
  have hpow : |v| ^ ((3 : ℝ) / 2) * |v| ^ ((1 : ℝ) / 2 + η) = |v| ^ (2 + η) := by
    rw [← Real.rpow_add (by linarith [hv] : (0 : ℝ) < |v|)]
    ring_nf
  have hstep1 : ‖Complex.Gamma (s + 1)‖ * ‖dslope (fun u : ℂ => (X : ℂ) ^ u - (U' : ℂ) ^ u) 0 s‖
      ≤ (Cge * 4 * |v| ^ ((3 : ℝ) / 2) * e) * D1 :=
    mul_le_mul hΓb' hds (norm_nonneg _) (by positivity)
  have hstep2 : ‖Complex.Gamma (s + 1)‖ * ‖dslope (fun u : ℂ => (X : ℂ) ^ u - (U' : ℂ) ^ u) 0 s‖
        * ‖DirichletCharacter.LFunction ψ (σ + s)‖
      ≤ (Cge * 4 * |v| ^ ((3 : ℝ) / 2) * e) * D1 * (CL2 * |v| ^ ((1 : ℝ) / 2 + η)) :=
    mul_le_mul hstep1 hLb (norm_nonneg _) (by positivity)
  have hstep3 : ‖Complex.Gamma (s + 1)‖ * ‖dslope (fun u : ℂ => (X : ℂ) ^ u - (U' : ℂ) ^ u) 0 s‖
        * ‖DirichletCharacter.LFunction ψ (σ + s)‖ * ‖lcmF q 1 W W ψ (σ + s)‖
      ≤ (Cge * 4 * |v| ^ ((3 : ℝ) / 2) * e) * D1 * (CL2 * |v| ^ ((1 : ℝ) / 2 + η)) * (2 * W) ^ 2 :=
    mul_le_mul hstep2 hlcm (norm_nonneg _) (by positivity)
  refine hstep3.trans ?_
  have hfinal : (Cge * 4 * |v| ^ ((3 : ℝ) / 2) * e) * D1 * (CL2 * |v| ^ ((1 : ℝ) / 2 + η)) * (2 * W) ^ 2
      ≤ (Cge * 16 * D1 * CL2 * (2 * W) ^ 2 + 1) * (e * |v| ^ (2 + η)) := by
    rw [← hpow]
    have hP0 : 0 ≤ Cge * D1 * CL2 * (2 * W) ^ 2 := by positivity
    have hY0 : 0 ≤ |v| ^ ((3 : ℝ) / 2) * |v| ^ ((1 : ℝ) / 2 + η) := by positivity
    have hPYe : 0 ≤ Cge * D1 * CL2 * (2 * W) ^ 2 * (|v| ^ ((3 : ℝ) / 2)
      * |v| ^ ((1 : ℝ) / 2 + η)) * e := by positivity
    nlinarith [hP0, hY0, he0, hPYe]
  exact hfinal.trans (le_of_eq (by ring))

/-- The horizontal-edge integrals of the cross contour shift tend to `0`. -/
theorem crossGram_edge_tendsto (q : ℕ) [NeZero q] (hq : 2 ≤ q) {W X U' : ℝ} (hW : 1 < W)
    (hX : 0 < X) (hU' : 0 < U') (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (σ : ℂ)
    (hσ0 : 0 < σ.re) (hσ1 : σ.re < 1) :
    (Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in (-σ.re)..1,
        Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in (-σ.re)..1,
        Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0)) := by
  obtain ⟨C, hCpos, hbd⟩ := norm_Ptw_cross_edge q 1 one_pos hW hX hU' ψ hψ hq σ hσ0 hσ1
  have hle : -σ.re ≤ 1 := by linarith
  have hpt : ∀ x ∈ Set.Icc (-σ.re) 1, ∀ T : ℝ, 1 ≤ T →
      ‖Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((x : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ C * Real.exp (-(Real.pi / 2) * T) * T ^ (2 + (1 : ℝ)) := by
    intro x hx T hT
    have h := hbd x hx T (by rw [abs_of_nonneg (by linarith)]; exact hT)
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ T)] at h
  have hpt' : ∀ x ∈ Set.Icc (-σ.re) 1, ∀ T : ℝ, 1 ≤ T →
      ‖Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * Complex.I))‖
        ≤ C * Real.exp (-(Real.pi / 2) * T) * T ^ (2 + (1 : ℝ)) := by
    intro x hx T hT
    have hconj : (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * Complex.I) = (x : ℂ) - (T : ℂ) * Complex.I := by
      rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hconj]
    have h := hbd x hx (-T) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hT)
    rw [abs_neg, abs_of_nonneg (by linarith : (0:ℝ) ≤ T)] at h
    have harg : (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I = (x : ℂ) - (T : ℂ) * Complex.I := by
      push_cast; ring
    rwa [harg] at h
  constructor
  · exact Work.LinnikAreas.Density4.rect_edge_tendsto_zero
      (Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ) (-σ.re) 1 (2 + (1 : ℝ)) C hle hCpos hpt
  · have h := Work.LinnikAreas.Density4.rect_edge_tendsto_zero
      (fun z => Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((starRingEnd ℂ) z))
      (-σ.re) 1 (2 + (1 : ℝ)) C hle hCpos hpt'
    have hfun : (fun R : ℝ => ∫ x : ℝ in (-σ.re)..1,
          (fun z => Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((starRingEnd ℂ) z))
            ((x : ℂ) + (R : ℂ) * Complex.I))
        = (fun R : ℝ => ∫ x : ℝ in (-σ.re)..1,
          Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((x : ℂ) - (R : ℂ) * Complex.I)) := by
      funext R
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rwa [hfun] at h

/-- The contour shift: the `Re s = 1` integral of the cross kernel equals its
`Re s = -σ.re` integral (the two vertical sides of the rectangle `[-σ.re,1] × [-R,R]`, whose
horizontal edges vanish and whose interior contains no pole, since `X^0 = U'^0` cancels the two
`Γ`-poles at the origin). -/
theorem crossGram_eq_Ptw_line_shifted (q : ℕ) [NeZero q] {W X U' : ℝ} (hq : 2 ≤ q) (hW : 1 < W)
    (hX : 0 < X) (hU' : 0 < U') (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (σ : ℂ)
    (hσ0 : 0 < σ.re) (hσ1 : σ.re < 1)
    (hInt : Integrable (fun t : ℝ =>
      Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
    (htop : Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in (-σ.re)..1,
        Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((x : ℂ) + (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0))
    (hbot : Filter.Tendsto (fun R : ℝ => ∫ x : ℝ in (-σ.re)..1,
        Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((x : ℂ) - (R : ℂ) * Complex.I))
      Filter.atTop (nhds 0)) :
    crossGram q W X U' ψ σ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ,
          Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  have hle : -σ.re ≤ 1 := by linarith
  have hline := Work.LinnikAreas2.Ssm_sub_eq_Ptw_line q hq 1 W W X U' ψ σ one_pos
    (le_of_lt hW) (le_of_lt hW) (le_of_lt hW) hX hU' hψ hσ0
  rw [crossGram, hline]
  congr 1
  have hIq : Integrable (fun t : ℝ =>
      Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ ((1 : ℂ) + (t : ℂ) * Complex.I)) :=
    Work.LinnikAreas2.integrable_Ptw_line_one (X := X) (Y := U') q hq one_pos (le_of_lt hW)
      (le_of_lt hW) (le_of_lt hW) hX hU' ψ hψ σ hσ0
  have hFd : ∀ R : ℝ, DifferentiableOn ℂ (Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ)
      (Set.uIcc (-σ.re) 1 ×ℂ Set.uIcc (-R) R) := by
    intro R
    refine (Work.LinnikAreas2.differentiableOn_Ptw q 1 W W X U' ψ hψ hX hU' σ).mono ?_
    rintro s ⟨hs1, _⟩
    simp only [Set.mem_setOf_eq]
    rw [Set.uIcc_of_le hle] at hs1
    linarith [hs1.1]
  exact Commons.Analysis.Complex.vertical_contour_shift (Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ)
    (-σ.re) 1 hle hFd hInt hIq htop hbot

/-- Integrability of the cross kernel on the shifted line `Re s = -σ.re`, from the pointwise bound
and the `Γ`-integral. -/
theorem integrable_Ptw_cross_shifted (q : ℕ) [NeZero q] {W X U' Cb r δ : ℝ} (hW : 1 < W)
    (hX : 0 < X) (hU' : 0 < U') (hCb : 0 < Cb) (hr : 0 ≤ r) (hδ : 0 < δ)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (σ : ℂ) (hσ0 : 0 < σ.re) (hσ1 : σ.re < 1)
    (hσδ : δ ≤ σ.re)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction ψ (σ + (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|) ^ r) :
    Integrable (fun t : ℝ =>
      Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hc1 : -1 < -σ.re := by linarith
  have hc2 : -σ.re ≤ -δ := by linarith
  have hbd := norm_Ptw_cross_line q hW hX hU' hCb hr hσ0 hLbd
  have hΓint : Integrable (fun t : ℝ =>
      ‖Complex.Gamma (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r) :=
    integrable_gamma_shifted r hr hδ (-σ.re) hc1 hc2
  have hmaj : Integrable (fun t : ℝ => (Cb * (X ^ (-σ.re) + U' ^ (-σ.re)) * (2 * W) ^ 2)
      * (‖Complex.Gamma (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r)) :=
    hΓint.const_mul _
  refine hmaj.mono' ?_ ?_
  · have hcont : Continuous (fun t : ℝ =>
        Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hmem : (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) ∈ {s : ℂ | -1 < s.re} := by
        simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero]
        linarith
      have hd : DifferentiableAt ℂ (Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ)
          (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) :=
        (Work.LinnikAreas2.differentiableOn_Ptw q 1 W W X U' ψ hψ hX hU' σ).differentiableAt
          ((isOpen_lt continuous_const continuous_re).mem_nhds hmem)
      have hg : ContinuousAt (fun t : ℝ => ((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) t := by
        fun_prop
      exact hd.continuousAt.comp (f := fun t : ℝ => ((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I) hg
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    have h := hbd t
    refine h.trans (le_of_eq ?_)
    ring

end Work.ZeroDensity.LogFree
