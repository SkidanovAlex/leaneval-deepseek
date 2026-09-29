import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.lyap_usc
import Submission.Work.TMComp.Kotani.EllDerivDefs
import Submission.Work.TMComp.RedC8.ell_le_lyap
import Submission.Work.TMComp.RedC8.EllBound.Defs
import Submission.Work.TMComp.RedC8.mobius_re_im
import Submission.Work.TMComp.RedC8.harc_harmonic_and_nonneg
import Submission.Work.TMComp.RedC8.harc_continuousAt_arc
import Submission.Work.TMComp.RedC8.circleAverage_maxPrinciple_limsup
import Submission.Work.TMComp.RedC8.ell_harmonicOnNhd
import Submission.Work.TMComp.RedC8.ell_tendsto_zero_near_real
import Submission.Work.TMComp.LocCantor.excess_seq
import Submission.Work.TMComp.LocCantor.K2_integral_of_excess
import Submission.Work.TMComp.LocCantor.jump_tendsto_ae
import Submission.Work.TMComp.LocCantor.C8_defect

/-!
# The a.e. phase jump of `cayley ∘ Ψ` tends to `0` along a vanishing sequence

This file closes the (L8)–(L11) gap of the Kotani continuation
(`Submission/Work/TMComp/RedC8/NOTES_route.md`), in a self-contained way:

* `arg_vertical_clean`, `harc_arc_value`, `harc_axis_value`: the two values of the
  harmonic-measure barrier `harc` which the (H)-argument needs (the arc value `M` and the
  value `(4M/π) arctan(ε/R)` on the vertical diameter), together with the trigonometric
  identity `arg ((R+iε)/(R-iε)) = 2 arctan(ε/R)` underlying the second one.  These are proved
  here from scratch so that the file does not depend on `RedC8/arg_vertical.lean`.
* `ell_le_M_of_norm_le`: the crude bound `ℓ(z) ≤ (1/2) log((B + 2|λ|)² + 2)` for `‖z‖ ≤ B`,
  `0 < Im z` (local copy, to avoid depending on the similarly-named lemma of
  `RedC8/ell_le_mul_of_lyap_eq_zero.lean`).
* `ell_le_mul_Icc`: **(H)** — if the Lyapunov exponent vanishes on `(a,b)`, then on every closed
  subinterval `[a',b'] ⊂ (a,b)` there is a *uniform* `C > 0` with `ℓ(E+iε) ≤ C ε` for all
  `E ∈ [a',b']`, `0 < ε ≤ 1`.  The proof is the harmonic-measure barrier argument of
  `RedC8/ell_le_mul_of_lyap_eq_zero.lean`, redone with the uniform radius
  `R = min (a'-a) (b-b')/2` and the uniform arc bound `M = (1/2) log((Mb + R + 2|λ|)² + 2)`,
  `Mb = max |a'| |b'|`, so that `C` does not depend on `E`.
* `ae_jump_of_lyap_eq_zero`: (H) plus the `LocCantor` chain
  (`excess_seq` → `K2_integral_of_excess` → `jump_tendsto_ae`, packaged as
  `LocCantor.jump_tendsto_ae_of_H`) gives, for a.e. phase `y ∈ (0,1]`, a sequence `ε_j ↓ 0`
  with `∫_{a'}^{b'} ‖cayley (Ψ(E+iε_j,y)) - cayley (Ψ(E-iε_j,y))‖ dE → 0`, arranged so that
  `0 < ε_j < 1` for every `j` (discard a finite initial segment).
-/

open MeasureTheory Filter Topology Set
open scoped Topology

noncomputable section

namespace Work.TMComp.RedC8

set_option maxHeartbeats 1000000

/-! ## A uniform bound for `ℓ` in terms of `‖z‖` -/

/-- `arctan x ≤ x` for `x ≥ 0`. -/
private lemma arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hf : ∀ t ∈ Set.Icc (0:ℝ) x, HasDerivWithinAt Real.arctan (1/(1+t^2)) (Set.Icc 0 x) t :=
    fun t _ => (Real.hasDerivAt_arctan t).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Ico (0:ℝ) x, ‖(1:ℝ)/(1+t^2)‖ ≤ 1 := by
    intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by positivity)]
    nlinarith [sq_nonneg t]
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := Real.arctan)
    (f' := fun t => (1:ℝ)/(1+t^2)) (C := 1) (a := (0:ℝ)) (b := x) hf hb x ⟨hx, le_rfl⟩
  simp only [Real.arctan_zero, sub_zero, Real.norm_eq_abs] at h
  rw [abs_of_nonneg (Real.arctan_nonneg.mpr hx), one_mul] at h
  exact h

/-- The Frobenius norm of the transfer matrix, in terms of the potential. -/
private lemma frob_tmC_eq (lam : ℝ) (z : ℂ) (x : ℝ) :
    Work.TMContract.frob (Work.TMContract.tmC lam z x)
      = Real.sqrt (‖z - ((Work.TMComp.Kotani.pot lam x : ℝ) : ℂ)‖ ^ 2 + 2) := by
  rw [Work.TMContract.frob, Work.TMContract.tmC]
  simp [Work.TMComp.Kotani.pot, Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val']
  congr 1
  ring

private lemma frob_tmC_pos (lam : ℝ) (z : ℂ) (x : ℝ) :
    0 < Work.TMContract.frob (Work.TMContract.tmC lam z x) := by
  rw [frob_tmC_eq]
  apply Real.sqrt_pos.mpr
  positivity

private lemma frob_tmC_le' (lam : ℝ) (z : ℂ) (x B : ℝ) (hB : ‖z‖ ≤ B) :
    Work.TMContract.frob (Work.TMContract.tmC lam z x)
      ≤ Real.sqrt ((B + 2 * |lam|) ^ 2 + 2) := by
  rw [frob_tmC_eq]
  apply Real.sqrt_le_sqrt
  have hp : ‖((Work.TMComp.Kotani.pot lam x : ℝ) : ℂ)‖ ≤ 2 * |lam| := by
    rw [show ‖((Work.TMComp.Kotani.pot lam x : ℝ) : ℂ)‖
        = |Work.TMComp.Kotani.pot lam x| from RCLike.norm_ofReal _]
    exact Work.TMComp.Kotani.pot_abs_le lam x
  have h1 : ‖z - ((Work.TMComp.Kotani.pot lam x : ℝ) : ℂ)‖ ≤ B + 2 * |lam| :=
    le_trans (norm_sub_le _ _) (add_le_add hB hp)
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) h1 2]

private lemma iterC_one (α lam : ℝ) (z : ℂ) (x : ℝ) :
    Work.TMContract.iterC α lam z 1 x = Work.TMContract.tmC lam z x := by
  simp only [Work.TMContract.iterC]
  simp

private lemma lyapAvg_zero_eq (α lam : ℝ) (z : ℂ) :
    Work.TMComp.Kotani.lyapAvg α lam 0 z
      = ∫ x in (0 : ℝ)..1,
          Real.log (Work.TMContract.frob (Work.TMContract.tmC lam z x)) := by
  rw [Work.TMComp.Kotani.lyapAvg]
  simp only [Nat.cast_zero, zero_add]
  rw [div_one]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [iterC_one]

private lemma continuous_log_frob_tmC (lam : ℝ) (z : ℂ) :
    Continuous (fun x : ℝ => Real.log (Work.TMContract.frob (Work.TMContract.tmC lam z x))) := by
  have hpot : Continuous (fun x : ℝ => Work.TMComp.Kotani.pot lam x) := by
    unfold Work.TMComp.Kotani.pot; fun_prop
  have hnorm : Continuous (fun x : ℝ => ‖z - ((Work.TMComp.Kotani.pot lam x : ℝ) : ℂ)‖) :=
    Continuous.norm (continuous_const.sub (Complex.continuous_ofReal.comp hpot))
  have hfrob : ∀ x : ℝ, Work.TMContract.frob (Work.TMContract.tmC lam z x)
      = Real.sqrt (‖z - ((Work.TMComp.Kotani.pot lam x : ℝ) : ℂ)‖ ^ 2 + 2) :=
    fun x => frob_tmC_eq lam z x
  simp only [hfrob]
  apply Continuous.log
  · exact Real.continuous_sqrt.comp ((hnorm.pow 2).add continuous_const)
  · intro x; positivity

private lemma lyapAvg_zero_le (α lam : ℝ) (z : ℂ) (B : ℝ) (hB : ‖z‖ ≤ B) :
    Work.TMComp.Kotani.lyapAvg α lam 0 z
      ≤ (1 / 2) * Real.log ((B + 2 * |lam|) ^ 2 + 2) := by
  rw [lyapAvg_zero_eq]
  set c : ℝ := (1 / 2) * Real.log ((B + 2 * |lam|) ^ 2 + 2) with hc
  have hX : 0 ≤ (B + 2 * |lam|) ^ 2 + 2 := by positivity
  have hpt : ∀ x ∈ Set.Icc (0:ℝ) 1,
      Real.log (Work.TMContract.frob (Work.TMContract.tmC lam z x)) ≤ c := by
    intro x _
    have h1 := frob_tmC_le' lam z x B hB
    have h2 : Real.log (Work.TMContract.frob (Work.TMContract.tmC lam z x))
        ≤ Real.log (Real.sqrt ((B + 2 * |lam|) ^ 2 + 2)) :=
      Real.log_le_log (frob_tmC_pos lam z x) h1
    rw [Real.log_sqrt hX] at h2
    rw [hc]
    linarith
  calc (∫ x in (0 : ℝ)..1, Real.log (Work.TMContract.frob (Work.TMContract.tmC lam z x)))
      ≤ ∫ x in (0 : ℝ)..1, c :=
        intervalIntegral.integral_mono_on (by norm_num)
          ((continuous_log_frob_tmC lam z).intervalIntegrable 0 1) intervalIntegrable_const hpt
    _ = c := by rw [intervalIntegral.integral_const]; simp

/-- `ℓ z ≤ (1/2) log((B + 2|λ|)² + 2)` when `0 < Im z` and `‖z‖ ≤ B`. -/
private lemma ell_le_M_of_norm_le (α lam : ℝ) (z : ℂ) (hzim : 0 < z.im) (B : ℝ) (hB : ‖z‖ ≤ B) :
    Work.TMComp.Kotani.ell α lam z ≤ (1 / 2) * Real.log ((B + 2 * |lam|) ^ 2 + 2) := by
  calc Work.TMComp.Kotani.ell α lam z ≤ Work.TMContract.lyap α lam z :=
        Work.TMComp.RedC8.ell_le_lyap α lam z hzim
    _ ≤ Work.TMComp.Kotani.lyapAvg α lam 0 z := by
        rw [Work.TMComp.Kotani.lyap_eq_iInf]
        exact ciInf_le (Work.TMComp.Kotani.lyapAvg_bddBelow α lam z) 0
    _ ≤ _ := lyapAvg_zero_le α lam z B hB

/-! ## The argument of `(R + iε)/(R - iε)` -/

/-- `((R : ℂ) + ε i) / ((R : ℂ) - ε i)` has argument `2 arctan (ε/R)` for `0 < ε < R`.
This is the statement of `RedC8/arg_vertical.lean`, proved here independently of it: the point
`Q` lies in the open first quadrant, its tangent is `2 R ε/(R²-ε²) = tan (2 arctan (ε/R))`, and
`tan` is injective on `(-π/2, π/2)`. -/
private lemma arg_vertical_clean (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R) :
    (((R : ℂ) + (ε : ℂ) * Complex.I) / ((R : ℂ) - (ε : ℂ) * Complex.I)).arg
      = 2 * Real.arctan (ε / R) := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hsin : Real.sin (2 * Real.arctan (ε / R)) = 2 * R * ε / (R ^ 2 + ε ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hA0 : √(1 + (ε/R)^2) ≠ 0 := by positivity
    field_simp
    have hBB : √((R ^ 2 + ε ^ 2) / R ^ 2)^2 = (R ^ 2 + ε ^ 2)/R^2 :=
      Real.sq_sqrt (by positivity)
    rw [hBB]
    field_simp
  have hcos : Real.cos (2 * Real.arctan (ε / R)) = (R ^ 2 - ε ^ 2) / (R ^ 2 + ε ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow]
    have hA0 : √(1 + (ε/R)^2) ≠ 0 := by positivity
    field_simp
    have hBB : √((R ^ 2 + ε ^ 2) / R ^ 2)^2 = (R ^ 2 + ε ^ 2)/R^2 :=
      Real.sq_sqrt (by positivity)
    rw [hBB]
    field_simp
    ring
  have hζ : (R : ℂ) - (ε : ℂ) * Complex.I ≠ 0 := by
    have him : ((R : ℂ) - (ε : ℂ) * Complex.I).im = -ε := by simp
    intro hh
    rw [hh] at him
    simp only [Complex.zero_im] at him
    linarith
  obtain ⟨hQre, hQim⟩ := mobius_re_im R ((ε : ℂ) * Complex.I) hζ
  have hnormζ : ‖((ε : ℂ) * Complex.I)‖ = ε := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos hε]
  have hnormd : ‖(R : ℂ) - (ε : ℂ) * Complex.I‖ ^ 2 = R ^ 2 + ε ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, Complex.sub_im, zero_sub,
      Complex.mul_im]
    ring
  have hQre' : (((R : ℂ) + (ε : ℂ) * Complex.I) / ((R : ℂ) - (ε : ℂ) * Complex.I)).re
      = (R ^ 2 - ε ^ 2) / (R ^ 2 + ε ^ 2) := by
    rw [hQre, hnormζ, hnormd]
  have hQim' : (((R : ℂ) + (ε : ℂ) * Complex.I) / ((R : ℂ) - (ε : ℂ) * Complex.I)).im
      = 2 * R * ε / (R ^ 2 + ε ^ 2) := by
    rw [hQim, hnormd]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero]
  have hpos : 0 < R ^ 2 - ε ^ 2 := by nlinarith
  have hre : 0 < (((R : ℂ) + (ε : ℂ) * Complex.I) / ((R : ℂ) - (ε : ℂ) * Complex.I)).re := by
    rw [hQre']
    exact div_pos hpos (by positivity)
  have hφmem : (((R : ℂ) + (ε : ℂ) * Complex.I) / ((R : ℂ) - (ε : ℂ) * Complex.I)).arg
      ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := (Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hre)
    rwa [abs_lt] at h
  have hψmem : 2 * Real.arctan (ε / R) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h0 : 0 < Real.arctan (ε / R) := Real.arctan_pos.mpr (by positivity)
    have h1 : Real.arctan (ε / R) < Real.pi / 4 := by
      have h2 := Real.arctan_lt_arctan_iff.mpr ((div_lt_one hR).mpr hεR)
      rwa [Real.arctan_one] at h2
    exact ⟨by linarith, by linarith⟩
  have htan : Real.tan (((R : ℂ) + (ε : ℂ) * Complex.I) / ((R : ℂ) - (ε : ℂ) * Complex.I)).arg
      = Real.tan (2 * Real.arctan (ε / R)) := by
    rw [Complex.tan_arg, hQim', hQre', Real.tan_eq_sin_div_cos, hsin, hcos]
  exact Real.strictMonoOn_tan.injOn hφmem hψmem htan

/-! ## The values of the barrier `harc` on the arc and on the diameter -/

/-- The barrier `harc E₀ R M` equals `M` on the upper arc `{‖z - E₀‖ = R, 0 < Im z}`. -/
private theorem harc_arc_value (E₀ R M : ℝ) (hR : 0 < R) :
    ∀ z : ℂ, ‖z - (E₀ : ℂ)‖ = R → 0 < z.im → harc E₀ R M z = M := by
  intro z hz hzim
  have hne : (R : ℂ) - (z - (E₀ : ℂ)) ≠ 0 := by
    intro h
    have hzero : ((R : ℂ) - (z - (E₀ : ℂ))).im = 0 := by rw [h]; simp
    simp [Complex.sub_im, Complex.ofReal_im] at hzero
    linarith
  obtain ⟨hre, himq⟩ := mobius_re_im R (z - (E₀ : ℂ)) hne
  have hargq : (((R : ℂ) + (z - (E₀ : ℂ))) / ((R : ℂ) - (z - (E₀ : ℂ)))).arg
      = Real.pi / 2 := by
    rw [Complex.arg_eq_pi_div_two_iff]
    refine ⟨?_, ?_⟩
    · rw [hre]
      simp [hz]
    · rw [himq]
      refine div_pos ?_ ?_
      · have hz' : (z - (E₀ : ℂ)).im = z.im := by simp
        rw [hz']
        positivity
      · exact sq_pos_of_pos (by rw [norm_pos_iff]; exact hne)
  rw [harc, Complex.log_im, hargq]
  field_simp

/-- The barrier `harc E₀ R M` at the vertical point `E₀ + iε` equals
`(4M/π) arctan (ε/R)`. -/
private theorem harc_axis_value (E₀ R M : ℝ) (hR : 0 < R) :
    ∀ ε : ℝ, 0 < ε → ε < R →
      harc E₀ R M ((E₀ : ℂ) + (ε : ℂ) * Complex.I)
        = (4 * M / Real.pi) * Real.arctan (ε / R) := by
  intro ε hε0 hεR
  have hζ : ((E₀ : ℂ) + (ε : ℂ) * Complex.I) - (E₀ : ℂ) = (ε : ℂ) * Complex.I := by ring
  rw [harc, Complex.log_im, hζ, arg_vertical_clean R ε hR hε0 hεR]
  ring

/-! ## (H): the uniform linear bound on a closed subinterval -/

/-- **(H) with a uniform constant on a closed subinterval.**  If the Lyapunov exponent vanishes
on `(a,b)`, then on every closed subinterval `[a',b'] ⊂ (a,b)` the averaged log-modulus `ℓ` of
the `m`-function satisfies `ℓ(E+iε) ≤ C ε` with `C` independent of `E ∈ [a',b']` and
`ε ∈ (0,1]`.

This is `RedC8/ell_le_mul_of_lyap_eq_zero.lean` redone with a *uniform* radius and arc bound:
`R = min (a'-a) (b-b')/2`, `M = (1/2) log ((Mb + R + 2|λ|)² + 2)`, `Mb = max |a'| |b'|`.  The
input is the upper semicontinuity of the Lyapunov exponent (`ell_tendsto_zero_near_real`), the
harmonicity of `ℓ` on `ℍ`, and the maximum principle with the barrier `harc`
(`circleAverage_maxPrinciple_limsup`). -/
private theorem ell_le_mul_Icc (α lam a b a' b' : ℝ) (ha : a < a') (hb : b' < b) (hab' : a' < b')
    (hL : ∀ E ∈ Set.Ioo a b, Work.TMContract.lyap α lam (E : ℂ) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ E ∈ Set.Icc a' b', ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) ≤ C * ε := by
  set R : ℝ := min (a' - a) (b - b') / 2 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    have h1 : 0 < a' - a := by linarith
    have h2 : 0 < b - b' := by linarith
    have h3 : 0 < min (a' - a) (b - b') := lt_min h1 h2
    linarith
  have hRa : a < a' - R := by
    have h : min (a' - a) (b - b') ≤ a' - a := min_le_left _ _
    rw [hRdef]; linarith
  have hRb : b' + R < b := by
    have h : min (a' - a) (b - b') ≤ b - b' := min_le_right _ _
    rw [hRdef]; linarith
  set Mb : ℝ := max |a'| |b'| with hMbdef
  have hMb0 : 0 ≤ Mb := le_trans (abs_nonneg a') (le_max_left _ _)
  set Marc : ℝ := (1 / 2) * Real.log ((Mb + R + 2 * |lam|) ^ 2 + 2) with hMarcdef
  have hMarcnn : 0 ≤ Marc := by
    rw [hMarcdef]
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    nlinarith [sq_nonneg (Mb + R + 2 * |lam|)]
  set Mbig : ℝ := (1 / 2) * Real.log ((Mb + 1 + 2 * |lam|) ^ 2 + 2) with hMbigdef
  have hMbignn : 0 ≤ Mbig := by
    rw [hMbigdef]
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    nlinarith [sq_nonneg (Mb + 1 + 2 * |lam|)]
  refine ⟨max 1 (max (4 * Marc / (Real.pi * R)) (Mbig / R)),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro E hE ε hε hε1
  have hEa' : a' ≤ E := hE.1
  have hEb' : E ≤ b' := hE.2
  have hEabs : |E| ≤ Mb := by
    rw [abs_le]
    constructor
    · have h2 : |a'| ≤ Mb := by rw [hMbdef]; exact le_max_left _ _
      have h4 : a' ≤ |a'| := le_abs_self a'
      have h5 : -a' ≤ |a'| := neg_le_abs a'
      linarith
    · have h2 : |b'| ≤ Mb := by rw [hMbdef]; exact le_max_right _ _
      have h4 : b' ≤ |b'| := le_abs_self b'
      linarith
  have hRmem : Set.Icc (E - R) (E + R) ⊆ Set.Ioo a b := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1, hRa], by linarith [hx.2, hRb]⟩
  have hnormE : ‖(E : ℂ)‖ = |E| := by simp
  have harcin : ∀ z : ℂ, ‖z - (E : ℂ)‖ = R → 0 < z.im →
      Work.TMComp.Kotani.ell α lam z ≤ Marc := by
    intro z hz hzim
    have hB : ‖z‖ ≤ Mb + R := by
      calc ‖z‖ = ‖(z - (E : ℂ)) + (E : ℂ)‖ := by ring_nf
        _ ≤ ‖z - (E : ℂ)‖ + ‖(E : ℂ)‖ := norm_add_le _ _
        _ = R + |E| := by rw [hz, hnormE]
        _ ≤ R + Mb := by linarith
        _ = Mb + R := by ring
    have h1 := ell_le_M_of_norm_le α lam z hzim (Mb + R) hB
    rw [hMarcdef]
    exact h1
  have hharm := ell_harmonicOnNhd α lam
  obtain ⟨hharcharm, harcnonneg⟩ := harc_harmonic_and_nonneg E R Marc hMarcnn
  have harcarc := harc_arc_value E R Marc hRpos
  have harcaxis := harc_axis_value E R Marc hRpos
  set Ω : Set ℂ := {z : ℂ | 0 < z.im ∧ ‖z - (E : ℂ)‖ < R} with hΩdef
  have hballset : Metric.ball (E : ℂ) R = {z : ℂ | ‖z - (E : ℂ)‖ < R} := by
    ext z; simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
  set V : ℂ → ℝ := fun z => Work.TMComp.Kotani.ell α lam z - harc E R Marc z with hVdef
  have hΩopen : IsOpen Ω := by
    rw [hΩdef, Set.ofPred_and, ← hballset]
    exact (isOpen_lt continuous_const Complex.continuous_im).inter Metric.isOpen_ball
  have hΩbdd : Bornology.IsBounded Ω := by
    rw [hΩdef, Set.ofPred_and, ← hballset]
    exact Metric.isBounded_ball.subset (fun z hz => hz.2)
  have hΩpre : IsPreconnected Ω := by
    rw [hΩdef, Set.ofPred_and, ← hballset]
    apply Convex.isPreconnected
    have h1 : Convex ℝ ({z : ℂ | 0 < z.im}) := by
      have he : ({z : ℂ | 0 < z.im}) = Complex.imCLM ⁻¹' (Set.Ioi (0:ℝ)) := by
        ext z; simp [Complex.imCLM_apply]
      rw [he]
      exact (convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap
    exact h1.inter (convex_ball (E : ℂ) R)
  have hfrontier : ∀ ζ ∈ frontier Ω,
      (0 < ζ.im ∧ ‖ζ - (E : ℂ)‖ = R) ∨ (ζ.im = 0 ∧ ‖ζ - (E : ℂ)‖ ≤ R) := by
    intro ζ hζ
    have hcl : ζ ∈ closure Ω := frontier_subset_closure hζ
    have hnot : ζ ∉ Ω := by
      have h := hζ
      rw [hΩopen.frontier_eq] at h
      exact h.2
    have him0 : 0 ≤ ζ.im :=
      closure_minimal (fun z hz => le_of_lt hz.1)
        (isClosed_le continuous_const Complex.continuous_im) hcl
    have hdiam : ‖ζ - (E : ℂ)‖ ≤ R := by
      have h1 : closure Ω ⊆ Metric.closedBall (E : ℂ) R :=
        closure_minimal
          (fun z hz => by rw [Metric.mem_closedBall, dist_eq_norm]; exact le_of_lt hz.2)
          Metric.isClosed_closedBall
      have h2 := h1 hcl
      rwa [Metric.mem_closedBall, dist_eq_norm] at h2
    rcases lt_or_eq_of_le him0 with hlt | heq
    · exact Or.inl ⟨hlt, le_antisymm hdiam (by
        by_contra hcon
        exact hnot ⟨hlt, not_le.mp hcon⟩)⟩
    · exact Or.inr ⟨heq.symm, hdiam⟩
  have hVc : ContinuousOn V Ω := by
    have h1 : ContinuousOn (fun w : ℂ => Work.TMComp.Kotani.ell α lam w) Ω :=
      (hharm.mono (fun z hz => hz.1)).continuousOn
    have h2 : ContinuousOn (harc E R Marc) Ω :=
      (hharcharm.mono (fun z hz => hz)).continuousOn
    exact h1.sub h2
  have hVmean : ∀ z ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall z r ⊆ Ω →
      V z ≤ Real.circleAverage V z r := by
    intro z hz r hr hball
    have hsub1 : Metric.closedBall z r ⊆ {w : ℂ | 0 < w.im} := fun w hw => (hball hw).1
    have hsub2 : Metric.closedBall z r ⊆ {w : ℂ | 0 < w.im ∧ ‖w - (E : ℂ)‖ < R} :=
      fun w hw => hball hw
    have h1 : Real.circleAverage (fun w => Work.TMComp.Kotani.ell α lam w) z r
        = Work.TMComp.Kotani.ell α lam z :=
      (hharm.mono (by rw [abs_of_pos hr]; exact hsub1)).circleAverage_eq
    have h2 : Real.circleAverage (harc E R Marc) z r = harc E R Marc z :=
      (hharcharm.mono (by rw [abs_of_pos hr]; exact hsub2)).circleAverage_eq
    have hsp1 : Metric.sphere z |r| ⊆ {w : ℂ | 0 < w.im} := by
      rw [abs_of_pos hr]
      exact fun w hw => (hball (Metric.sphere_subset_closedBall hw)).1
    have hsp2 : Metric.sphere z |r| ⊆ {w : ℂ | 0 < w.im ∧ ‖w - (E : ℂ)‖ < R} := by
      rw [abs_of_pos hr]
      exact fun w hw => hball (Metric.sphere_subset_closedBall hw)
    have hci1 : CircleIntegrable (fun w => Work.TMComp.Kotani.ell α lam w) z r :=
      ContinuousOn.circleIntegrable' (hharm.mono hsp1).continuousOn
    have hci2 : CircleIntegrable (harc E R Marc) z r :=
      ContinuousOn.circleIntegrable' (hharcharm.mono hsp2).continuousOn
    have hsub := Real.circleAverage_fun_sub (f₁ := fun w => Work.TMComp.Kotani.ell α lam w)
      (f₂ := harc E R Marc) hci1 hci2
    simp only [hVdef]
    rw [hsub, h1, h2]
  have hbd : ∀ ζ ∈ frontier Ω, ∀ η : ℝ, 0 < η →
      ∀ᶠ z in nhdsWithin ζ Ω, V z ≤ 0 + η := by
    intro ζ hζ η hη
    rcases hfrontier ζ hζ with ⟨him, hdist⟩ | ⟨him, hdist⟩
    · have hcont : ContinuousAt V ζ := by
        have h1 : ContinuousAt (fun w : ℂ => Work.TMComp.Kotani.ell α lam w) ζ :=
          (hharm ζ him).1.continuousAt
        have h2 : ContinuousAt (harc E R Marc) ζ := harc_continuousAt_arc E R Marc ζ him hdist
        exact h1.sub h2
      have hleζ : V ζ < 0 + η := by
        have h1 : Work.TMComp.Kotani.ell α lam ζ ≤ Marc := harcin ζ hdist him
        have h2 : harc E R Marc ζ = Marc := harcarc ζ hdist him
        simp only [hVdef, h2]
        linarith
      exact (hcont.eventually (eventually_le_nhds hleζ)).filter_mono nhdsWithin_le_nhds
    · have hxmem : ζ.re ∈ Set.Ioo a b := by
        have h1 : |ζ.re - E| ≤ R := by
          have h2 := Complex.abs_re_le_norm (ζ - (E : ℂ))
          simp only [Complex.sub_re, Complex.ofReal_re] at h2
          exact le_trans h2 hdist
        refine hRmem ?_
        rw [Set.mem_Icc]
        exact ⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩
      have hζeq : ζ = ((ζ.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [him]
      have hℓ := ell_tendsto_zero_near_real α lam a b hL ζ.re hxmem η hη
      have hmono : nhdsWithin ζ Ω ≤ nhdsWithin ((ζ.re : ℝ) : ℂ) {z : ℂ | 0 < z.im} := by
        rw [← hζeq]
        exact nhdsWithin_mono ζ (fun z hz => hz.1)
      filter_upwards [hℓ.filter_mono hmono, self_mem_nhdsWithin] with z hz1 hz2
      have hnn : 0 ≤ harc E R Marc z := harcnonneg z hz2.1 hz2.2
      simp only [hVdef]
      linarith
  have hmax : ∀ z ∈ Ω, V z ≤ 0 :=
    circleAverage_maxPrinciple_limsup (C := 0) hΩopen hΩbdd hΩpre hVc hVmean hbd
  have hEim : ((E : ℂ) + (ε : ℂ) * Complex.I).im = ε := by simp
  have hsubε : ((E : ℂ) + (ε : ℂ) * Complex.I) - (E : ℂ) = (ε : ℂ) * Complex.I := by ring
  have hnε : ‖(ε : ℂ) * Complex.I‖ = ε := by
    rw [Complex.norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos hε]
  rcases lt_or_ge ε R with hεR | hRε
  · have hzΩ : ((E : ℂ) + (ε : ℂ) * Complex.I) ∈ Ω := by
      refine ⟨by rw [hEim]; exact hε, ?_⟩
      rw [hsubε, hnε]
      exact hεR
    have hVle : V ((E : ℂ) + (ε : ℂ) * Complex.I) ≤ 0 := hmax _ hzΩ
    have hell : Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I)
        ≤ (4 * Marc / (Real.pi * R)) * ε := by
      have h1 : Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I)
          ≤ harc E R Marc ((E : ℂ) + (ε : ℂ) * Complex.I) := by
        simp only [hVdef] at hVle
        linarith
      rw [harcaxis ε hε hεR] at h1
      have h2 : Real.arctan (ε / R) ≤ ε / R := arctan_le_self (by positivity)
      have h3 : (4 * Marc / Real.pi) * Real.arctan (ε / R) ≤ (4 * Marc / Real.pi) * (ε / R) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (4 * Marc / Real.pi) * (ε / R) = (4 * Marc / (Real.pi * R)) * ε := by ring
      linarith [h1, h3, h4.le, h4.ge]
    have h5 : (4 * Marc / (Real.pi * R))
        ≤ max 1 (max (4 * Marc / (Real.pi * R)) (Mbig / R)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    exact le_trans hell (mul_le_mul_of_nonneg_right h5 (le_of_lt hε))
  · have h1 : Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) ≤ Mbig := by
      refine (ell_le_M_of_norm_le α lam _ (by rw [hEim]; exact hε) (Mb + 1) ?_).trans ?_
      · calc ‖(E : ℂ) + (ε : ℂ) * Complex.I‖
            ≤ ‖(E : ℂ)‖ + ‖(ε : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |E| + ε := by rw [hnormE, hnε]
          _ ≤ Mb + 1 := by linarith
      · rw [hMbigdef]
    have h5 : (Mbig / R) ≤ max 1 (max (4 * Marc / (Real.pi * R)) (Mbig / R)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have h3 : Mbig ≤ (Mbig / R) * R := by
      rw [div_mul_cancel₀ _ (ne_of_gt hRpos)]
    calc Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I)
        ≤ Mbig := h1
      _ ≤ (Mbig / R) * R := h3
      _ ≤ (Mbig / R) * ε := mul_le_mul_of_nonneg_left hRε (div_nonneg hMbignn (le_of_lt hRpos))
      _ ≤ max 1 (max (4 * Marc / (Real.pi * R)) (Mbig / R)) * ε :=
            mul_le_mul_of_nonneg_right h5 (le_of_lt hε)

/-! ## The a.e. phase statement -/

theorem ae_jump_of_lyap_eq_zero (α lam a b a' b' : ℝ) (hab : a < b) (ha' : a < a') (hb' : b' < b) (ha'b' : a' < b') (hL : ∀ E ∈ Set.Ioo a b, Work.TMContract.lyap α lam (E : ℂ) = 0) : ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)), ∃ e : ℕ → ℝ, (∀ j : ℕ, 0 < e j ∧ e j < 1) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun j : ℕ => ∫ E in a'..b', ‖Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) + (e j : ℂ) * Complex.I) y) - Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam ((E : ℂ) - (e j : ℂ) * Complex.I) y)‖) Filter.atTop (nhds 0) := by
  obtain ⟨C, hCpos, hC⟩ := ell_le_mul_Icc α lam a b a' b' ha' hb' ha'b' hL
  have hH : ∃ C : ℝ, 0 < C ∧ ∀ E ∈ Set.Ioc a' b', ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Work.TMComp.Kotani.ell α lam ((E : ℂ) + (ε : ℂ) * Complex.I) ≤ C * ε :=
    ⟨C, hCpos, fun E hE ε hε hε1 => hC E ⟨le_of_lt hE.1, hE.2⟩ ε hε hε1⟩
  have hKfin : MeasureTheory.volume (Set.Ioc a' b') < ⊤ := measure_Ioc_lt_top
  have hae := Work.TMComp.LocCantor.jump_tendsto_ae_of_H α lam (K := Set.Ioc a' b')
    measurableSet_Ioc hKfin hH
  filter_upwards [hae] with y hy
  obtain ⟨e, hepos, he0, hlim⟩ := hy
  have hev : ∀ᶠ j in Filter.atTop, e j < 1 :=
    he0.eventually (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hev
  have hshift : Filter.Tendsto (fun j : ℕ => j + J) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop]
    exact fun a => ⟨a, fun b hb => le_trans hb (Nat.le_add_right b J)⟩
  refine ⟨fun j => e (j + J), ?_, ?_, ?_⟩
  · intro j
    exact ⟨hepos (j + J), hJ (j + J) (Nat.le_add_left J j)⟩
  · exact he0.comp hshift
  · have hcomp : Filter.Tendsto (fun j : ℕ => ∫ E in Set.Ioc a' b',
        ‖Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam
            ((E : ℂ) + (e (j + J) : ℂ) * Complex.I) y)
          - Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam
            ((E : ℂ) - (e (j + J) : ℂ) * Complex.I) y)‖) Filter.atTop (nhds 0) :=
      hlim.comp hshift
    have hbridge : (fun j : ℕ => ∫ E in a'..b',
        ‖Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam
            ((E : ℂ) + (e (j + J) : ℂ) * Complex.I) y)
          - Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam
            ((E : ℂ) - (e (j + J) : ℂ) * Complex.I) y)‖)
        = (fun j : ℕ => ∫ E in Set.Ioc a' b',
        ‖Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam
            ((E : ℂ) + (e (j + J) : ℂ) * Complex.I) y)
          - Work.TMComp.Kotani.cayley (Work.TMComp.Kotani.Psi α lam
            ((E : ℂ) - (e (j + J) : ℂ) * Complex.I) y)‖) := by
      funext j
      exact intervalIntegral.integral_of_le ha'b'.le
    rw [hbridge]
    exact hcomp

end Work.TMComp.RedC8
