import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.profHatCube_moments
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The profile moments: `Integrable (φ²)` and `Integrable (‖p‖²φ²)` for every `M ≥ 1` -/

/-- **`p ↦ (profHatCube M p)²` is integrable** for `M ≥ 1`: Plancherel for the (bounded,
compactly supported, hence `L¹ ∩ L²`) cube bump, plus `profHatCube ≤ ‖kinFT χ_M‖`. -/
theorem profCubeSqIntegrable (M : ℕ) (hM : 1 ≤ M) :
    MeasureTheory.Integrable (fun p : E3 => (profHatCube M p) ^ 2) := by
  have hcont : Continuous (fun z : E3 => (chiSmall M z : ℂ)) :=
    Complex.continuous_ofReal.comp (chiSmall_continuous hM)
  have hcs : HasCompactSupport (fun z : E3 => (chiSmall M z : ℂ)) :=
    (chiSmall_hasCompactSupport hM).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hmem1 : MemLp (fun z : E3 => (chiSmall M z : ℂ)) 1 volume :=
    memLp_one_iff_integrable.mpr (hcont.integrable_of_hasCompactSupport hcs)
  have hmem2 : MemLp (fun z : E3 => (chiSmall M z : ℂ)) 2 volume :=
    hcont.memLp_of_hasCompactSupport hcs
  refine (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp hmem1 hmem2).1.congr ?_
  filter_upwards with p
  rw [pcKinFT_chiSmall_eq M hM p, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-- The explicit `k`-th partial derivative `pcD M k` of the cube bump is measurable. -/
private lemma pcD_measurable (M : ℕ) (k : Fin 3) :
    Measurable (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) := by
  refine Complex.measurable_ofReal.comp ?_
  rw [show pcD M k = fun z : E3 => cSmall M * phiCDeriv M (z.ofLp k)
      * ∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i) from rfl]
  refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
  · exact (measurable_phiCDeriv M).comp (by fun_prop)
  · refine Finset.measurable_prod _ fun i _ => ?_
    exact (zeta1d_continuous.pow M).measurable.comp (by fun_prop)

/-- `pcD M k` vanishes outside the unit ball. -/
private lemma pcD_eq_zero_of_one_lt_norm {M : ℕ} (hM : 1 ≤ M) (k : Fin 3) {z : E3}
    (hz : 1 < ‖z‖) : pcD M k z = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, 1 / 2 < |z.ofLp i| := by
    by_contra hcon
    rw [not_exists] at hcon
    have hle : ∀ j : Fin 3, |z.ofLp j| ≤ 1 / 2 := fun j => le_of_not_gt (hcon j)
    have hsq : ‖z‖ ^ 2 ≤ 3 * (1 / 2) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ j, ‖z.ofLp j‖ ^ 2 ≤ ∑ _j : Fin 3, (1 / 2) ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hle j) 2
        _ = 3 * (1 / 2) ^ 2 := by simp
    have h3 : (3 : ℝ) * (1 / 2) ^ 2 < 1 ^ 2 := by norm_num
    nlinarith [norm_nonneg z, hsq, h3]
  rw [pcD]
  by_cases hik : i = k
  · subst hik
    rw [phiCDeriv_eq_zero_of_half_le (le_of_lt hi), mul_zero, zero_mul]
  · have hzi : phiC M (z.ofLp i) = 0 := phiC_eq_zero_of_half_le hM (le_of_lt hi)
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩) hzi]
    ring

/-- `pcD M k`, viewed in `ℂ`, lies in `L¹ ∩ L²` (bounded, compactly supported). -/
private lemma pcD_memLp (M : ℕ) (hM : 1 ≤ M) (k : Fin 3) :
    MemLp (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) 1 volume
      ∧ MemLp (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) 2 volume := by
  have hmeas := pcD_measurable M k
  have hsupp : ∀ z : E3, 1 < ‖z‖ → ((pcD M k z : ℝ) : ℂ) = 0 :=
    fun z hz => by rw [pcD_eq_zero_of_one_lt_norm hM k hz, Complex.ofReal_zero]
  have hcs : HasCompactSupport (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : E3) 1) (isClosed_tsupport _) ?_
    refine closure_minimal ?_ isClosed_closedBall
    intro z hz
    simp only [Function.mem_support, ne_eq] at hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    by_contra h
    exact hz (by simp [hsupp z (lt_of_not_ge h)])
  have hbound : ∀ᵐ z : E3 ∂(volume : Measure E3),
      ‖((pcD M k z : ℝ) : ℂ)‖ ≤ |cSmall M| * ((M : ℝ) * Real.pi) := by
    filter_upwards with z
    rw [pcNorm_ofReal, pcD, abs_mul, abs_mul]
    have hprod : |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) (fun i _ => abs_phiC_le_one M _)
    calc |cSmall M| * |phiCDeriv M (z.ofLp k)|
            * |∏ i ∈ Finset.univ.erase k, phiC M (z.ofLp i)|
        ≤ |cSmall M| * ((M : ℝ) * Real.pi) * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (abs_phiCDeriv_le M _) (abs_nonneg _)) hprod
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      _ = |cSmall M| * ((M : ℝ) * Real.pi) := by ring
  exact ⟨hcs.memLp_of_bound hmeas.aestronglyMeasurable _ hbound,
    hcs.memLp_of_bound hmeas.aestronglyMeasurable _ hbound⟩

/-- **`p ↦ ‖p‖²·(profHatCube M p)²` is integrable for every `M ≥ 1`** (the Lipschitz case
`M = 1` included).  The a.e. explicit partials `pcD M k` of the cube bump satisfy the pointwise
identity `‖p‖²·φ(p)² = Σ_k ‖kinFT (pcD M k) p‖²`, and each summand is integrable by Plancherel
for `L¹ ∩ L²`. -/
theorem profCubeMom2Integrable (M : ℕ) (hM : 1 ≤ M) :
    MeasureTheory.Integrable (fun p : E3 => ‖p‖ ^ 2 * (profHatCube M p) ^ 2) := by
  have hInt : ∀ k : Fin 3, Integrable
      (fun p : E3 => ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2) :=
    fun k => (Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
      (pcD_memLp M hM k).1 (pcD_memLp M hM k).2).1
  refine (integrable_finsetSum (Finset.univ : Finset (Fin 3))
    (f := fun (k : Fin 3) (p : E3) =>
      ‖kinFT (fun z : E3 => ((pcD M k z : ℝ) : ℂ)) p‖ ^ 2)
    (fun k _ => hInt k)).congr ?_
  filter_upwards with p
  have hχ : (profHatCube M p) ^ 2
      = ‖kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2 := by
    rw [pcKinFT_chiSmall_eq M hM p, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [hχ]
  rw [show ‖p‖ ^ 2 = ∑ k : Fin 3, (p.ofLp k) ^ 2 from by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pcKinFT_pcD M hM k p]
  have hnorm : ‖Complex.I * (p.ofLp k : ℂ)
        * kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2
      = (p.ofLp k) ^ 2 * ‖kinFT (fun z : E3 => (chiSmall M z : ℂ)) p‖ ^ 2 := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow, Complex.norm_I, one_pow, one_mul,
      pcNorm_ofReal, sq_abs]
  rw [hnorm]

/-! ## 2. Elementary properties of the FS cut-off `fsKinCoeff` -/

/-- `fsKinCoeff c r ≤ 2r² + 2c²` (no sign hypothesis). -/
private lemma fsKinCoeff_le_two_sq (c r : ℝ) : fsKinCoeff c r ≤ 2 * r ^ 2 + 2 * c ^ 2 := by
  unfold fsKinCoeff
  have h1 : max (r - c) 0 ≤ |r| + |c| := by
    refine max_le ?_ (by positivity)
    have h2 := le_abs_self r
    have h3 := neg_le_abs c
    linarith
  calc max (r - c) 0 ^ 2 ≤ (|r| + |c|) ^ 2 := pow_le_pow_left₀ (le_max_right _ _) h1 2
    _ ≤ 2 * r ^ 2 + 2 * c ^ 2 := by
        rw [add_sq]
        nlinarith [sq_abs r, sq_abs c, sq_nonneg (|r| - |c|), abs_nonneg r, abs_nonneg c]

/-- `fsKinCoeff c r = (r − c)²` once `c ≤ r`. -/
private lemma fsKinCoeff_eq_of_le {c r : ℝ} (h : c ≤ r) : fsKinCoeff c r = (r - c) ^ 2 := by
  unfold fsKinCoeff
  rw [max_eq_left (by linarith)]

/-- `fsKinCoeff c r ≤ r²` for `c, r ≥ 0`. -/
private lemma fsKinCoeff_le_sq {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) : fsKinCoeff c r ≤ r ^ 2 := by
  unfold fsKinCoeff
  refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ ?_) 2
  · linarith
  · exact hr

/-- `fsKinCoeff` is antitone in its cut-off. -/
private lemma fsKinCoeff_anti {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) (r : ℝ) :
    fsKinCoeff c₂ r ≤ fsKinCoeff c₁ r := by
  unfold fsKinCoeff
  refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ ?_) 2
  · exact le_trans (by linarith : r - c₂ ≤ r - c₁) (le_max_left _ _)
  · exact le_max_right _ _

/-- **The shift only costs `‖ρ‖` in the cut-off.** -/
private lemma fsKinCoeff_shift_le (C : ℝ) (ρ p : E3) :
    fsKinCoeff C ‖ρ + p‖ ≤ fsKinCoeff (C - ‖ρ‖) ‖p‖ := by
  have h1 : ‖ρ + p‖ - C ≤ ‖p‖ - (C - ‖ρ‖) := by
    have h := norm_add_le ρ p
    linarith
  have h2 : max (‖ρ + p‖ - C) 0 ≤ max (‖p‖ - (C - ‖ρ‖)) 0 :=
    max_le (h1.trans (le_max_left _ _)) (le_max_right _ _)
  exact pow_le_pow_left₀ (le_max_right _ _) h2 2

/-- **The cut-off scales homogeneously**: `fsKinCoeff e (a·r) = a²·fsKinCoeff (e/a) r` for
`a > 0`. -/
private lemma fsKinCoeff_mul_scale {a e : ℝ} (ha : 0 < a) (r : ℝ) :
    fsKinCoeff e (a * r) = a ^ 2 * fsKinCoeff (e / a) r := by
  unfold fsKinCoeff
  have h1 : max (a * r - e) 0 = a * max (r - e / a) 0 := by
    have h : a * (r - e / a) = a * r - e := by
      rw [mul_sub, mul_div_cancel₀ e (ne_of_gt ha)]
    rw [← h, mul_max_of_nonneg _ _ ha.le, mul_zero]
  rw [h1, mul_pow]

private lemma continuous_fsKinCoeff (c : ℝ) : Continuous (fun x : ℝ => fsKinCoeff c x) := by
  unfold fsKinCoeff
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

/-! ## 3. Integrability of the cut-off-weighted profile squares -/

/-- `φ²‖·‖` is integrable as soon as `φ²` and `‖·‖²φ²` are. -/
private lemma integrable_phi_sq_norm {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2)) :
    Integrable (fun p : E3 => φ p ^ 2 * ‖p‖) := by
  refine (h0.add h2).mono' (h0.aestronglyMeasurable.mul continuous_norm.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg p))]
  have hp : ‖p‖ ≤ 1 + ‖p‖ ^ 2 := by nlinarith [norm_nonneg p, sq_nonneg (‖p‖ - 1)]
  calc φ p ^ 2 * ‖p‖ ≤ φ p ^ 2 * (1 + ‖p‖ ^ 2) := mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = φ p ^ 2 + ‖p‖ ^ 2 * φ p ^ 2 := by ring

/-- `fsKinCoeff c ‖·‖ · φ²` is integrable for every real `c` (dominated by
`2‖p‖²φ² + 2c²φ²`). -/
private lemma integrable_fsKinCoeff_phi_sq {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2)) (c : ℝ) :
    Integrable (fun p : E3 => fsKinCoeff c ‖p‖ * φ p ^ 2) := by
  have hmaj : Integrable (fun p : E3 =>
      2 * (‖p‖ ^ 2 * φ p ^ 2) + (2 * c ^ 2) * φ p ^ 2) :=
    (h2.const_mul 2).add (h0.const_mul (2 * c ^ 2))
  refine hmaj.mono' (((continuous_fsKinCoeff c).comp continuous_norm).aestronglyMeasurable.mul
    h0.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))]
  calc fsKinCoeff c ‖p‖ * φ p ^ 2 ≤ (2 * ‖p‖ ^ 2 + 2 * c ^ 2) * φ p ^ 2 :=
        mul_le_mul_of_nonneg_right (fsKinCoeff_le_two_sq c ‖p‖) (sq_nonneg _)
    _ = 2 * (‖p‖ ^ 2 * φ p ^ 2) + (2 * c ^ 2) * φ p ^ 2 := by ring

/-- `fsKinCoeff c ‖ρ + ·‖ · φ²` is integrable for every real `c` and every `ρ`. -/
private lemma integrable_fsKinCoeff_shift_phi_sq {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2)) (c : ℝ) (ρ : E3) :
    Integrable (fun p : E3 => fsKinCoeff c ‖ρ + p‖ * φ p ^ 2) := by
  have hmaj : Integrable (fun p : E3 =>
      4 * (‖p‖ ^ 2 * φ p ^ 2) + (8 * ‖ρ‖ ^ 2 + 4 * c ^ 2) * φ p ^ 2) :=
    (h2.const_mul 4).add (h0.const_mul (8 * ‖ρ‖ ^ 2 + 4 * c ^ 2))
  refine hmaj.mono' (((continuous_fsKinCoeff c).comp
    (continuous_const.add continuous_id).norm).aestronglyMeasurable.mul h0.aestronglyMeasurable) ?_
  filter_upwards with p
  rw [Real.norm_of_nonneg (mul_nonneg (fsKinCoeff_nonneg c ‖ρ + p‖) (sq_nonneg _))]
  have hsum : ‖ρ + p‖ ^ 2 ≤ 2 * ‖ρ‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
    have h1 : ‖ρ + p‖ ≤ ‖ρ‖ + ‖p‖ := norm_add_le ρ p
    have h2 : ‖ρ + p‖ ^ 2 ≤ (‖ρ‖ + ‖p‖) ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
    nlinarith [h2, sq_nonneg (‖ρ‖ - ‖p‖)]
  calc fsKinCoeff c ‖ρ + p‖ * φ p ^ 2
      ≤ (4 * ‖p‖ ^ 2 + (8 * ‖ρ‖ ^ 2 + 4 * c ^ 2)) * φ p ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have h := fsKinCoeff_le_two_sq c ‖ρ + p‖
        nlinarith [h, hsum, sq_nonneg ‖ρ‖, sq_nonneg c]
    _ = 4 * (‖p‖ ^ 2 * φ p ^ 2) + (8 * ‖ρ‖ ^ 2 + 4 * c ^ 2) * φ p ^ 2 := by ring

/-! ## 4. The scale-one two-cut comparison for an abstract profile -/

/-- The scale-one two-cut symbol of a profile `φ`: `(2π)⁻³ ∫_p F‖q + p‖ · φ(p)²`. -/
private noncomputable def Sym (φ : E3 → ℝ) (F : ℝ → ℝ) (q : E3) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖q + p‖ * φ p ^ 2

/-- The first moment `M₁ = (2π)⁻³ ∫ φ(p)² ‖p‖`. -/
private noncomputable def M1 (φ : E3 → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, φ p ^ 2 * ‖p‖

/-- The second moment `M₂ = (2π)⁻³ ∫ φ(p)² ‖p‖²`. -/
private noncomputable def M2 (φ : E3 → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2

private lemma Sym_zero_eq (φ : E3 → ℝ) (F : ℝ → ℝ) :
    Sym φ F 0 = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * φ p ^ 2 := by
  simp only [Sym, zero_add]

/-- `symACube M 1 F q` is the scale-one symbol of the profile `profHatCube M`. -/
private lemma symACube_one_eq (M : ℕ) (F : ℝ → ℝ) (q : E3) :
    symACube M 1 F q = Sym (profHatCube M) F q := by
  simp only [symACube, Sym, inv_one, one_smul]

/-- The symbol at `q = 0` of a nonnegative cut-off is nonnegative. -/
private lemma Sym_zero_nonneg {φ : E3 → ℝ} {F : ℝ → ℝ} (hF : ∀ r : ℝ, 0 ≤ F r) :
    0 ≤ Sym φ F 0 := by
  rw [Sym_zero_eq]
  refine mul_nonneg (by positivity) (integral_nonneg (fun p => ?_))
  exact mul_nonneg (hF ‖p‖) (sq_nonneg _)

/-- The symbol at `q = 0` is antitone in the cut-off. -/
private lemma Sym_zero_anti {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2))
    {c₁ c₂ : ℝ} (h₁ : 0 ≤ c₁) (h : c₁ ≤ c₂) :
    Sym φ (fsKinCoeff c₂) 0 ≤ Sym φ (fsKinCoeff c₁) 0 := by
  rw [Sym_zero_eq, Sym_zero_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact integral_mono (integrable_fsKinCoeff_phi_sq h0 h2 c₂)
    (integrable_fsKinCoeff_phi_sq h0 h2 c₁)
    (fun p => mul_le_mul_of_nonneg_right (fsKinCoeff_anti h ‖p‖) (sq_nonneg _))

/-- The symbol at `q = 0` at a nonnegative cut-off is at most the second moment `M₂`. -/
private lemma Sym_zero_le_M2 {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2)) {c : ℝ} (hc : 0 ≤ c) :
    Sym φ (fsKinCoeff c) 0 ≤ M2 φ := by
  have h2' : Integrable (fun p : E3 => φ p ^ 2 * ‖p‖ ^ 2) :=
    h2.congr (Filter.Eventually.of_forall (fun p => by ring))
  rw [Sym_zero_eq, M2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine integral_mono (integrable_fsKinCoeff_phi_sq h0 h2 c) h2' (fun p => ?_)
  calc fsKinCoeff c ‖p‖ * φ p ^ 2 ≤ ‖p‖ ^ 2 * φ p ^ 2 :=
        mul_le_mul_of_nonneg_right (fsKinCoeff_le_sq hc (norm_nonneg p)) (sq_nonneg _)
    _ = φ p ^ 2 * ‖p‖ ^ 2 := by ring

/-- The exact `p`-integral of the quadratic majorant:
`∫_p (a + ‖p‖)² φ(p)² = a² ∫φ² + 2a ∫φ²‖p‖ + ∫φ²‖p‖²`. -/
private lemma integral_sq_shift {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2)) (a : ℝ) :
    (∫ p : E3, (a + ‖p‖) ^ 2 * φ p ^ 2)
      = a ^ 2 * (∫ p : E3, φ p ^ 2) + 2 * a * (∫ p : E3, φ p ^ 2 * ‖p‖)
        + ∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2 := by
  have h1 : Integrable (fun p : E3 => φ p ^ 2 * ‖p‖) := integrable_phi_sq_norm h0 h2
  have h2' : Integrable (fun p : E3 => φ p ^ 2 * ‖p‖ ^ 2) := by
    refine h2.congr (Filter.Eventually.of_forall (fun p => by ring))
  have hEq : (fun p : E3 => (a + ‖p‖) ^ 2 * φ p ^ 2)
      = fun p : E3 => a ^ 2 * (φ p ^ 2) + (2 * a) * (φ p ^ 2 * ‖p‖)
          + φ p ^ 2 * ‖p‖ ^ 2 := by
    funext p; ring
  rw [hEq]
  have hT1 : Integrable (fun p : E3 => a ^ 2 * (φ p ^ 2)) := h0.const_mul _
  have hT2 : Integrable (fun p : E3 => (2 * a) * (φ p ^ 2 * ‖p‖)) := h1.const_mul _
  have hsplit2 : (∫ p : E3, (a ^ 2 * (φ p ^ 2) + (2 * a) * (φ p ^ 2 * ‖p‖))
        + φ p ^ 2 * ‖p‖ ^ 2)
      = (∫ p : E3, a ^ 2 * (φ p ^ 2) + (2 * a) * (φ p ^ 2 * ‖p‖))
        + (∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2) :=
    integral_add (hT1.add hT2) h2'
  have hsplit1 : (∫ p : E3, a ^ 2 * (φ p ^ 2) + (2 * a) * (φ p ^ 2 * ‖p‖))
      = (∫ p : E3, a ^ 2 * (φ p ^ 2)) + (∫ p : E3, (2 * a) * (φ p ^ 2 * ‖p‖)) :=
    integral_add hT1 hT2
  rw [hsplit2, hsplit1, integral_const_mul, integral_const_mul]

/-- **The far-regime bound**: for `C ≤ ‖ρ‖`,
`Sym φ (fsKinCoeff C) ρ ≤ (‖ρ‖−C)² + 2(‖ρ‖−C)·M₁ + M₂`. -/
private lemma Sym_far_le {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2))
    (hnorm : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2) = 1)
    {C : ℝ} (ρ : E3) (hρ : C ≤ ‖ρ‖) :
    Sym φ (fsKinCoeff C) ρ ≤ (‖ρ‖ - C) ^ 2 + 2 * (‖ρ‖ - C) * M1 φ + M2 φ := by
  have h1 : Integrable (fun p : E3 => φ p ^ 2 * ‖p‖) := integrable_phi_sq_norm h0 h2
  have h2' : Integrable (fun p : E3 => φ p ^ 2 * ‖p‖ ^ 2) := by
    refine h2.congr (Filter.Eventually.of_forall (fun p => by ring))
  have hpt : ∀ p : E3,
      fsKinCoeff C ‖ρ + p‖ * φ p ^ 2 ≤ ((‖ρ‖ - C) + ‖p‖) ^ 2 * φ p ^ 2 := by
    intro p
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    show fsKinCoeff C ‖ρ + p‖ ≤ ((‖ρ‖ - C) + ‖p‖) ^ 2
    unfold fsKinCoeff
    refine pow_le_pow_left₀ (le_max_right (‖ρ + p‖ - C) 0) ?_ 2
    refine max_le ?_ ?_
    · have h : ‖ρ + p‖ ≤ ‖ρ‖ + ‖p‖ := norm_add_le _ _
      linarith
    · linarith [norm_nonneg p]
  have hmaj : Integrable (fun p : E3 => ((‖ρ‖ - C) + ‖p‖) ^ 2 * φ p ^ 2) := by
    have hEq : (fun p : E3 => ((‖ρ‖ - C) + ‖p‖) ^ 2 * φ p ^ 2)
        = fun p : E3 => (‖ρ‖ - C) ^ 2 * (φ p ^ 2) + (2 * (‖ρ‖ - C)) * (φ p ^ 2 * ‖p‖)
            + φ p ^ 2 * ‖p‖ ^ 2 := by
      funext p; ring
    rw [hEq]
    exact ((h0.const_mul _).add (h1.const_mul _)).add h2'
  have hmono : (∫ p : E3, fsKinCoeff C ‖ρ + p‖ * φ p ^ 2)
      ≤ ∫ p : E3, ((‖ρ‖ - C) + ‖p‖) ^ 2 * φ p ^ 2 :=
    integral_mono (integrable_fsKinCoeff_shift_phi_sq h0 h2 C ρ) hmaj hpt
  rw [Sym]
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, fsKinCoeff C ‖ρ + p‖ * φ p ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, ((‖ρ‖ - C) + ‖p‖) ^ 2 * φ p ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (‖ρ‖ - C) ^ 2 + 2 * (‖ρ‖ - C) * M1 φ + M2 φ := by
        rw [integral_sq_shift h0 h2 (‖ρ‖ - C), M1, M2]
        rw [show ((2 * Real.pi) ^ 3)⁻¹ * ((‖ρ‖ - C) ^ 2 * (∫ p : E3, φ p ^ 2)
              + 2 * (‖ρ‖ - C) * (∫ p : E3, φ p ^ 2 * ‖p‖)
              + ∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2)
            = (‖ρ‖ - C) ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2))
              + 2 * (‖ρ‖ - C) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2 * ‖p‖))
              + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2) from by ring]
        rw [hnorm]
        ring

/-- **The Young/AM–GM bound on the first moment**: `8M₂ ≤ (1−d)²C²` forces
`M₁ ≤ 3(1−d)C/8`. -/
private lemma M1_le_three_eighths {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2))
    (hnorm : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2) = 1)
    {C d : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hM2 : 8 * M2 φ ≤ (1 - d) ^ 2 * C ^ 2) : M1 φ ≤ 3 * (1 - d) * C / 8 := by
  set a : ℝ := (1 - d) * C / 4 with ha
  have h1d : 0 < 1 - d := by linarith
  have ha_pos : 0 < a := by rw [ha]; positivity
  have h4a : 0 < 4 * a := by linarith
  have h4a_ne : 4 * a ≠ 0 := ne_of_gt h4a
  have hpt : ∀ p : E3, ‖p‖ ≤ a + ‖p‖ ^ 2 / (4 * a) := by
    intro p
    have hcancel : 4 * a * (‖p‖ ^ 2 / (4 * a)) = ‖p‖ ^ 2 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ h4a_ne]
    have hexp : 4 * a * (a + ‖p‖ ^ 2 / (4 * a)) = 4 * a ^ 2 + ‖p‖ ^ 2 := by
      rw [mul_add, hcancel]; ring
    have hkey : 4 * a * ‖p‖ ≤ 4 * a * (a + ‖p‖ ^ 2 / (4 * a)) := by
      rw [hexp]
      nlinarith [sq_nonneg (‖p‖ - 2 * a)]
    exact le_of_mul_le_mul_left hkey h4a
  have h1 : Integrable (fun p : E3 => φ p ^ 2 * ‖p‖) := integrable_phi_sq_norm h0 h2
  have h2' : Integrable (fun p : E3 => φ p ^ 2 * ‖p‖ ^ 2) := by
    refine h2.congr (Filter.Eventually.of_forall (fun p => by ring))
  have hmaj_eq : (fun p : E3 => φ p ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)))
      = fun p : E3 => a * (φ p ^ 2) + (1 / (4 * a)) * (φ p ^ 2 * ‖p‖ ^ 2) := by
    funext p; ring
  have hmaj_int : Integrable (fun p : E3 => φ p ^ 2 * (a + ‖p‖ ^ 2 / (4 * a))) := by
    rw [hmaj_eq]
    exact (h0.const_mul a).add (h2'.const_mul (1 / (4 * a)))
  have hcomp : (∫ p : E3, φ p ^ 2 * ‖p‖)
      ≤ ∫ p : E3, φ p ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)) :=
    integral_mono h1 hmaj_int (fun p => mul_le_mul_of_nonneg_left (hpt p) (sq_nonneg _))
  have hval : (∫ p : E3, φ p ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)))
      = a * (∫ p : E3, φ p ^ 2) + (1 / (4 * a)) * (∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2) := by
    rw [hmaj_eq, integral_add (h0.const_mul a) (h2'.const_mul _), integral_const_mul,
      integral_const_mul]
  have hM1a : M1 φ ≤ a + (1 / (4 * a)) * M2 φ := by
    rw [M1, M2]
    have hπ : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
    calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2 * ‖p‖)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, φ p ^ 2 * (a + ‖p‖ ^ 2 / (4 * a)) :=
          mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = ((2 * Real.pi) ^ 3)⁻¹ * (a * (∫ p : E3, φ p ^ 2)
            + (1 / (4 * a)) * (∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2)) := by rw [hval]
      _ = a + (1 / (4 * a)) * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2) := by
          rw [show ((2 * Real.pi) ^ 3)⁻¹ * (a * (∫ p : E3, φ p ^ 2)
                + (1 / (4 * a)) * (∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2))
              = a * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2))
                + (1 / (4 * a)) * (((2 * Real.pi) ^ 3)⁻¹
                  * (∫ p : E3, φ p ^ 2 * ‖p‖ ^ 2)) from by ring]
          rw [hnorm, mul_one]
  have hM2le : M2 φ ≤ (1 - d) ^ 2 * C ^ 2 / 8 := by nlinarith [hM2]
  have hnum : a + (1 / (4 * a)) * M2 φ ≤ 3 * (1 - d) * C / 8 := by
    have hcancel : 4 * a * (1 / (4 * a) * M2 φ) = M2 φ := by
      rw [← mul_assoc, mul_one_div_cancel h4a_ne, one_mul]
    have hexp : 4 * a * (a + (1 / (4 * a)) * M2 φ) = 4 * a ^ 2 + M2 φ := by
      rw [mul_add, ← mul_assoc, mul_one_div_cancel h4a_ne, one_mul]; ring
    have key : 4 * a * (a + (1 / (4 * a)) * M2 φ) ≤ 4 * a * (3 * (1 - d) * C / 8) := by
      rw [hexp, ha]
      nlinarith [hM2le]
    exact le_of_mul_le_mul_left key h4a
  linarith [hM1a, hnum]

/-- **The three-region arithmetic of the two-cut comparison** (pure real). -/
private lemma mixArith {M1 M2 C d ε β : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2) (hβ : 0 ≤ β)
    (hM1 : M1 ≤ 3 * (1 - d) * C / 8) (hM2 : 8 * M2 ≤ (1 - d) ^ 2 * C ^ 2) :
    M1 ≤ (1 - ε) * (C - d * C / 2) + ε * (C / 2)
      ∧ M2 ≤ (1 - ε) * (C - d * C / 2) ^ 2 + ε * (C / 2) ^ 2 + β
      ∧ (∀ t : ℝ, C / 2 ≤ t → M2 ≤ (1 - ε) * (t - d * C / 2) ^ 2) := by
  have hM2' : M2 ≤ (1 - d) ^ 2 * C ^ 2 / 8 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hεC : 0 ≤ ε * C := mul_nonneg hε0 (le_of_lt hC)
    have hεdC : 0 ≤ ε * ((1 - d) * C) :=
      mul_nonneg hε0 (mul_nonneg (by linarith) (le_of_lt hC))
    nlinarith [hM1, hε, hε0, hd, hd0, hC, hεC, hεdC]
  · have hge : (C * (1 - d)) ^ 2 ≤ (C - d * C / 2) ^ 2 := by
      refine pow_le_pow_left₀ (by nlinarith [hd, hC]) ?_ 2
      nlinarith [hd, hC, hd0]
    have hhalf : (1 : ℝ) / 2 ≤ 1 - ε := by linarith
    have h2 : (1 / 2) * (C - d * C / 2) ^ 2
        ≤ (1 - ε) * (C - d * C / 2) ^ 2 := mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
    have h3 : (1 / 2) * (C * (1 - d)) ^ 2 ≤ (1 / 2) * (C - d * C / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hge (by norm_num)
    have h4 : (1 - d) ^ 2 * C ^ 2 / 8 ≤ (1 / 2) * (C * (1 - d)) ^ 2 := by
      nlinarith [sq_nonneg ((1 - d) * C)]
    have hεC : 0 ≤ ε * (C / 2) ^ 2 := mul_nonneg hε0 (sq_nonneg _)
    linarith
  · intro t ht
    have ht' : C * (1 - d) / 2 ≤ t - d * C / 2 := by nlinarith [ht, hd0, hC]
    have h0 : 0 ≤ C * (1 - d) / 2 := by nlinarith [hd, hC]
    have hsq : (C * (1 - d) / 2) ^ 2 ≤ (t - d * C / 2) ^ 2 := pow_le_pow_left₀ h0 ht' 2
    have h2 : (1 - d) ^ 2 * C ^ 2 / 8 ≤ (1 / 2) * (C * (1 - d) / 2) ^ 2 := by
      nlinarith [sq_nonneg ((1 - d) * C)]
    have hhalf : (1 : ℝ) / 2 ≤ 1 - ε := by linarith
    have h3 : (1 / 2) * (C * (1 - d) / 2) ^ 2 ≤ (1 - ε) * (C * (1 - d) / 2) ^ 2 :=
      mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)
    have h4 : (1 - ε) * (C * (1 - d) / 2) ^ 2 ≤ (1 - ε) * (t - d * C / 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by linarith)
    linarith

/-- **The scale-one two-cut comparison** for an abstract profile `φ` satisfying the three
profile inputs (`φ²` integrable, `‖p‖²φ²` integrable, unit mass) and the FS hypotheses
`hnear`/`hM1`/`hM2`/`htail`. -/
theorem cubeTwoCut {φ : E3 → ℝ}
    (h0 : Integrable (fun p : E3 => φ p ^ 2))
    (h2 : Integrable (fun p : E3 => ‖p‖ ^ 2 * φ p ^ 2))
    (hnorm : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, φ p ^ 2) = 1)
    {C d ε β : ℝ} (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hnear : ∀ ρ : E3, Sym φ (fsKinCoeff C) ρ ≤ Sym φ (fsKinCoeff (C - ‖ρ‖)) 0)
    (hM1 : ((2 * Real.pi) ^ 3)⁻¹ * (∫ t : E3, φ t ^ 2 * ‖t‖) ≤ C)
    (hM2 : 8 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ t : E3, φ t ^ 2 * ‖t‖ ^ 2))
      ≤ (1 - d) ^ 2 * C ^ 2)
    (htail : Sym φ (fsKinCoeff (C / 2)) 0 ≤ β) :
    ∀ ρ : E3, Sym φ (fsKinCoeff C) ρ
      ≤ (1 - ε) * fsKinCoeff (d * C / 2) ‖ρ‖ + ε * fsKinCoeff (C / 2) ‖ρ‖ + β := by
  have hM1' : M1 φ ≤ C := hM1
  have hM2' : 8 * M2 φ ≤ (1 - d) ^ 2 * C ^ 2 := hM2
  have hβ : 0 ≤ β := le_trans (Sym_zero_nonneg (fun r => fsKinCoeff_nonneg (C / 2) r)) htail
  have hC0 : 0 ≤ C := le_of_lt hC
  have hd1 : d ≤ 1 := by linarith
  have hM1le : M1 φ ≤ 3 * (1 - d) * C / 8 := M1_le_three_eighths h0 h2 hnorm hC hd0 hd hM2'
  obtain ⟨harith1, harith2, harith3⟩ :=
    mixArith hC hd0 hd hε0 hε hβ hM1le hM2'
  intro ρ
  rcases le_total ‖ρ‖ (C / 2) with ht | ht
  · -- region 1: `‖ρ‖ ≤ C/2`
    have hA : Sym φ (fsKinCoeff C) ρ ≤ β := by
      refine le_trans (hnear ρ) (le_trans (Sym_zero_anti h0 h2 (by linarith) ?_) htail)
      linarith
    have h1 : 0 ≤ (1 - ε) * fsKinCoeff (d * C / 2) ‖ρ‖ :=
      mul_nonneg (by linarith) (fsKinCoeff_nonneg _ _)
    have h2' : 0 ≤ ε * fsKinCoeff (C / 2) ‖ρ‖ :=
      mul_nonneg hε0 (fsKinCoeff_nonneg _ _)
    linarith
  · rcases le_total ‖ρ‖ C with ht2 | ht2
    · -- region 2: `C/2 ≤ ‖ρ‖ ≤ C`
      have hA : Sym φ (fsKinCoeff C) ρ ≤ M2 φ :=
        le_trans (hnear ρ) (Sym_zero_le_M2 h0 h2 (by linarith))
      have hfs : fsKinCoeff (d * C / 2) ‖ρ‖ = (‖ρ‖ - d * C / 2) ^ 2 :=
        fsKinCoeff_eq_of_le (by nlinarith [hd1, hC0, ht])
      have hM : M2 φ ≤ (1 - ε) * (‖ρ‖ - d * C / 2) ^ 2 := harith3 ‖ρ‖ ht
      have hrest : 0 ≤ ε * fsKinCoeff (C / 2) ‖ρ‖ + β := by
        have := mul_nonneg hε0 (fsKinCoeff_nonneg (C / 2) ‖ρ‖)
        linarith
      rw [hfs]
      linarith
    · -- region 3: `C ≤ ‖ρ‖`
      have ht3 : C ≤ ‖ρ‖ := ht2
      have hfar := Sym_far_le h0 h2 hnorm ρ ht3
      have hfs1 : fsKinCoeff (d * C / 2) ‖ρ‖ = (‖ρ‖ - d * C / 2) ^ 2 :=
        fsKinCoeff_eq_of_le (by nlinarith [hd1, hC0, ht3])
      have hfs2 : fsKinCoeff (C / 2) ‖ρ‖ = (‖ρ‖ - C / 2) ^ 2 :=
        fsKinCoeff_eq_of_le (by linarith)
      have hprod : 2 * (‖ρ‖ - C) * M1 φ
          ≤ 2 * (‖ρ‖ - C) * ((1 - ε) * (C - d * C / 2) + ε * (C / 2)) :=
        mul_le_mul_of_nonneg_left harith1 (by linarith)
      have e1 : ‖ρ‖ - d * C / 2 = (‖ρ‖ - C) + (C - d * C / 2) := by ring
      have e2 : ‖ρ‖ - C / 2 = (‖ρ‖ - C) + C / 2 := by ring
      rw [hfs1, hfs2, e1, e2]
      nlinarith [hfar, hprod, harith2]

/-! ## 5. The near-regime monotonicity and the scaling law for the cube symbol -/

/-- **The near-regime monotonicity of the cube symbol.** -/
theorem cubeSymA_near (M : ℕ) (hM : 1 ≤ M) {C : ℝ} (ρ : E3) :
    symACube M 1 (fsKinCoeff C) ρ ≤ symACube M 1 (fsKinCoeff (C - ‖ρ‖)) 0 := by
  have h0 := profCubeSqIntegrable M hM
  have h2 := profCubeMom2Integrable M hM
  have hpt : ∀ p : E3, fsKinCoeff C ‖ρ + p‖ * (profHatCube M p) ^ 2
      ≤ fsKinCoeff (C - ‖ρ‖) ‖p‖ * (profHatCube M p) ^ 2 :=
    fun p => mul_le_mul_of_nonneg_right (fsKinCoeff_shift_le C ρ p) (sq_nonneg _)
  have hmono : (∫ p : E3, fsKinCoeff C ‖ρ + p‖ * (profHatCube M p) ^ 2)
      ≤ ∫ p : E3, fsKinCoeff (C - ‖ρ‖) ‖p‖ * (profHatCube M p) ^ 2 :=
    integral_mono (integrable_fsKinCoeff_shift_phi_sq h0 h2 C ρ)
      (integrable_fsKinCoeff_phi_sq h0 h2 (C - ‖ρ‖)) hpt
  rw [symACube, symACube]
  simp only [inv_one, one_smul, zero_add]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- **The scaling law of the cube symbol**: for `a > 0`,
`symACube M a (fsKinCoeff (C/a)) q = (a²)⁻¹ · symACube M 1 (fsKinCoeff C) (a • q)`. -/
theorem symACube_scale (M : ℕ) {a C : ℝ} (ha : 0 < a) (q : E3) :
    symACube M a (fsKinCoeff (C / a)) q
      = (a ^ 2)⁻¹ * symACube M 1 (fsKinCoeff C) (a • q) := by
  have hpt : ∀ p : E3, fsKinCoeff (C / a) ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2
      = (a ^ 2)⁻¹ * (fsKinCoeff C ‖a • q + p‖ * (profHatCube M p) ^ 2) := by
    intro p
    have hdecomp : a • q + p = a • (q + a⁻¹ • p) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
    have hnorm : ‖a • q + p‖ = a * ‖q + a⁻¹ • p‖ := by
      rw [hdecomp, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have hkey : fsKinCoeff (C / a) ‖q + a⁻¹ • p‖ = (a ^ 2)⁻¹ * fsKinCoeff C ‖a • q + p‖ := by
      rw [hnorm, fsKinCoeff_mul_scale (a := a) (e := C) ha]
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt ha)), one_mul]
    rw [hkey, mul_assoc]
  rw [symACube, symACube]
  simp only [inv_one, one_smul]
  rw [show (∫ p : E3, fsKinCoeff (C / a) ‖q + a⁻¹ • p‖ * (profHatCube M p) ^ 2)
      = ∫ p : E3, (a ^ 2)⁻¹ * (fsKinCoeff C ‖a • q + p‖ * (profHatCube M p) ^ 2) from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_const_mul]
  ring

/-! ## 6. The target -/

theorem symACube_fsKinCoeff_mix_scaled (M : ℕ) (hM : 1 ≤ M) {a C d ε β : ℝ}
    (ha : 0 < a) (hC : 0 < C) (hd0 : 0 ≤ d) (hd : d ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hM1 : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ t : EuclideanSpace ℝ (Fin 3), (Work.BoseFixB1S.profHatCube M t) ^ 2 * ‖t‖) ≤ C)
    (hM2 : 8 * (((2 * Real.pi) ^ 3)⁻¹ *
        (∫ t : EuclideanSpace ℝ (Fin 3), (Work.BoseFixB1S.profHatCube M t) ^ 2 * ‖t‖ ^ 2))
      ≤ (1 - d) ^ 2 * C ^ 2)
    (htail : Work.BoseFixB1S.symACube M 1 (Submission.BoseGases.fsKinCoeff (C / 2)) 0 ≤ β)
    (q : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1S.symACube M a (Submission.BoseGases.fsKinCoeff (C / a)) q
      ≤ (1 - ε) * Submission.BoseGases.fsKinCoeff (d * C / (2 * a)) ‖q‖
        + ε * Submission.BoseGases.fsKinCoeff (C / (2 * a)) ‖q‖ + β / a ^ 2 := by
  have h0 := profCubeSqIntegrable M hM
  have h2 := profCubeMom2Integrable M hM
  have hnorm := pcProfHatCube_mass_eq M hM
  have htail' : Sym (profHatCube M) (fsKinCoeff (C / 2)) 0 ≤ β := by
    simpa only [Sym, symACube, inv_one, one_smul, zero_add] using htail
  have hcore := cubeTwoCut h0 h2 hnorm hC hd0 hd hε0 hε
    (fun ρ => by simpa only [symACube_one_eq] using cubeSymA_near M hM ρ) hM1 hM2 htail'
  have h1 := hcore (a • q)
  rw [Sym] at h1
  have hsym1 : ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : E3, fsKinCoeff C ‖a • q + p‖ * (profHatCube M p) ^ 2)
      = symACube M 1 (fsKinCoeff C) (a • q) := by
    rw [symACube]
    simp only [inv_one, one_smul]
  rw [hsym1] at h1
  rw [symACube_scale (M := M) (C := C) ha q]
  have hnormq : ‖a • q‖ = a * ‖q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hf1 : fsKinCoeff (d * C / 2) ‖a • q‖ = a ^ 2 * fsKinCoeff (d * C / (2 * a)) ‖q‖ := by
    rw [hnormq, fsKinCoeff_mul_scale (a := a) (e := d * C / 2) ha]
    congr 1
    ring
  have hf2 : fsKinCoeff (C / 2) ‖a • q‖ = a ^ 2 * fsKinCoeff (C / (2 * a)) ‖q‖ := by
    rw [hnormq, fsKinCoeff_mul_scale (a := a) (e := C / 2) ha]
    congr 1
    ring
  refine le_trans (mul_le_mul_of_nonneg_left h1 (by positivity)) ?_
  rw [hf1, hf2]
  refine le_of_eq ?_
  field_simp

end Work.BoseFixB1S
