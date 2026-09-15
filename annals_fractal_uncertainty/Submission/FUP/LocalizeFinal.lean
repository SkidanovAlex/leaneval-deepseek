import Submission.FUP.LocalizeMod
import Submission.FUP.Metric
import Submission.FUP.Damping
import Submission.FUP.HSLocalize
import Submission.Commons.Analysis.Inequalities.final_interpolation
import Submission.Commons.Analysis.Inequalities.exists_R_coeff_small_q1
import Submission.Commons.Analysis.Fourier.finset_bracket_lattice_le
import Submission.Commons.Analysis.Fourier.covering_cube_shift_small
import Submission.Commons.Analysis.Fourier.modulation_average_lintegral
import Submission.Commons.Analysis.Measure.finset_rpow_mul_rpow_sum_le

open FractalUncertainty MeasureTheory Metric Set Complex Filter
open scoped ENNReal BigOperators Topology FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.FUP

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-! ## Elementary helpers -/

/-- The norm of `subLp` is the `eLpNorm` of the indicator. -/
lemma norm_subLp_eq_eLpNorm (S : Set ℝᵈ) (hS : MeasurableSet S)
    (g : Lp ℂ 2 (volume : Measure ℝᵈ)) :
    ‖subLp S g hS‖
      = (eLpNorm (S.indicator (g : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal := by
  rw [subLp, Lp.norm_toLp]

/-- The volume of the symmetric cube `[-c,c]^d`. -/
lemma volume_cube (c : ℝ) (hc : 0 ≤ c) :
    (volume : Measure ℝᵈ) (cube (-c) c) = ENNReal.ofReal ((2 * c) ^ d) := by
  rw [show (cube (-c) c : Set ℝᵈ) = box (fun _ : Fin d => -c) (fun _ : Fin d => c) from rfl,
    volume_box]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show c - -c = 2 * c by ring, ← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 2 * c)]

/-- The cube `[a,b]^d` is measurable. -/
lemma measurableSet_cube (a b : ℝ) : MeasurableSet (cube a b : Set ℝᵈ) := by
  have h : (cube a b : Set ℝᵈ) = box (fun _ : Fin d => a) (fun _ : Fin d => b) := by
    ext x; rw [mem_cube_iff, mem_box]; simp only [Set.mem_Icc]
  rw [h]; exact measurableSet_box _ _

/-- Translation in a set integral: `∫_{s} h (x + c) = ∫_{s + c} h`. -/
lemma setIntegral_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : ℝᵈ → E} (c : ℝᵈ) {s : Set ℝᵈ} (hs : MeasurableSet s) :
    ∫ x in s, h (x + c) = ∫ y in {y : ℝᵈ | y - c ∈ s}, h y := by
  have hmem : MeasurableSet {y : ℝᵈ | y - c ∈ s} := hs.preimage (by measurability)
  have hmp : MeasurePreserving (fun x : ℝᵈ => x + c) (volume : Measure ℝᵈ) volume :=
    measurePreserving_add_right _ _
  have key := hmp.integral_comp (Homeomorph.addRight c).measurableEmbedding
    (fun y : ℝᵈ => {y : ℝᵈ | y - c ∈ s}.indicator h y)
  rw [← integral_indicator hs, ← integral_indicator hmem]
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show s.indicator (fun x => h (x + c)) x = {y : ℝᵈ | y - c ∈ s}.indicator h (x + c)
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (show x + c ∈ {y : ℝᵈ | y - c ∈ s} from by simpa using hx)]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x + c ∉ {y : ℝᵈ | y - c ∈ s} from
        fun hh => hx (by simpa using hh))]

/-- **Plancherel on a cube containing the frequency support.** -/
lemma plancherel_cube {α₁ : ℝ} {f : Lp ℂ 2 (volume : Measure ℝᵈ)}
    (hfY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 →
        ξ ∈ cube (-α₁) α₁) :
    ∫ x in cube (-α₁) α₁,
        ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2 = ‖f‖ ^ 2 := by
  set g : ℝᵈ → ℝ := fun x =>
    ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2 with hg
  have hcube : MeasurableSet (cube (-α₁) α₁ : Set ℝᵈ) := measurableSet_cube _ _
  have hae : g =ᵐ[volume] (cube (-α₁) α₁ : Set ℝᵈ).indicator g := by
    filter_upwards [hfY] with x hx
    by_cases h : x ∈ cube (-α₁) α₁
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, hg]
      simp only
      rw [show ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x = 0 from
        by_contra (fun hne => h (hx hne))]
      simp
  calc ∫ x in cube (-α₁) α₁, g x
      = ∫ x, (cube (-α₁) α₁ : Set ℝᵈ).indicator g x :=
        (integral_indicator hcube).symm
    _ = ∫ x, g x := integral_congr_ae hae.symm
    _ = ‖(𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ))‖ ^ 2 := (norm_sq_eq_integral (𝓕 f)).symm
    _ = ‖f‖ ^ 2 := by rw [MeasureTheory.Lp.norm_fourier_eq]

/-- The sup norm on the coefficient space is bounded by the Euclidean norm. -/
lemma pi_norm_le_euclidean (v : ℝᵈ) : ‖v.ofLp‖ ≤ ‖v‖ := by
  rw [Pi.norm_def]
  rw [show ‖v‖ = ((‖v‖₊ : NNReal) : ℝ) from rfl]
  rw [NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  exact PiLp.norm_apply_le v i

/-- The damping bound implies `‖ψ‖ ≤ 1` pointwise a.e. -/
lemma bracket_rpow_neg_le_one (x : ℝᵈ) : bracket x ^ (-(d : ℝ)) ≤ 1 := by
  refine Real.rpow_le_one_of_one_le_of_nonpos (x := bracket x) (z := -(d : ℝ)) ?_ ?_
  · rw [bracket]
    exact Real.one_le_sqrt.mpr (by nlinarith [sq_nonneg ‖x‖])
  · exact neg_nonpos.mpr (Nat.cast_nonneg d)

/-! ## The modulation step: P2 + the window bound -/

/-- **The `L²` mass of `𝓕f` on the unit cube, bounded via the window estimate.**
This is the last display of Han–Schlag's Lemma 4.3 combined with the modulation average. -/
lemma modulation_step {fM : Lp ℂ 2 (volume : Measure ℝᵈ)} {ψ : Lp ℂ 2 (volume : Measure ℝᵈ)}
    {c₂ BOUND : ℝ} (hc₂ : 0 ≤ c₂) (hBOUND : 0 ≤ BOUND)
    (hψnorm : c₂ ^ 2 ≤ ∫ x in cube (-1) 1, ‖(ψ : ℝᵈ → ℂ) x‖ ^ 2)
    (hψb : ∀ᵐ x ∂(volume : Measure ℝᵈ), ‖(ψ : ℝᵈ → ℂ) x‖ ≤ 1)
    (hwin : ∀ η : ℝᵈ, (∀ i : Fin d, |η i| ≤ 2) →
      ∫ ξ, ‖winP fM η ξ * (ψ : ℝᵈ → ℂ) ξ‖ ^ 2 ≤ BOUND) :
    c₂ ^ 2 * (∫ x in cube (-1) 1,
        ‖((𝓕 fM : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2)
      ≤ 4 ^ d * BOUND := by
  classical
  set F : ℝᵈ → ℂ := ((𝓕 fM : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) with hF
  set Ψ : ℝᵈ → ℂ := (ψ : ℝᵈ → ℂ) with hΨ
  have hFm : MemLp F 2 (volume : Measure ℝᵈ) := by rw [hF]; exact Lp.memLp (𝓕 fM)
  have hΨm : MemLp Ψ 2 (volume : Measure ℝᵈ) := by rw [hΨ]; exact Lp.memLp ψ
  have hFint : Integrable (fun x : ℝᵈ => ‖F x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).mp hFm
  have hK1 : (cube (-1) 1 : Set ℝᵈ) = {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1} := by
    ext x; exact mem_cube_iff (-1) 1 x
  have hK2 : (cube (-2) 2 : Set ℝᵈ) = {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2} := by
    ext x; exact mem_cube_iff (-2) 2 x
  have hψnorm' : c₂ ^ 2 ≤ ∫ ξ in {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}, ‖Ψ ξ‖ ^ 2 := by
    rw [← hK1]; rw [hΨ]; exact hψnorm
  have hP2 := Commons.Analysis.Fourier.modulation_average_lintegral (d := d) hc₂
    (F := F) (Ψ := Ψ) hFm hΨm hψnorm'
  -- LHS conversion
  have hLHS : ∫⁻ θ in {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1},
        ENNReal.ofReal (‖F θ‖ ^ 2)
      = ENNReal.ofReal (∫ θ in {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}, ‖F θ‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hFint.integrableOn
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))).symm
  -- inner bound
  have hinner : ∀ η : ℝᵈ, (∀ i : Fin d, |η i| ≤ 2) →
      ∫⁻ ξ, ENNReal.ofReal (‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2) ≤ ENNReal.ofReal BOUND := by
    intro η hη
    have hmp : MeasurePreserving (fun x : ℝᵈ => x - η) (volume : Measure ℝᵈ) volume :=
      measurePreserving_sub_right _ _
    have hFAE : AEStronglyMeasurable F (Measure.map (fun x : ℝᵈ => x - η) volume) := by
      rw [hmp.map_eq]; exact hFm.aestronglyMeasurable
    have hmeas : AEStronglyMeasurable (fun ξ : ℝᵈ => ‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2) volume :=
      ((hFAE.comp_measurable (measurable_id.sub measurable_const)).norm.pow 2).mul
        (hΨm.aestronglyMeasurable.norm.pow 2)
    have hint : Integrable (fun ξ : ℝᵈ => ‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2) volume := by
      refine Integrable.mono' (hFint.comp_sub_right η) hmeas ?_
      · filter_upwards [hψb] with ξ hξ
        rw [hΨ] at hξ
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc ‖F (ξ - η)‖ ^ 2 * ‖(ψ : ℝᵈ → ℂ) ξ‖ ^ 2
            ≤ ‖F (ξ - η)‖ ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left (by nlinarith [hξ, norm_nonneg ((ψ : ℝᵈ → ℂ) ξ)])
                (by positivity)
          _ = ‖F (ξ - η)‖ ^ 2 := by ring
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun x => by positivity))]
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : (∫ ξ, ‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2)
        = ∫ ξ, ‖winP fM η ξ * (ψ : ℝᵈ → ℂ) ξ‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show ‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2 = ‖winP fM η ξ * (ψ : ℝᵈ → ℂ) ξ‖ ^ 2
      rw [show ‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2 = ‖F (ξ - η) * Ψ ξ‖ ^ 2 by
        rw [Complex.norm_mul, mul_pow], hΨ]
      rw [show F (ξ - η) = winP fM η ξ from rfl]
    rw [heq]
    exact hwin η hη
  -- outer bound
  have hK2meas : MeasurableSet {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2} := by
    rw [← hK2]; exact measurableSet_cube _ _
  have houter : ∫⁻ η in {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2},
        ∫⁻ ξ, ENNReal.ofReal (‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2)
      ≤ ENNReal.ofReal BOUND * (volume : Measure ℝᵈ) {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2} := by
    calc _ ≤ ∫⁻ _η in {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2}, ENNReal.ofReal BOUND := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hK2meas]
          filter_upwards with η hη
          exact hinner η (fun i => abs_le.mpr ⟨(hη i).1, (hη i).2⟩)
      _ = ENNReal.ofReal BOUND * (volume : Measure ℝᵈ) {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2} :=
          setLIntegral_const _ _
  have h4d : (volume : Measure ℝᵈ) {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2}
      = ENNReal.ofReal ((4 : ℝ) ^ d) := by
    rw [← hK2, volume_cube 2 (by norm_num)]
    norm_num
  have hfin : ENNReal.ofReal (c₂ ^ 2 * (∫ x in cube (-1) 1,
        ‖((𝓕 fM : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2))
      ≤ ENNReal.ofReal ((4 : ℝ) ^ d * BOUND) := by
    have hA : (∫ x in cube (-1) 1,
        ‖((𝓕 fM : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2)
        = ∫ x in {y : ℝᵈ | ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1}, ‖F x‖ ^ 2 := by
      rw [hK1, show ((𝓕 fM : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) = F from hF.symm]
    rw [hA]
    calc ENNReal.ofReal (c₂ ^ 2 * ∫ x in {y : ℝᵈ | ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1}, ‖F x‖ ^ 2)
        = ENNReal.ofReal (c₂ ^ 2)
            * ENNReal.ofReal (∫ x in {y : ℝᵈ | ∀ i, y i ∈ Set.Icc (-1 : ℝ) 1}, ‖F x‖ ^ 2) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (c₂ ^ 2)
            * ∫⁻ θ in {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1}, ENNReal.ofReal (‖F θ‖ ^ 2) := by
          rw [hLHS]
      _ ≤ ∫⁻ η in {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2},
            ∫⁻ ξ, ENNReal.ofReal (‖F (ξ - η)‖ ^ 2 * ‖Ψ ξ‖ ^ 2) := hP2
      _ ≤ ENNReal.ofReal BOUND * (volume : Measure ℝᵈ) {x : ℝᵈ | ∀ i, x i ∈ Set.Icc (-2 : ℝ) 2} :=
          houter
      _ = ENNReal.ofReal BOUND * ENNReal.ofReal ((4 : ℝ) ^ d) := by rw [h4d]
      _ = ENNReal.ofReal (BOUND * (4 : ℝ) ^ d) := (ENNReal.ofReal_mul hBOUND).symm
      _ = ENNReal.ofReal ((4 : ℝ) ^ d * BOUND) := by ring_nf
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hfin

/-! ## The translation of the modulated cube integral -/

/-- **The mass of `𝓕(f_m)` on the unit cube is the mass of `𝓕f` on the translated cube.** -/
lemma integral_fourier_modFun_cube (f : Lp ℂ 2 (volume : Measure ℝᵈ)) (m : Fin d → ℤ) :
    ∫ x in cube (-1) 1,
        ‖((𝓕 ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ)))
          : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2
      = ∫ y in {y : ℝᵈ | y + ellVec m ∈ cube (-1) 1},
          ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y‖ ^ 2 := by
  have hset : {y : ℝᵈ | y + ellVec m ∈ cube (-1) 1}
      = {y : ℝᵈ | y - (-ellVec m) ∈ cube (-1) 1} := by
    ext y
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, show y + ellVec m = y - (-ellVec m) by abel]
  have hcomp := setIntegral_comp_add
    (h := fun y : ℝᵈ => ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y‖ ^ 2)
    (-ellVec m) (measurableSet_cube (-1) 1)
  rw [hset, ← hcomp]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (fourier_modFun (m := m) (Lp.memLp f))] with x hx
  rw [show x + -ellVec m = x - ellVec m by abel]
  rw [hx, Lp.toLp_coeFn f (Lp.memLp f)]

/-! ## The per-cell window step -/

/-- **The per-cell estimate.**  Combining the modulation average (P2) with the single-window
estimate `window_bound_of_damping` for the modulation index `m`: the `L²` mass of `𝓕f` on the
translated unit cube is bounded by `4^d` times the window bound, in the cleaned form in which the
constants `B = cellZConst …`, `U = windowD …`, `CW = windowCW …`, `κ = zpKappa …`, `t = truncBeta …`
appear. -/
lemma window_step {q ε δ H ηL r c₁ c₃ α R B U t CW κ c₂ : ℝ} (hd : 1 ≤ d)
    (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hηL0 : 0 < ηL) (hc₁ : 0 < c₁) (hr0 : 0 < r)
    (hητ : 1 ≤ ηL * phiLens q ε (1 - 3 * δ))
    (hIbig : ENNReal.ofReal ((ηL * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((c₁ / 2) ^ d))
    (hc₃ : 0 < c₃) (hα0 : 0 < α) (hα1 : α ≤ 1) (hR0 : 0 < R) (hR1 : 1 ≤ R)
    (hRc : (2 * (d : ℝ) / c₃) ^ 2 ≤ R)
    (hQ4 : 4 * Real.pi * windowQ ηL q r ≤ c₃ * (Real.log (2 + R)) ^ (-α))
    (hc₂ : 0 < c₂)
    (hB : B = cellZConst q ε δ H ηL (c₁ / 4) d) (hU : U = windowD d q ε ηL r)
    (ht : t = truncBeta d c₃ α R) (hCW : CW = windowCW d) (hκ : κ = zpKappa δ H d)
    {f : Lp ℂ 2 (volume : Measure ℝᵈ)} {Y Z : Set ℝᵈ} {m : Fin d → ℤ}
    (hdamp : AdmitsL1Damping Z (c₁ / 2) c₂ c₃ α)
    (hfY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y)
    (hZY : ∀ y ∈ Y, ∀ η : ℝᵈ, (∀ i : Fin d, |η i| ≤ 2) → ellVec m + η + y ∈ Z)
    {γ : ℝᵈ} {a : (Fin d → ℤ) → Fin d → ℝ}
    (ha : ∀ n : Fin d → ℤ, ∀ i : Fin d,
      2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) :
    c₂ ^ 2 * (∫ y in {y : ℝᵈ | y + ellVec m ∈ cube (-1) 1},
        ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y‖ ^ 2)
      ≤ 4 ^ d * (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
          * (hsq ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ)))) ^ (1 - κ)
          * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a)
                ((memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ)))
                (measurableSet_locCubes c₁ a))
            + 2 * t ^ 2 * CW ^ 2 * hsq ((memLp_modFun (m := m) (Lp.memLp f)).toLp
                (modFun m (f : ℝᵈ → ℂ)))) ^ κ
          + t ^ 2 * CW * hsq ((memLp_modFun (m := m) (Lp.memLp f)).toLp
              (modFun m (f : ℝᵈ → ℂ)))) := by
  classical
  set fM : Lp ℂ 2 (volume : Measure ℝᵈ) :=
    (memLp_modFun (m := m) (Lp.memLp f)).toLp (modFun m (f : ℝᵈ → ℂ)) with hfM
  obtain ⟨ψ, hψsupp0, hψnorm0, hψw0, hψdec0⟩ := hdamp
  -- the support of `𝓕ψ` in the form used by `window_bound`
  have hψsupp : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), (∃ i : Fin d, c₁ / 2 < |ξ i|) →
      ((𝓕 ψ : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0 := by
    filter_upwards [hψsupp0] with ξ hξ hlt
    refine hξ (fun hc => ?_)
    rw [mem_cube_iff] at hc
    obtain ⟨i, hi⟩ := hlt
    exact absurd (abs_le.mpr ⟨(hc i).1, (hc i).2⟩) (not_le.mpr hi)
  -- the weight bound in the form used by `window_bound`
  have hψw : ∀ᵐ x ∂(volume : Measure ℝᵈ),
      ‖(ψ : ℝᵈ → ℂ) x‖ ≤ (1 + ‖x‖ ^ 2) ^ (-(d : ℝ) / 2) := by
    filter_upwards [hψw0] with x hx
    rwa [bracket_pow] at hx
  -- the window bound for every `η ∈ [-2,2]^d`
  have hwin : ∀ η : ℝᵈ, (∀ i : Fin d, |η i| ≤ 2) →
      ∫ ξ, ‖winP fM η ξ * (ψ : ℝᵈ → ℂ) ξ‖ ^ 2
        ≤ cellZConst q ε δ H ηL (c₁ / 4) d
          * (windowD d q ε ηL r * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d
              * (windowCW d * hsq fM)))) ^ (1 - zpKappa δ H d)
          * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a))
              + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq fM) ^ (zpKappa δ H d)
          + (truncBeta d c₃ α R) ^ 2 * windowCW d * hsq fM := by
    intro η hη
    exact window_bound_of_damping (d := d) (q := q) (ε := ε) (δ := δ) (H := H) (ηL := ηL)
      (r := r) (c₁ := c₁) (c₃ := c₃) (α := α) (R := R) hd hq hε0 hε1 hδ0 hδ3 hH0 hH1 hηL0
      hc₁ hr0 hητ hIbig hc₃ hα0 hα1 hR0 hR1 hRc hQ4 hψsupp hψw hψdec0 (hηm := hη) hfY
      (hZY := fun y hy => hZY y hy η hη) ha
  -- the bound in the cleaned form
  have hclean : cellZConst q ε δ H ηL (c₁ / 4) d
        * (windowD d q ε ηL r * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d
            * (windowCW d * hsq fM)))) ^ (1 - zpKappa δ H d)
        * (2 * (windowCW d) ^ 2 * hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a))
            + 2 * (truncBeta d c₃ α R) ^ 2 * (windowCW d) ^ 2 * hsq fM) ^ (zpKappa δ H d)
        + (truncBeta d c₃ α R) ^ 2 * windowCW d * hsq fM
      = B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
          * (hsq fM) ^ (1 - κ)
          * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a))
              + 2 * t ^ 2 * CW ^ 2 * hsq fM) ^ κ
          + t ^ 2 * CW * hsq fM := by
    have hxnn : 0 ≤ hsq fM := hsq_nonneg fM
    have hAnn : 0 ≤ U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW)) := by
      have hUpos : 0 < U := by
        rw [hU]; exact windowD_pos hηL0 hr0 hq hε0 (by linarith)
      have hQpos : 0 < windowQ ηL q r := by rw [windowQ]; positivity
      have hCWpos : 0 < CW := by rw [hCW]; exact windowCW_pos d
      positivity
    have hmul : (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * (CW * hsq fM))))
        = (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) * hsq fM := by ring
    rw [← hB, ← hU, ← hCW, ← hκ, ← ht, hmul, Real.mul_rpow hAnn hxnn]
    ring_nf
  rw [hclean] at hwin
  -- nonnegativity of the bound
  have hbnd_nn : 0 ≤ B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
        * (hsq fM) ^ (1 - κ)
        * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a))
            + 2 * t ^ 2 * CW ^ 2 * hsq fM) ^ κ + t ^ 2 * CW * hsq fM := by
    have hBpos : 0 < B := by
      rw [hB]; exact cellZConst_pos q ε δ H ηL (c₁ / 4) d hδ0 hδ3 hq hε0 hε1 hηL0
        (by linarith)
    have hUpos : 0 < U := by
      rw [hU]; exact windowD_pos hηL0 hr0 hq hε0 (by linarith)
    have hCWpos : 0 < CW := by rw [hCW]; exact windowCW_pos d
    have hQpos : 0 < windowQ ηL q r := by rw [windowQ]; positivity
    have htnn : 0 ≤ t := by rw [ht]; exact truncBeta_nonneg d c₃ α R
    have hAnn : 0 ≤ U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW)) := by positivity
    have hxnn : 0 ≤ hsq fM := hsq_nonneg fM
    have hsub : 0 ≤ hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a)) :=
      hsq_nonneg _
    have h1 : 0 ≤ (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ) :=
      Real.rpow_nonneg hAnn _
    have hx1 : 0 ≤ (hsq fM) ^ (1 - κ) := Real.rpow_nonneg hxnn _
    have h2 : 0 ≤ (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a))
        + 2 * t ^ 2 * CW ^ 2 * hsq fM) ^ κ :=
      Real.rpow_nonneg (by positivity) _
    have h3 : 0 ≤ t ^ 2 * CW * hsq fM := by positivity
    have h4 : 0 ≤ B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
        * (hsq fM) ^ (1 - κ)
        * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a))
            + 2 * t ^ 2 * CW ^ 2 * hsq fM) ^ κ :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hBpos) h1) hx1) h2
    linarith
  -- the `L²` bound on the unit cube
  have hψb : ∀ᵐ x ∂(volume : Measure ℝᵈ), ‖(ψ : ℝᵈ → ℂ) x‖ ≤ 1 := by
    filter_upwards [hψw0] with x hx
    exact hx.trans (bracket_rpow_neg_le_one x)
  have hstep := modulation_step (fM := fM) (ψ := ψ) (c₂ := c₂)
    (BOUND := B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
        * (hsq fM) ^ (1 - κ)
        * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) fM (measurableSet_locCubes c₁ a))
            + 2 * t ^ 2 * CW ^ 2 * hsq fM) ^ κ + t ^ 2 * CW * hsq fM)
    (le_of_lt hc₂) hbnd_nn hψnorm0 hψb hwin
  -- convert the cube integral
  have htrans := integral_fourier_modFun_cube (f := f) (m := m)
  rw [hfM] at hstep
  rw [htrans] at hstep
  exact hstep

lemma shiftSet_eq (m : Fin d → ℤ) :
    {x : ℝᵈ | ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1}
      = {y : ℝᵈ | y + ellVec (-m) ∈ cube (-1) 1} := by
  ext y
  show (∀ i : Fin d, |y i - 2 * (m i : ℝ)| ≤ 1)
      ↔ y + ellVec (-m) ∈ cube (-1) 1
  rw [mem_cube_iff]
  have hkey : ∀ i : Fin d, (y + ellVec (-m)).ofLp i = y.ofLp i - 2 * (m i : ℝ) := by
    intro i
    simp only [WithLp.ofLp_add, Pi.add_apply, ellVec_apply, Pi.neg_apply, Int.cast_neg]
    ring
  simp only [hkey, Set.mem_Icc]
  constructor
  · intro h i
    exact abs_le.mp (h i)
  · intro h i
    rw [abs_le]
    exact h i

/-- **Han–Schlag's Corollary 4.2 from the explicit parameters.** -/
theorem localisation_bound_of_params {c₁ c₂ c₃ α : ℝ} (hd : 1 ≤ d)
    (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₂ : 0 < c₂) (hc₂1 : c₂ < 1) (hc₃ : 0 < c₃)
    (hα0 : 0 < α) (hα1 : α < 1) {Clat : ℝ} (hClat : 1 ≤ Clat)
    (hC₀ : ∀ (η : ℝᵈ) (s : Finset (Fin d → ℤ)),
      (∑ m ∈ s, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ))) ≤ Clat)
    {R q ε δ H ηL r κ CW B U t : ℝ}
    (hR2 : 2 ≤ R) (hRc : (2 * (d : ℝ) / c₃) ^ 2 ≤ R)
    (hq : 0 < q) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2) (hδ0 : 0 < δ) (hδ3 : δ < 1 / 3)
    (hH0 : 0 < H) (hH1 : H ≤ 1) (hηL0 : 0 < ηL) (hr0 : 0 < r)
    (hητ : 1 ≤ ηL * phiLens q ε (1 - 3 * δ))
    (hQ4 : 4 * Real.pi * windowQ ηL q r ≤ c₃ * (Real.log (2 + R)) ^ (-α))
    (hIbig : ENNReal.ofReal ((ηL * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((c₁ / 2) ^ d))
    (hCW : CW = windowCW d) (hκ : κ = zpKappa δ H d)
    (hB : B = cellZConst q ε δ H ηL (c₁ / 4) d)
    (hU : U = windowD d q ε ηL r) (ht : t = truncBeta d c₃ α R)
    (hsmall : (4 : ℝ) ^ d * (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
        * Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ * t ^ (2 * κ) + t ^ 2 * CW * Clat)
        ≤ c₂ ^ 2 / 2) :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ (α₁ : ℝ), 1 ≤ α₁ → ∀ (γ : ℝᵈ) (Y : Set ℝᵈ),
        Y ⊆ cube (-α₁) α₁ →
        (∀ η : ℝᵈ, (∀ i : Fin d, η i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1)) →
          AdmitsL1Damping ((fun z : ℝᵈ => η + z) '' (addSet Y (cube (-2) 2))) (c₁ / 2) c₂ c₃ α) →
        ∀ (a : (Fin d → ℤ) → Fin d → ℝ),
          (∀ n : Fin d → ℤ, ∀ i : Fin d,
            2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) →
          ∀ (f : Lp ℂ 2 (volume : Measure ℝᵈ)),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
                ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) →
            ‖f‖ ≤ Cstar * (eLpNorm
              ((⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + 2 * c₁)).indicator
                (f : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal := by
  classical
  have hκmem := twoConstKappa_mem hδ0 hδ3 hH0 hH1
  have hκpos : 0 < κ := by rw [hκ, zpKappa]; exact pow_pos hκmem.1 d
  have hκle : κ ≤ 1 := by rw [hκ, zpKappa]; exact pow_le_one₀ (le_of_lt hκmem.1) hκmem.2
  have hBpos : 0 < B := by
    rw [hB]; exact cellZConst_pos q ε δ H ηL (c₁ / 4) d hδ0 hδ3 hq hε0 hε1 hηL0 (by linarith)
  have hUpos : 0 < U := by
    rw [hU]; exact windowD_pos hηL0 hr0 hq hε0 (by linarith)
  have hCWpos : 0 < CW := by rw [hCW]; exact windowCW_pos d
  have hQpos : 0 < windowQ ηL q r := by rw [windowQ]; positivity
  have htnn : 0 ≤ t := by rw [ht]; exact truncBeta_nonneg d c₃ α R
  have hAnnpos : 0 < U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW)) := by positivity
  refine ⟨(2 * (4 : ℝ) ^ d
      * (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ))
      * Clat ^ (1 - κ) * (2 * CW ^ 2 * Clat) ^ κ / c₂ ^ 2) ^ (1 / (2 * κ)), ?_, ?_⟩
  · refine Real.rpow_pos_of_pos ?_ _
    have hClatpos : 0 < Clat := lt_of_lt_of_le one_pos hClat
    have h1 : 0 < B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ) :=
      mul_pos hBpos (Real.rpow_pos_of_pos hAnnpos _)
    have h2 : 0 < Clat ^ (1 - κ) := Real.rpow_pos_of_pos hClatpos _
    have h3 : 0 < (2 * CW ^ 2 * Clat) ^ κ := Real.rpow_pos_of_pos (by positivity) _
    positivity
  · intro α₁ hα₁ γ Y hYsub hdamp a ha f hfY
    have hsupp : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
        ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ cube (-α₁) α₁ := by
      filter_upwards [hfY] with ξ hξ hne
      exact hYsub (hξ hne)
    obtain ⟨s, hs_small, hs_cover⟩ := Commons.Analysis.Fourier.covering_cube_shift_small d hα₁
    set fM : (Fin d → ℤ) → Lp ℂ 2 (volume : Measure ℝᵈ) := fun m =>
      (memLp_modFun (m := -m) (Lp.memLp f)).toLp (modFun (-m) (f : ℝᵈ → ℂ)) with hfM
    have hcell : ∀ m ∈ s, c₂ ^ 2 * (∫ y in {y : ℝᵈ | y + ellVec (-m) ∈ cube (-1) 1},
          ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y‖ ^ 2)
        ≤ 4 ^ d * (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (hsq (fM m)) ^ (1 - κ)
            * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ
            + t ^ 2 * CW * hsq (fM m)) := by
      intro m hm
      have hηcond : ∀ i : Fin d, ellVec (-m) i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1) := by
        intro i
        rw [ellVec_apply, Pi.neg_apply, Int.cast_neg]
        have h := abs_le.mp (hs_small m hm i)
        exact ⟨by linarith [h.1], by linarith [h.2]⟩
      refine window_step (d := d) (q := q) (ε := ε) (δ := δ) (H := H) (ηL := ηL) (r := r)
        (c₁ := c₁) (c₃ := c₃) (α := α) (R := R) (B := B) (U := U) (t := t) (CW := CW)
        (κ := κ) (c₂ := c₂) hd hq hε0 hε1 hδ0 hδ3 hH0 hH1 hηL0 hc₁ hr0 hητ hIbig
        hc₃ hα0 (le_of_lt hα1) (by linarith) (by linarith) hRc hQ4 hc₂ hB hU ht hCW hκ
        (f := f) (Y := Y)
        (Z := (fun z : ℝᵈ => ellVec (-m) + z) '' (addSet Y (cube (-2) 2)))
        (m := -m) (γ := γ) (a := a) (hdamp (ellVec (-m)) hηcond) hfY ?_ ha
      intro y hy η hη
      refine ⟨y + η, ⟨y, hy, η, ?_, rfl⟩, ?_⟩
      · rw [mem_cube_iff]
        intro i
        exact abs_le.mp (hη i)
      · abel
    -- the covering sum
    have hcover0 := hs_cover (fun x : ℝᵈ =>
      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x) (Lp.memLp (𝓕 f))
    have hseteq : ∀ m : Fin d → ℤ,
        {x : ℝᵈ | ∀ i : Fin d, |x i - 2 * (m i : ℝ)| ≤ 1}
          = {y : ℝᵈ | y + ellVec (-m) ∈ cube (-1) 1} := fun m => shiftSet_eq m
    simp only [hseteq] at hcover0
    have hcover : (∫ x in cube (-α₁) α₁,
          ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2)
        ≤ ∑ m ∈ s, ∫ y in {y : ℝᵈ | y + ellVec (-m) ∈ cube (-1) 1},
            ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y‖ ^ 2 := by
      rw [show (cube (-α₁) α₁ : Set ℝᵈ)
          = {x : ℝᵈ | ∀ i : Fin d, -α₁ ≤ x i ∧ x i ≤ α₁} from by
        ext x; simp only [Set.mem_ofPred_eq, mem_cube]]
      exact hcover0
    have hpl := plancherel_cube (α₁ := α₁) (f := f) hsupp
    -- the L² bound
    have hmain_le : c₂ ^ 2 * ‖f‖ ^ 2
        ≤ 4 ^ d * ∑ m ∈ s, (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (hsq (fM m)) ^ (1 - κ)
            * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ
            + t ^ 2 * CW * hsq (fM m)) := by
      rw [← hpl]
      calc c₂ ^ 2 * (∫ x in cube (-α₁) α₁,
              ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) x‖ ^ 2)
          ≤ c₂ ^ 2 * (∑ m ∈ s, ∫ y in {y : ℝᵈ | y + ellVec (-m) ∈ cube (-1) 1},
              ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left hcover (by positivity)
        _ = ∑ m ∈ s, c₂ ^ 2 * (∫ y in {y : ℝᵈ | y + ellVec (-m) ∈ cube (-1) 1},
              ‖((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) y‖ ^ 2) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ m ∈ s, 4 ^ d * (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (hsq (fM m)) ^ (1 - κ)
            * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ
            + t ^ 2 * CW * hsq (fM m)) :=
            Finset.sum_le_sum hcell
        _ = 4 ^ d * ∑ m ∈ s, (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (hsq (fM m)) ^ (1 - κ)
            * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ
            + t ^ 2 * CW * hsq (fM m)) := by
            rw [Finset.mul_sum]
    -- the lattice sums
    have hsum_x : (∑ m ∈ s, hsq (fM m)) ≤ Clat * ‖f‖ ^ 2 := by
      have h := sum_hsq_mod_le (d := d) Clat hC₀ (f : ℝᵈ → ℂ) (Lp.memLp f)
        (s.image (fun m : Fin d → ℤ => -m))
      rw [Finset.sum_image] at h
      · rw [Lp.toLp_coeFn f (Lp.memLp f)] at h
        simpa only [hfM] using h
      · intro a _ b _ hab; simpa using congrArg Neg.neg hab
    have hsum_s : (∑ m ∈ s, hsq (subLp (locCubes c₁ a) (fM m)
          (measurableSet_locCubes c₁ a))) ≤ Clat * ‖subLp (locCubes c₁ a) f
            (measurableSet_locCubes c₁ a)‖ ^ 2 := by
      have h := sum_hsq_subLp_modFun_le (d := d) Clat hC₀ f (locCubes c₁ a)
        (measurableSet_locCubes c₁ a) (s.image (fun m : Fin d → ℤ => -m))
      rw [Finset.sum_image] at h
      · simpa only [hfM] using h
      · intro a _ b _ hab; simpa using congrArg Neg.neg hab
    have hsum_y : (∑ m ∈ s, (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m)
            (measurableSet_locCubes c₁ a)) + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)))
        ≤ 2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2
          + 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2 := by
      have heq : (∑ m ∈ s, (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m)
              (measurableSet_locCubes c₁ a)) + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)))
          = 2 * CW ^ 2 * (∑ m ∈ s, hsq (subLp (locCubes c₁ a) (fM m)
              (measurableSet_locCubes c₁ a)))
            + 2 * t ^ 2 * CW ^ 2 * (∑ m ∈ s, hsq (fM m)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      rw [heq]
      have h3 : 2 * CW ^ 2 * (∑ m ∈ s, hsq (subLp (locCubes c₁ a) (fM m)
            (measurableSet_locCubes c₁ a)))
          ≤ 2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2 :=
        (mul_le_mul_of_nonneg_left hsum_s (by positivity)).trans_eq (by ring)
      have h4 : 2 * t ^ 2 * CW ^ 2 * (∑ m ∈ s, hsq (fM m))
          ≤ 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2 :=
        (mul_le_mul_of_nonneg_left hsum_x (by positivity)).trans_eq (by ring)
      linarith [h3, h4]
    -- Hölder
    have hholder : (∑ m ∈ s, (hsq (fM m)) ^ (1 - κ)
          * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
              + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ)
        ≤ (∑ m ∈ s, hsq (fM m)) ^ (1 - κ)
          * (∑ m ∈ s, (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m)
              (measurableSet_locCubes c₁ a)) + 2 * t ^ 2 * CW ^ 2 * hsq (fM m))) ^ κ := by
      exact Commons.Analysis.Measure.finset_rpow_mul_rpow_sum_le s
        (fun m => hsq (fM m))
        (fun m => 2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
          + 2 * t ^ 2 * CW ^ 2 * hsq (fM m))
        (fun m => hsq_nonneg _)
        (fun m => by
          have h1 := hsq_nonneg (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
          have h2 := hsq_nonneg (fM m)
          positivity)
        hκpos hκle
    -- assemble
    have hA0nn : 0 ≤ B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ) :=
      le_of_lt (mul_pos hBpos (Real.rpow_pos_of_pos hAnnpos _))
    have hxsum_nn : 0 ≤ ∑ m ∈ s, hsq (fM m) := Finset.sum_nonneg fun m _ => hsq_nonneg _
    have hysum_nn : 0 ≤ ∑ m ∈ s, (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m)
        (measurableSet_locCubes c₁ a)) + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) := by
      refine Finset.sum_nonneg fun m _ => ?_
      have h1 := hsq_nonneg (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
      have h2 := hsq_nonneg (fM m)
      positivity
    have hsplit : (∑ m ∈ s, (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (hsq (fM m)) ^ (1 - κ)
            * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ
            + t ^ 2 * CW * hsq (fM m)))
        = B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (∑ m ∈ s, (hsq (fM m)) ^ (1 - κ)
              * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                  + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ)
          + t ^ 2 * CW * (∑ m ∈ s, hsq (fM m)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
      · rw [Finset.mul_sum]
    have hstep1 : B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
          * (∑ m ∈ s, (hsq (fM m)) ^ (1 - κ)
            * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ)
        ≤ B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * ((∑ m ∈ s, hsq (fM m)) ^ (1 - κ)
              * (∑ m ∈ s, (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m)
                  (measurableSet_locCubes c₁ a)) + 2 * t ^ 2 * CW ^ 2 * hsq (fM m))) ^ κ) :=
      mul_le_mul_of_nonneg_left hholder hA0nn
    have hxpow : (∑ m ∈ s, hsq (fM m)) ^ (1 - κ) ≤ (Clat * ‖f‖ ^ 2) ^ (1 - κ) :=
      Real.rpow_le_rpow hxsum_nn hsum_x (by linarith)
    have hypow : (∑ m ∈ s, (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m)
          (measurableSet_locCubes c₁ a)) + 2 * t ^ 2 * CW ^ 2 * hsq (fM m))) ^ κ
        ≤ (2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2
            + 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2) ^ κ :=
      Real.rpow_le_rpow hysum_nn hsum_y (le_of_lt hκpos)
    have hstep2 : B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * ((∑ m ∈ s, hsq (fM m)) ^ (1 - κ)
              * (∑ m ∈ s, (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m)
                  (measurableSet_locCubes c₁ a)) + 2 * t ^ 2 * CW ^ 2 * hsq (fM m))) ^ κ)
        ≤ B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * ((Clat * ‖f‖ ^ 2) ^ (1 - κ)
              * (2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2
                  + 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2) ^ κ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hxpow hypow (Real.rpow_nonneg hysum_nn _)
          (Real.rpow_nonneg (by positivity) _)) hA0nn
    have hstep3 : t ^ 2 * CW * (∑ m ∈ s, hsq (fM m)) ≤ t ^ 2 * CW * Clat * ‖f‖ ^ 2 :=
      (mul_le_mul_of_nonneg_left hsum_x (by positivity)).trans_eq (by ring)
    have hsum_bound : (∑ m ∈ s, (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (hsq (fM m)) ^ (1 - κ)
            * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ
            + t ^ 2 * CW * hsq (fM m)))
        ≤ B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (Clat * ‖f‖ ^ 2) ^ (1 - κ)
            * (2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2
                + 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2) ^ κ
          + t ^ 2 * CW * Clat * ‖f‖ ^ 2 := by
      calc (∑ m ∈ s, (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
              * (hsq (fM m)) ^ (1 - κ)
              * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                  + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ
              + t ^ 2 * CW * hsq (fM m)))
          = B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
              * (∑ m ∈ s, (hsq (fM m)) ^ (1 - κ)
                * (2 * CW ^ 2 * hsq (subLp (locCubes c₁ a) (fM m) (measurableSet_locCubes c₁ a))
                    + 2 * t ^ 2 * CW ^ 2 * hsq (fM m)) ^ κ)
            + t ^ 2 * CW * (∑ m ∈ s, hsq (fM m)) := hsplit
        _ ≤ B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
              * ((Clat * ‖f‖ ^ 2) ^ (1 - κ)
                * (2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2
                    + 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2) ^ κ)
            + t ^ 2 * CW * Clat * ‖f‖ ^ 2 := add_le_add (hstep1.trans hstep2) hstep3
        _ = B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
              * (Clat * ‖f‖ ^ 2) ^ (1 - κ)
              * (2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2
                  + 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2) ^ κ
            + t ^ 2 * CW * Clat * ‖f‖ ^ 2 := by
          rw [← mul_assoc, ← mul_assoc]
    -- the final interpolation
    have hbound : c₂ ^ 2 * ‖f‖ ^ 2
        ≤ (4 : ℝ) ^ d * (B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ)
            * (Clat * ‖f‖ ^ 2) ^ (1 - κ)
            * (2 * CW ^ 2 * Clat * ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2
                + 2 * t ^ 2 * CW ^ 2 * Clat * ‖f‖ ^ 2) ^ κ
          + t ^ 2 * CW * Clat * ‖f‖ ^ 2) :=
      hmain_le.trans (mul_le_mul_of_nonneg_left hsum_bound (by positivity : (0:ℝ) ≤ (4:ℝ) ^ d))
    have hfin := Commons.Analysis.Inequalities.final_interpolation (d := d)
      (c₂ := c₂) (κ := κ)
      (A₀ := B * (U * ((2 * windowQ ηL q r) ^ d * ((1 + R ^ 2) ^ d * CW))) ^ (1 - κ))
      (Clat := Clat) (CW := CW)
      (U := ‖subLp (locCubes c₁ a) f (measurableSet_locCubes c₁ a)‖ ^ 2)
      (V := ‖f‖ ^ 2) (t := t)
      hc₂ hκpos hκle (mul_pos hBpos (Real.rpow_pos_of_pos hAnnpos _)) hClat hCWpos
      (by positivity) (by positivity) htnn hsmall hbound
    rw [Real.sqrt_sq (norm_nonneg f), Real.sqrt_sq (norm_nonneg _)] at hfin
    rw [norm_subLp_eq_eLpNorm] at hfin
    exact hfin

/-- **Han–Schlag's Corollary 4.2 (`cor:UPY`) for `d ≥ 1`.** -/
theorem localisation_bound_all (hd : 1 ≤ d)
    {c₁ c₂ c₃ α : ℝ} (hc₁ : 0 < c₁) (hc₁2 : c₁ ≤ 1 / 2) (hc₂ : c₂ ∈ Set.Ioo 0 1)
    (hc₃ : 0 < c₃) (hα : α ∈ Set.Ioo 0 1) :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ (α₁ : ℝ), 1 ≤ α₁ → ∀ (γ : ℝᵈ) (Y : Set ℝᵈ),
        Y ⊆ cube (-α₁) α₁ →
        (∀ η : ℝᵈ, (∀ i : Fin d, η i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1)) →
          AdmitsL1Damping ((fun z : ℝᵈ => η + z) '' (addSet Y (cube (-2) 2))) (c₁ / 2) c₂ c₃ α) →
        ∀ (a : (Fin d → ℤ) → Fin d → ℝ),
          (∀ n : Fin d → ℤ, ∀ i : Fin d,
            2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) →
          ∀ (f : Lp ℂ 2 (volume : Measure ℝᵈ)),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
                ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) →
            ‖f‖ ≤ Cstar * (eLpNorm
              ((⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + 2 * c₁)).indicator
                (f : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal := by
  obtain ⟨Clat, hClatpos, hClat⟩ := Commons.Analysis.Fourier.finset_bracket_lattice_le d
  set Clat' : ℝ := max Clat 1 with hClat'def
  have hClat'1 : 1 ≤ Clat' := le_max_right _ _
  have hC₀ : ∀ (η : ℝᵈ) (s : Finset (Fin d → ℤ)),
      (∑ m ∈ s, (1 + ‖η + ellVec m‖ ^ 2) ^ (-(d : ℝ))) ≤ Clat' := by
    intro η s
    refine (Finset.sum_le_sum fun m _ => ?_).trans ((hClat η s).trans (le_max_left _ _))
    have hofLp : (η + ellVec m).ofLp = η.ofLp + (fun i : Fin d => 2 * (m i : ℝ)) := by
      rw [WithLp.ofLp_add]; rfl
    rw [← hofLp]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ ?_
    · have h := pi_norm_le_euclidean (η + ellVec m)
      nlinarith [h, norm_nonneg ((η + ellVec m).ofLp)]
    · exact neg_nonpos.mpr (Nat.cast_nonneg d)
  obtain ⟨R, q, ε, δ, H, ηL, r, κ, CW, B, U, t, hR2, hRc, hq1, hq, hε0, hε1, hδ0, hδ3,
    hH0, hH1, hηL0, hr0, hητ, hQ4, hIbig, hκ, hCW, hB, hU, hT, hsmall⟩ :=
    Commons.Analysis.Inequalities.exists_R_coeff_small_q1 hd hc₁ hc₁2 hc₂.1 hc₂.2 hc₃
      hα.1 hα.2 hClat'1
  -- identify `κ` with `zpKappa`
  have hKeq : zpKappa δ H d
      = ((1 + 2 * δ⁻¹ ^ 3 * Real.log (2 / δ) + δ⁻¹ ^ 2 * Real.log (2 * Real.exp 1 / H))⁻¹) ^ d := by
    rw [zpKappa, twoConstKappa, twoConstK]
    congr 1
    congr 1
    ring
  have hκeq : κ = zpKappa δ H d := hκ.trans hKeq.symm
  have hBeq : B = cellZConst q ε δ H ηL (c₁ / 4) d := by
    rw [hB, hκeq, cellZConst, zpLamMax, zpLamMin]
  have hCWeq : CW = windowCW d := hCW
  have hteq : t = truncBeta d c₃ α R := hT
  have hUeq : U = windowD d q ε ηL r := by
    have hlog : (1 + (1 - ε)) / (1 - (1 - ε)) = (1 + (1 - ε) * 1) / (1 - (1 - ε) * 1) := by ring
    rw [hU, windowD, phiLens, hq1, hlog]
    congr 1
    congr 1
    ring
  have hητ' : 1 ≤ ηL * phiLens q ε (1 - 3 * δ) := hητ
  have hQ4' : 4 * Real.pi * windowQ ηL q r ≤ c₃ * (Real.log (2 + R)) ^ (-α) := hQ4
  have hIbig' : ENNReal.ofReal ((ηL * zpLamMax q ε) ^ d * (2 * (20 ^ d * H)))
      ≤ ENNReal.ofReal ((c₁ / 2) ^ d) := ENNReal.ofReal_le_ofReal hIbig
  exact localisation_bound_of_params hd hc₁ hc₁2 hc₂.1 hc₂.2 hc₃ hα.1 hα.2 hClat'1 hC₀
    hR2 hRc hq hε0 hε1 hδ0 hδ3 hH0 hH1 hηL0 hr0 hητ' hQ4' hIbig' hCWeq hκeq hBeq hUeq hteq
    hsmall

/-- **`LocalizationStatement` in dimension `0`** (the space is a single point, so the
localisation set is everything). -/
theorem localization_statement_zero : LocalizationStatement (d := 0) := by
  refine ⟨1, one_pos, ?_⟩
  intro c₁ hc₁ hc₁2 c₂ hc₂ c₃ hc₃ α hα
  refine ⟨1, one_pos, ?_⟩
  intro α₁ hα₁ γ Y hYsub hdamp a ha f hfY
  have hS : (⋃ n : Fin 0 → ℤ, box (a n) (fun i => a n i + 2 * c₁)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨fun _ => 0, by rw [mem_box]; exact fun i => i.elim0⟩
  rw [hS, Set.indicator_univ]
  have hnorm : (eLpNorm (f : EuclideanSpace ℝ (Fin 0) → ℂ) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 0)))).toReal = ‖f‖ := by
    rw [MeasureTheory.Lp.norm_def]
  rw [hnorm, one_mul]

/-- **`Submission.FUP.LocalizationStatement` is PROVED.** -/
theorem localization_statement : LocalizationStatement (d := d) := by
  by_cases hd : 1 ≤ d
  · exact ⟨1, one_pos, fun c₁ hc₁ hc₁2 c₂ hc₂ c₃ hc₃ α hα =>
      localisation_bound_all hd hc₁ hc₁2 hc₂ hc₃.1 hα⟩
  · have hd0 : d = 0 := by omega
    rw [hd0]
    exact localization_statement_zero

end Submission.FUP
