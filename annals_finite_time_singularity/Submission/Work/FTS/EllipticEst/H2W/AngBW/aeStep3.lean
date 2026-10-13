/-
Work module for the Elgindi finite-time-singularity project.

# `H2W.AngBW.aeStep3` — Step 3 of the level-`0` elliptic estimate in the a.e. class

Target (`Submission/Work/FTS/EllipticEst/H2W/AngBW/aeStep3.lean`): for `AeData α u G`,

  `‖α² z²∂_zz u‖_ρ ≤ C (‖G‖_ρ + α‖z∂_z u‖_ρ + ‖∂_θθ u‖_ρ + ‖u‖_ρ)`,  `‖g‖_ρ = √(HkSq α 0 g)`.

The module is an *assembly*: the arithmetic of the estimate (the rearrangement
`α²z²∂_zz u = -G - α(5+α)z∂_zu - ∂_θθu + ∂_θ(tan θ·u) - 6u` of `bslOp α u = G` on the open
quadrant, the five-term Cauchy–Schwarz domination of the level-`0` integrands, the honest
integration, and the square-root arithmetic) is carried out in the helper namespace
`Work.FTS.EllipticEst.H2W.AngBW.S3`; the four analytic inputs are

* `S3.hkMem_u`    — `HkMem α 0 u` (`Step3/HkMemU.lean`),
* `S3.hkMem_gradU`— `HkMem α 0 (z∂_z u)` (`Step3/HkMemGradU.lean`),
* `H2W.Ae.hkMem_ang1` — `HkMem α 0 (∂_θ(tan θ·u))` from the two above,
* `S3.ang1_bound` — the `I₄`-estimate `‖∂_θ(tan θ·u)‖_ρ ≤ C (‖u‖_ρ + ‖∂_θθ u‖_ρ)`
  (`Step3/Ang1Bound.lean`).

The helper modules are copies of the corresponding `Honest`/`H2W.Ae` modules with the
(transitively) unbuildable imports `Honest.firstOrderHonest`, `TanTheta.slice_hypotheses` and
`HkNorm_Dz_le_open` replaced by their buildable siblings; all of them are completely proved
and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Assembly
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemU
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.HkMemGradU
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Step3.Ang1Bound
import Submission.Work.FTS.EllipticEst.H2W.Ae.hkMem_ang1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AngBW.S3

open Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false


set_option autoImplicit false

/-! ## The pointwise rearrangement of the equation -/

/-- **The equation solved for `α² z² ∂_zz u`** on the open quadrant. -/
theorem scaled_rad2_eq {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z θ : ℝ}
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    α ^ 2 * rad2 u z θ = -G z θ - α * (5 + α) * grad u z θ - ang2 u z θ + ang1 u z θ
      - 6 * u z θ := by
  have h2 := AeData.eq h z hz θ hθ0 hθ1
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at h2
  have hrad : rad2 u z θ = z ^ 2 * Work.Spaces.pzIter 2 u z θ := rfl
  have hg : grad u z θ = z * Work.Spaces.pz u z θ := rfl
  have ha : ang2 u z θ = Work.Spaces.pthIter 2 u z θ := rfl
  have hu : ang1 u z θ = Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ := rfl
  rw [hrad, hg, ha, hu]
  linarith

/-! ## The pointwise domination of the level-`0` integrands -/

/-- The case `n = 5` of Cauchy–Schwarz: `(Σ aᵢ)² ≤ 5 Σ aᵢ²`. -/
private theorem five_term_sq_le (a b c d e : ℝ) : (a + b + c + d + e) ^ 2 ≤
    5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

/-- **The pointwise domination of the level-`0` integrand of `α² z²∂_zz u`** on the whole
closed quadrant: the boundary lines contribute `0 ≤ 0`, and on the open quadrant the
rearranged equation and Cauchy–Schwarz give the result. -/
theorem HkIntegrand_rad2_le {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (fun z θ => α ^ 2 * rad2 u z θ) z θ
        ≤ 5 * (Work.Spaces.HkIntegrand α 0 G z θ
            + (α * (5 + α)) ^ 2 * Work.Spaces.HkIntegrand α 0 (grad u) z θ
            + Work.Spaces.HkIntegrand α 0 (ang2 u) z θ
            + Work.Spaces.HkIntegrand α 0 (ang1 u) z θ
            + 6 ^ 2 * Work.Spaces.HkIntegrand α 0 u z θ) := by
  intro z hz θ hθ
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
    Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [← hz0]
    have hw : Work.Spaces.w 0 = 0 := by norm_num [Work.Spaces.w]
    simp [hw]
  rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).1 with hθ0 | hθ0pos
  · rw [← hθ0]
    have hr : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [Real.zero_rpow]; norm_num [Work.Spaces.eta]
    simp [show (2 : ℝ) * 0 = 0 from by norm_num, hr]
  rcases eq_or_lt_of_le (Set.mem_Icc.mp hθ).2 with hθpi | hθlt
  · rw [hθpi, show 2 * (Real.pi / 2) = Real.pi from by ring, Real.sin_pi]
    have hr : (0 : ℝ) ^ (Work.Spaces.eta / 2) = 0 := by
      rw [Real.zero_rpow]; norm_num [Work.Spaces.eta]
    simp [hr]
  · set W : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) with hW
    have h1 := scaled_rad2_eq h hzpos hθ0pos hθlt
    have hss : (α ^ 2 * rad2 u z θ) * W
        = -(G z θ * W) - (α * (5 + α) * (grad u z θ * W)) - (ang2 u z θ * W)
          + ang1 u z θ * W - 6 * (u z θ * W) := by
      rw [h1]; ring
    rw [hss]
    have h5 := five_term_sq_le (-(G z θ * W)) (-(α * (5 + α) * (grad u z θ * W)))
      (-(ang2 u z θ * W)) (ang1 u z θ * W) (-(6 * (u z θ * W)))
    nlinarith [h5]

/-! ## The honest integration step -/

/-- **Five-term aggregation of a pointwise integrand domination.**  If the level-`0`
integrand of `h` is dominated by a five-term combination of the integrands of `f₁,…,f₅`
and the latter are honest, then the same holds for the `HkSq`-functionals. -/
theorem HkSq_five_le {α : ℝ} {f₁ f₂ f₃ f₄ f₅ h : ℝ → ℝ → ℝ} (c₁ c₂ c₃ c₄ c₅ : ℝ)
    (h₁ : Work.Spaces.HkMem α 0 f₁) (h₂ : Work.Spaces.HkMem α 0 f₂)
    (h₃ : Work.Spaces.HkMem α 0 f₃) (h₄ : Work.Spaces.HkMem α 0 f₄)
    (h₅ : Work.Spaces.HkMem α 0 f₅)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 h z θ
        ≤ 5 * (c₁ ^ 2 * Work.Spaces.HkIntegrand α 0 f₁ z θ
            + c₂ ^ 2 * Work.Spaces.HkIntegrand α 0 f₂ z θ
            + c₃ ^ 2 * Work.Spaces.HkIntegrand α 0 f₃ z θ
            + c₄ ^ 2 * Work.Spaces.HkIntegrand α 0 f₄ z θ
            + c₅ ^ 2 * Work.Spaces.HkIntegrand α 0 f₅ z θ)) :
    Work.Spaces.HkSq α 0 h
      ≤ 5 * (c₁ ^ 2 * Work.Spaces.HkSq α 0 f₁ + c₂ ^ 2 * Work.Spaces.HkSq α 0 f₂
          + c₃ ^ 2 * Work.Spaces.HkSq α 0 f₃ + c₄ ^ 2 * Work.Spaces.HkSq α 0 f₄
          + c₅ ^ 2 * Work.Spaces.HkSq α 0 f₅) := by
  set F : Fin 5 → ℝ → ℝ → ℝ := ![f₁, f₂, f₃, f₄, f₅] with hF
  set c : Fin 5 → ℝ := ![c₁, c₂, c₃, c₄, c₅] with hc
  have hF0 : F 0 = f₁ := by simp [hF]
  have hF1 : F 1 = f₂ := by simp [hF]
  have hF2 : F 2 = f₃ := by simp [hF]
  have hF3 : F 3 = f₄ := by simp [hF]
  have hF4 : F 4 = f₅ := by simp [hF]
  have hc0 : c 0 = c₁ := by simp [hc]
  have hc1 : c 1 = c₂ := by simp [hc]
  have hc2 : c 2 = c₃ := by simp [hc]
  have hc3 : c 3 = c₄ := by simp [hc]
  have hc4 : c 4 = c₅ := by simp [hc]
  have hFmem : ∀ i, Work.Spaces.HkMem α 0 (F i) := by
    intro i
    fin_cases i <;> simp [hF0, hF1, hF2, hF3, hF4, h₁, h₂, h₃, h₄, h₅]
  have hpt' : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 h z θ
        ≤ 5 * ∑ i : Fin 5, (c i) ^ 2 * Work.Spaces.HkIntegrand α 0 (F i) z θ := by
    intro z hz θ hθ
    have := hpt z hz θ hθ
    rw [Fin.sum_univ_five]
    simp only [hc0, hc1, hc2, hc3, hc4, hF0, hF1, hF2, hF3, hF4]
    linarith [this]
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)
        ≤ 5 * ∑ i : Fin 5,
            (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ) := by
    intro z hz
    have hint : MeasureTheory.Integrable (fun θ => 5 * ∑ i : Fin 5,
        (c i) ^ 2 * Work.Spaces.HkIntegrand α 0 (F i) z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      refine ((MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => ?_)).const_mul 5)
      exact ((hFmem i).1 z hz).const_mul _
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := volume.restrict Work.Spaces.Iθ)
      (f := fun θ => Work.Spaces.HkIntegrand α 0 h z θ)
      (g := fun θ => 5 * ∑ i : Fin 5, (c i) ^ 2 * Work.Spaces.HkIntegrand α 0 (F i) z θ)
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
      hint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt' z hz θ hθ)
    refine hmono.trans_eq ?_
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    · simp only [MeasureTheory.integral_const_mul]
    · intro i _
      exact ((hFmem i).1 z hz).const_mul _
  have hbound : MeasureTheory.IntegrableOn (fun z => 5 * ∑ i : Fin 5,
      (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ))
      Work.Spaces.Iz := by
    refine ((MeasureTheory.integrable_finset_sum Finset.univ (fun i _ => ?_)).const_mul 5)
    exact ((hFmem i).2).const_mul _
  have houter := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict Work.Spaces.Iz)
    (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 h z θ)
    (g := fun z => 5 * ∑ i : Fin 5,
        (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ))
    (Eventually.of_forall fun z => integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 0 _ z θ)
    hbound
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  have e : (∫ z in Work.Spaces.Iz, 5 * ∑ i : Fin 5,
      (c i) ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (F i) z θ))
      = 5 * (c₁ ^ 2 * Work.Spaces.HkSq α 0 f₁ + c₂ ^ 2 * Work.Spaces.HkSq α 0 f₂
          + c₃ ^ 2 * Work.Spaces.HkSq α 0 f₃ + c₄ ^ 2 * Work.Spaces.HkSq α 0 f₄
          + c₅ ^ 2 * Work.Spaces.HkSq α 0 f₅) := by
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_finset_sum]
    · rw [Finset.mul_sum, Fin.sum_univ_five]
      simp only [hc0, hc1, hc2, hc3, hc4, hF0, hF1, hF2, hF3, hF4]
      simp only [MeasureTheory.integral_const_mul]
      simp only [Work.Spaces.HkSq]
      ring
    · intro i _
      exact ((hFmem i).2).const_mul _
  exact houter.trans_eq e

/-- **The `HkSq`-domination of `α² z²∂_zz u`.** -/
theorem HkSq_rad2_le {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G)
    (hu : Work.Spaces.HkMem α 0 u) (hd : Work.Spaces.HkMem α 0 (grad u))
    (ha : Work.Spaces.HkMem α 0 (ang1 u)) :
    Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * rad2 u z θ)
      ≤ 5 * (Work.Spaces.HkSq α 0 G + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u)
          + Work.Spaces.HkSq α 0 (ang2 u) + Work.Spaces.HkSq α 0 (ang1 u)
          + 6 ^ 2 * Work.Spaces.HkSq α 0 u) := by
  have hmain := HkSq_five_le (f₁ := G) (f₂ := grad u) (f₃ := ang2 u) (f₄ := ang1 u)
    (f₅ := u) (h := fun z θ => α ^ 2 * rad2 u z θ) 1 (α * (5 + α)) 1 1 6
    (AeData.memG h) hd (AeData.memAng2 h) ha hu
    (fun z hz θ hθ => by
      have hpt := HkIntegrand_rad2_le h z hz θ hθ
      simpa only [one_pow, one_mul] using hpt)
  simpa only [one_pow, one_mul] using hmain

/-! ## The square-root arithmetic -/

/-- The two-term square root inequality `√(a+b) ≤ √a + √b`. -/
private theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- `√(a+b+c+d+e) ≤ √a + √b + √c + √d + √e` for nonnegative `a,…,e`. -/
private theorem sqrt_five_le {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    Real.sqrt (a + b + c + d + e)
      ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c + Real.sqrt d + Real.sqrt e := by
  have h1 : Real.sqrt (a + b + c + d + e) ≤ Real.sqrt (a + b + c + d) + Real.sqrt e :=
    sqrt_add_le' (by linarith) he
  have h2 : Real.sqrt (a + b + c + d) ≤ Real.sqrt (a + b + c) + Real.sqrt d :=
    sqrt_add_le' (by linarith) hd
  have h3 : Real.sqrt (a + b + c) ≤ Real.sqrt (a + b) + Real.sqrt c :=
    sqrt_add_le' (by linarith) hc
  have h4 : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := sqrt_add_le' ha hb
  linarith

/-! ## The inputs from the analysis of the a.e. class -/

/- **Honesty of `u`**, of `z ∂_z u` and of `∂_θ(tan θ · u)` are all proved (with the same
names, in the same namespace) in the delivered, axiom-clean modules
`H2W/Ae/hkMem_u.lean`, `H2W/Ae/hkMem_gradU.lean` and `H2W/Ae/hkMem_ang1.lean`, imported at the
top of this file; likewise the `I₄`-bound `ang1_bound` (`H2W/Ae/ang1_bound.lean`). -/

/-! ## The assembly -/

/-- **`step3Ae` from the pieces.** -/
theorem step3Ae_of_pieces (CU : ℝ) (hCU : 0 < CU)
    (hu : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 u)
    (hd : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 (grad u))
    (ha : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G → Work.Spaces.HkMem α 0 (ang1 u))
    (hb : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
      Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
        ≤ CU * (Real.sqrt (Work.Spaces.HkSq α 0 u)
            + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u)))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), AeData α u G →
        nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
          ≤ C * (nrm α G + α * nrm α (grad u) + nrm α (ang2 u) + nrm α u) := by
  refine ⟨Real.sqrt 5 * (11 + CU), by positivity, ?_⟩
  intro α u G hA
  have hα4 : α ≤ 1 / 4 := AeData.hα4 hA
  have hα0 : (0 : ℝ) ≤ α := le_of_lt (AeData.hα hA)
  have hSq := HkSq_rad2_le hA (hu α u G hA) (hd α u G hA) (ha α u G hA)
  have hang := hb α u G hA
  -- the individual nonnegativities
  have nG : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
  have nd : 0 ≤ Work.Spaces.HkSq α 0 (grad u) := Work.Spaces.HkSq_nonneg α 0 (grad u)
  have nB : 0 ≤ Work.Spaces.HkSq α 0 (ang2 u) := Work.Spaces.HkSq_nonneg α 0 (ang2 u)
  have nA : 0 ≤ Work.Spaces.HkSq α 0 (ang1 u) := Work.Spaces.HkSq_nonneg α 0 (ang1 u)
  have nU : 0 ≤ Work.Spaces.HkSq α 0 u := Work.Spaces.HkSq_nonneg α 0 u
  have hc2 : 0 ≤ (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u) :=
    mul_nonneg (sq_nonneg _) nd
  -- the square root of the sum
  have hroot : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
      ≤ Real.sqrt 5 * (Real.sqrt (Work.Spaces.HkSq α 0 G)
          + α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
          + 6 * Real.sqrt (Work.Spaces.HkSq α 0 u)) := by
    have h1 : nrm α (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        = Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * rad2 u z θ)) := rfl
    rw [h1]
    have h2 : Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * rad2 u z θ))
        ≤ Real.sqrt (5 * (Work.Spaces.HkSq α 0 G
            + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u)
            + Work.Spaces.HkSq α 0 (ang2 u) + Work.Spaces.HkSq α 0 (ang1 u)
            + 6 ^ 2 * Work.Spaces.HkSq α 0 u)) := Real.sqrt_le_sqrt hSq
    refine h2.trans ?_
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 5)
    have h5 := sqrt_five_le nG hc2 nB nA (by positivity : (0 : ℝ) ≤ 6 ^ 2 * Work.Spaces.HkSq α 0 u)
    refine h5.trans ?_
    have e1 : Real.sqrt ((α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (grad u))
        = α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hα0 (by linarith))]
    have e2 : Real.sqrt (6 ^ 2 * Work.Spaces.HkSq α 0 u)
        = 6 * Real.sqrt (Work.Spaces.HkSq α 0 u) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6 ^ 2),
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
    rw [e1, e2]
  -- the `ang1`-bound and the constant
  refine hroot.trans ?_
  have nSg : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 G) := Real.sqrt_nonneg _
  have nSd : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (grad u)) := Real.sqrt_nonneg _
  have nSb : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u)) := Real.sqrt_nonneg _
  have nSu : 0 ≤ Real.sqrt (Work.Spaces.HkSq α 0 u) := Real.sqrt_nonneg _
  have h5a : (5 : ℝ) + α ≤ 11 + CU := by linarith
  have h1a : (1 : ℝ) + CU ≤ 11 + CU := by linarith
  have h6a : (6 : ℝ) + CU ≤ 11 + CU := by linarith
  have hone : (1 : ℝ) ≤ 11 + CU := by linarith
  have hCU0 : (0 : ℝ) ≤ CU := le_of_lt hCU
  have hang' : Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
      ≤ CU * (Real.sqrt (Work.Spaces.HkSq α 0 u)
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))) := hang
  have key : Real.sqrt (Work.Spaces.HkSq α 0 G)
        + α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
        + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
        + Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
        + 6 * Real.sqrt (Work.Spaces.HkSq α 0 u)
      ≤ (11 + CU) * (Real.sqrt (Work.Spaces.HkSq α 0 G)
          + α * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + Real.sqrt (Work.Spaces.HkSq α 0 u)) := by
    have hαd : 0 ≤ α * Real.sqrt (Work.Spaces.HkSq α 0 (grad u)) := mul_nonneg hα0 nSd
    have k1 : Real.sqrt (Work.Spaces.HkSq α 0 G)
        ≤ (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 G) := by nlinarith [nSg, hone]
    have k2 : α * (5 + α) * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))
        ≤ (11 + CU) * (α * Real.sqrt (Work.Spaces.HkSq α 0 (grad u))) := by
      nlinarith [hαd, h5a]
    have k3 : Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + Real.sqrt (Work.Spaces.HkSq α 0 (ang1 u))
          + 6 * Real.sqrt (Work.Spaces.HkSq α 0 u)
        ≤ (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
          + (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 u) := by
      have hA : CU * Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
            + (CU + 6) * Real.sqrt (Work.Spaces.HkSq α 0 u)
          ≤ (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 (ang2 u))
            + (11 + CU) * Real.sqrt (Work.Spaces.HkSq α 0 u) := by
        nlinarith [nSb, nSu]
      nlinarith [hang', hA, nSb, nSu]
    nlinarith [k1, k2, k3, nSg, nSd, nSb, nSu, hα0]
  simpa only [nrm, mul_assoc] using mul_le_mul_of_nonneg_left key (Real.sqrt_nonneg 5)

theorem step3Ae : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.H2W.Ae.nrm α
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.ang2 u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α u) := by
  obtain ⟨CU, hCU, hCUb⟩ := ang1_bound
  refine step3Ae_of_pieces CU hCU (fun α u G h => hkMem_u α u G h)
    (fun α u G h => hkMem_gradU α u G h)
    (fun α u G h => hkMem_ang1 α u G h (hkMem_u α u G h) (hkMem_gradU α u G h)) ?_
  intro α u G h
  exact hCUb α u (AeData.smooth h) (AeData.dirZero h) (AeData.dirPi h)
    (hkMem_u α u G h) (AeData.memAng2 h)
    (hkMem_ang1 α u G h (hkMem_u α u G h) (hkMem_gradU α u G h))


end Work.FTS.EllipticEst.H2W.AngBW.S3

namespace Work.FTS.EllipticEst.H2W.AngBW

/-- **Step 3 of the level-`0` elliptic estimate in the class `AeData`**: the requested lemma.

Proved in the helper namespace `Work.FTS.EllipticEst.H2W.AngBW.S3` (see the module docstring):
the arithmetic of the a.e. estimate together with the four analytic inputs
`S3.hkMem_u`, `S3.hkMem_gradU`, `H2W.Ae.hkMem_ang1` and the `I₄`-bound `S3.ang1_bound`. -/
theorem aeStep3 : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.FTS.EllipticEst.H2W.Ae.nrm α
          (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 u z θ))
        ≤ C * (Work.FTS.EllipticEst.H2W.Ae.nrm α G
          + α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.ang2 u)
          + Work.FTS.EllipticEst.H2W.Ae.nrm α u) :=
  Work.FTS.EllipticEst.H2W.AngBW.S3.step3Ae

end Work.FTS.EllipticEst.H2W.AngBW
