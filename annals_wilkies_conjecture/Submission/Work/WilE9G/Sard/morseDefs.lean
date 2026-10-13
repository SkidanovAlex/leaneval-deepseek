import Mathlib

/-!
# Vocabulary for Morse's criticality theorem

We formalise the framework of A. P. Morse's *The behavior of a function on its critical set*
(Annals of Math. 40 (1939)) in the "chart/parametrisation" form used to prove
`Work.WilE9G.Sard.morseDecomposition`.

The central notion is *flatness of order `m`* at a point: a map `F` is flat of order `m` at `x`
if `‖F y‖ ≤ ε ‖y - x‖^m` for all `y` close enough to `x`, for every `ε > 0`
(`FlatAt`).  A *chart datum* is a `C¹`, distance-non-decreasing parametrisation `γ` of a piece
of `ℝ^d`, together with a base point and a radius; the pieces are the images of the balls
`ball base rad` intersected with the set under consideration.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.WilE9G.Sard

open Set Filter Metric Bornology
open scoped Topology

/-- `F` is **flat of order `m` at `x`**: for every `ε > 0` there is `ρ > 0` such that
`‖F y‖ ≤ ε ‖y - x‖^m` whenever `‖y - x‖ ≤ ρ`. -/
def FlatAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → G) (m : ℕ) (x : E) : Prop :=
  ∀ ε > 0, ∃ ρ > 0, ∀ y, ‖y - x‖ ≤ ρ → ‖F y‖ ≤ ε * ‖y - x‖ ^ m

/-- A map does not decrease distances. -/
def Expanding {E E' : Type*} [PseudoMetricSpace E] [PseudoMetricSpace E'] (γ : E → E') : Prop :=
  ∀ x y, dist x y ≤ dist (γ x) (γ y)

/-- A chart datum in `ℝ^d`: an expanding `C¹` map `γ` from `ℝ^t` to `ℝ^d`, a base point in the
source and a radius.  The set analysed is covered by the images of the *open* balls
`ball base rad`; the smoothness and the distance condition are required on the closed ball. -/
structure ChartDatum (d : ℕ) where
  /-- dimension of the parameter space -/
  t : ℕ
  /-- the parametrisation -/
  γ : (Fin t → ℝ) → (Fin d → ℝ)
  /-- base point in the parameter space -/
  base : Fin t → ℝ
  /-- radius of the piece -/
  rad : ℝ
  rad_pos : 0 < rad
  contdiffOn : ContDiffOn ℝ 1 γ (closedBall base rad)
  expanding : ∀ x ∈ closedBall base rad, ∀ y ∈ closedBall base rad,
    dist x y ≤ dist (γ x) (γ y)

/-- **Upgrade step (Morse's Lemma 3.2).**  If the derivative of `F` along `γ` is flat of order
`m - 1` at `x₀` and `γ` is Lipschitz near `x₀`, then `F ∘ γ` is flat of order `m` at `x₀`
(provided `F (γ x₀) = 0`, which holds on the pieces of the decomposition). -/
theorem FlatAt.comp_of_fderiv {m : ℕ} (hm : 1 ≤ m)
    {E G E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F : E → G} {γ : E' → E} {x₀ : E'} {L ρ₀ : ℝ}
    (hdiffF : ∀ z, ‖z - x₀‖ ≤ ρ₀ → DifferentiableAt ℝ F (γ z))
    (hdiffγ : ∀ z, ‖z - x₀‖ ≤ ρ₀ → DifferentiableAt ℝ γ z)
    (hx₀ : F (γ x₀) = 0)
    (hL : 0 ≤ L) (hρ₀ : 0 < ρ₀)
    (hγL : ∀ z, ‖z - x₀‖ ≤ ρ₀ → ‖fderiv ℝ γ z‖ ≤ L)
    (hflat : FlatAt (fun z => fderiv ℝ F (γ z)) (m - 1) x₀) :
    FlatAt (fun z => F (γ z)) m x₀ := by
  intro ε hε
  have hL1 : (0 : ℝ) < L + 1 := by linarith
  set ε' : ℝ := ε / (L + 1) with hε'def
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := hflat ε' hε'pos
  refine ⟨min ρ₀ ρ₁, lt_min hρ₀ hρ₁pos, fun y hy => ?_⟩
  have hyρ₀ : ‖y - x₀‖ ≤ ρ₀ := hy.trans (min_le_left _ _)
  have hyρ₁ : ‖y - x₀‖ ≤ ρ₁ := hy.trans (min_le_right _ _)
  set r : ℝ := ‖y - x₀‖ with hrdef
  have hrnn : 0 ≤ r := norm_nonneg _
  have hcomp : ∀ z ∈ closedBall x₀ r, fderiv ℝ (fun w => F (γ w)) z
      = (fderiv ℝ F (γ z)).comp (fderiv ℝ γ z) := by
    intro z hz
    have hzx : ‖z - x₀‖ ≤ r := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    exact fderiv_comp z (hdiffF z (hzx.trans hyρ₀)) (hdiffγ z (hzx.trans hyρ₀))
  have hbound : ∀ z ∈ closedBall x₀ r,
      ‖fderiv ℝ (fun w => F (γ w)) z‖ ≤ ε' * r ^ (m - 1) * L := by
    intro z hz
    have hzx : ‖z - x₀‖ ≤ r := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    have hzρ₁ : ‖z - x₀‖ ≤ ρ₁ := hzx.trans hyρ₁
    have hzρ₀ : ‖z - x₀‖ ≤ ρ₀ := hzx.trans hyρ₀
    rw [hcomp z hz]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖fderiv ℝ F (γ z)‖ ≤ ε' * ‖z - x₀‖ ^ (m - 1) := hρ₁ z hzρ₁
    have h2 : ‖fderiv ℝ γ z‖ ≤ L := hγL z hzρ₀
    have h3 : ‖z - x₀‖ ^ (m - 1) ≤ r ^ (m - 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hzx (m - 1)
    calc ‖fderiv ℝ F (γ z)‖ * ‖fderiv ℝ γ z‖
        ≤ (ε' * ‖z - x₀‖ ^ (m - 1)) * L :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ ≤ (ε' * r ^ (m - 1)) * L := by
          refine mul_le_mul_of_nonneg_right ?_ hL
          exact mul_le_mul_of_nonneg_left h3 hε'pos.le
      _ = ε' * r ^ (m - 1) * L := by ring
  have hdiff : ∀ z ∈ closedBall x₀ r, DifferentiableAt ℝ (fun w => F (γ w)) z := by
    intro z hz
    have hzx : ‖z - x₀‖ ≤ r := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    exact (hdiffF z (hzx.trans hyρ₀)).comp z (hdiffγ z (hzx.trans hyρ₀))
  have hx₀mem : x₀ ∈ closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_self]; exact hrnn
  have hymem : y ∈ closedBall x₀ r := by
    rw [Metric.mem_closedBall, dist_eq_norm, hrdef]
  have hmvt := (convex_closedBall x₀ r).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound hx₀mem hymem
  have hry : ‖y - x₀‖ = r := hrdef.symm
  have hexp : (ε' * r ^ (m - 1) * L) * ‖y - x₀‖ = ε' * L * r ^ m := by
    rw [hry]
    have hpow : r ^ (m - 1) * r = r ^ m := by
      rw [← pow_succ]; congr 1; omega
    calc (ε' * r ^ (m - 1) * L) * r = ε' * L * (r ^ (m - 1) * r) := by ring
      _ = ε' * L * r ^ m := by rw [hpow]
  rw [hexp] at hmvt
  have hcoef : ε' * L ≤ ε := by
    have hE : ε' * L = ε * L / (L + 1) := by rw [hε'def]; ring
    rw [hE, div_le_iff₀ hL1]
    nlinarith [hε.le, hL]
  have hfin : ε' * L * r ^ m ≤ ε * r ^ m :=
    mul_le_mul_of_nonneg_right hcoef (pow_nonneg hrnn m)
  have := hmvt.trans hfin
  rw [hx₀, sub_zero, hrdef] at this
  exact this

end Work.WilE9G.Sard
