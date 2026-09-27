import Mathlib
import Submission.Work.Drive.descent_strip_injective
import Submission.Work.Drive.planeChartDataAux
import Submission.Work.Drive.bandData
import Submission.Work.Drive.directionOnly_descent

namespace Work.Drive

open scoped ContDiff
open Filter

/-!
# The pair `(pcA, pcDc)` is injective on a collar of the seam circle `‖z‖ = 1/2`

This file proves `Work.Drive.exists_collar_pair_injective`.

## The mathematical content

The band profiles of the plane chart are `x z = z/‖z‖` (the direction) and
`τ z = bandProf a ‖z‖` (the opening, `≤ 0` inside the disk `‖z‖ ≤ 1/2`).  The pair
`(pcA, pcDc)` reads the data of the chord of opening `τ z` in the direction `x z`.

* `Work.Drive.descent_strip_injective` says that on the strip `τ ∈ [-c', 0]` the pair `(pcA, pcDc)`
  determines the direction modulo `2π` **and** the opening;
* since `z ↦ z/‖z‖` is injective on a ray and the opening is a function of the radius, it remains to
  know that `ρ ↦ bandProf a ρ` is injective on a collar of `1/2` (from below).  This is the only
  genuine content here: `bandProf a ρ = pStep a (1/2) ρ * (π²/2)(ρ - 1/2)` vanishes at both ends of
  `[a, 1/2]` and is negative in between, so it is *not* injective on the whole interval; but its
  derivative at `1/2` equals `π²/2 > 0` (the step is locally constant `1` there, so only the linear
  factor contributes), hence it is strictly monotone on a small interval `[ρ₂, 1/2]`.

The collar of the theorem is then the intersection of that monotonicity collar (for the injectivity
of the radius) and of a collar on which `bandProf a` takes its values in the strip `[-c', 0]` known
to the descent lemma (continuity of `bandProf a` at `1/2`).
-/

noncomputable section

/-! ## The derivative of the band profile at the seam -/

/-- The step `pStep a (1/2)` has vanishing derivative at `1/2`: it is constant `1` from `1/2` on
(and bounded above by `1` everywhere), so `1/2` is a local maximum. -/
private lemma deriv_pStep_half (a : ℝ) (ha : a < 1/2) :
    deriv (fun ρ : ℝ => pStep a (1/2) ρ) (1/2) = 0 := by
  refine IsLocalMax.deriv_eq_zero ?_
  refine Filter.Eventually.of_forall fun ρ => ?_
  show pStep a (1/2) ρ ≤ pStep a (1/2) (1/2)
  rw [pStep_eq_one ha le_rfl]
  exact pStep_le_one a (1/2) ρ

/-- The derivative of the linear factor `ρ ↦ (π²/2)(ρ - 1/2)` at `1/2`. -/
private lemma hasDerivAt_lin_half :
    HasDerivAt (fun ρ : ℝ => Real.pi ^ 2 / 2 * (ρ - 1/2)) (Real.pi ^ 2 / 2) (1/2) := by
  have hbase : HasDerivAt (fun ρ : ℝ => ρ - 1/2) 1 (1/2) := by
    simpa using (hasDerivAt_id (1/2 : ℝ)).sub_const (1/2)
  have := hbase.const_mul (Real.pi ^ 2 / 2)
  rwa [mul_one] at this

/-- **The band profile is increasing at the seam**: `deriv (bandProf a) (1/2) = π²/2`. -/
private lemma deriv_bandProf_half (a : ℝ) (ha : a < 1/2) :
    deriv (bandProf a) (1/2) = Real.pi ^ 2 / 2 := by
  have h1 : DifferentiableAt ℝ (fun ρ : ℝ => pStep a (1/2) ρ) (1/2) :=
    ((contDiff_pStep a (1/2)).differentiable (by simp)).differentiableAt
  have h2 := hasDerivAt_lin_half
  have hband : bandProf a
      = (fun ρ : ℝ => pStep a (1/2) ρ) * (fun ρ : ℝ => Real.pi ^ 2 / 2 * (ρ - 1/2)) := rfl
  rw [hband, deriv_mul h1 h2.differentiableAt, deriv_pStep_half a ha, h2.deriv,
    pStep_eq_one ha le_rfl]
  ring

/-- **The collar of the band profile.**  For every `c' > 0` there is a radius `ρ₂` with
`a ≤ ρ₂ < 1/2` (and `ρ₂ > 0`) such that on `[ρ₂, 1/2]` the band profile takes its values in
`[-c', 0]` and is strictly monotone (hence injective). -/
private lemma exists_collar_mono_bandProf (a c' : ℝ) (ha : a < 1/2) (hc' : 0 < c') :
    ∃ ρ₂ : ℝ, a ≤ ρ₂ ∧ 0 < ρ₂ ∧ ρ₂ < 1/2 ∧
      (∀ ρ : ℝ, ρ₂ ≤ ρ → ρ ≤ 1/2 → -c' ≤ bandProf a ρ ∧ bandProf a ρ ≤ 0) ∧
      StrictMonoOn (bandProf a) (Set.Icc ρ₂ (1/2)) := by
  have hcontb : ContinuousAt (bandProf a) (1/2) := (contDiff_bandProf a).continuous.continuousAt
  have hbval : bandProf a (1/2) = 0 := by rw [bandProf]; ring
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcontb c' hc'
  have hcontd : ContinuousAt (deriv (bandProf a)) (1/2) :=
    ((contDiff_bandProf a).continuous_deriv (by norm_num)).continuousAt
  have hdval : deriv (bandProf a) (1/2) = Real.pi ^ 2 / 2 := deriv_bandProf_half a ha
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcontd (Real.pi ^ 2 / 4) (by positivity)
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  have hδ₁le : δ ≤ δ₁ := min_le_left _ _
  have hδ₂le : δ ≤ δ₂ := min_le_right _ _
  set ρ₂ : ℝ := max (max a (1/2 - δ/2)) (1/8) with hρ₂def
  have hρ₂a : a ≤ ρ₂ := le_trans (le_max_left a _) (le_max_left _ _)
  have hρ₂pos : 0 < ρ₂ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ₂lt : ρ₂ < 1/2 := max_lt (max_lt ha (by linarith)) (by norm_num)
  have hρ₂close : 1/2 - δ/2 ≤ ρ₂ := le_trans (le_max_right a _) (le_max_left _ _)
  refine ⟨ρ₂, hρ₂a, hρ₂pos, hρ₂lt, ?_, ?_⟩
  · intro ρ h1 h2
    refine ⟨?_, bandProf_nonpos h2⟩
    have hlt : (1:ℝ)/2 - ρ < δ₁ := by
      have h3 : (1:ℝ)/2 - ρ ≤ δ/2 := by linarith
      have h4 : δ/2 < δ₁ := by linarith
      linarith
    have hdist : dist ρ (1/2) < δ₁ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : ρ - 1/2 ≤ 0)]
      linarith
    have hh := hδ₁ hdist
    rw [Real.dist_eq, hbval, sub_zero, abs_lt] at hh
    linarith [hh.1]
  · refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ((contDiff_bandProf a).continuous.continuousOn) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : ρ₂ < x := hx.1
    have hx2 : x < 1/2 := hx.2
    have hlt : dist x (1/2) < δ₂ := by
      rw [Real.dist_eq, abs_of_neg (by linarith : x - 1/2 < 0)]
      have h3 : (1:ℝ) / 2 - x < δ / 2 := by linarith
      have h4 : δ / 2 < δ₂ := by linarith
      linarith
    have hh := hδ₂ hlt
    rw [Real.dist_eq, hdval, abs_lt] at hh
    linarith [hh.1]

theorem exists_collar_pair_injective {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (M W : ℂ × ℝ → ℂ) (c : ℝ)
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W) (hc : 0 < c)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    (hband : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 →
      4 * |τ| * ‖W (x, τ)‖ ^ 2 < ‖M (x, τ)‖ ^ 2)
    (hWne : ∀ x : ℂ, ∀ τ : ℝ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 2 → -c ≤ τ → τ < 0 → W (x, τ) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 8 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    (hdir : ∀ (x x' : ℂ) (τ : ℝ), 1 / 8 ≤ ‖x‖ → 1 / 8 ≤ ‖x'‖ →
      x / ((‖x‖ : ℝ) : ℂ) = x' / ((‖x'‖ : ℝ) : ℂ) →
      M (x, τ) = M (x', τ) ∧ W (x, τ) = W (x', τ))
    {a : ℝ} (ha : a < 1 / 2)
    (x : ℂ → ℂ) (τ : ℂ → ℝ)
    (hx : ∀ z : ℂ, a ≤ ‖z‖ → x z = z / ((‖z‖ : ℝ) : ℂ))
    (hτ : ∀ z : ℂ, τ z = Work.Drive.bandProf a ‖z‖) :
    ∃ ρ₂ : ℝ, a ≤ ρ₂ ∧ ρ₂ < 1 / 2 ∧ ∀ z z' : ℂ,
      ρ₂ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ρ₂ ≤ ‖z'‖ → ‖z'‖ ≤ 1 / 2 →
      Work.Drive.pcA M W x τ z = Work.Drive.pcA M W x τ z' →
      Work.Drive.pcDc M W x τ z = Work.Drive.pcDc M W x τ z' → z = z' := by
  classical
  obtain ⟨c', hc'pos, _hc'le, hstrip⟩ :=
    descent_strip_injective γ hγ hγne M W c hMsm hWsm hc hMval hWval hband hWne hM0 hW0
  obtain ⟨ρ₂, hρ₂a, _hρ₂pos, hρ₂lt, hbound, hmono⟩ := exists_collar_mono_bandProf a c' ha hc'pos
  refine ⟨ρ₂, hρ₂a, hρ₂lt, ?_⟩
  intro z z' hz1 hz2 hz1' hz2' hA hDc
  have hza : a ≤ ‖z‖ := le_trans hρ₂a hz1
  have hza' : a ≤ ‖z'‖ := le_trans hρ₂a hz1'
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    linarith
  have hz0' : z' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1'
    linarith
  have hnorm0 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := fun h =>
    norm_ne_zero_iff.mpr hz0 (Complex.ofReal_eq_zero.mp h)
  have hnorm0' : ((‖z'‖ : ℝ) : ℂ) ≠ 0 := fun h =>
    norm_ne_zero_iff.mpr hz0' (Complex.ofReal_eq_zero.mp h)
  -- `x` is the direction, written with the argument
  have hxz : x z = Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I) := by
    rw [hx z hza, div_eq_iff hnorm0, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have hxz' : x z' = Complex.exp (((Complex.arg z' : ℝ) : ℂ) * Complex.I) := by
    rw [hx z' hza', div_eq_iff hnorm0', mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I z').symm
  have hτz : τ z = bandProf a ‖z‖ := hτ z
  have hτz' : τ z' = bandProf a ‖z'‖ := hτ z'
  obtain ⟨hbd1, hbd2⟩ := hbound ‖z‖ hz1 hz2
  obtain ⟨hbd1', hbd2'⟩ := hbound ‖z'‖ hz1' hz2'
  -- the data of `z` in the `(direction, opening)` parametrisation used by the descent lemma
  have hAe : pcA M W x τ z
      = pcA M W (fun _ : ℂ => Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I))
          (fun _ : ℂ => bandProf a ‖z‖) 0 := by
    simp only [pcA, hxz, hτz]
  have hAe' : pcA M W x τ z'
      = pcA M W (fun _ : ℂ => Complex.exp (((Complex.arg z' : ℝ) : ℂ) * Complex.I))
          (fun _ : ℂ => bandProf a ‖z'‖) 0 := by
    simp only [pcA, hxz', hτz']
  have hDe : pcDc M W x τ z
      = pcDc M W (fun _ : ℂ => Complex.exp (((Complex.arg z : ℝ) : ℂ) * Complex.I))
          (fun _ : ℂ => bandProf a ‖z‖) 0 := by
    simp only [pcDc, pcD, pcA, hxz, hτz]
  have hDe' : pcDc M W x τ z'
      = pcDc M W (fun _ : ℂ => Complex.exp (((Complex.arg z' : ℝ) : ℂ) * Complex.I))
          (fun _ : ℂ => bandProf a ‖z'‖) 0 := by
    simp only [pcDc, pcD, pcA, hxz', hτz']
  -- the descent strip: equality of the data forces the angle modulo `2π` and the opening
  obtain ⟨hk, hτeq⟩ := hstrip (Complex.arg z) (Complex.arg z') (bandProf a ‖z‖) (bandProf a ‖z'‖)
    ⟨hbd1, hbd2⟩ ⟨hbd1', hbd2'⟩ (hAe.symm.trans (hA.trans hAe'))
      (hDe.symm.trans (hDc.trans hDe'))
  obtain ⟨k, hk⟩ := hk
  have hdir_eq : x z = x z' := by
    rw [hxz, hxz', Complex.exp_eq_exp_iff_exists_int]
    refine ⟨k, ?_⟩
    have h2π : ((2 : ℝ) * Real.pi) ≠ 0 := by positivity
    have hk2 : (Complex.arg z : ℝ) = Complex.arg z' + (k : ℝ) * (2 * Real.pi) := by
      have h : (Complex.arg z - Complex.arg z') / (2 * Real.pi) = (k : ℝ) := hk.symm
      rw [div_eq_iff h2π] at h
      linarith
    have hc2 : ((Complex.arg z : ℝ) : ℂ)
        = ((Complex.arg z' : ℝ) : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
      rw [hk2]; push_cast; ring
    rw [hc2]; ring
  -- the radius is determined by the opening on the collar
  have hρeq : ‖z‖ = ‖z'‖ := hmono.injOn ⟨hz1, hz2⟩ ⟨hz1', hz2'⟩ hτeq
  have hzeq : z = ((‖z‖ : ℝ) : ℂ) * x z := by
    rw [hxz]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  have hzeq' : z' = ((‖z'‖ : ℝ) : ℂ) * x z' := by
    rw [hxz']
    exact (Complex.norm_mul_exp_arg_mul_I z').symm
  rw [hzeq, hzeq', hρeq, hdir_eq]

end

end Work.Drive
