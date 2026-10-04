/-
# Layer D: the positivity set of `psi` is a neighbourhood of `0`

The Galerkin vector field

  `psi hLC D ρ ε c hg = if (g₀ + genMap D ε c) is positive definite then … else 0`

takes its first branch on the set of coefficient families `c` for which

  `∀ x v, v ≠ 0 → 0 < addSec g₀ (genMap D ε c) x v v`.

This module proves that this set is a *neighbourhood of `0`*: there is `δ > 0` such that every `c`
with `Σ_z |c z| < δ` satisfies the condition.  The proof is a uniform pointwise bound on the
spanning family `jSym D ε z`: on the support of `ψ i = χ i · ζ i ∘ pt i` the frame `e i` is
`g₀`-orthonormal (`B3.isONFrame_of_psi_ne_zero`), `χ i = 1`, and the volume density is bounded below
by the uniform constant of `B3.dens_lower_bound`; off the support the whole term vanishes.  Hence

  `|jSym D ε z x v v| ≤ K · g₀(x)(v,v)`

uniformly in `z`, `x` and `v`, and `genMap D ε c = Σ_z c z • jSym D ε z` gives the claim.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.D.psi.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open Classical
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

/-! ## 1. Cauchy–Schwarz for the inner product of a metric -/

/-- **Cauchy–Schwarz for the metric `g`**, with the inner product space structure on the tangent
spaces induced by `g.toRiemannianMetric`. -/
lemma smet_inner_sq_le (g : Submission.Diff.SMet I M) (x : M)
    (v w : TangentSpace I x) :
    (g.inner x v w) ^ 2 ≤ g.inner x v v * g.inner x w w := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) :=
    inferInstance
  have h : ∀ a b : TangentSpace I x, inner ℝ a b = g.inner x a b := fun a b => rfl
  rw [← h v w, ← h v v, ← h w w, pow_two]
  exact real_inner_mul_inner_self_le v w

/-- The `g`-inner product of a vector with itself is nonnegative. -/
lemma smet_inner_self_nonneg (g : Submission.Diff.SMet I M) (x : M)
    (v : TangentSpace I x) : 0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact le_of_lt (g.pos x v hv)

/-! ## 2. Auxiliary bounds -/

/-- **The mode functions are bounded by one in absolute value.** -/
lemma abs_modeFun_le_one (n : ℕ) {ε : ℝ} (q : Work.Diff.STE.B3.QIdx n ε)
    (z : Fin n → ℝ) : |Work.Diff.STE.B3.modeFun n q z| ≤ 1 := by
  have hnorm : ‖Work.Diff.STE.fourierExp (↑q.1) z‖ = 1 := by
    rw [Work.Diff.STE.fourierExp, Complex.norm_exp]
    simp [Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rcases hq : q.2 with _ | _
  · simp only [Work.Diff.STE.B3.modeFun, hq]
    calc |(Work.Diff.STE.fourierExp (↑q.1) z).re| ≤ ‖Work.Diff.STE.fourierExp (↑q.1) z‖ :=
        Complex.abs_re_le_norm _
      _ = 1 := hnorm
  · simp only [Work.Diff.STE.B3.modeFun, hq]
    calc |(Work.Diff.STE.fourierExp (↑q.1) z).im| ≤ ‖Work.Diff.STE.fourierExp (↑q.1) z‖ :=
        Complex.abs_im_le_norm _
      _ = 1 := hnorm

/-- Every value of the normalised weight family is bounded by one, because the squares sum to
one. -/
lemma abs_zeta_le_one (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) (p : M) : |D.ζ i p| ≤ 1 := by
  have hterm : (D.ζ i p) ^ 2 ≤ ∑ j : ι₀, (D.ζ j p) ^ 2 :=
    Finset.single_le_sum (f := fun j : ι₀ => (D.ζ j p) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [D.hζsq] at hterm
  calc |D.ζ i p| = Real.sqrt ((D.ζ i p) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hterm
    _ = 1 := Real.sqrt_one

/-- The same bound as `abs_zeta_le_one`, under the name used elsewhere in the workspace. -/
lemma abs_zeta_le_one_local (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i : ι₀) (p : M) : |D.ζ i p| ≤ 1 := abs_zeta_le_one (I := I) (M := M) D i p

/-! ## 3. The pointwise bound on the spanning family -/

/-- **One summand of the spanning family is bounded by the metric itself.**  On the support of
`ψ i = χ i · ζ i ∘ pt i` the frame `e i` is `g₀`-orthonormal, `χ i = 1` and the volume density is
bounded below; off the support the whole vector vanishes. -/
lemma abs_jVec_apply_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε d₀ : ℝ)
    (hd₀ : 0 < d₀)
    (hdens : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (q : Work.Diff.STE.B3.QIdx (Module.finrank ℝ E) ε)
    (p : M) (v : TangentSpace I p) :
    |Work.Diff.STE.B3.jVec (I := I) (M := M) D ε i a b q p v v| ≤
      (Real.sqrt d₀)⁻¹ * g₀.inner p v v := by
  have hg : 0 ≤ g₀.inner p v v := smet_inner_self_nonneg (I := I) (M := M) g₀ p v
  simp only [Work.Diff.STE.B3.jVec, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Work.Diff.STE.B3.jForm, ContinuousLinearMap.smulRight_apply, smul_apply,
    Work.Diff.STE.B3.jWgt]
  rcases eq_or_ne (D.ζ i p) 0 with hζ | hζ
  · rw [hζ, zero_mul, zero_mul, zero_mul, zero_mul]
    simp only [abs_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hg
  · have hp : p ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i p hζ).1
    have hcoord : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) p‖ < D.σ i := (D.hζsupp i p hζ).2
    have hχ : D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) p) = 1 :=
      D.hχ1 i _ (le_of_lt hcoord)
    have hsig : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) p‖ ≤ 2 * D.σ i := by
      have := D.hσ i; linarith
    have hON : Submission.Diff.IsONFrame g₀ p (fun a => D.e i a p) := by
      have h := D.heON i (Work.Diff.STE.coord (I := I) (D.x₀ i) p) hsig
      have hpt : D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) p) = p := D.pt_coord i hp
      rw [show (extChartAt I (D.x₀ i)).symm (Work.Diff.STE.flatToE (I := I) (D.x₀ i)
          (Work.Diff.STE.coord (I := I) (D.x₀ i) p)) = p from hpt] at h
      exact h
    have hdensle : d₀ ≤ D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p) := hdens i _ hsig
    have hζ1 : |D.ζ i p| ≤ 1 := abs_zeta_le_one (I := I) (M := M) D i p
    have hχ1 : |D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)| ≤ 1 := by
      rw [hχ]; norm_num
    have hsqrtpos : 0 < Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)) :=
      Real.sqrt_pos.mpr (lt_of_lt_of_le hd₀ hdensle)
    have hinv : |(Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)))⁻¹|
        ≤ (Real.sqrt d₀)⁻¹ := by
      rw [abs_inv, abs_of_pos hsqrtpos]
      exact inv_anti₀ (Real.sqrt_pos.mpr hd₀) (Real.sqrt_le_sqrt hdensle)
    have hmode : |Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q
        (Work.Diff.STE.coord (I := I) (D.x₀ i) p)| ≤ 1 := abs_modeFun_le_one _ q _
    have ha : |g₀.inner p (D.e i a p) v| ≤ Real.sqrt (g₀.inner p v v) := by
      have h1 : (g₀.inner p (D.e i a p) v) ^ 2 ≤ g₀.inner p v v := by
        have h := smet_inner_sq_le (I := I) (M := M) g₀ p (D.e i a p) v
        rw [hON a a] at h
        simpa using h
      calc |g₀.inner p (D.e i a p) v| = Real.sqrt ((g₀.inner p (D.e i a p) v) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (g₀.inner p v v) := Real.sqrt_le_sqrt h1
    have hb : |g₀.inner p (D.e i b p) v| ≤ Real.sqrt (g₀.inner p v v) := by
      have h1 : (g₀.inner p (D.e i b p) v) ^ 2 ≤ g₀.inner p v v := by
        have h := smet_inner_sq_le (I := I) (M := M) g₀ p (D.e i b p) v
        rw [hON b b] at h
        simpa using h
      calc |g₀.inner p (D.e i b p) v| = Real.sqrt ((g₀.inner p (D.e i b p) v) ^ 2) :=
            (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (g₀.inner p v v) := Real.sqrt_le_sqrt h1
    have hpair : |g₀.inner p (D.e i a p) v * g₀.inner p (D.e i b p) v|
        ≤ g₀.inner p v v := by
      rw [abs_mul]
      calc |g₀.inner p (D.e i a p) v| * |g₀.inner p (D.e i b p) v|
          ≤ Real.sqrt (g₀.inner p v v) * Real.sqrt (g₀.inner p v v) :=
            mul_le_mul ha hb (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = g₀.inner p v v := Real.mul_self_sqrt hg
    rw [abs_mul, abs_mul, abs_mul, abs_mul]
    calc |D.ζ i p| * |D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)|
          * |(Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) p)))⁻¹|
          * |Work.Diff.STE.B3.modeFun (Module.finrank ℝ E) q
              (Work.Diff.STE.coord (I := I) (D.x₀ i) p)|
          * |g₀.inner p (D.e i a p) v * g₀.inner p (D.e i b p) v|
        ≤ 1 * 1 * (Real.sqrt d₀)⁻¹ * 1 * g₀.inner p v v := by
          gcongr
      _ = (Real.sqrt d₀)⁻¹ * g₀.inner p v v := by ring

/-! ## 4. The bound on the spanning family `jSym` and the positivity neighbourhood -/

/-- **The symmetrised spanning family is bounded by the metric**, uniformly in the index. -/
lemma abs_jSym_apply_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε d₀ : ℝ)
    (hd₀ : 0 < d₀)
    (hdens : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε) (p : M) (v : TangentSpace I p) :
    |jSym (I := I) (M := M) D ε z p v v| ≤ 2 * (Real.sqrt d₀)⁻¹ * g₀.inner p v v := by
  have h1 := abs_jVec_apply_le (I := I) (M := M) D ε d₀ hd₀ hdens
    z.1 z.2.1 z.2.2.1 z.2.2.2 p v
  have h2 := abs_jVec_apply_le (I := I) (M := M) D ε d₀ hd₀ hdens
    (idxSwap (E := E) (ι₀ := ι₀) ε z).1 (idxSwap (E := E) (ι₀ := ι₀) ε z).2.1
    (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.1 (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.2 p v
  have hj : jSym (I := I) (M := M) D ε z p v v
      = Work.Diff.STE.B3.jVec (I := I) (M := M) D ε z.1 z.2.1 z.2.2.1 z.2.2.2 p v v
        + Work.Diff.STE.B3.jVec (I := I) (M := M) D ε (idxSwap (E := E) (ι₀ := ι₀) ε z).1
            (idxSwap (E := E) (ι₀ := ι₀) ε z).2.1 (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.1
            (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.2 p v v := by
    simp only [jSym, Work.Diff.STE.B3.jFamily, Finset.sum_apply, Pi.add_apply,
      ContinuousLinearMap.add_apply]
  rw [hj]
  calc |Work.Diff.STE.B3.jVec (I := I) (M := M) D ε z.1 z.2.1 z.2.2.1 z.2.2.2 p v v
        + Work.Diff.STE.B3.jVec (I := I) (M := M) D ε (idxSwap (E := E) (ι₀ := ι₀) ε z).1
            (idxSwap (E := E) (ι₀ := ι₀) ε z).2.1 (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.1
            (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.2 p v v|
      ≤ |Work.Diff.STE.B3.jVec (I := I) (M := M) D ε z.1 z.2.1 z.2.2.1 z.2.2.2 p v v|
        + |Work.Diff.STE.B3.jVec (I := I) (M := M) D ε (idxSwap (E := E) (ι₀ := ι₀) ε z).1
            (idxSwap (E := E) (ι₀ := ι₀) ε z).2.1 (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.1
            (idxSwap (E := E) (ι₀ := ι₀) ε z).2.2.2 p v v| := abs_add_le _ _
    _ ≤ (Real.sqrt d₀)⁻¹ * g₀.inner p v v + (Real.sqrt d₀)⁻¹ * g₀.inner p v v := add_le_add h1 h2
    _ = 2 * (Real.sqrt d₀)⁻¹ * g₀.inner p v v := by ring

/-- **The perturbation `genMap D ε c` is small for small coefficients**: uniformly in the point and
the vector, it is bounded by `(Σ_z |c z|) · K` times the metric. -/
lemma abs_genMap_apply_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε d₀ : ℝ)
    (hd₀ : 0 < d₀)
    (hdens : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) (p : M) (v : TangentSpace I p) :
    |genMap (I := I) (M := M) D ε c p v v|
      ≤ (∑ z, |c z|) * (2 * (Real.sqrt d₀)⁻¹) * g₀.inner p v v := by
  have hterm : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      |c z * jSym (I := I) (M := M) D ε z p v v|
        ≤ |c z| * (2 * (Real.sqrt d₀)⁻¹ * g₀.inner p v v) := by
    intro z
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (abs_jSym_apply_le (I := I) (M := M) D ε d₀ hd₀ hdens z p v) (abs_nonneg _)
  have hunfold : genMap (I := I) (M := M) D ε c p v v
      = ∑ z, c z * jSym (I := I) (M := M) D ε z p v v := by
    simp only [genMap, Finset.sum_apply, Pi.smul_apply, smul_apply, sum_apply, smul_eq_mul]
  rw [hunfold]
  calc |∑ z, c z * jSym (I := I) (M := M) D ε z p v v|
      ≤ ∑ z, |c z * jSym (I := I) (M := M) D ε z p v v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, |c z| * (2 * (Real.sqrt d₀)⁻¹ * g₀.inner p v v) := Finset.sum_le_sum fun z _ => hterm z
    _ = (∑ z, |c z|) * (2 * (Real.sqrt d₀)⁻¹ * g₀.inner p v v) := by rw [Finset.sum_mul]
    _ = (∑ z, |c z|) * (2 * (Real.sqrt d₀)⁻¹) * g₀.inner p v v := by ring

/-- **The positivity set of `psi` is a neighbourhood of `0`**: for small coefficients the perturbed
section `g₀ + genMap D ε c` is positive definite. -/
theorem eventually_posDef (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε : ℝ) :
    ∀ᶠ c in 𝓝 (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
      ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < addSec (I := I) g₀ (genMap (I := I) (M := M) D ε c) x v v := by
  obtain ⟨d₀, hd₀, hdens⟩ :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  set K : ℝ := 2 * (Real.sqrt d₀)⁻¹ with hK
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos two_pos (inv_pos.mpr (Real.sqrt_pos.mpr hd₀))
  have hδpos : 0 < 1 / (2 * K + 1) := by positivity
  have hopen : IsOpen {c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ |
      (∑ z, |c z|) < 1 / (2 * K + 1)} := by
    have hcont : Continuous fun c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ =>
        ∑ z, |c z| := by fun_prop
    exact isOpen_lt hcont continuous_const
  have hmem : (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ) ∈
      {c | (∑ z, |c z|) < 1 / (2 * K + 1)} := by
    simp only [Set.mem_setOf_eq]
    simpa using hδpos
  refine Filter.mem_of_superset (IsOpen.mem_nhds hopen hmem) ?_
  intro c hc x v hv
  rw [Work.Diff.STE.D.addSec_apply]
  have hgpos : 0 < g₀.inner x v v := g₀.pos x v hv
  have hbd := abs_genMap_apply_le (I := I) (M := M) D ε d₀ hd₀ hdens c x v
  have hsumlt : (∑ z, |c z|) * K < 1 / 2 := by
    have h1 : (∑ z, |c z|) < 1 / (2 * K + 1) := hc
    have h2 : (∑ z, |c z|) * K < (1 / (2 * K + 1)) * K :=
      mul_lt_mul_of_pos_right h1 hKpos
    have h3 : (1 / (2 * K + 1)) * K < 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith [h2, h3]
  have hbdd : |genMap (I := I) (M := M) D ε c x v v| < 1 / 2 * g₀.inner x v v := by
    have hbdd' : |genMap (I := I) (M := M) D ε c x v v|
        ≤ (∑ z, |c z|) * K * g₀.inner x v v := by simpa [hK, mul_assoc] using hbd
    calc |genMap (I := I) (M := M) D ε c x v v|
        ≤ (∑ z, |c z|) * K * g₀.inner x v v := hbdd'
      _ < 1 / 2 * g₀.inner x v v := by
          exact mul_lt_mul_of_pos_right hsumlt hgpos
  have := (abs_le.mp (le_of_lt hbdd)).1
  linarith

end

end Work.Diff.STE.D
