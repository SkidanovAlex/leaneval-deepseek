import Mathlib
import Submission.Work.EvenBound.Imports
import Submission.Work.ValueClosed.exists_chart_convergent_subseq

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.EvenBound.Attain

set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic Submission.GlobalExp Submission.InjRadius
open Submission.GeodesicLoop Submission.LensLoop

/-- **The global injectivity radius `injSup hmet = inf_p inj(p)` is attained**, below the conjugate
radius `π/√K`, on a compact manifold with `sec ≤ K`, `0 < K`.

*Proof route.*  `m := injSup hmet` satisfies `InjAllAtLeast hmet m` and `¬ InjAllAtLeast hmet r`
for `r > m`, and `m < π/√K`.  `Submission.KlingenbergEven.exists_cutPoint_sequence` gives points
`p n`, radii `mr n ∈ [m, m + 1/(n+1))` with `InjAtLeast (p n) (mr n)` and *maximality*, and distinct
unit directions `ξ n ≠ η n` whose rays meet at `q n` after time `mr n`, both minimising.
`XuTrap.xuCornerExcluded` at `p n` gives `w₁ n = -w₂ n` for the velocities at `q n`, hence (with
`GeodesicLoop.GExp_add_two_mul_of_velocity_eq_neg` and `GExpGlob.GExp_add_smul`) the two vectors
`V n := mr n • w₁ n` and `-V n` at `q n` **both** exponentiate to `p n` (`w₁ n` is the velocity of
the `ξ n`-ray at `mr n`, so the ray from `q n` in that direction runs back to `p n` in time `mr n`;
the ray in the opposite direction is the continuation of the same geodesic and reaches `p n` at
time `2 * mr n` by the value-closure).
Extract a subsequence with `p n → p`, `mr n → m` and the chart coordinates of `V n` converging to
`V` (compactness of `M` and of a closed ball of `E`), use `GExpJointPt.tendsto_GExp_frameVector` for
the joint continuity of `GExp` in the base point, and `KlingenbergAttain.tendsto_norm_frameVector`
for the norms: then `GExp p V = GExp p (-V) = p`, `‖V‖ = m`, `V ≠ 0`.  So `¬ InjAtLeast hmet p r`
for every `r > m` (`Submission.InjRadius.not_injAtLeast_of_two_of_norm_eq` applied to the two
distinct vectors `V`, `-V`, of norm `m < r`), while `InjAtLeast hmet p m` holds by
`InjSup.injAllAtLeast_injSup`. -/
theorem injSup_attained_of_lt_pi_div_sqrt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hcurv : Submission.RauchK.CurvLe cov K) (hK : 0 < K)
    (hmπ : Submission.InjSup.injSup hmet < Real.pi / Real.sqrt K) :
    ∃ p : M, Submission.InjRadius.InjAtLeast hmet p (Submission.InjSup.injSup hmet) ∧
      ∀ r : ℝ, Submission.InjSup.injSup hmet < r → ¬ Submission.InjRadius.InjAtLeast hmet p r := by
  classical
  obtain ⟨p, mr, ξ, η, hmr0, hmle, hmrπ, hmrbdd, hinjp, hmaxp, hξ1, hη1, hξη, hmeet,
    hminξ, hminη⟩ :=
    Submission.KlingenbergEven.exists_cutPoint_sequence (cov := cov) hmet htor hcurv hK hmπ
  -- positivity of the global injectivity radius
  obtain ⟨x₀⟩ : Nonempty M := inferInstance
  obtain ⟨R, -, hR⟩ := Submission.CutTime.exists_edist_le (I := I) (cov := cov) hmet htor x₀
  have hbdd : BddAbove {r : ℝ | Submission.InjRadius.InjAllAtLeast hmet r} :=
    Submission.InjSup.bddAbove_injAllAtLeast_of_diam_le (cov := cov) hmet htor hR
  obtain ⟨ρ, hρ0, hρall⟩ := Submission.UniformInj.exists_pos_injAllAtLeast (cov := cov) hmet
  have hm0 : 0 < Submission.InjSup.injSup hmet :=
    lt_of_lt_of_le hρ0 (le_csSup hbdd hρall)
  -- the two directions are non-zero
  have hξne : ∀ n, ξ n ≠ 0 := fun n => by
    intro h0
    have h := hξ1 n
    rw [h0, norm_zero] at h
    norm_num at h
  -- Xu's theorem at each `p n`
  have hvel : ∀ n : ℕ,
      curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet (p n) (t • ξ n)) (mr n)
      = -curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet (p n) (t • η n)) (mr n) := by
    intro n
    exact Submission.XuTrap.xuCornerExcluded (cov := cov) hmet htor (p n) (hmr0 n) (hinjp n)
      (hmaxp n) (ξ n) (η n) (hξ1 n) (hη1 n) (hξη n) (hminξ n) (hminη n) (hmeet n)
      (Submission.ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt (cov := cov) hmet htor hcurv hK
        (hmrπ n))
  -- the meeting points and the arrival velocities
  let q : ℕ → M := fun n => GExp (cov := cov) hmet (p n) (mr n • ξ n)
  let w₁ : (n : ℕ) → TangentSpace I (q n) :=
    fun n => curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet (p n) (t • ξ n)) (mr n)
  have hw₁unit : ∀ n, ‖w₁ n‖ = 1 := by
    intro n
    change ‖curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet (p n) (t • ξ n))
      (mr n)‖ = 1
    rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet (p n) (hξne n)
      (ne_of_gt (hmr0 n))]
    exact hξ1 n
  -- ### compactness: a chart-convergent subsequence of the unit arrival velocities
  obtain ⟨z₀, q₀, y₀, φ, hφ, hq₀src, hqconv, y, hyconv, hframe, hynorm⟩ :=
    Work.ValueClosed.exists_chart_convergent_subseq (I := I) q w₁ hw₁unit
  -- ### `mr n → m` and along the subsequence
  have hmrlim : Tendsto mr atTop (𝓝 (Submission.InjSup.injSup hmet)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ hmle hmrbdd
    simpa using (tendsto_const_nhds (x := Submission.InjSup.injSup hmet)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmrlimφ : Tendsto (fun k => mr (φ k)) atTop (𝓝 (Submission.InjSup.injSup hmet)) :=
    hmrlim.comp hφ.tendsto_atTop
  -- ### the two vectors at `q n` which both exponentiate to `p n`
  have hVpos : ∀ n, GExp (cov := cov) hmet (q n) (mr n • w₁ n) = p n := by
    intro n
    have h1 := Submission.GeodesicLoop.GExp_neg_velocity_of_ray (cov := cov) hmet (p n)
      (ξ := η n) (hη1 n) (m := mr n) (hmr0 n) (s := mr n) (le_of_lt (hmr0 n)) le_rfl
    rw [sub_self, zero_smul, GExp_zero] at h1
    rw [← hmeet n] at h1
    rw [← hvel n] at h1
    exact h1
  have hVneg : ∀ n, GExp (cov := cov) hmet (q n) (-(mr n • w₁ n)) = p n := by
    intro n
    have h1 := Submission.GeodesicLoop.GExp_neg_velocity_of_ray (cov := cov) hmet (p n)
      (ξ := ξ n) (hξ1 n) (m := mr n) (hmr0 n) (s := mr n) (le_of_lt (hmr0 n)) le_rfl
    rw [sub_self, zero_smul, GExp_zero] at h1
    have h2 : mr n • (-curveVelocity (I := I)
        (fun t : ℝ => GExp (cov := cov) hmet (p n) (t • ξ n)) (mr n)) = -(mr n • w₁ n) := by
      rw [smul_neg]
    rw [h2] at h1
    exact h1
  have hVnorm : ∀ n, ‖mr n • w₁ n‖ = mr n := by
    intro n
    rw [norm_smul, Real.norm_of_nonneg (hmr0 n).le, hw₁unit n, mul_one]
  -- ### the chart coordinates of the two vectors
  let an : ℕ → E := fun k => mr (φ k) • y k
  let bn : ℕ → E := fun k => -(mr (φ k) • y k)
  have han : Tendsto an atTop (𝓝 (Submission.InjSup.injSup hmet • y₀)) := by
    change Tendsto (fun k => mr (φ k) • y k) atTop
      (𝓝 (Submission.InjSup.injSup hmet • y₀))
    exact hmrlimφ.smul hyconv
  have hbn : Tendsto bn atTop (𝓝 (-(Submission.InjSup.injSup hmet • y₀))) := by
    change Tendsto (fun k => -(mr (φ k) • y k)) atTop
      (𝓝 (-(Submission.InjSup.injSup hmet • y₀)))
    exact han.neg
  have hframeV : ∀ k, frameVector (I := I) z₀ (q (φ k)) (an k) = mr (φ k) • w₁ (φ k) := by
    intro k
    change frameVector (I := I) z₀ (q (φ k)) (mr (φ k) • y k) = mr (φ k) • w₁ (φ k)
    rw [Submission.Geodesic.frameVector_smul, ← hframe k]
  have hframeW : ∀ k,
      frameVector (I := I) z₀ (q (φ k)) (bn k) = -(mr (φ k) • w₁ (φ k)) := by
    intro k
    change frameVector (I := I) z₀ (q (φ k)) (-(mr (φ k) • y k)) = -(mr (φ k) • w₁ (φ k))
    rw [Submission.Geodesic.frameVector_neg, Submission.Geodesic.frameVector_smul, ← hframe k]
  have hframeVnorm : ∀ k, ‖frameVector (I := I) z₀ (q (φ k)) (an k)‖ = mr (φ k) := by
    intro k
    rw [hframeV k, norm_smul, Real.norm_of_nonneg (hmr0 (φ k)).le, hw₁unit (φ k), mul_one]
  have hframeWnorm : ∀ k, ‖frameVector (I := I) z₀ (q (φ k)) (bn k)‖ = mr (φ k) := by
    intro k
    rw [hframeW k, norm_neg, norm_smul, Real.norm_of_nonneg (hmr0 (φ k)).le, hw₁unit (φ k),
      mul_one]
  -- ### the limiting vectors are non-zero and distinct
  have hVlimit_ne : frameVector (I := I) z₀ q₀ (Submission.InjSup.injSup hmet • y₀) ≠ 0 := by
    intro h0
    have h4 := congrArg norm h0
    rw [norm_zero, Submission.Geodesic.frameVector_smul, norm_smul,
      Real.norm_of_nonneg hm0.le, hynorm, mul_one] at h4
    exact absurd h4 (ne_of_gt hm0)
  have hdist : frameVector (I := I) z₀ q₀ (Submission.InjSup.injSup hmet • y₀)
      ≠ frameVector (I := I) z₀ q₀ (-(Submission.InjSup.injSup hmet • y₀)) := by
    intro hcon
    rw [Submission.Geodesic.frameVector_neg] at hcon
    refine hVlimit_ne ?_
    have h2 : frameVector (I := I) z₀ q₀ (Submission.InjSup.injSup hmet • y₀)
        + frameVector (I := I) z₀ q₀ (Submission.InjSup.injSup hmet • y₀) = 0 :=
      eq_neg_iff_add_eq_zero.mp hcon
    have h3 : (2 : ℝ) • frameVector (I := I) z₀ q₀ (Submission.InjSup.injSup hmet • y₀) = 0 := by
      rw [two_smul]
      exact h2
    exact (smul_eq_zero.mp h3).resolve_left (by norm_num)
  -- ### the eventual properties along the subsequence
  have hne_ev : ∀ᶠ k in atTop, frameVector (I := I) z₀ (q (φ k)) (an k)
      ≠ frameVector (I := I) z₀ (q (φ k)) (bn k) := by
    filter_upwards with k
    rw [hframeV k, hframeW k]
    intro hcon
    have h2 : (2 : ℝ) • (mr (φ k) • w₁ (φ k)) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hcon
    have h3 : mr (φ k) • w₁ (φ k) = 0 := (smul_eq_zero.mp h2).resolve_left (by norm_num)
    have h4 := hVnorm (φ k)
    rw [h3, norm_zero] at h4
    exact absurd h4.symm (ne_of_gt (hmr0 (φ k)))
  have heq_ev : ∀ᶠ k in atTop,
      GExp (cov := cov) hmet (q (φ k)) (frameVector (I := I) z₀ (q (φ k)) (an k))
        = GExp (cov := cov) hmet (q (φ k)) (frameVector (I := I) z₀ (q (φ k)) (bn k)) := by
    filter_upwards with k
    rw [hframeV k, hframeW k]
    exact (hVpos (φ k)).trans (hVneg (φ k)).symm
  -- ### the limit step
  have hfail : ∀ r' : ℝ, Submission.InjSup.injSup hmet < r' →
      ¬ Submission.InjRadius.InjAtLeast hmet q₀ r' := by
    intro r' hr'
    have hr : Submission.InjSup.injSup hmet
        < (Submission.InjSup.injSup hmet + r') / 2 := by linarith
    have hrr : (Submission.InjSup.injSup hmet + r') / 2 < r' := by linarith
    refine Submission.KlingenbergAttain.not_injAtLeast_of_tendsto_witness (cov := cov) hmet htor
      (z₀ := z₀) (p₀ := q₀)
      (r := (Submission.InjSup.injSup hmet + r') / 2)
      hq₀src hqconv han hbn hdist ?_ hne_ev heq_ev r' hrr
    have hev : ∀ᶠ k in atTop,
        mr (φ k) < (Submission.InjSup.injSup hmet + r') / 2 :=
      hmrlimφ.eventually (isOpen_Iio.mem_nhds hr)
    filter_upwards [hev] with k hk
    rw [hframeVnorm k, hframeWnorm k]
    exact ⟨hk, hk⟩
  exact ⟨q₀, Submission.InjSup.injAllAtLeast_injSup hmet q₀, hfail⟩

end Work.EvenBound.Attain
