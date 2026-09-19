import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_neg_one_tight

noncomputable section

open Complex Filter Set
open scoped Real Topology

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Finitely many zero-heights in a unit window

For a non-trivial primitive Dirichlet character, the zeros of the completed
L-function all have real part in the open strip `(0,1)` (commons theorem
`zerosInStrip`).  Since a non-identically-zero entire function has no
accumulation point of zeros, any bounded window of heights therefore contains
only finitely many distinct zero heights.
-/

/-- An entire function that is not identically zero has only finitely many zeros
meeting any compact set. -/
private lemma finite_zeros_inter_compact {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hfne : ¬ ∀ z : ℂ, f z = 0) {K : Set ℂ}
    (hK : IsCompact K) : (K ∩ {z : ℂ | f z = 0}).Finite := by
  -- `f` is analytic on the (preconnected) whole plane; since it is not identically
  -- zero, its zero set has no accumulation point.
  have hne' : ∀ᶠ x in codiscreteWithin (Set.univ : Set ℂ), f x ≠ 0 := by
    have h := AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected (𝕜 := ℂ)
      hf isPreconnected_univ
    rcases h with hEq | hnz
    · exfalso
      apply hfne
      intro z
      exact hEq (by trivial : z ∈ (Set.univ : Set ℂ))
    · exact hnz
  have hnoAcc : ∀ x : ℂ, ¬ AccPt x (𝓟 {z : ℂ | f z = 0}) := by
    intro x hx
    have hm := (mem_codiscreteWithin_accPt.mp hne') x trivial
    apply hm
    apply AccPt.mono hx
    have hset : {z : ℂ | f z = 0} =
        (Set.univ : Set ℂ) \ {z : ℂ | f z ≠ 0} := by
      ext z
      by_cases hfz : f z = 0 <;> simp [hfz]
    rw [hset]
  by_contra hinf
  rcases Set.Infinite.exists_accPt_of_subset_isCompact hinf hK
    (Set.inter_subset_left (s := K) (t := {z : ℂ | f z = 0})) with ⟨x, _hxK, hxAcc⟩
  exact hnoAcc x (AccPt.mono hxAcc
    (principal_mono.mpr
      (Set.inter_subset_right (s := K) (t := {z : ℂ | f z = 0}))))

/-- Zeros of the completed L-function of a non-trivial primitive character with
imaginary part in the open unit window `(c, c+1)` lie in a fixed compact disc. -/
private lemma zerosInWindow_mem_closedBall {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    (c : ℝ) (z : ℂ) (hz0 : DirichletCharacter.completedLFunction χ z = 0)
    (hzc : c < z.im) (hz1 : z.im < c + 1) :
    z ∈ Metric.closedBall (0 : ℂ) (|c| + |c + 1| + 3) := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hst := zerosInStrip χ hχ hχprim z hz0
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ (1 : ℝ) + (|c| + 1) := by
      have hre_abs : |z.re| ≤ 1 := by
        have hre_nonneg : 0 ≤ z.re := le_of_lt hst.1
        rw [abs_of_nonneg hre_nonneg]
        exact le_of_lt hst.2
      have him_abs : |z.im| ≤ |c| + 1 := by
        have hzsub0 : 0 < z.im - c := by linarith
        have hzsub1 : z.im - c < 1 := by linarith
        have hzsub_abs : |z.im - c| ≤ 1 := by
          rw [abs_of_nonneg (le_of_lt hzsub0)]
          exact le_of_lt hzsub1
        calc
          |z.im| = |c + (z.im - c)| := by
            congr 1
            ring
          _ ≤ |c| + |z.im - c| := abs_add_le c (z.im - c)
          _ ≤ |c| + 1 := add_le_add (le_refl |c|) hzsub_abs
      exact add_le_add hre_abs him_abs
    _ ≤ |c| + |c + 1| + 3 := by
      nlinarith [abs_nonneg (c + 1)]

theorem finite_zeroHeights_window {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (c : ℝ) :
    Set.Finite {y : ℝ | ∃ u : ℂ,
      DirichletCharacter.completedLFunction χ u = 0 ∧ c < u.im ∧ u.im < c + 1 ∧ u.im = y} := by
  let R : ℝ := |c| + |c + 1| + 3
  let Zwin : Set ℂ := {z : ℂ |
    DirichletCharacter.completedLFunction χ z = 0 ∧ c < z.im ∧ z.im < c + 1}
  -- the heights are exactly the imaginary parts of the zeros in the window
  have hY : {y : ℝ | ∃ u : ℂ,
        DirichletCharacter.completedLFunction χ u = 0 ∧ c < u.im ∧ u.im < c + 1 ∧ u.im = y} =
      (fun u : ℂ => u.im) '' Zwin := by
    ext y
    constructor
    · rintro ⟨u, hu0, huc, hu1, rfl⟩
      exact ⟨u, ⟨hu0, huc, hu1⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, hu.2.1, hu.2.2, rfl⟩
  -- whole-plane analyticity of Λ(χ, ·)
  have hΛan : AnalyticOnNhd ℂ
      (fun z : ℂ => DirichletCharacter.completedLFunction χ z) Set.univ := by
    intro z hz
    exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z
  -- Λ(χ, ·) is not identically zero (zeros have real part in (0,1), so 2 is not a zero)
  have hΛne : ¬ ∀ z : ℂ, DirichletCharacter.completedLFunction χ z = 0 := by
    intro hzall
    have h2 : DirichletCharacter.completedLFunction χ (2 : ℂ) = 0 := hzall (2 : ℂ)
    have hst := zerosInStrip χ hχ hχprim (2 : ℂ) h2
    have : (2 : ℂ).re < 1 := hst.2
    norm_num at this
  -- every zero in the window lies in the compact disc of radius R around 0
  have hZwin_sub : Zwin ⊆
      Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | DirichletCharacter.completedLFunction χ z = 0} := by
    intro z hz
    rcases hz with ⟨hz0, hzc, hz1⟩
    constructor
    · dsimp [R]
      exact zerosInWindow_mem_closedBall χ hχ hχprim c z hz0 hzc hz1
    · exact hz0
  have hZwinFin : Zwin.Finite := by
    exact (finite_zeros_inter_compact (K := Metric.closedBall (0 : ℂ) R) hΛan hΛne
      (isCompact_closedBall 0 R)).subset hZwin_sub
  rw [hY]
  exact hZwinFin.image (fun u : ℂ => u.im)

end Commons.NumberTheory.DirichletCharacter