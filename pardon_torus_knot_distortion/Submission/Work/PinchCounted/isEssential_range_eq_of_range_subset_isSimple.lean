import Mathlib
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_isSimple
import Submission.Work.InnermostDisk.not_isEssential_iff_homotopic_const

/-!
# An essential loop contained in a simple loop fills it

Let `F = P.carrier` be a parametrised torus and let `c`, `γ` be closed curves of `F` with `c`
*simple* (embedded).  This file proves

`Work.PinchCounted.isEssential_range_eq_of_range_subset_isSimple`:

if the image of `γ` is contained in the image of `c` and `γ` is *essential*, then the two images
are equal.

The mathematical content is the standard description of the loops in the image of an embedded
circle: since `c` is simple, its image is a circle and `Set.rangeFactorization c.γ : ℝ → Set.range c.γ`
is a covering map (`Work.InnermostDisk.isCoveringMap_rangeFactorization`), so `γ` lifts to a
continuous `φ : ℝ → ℝ` with `γ = c ∘ φ`.  Over one period `φ` advances by a constant integer
multiple `k·2π` of a period (`LiftOf.continuous_int_multiple_const`), i.e. `γ` is a `k`-fold cover
of `c`.

If `k = 0` then `φ` is `2π`-periodic, so the straight-line interpolation of `φ` to `φ 0` descends
through `c` to a homotopy from `γ` to a constant curve; hence `γ` would be inessential,
contradicting the hypothesis.  Therefore `k ≠ 0`, and then the image of `φ` on one period
`[0, 2π]` contains an interval of length at least `2π` (the interval between `φ 0` and
`φ (2π) = φ 0 + k·2π`); shifting any parameter of `c` into that interval by a period and applying
the intermediate value theorem produces a parameter of `γ`.  So `Set.range c.γ ⊆ Set.range γ.γ`,
and with the hypothesis `Set.range γ.γ = Set.range c.γ`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PinchCounted

noncomputable section

theorem isEssential_range_eq_of_range_subset_isSimple {P : Work.CoreTopology.ParamTorus}
    {γ c : Work.CoreTopology.ClosedCurve P} (hsimp : Work.CoreTopology.IsSimple P c)
    (hsub : Set.range γ.γ ⊆ Set.range c.γ) (hess : Work.CoreTopology.IsEssential P γ) :
    Set.range γ.γ = Set.range c.γ := by
  refine Set.Subset.antisymm hsub ?_
  -- `c` is simple, so it is a covering map onto its image
  have hcov : IsCoveringMap (Set.rangeFactorization c.γ) :=
    Work.InnermostDisk.isCoveringMap_rangeFactorization c.cont c.periodic hsimp
  -- `γ`, viewed as a curve in the circle `Set.range c.γ`
  let γbar : C(ℝ, Set.range c.γ) :=
    ⟨fun t => ⟨γ.γ t, hsub ⟨t, rfl⟩⟩, γ.cont.subtype_mk fun t => hsub ⟨t, rfl⟩⟩
  obtain ⟨s₀, hs₀⟩ := hsub ⟨0, rfl⟩
  -- lift it through the covering by the line
  obtain ⟨φ, ⟨-, hφ⟩, -⟩ := hcov.existsUnique_continuousMap_lifts γbar 0 s₀ (by
    show Set.rangeFactorization c.γ s₀ = γbar 0
    exact Subtype.ext hs₀)
  have hcomp : ∀ t : ℝ, γ.γ t = c.γ (φ t) := by
    intro t
    exact (congrArg Subtype.val (congr_fun hφ t)).symm
  -- the lift advances by a constant integer multiple of `2π` over one period
  have hd : ∀ t : ℝ, ∃ k : ℤ, φ (t + 2 * Real.pi) - φ t = (k : ℝ) * (2 * Real.pi) := by
    intro t
    have h1 : c.γ (φ (t + 2 * Real.pi)) = c.γ (φ t) := by
      rw [← hcomp (t + 2 * Real.pi), ← hcomp t, γ.periodic t]
    obtain ⟨k, hk⟩ :=
      (Work.InnermostDisk.eq_iff_sub_int_mul_two_pi c.periodic
        (show Set.InjOn c.γ (Set.Ico 0 (2 * Real.pi)) from hsimp)
        (φ (t + 2 * Real.pi)) (φ t)).mp h1
    exact ⟨k, by linarith⟩
  obtain ⟨k, hk⟩ := Work.CoreTopology.LiftOf.continuous_int_multiple_const
    (fun t : ℝ => φ (t + 2 * Real.pi) - φ t)
    ((φ.continuous.comp (continuous_id.add continuous_const)).sub φ.continuous) hd
  -- essentiality forces `k ≠ 0`: otherwise `γ` is a reparametrisation through a periodic lift,
  -- hence null-homotopic
  have hkne : k ≠ 0 := by
    intro hk0
    have hper : ∀ t : ℝ, φ (t + 2 * Real.pi) = φ t := by
      intro t
      have h := hk t
      rw [hk0] at h
      exact sub_eq_zero.mp (by simpa using h)
    have hhom : Work.CoreTopology.Homotopic P γ
        (Work.InnermostDisk.constCurve P (c.γ (φ 0)) (c.mem (φ 0))) := by
      refine ⟨fun s t => c.γ ((1 - s) * φ t + s * φ 0), ?_, ?_, ?_, ?_, ?_⟩
      · exact c.cont.comp (by fun_prop)
      · intro s t; exact c.mem _
      · intro t
        show c.γ ((1 - 0) * φ t + 0 * φ 0) = γ.γ t
        rw [hcomp t]; simp
      · intro t
        show c.γ ((1 - 1) * φ t + 1 * φ 0) =
          Work.InnermostDisk.constCurve P (c.γ (φ 0)) (c.mem (φ 0)) t
        simp
      · intro s t
        show c.γ ((1 - s) * φ (t + 2 * Real.pi) + s * φ 0) = c.γ ((1 - s) * φ t + s * φ 0)
        rw [hper t]
    exact (Work.InnermostDisk.not_isEssential_iff_homotopic_const P γ).mpr
      ⟨c.γ (φ 0), c.mem (φ 0), hhom⟩ hess
  -- every value of `c` is a value of `γ`
  intro y hy
  obtain ⟨s, rfl⟩ := hy
  have hφ2π : φ (2 * Real.pi) = φ 0 + (k : ℝ) * (2 * Real.pi) := by
    have := hk 0; rw [zero_add] at this; linarith
  set A : ℝ := min (φ 0) (φ (2 * Real.pi)) with hA
  set B : ℝ := max (φ 0) (φ (2 * Real.pi)) with hB
  -- the image of `φ` over one period contains the whole interval `[A, B]`
  have hivt : Set.Icc A B ⊆ φ '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
    rw [hA, hB]
    rcases le_total (φ 0) (φ (2 * Real.pi)) with h | h
    · rw [min_eq_left h, max_eq_right h]
      exact intermediate_value_Icc (by positivity) φ.continuous.continuousOn
    · rw [min_eq_right h, max_eq_left h]
      exact intermediate_value_Icc' (by positivity) φ.continuous.continuousOn
  -- and that interval has length at least one period, since `k ≠ 0`
  have hlen : 2 * Real.pi ≤ B - A := by
    rw [hA, hB, max_sub_min_eq_abs, hφ2π]
    have harg : φ 0 + (k : ℝ) * (2 * Real.pi) - φ 0 = (k : ℝ) * (2 * Real.pi) := by ring
    rw [harg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hkne
    nlinarith [hk1, Real.pi_pos]
  -- shift the parameter `s` of `c` into that interval
  obtain ⟨m, hm⟩ := Work.InnermostDisk.exists_int_shift_mem_Ico (s - A)
  set s' : ℝ := s + (m : ℝ) * (2 * Real.pi) with hs'
  have hs'A : A ≤ s' := by
    have h1 := hm.1; rw [hs']; linarith
  have hs'B : s' ≤ B := by
    have h1 := hm.2; rw [hs']; linarith
  obtain ⟨t, -, ht⟩ := hivt ⟨hs'A, hs'B⟩
  refine ⟨t, ?_⟩
  show γ.γ t = c.γ s
  rw [hcomp t, ht, hs']
  have hp : Function.Periodic c.γ (2 * Real.pi) := c.periodic
  exact hp.int_mul m s

end

end Work.PinchCounted
