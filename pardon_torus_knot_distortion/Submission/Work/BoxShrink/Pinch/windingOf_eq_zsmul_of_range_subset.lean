import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_isSimple

namespace Work.BoxShrink.Pinch

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- **The parameter functions of a lift advance by integer multiples of `2π`.**  If `L` is a
lift of a closed curve of the torus `P`, then over a shift of the *parameter* by `m` periods the
two coordinates of the lift advance by `m` times the corresponding component of the winding
vector.  This is `LiftOf.period_shift_winding` iterated; the clean way to iterate it is to note
that `u ↦ L.Θ u - (L.winding).1 * u` is `2π`-periodic. -/
theorem liftOf_shift_int {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) (s : ℝ) (m : ℤ) :
    L.Θ (s + m * (2 * Real.pi)) = L.Θ s + m * (L.winding).1 * (2 * Real.pi) ∧
    L.Φ (s + m * (2 * Real.pi)) = L.Φ s + m * (L.winding).2 * (2 * Real.pi) := by
  have hperΘ : Function.Periodic
      (fun u : ℝ => L.Θ u - ((L.winding).1 : ℝ) * u) (2 * Real.pi) := by
    intro u
    show L.Θ (u + 2 * Real.pi) - ((L.winding).1 : ℝ) * (u + 2 * Real.pi)
        = L.Θ u - ((L.winding).1 : ℝ) * u
    rw [(L.period_shift_winding u).1]
    ring
  have hperΦ : Function.Periodic
      (fun u : ℝ => L.Φ u - ((L.winding).2 : ℝ) * u) (2 * Real.pi) := by
    intro u
    show L.Φ (u + 2 * Real.pi) - ((L.winding).2 : ℝ) * (u + 2 * Real.pi)
        = L.Φ u - ((L.winding).2 : ℝ) * u
    rw [(L.period_shift_winding u).2]
    ring
  constructor
  · have hh : L.Θ (s + m * (2 * Real.pi)) - ((L.winding).1 : ℝ) * (s + m * (2 * Real.pi))
        = L.Θ s - ((L.winding).1 : ℝ) * s := hperΘ.int_mul m s
    have h2 : L.Θ (s + m * (2 * Real.pi)) - L.Θ s
        = ((L.winding).1 : ℝ) * ((m : ℝ) * (2 * Real.pi)) := by
      rw [mul_add] at hh
      linarith
    have h3 : ((L.winding).1 : ℝ) * ((m : ℝ) * (2 * Real.pi))
        = (m : ℝ) * (L.winding).1 * (2 * Real.pi) := by ring
    linarith [h2, h3]
  · have hh : L.Φ (s + m * (2 * Real.pi)) - ((L.winding).2 : ℝ) * (s + m * (2 * Real.pi))
        = L.Φ s - ((L.winding).2 : ℝ) * s := hperΦ.int_mul m s
    have h2 : L.Φ (s + m * (2 * Real.pi)) - L.Φ s
        = ((L.winding).2 : ℝ) * ((m : ℝ) * (2 * Real.pi)) := by
      rw [mul_add] at hh
      linarith
    have h3 : ((L.winding).2 : ℝ) * ((m : ℝ) * (2 * Real.pi))
        = (m : ℝ) * (L.winding).2 * (2 * Real.pi) := by ring
    linarith [h2, h3]

/-- A closed curve `γ` whose image lies in the image of a *simple* closed curve `γ₀` has winding
vector an integer multiple of that of `γ₀`. -/
theorem windingOf_eq_zsmul_of_range_subset {P : Work.CoreTopology.ParamTorus}
    {γ γ₀ : Work.CoreTopology.ClosedCurve P} (hs : Work.CoreTopology.IsSimple P γ₀)
    (h : Set.range γ.γ ⊆ Set.range γ₀.γ) :
    ∃ k : ℤ, Work.SurgeryInvariance.windingOf P γ = k • Work.SurgeryInvariance.windingOf P γ₀ := by
  -- the simple curve `γ₀` is a covering map onto its image
  have hcov : IsCoveringMap (Set.rangeFactorization γ₀.γ) :=
    Work.InnermostDisk.isCoveringMap_rangeFactorization γ₀.cont γ₀.periodic hs
  -- `γ`, viewed as a curve in the image of `γ₀`
  let γbar : C(ℝ, Set.range γ₀.γ) :=
    ⟨fun t => ⟨γ.γ t, h ⟨t, rfl⟩⟩, γ.cont.subtype_mk fun t => h ⟨t, rfl⟩⟩
  obtain ⟨s₀, hs₀⟩ := h ⟨0, rfl⟩
  -- lift it through the covering by the line
  obtain ⟨φ, ⟨-, hφ⟩, -⟩ := hcov.existsUnique_continuousMap_lifts γbar 0 s₀ (by
    show Set.rangeFactorization γ₀.γ s₀ = γbar 0
    exact Subtype.ext hs₀)
  have hcomp : ∀ t : ℝ, γ₀.γ (φ t) = γ.γ t := by
    intro t
    exact congrArg Subtype.val (congr_fun hφ t)
  -- `φ` advances by a constant integer multiple of `2π` over one period
  have hd : ∀ t : ℝ, ∃ k : ℤ, φ (t + 2 * Real.pi) - φ t = k * (2 * Real.pi) := by
    intro t
    have h1 : γ₀.γ (φ (t + 2 * Real.pi)) = γ₀.γ (φ t) := by
      rw [hcomp (t + 2 * Real.pi), hcomp t, γ.periodic t]
    obtain ⟨k, hk⟩ := (Work.InnermostDisk.eq_iff_sub_int_mul_two_pi γ₀.periodic hs
      (φ (t + 2 * Real.pi)) (φ t)).mp h1
    exact ⟨k, by linarith⟩
  obtain ⟨k, hk⟩ := Work.CoreTopology.LiftOf.continuous_int_multiple_const
    (fun t : ℝ => φ (t + 2 * Real.pi) - φ t)
    ((φ.continuous.comp (continuous_id.add continuous_const)).sub φ.continuous) hd
  have hφ0 : φ (2 * Real.pi) = φ 0 + (k : ℝ) * (2 * Real.pi) := by
    have := hk 0
    simp only [zero_add] at this
    linarith
  -- a lift of `γ₀` and the induced lift of `γ`
  obtain ⟨L₀⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ₀
  let L : Work.CoreTopology.LiftOf P γ :=
    { Θ := fun t => L₀.Θ (φ t)
      Φ := fun t => L₀.Φ (φ t)
      contΘ := L₀.contΘ.comp φ.continuous
      contΦ := L₀.contΦ.comp φ.continuous
      lifts := fun t => (L₀.lifts (φ t)).trans (hcomp t) }
  have hshift := liftOf_shift_int L₀ (φ 0) k
  -- the two winding vectors agree up to the factor `k`
  have hZ1 : (L.winding).1 = k * (L₀.winding).1 := by
    have hspec := L.winding_spec
    have e1 : L.Θ (2 * Real.pi) = L.Θ 0 + (k : ℝ) * (L₀.winding).1 * (2 * Real.pi) := by
      show L₀.Θ (φ (2 * Real.pi)) = L₀.Θ (φ 0) + (k : ℝ) * (L₀.winding).1 * (2 * Real.pi)
      rw [hφ0, hshift.1]
    have hR : ((L.winding).1 : ℝ) * (2 * Real.pi)
        = ((k : ℝ) * ((L₀.winding).1 : ℝ)) * (2 * Real.pi) := by
      linarith [hspec.1, e1]
    have hc := mul_right_cancel₀ Work.CoreTopology.two_pi_ne_zero hR
    exact_mod_cast hc
  have hZ2 : (L.winding).2 = k * (L₀.winding).2 := by
    have hspec := L.winding_spec
    have e2 : L.Φ (2 * Real.pi) = L.Φ 0 + (k : ℝ) * (L₀.winding).2 * (2 * Real.pi) := by
      show L₀.Φ (φ (2 * Real.pi)) = L₀.Φ (φ 0) + (k : ℝ) * (L₀.winding).2 * (2 * Real.pi)
      rw [hφ0, hshift.2]
    have hR : ((L.winding).2 : ℝ) * (2 * Real.pi)
        = ((k : ℝ) * ((L₀.winding).2 : ℝ)) * (2 * Real.pi) := by
      linarith [hspec.2, e2]
    have hc := mul_right_cancel₀ Work.CoreTopology.two_pi_ne_zero hR
    exact_mod_cast hc
  have hLwind : L.winding = k • L₀.winding := by
    apply Prod.ext
    · show (L.winding).1 = (k • L₀.winding).1
      rw [hZ1]
      simp
    · show (L.winding).2 = (k • L₀.winding).2
      rw [hZ2]
      simp
  refine ⟨k, ?_⟩
  rw [Work.SurgeryInvariance.windingOf_eq P γ L, Work.SurgeryInvariance.windingOf_eq P γ₀ L₀]
  exact hLwind

end

end Work.BoxShrink.Pinch
