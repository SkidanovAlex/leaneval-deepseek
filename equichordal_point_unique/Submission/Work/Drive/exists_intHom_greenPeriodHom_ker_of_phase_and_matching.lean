import Mathlib
import Submission.Work.Drive.exists_continuous_singleZero_phase
import Submission.Work.Drive.greenPeriodHom_eq_windingHom
import Submission.Work.Analysis.RiemannSurface.windingHom_unconditional

namespace Work.Drive

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

/-- **The lift of `Θ u₀` at `w₀'` is the deck shift of the lift at `w₀`.**  If `w₀' = w₀ + m·2πi`
then the two points of the logarithmic fibre differ by the deck shift `logFiberShift ℓ m`. -/
theorem logPt_eq_logFiberShift_of_exp_eq {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
    (ℓ : Y → ℂ) (y₀ : Y) {w₀ w₀' : ℂ} (hw₀ : Complex.exp w₀ = ℓ y₀)
    (hw₀' : Complex.exp w₀' = ℓ y₀) (m : ℤ)
    (hm : w₀' = w₀ + (m : ℂ) * (2 * Real.pi * Complex.I)) :
    Work.SimplyConnected.ABS.logPt ℓ y₀ w₀' hw₀' =
      Work.SimplyConnected.ABS.logFiberShift ℓ m (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀ hw₀) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · rw [Work.SimplyConnected.ABS.logFiberShift_coe, Work.SimplyConnected.ABS.logShift_coe]
    exact hm

/-- **The winding integers of the logarithmic cover do not depend on the chosen lift** of the base
value: if `W` reads off the monodromy of the log cover of `ℓ` at the lift `w₀` of `ℓ y₀`, then it
reads it off at *every* lift `w₀'` of `ℓ y₀` as well.  This converts the single-lift form
`Work.Analysis.RiemannSurface.exists_windingHom_of_continuous` into the `∀ w₀` form required by the
matching hypothesis. -/
theorem windingHom_indep_of_lift {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
    (ℓ : Y → ℂ) (hℓ : Continuous ℓ) (hne : ∀ y, ℓ y ≠ 0)
    (y₀ : Y) (w₀ : ℂ) (hw₀ : Complex.exp w₀ = ℓ y₀)
    (W : Additive (FundamentalGroup Y y₀) →+ ℤ)
    (hW : ∀ γ : FundamentalGroup Y y₀,
      Work.SimplyConnected.ABS.logCoord ℓ
        ((Work.Analysis.RiemannSurface.isCoveringMap_logProj ℓ hℓ hne).monodromy γ
          (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀ hw₀)).1
        = w₀ + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I)) :
    ∀ (w₀' : ℂ) (hw₀' : Complex.exp w₀' = ℓ y₀) (γ : FundamentalGroup Y y₀),
      Work.SimplyConnected.ABS.logCoord ℓ
        ((Work.Analysis.RiemannSurface.isCoveringMap_logProj ℓ hℓ hne).monodromy γ
          (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀' hw₀')).1
        = w₀' + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I) := by
  intro w₀' hw₀' γ
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hw₀'.trans hw₀.symm)
  have hpt := logPt_eq_logFiberShift_of_exp_eq ℓ y₀ hw₀ hw₀' m hm
  have hmono : (Work.Analysis.RiemannSurface.isCoveringMap_logProj ℓ hℓ hne).monodromy γ
      (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀' hw₀')
      = Work.SimplyConnected.ABS.logFiberShift ℓ m
          ((Work.Analysis.RiemannSurface.isCoveringMap_logProj ℓ hℓ hne).monodromy γ
            (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀ hw₀)) := by
    rw [hpt, Work.SimplyConnected.ABS.monodromy_logShift]
  calc Work.SimplyConnected.ABS.logCoord ℓ
        ((Work.Analysis.RiemannSurface.isCoveringMap_logProj ℓ hℓ hne).monodromy γ
          (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀' hw₀')).1
      = Work.SimplyConnected.ABS.logCoord ℓ
          ↑(Work.SimplyConnected.ABS.logFiberShift ℓ m
            ((Work.Analysis.RiemannSurface.isCoveringMap_logProj ℓ hℓ hne).monodromy γ
              (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀ hw₀))) := by rw [hmono]
    _ = Work.SimplyConnected.ABS.logCoord ℓ
          ↑((Work.Analysis.RiemannSurface.isCoveringMap_logProj ℓ hℓ hne).monodromy γ
              (Work.SimplyConnected.ABS.logPt ℓ y₀ w₀ hw₀))
          + (m : ℂ) * (2 * Real.pi * Complex.I) :=
        Work.SimplyConnected.ABS.logCoord_logFiberShift ℓ m _
    _ = (w₀ + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I))
          + (m : ℂ) * (2 * Real.pi * Complex.I) := by rw [hW γ]
    _ = w₀' + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hm]; ring


theorem exists_intHom_greenPeriodHom_ker_of_phase_and_matching {X : Type*}
    [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hEharm : Submission.HarmonicOnX E (Set.univ \ {z₀}))
    (hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {z₀}) z₀ E)
    (u₀ : Work.Modulus.puncturedOpens z₀)
    (hphase : ∃ Θ : X → ℂ, Continuous Θ ∧ (∀ x : X, x ≠ z₀ → Θ x ≠ 0) ∧
      ∃ (u : X → ℂ) (V : Set X), V ∈ nhds z₀ ∧ ContinuousOn u V ∧ (∀ x ∈ V, u x ≠ 0) ∧
        ∀ x ∈ V, Θ x = ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀) * u x)
    (hmatch : ∀ (Θ : X → ℂ) (hΘ : Continuous Θ) (hΘne : ∀ x : X, x ≠ z₀ → Θ x ≠ 0)
      (hloc : ∃ (u : X → ℂ) (V : Set X), V ∈ nhds z₀ ∧ ContinuousOn u V ∧
        (∀ x ∈ V, u x ≠ 0) ∧
        ∀ x ∈ V, Θ x = ((chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀) * u x)
      (u : Work.Modulus.puncturedOpens z₀)
      (W : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u) →+ ℤ),
      (∀ (w₀ : ℂ) (hw₀ : Complex.exp w₀ = Θ u.1)
        (γ : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u),
        Work.SimplyConnected.ABS.logCoord (fun v : ↥(Work.Modulus.puncturedOpens z₀) => Θ v.1)
          ((Work.Analysis.RiemannSurface.isCoveringMap_logProj
              (fun v : ↥(Work.Modulus.puncturedOpens z₀) => Θ v.1)
              (hΘ.comp continuous_subtype_val) (fun v => hΘne v.1 v.2)).monodromy γ
            (Work.SimplyConnected.ABS.logPt (fun v : ↥(Work.Modulus.puncturedOpens z₀) => Θ v.1)
              u w₀ hw₀)).1
          = w₀ + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I)) →
      ∀ γ : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u),
        Work.SimplyConnected.ABS.inclMapP z₀ u (Additive.toMul γ) = 1 →
          Work.ModulusLP.greenPeriodHom hEharm u γ = -(W γ : ℝ) * (2 * Real.pi) ∨
          Work.ModulusLP.greenPeriodHom hEharm u γ = (W γ : ℝ) * (2 * Real.pi)) :
    ∃ W : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀) →+ ℤ,
      ∀ γ : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
        Work.SimplyConnected.ABS.inclMapP z₀ u₀ (Additive.toMul γ) = 1 →
          Work.ModulusLP.greenPeriodHom hEharm u₀ γ = (W γ : ℝ) * (2 * Real.pi) := by
  obtain ⟨Θ, hΘ, hΘne, hloc⟩ := hphase
  let ℓ : ↥(Work.Modulus.puncturedOpens z₀) → ℂ := fun v => Θ v.1
  have hℓ : Continuous ℓ := hΘ.comp continuous_subtype_val
  have hℓne : ∀ v : ↥(Work.Modulus.puncturedOpens z₀), ℓ v ≠ 0 := fun v => hΘne v.1 v.2
  haveI : ConnectedSpace ↥(Work.Modulus.puncturedOpens z₀) := Work.Modulus.puncturedConnected z₀
  obtain ⟨w₀, hw₀⟩ : ∃ w : ℂ, Complex.exp w = ℓ u₀ :=
    ⟨Complex.log (ℓ u₀), Complex.exp_log (hℓne u₀)⟩
  obtain ⟨W, hW⟩ :=
    Work.Analysis.RiemannSurface.exists_windingHom_of_continuous ℓ hℓ hℓne u₀ w₀ hw₀
  have hWall : ∀ (w : ℂ) (hw : Complex.exp w = Θ u₀.1)
      (γ : FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
      Work.SimplyConnected.ABS.logCoord
        (fun v : ↥(Work.Modulus.puncturedOpens z₀) => Θ v.1)
        ((Work.Analysis.RiemannSurface.isCoveringMap_logProj
            (fun v : ↥(Work.Modulus.puncturedOpens z₀) => Θ v.1)
            (hΘ.comp continuous_subtype_val) (fun v => hΘne v.1 v.2)).monodromy γ
          (Work.SimplyConnected.ABS.logPt
            (fun v : ↥(Work.Modulus.puncturedOpens z₀) => Θ v.1) u₀ w hw)).1
        = w + (W (Additive.ofMul γ) : ℂ) * (2 * Real.pi * Complex.I) :=
    windingHom_indep_of_lift ℓ hℓ hℓne u₀ w₀ hw₀ W hW
  have hdisj := hmatch Θ hΘ hΘne hloc u₀ W hWall
  by_cases hgood : ∀ γ : Additive (FundamentalGroup (↥(Work.Modulus.puncturedOpens z₀)) u₀),
      Work.SimplyConnected.ABS.inclMapP z₀ u₀ (Additive.toMul γ) = 1 →
        Work.ModulusLP.greenPeriodHom hEharm u₀ γ = (W γ : ℝ) * (2 * Real.pi)
  · exact ⟨W, hgood⟩
  · push_neg at hgood
    obtain ⟨γ₀, hγ₀ker, hγ₀ne⟩ := hgood
    have hγ₀ : Work.ModulusLP.greenPeriodHom hEharm u₀ γ₀ = -(W γ₀ : ℝ) * (2 * Real.pi) :=
      (hdisj γ₀ hγ₀ker).resolve_right hγ₀ne
    have hWγ₀ : W γ₀ ≠ 0 := by
      intro h0
      exact hγ₀ne (by rw [hγ₀, h0]; norm_num)
    refine ⟨-W, ?_⟩
    intro γ hγker
    have hπ : (2 * (Real.pi : ℝ)) ≠ 0 := by positivity
    rcases hdisj γ hγker with h | h
    · rw [h]
      simp [AddMonoidHom.neg_apply]
    · by_cases hWγ : W γ = 0
      · rw [h, hWγ]
        simp [AddMonoidHom.neg_apply, hWγ]
      · exfalso
        have hker_add : Work.SimplyConnected.ABS.inclMapP z₀ u₀
            (Additive.toMul (γ₀ + γ)) = 1 := by
          have h1 : Additive.toMul (γ₀ + γ) = Additive.toMul γ₀ * Additive.toMul γ := rfl
          rw [h1, map_mul, hγ₀ker, hγker, mul_one]
        have hPsum : Work.ModulusLP.greenPeriodHom hEharm u₀ (γ₀ + γ)
            = ((W γ : ℝ) - (W γ₀ : ℝ)) * (2 * Real.pi) := by
          rw [map_add, hγ₀, h]; ring
        have hWsum : ((W (γ₀ + γ) : ℤ) : ℝ) = (W γ₀ : ℝ) + (W γ : ℝ) := by
          rw [map_add]; push_cast; ring
        rcases hdisj (γ₀ + γ) hker_add with hA | hB
        · have heq : ((W γ : ℝ) - (W γ₀ : ℝ)) * (2 * Real.pi)
              = -((W γ₀ : ℝ) + (W γ : ℝ)) * (2 * Real.pi) := by
            rw [← hPsum, hA, hWsum]
          have h2 : (W γ : ℝ) - (W γ₀ : ℝ) = -((W γ₀ : ℝ) + (W γ : ℝ)) :=
            mul_right_cancel₀ hπ heq
          have hz : (W γ : ℝ) = 0 := by linarith
          exact hWγ (by exact_mod_cast hz)
        · have heq : ((W γ : ℝ) - (W γ₀ : ℝ)) * (2 * Real.pi)
              = ((W γ₀ : ℝ) + (W γ : ℝ)) * (2 * Real.pi) := by
            rw [← hPsum, hB, hWsum]
          have h2 : (W γ : ℝ) - (W γ₀ : ℝ) = (W γ₀ : ℝ) + (W γ : ℝ) :=
            mul_right_cancel₀ hπ heq
          have hz : (W γ₀ : ℝ) = 0 := by linarith
          exact hWγ₀ (by exact_mod_cast hz)

end Work.Drive
