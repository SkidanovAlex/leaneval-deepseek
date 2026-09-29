import Mathlib
import Submission.Work.TMContract.Defs
import Submission.Work.TMC13.PruferCore
import Submission.Work.TMC13.pruferCore_continuous
import Submission.Work.TMComp.RotBasics.PS

/-!
# The Prüfer lift `pruferStep a` of the companion matrix `!![a,-1;1,0]`

`Work.TMContract.pruferStep a t` is the Prüfer angle (in half-turns: `π` is one unit) of
the direction `(cos πt, sin πt)` under the companion matrix `!![a,-1;1,0]`.  This module
assembles the four facts about it that the Ten Martini development uses:

* joint continuity in `(a,t)`;
* the degree-one property `pruferStep a (t+1) = pruferStep a t + 1`;
* monotonicity in `t` (an increasing circle map of degree one);
* the direction relation: the image of `(cos πt, sin πt)` under `!![a,-1;1,0]` is a nonzero
  multiple of `(cos (π * pruferStep a t), sin (π * pruferStep a t))`.

The continuity proof uses the decomposition `pruferStep a t = t + pruferCore a (fract (t+1/2))`
of `Submission/Work/TMC13/PruferCore.lean` together with the continuity of the periodic core
on `ℝ × [0,1]` (`Work.TMC13.pruferCore_continuous`) and the gluing theorem
`ContinuousOn.comp_fract` of Mathlib.
-/

open Matrix

namespace Work.TMC13

noncomputable section

/-- The companion matrix acts on the vector `(x,y)` as `(x,y) ↦ (a x - y, x)`. -/
theorem mulVec_comp (a x y : ℝ) :
    Matrix.mulVec (!![a, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![x, y] = ![a * x - y, x] := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- `pruferStep a t = t + pruferCore a (fract (t + 1/2))`: the lift is the sum of the
identity and the `1`-periodic core evaluated at `fract (t + 1/2)`. -/
theorem pruferStep_eq_core (a t : ℝ) :
    Work.TMContract.pruferStep a t = t + pruferCore a (Int.fract (t + 1 / 2)) := by
  rw [Work.TMContract.pruferStep]
  set k : ℤ := ⌊t + 1 / 2⌋ with hk
  have hfrac : Int.fract (t + 1 / 2) = t + 1 / 2 - (k : ℝ) := rfl
  by_cases h0 : t - (k : ℝ) = -1 / 2
  · rw [if_pos h0, hfrac]
    have hzero : t + 1 / 2 - (k : ℝ) = 0 := by linarith
    rw [hzero, pruferCore_zero]
    linarith
  · rw [if_neg h0, hfrac]
    have hr1 : ¬ (t + 1 / 2 - (k : ℝ) = 1) := by
      intro hc
      have hlt := Int.fract_lt_one (t + 1 / 2)
      rw [hfrac] at hlt
      linarith
    have hr0 : ¬ (t + 1 / 2 - (k : ℝ) = 0) := by intro hc; exact h0 (by linarith)
    unfold pruferCore
    rw [if_neg hr1, if_neg hr0]
    have hrs : t + 1 / 2 - (k : ℝ) - 1 / 2 = t - (k : ℝ) := by ring
    rw [hrs]
    ring

/-- `pruferStep` is jointly continuous in `(a,t)`. -/
theorem continuous_pruferStep_pair :
    Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2) := by
  have hcomp : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => pruferCore q.1.1 q.2)
      (Set.univ ×ˢ Set.Icc 0 1) :=
    pruferCore_continuous.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) (by fun_prop)
      (by rintro ⟨⟨a, t⟩, r⟩ ⟨-, hr⟩; exact ⟨trivial, hr⟩)
  have hglue : Continuous (fun p : ℝ × ℝ => pruferCore p.1 (Int.fract (p.2 + 1/2))) :=
    ContinuousOn.comp_fract (f := fun p : ℝ × ℝ => fun r : ℝ => pruferCore p.1 r)
      hcomp (by fun_prop)
      (fun p => by rw [pruferCore_zero, pruferCore_one])
  have hEq : (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2)
      = fun p : ℝ × ℝ => p.2 + pruferCore p.1 (Int.fract (p.2 + 1/2)) := by
    funext p
    exact pruferStep_eq_core p.1 p.2
  rw [hEq]
  exact continuous_snd.add hglue

/-- `pruferStep a` is a degree-one circle map: shifting the argument by one (a half turn)
shifts the value by one. -/
theorem pruferStep_period (a t : ℝ) :
    Work.TMContract.pruferStep a (t + 1) = Work.TMContract.pruferStep a t + 1 := by
  have hfl : ⌊t + 1 + 1/2⌋ = ⌊t + 1/2⌋ + 1 := by
    rw [show t + 1 + 1/2 = (t + 1/2) + 1 by ring, Int.floor_add_one]
  simp only [Work.TMContract.pruferStep, hfl]
  rw [show t + 1 - (((⌊t + 1 / 2⌋ + 1 : ℤ)) : ℝ) = t - ((⌊t + 1/2⌋ : ℤ) : ℝ)
    by push_cast; ring]
  split_ifs with h <;> (push_cast; ring)

/-- `pruferStep a` is monotone in `t`. -/
theorem monotone_pruferStep (a : ℝ) : Monotone (Work.TMContract.pruferStep a) :=
  Work.TMComp.RotBasics.pruferStep_mono a

/-- The direction relation, in the vector form `Fin 2 → ℝ`: the companion matrix sends the
direction `(cos πt, sin πt)` to the direction `(cos (π * pruferStep a t), sin (...))` up to
a nonzero real multiple. -/
theorem prufer_dir_vec (a t : ℝ) :
    ∃ c : ℝ, c ≠ 0 ∧
      Matrix.mulVec (!![a, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
          ![Real.cos (Real.pi * t), Real.sin (Real.pi * t)] =
        c • ![Real.cos (Real.pi * Work.TMContract.pruferStep a t),
              Real.sin (Real.pi * Work.TMContract.pruferStep a t)] := by
  obtain ⟨ρ, hρ, h⟩ := Work.TMComp.RotBasics.pruferStep_smul_eq a t
  refine ⟨ρ, ne_of_gt hρ, ?_⟩
  -- Package the two `Fin 2 → ℝ` vectors as complex numbers.
  have hmix : (⟨a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t),
      Real.cos (Real.pi * t)⟩ : ℂ)
      = ρ • Work.TMComp.RotBasics.vc (Work.TMContract.pruferStep a t) := by
    rw [← Work.TMComp.RotBasics.smul_comp a t]
    exact h
  have h1 : a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t)
      = ρ * Real.cos (Real.pi * Work.TMContract.pruferStep a t) := by
    have := congrArg Complex.re hmix
    simpa [Work.TMComp.RotBasics.vc, Complex.smul_re] using this
  have h2 : Real.cos (Real.pi * t)
      = ρ * Real.sin (Real.pi * Work.TMContract.pruferStep a t) := by
    have := congrArg Complex.im hmix
    simpa [Work.TMComp.RotBasics.vc, Complex.smul_im] using this
  rw [mulVec_comp]
  funext i
  fin_cases i
  · simpa using h1
  · simpa using h2

/-- **The Prüfer lift of the companion matrix `!![a,-1;1,0]`.**  `pruferStep a` is a
continuous, monotone degree-one lift of the projective action of `!![a,-1;1,0]` on
directions `(cos πt, sin πt)`: it is jointly continuous in `(a,t)`, satisfies
`pruferStep a (t+1) = pruferStep a t + 1`, is monotone in `t`, and the matrix sends the
direction `(cos πt, sin πt)` to the direction `(cos (π * pruferStep a t), sin (...))`. -/
theorem prufer_lift (a : ℝ) :
    Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferStep p.1 p.2) ∧
    (∀ t : ℝ, Work.TMContract.pruferStep a (t + 1) = Work.TMContract.pruferStep a t + 1) ∧
    Monotone (Work.TMContract.pruferStep a) ∧
    (∀ t : ℝ, ∃ c : ℝ, c ≠ 0 ∧
      Matrix.mulVec (!![a, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)
          ![Real.cos (Real.pi * t), Real.sin (Real.pi * t)] =
        c • ![Real.cos (Real.pi * Work.TMContract.pruferStep a t),
              Real.sin (Real.pi * Work.TMContract.pruferStep a t)]) :=
  ⟨continuous_pruferStep_pair, fun t => pruferStep_period a t, monotone_pruferStep a,
    fun t => prufer_dir_vec a t⟩

end

end Work.TMC13
