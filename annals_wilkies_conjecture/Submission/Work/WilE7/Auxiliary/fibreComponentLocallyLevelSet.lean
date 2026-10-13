import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Auxiliary.analyticLevelSetChart
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.eventually_mem_fiber_of_good
import Submission.Work.WilE7.fiber_germ_subset_component

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace Work.WilE7.Auxiliary

open WilkiesDesign WilkiesDesign.E

/-- **The connected component of a point of a `Good` stratum's fibre is locally the level set of
the defining equations.**

Let `S` be a `Good` stratum of format `(p, q)`, `z ∈ S.X.set`, `x₀ = projFirst p q z` the base
point and `C = connectedComponentIn (fiber S.X.set x₀) (projSnd p q z)` the connected component of
`projSnd p q z` in the fibre of `S.X.set` over `x₀`.

Two facts combine.

* *`C ⊆ {h = 0}` globally.*  Every point `y` of the fibre over `x₀` gives a point
  `Fin.append x₀ y` of `S.X.set`, and the `Good` condition says that the equations `h_a` vanish at
  every point of `S.X.set`.  So `C ⊆ {y | eaEval (h a) (x₀, y) = 0}`.

* *`{h = 0} ⊆ C` locally.*  By `Good`, near `y₀ ∈ C` the fibre over `x₀` *coincides* with the level
  set of the analytic map `g : y ↦ (eaEval S.X.c (S.h a) (x₀, y))_a`, whose derivative at `y₀` is
  surjective (the fibrewise Jacobian of the `h_a` has full row rank `S.j`).  By
  `fiber_germ_subset_component` the fibre is a germ of `C` near `y₀`: there is `ε > 0` such that
  every point of the fibre at distance `< ε` from `y₀` already lies in `C`.  The remaining
  `Good`-neighbourhood converts the level-set condition into membership in the fibre.

Hence `U := ball y₀ (min ε ε₁)` (with `ε₁` the radius of the `Good`-neighbourhood) satisfies
`C ∩ U = {h = 0} ∩ U`, and it contains `y₀`. -/
theorem fibreComponentLocallyLevelSet {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (hGood : S.Good) (z : Fin (p + q) → ℝ) (hz : z ∈ S.X.set) :
    ∀ y₀ ∈ connectedComponentIn (WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z))
        (WilkiesDesign.E.projSnd p q z),
      ∃ U : Set (Fin q → ℝ), IsOpen U ∧ y₀ ∈ U ∧
        connectedComponentIn (WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z))
            (WilkiesDesign.E.projSnd p q z) ∩ U
          = {y | (fun a : Fin S.j => WilkiesDesign.E.eaEval S.X.c (S.h a)
                (Fin.append (WilkiesDesign.E.projFirst p q z) y)) = 0} ∩ U := by
  intro y₀ hy₀
  -- `Fin.append x₀ y₀` is a point of the stratum, hence `Good` applies there.
  have hzf : Fin.append (WilkiesDesign.E.projFirst p q z) y₀ ∈ S.X.set :=
    (Work.WilE7.mem_fiber_iff S.X.set (WilkiesDesign.E.projFirst p q z) y₀).mp
      (connectedComponentIn_subset _ _ hy₀)
  -- The fibre is a germ of the connected component of `y₀` (local connectivity at `y₀`).
  obtain ⟨ε, hεpos, hε⟩ :=
    Work.WilE7.fiber_germ_subset_component S hGood
      (Fin.append (WilkiesDesign.E.projFirst p q z) y₀) hzf
  have hε' : ∀ y' : Fin q → ℝ, dist y' y₀ < ε →
      y' ∈ WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z) →
      y' ∈ connectedComponentIn
        (WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z)) y₀ := by
    intro y' hd hmem
    have h1 := hε y' (by simpa only [Work.WilE7.projSnd_append] using hd)
      (by simpa only [Work.WilE7.projFirst_append] using hmem)
    simpa only [Work.WilE7.projFirst_append, Work.WilE7.projSnd_append] using h1
  -- The `Good`-neighbourhood: near `y₀`, the level set of `h` lies in the fibre.
  obtain ⟨ε₁, hε₁pos, hε₁₀⟩ :=
    Metric.eventually_nhds_iff.mp
      (Work.WilE7.eventually_mem_fiber_of_good S hGood (WilkiesDesign.E.projFirst p q z) y₀ hzf)
  have hε₁ : ∀ y' : Fin q → ℝ, dist y' y₀ < ε₁ →
      (∀ a, WilkiesDesign.E.eaEval S.X.c (S.h a)
        (Fin.append (WilkiesDesign.E.projFirst p q z) y') = 0) →
      y' ∈ WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z) :=
    fun y' hd h0 => hε₁₀ hd h0
  refine ⟨Metric.ball y₀ (min ε ε₁), Metric.isOpen_ball,
    Metric.mem_ball_self (lt_min hεpos hε₁pos), ?_⟩
  ext y
  constructor
  · -- `C ∩ U ⊆ {h = 0} ∩ U`: use that `Good` kills `h` on all of `S.X.set`.
    intro hy
    obtain ⟨hyC, hyU⟩ := hy
    have hyX : Fin.append (WilkiesDesign.E.projFirst p q z) y ∈ S.X.set :=
      (Work.WilE7.mem_fiber_iff S.X.set (WilkiesDesign.E.projFirst p q z) y).mp
        (connectedComponentIn_subset _ _ hyC)
    refine ⟨?_, hyU⟩
    funext a
    simpa using (hGood (Fin.append (WilkiesDesign.E.projFirst p q z) y) hyX).1 a
  · -- `{h = 0} ∩ U ⊆ C ∩ U`: convert the level set into the fibre, then into `C`.
    intro hy
    obtain ⟨hyZ, hyU⟩ := hy
    have hd : dist y y₀ < min ε ε₁ := Metric.mem_ball.mp hyU
    have hyfib : y ∈ WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z) :=
      hε₁ y (lt_of_lt_of_le hd (min_le_right ε ε₁)) (fun a => by
        simpa using congrFun hyZ a)
    have hyC : y ∈ connectedComponentIn
        (WilkiesDesign.E.fiber S.X.set (WilkiesDesign.E.projFirst p q z)) y₀ :=
      hε' y (lt_of_lt_of_le hd (min_le_left ε ε₁)) hyfib
    refine ⟨?_, hyU⟩
    -- `y₀` and `projSnd p q z` lie in the same connected component of the fibre.
    rw [connectedComponentIn_eq hy₀]
    exact hyC

end Work.WilE7.Auxiliary
