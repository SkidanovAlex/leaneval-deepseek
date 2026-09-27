import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.modelFlowDefs

/-!
# The window datum of the `n = 2` critical-window drawing

This file carries the *data structure* (and only the structure, no existence proof) that the
critical-window drawing of `Work.Drive.N2.criticalWindowDrawing` consumes:

* an injective enumeration `x` of the critical points of `f` (with a marked index `j` at the
  prescribed critical point `p`),
* pairwise disjoint Morse charts `φ i` at them, centred, with the signed quadratic normal form
  `f = f (x i) + chartQ (φ i) (s₁ i) (s₂ i)`,
* a chart radius `ρ i` and a closed chart region `C i` (whose closure is contained in the chart)
  containing the ball of radius `ρ i / 8`,
* the value separation of the balls: the balls of the *other* charts carry no value of distance
  `≤ 2 * ηd` from `f (x j)`,
* the model-adapted level flow `Φ` with its laws (`Φ (0,y) = y`, the composition law, the level law
  off the balls and the chart ODE on the regions `C i`),
* the monotonicity of `f` along the orbits.

The existence proof (`Work.Drive.N2.windowDatumExists`) is the bookkeeping of
`exists_injective_enum_critical`, `exists_disjoint_chart_neighborhoods`, `exists_morseChart_fixed`,
`exists_shrunk_chart_data`, `exists_modelRadii_strictSeparation`,
`exists_modelAdapted_levelFlow_chartODE` and `levelMonoOn_of_modelAdaptedFlow`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The model chart datum of the `n = 2` window construction. -/
structure WindowDatum (f : M → ℝ) (p : M) where
  N : ℕ
  x : Fin N → M
  φ : Fin N → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))
  s₁ : Fin N → ℝ
  s₂ : Fin N → ℝ
  ρ : Fin N → ℝ
  C : Fin N → Set M
  j : Fin N
  hxj : x j = p
  hinj : Function.Injective x
  hcrit : ∀ i, Work.Drive.Morse.IsCritical f (x i)
  hcover : ∀ y, Work.Drive.Morse.IsCritical f y → ∃ i, x i = y
  hρ : ∀ i, 0 < ρ i
  hsrc : ∀ i, x i ∈ (φ i).source
  hcen : ∀ i, φ i (x i) = 0
  hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1)
  hval : ∀ i y, y ∈ (φ i).source → f y = f (x i) + chartQ (φ i) (s₁ i) (s₂ i) y
  hφ : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => φ i y) (φ i).source
  hφ' : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z => (φ i).symm z) (φ i).target
  hdisj : ∀ i j', i ≠ j' → Disjoint (φ i).source (φ j').source
  hCsub : ∀ i, C i ⊆ (φ i).source
  hCclosed : ∀ i, IsClosed (C i)
  hCcl : ∀ i, IsCompact (closure (C i)) ∧ closure (C i) ⊆ (φ i).source
  hCball : ∀ i, modelBall (φ i) (ρ i / 8) ⊆ C i
  hCop : ∀ i, {y : M | y ∈ (φ i).source ∧ ‖φ i y‖ < ρ i} ⊆ C i
  ηd : ℝ
  hηd : 0 < ηd
  hηd' : ηd < 1 / 10
  hsep : ∀ i j', i ≠ j' → 2 * ηd < |f (x i) - f (x j')|
  hsepK : ∀ i j', i ≠ j' → ∀ z : M, z ∈ modelBall (φ i) (ρ i / 8) →
    2 * ηd < |f z - f (x j')|
  Φ : ℝ × M → M
  hΦsm : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΦ0 : ∀ y : M, Φ (0, y) = y
  hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y)
  hlevel : ∀ (y : M) (t : ℝ),
    (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i,
      Φ (u, y) ∉ modelBall (φ i) (ρ i / 8)) →
    f (Φ (t, y)) = f y + t
  hODE : ∀ (i : Fin N) (y : M) (t : ℝ),
    (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
    HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
      (chartMult (ρ i / 8) (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
    HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
      (chartMult (ρ i / 8) (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t
  hmono : ∀ y : M, MonotoneOn (fun t : ℝ => f (Φ (t, y))) (Set.Ici 0)

/-- The balls of the other charts are contained in the closed set of values at distance `≥ 2 * ηd`
from the value of the marked point; this is the form of the separation the legality consumes. -/
theorem WindowDatum.mem_K_of_mem_other {f : M → ℝ} {p : M} (D : WindowDatum f p)
    {i : Fin D.N}
    (hi : i ≠ D.j) {z : M} (hz : z ∈ modelBall (D.φ i) (D.ρ i / 8)) :
    2 * D.ηd ≤ |f z - f (D.x D.j)| := by
  have h := D.hsepK i D.j hi z hz
  have h' : |f z - f (D.x D.j)| = |f (D.x D.j) - f z| := abs_sub_comm _ _
  linarith [h, h']

end Work.Drive.N2
