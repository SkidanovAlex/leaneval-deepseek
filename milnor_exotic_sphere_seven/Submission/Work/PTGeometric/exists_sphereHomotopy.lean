import Mathlib
import Submission.Work.Stems.exists_collapsingMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Descending a cube homotopy along a collapse of the boundary

`φ : Iⁿ → Sⁿ` is the quotient map collapsing the boundary of the cube to a point (the
hypotheses `hφ hφfib` say precisely that it is a quotient map which only identifies boundary
points among themselves).  A homotopy `H : I × Iⁿ → T` which is constant on the boundary of the
cube and at time `1` therefore factors through `φ` in the cube variable, giving a homotopy
`Sⁿ × I → T` out of the sphere, still constant at time `1`.

The proof is the quotient-map computation `continuous_lift_prod_left` (product of a quotient map
with a locally compact space) plus the observation that `H (t, ·)` is constant on the fibres of
`φ`:  two cube points with the same image are either equal, or both lie on the boundary, where
`H` is constant for every time.
-/

namespace Work.PTGeometric

theorem exists_sphereHomotopy {n : ℕ} (hn : 1 ≤ n)
    (φ : C(Fin n → Set.Icc (0 : ℝ) 1, Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
    (hφ : Topology.IsQuotientMap φ)
    (hφfib : ∀ q q' : Fin n → Set.Icc (0 : ℝ) 1, φ q = φ q' →
      q = q' ∨ (q ∈ _root_.Cube.boundary (Fin n) ∧ q' ∈ _root_.Cube.boundary (Fin n)))
    {T : Type} [TopologicalSpace T] {y₀ : T} (H : C(Set.Icc (0 : ℝ) 1 × (Fin n → Set.Icc (0 : ℝ) 1), T))
    (hH : ∀ (t : Set.Icc (0 : ℝ) 1) (y : Fin n → Set.Icc (0 : ℝ) 1),
      y ∈ _root_.Cube.boundary (Fin n) → H (t, y) = y₀)
    (hH1 : ∀ y : Fin n → Set.Icc (0 : ℝ) 1, H (1, y) = y₀) :
    ∃ Hbar : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (0 : ℝ) 1, T),
      (∀ (y : Fin n → Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) 1), Hbar (φ y, t) = H (t, y)) ∧
      (∀ s : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, Hbar (s, 1) = y₀) := by
  classical
  -- `H (t, ·)` is constant on the fibres of `φ`.
  have key : ∀ (y y' : Fin n → Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) 1),
      φ y = φ y' → H (t, y) = H (t, y') := by
    intro y y' t h
    rcases hφfib y y' h with h' | ⟨hy, hy'⟩
    · rw [h']
    · rw [hH t y hy, hH t y' hy']
  -- the descended map on `Sⁿ × I`, defined by choosing a cube preimage.
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Set.Icc (0 : ℝ) 1 → T :=
    fun p => H (p.2, (hφ.surjective p.1).choose)
  have hg_apply : ∀ (y : Fin n → Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) 1),
      g (φ y, t) = H (t, y) := by
    intro y t
    show H (t, (hφ.surjective (φ y)).choose) = H (t, y)
    exact key _ _ t (hφ.surjective (φ y)).choose_spec
  -- it is continuous, because after composing with `φ × id` it is `(y,t) ↦ H (t,y)`.
  have hcont : Continuous fun p : (Fin n → Set.Icc (0 : ℝ) 1) × Set.Icc (0 : ℝ) 1 =>
      g (φ p.1, p.2) := by
    have hfun : (fun p : (Fin n → Set.Icc (0 : ℝ) 1) × Set.Icc (0 : ℝ) 1 =>
        g (φ p.1, p.2)) = fun p => H (p.2, p.1) := by
      funext p
      exact hg_apply p.1 p.2
    rw [hfun]
    exact H.continuous.comp (continuous_snd.prodMk continuous_fst)
  have hgcont : Continuous g := hφ.continuous_lift_prod_left hcont
  refine ⟨⟨g, hgcont⟩, ?_, ?_⟩
  · intro y t
    exact hg_apply y t
  · intro s
    obtain ⟨y, hy⟩ := hφ.surjective s
    rw [← hy]
    show g (φ y, (1 : Set.Icc (0 : ℝ) 1)) = y₀
    rw [hg_apply y 1]
    exact hH1 y

end Work.PTGeometric
