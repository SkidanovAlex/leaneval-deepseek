/-
  WilG4c / StepLipPieces — the piece-level vocabulary of the §5.3 reduction.

  In the corrected route for `Work.WilG4c.StepLip` (see `StepLip_RouteNotes.md` §10) the
  `y`-pullback `G_ψ` of the family is cut by a cylindrical decomposition of the `(λ,s)`-space
  (coordinates: `λ` the `p` parameters, `s` the distinguished cube coordinate), and each cell
  `κ` contributes the *piece*

      `K(λ, t, u) := G_ψ(λ, φ_κ(λ,t), u)`,

  where `φ_κ : (0,1) → (the fibre of κ)` is the exact-cover chart produced by
  `Work.WilkG4c.ChartsExactCell`.  Its `t`-slices are literally the `G_ψ`-slices at the
  `x`-value `φ_κ(λ,t) ∈ I`, which is what makes the `PY`/`YBound` transfer *chain-rule free*.

  This file contains the three elementary transfers that every such piece needs:

  * `slice_pieceFam` — the slice identity `slice (K i l) t = slice (G_ψ i l) (φ_κ l t)`;
  * `pieceFam_ybound` — `YBound` transfers from `G_ψ` (Λ-restricted form, since `YBound` is a
    global predicate over all `l`);
  * `pieceFam_lip` — the metric Lipschitz bound for a piece assembled from its two directional
    bounds (`t`-direction with constant `C`, `u`-direction with constant `1`); the resulting
    constant is `C + 1`, which is what `Work.WilkG4c.LipRescale` consumes.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.Hyps

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- The *piece* of a family `G : Family k p (n+1)` cut by a chart `ψ` of the distinguished
coordinate: `pieceFam G ψ i l z = G i l (cons (ψ l (z 0)) (tail z))`. -/
def pieceFam {k p n : ℕ} (G : Family k p (n + 1)) (ψ : (Fin p → ℝ) → ℝ → ℝ) :
    Family k p (n + 1) :=
  fun i l z => G i l (Fin.cons (ψ l (z 0)) (Fin.tail z))

@[simp] theorem pieceFam_apply {k p n : ℕ} (G : Family k p (n + 1))
    (ψ : (Fin p → ℝ) → ℝ → ℝ) (i : Fin k) (l : Fin p → ℝ) (z : Fin (n + 1) → ℝ) :
    pieceFam G ψ i l z = G i l (Fin.cons (ψ l (z 0)) (Fin.tail z)) := rfl

/-- The `t`-slice of a piece is the `G`-slice at the chart value `ψ l t`: no chain rule. -/
theorem slice_pieceFam {k p n : ℕ} (G : Family k p (n + 1))
    (ψ : (Fin p → ℝ) → ℝ → ℝ) (i : Fin k) (l : Fin p → ℝ) (t : ℝ) :
    slice (pieceFam G ψ i l) t = slice (G i l) (ψ l t) := by
  funext y
  simp [slice, pt, pieceFam]

/-- `YBound` of a piece, in the `Λ`-restricted form: the slices of the piece are the slices of
`G` at `ψ l t`, so the bounds are those of `G` at that point. -/
theorem pieceFam_ybound {k p n r : ℕ} (G : Family k p (n + 1))
    (ψ : (Fin p → ℝ) → ℝ → ℝ) (Λ : Set (Fin p → ℝ))
    (hψI : ∀ l ∈ Λ, ∀ t ∈ I, ψ l t ∈ I)
    (hY : ∀ i, ∀ l ∈ Λ, ∀ x ∈ I, ∀ m, m ≤ r → ∀ y ∈ openCube n,
      ‖iteratedFDeriv ℝ m (slice (G i l) x) y‖ ≤ 1) :
    ∀ i, ∀ l ∈ Λ, ∀ t ∈ I, ∀ m, m ≤ r → ∀ y ∈ openCube n,
      ‖iteratedFDeriv ℝ m (slice (pieceFam G ψ i l) t) y‖ ≤ 1 := by
  intro i l hl t ht m hm y hy
  rw [slice_pieceFam]
  exact hY i l hl (ψ l t) (hψI l hl t ht) m hm y hy

/-- The `u`-direction of a piece at a fixed chart value: it is the corresponding slice of `G`,
so its Lipschitz constant is that of the slice. -/
theorem pieceFam_lipY {k p n : ℕ} {G : Family k p (n + 1)}
    {ψ : (Fin p → ℝ) → ℝ → ℝ} {i : Fin k} {l : Fin p → ℝ} {x : ℝ}
    (hLip : ∀ u ∈ openCube n, ∀ u' ∈ openCube n,
      |G i l (Fin.cons (ψ l x) u) - G i l (Fin.cons (ψ l x) u')| ≤ dist u u') :
    ∀ u ∈ openCube n, ∀ u' ∈ openCube n,
      |pieceFam G ψ i l (Fin.cons x u) - pieceFam G ψ i l (Fin.cons x u')| ≤ dist u u' := by
  intro u hu u' hu'
  simpa [pieceFam] using hLip u hu u' hu'

/-- **The metric Lipschitz bound of a piece**, assembled from its two directional bounds: the
`u`-direction (constant `1`, at a fixed chart value) and the `t`-direction (constant `C`, at a
fixed `u`).  The resulting constant is `C + 1`. -/
theorem pieceFam_lip {k p n : ℕ} {G : Family k p (n + 1)} {ψ : (Fin p → ℝ) → ℝ → ℝ}
    {i : Fin k} {l : Fin p → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hψI : ∀ t ∈ I, ψ l t ∈ I)
    (hψlip : ∀ t ∈ I, ∀ t' ∈ I, |ψ l t - ψ l t'| ≤ |t - t'|)
    (hu : ∀ x ∈ I, ∀ u ∈ openCube n, ∀ u' ∈ openCube n,
      |G i l (Fin.cons x u) - G i l (Fin.cons x u')| ≤ dist u u')
    (ht : ∀ t ∈ I, ∀ t' ∈ I, ∀ u ∈ openCube n,
      |G i l (Fin.cons t u) - G i l (Fin.cons t' u)| ≤ C * |t - t'|) :
    ∀ z ∈ openCube (n + 1), ∀ z' ∈ openCube (n + 1),
      |pieceFam G ψ i l z - pieceFam G ψ i l z'| ≤ (C + 1) * dist z z' := by
  intro z hz z' hz'
  have hz0I : z 0 ∈ I := hz 0
  have hz0'I : z' 0 ∈ I := hz' 0
  have htz : Fin.tail z ∈ openCube n := fun j => hz j.succ
  have htz' : Fin.tail z' ∈ openCube n := fun j => hz' j.succ
  -- the intermediate slice: the chart value of `z` with the tail of `z'`
  have hstep1 : |pieceFam G ψ i l z
      - G i l (Fin.cons (ψ l (z 0)) (Fin.tail z'))| ≤ dist (Fin.tail z) (Fin.tail z') := by
    have h := hu (ψ l (z 0)) (hψI (z 0) hz0I) (Fin.tail z) htz (Fin.tail z') htz'
    simpa [pieceFam] using h
  have hstep2 : |G i l (Fin.cons (ψ l (z 0)) (Fin.tail z'))
      - pieceFam G ψ i l z'| ≤ C * |z 0 - z' 0| := by
    have h := ht (ψ l (z 0)) (hψI (z 0) hz0I) (ψ l (z' 0)) (hψI (z' 0) hz0'I)
      (Fin.tail z') htz'
    have hψ := hψlip (z 0) hz0I (z' 0) hz0'I
    have hmono : C * |ψ l (z 0) - ψ l (z' 0)| ≤ C * |z 0 - z' 0| :=
      mul_le_mul_of_nonneg_left hψ hC
    have h' : |G i l (Fin.cons (ψ l (z 0)) (Fin.tail z'))
        - G i l (Fin.cons (ψ l (z' 0)) (Fin.tail z'))| ≤ C * |ψ l (z 0) - ψ l (z' 0)| := by
      simpa using h
    have h'' : |G i l (Fin.cons (ψ l (z 0)) (Fin.tail z'))
        - pieceFam G ψ i l z'| ≤ C * |ψ l (z 0) - ψ l (z' 0)| := by
      simpa [pieceFam] using h'
    linarith
  have h1 : dist (Fin.tail z) (Fin.tail z') ≤ dist z z' := by
    rw [dist_pi_le_iff dist_nonneg]
    intro j
    exact dist_le_pi_dist z z' j.succ
  have h2 : |z 0 - z' 0| ≤ dist z z' := by
    have h := dist_le_pi_dist z z' (0 : Fin (n + 1))
    rwa [Real.dist_eq] at h
  calc |pieceFam G ψ i l z - pieceFam G ψ i l z'|
      ≤ |pieceFam G ψ i l z - G i l (Fin.cons (ψ l (z 0)) (Fin.tail z'))|
        + |G i l (Fin.cons (ψ l (z 0)) (Fin.tail z')) - pieceFam G ψ i l z'| := abs_sub_le _ _ _
    _ ≤ dist (Fin.tail z) (Fin.tail z') + C * |z 0 - z' 0| := add_le_add hstep1 hstep2
    _ ≤ dist z z' + C * dist z z' :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 hC)
    _ = (C + 1) * dist z z' := by ring

end Work.WilkG4c
