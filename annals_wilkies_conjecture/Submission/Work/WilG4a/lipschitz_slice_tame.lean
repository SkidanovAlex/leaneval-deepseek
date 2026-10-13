/-
  WilG4a — the one-variable tameness of the slices of a family member (`SliceTame`).

  `SliceTame S p F0` is the fibre-wise form of the one-variable smoothness theorem: for
  every `Ω`-definable family member `f : ℝᵖ × ℝ → ℝ` of format `F0` and degree `D`, and
  every parameter value `l`, the set of `x` at which the slice `x ↦ f l x` fails to be `C¹`
  has empty interior.

  The hypothesis `hsm` is the corresponding statement for *every* `Ω`-definable function of
  every arity: `graphOf g ∈ S.Ω F D (n+1)` implies that the non-`C¹` locus of `g` has empty
  interior.  The proof is then:

  * **Slice the graph.**  `graphFam f` is, by definition, the graph of the uncurried family
    member `G z = f (z ∘ Fin.castSucc) (z (Fin.last p))`, and
    `Work.WilG1.Thin.sliceGraph_mem` turns the `Ω`-membership of `graphOf G` into one of
    `graphOf (fun u : Fin 1 → ℝ => f l (u 0))`: one fixes the first `p` coordinates to `l`
    by intersecting with `p` hyperplane sections (each of a *linear* polynomial, hence of
    uniformly bounded degree), and then reindexes the two remaining coordinates with
    `Work.WilG5.coordImage_mem`.

  * **Apply `hsm`** at arity `1` to that slice, obtaining that the non-`C¹` locus of
    `u ↦ f l (u 0)` has empty interior.

  * **Transport along `Fin 1 → ℝ ≃ ℝ`.**  Composition with the linear map `u ↦ u 0` and the
    diagonal `s ↦ (fun _ => s)` identifies `C¹` points of `u ↦ f l (u 0)` with `C¹` points of
    the slice `x ↦ f l x`; then `contDiffAt_one_iff` exhibits a neighbourhood `u` on which
    the slice is differentiable with a continuous Fréchet derivative, which is exactly the
    `ε`-`δ` statement appearing in `SliceTame`.
-/
import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG5.Reindex2
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Thin.sliceGraph_mem

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesConjecture WilkiesDesign

namespace Work.WilG4a

/-! ## 1. The smoothness predicate appearing in `SliceTame` -/

/-- The one-variable smoothness condition appearing (negated) in `SliceTame`: the function
`H` is differentiable at `x`, its derivative there is `s`, and *every* nearby point carries a
derivative, close to `s`.  Unfolding this definition gives literally the inner formula of
`SliceTame`. -/
def SliceSmooth (H : ℝ → ℝ) (x : ℝ) : Prop :=
  DifferentiableAt ℝ H x ∧
    ∃ s : ℝ, HasDerivAt H s x ∧
      ∀ ε > 0, ∃ δ > 0, ∀ x' : ℝ, |x' - x| < δ →
        ∃ s' : ℝ, HasDerivAt H s' x' ∧ |s' - s| < ε

/-! ## 2. `C¹` at a point implies the predicate -/

/-- A point at which a real function is `C¹` satisfies `SliceSmooth`.  `contDiffAt_one_iff`
produces a neighbourhood `u` of `x` together with a continuous family of Fréchet derivatives
on `u`; the existence of the derivative at every nearby point comes from that neighbourhood,
and its continuity from the continuity of the derivative family. -/
theorem sliceSmooth_of_contDiffAt {H : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ 1 H x) :
    SliceSmooth H x := by
  obtain ⟨f', u, hu, hcont, hder⟩ := contDiffAt_one_iff.mp h
  have hxu : x ∈ u := mem_of_mem_nhds hu
  refine ⟨h.differentiableAt_one, deriv H x, h.differentiableAt_one.hasDerivAt, ?_⟩
  intro ε hε
  obtain ⟨δ₁, hδ₁, hδ₁u⟩ := Metric.mem_nhds_iff.mp hu
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := (Metric.continuousOn_iff.mp hcont) x hxu ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x' hx' => ?_⟩
  have hx'd₁ : dist x' x < δ₁ :=
    lt_of_lt_of_le (by rwa [Real.dist_eq]) (min_le_left _ _)
  have hx'u : x' ∈ u := hδ₁u hx'd₁
  have hx'd₂ : dist x' x < δ₂ :=
    lt_of_lt_of_le (by rwa [Real.dist_eq]) (min_le_right _ _)
  have hclose : dist (f' x') (f' x) < ε := hδ₂' x' hx'u hx'd₂
  refine ⟨f' x' 1, (hder x' hx'u).hasDerivAt, ?_⟩
  have hs_eq : deriv H x = f' x 1 := (hder x hxu).hasDerivAt.deriv
  rw [hs_eq]
  calc |f' x' 1 - f' x 1| = ‖(f' x' - f' x) 1‖ := by
        rw [sub_apply, Real.norm_eq_abs]
    _ ≤ ‖f' x' - f' x‖ * ‖(1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖f' x' - f' x‖ := by rw [norm_one, mul_one]
    _ = dist (f' x') (f' x) := by rw [dist_eq_norm]
    _ < ε := hclose

/-- `SliceSmooth` transported from `Fin 1 → ℝ` to `ℝ`: a `C¹` point of the function
`u ↦ H (u 0)` is a `C¹` point of `H`.  The point `z` of `Fin 1 → ℝ` is identified with the
real number `z 0`. -/
theorem sliceSmooth_of_contDiffAt_fin1 {H : ℝ → ℝ} (z : Fin 1 → ℝ)
    (h : ContDiffAt ℝ 1 (fun u : Fin 1 → ℝ => H (u 0)) z) : SliceSmooth H (z 0) := by
  have heta : (fun _ : Fin 1 => z 0) = z := by
    funext i
    rw [Subsingleton.elim i 0]
  have h' : ContDiffAt ℝ 1 (fun u : Fin 1 → ℝ => H (u 0)) (fun _ : Fin 1 => z 0) := by
    simpa only [heta] using h
  have hg : ContDiffAt ℝ 1 (fun s : ℝ => (fun _ : Fin 1 => s)) (z 0) :=
    contDiffAt_pi' (fun _ => contDiffAt_id)
  have hcd : ContDiffAt ℝ 1 H (z 0) := by
    simpa [Function.comp_def] using ContDiffAt.comp (z 0) h' hg
  exact sliceSmooth_of_contDiffAt hcd

/-! ## 3. Reduction of `Fin 1 → ℝ` neighbourhoods to `ℝ` neighbourhoods -/

/-- The `ε`-ball of a point of `Fin 1 → ℝ` has the same `0`-coordinate description as the
`ε`-ball of the corresponding real number: `Fin 1 → ℝ` carries the sup metric over a single
coordinate. -/
theorem dist_fin1_eq {z : Fin 1 → ℝ} (x : ℝ) :
    dist z (fun _ : Fin 1 => x) = dist (z 0) x := by
  refine le_antisymm ?_ ?_
  · refine (dist_pi_le_iff (f := z) (g := fun _ : Fin 1 => x) (r := dist (z 0) x)
      dist_nonneg).mpr ?_
    intro i
    rw [Subsingleton.elim i 0]
  · have h := (dist_pi_le_iff (f := z) (g := fun _ : Fin 1 => x)
      (r := dist z (fun _ : Fin 1 => x)) dist_nonneg).mp le_rfl
    simpa using h 0

/-! ## 4. The main theorem -/

theorem lipschitz_slice_tame (S : WilkiesDesign.SOMin) (p F0 : ℕ)
    (hsm : ∀ {n F D : ℕ} (g : (Fin n → ℝ) → ℝ), WilkiesDesign.graphOf g ∈ S.Ω F D (n + 1) →
        interior {z : Fin n → ℝ | ¬ ContDiffAt ℝ 1 g z} = ∅) :
    Work.WilG4a.SliceTame S p F0 := by
  intro D f hf l
  -- The slice `x ↦ f l x` is the one-dimensional graph cut out of `graphFam f`.
  obtain ⟨a, b, hmem⟩ := Work.WilG1.Thin.sliceGraph_mem (S := S) (p := p) (F := F0) (D := D)
    (fun z : Fin (p + 1) → ℝ => f (fun i => z (Fin.castSucc i)) (z (Fin.last p))) hf l
  have hfun : (fun u : Fin 1 → ℝ => (fun z : Fin (p + 1) → ℝ =>
        f (fun i => z (Fin.castSucc i)) (z (Fin.last p))) (Fin.snoc l (u 0)))
      = fun u : Fin 1 → ℝ => f l (u 0) := by
    funext u
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  have hmem' : WilkiesDesign.graphOf (fun u : Fin 1 → ℝ => f l (u 0)) ∈ S.Ω a (b.eval D) 2 := by
    rwa [hfun] at hmem
  -- The one-variable smoothness input, at arity one.
  have hempty := hsm (fun u : Fin 1 → ℝ => f l (u 0)) hmem'
  change interior {x : ℝ | ¬ SliceSmooth (f l) x} = ∅
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  -- A whole ball of `Fin 1 → ℝ` around the point corresponding to `x` is bad.
  have hsub : Metric.ball (fun _ : Fin 1 => x) ε ⊆
      {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fun u : Fin 1 → ℝ => f l (u 0)) z} := by
    intro z hz hcd
    rw [Metric.mem_ball, dist_fin1_eq, Real.dist_eq] at hz
    have hmem_ball : z 0 ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hz
    exact (interior_subset (hball hmem_ball)) (sliceSmooth_of_contDiffAt_fin1 z hcd)
  have hmem_int : (fun _ : Fin 1 => x) ∈ interior
      {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fun u : Fin 1 → ℝ => f l (u 0)) z} := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hε) hsub
  rw [hempty] at hmem_int
  exact hmem_int

end Work.WilG4a
