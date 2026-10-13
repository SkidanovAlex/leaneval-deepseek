/-
  WilG4c — the *fibre* (slice) regularity of a family member.

  The `Ω`-machinery of BNZ §§5.2–5.5 controls the *joint* object `famFunHat f` on
  `ℝ^{p+N}`, and in particular (through `SharpCD`) the *joint* non-`C^k` locus
  `badLoc f k = (cLoc f k)ᶜ`, i.e. the complement of the interior of the joint `C^k`
  locus.  The F-lemma, however, is a statement about the *fibre* functions
  `z ↦ f l z` at a *fixed* parameter `l` (`ChartsOK` asks for `ContDiffOn` of
  `t ↦ F i l (φ l t)`): only the fibre regularity is ever used.

  The two notions differ exactly on the thin joint-bad locus: `f l z = |l| + z/3` is
  nowhere jointly `C¹` on the line `l = 0`, while every fibre `z ↦ |l| + z/3` is
  `C^∞` there.  So the *fibre* bad locus is strictly *smaller* than the joint one —
  but `Ω` is not closed under subsets, hence the fibre bad locus is not directly
  `Ω`-bounded (this is the open hole `Work.WilG4c.FibreSmoothSet` /
  `Work.WilG4c.SliceDerivGraphMem`).

  What *is* true, and is what this file records, is that the **fibre itself is again a
  definable object with a uniform format and degree**:

  * `fibreGraphMem` — the graph `graphOf (z ↦ f l z)` of the `l`-fibre of a family
    member whose `famGraph` is `Ω F0 D (p+N+1)` is `Ω (F0+K) (D+K) (N+1)` for a
    constant `K` depending only on `p, N` — in particular *uniformly in the point `l`*.
    (This is the slice stability of `Ω`; the proof uses the already existing
    `Work.WilG4c.sliceGraph_mem_gen'`, which intersects `famGraph f` with the `p`
    coordinate hyperplanes `z_i = l_i` (each of degree `1`) and then keeps the trailing
    `N+1` coordinates.)

  * `fibreBadThin` — consequently the closure of the fibre non-`C¹` locus of `f l`
    has empty interior, again with a format/degree uniform in `l`.
    (`Work.WilG4c.interior_closure_nonC1_empty` applied to the `l`-fibre.)

  * `fibreGoodDense` — the fibre `C¹`-locus of `f l` is dense in every ball of the open
    cube: the escape points that §5.5 needs at a fibre-nonsmooth point can always be
    found *inside the fibre* (where the parameter is kept fixed), which is what the
    "Lipschitz escape" in the clean-up argument requires.

  This is the provable half of the fibre-smoothness analysis; the unprovable half
  (`Ω`-boundedness of the fibre bad locus itself) is *not* needed for the density
  statement above and remains the open hole of the area.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.graphOf_member_mem
import Submission.Work.WilG4c.badCurveStrip_interior_empty

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Fibres of `famFun` -/

/-- Reading `famFun f` at a glued point recovers the family member: `famFun f (l ⌢ u) = f l u`. -/
theorem famFun_append' {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (l : Fin p → ℝ)
    (u : Fin N → ℝ) : famFun f (Fin.append l u) = f l u := by
  rw [famFun]
  congr 1
  · funext i; exact Fin.append_left l u i
  · funext j; exact Fin.append_right l u j

/-- The `l`-fibre functions of a family member agree. -/
theorem fibre_fun_eq {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (l : Fin p → ℝ) :
    (fun u : Fin N → ℝ => famFun f (Fin.append l u)) = (fun u : Fin N → ℝ => f l u) :=
  funext (fun u => famFun_append' f l u)

/-! ## 2. The fibre graph is `Ω`-bounded, uniformly in the parameter -/

/-- **The `l`-fibre graph of a family member is `Ω`-bounded, uniformly in `l`.**  There is a
constant `K` depending only on `p` and `N` such that for every format `F0`, degree `D`, family
member `f` with `famGraph f ∈ S.Ω F0 D (p+N+1)` and every parameter `l ∈ ℝ^p`, the graph of the
fibre function `z ↦ f l z` (over `ℝ^{N+1}`) is `Ω`-definable at format `F0 + K` and degree
`D + K`.

This is the slice-stability of `Ω` (`Work.WilG4c.sliceGraph_mem_gen'`): intersecting the
`Ω`-set `famGraph f` with the `p` coordinate hyperplanes `z i = l i` (each cut out by the
degree-one polynomial `X i - C (l i)`) costs only the *sum* of the degrees, so the resulting
degree is `D + p + …` — a constant shift, i.e. uniform in `l` and linear in `D`. -/
theorem fibreGraphMem (S : SOMin) (p N : ℕ) :
    ∃ K : ℕ, ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (l : Fin p → ℝ),
      famGraph f ∈ S.Ω F0 D (p + N + 1) →
      graphOf (fun z : Fin N → ℝ => f l z) ∈ S.Ω (F0 + K) (D + K) (N + 1) := by
  obtain ⟨K, hK⟩ := sliceGraph_mem_gen' S p N
  refine ⟨K, ?_⟩
  intro F0 D f l hf
  have h := hK F0 D (famFun f) l (by rwa [graphOf_famFun])
  rwa [fibre_fun_eq f l] at h

/-! ## 3. The fibre bad locus has nowhere dense closure -/

/-- **The fibre non-`C¹` locus of a family member has nowhere dense closure**, uniformly in
the parameter.  There is a constant `K` depending only on `p`, `N` such that for every
`f` with `famGraph f ∈ S.Ω F0 D (p+N+1)` and every `l`,
`interior (closure {z : ¬ ContDiffAt ℝ 1 (z ↦ f l z) z}) = ∅`.

Proof: by `fibreGraphMem` the fibre function is a definable function with `Ω`-graph at a
format/degree independent of `l`, so `Work.WilG4c.interior_closure_nonC1_empty` (generic
smoothness of definable functions, from `SharpCD`) applies uniformly. -/
theorem fibreBadThin (S : SOMin) (hcd : S.SharpCD) (p N : ℕ) :
    ∃ K : ℕ, ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (l : Fin p → ℝ),
      famGraph f ∈ S.Ω F0 D (p + N + 1) →
      interior (closure {z : Fin N → ℝ | ¬ ContDiffAt ℝ 1 (fun z : Fin N → ℝ => f l z) z})
        = ∅ := by
  obtain ⟨K, hK⟩ := fibreGraphMem S p N
  refine ⟨K, ?_⟩
  intro F0 D f l hf
  exact interior_closure_nonC1_empty S hcd (fun z : Fin N → ℝ => f l z) (hK F0 D f l hf)

/-! ## 4. Density of the fibre-good locus -/

/-- The open cube is open. -/
theorem openCube_isOpen' (N : ℕ) : IsOpen (openCube N) := by
  have h : openCube N
      = ⋂ i : Fin N, (fun p : Fin N → ℝ => p i) ⁻¹' Set.Ioo (0 : ℝ) 1 := by
    ext t
    simp only [openCube, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (continuous_apply i))

/-- **The fibre `C¹`-locus of a family member is dense in each ball of the open cube.**
There is a constant `K` (only depending on `p`, `N`) such that for every `f` with
`famGraph f ∈ S.Ω F0 D (p+N+1)`, every `l`, every `x ∈ openCube N` and every `η > 0` there
is `z ∈ openCube N` with `dist z x < η` at which the *fibre* function `z ↦ f l z` is `C¹`.

This is the "escape in the fibre" statement used by the §5.5 clean-up: at a fibre-nonsmooth
point one may always move, *inside the same fibre*, to a fibre-smooth point — the parameter
`l` is not changed, which is essential since the F-lemma only supplies Lipschitz control in
the fibre variables.

Note that this density is *fibre-wise*: the joint `C¹` locus of `famFun f` can be empty on a
whole fibre (e.g. `f l z = (2 + |l| + g z)/5`, `g` smooth), so no joint statement can replace
it.  The proof uses that the fibre-bad closure has empty interior (`fibreBadThin`). -/
theorem fibreGoodDense (S : SOMin) (hcd : S.SharpCD) (p N : ℕ) :
    ∃ K : ℕ, ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (l : Fin p → ℝ),
      famGraph f ∈ S.Ω F0 D (p + N + 1) →
      ∀ x ∈ openCube N, ∀ η : ℝ, 0 < η →
        ∃ z ∈ openCube N, dist z x < η ∧ ContDiffAt ℝ 1 (fun z : Fin N → ℝ => f l z) z := by
  obtain ⟨K, hK⟩ := fibreBadThin S hcd p N
  refine ⟨K, ?_⟩
  intro F0 D f l hf x hx η hη
  set B : Set (Fin N → ℝ) := {z : Fin N → ℝ | ¬ ContDiffAt ℝ 1 (fun z : Fin N → ℝ => f l z) z}
    with hB
  have hthin : interior (closure B) = ∅ := hK F0 D f l hf
  -- the open ball intersected with the cube is a nonempty open set, so it is not contained
  -- in the (empty-interior) closure of `B`
  have hne : (openCube N ∩ Metric.ball x η).Nonempty := by
    refine ⟨x, hx, ?_⟩
    rw [Metric.mem_ball]
    simpa using hη
  have hopen : IsOpen (openCube N ∩ Metric.ball x η) :=
    (openCube_isOpen' N).inter Metric.isOpen_ball
  by_contra hcon
  push_neg at hcon
  -- every point of the ball ∩ cube is in the closure of `B`
  have hsub : openCube N ∩ Metric.ball x η ⊆ closure B := by
    intro z hz
    exact subset_closure (hcon z hz.1 (Metric.mem_ball.mp hz.2))
  have hsub' : openCube N ∩ Metric.ball x η ⊆ interior (closure B) :=
    interior_maximal hsub hopen
  rw [hthin] at hsub'
  exact Set.not_nonempty_empty (hne.mono (fun z hz => hsub' hz))

end Work.WilG4c
