import Mathlib
import Submission.Work.ThomBordism.Grassmann.thomSpacePieces
import Submission.Work.ThomBordism.Grassmann.Torsion.contractibleFar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The escape to infinity: avoiding the zero section lets one push into the far region

The first of the two steps of the proof that the chart pieces of the Thom space
(`Work.ThomBordism.Grassmann.chartPiece`) are `(k-1)`-connected.

**The statement** (`escape_to_far`).  Let `f : I^j → Th γ` be continuous into the metric-free Thom
space `OnePoint (TotalSpace γ)`, whose image **avoids the zero section** (`fibN (f x) ≠ 0` whenever
`f x` is a point of the total space) and whose boundary values lie in the far region
`far 1 = {fibN > 1} ∪ {∞}`.  Then `f` is homotopic, **relative to `∂I^j`**, into `far 1`.

**The construction.**  The radial escape of `Torsion.pushF` (`some p ↦ (1-s)⁻¹ • p`, `s = 1`
collapsing to `∞`) is applied with the homotopy parameter `t · η x`, where

* `A := {p | fibN p ≤ 1} ⊆ TotalSpace` is closed in the Thom space (it is the image of the compact
  set `{fibN ≤ 1}` under the open embedding `OnePoint.some`), so `K := f ⁻¹' A` is a closed subset of
  the compact cube which is disjoint from `∂I^j` (whose image lies in `far 1`); the Urysohn lemma
  gives `η : I^j → [0,1]` with `η = 1` on `K` and `η = 0` on `∂I^j`;
* the factor `η` makes the homotopy relative to `∂I^j` (as `pushF 0 = id`) and makes the endpoint
  land in `far 1`: for `x ∈ K` the coefficient is `1` and `pushF 1 = ∞`; for `x ∉ K` with `η x < 1`
  the fibre norm is multiplied by `(1-η x)⁻¹ ≥ 1` while `fibN (f x) > 1`.

The only input from the existing library is the continuity of the composed push
(`Torsion.continuousAt_pushF_some`, available exactly under the hypothesis `fibN p ≠ 0` — this is
where the avoidance of the zero section is used — and `Torsion.continuousAt_pushF_infty`).

## Main declarations

* `continuous_pushF_comp` — continuity of `x ↦ pushF (θ x) (h x)` for `h` avoiding the zero section;
* `fibNLeOne`, `isClosed_fibNLeOne` — the closed set `{fibN ≤ 1}` in the Thom space;
* `escape_to_far` — the escape statement.
-/

open scoped Topology unitInterval
open Work.TangentClasses

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## Continuity of the composed radial push -/

/-- **The composed radial push is continuous** as long as the map `h` avoids the zero section: at a
point `x₀` with `h x₀ = some p` we use `Torsion.continuousAt_pushF_some` (available exactly because
`fibN p ≠ 0`), and at `x₀` with `h x₀ = ∞` we use `Torsion.continuousAt_pushF_infty`. -/
theorem continuous_pushF_comp {X : Type*} [TopologicalSpace X] (h : C(X, Torsion.TP k m))
    (hav : ∀ x p, h x = OnePoint.some p → Torsion.fibN k m p ≠ 0) (θ : C(X, unitInterval)) :
    Continuous fun x => Torsion.pushF k m (θ x) (h x) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hpair : ContinuousAt (fun x => (h x, θ x)) x₀ :=
    (h.continuous.prodMk θ.continuous).continuousAt
  rcases hy : h x₀ with _ | p
  · have hval : h x₀ = OnePoint.infty := hy
    have hbase : ContinuousAt
        (fun r : Torsion.TP k m × unitInterval => Torsion.pushF k m r.2 r.1)
        (h x₀, θ x₀) := by
      rw [hval]
      exact Torsion.continuousAt_pushF_infty k m (θ x₀)
    exact ContinuousAt.comp (f := fun x => (h x, θ x))
      (g := fun r : Torsion.TP k m × unitInterval => Torsion.pushF k m r.2 r.1) hbase hpair
  · have hval : h x₀ = OnePoint.some p := hy
    have hbase : ContinuousAt
        (fun r : Torsion.TP k m × unitInterval => Torsion.pushF k m r.2 r.1)
        (h x₀, θ x₀) := by
      rw [hval]
      exact Torsion.continuousAt_pushF_some k m p (hav x₀ p hval) (θ x₀)
    exact ContinuousAt.comp (f := fun x => (h x, θ x))
      (g := fun r : Torsion.TP k m × unitInterval => Torsion.pushF k m r.2 r.1) hbase hpair

/-! ## The closed set `{fibN ≤ 1}` inside the Thom space -/

/-- The set of points of the total space with `fibN ≤ 1`, as a subset of the Thom space. -/
def fibNLeOne (k m : ℕ) : Set (Torsion.TP k m) :=
  OnePoint.some '' {p : Torsion.TM k m | Torsion.fibN k m p ≤ 1}

/-- **The set `{fibN ≤ 1}` is closed** in the Thom space: it is the image of the compact set
`{fibN ≤ 1}` under the open embedding `OnePoint.some`. -/
theorem isClosed_fibNLeOne (k m : ℕ) : IsClosed (fibNLeOne k m) :=
  OnePoint.isClosed_image_coe.mpr
    ⟨isClosed_le (Torsion.fibN_continuous k m) continuous_const, Torsion.isCompact_fibN_le k m 1⟩

/-- The point at infinity is not in `fibNLeOne`. -/
theorem infty_notMem_fibNLeOne (k m : ℕ) : (OnePoint.infty : Torsion.TP k m) ∉ fibNLeOne k m := by
  rintro ⟨q, -, hq⟩
  exact Option.some_ne_none q hq

/-- A point of the total space with `fibN ≤ 1` lies in `fibNLeOne`. -/
theorem some_mem_fibNLeOne {k m : ℕ} {p : Torsion.TM k m} (hp : Torsion.fibN k m p ≤ 1) :
    (OnePoint.some p : Torsion.TP k m) ∈ fibNLeOne k m :=
  ⟨p, hp, rfl⟩

/-- A point of the total space whose image lies in `fibNLeOne` has `fibN ≤ 1`. -/
theorem fibN_le_one_of_mem_fibNLeOne {k m : ℕ} {p : Torsion.TM k m}
    (hp : (OnePoint.some p : Torsion.TP k m) ∈ fibNLeOne k m) :
    Torsion.fibN k m p ≤ 1 := by
  obtain ⟨q, hq, hqp⟩ := hp
  rwa [Option.some.inj hqp] at hq

/-! ## The escape homotopy -/

/-- **The escape to the far region.**  A map `f : I^j → Th γ` whose image avoids the zero section
and whose boundary values lie in `far 1` is homotopic, relative to the boundary, into `far 1`. -/
theorem escape_to_far (k m : ℕ) {j : ℕ} (f : C(Work.ThomBordism.TwoSet.IC j, Torsion.TP k m))
    (hav : ∀ x p, f x = OnePoint.some p → Torsion.fibN k m p ≠ 0)
    (hbd : ∀ x, x ∈ Cube.boundary (Fin j) → f x ∈ Torsion.far k m 1) :
    ∃ G : C(Work.ThomBordism.TwoSet.IC j × I, Torsion.TP k m),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x, x ∈ Cube.boundary (Fin j) → ∀ t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ Torsion.far k m 1) := by
  classical
  -- the closed set where the fibre norm is at most one
  have hKclosed : IsClosed (f ⁻¹' fibNLeOne k m) := (isClosed_fibNLeOne k m).preimage f.continuous
  have hbdclosed : IsClosed (Cube.boundary (Fin j) : Set (Work.ThomBordism.TwoSet.IC j)) :=
    Work.ThomBordism.TwoSet.isClosed_cubeBoundary j
  have hdisj : Disjoint (Cube.boundary (Fin j) : Set (Work.ThomBordism.TwoSet.IC j))
      (f ⁻¹' fibNLeOne k m) := by
    rw [Set.disjoint_left]
    intro x hx hxK
    rw [Set.mem_preimage] at hxK
    rcases hfx : f x with _ | p
    · have hval : f x = OnePoint.infty := hfx
      exact (infty_notMem_fibNLeOne k m) (hval ▸ hxK)
    · rw [hfx] at hxK
      have hp1 : Torsion.fibN k m p ≤ 1 := fibN_le_one_of_mem_fibNLeOne hxK
      have hp2 : 1 < Torsion.fibN k m p := by
        have h' := hbd x hx
        rw [hfx] at h'
        exact (Torsion.some_mem_far_iff k m 1 p).mp h'
      linarith
  obtain ⟨η, hη0, hη1, hηrange⟩ :=
    exists_continuous_zero_one_of_isClosed hbdclosed hKclosed hdisj
  have hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1 := fun x => Set.mem_Icc.mp (hηrange x)
  -- the escape homotopy parameter
  set θ : C(Work.ThomBordism.TwoSet.IC j × I, unitInterval) :=
    ⟨fun p => ⟨(p.2 : ℝ) * (η p.1 : ℝ), mul_nonneg p.2.2.1 (hηrange p.1).1,
      by have h1 := (hη01 p.1).2; have h2 := p.2.2.2
         nlinarith [h1, h2, (hη01 p.1).1, p.2.2.1]⟩,
      Continuous.subtype_mk (((continuous_subtype_val.comp continuous_snd) :
          Continuous fun p : Work.ThomBordism.TwoSet.IC j × I => (p.2 : ℝ)).mul
        (η.continuous.comp (continuous_fst : Continuous fun p :
          Work.ThomBordism.TwoSet.IC j × I => p.1))) _⟩ with hθdef
  have hcomp : Continuous fun p : Work.ThomBordism.TwoSet.IC j × I =>
      Torsion.pushF k m (θ p) (f p.1) :=
    continuous_pushF_comp (X := Work.ThomBordism.TwoSet.IC j × I)
      (f.comp ⟨fun p : Work.ThomBordism.TwoSet.IC j × I => p.1, continuous_fst⟩)
      (fun p q hp => hav p.1 q (by simpa using hp)) θ
  refine ⟨⟨fun p => Torsion.pushF k m (θ p) (f p.1), hcomp⟩, ?_, ?_, ?_⟩
  · intro x
    have h0 : θ (x, 0) = 0 := by
      apply Subtype.ext
      simp [hθdef]
    change Torsion.pushF k m (θ (x, 0)) (f x) = f x
    rw [h0]
    exact Torsion.pushF_zero k m (f x)
  · intro x hx t
    have hηx : η x = 0 := hη0 hx
    have h0 : θ (x, t) = 0 := by
      apply Subtype.ext
      simp [hθdef, hηx]
    change Torsion.pushF k m (θ (x, t)) (f x) = f x
    rw [h0]
    exact Torsion.pushF_zero k m (f x)
  · intro x
    have hval : θ (x, 1) = ⟨η x, hη01 x⟩ := by
      apply Subtype.ext
      simp [hθdef]
    change Torsion.pushF k m (θ (x, 1)) (f x) ∈ Torsion.far k m 1
    rw [hval]
    rcases hfx : f x with _ | p
    · change Torsion.pushF k m ⟨η x, hη01 x⟩ (OnePoint.infty) ∈ Torsion.far k m 1
      rw [Torsion.pushF_infty]
      exact Torsion.infty_mem_far k m 1
    · by_cases h1 : (η x : ℝ) = 1
      · change Torsion.pushF k m ⟨η x, hη01 x⟩ (OnePoint.some p) ∈ Torsion.far k m 1
        rw [Torsion.pushF_some, if_pos h1]
        exact Torsion.infty_mem_far k m 1
      · have hxK : x ∉ f ⁻¹' fibNLeOne k m := by
          intro hxK
          exact h1 (by rw [hη1 hxK]; rfl)
        have hgt : 1 < Torsion.fibN k m p := by
          by_contra hle
          refine hxK ?_
          rw [Set.mem_preimage, hfx]
          exact some_mem_fibNLeOne (le_of_not_gt hle)
        have hlt : (η x : ℝ) < 1 := lt_of_le_of_ne (hη01 x).2 h1
        have hpos : 0 < 1 - (η x : ℝ) := by linarith
        have hle1 : 1 ≤ (1 - (η x : ℝ))⁻¹ := by
          rw [one_le_inv₀ hpos]
          linarith [(hη01 x).1]
        change Torsion.pushF k m ⟨η x, hη01 x⟩ (OnePoint.some p) ∈ Torsion.far k m 1
        rw [Torsion.pushF_some, if_neg h1]
        exact (Torsion.some_mem_far_iff k m 1 _).mpr (by
          rw [Torsion.fibN_smul k m (le_trans zero_le_one hle1) p]
          have h2 : Torsion.fibN k m p ≤ (1 - (η x : ℝ))⁻¹ * Torsion.fibN k m p :=
            le_mul_of_one_le_left (Torsion.fibN_nonneg k m p) hle1
          linarith)

end

end Work.ThomBordism.Grassmann
