import Mathlib
import Submission.Work.RatHurewicz.GluingPinch.PinchAll
import Submission.Work.RatHurewicz.cubePinchDefs
import Submission.Work.RatHurewicz.PsiKillsAux
import Submission.Work.RatHurewicz.GluingPinch.CoordGen
import Submission.Work.RatHurewicz.GluingPinch.ReadSign
import Submission.Work.RatHurewicz.GluingPinch.CutGen
import Submission.Work.RatHurewicz.GluingPinch.cl_grid
import Submission.Work.Stems.Hur2b.assembly_homotopic_const
import Submission.Work.RatHurewicz.collapseClassOne
import Submission.Work.RatHurewicz.Walk.starContract
import Submission.Work.Stems.HomAdd.PrismFaces
import Submission.Work.Stems.HomAdd.cl_rhoPos
import Submission.Work.Stems.HomAdd.cl_rhoNeg
import Submission.Work.RatHurewicz.GluingPinch.prismKill
import Submission.Work.RatHurewicz.Walk.pinchAllViaNet

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The pinched-cube homotopy addition for all `k` (Hutchings `(2.2b)`)

Target: `Work.RatHurewicz.PinchAll` — for a `(k+1)`-cube `g` which is `y` on its `(k-1)`-skeleton,
the signed product of the classes of its `2(k+1)` faces is `1`.

This file first establishes the two *support lemmas* that the pinch consumes:

* `collapseCubeTrivial`: Hutchings `2.2(a)` in the form the pinch uses — a based cube which is the
  composite `f ∘ φ` of a map `f` on a space contracted to a point `v` (with `f v = x₀`) with a cube
  map `φ` collapsing `∂Iⁿ` to `v` has trivial class.
* `readingFinset` / `readingCoordwise`: the *sign of a coordinatewise reading* — composing a based
  cube with a coordinatewise map whose coordinates fix or swap the endpoints multiplies the class by
  the product of the signs.  This is the whole sign content of the arrangement computation (no
  degree theory is used: the two inputs are `cl_coordUpd` and `cl_coordUpd_swap`).
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz.GluingPinch

noncomputable section

/-! ## Support 1: a cube factoring through a collapsed model is trivial -/

theorem collapseCubeTrivial {Z X : Type} [TopologicalSpace Z] [TopologicalSpace X] (n : ℕ)
    [NeZero n] (v : Z) (x₀ : X) (f : C(Z, X)) (hfv : f v = x₀)
    (C : C(Z × unitInterval, Z)) (hC0 : ∀ z, C (z, 0) = z) (hC1 : ∀ z, C (z, 1) = v)
    (hCv : ∀ t, C (v, t) = v)
    (φ : C(IC n, Z)) (hφ : ∀ u : IC n, u ∈ Cube.boundary (Fin n) → φ u = v) :
    Work.RatHurewicz.cl n X x₀
      ⟨f.comp φ, fun u hu => by rw [ContinuousMap.comp_apply, hφ u hu, hfv]⟩ = 1 := by
  have hHom : GenLoop.Homotopic
      (⟨f.comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, hφ u hu, hfv]⟩ : GenLoop (Fin n) X x₀) GenLoop.const := by
    refine Work.Stems.Hur2b.homotopic_const_of_boundary_const n (X := X) (x₀ := x₀)
      ⟨f.comp φ, fun u hu => by rw [ContinuousMap.comp_apply, hφ u hu, hfv]⟩ x₀
      ⟨fun w => f (C (φ w.1, w.2)), by fun_prop⟩ ?_ ?_ ?_
    · intro y
      show f (C (φ y, 0)) = f (φ y)
      rw [hC0]
    · intro y
      show f (C (φ y, 1)) = x₀
      rw [hC1, hfv]
    · intro y y' t hy hy'
      show f (C (φ y, t)) = f (C (φ y', t))
      rw [hφ y hy, hφ y' hy']
  have h1 : (Quotient.mk _ (show GenLoop (Fin n) X x₀ from
      ⟨f.comp φ, fun u hu => by rw [ContinuousMap.comp_apply, hφ u hu, hfv]⟩)
      : HomotopyGroup (Fin n) X x₀) = ⟦GenLoop.const⟧ := Quotient.sound hHom
  exact h1.trans HomotopyGroup.one_def

/-- **Hutchings `2.2(a)`, set-valued form.**  If the contraction of `Z` keeps a set `S` inside the
fibre of `x₀` (`f (C (z,t)) = x₀` for `z ∈ S`), and the cube map `φ` sends `∂Iⁿ` into `S`, then the
based cube `f ∘ φ` has trivial class.  This is the form the pinch uses: `∂Iⁿ` need not be collapsed
to a single point, only into a set that the contraction drives into the base point. -/
theorem collapseCubeTrivialSet {Z X : Type} [TopologicalSpace Z] [TopologicalSpace X] (n : ℕ)
    [NeZero n] (v : Z) (x₀ : X) (f : C(Z, X)) (hfv : f v = x₀)
    (C : C(Z × unitInterval, Z)) (hC0 : ∀ z, C (z, 0) = z) (hC1 : ∀ z, C (z, 1) = v)
    (S : Set Z) (hS : ∀ z ∈ S, ∀ t : unitInterval, f (C (z, t)) = x₀)
    (φ : C(IC n, Z)) (hφ : ∀ u : IC n, u ∈ Cube.boundary (Fin n) → φ u ∈ S) :
    Work.RatHurewicz.cl n X x₀
      ⟨f.comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, ← hC0 (φ u)]
        exact hS (φ u) (hφ u hu) 0⟩ = 1 := by
  have hHom : GenLoop.Homotopic
      (⟨f.comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, ← hC0 (φ u)]
        exact hS (φ u) (hφ u hu) 0⟩ : GenLoop (Fin n) X x₀) GenLoop.const := by
    refine Work.Stems.Hur2b.homotopic_const_of_boundary_const n (X := X) (x₀ := x₀)
      ⟨f.comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, ← hC0 (φ u)]
        exact hS (φ u) (hφ u hu) 0⟩ x₀
      ⟨fun w => f (C (φ w.1, w.2)), by fun_prop⟩ ?_ ?_ ?_
    · intro y
      show f (C (φ y, 0)) = f (φ y)
      rw [hC0 (φ y)]
    · intro y
      show f (C (φ y, 1)) = x₀
      rw [hC1 (φ y), hfv]
    · intro y y' t hy hy'
      show f (C (φ y, t)) = f (C (φ y', t))
      rw [hS (φ y) (hφ y hy) t, hS (φ y') (hφ y' hy') t]
  have h1 : (Quotient.mk _ (show GenLoop (Fin n) X x₀ from
      ⟨f.comp φ, fun u hu => by
        rw [ContinuousMap.comp_apply, ← hC0 (φ u)]
        exact hS (φ u) (hφ u hu) 0⟩) : HomotopyGroup (Fin n) X x₀) = ⟦GenLoop.const⟧ :=
    Quotient.sound hHom
  exact h1.trans HomotopyGroup.one_def

theorem unitInterval_one_ne_zero : (1 : unitInterval) ≠ 0 := fun h => by
  have := congrArg (fun x : unitInterval => (x : ℝ)) h
  norm_num at this

/-! ## Support 2: the sign of a coordinatewise reading -/

/-- The coordinatewise self-map `u ↦ (fun j => if j ∈ S then ψ j (u j) else u j)` of `I^n`. -/
def cwise {n : ℕ} (S : Finset (Fin n)) (ψ : Fin n → C(unitInterval, unitInterval)) :
    C(IC n, IC n) :=
  ⟨fun u j => if j ∈ S then ψ j (u j) else u j, by
    apply continuous_pi
    intro j
    by_cases hj : j ∈ S
    · simp only [hj, if_pos]
      exact (ψ j).continuous.comp (continuous_apply j)
    · simp only [hj, if_false]
      exact continuous_apply j⟩

@[simp] theorem cwise_apply {n : ℕ} (S : Finset (Fin n))
    (ψ : Fin n → C(unitInterval, unitInterval)) (u : IC n) :
    cwise S ψ u = fun j => if j ∈ S then ψ j (u j) else u j := rfl

/-- The coordinatewise map of `insert i S` factors through the neighbour of `S`. -/
theorem cwise_insert {n : ℕ} (i : Fin n) (S : Finset (Fin n))
    (ψ : Fin n → C(unitInterval, unitInterval)) (hi : i ∉ S) :
    cwise (insert i S) ψ = (cwise S ψ).comp (Work.RatHurewicz.coordUpd n i (ψ i)) := by
  apply ContinuousMap.ext
  intro u
  funext j
  rw [ContinuousMap.comp_apply, Work.RatHurewicz.coordUpd_apply]
  simp only [cwise_apply]
  by_cases hj : j ∈ S
  · have hji : j ≠ i := fun h => hi (h ▸ hj)
    rw [if_pos (Finset.mem_insert_of_mem hj), if_pos hj, Function.update_apply, if_neg hji]
  · by_cases hji : j = i
    · rw [hji, if_pos (Finset.mem_insert_self i S), if_neg hi, Function.update_apply,
        if_pos rfl]
    · rw [if_neg (fun hmem => by
          rcases Finset.mem_insert.mp hmem with h | h
          · exact hji h
          · exact hj h), if_neg hj, Function.update_apply, if_neg hji]

/-- The coordinatewise map sends the boundary to the boundary. -/
theorem cwise_mem_boundary {n : ℕ} {S : Finset (Fin n)}
    {ψ : Fin n → C(unitInterval, unitInterval)}
    (hfix : ∀ i ∈ S, (ψ i 0 = 0 ∧ ψ i 1 = 1) ∨ (ψ i 0 = 1 ∧ ψ i 1 = 0))
    {u : IC n} (hu : u ∈ Cube.boundary (Fin n)) :
    cwise S ψ u ∈ Cube.boundary (Fin n) := by
  obtain ⟨m, hm | hm⟩ := hu
  · refine ⟨m, ?_⟩
    simp only [cwise_apply]
    by_cases hmS : m ∈ S
    · rw [if_pos hmS]
      rcases hfix m hmS with ⟨h0, _⟩ | ⟨h0, _⟩
      · left; rw [hm, h0]
      · right; rw [hm, h0]
    · left; rw [if_neg hmS]; exact hm
  · refine ⟨m, ?_⟩
    simp only [cwise_apply]
    by_cases hmS : m ∈ S
    · rw [if_pos hmS]
      rcases hfix m hmS with ⟨_, h1⟩ | ⟨_, h1⟩
      · right; rw [hm, h1]
      · left; rw [hm, h1]
    · right; rw [if_neg hmS]; exact hm

/-- **The sign of a coordinatewise reading** (Finset form). -/
theorem readingFinset {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (S : Finset (Fin n)) (ψ : Fin n → C(unitInterval, unitInterval))
    (hfix : ∀ i ∈ S, (ψ i 0 = 0 ∧ ψ i 1 = 1) ∨ (ψ i 0 = 1 ∧ ψ i 1 = 0))
    (p q : GenLoop (Fin n) X x₀)
    (hq : ∀ u : IC n, q.1 u = p.1 (cwise S ψ u)) :
    Work.RatHurewicz.cl n X x₀ q
      = (Work.RatHurewicz.cl n X x₀ p) ^
          (∏ i ∈ S, (if ψ i 0 = 0 then (1 : ℤ) else -1)) := by
  classical
  induction S using Finset.induction_on generalizing p q with
  | empty =>
      have hpq : q = p := by
        apply Subtype.ext
        apply ContinuousMap.ext
        intro u
        rw [hq u]
        congr 1
      rw [hpq]
      simp
  | insert i S' hi ih =>
      let P' : GenLoop (Fin n) X x₀ :=
        ⟨p.1.comp (cwise S' ψ),
          fun u hu => p.2 _ (cwise_mem_boundary
            (S := S') (ψ := ψ)
            (fun j hj => hfix j (Finset.mem_insert_of_mem hj)) hu)⟩
      have hP'val : ∀ u : IC n, P'.1 u = p.1 (cwise S' ψ u) := fun u => rfl
      have hP'cl : Work.RatHurewicz.cl n X x₀ P'
          = (Work.RatHurewicz.cl n X x₀ p) ^
              (∏ i ∈ S', (if ψ i 0 = 0 then (1 : ℤ) else -1)) :=
        ih (fun j hj => hfix j (Finset.mem_insert_of_mem hj)) p P' (fun u => rfl)
      have hqcoord : ∀ u : IC n, q.1 u = P'.1 (Work.RatHurewicz.coordUpd n i (ψ i) u) := by
        intro u
        rw [hq u]
        rw [cwise_insert i S' ψ hi]
        rfl
      rcases hfix i (Finset.mem_insert_self i S') with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · have hqeq : q = ⟨P'.1.comp (Work.RatHurewicz.coordUpd n i (ψ i)),
            fun u hu => P'.2 _ (Work.RatHurewicz.coordUpd_mem_boundary i (ψ i) h0 h1 hu)⟩ :=
          Subtype.ext (ContinuousMap.ext hqcoord)
        have hc := Work.RatHurewicz.cl_coordUpd (n := n) (X := X) (x₀ := x₀) i (ψ i) h0 h1 P'
        rw [← hqeq] at hc
        rw [hc, hP'cl, Finset.prod_insert hi]
        simp [h0]
      · have hqeq : q = ⟨P'.1.comp (Work.RatHurewicz.coordUpd n i (ψ i)),
            fun u hu => P'.2 _ (Work.RatHurewicz.coordUpd_mem_boundary' i (ψ i)
              (Or.inr h0) (Or.inl h1) hu)⟩ :=
          Subtype.ext (ContinuousMap.ext hqcoord)
        have hc := Work.RatHurewicz.cl_coordUpd_swap (n := n) (X := X) (x₀ := x₀) i (ψ i) h0 h1 P'
        rw [← hqeq] at hc
        rw [hc, hP'cl, Finset.prod_insert hi]
        simp [h0, unitInterval_one_ne_zero]

/-- **The sign of a coordinatewise reading** (full form). -/
theorem readingCoordwise {n : ℕ} [NeZero n] {X : Type} [TopologicalSpace X] {x₀ : X}
    (ψ : Fin n → C(unitInterval, unitInterval))
    (hfix : ∀ i : Fin n, (ψ i 0 = 0 ∧ ψ i 1 = 1) ∨ (ψ i 0 = 1 ∧ ψ i 1 = 0))
    (p q : GenLoop (Fin n) X x₀)
    (hq : ∀ u : IC n, q.1 u = p.1 (fun i => ψ i (u i))) :
    Work.RatHurewicz.cl n X x₀ q
      = (Work.RatHurewicz.cl n X x₀ p) ^
          (∏ i : Fin n, (if ψ i 0 = 0 then (1 : ℤ) else -1)) := by
  have h := readingFinset (Finset.univ : Finset (Fin n)) ψ (fun i _ => hfix i) p q
    (fun u => by
      rw [hq u]
      congr 1
      funext j
      simp only [cwise_apply, Finset.mem_univ, if_true])
  simpa using h


/-! ## Support 3: the "star" nullity

If `ψ : I^k → I^{k+1}` maps `∂I^k` into the *star* of a vertex `v` of the cube — i.e. every point of
`ψ(∂I^k)` agrees with `v` in (at least) two coordinates — then `cl (g ∘ ψ) = 1`.  The reason is
`collapseCubeTrivialSet` with `S` the star: the straight-line contraction towards `v` fixes every
coordinate in which a point of the star already agrees with `v`, so it keeps `S` inside the
`(k-1)`-skeleton, where `g` is `x₀`.  (This is the "star mechanism" of the pinch's collar.) -/

/-- The star of `v` inside `I^n`: the points agreeing with `v` in two coordinates. -/
def Star {n : ℕ} (v : IC n) : Set (IC n) :=
  {z | ∃ i j : Fin n, i ≠ j ∧ z i = v i ∧ z j = v j}

theorem segPt_mem_star {n : ℕ} {v z : IC n} (hz : z ∈ Star v) {t : unitInterval} :
    segPt z v t ∈ Star v := by
  obtain ⟨i, j, hij, hi, hj⟩ := hz
  exact ⟨i, j, hij, Work.RatHurewicz.Walk.segPt_coord_eq_right z v t i hi, Work.RatHurewicz.Walk.segPt_coord_eq_right z v t j hj⟩

theorem star_subset_inSkel {k : ℕ} {v z : IC (k + 1)} (hv : ∀ i : Fin (k + 1), v i = 0 ∨ v i = 1)
    (hz : z ∈ Star v) : InSkel k z := by
  obtain ⟨i, j, hij, hi, hj⟩ := hz
  exact ⟨i, j, hij, by rw [hi]; exact hv i, by rw [hj]; exact hv j⟩

/-- **The star nullity.**  A based cube of the form `g ∘ ψ` whose boundary is read inside the star
of a vertex of the cube has trivial class. -/
theorem cl_comp_eq_one_of_star {k : ℕ} [NeZero k] {X : Type} [TopologicalSpace X] {x₀ : X}
    (g : C(IC (k + 1), X)) (hg : ∀ z : IC (k + 1), InSkel k z → g z = x₀)
    (ψ : C(IC k, IC (k + 1))) (v : IC (k + 1))
    (hv : ∀ i : Fin (k + 1), v i = 0 ∨ v i = 1)
    (hψ : ∀ u : IC k, u ∈ Cube.boundary (Fin k) → ψ u ∈ Star v) :
    Work.RatHurewicz.cl k X x₀
      ⟨g.comp ψ, fun u hu => hg (ψ u) (star_subset_inSkel hv (hψ u hu))⟩ = 1 := by
  have hvskel : InSkel k v := by
    haveI hnt : Nontrivial (Fin (k + 1)) :=
      ⟨⟨⟨0, Nat.succ_pos k⟩, ⟨1, Nat.succ_lt_succ (Nat.pos_of_ne_zero (NeZero.ne k))⟩,
        by simp⟩⟩
    obtain ⟨i, j, hij⟩ := exists_pair_ne (Fin (k + 1))
    exact ⟨i, j, hij, hv i, hv j⟩
  refine collapseCubeTrivialSet k v x₀ g (hg v hvskel)
    ⟨fun p : IC (k + 1) × unitInterval => segPt p.1 v p.2, ?_⟩
    (fun z => segPt_zero z v) (fun z => segPt_one z v) (Star v) ?_ ψ ?_
  · refine continuous_pi fun i => ?_
    apply Continuous.subtype_mk
    fun_prop
  · intro z hz t
    exact hg _ (star_subset_inSkel hv (segPt_mem_star hz))
  · intro u hu
    exact hψ u hu

/-! ## The target

**Proven.**  The statement is `Work.RatHurewicz.PinchAll`.  The team's *prism* proof of it is
`Work.RatHurewicz.Walk.pinchAllViaNet` (`Submission/Work/RatHurewicz/Walk/pinchAllViaNet.lean`,
completed and axiom-clean (axioms `propext, Classical.choice, Quot.sound`)): kill the `2k` side faces of the cube
one after another with the prism maps, keeping the invariant
`Qs · [top] · [bottom]⁻¹` (which is `1` for a cube all of whose side faces are constant, since then
the cube is a based homotopy between its top and bottom faces), and finish with the group algebra.

The *same* argument, with the side conditions of the killing step developed here in detail, is
carried out independently in this area by the files

* `GluingPinch/prismKill.lean` — the explicit coordinate maps `killCMPos`/`killCMNeg` realising the
  gluing, their two halves, the skeleton-preservation, the killed hyperplane and the preservation of
  the earlier kills;
* `GluingPinch/prismFace.lean` — the faces of the killed cubes (`faceOf`, `fcl`), including the
  killed face (constant), its opposite (unchanged) and the top face (gaining a factor);
* `GluingPinch/killPos_face_class.lean` — the side faces of `killPos k i g` keep their class.

Those files are not needed for the statement below, which we take from the team's completed
development. -/

/-- **The general cubical homotopy-addition statement** (Hutchings `(2.2b)`, all `k`): a cube
`g : I^{k+1} → Y` that is `y` on its `(k-1)`-skeleton has face classes whose signed product is `1`.
The signs `(-1)^i`, `-(-1)^i` are those of the cubical boundary operator. -/
theorem pinchAll : Work.RatHurewicz.PinchAll := Work.RatHurewicz.Walk.pinchAllViaNet

end

end Work.RatHurewicz.GluingPinch
