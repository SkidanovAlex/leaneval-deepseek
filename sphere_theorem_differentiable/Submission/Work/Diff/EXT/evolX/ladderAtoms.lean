import Mathlib
import Submission.Work.Diff.EXT.evolX.lapCommAuxDefs
import Submission.Work.Diff.EXT.lapComm_curvActT_deriv
import Submission.Work.Diff.EXT.reactBase
import Submission.Work.Diff.GE.kato_geodesic_frame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The "atoms" of the level ladder for the adjacent-swap bound of the curvature tower

`Work.Diff.EXT.evolX.ckt_adjacent_swap_bound` bounds the difference
`ckt g d G x - ckt g d (tupSwap d p hp G) x` of the level-`d` tower under the exchange of two adjacent
*derivative* slots by `C · Shape g x (d-2) · ∏ ‖G r x‖`.

The exchange of two adjacent differentiation slots of `∇^dRm` is a *curvature action* at level
`d-2` (`Work.Diff.EXT.ckt_ricci`), and applying the `p` outer derivatives distributes the
derivative count over the two curvature factors (Leibniz), so the difference is a sum of
*contractions of two curvature jets whose levels add to `d-2`*.

The present module sets up the bookkeeping for that statement.  The objects are

* `Zf g W l Ψ` — the **level-`l` curvature vector** with the `l+3` argument fields `Ψ`, expanded in
  the frame field `W`: the vector whose pairing with `D` is the tower `ckt g l (snoc Ψ D)`.  For
  `l = 0` this is (up to sign) `curv (Ψ 0) (Ψ 1) (Ψ 2)`, the curvature vector;
* `Atom g W m l s κ ξ F` — an **atom of level `m + l`**: the level-`m` tower evaluated on the tuple
  whose slot `s` carries the level-`l` curvature vector `Zf g W l (F ∘ ξ)` and whose other slots
  carry the tuple entries `F (κ i)`.  The index maps `κ`, `ξ` (`GoodData`) are a partition of the
  tuple positions, so an atom of level `L` is an operator of arity `L + 6` in which every entry of
  the tuple occurs exactly once.

The two structural facts (proved in the companion modules) are

* `extStep g (Atom … m l …) F x = Atom … (m+1) l … F x + Atom … m (l+1) … F x`: the covariant
  derivative of an atom is the sum of the two atoms obtained by attributing the new differentiation
  direction to one of the two factors — this is the Leibniz rule of the ladder (the corrections of
  `Work.Diff.EXT.mvfderiv_ckt_T2` cancel against the corrections of `extStep`, by the partition
  property of `κ`/`ξ`);
* `|Atom … m l … F x| ≤ C (finrank ℝ E) · Shape g x (m+l) · ∏ ‖F r x‖`: the level bound.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.evolX

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-! ## Notation-free wrappers (so that delegated statements elaborate without `open`s) -/

/-- A smooth tangent field.  (Wrapper around `Work.Diff.GE.SmoothFieldT`.) -/
abbrev SmTf (X : Work.Diff.EXT.TField (I := I) (M := M)) : Prop :=
  Work.Diff.GE.SmoothFieldT (I := I) (M := M) X

/-- The frame family `W` is `g`-orthonormal near `x`. -/
abbrev ONFrameAt (g : SMet I M) (x : M)
    (W : Fin (Module.finrank ℝ E) → Work.Diff.EXT.TField (I := I) (M := M)) : Prop :=
  Filter.Eventually (fun y : M => Submission.Diff.IsONFrame g y (fun i => W i y)) (nhds x)

/-! ## The level-`l` curvature vector -/

/-- **The level-`l` curvature vector** with the `l + 3` argument fields `Ψ`, expanded in the frame
field `W`: the field `∑ i, (ckt g l (snoc Ψ (W i))) • W i`, characterised (for `W` orthonormal near
the base point) by the pairing identity `g.inner (Zf g W l Ψ) D = ckt g l (snoc Ψ D)`. -/
noncomputable def Zf (g : SMet I M) (W : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (l : ℕ) (Ψ : Fin (l + 3) → TField (I := I) (M := M)) : TField (I := I) (M := M) :=
  fun y => ∑ i, (Work.Diff.EXT.ckt g l (Fin.snoc Ψ (W i)) y) • W i y

/-- **The admissibility of the index maps of an atom.**  `κ` selects, for the tower slots other than
`s`, the tuple entry that fills them; `ξ` selects, for the `l + 3` arguments of the level-`l`
curvature vector, the tuple entry that fills them.  The conditions say that the two families are
injective, mutually disjoint, and cover every tuple position: the tuple is partitioned between the
tower slots and the arguments of the curvature vector. -/
def GoodDataN (m l N : ℕ) (s : Fin (m + 4))
    (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N) : Prop :=
  (∀ i j, i ≠ s → j ≠ s → κ i = κ j → i = j)
    ∧ Function.Injective ξ
    ∧ (∀ i r, i ≠ s → κ i ≠ ξ r)
    ∧ (∀ u : Fin N, (∃ i, i ≠ s ∧ κ i = u) ∨ (∃ r, ξ r = u))

/-- **An atom of level `m + l` and arity `N`**: the level-`m` tower evaluated on the tuple whose
slot `s` carries the level-`l` curvature vector `Zf g W l (F ∘ ξ)`, and whose remaining slots carry
the tuple entries `F (κ i)`. -/
noncomputable def Atom (g : SMet I M) (W : Fin (Module.finrank ℝ E) → TField (I := I) (M := M))
    (m l N : ℕ) (s : Fin (m + 4))
    (κ : Fin (m + 4) → Fin N) (ξ : Fin (l + 3) → Fin N)
    (F : Fin N → TField (I := I) (M := M)) : M → ℝ :=
  fun y => Work.Diff.EXT.ckt g m
    (fun i => if i = s then Zf (I := I) (M := M) g W l (fun r => F (ξ r)) else F (κ i)) y

/-! ## The partition lemmas for the index maps

Under `GoodDataN` the tuple positions split into the tower slots and the arguments of the curvature
vector, so sums and products over `Fin N` split accordingly. -/

/-! ## The index maps of the base atoms (the curvature action `curvActT`) -/

/-- The `κ`-map of the `s`-th base atom: the tower slot `i ≠ s` carries the tuple entry `i + 2`
(the remaining slots of `H ∘ succ ∘ succ`); the value at `i = s` is immaterial. -/
noncomputable def baseK (j : ℕ) (s : Fin (j + 4)) : Fin (j + 4) → Fin (j + 6) :=
  fun i => if i = s then 0 else ⟨i.val + 2, by have := i.isLt; omega⟩

/-- The `ξ`-map of the `s`-th base atom: the three arguments of the curvature vector are the tuple
entries `0`, `1` and `s + 2`. -/
noncomputable def baseXi (j : ℕ) (s : Fin (j + 4)) : Fin 3 → Fin (j + 6) :=
  ![0, 1, ⟨s.val + 2, by have := s.isLt; omega⟩]

/-- **Splitting a sum over the tuple positions.** -/
theorem sum_split_of_goodDataN {m l N : ℕ} {s : Fin (m + 4)}
    {κ : Fin (m + 4) → Fin N} {ξ : Fin (l + 3) → Fin N}
    (h : GoodDataN m l N s κ ξ) (f : Fin N → ℝ) :
    (∑ u : Fin N, f u)
      = (∑ i ∈ (Finset.univ.erase s : Finset (Fin (m + 4))), f (κ i))
        + ∑ r : Fin (l + 3), f (ξ r) := by
  classical
  obtain ⟨hκ, hξ, hdisj, hcov⟩ := h
  set K : Finset (Fin N) := (Finset.univ.erase s).image κ with hK
  set X : Finset (Fin N) := Finset.univ.image ξ with hX
  have hinj : ∀ x ∈ (Finset.univ.erase s : Finset (Fin (m + 4))),
      ∀ y ∈ (Finset.univ.erase s : Finset (Fin (m + 4))), κ x = κ y → x = y := by
    intro x hx y hy hxy
    exact hκ x y (Finset.mem_erase.mp hx).1 (Finset.mem_erase.mp hy).1 hxy
  have hKval : (∑ u ∈ K, f u) = ∑ i ∈ (Finset.univ.erase s : Finset (Fin (m + 4))), f (κ i) := by
    rw [hK]
    exact Finset.sum_image hinj
  have hXval : (∑ u ∈ X, f u) = ∑ r : Fin (l + 3), f (ξ r) := by
    rw [hX]
    exact Finset.sum_image (fun x _ y _ hxy => hξ hxy)
  have hKX : Disjoint K X := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [hK, Finset.mem_image] at hu
    obtain ⟨i, hi, hiu⟩ := hu
    rw [hX, Finset.mem_image] at hu'
    obtain ⟨r, -, hr⟩ := hu'
    exact hdisj i r (Finset.mem_erase.mp hi).1 (by rw [hiu, hr])
  have hcov' : K ∪ X = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro u
    rcases hcov u with ⟨i, hi, hiu⟩ | ⟨r, hr⟩
    · exact Finset.mem_union_left _
        (by rw [hK, Finset.mem_image]
            exact ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hiu⟩)
    · exact Finset.mem_union_right _
        (by rw [hX, Finset.mem_image]; exact ⟨r, Finset.mem_univ _, hr⟩)
  rw [← hcov', Finset.sum_union hKX, hKval, hXval]

/-- **Splitting a product over the tuple positions.** -/
theorem prod_split_of_goodDataN {m l N : ℕ} {s : Fin (m + 4)}
    {κ : Fin (m + 4) → Fin N} {ξ : Fin (l + 3) → Fin N}
    (h : GoodDataN m l N s κ ξ) (f : Fin N → ℝ) :
    (∏ u : Fin N, f u)
      = (∏ i ∈ (Finset.univ.erase s : Finset (Fin (m + 4))), f (κ i))
        * ∏ r : Fin (l + 3), f (ξ r) := by
  classical
  obtain ⟨hκ, hξ, hdisj, hcov⟩ := h
  set K : Finset (Fin N) := (Finset.univ.erase s).image κ with hK
  set X : Finset (Fin N) := Finset.univ.image ξ with hX
  have hinj : ∀ x ∈ (Finset.univ.erase s : Finset (Fin (m + 4))),
      ∀ y ∈ (Finset.univ.erase s : Finset (Fin (m + 4))), κ x = κ y → x = y := by
    intro x hx y hy hxy
    exact hκ x y (Finset.mem_erase.mp hx).1 (Finset.mem_erase.mp hy).1 hxy
  have hKval : (∏ u ∈ K, f u)
      = ∏ i ∈ (Finset.univ.erase s : Finset (Fin (m + 4))), f (κ i) := by
    rw [hK]
    exact Finset.prod_image hinj
  have hXval : (∏ u ∈ X, f u) = ∏ r : Fin (l + 3), f (ξ r) := by
    rw [hX]
    exact Finset.prod_image (fun x _ y _ hxy => hξ hxy)
  have hKX : Disjoint K X := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    rw [hK, Finset.mem_image] at hu
    obtain ⟨i, hi, hiu⟩ := hu
    rw [hX, Finset.mem_image] at hu'
    obtain ⟨r, -, hr⟩ := hu'
    exact hdisj i r (Finset.mem_erase.mp hi).1 (by rw [hiu, hr])
  have hcov' : K ∪ X = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro u
    rcases hcov u with ⟨i, hi, hiu⟩ | ⟨r, hr⟩
    · exact Finset.mem_union_left _
        (by rw [hK, Finset.mem_image]
            exact ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hiu⟩)
    · exact Finset.mem_union_right _
        (by rw [hX, Finset.mem_image]; exact ⟨r, Finset.mem_univ _, hr⟩)
  rw [← hcov', Finset.prod_union hKX, hKval, hXval]

end Work.Diff.EXT.evolX
