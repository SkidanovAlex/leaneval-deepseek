import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE7.reindex_eval

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
## Un-splitting the coordinates in `E6_fiber_closure`

The frozen `E6_fiber_closure` is stated in the *split* form: a semi-Pfaffian set is a set
in `ℝ^{p+q}` with a distinguished first factor of `p` coordinates, and the output is its
*fibrewise* closure `fiberClosure X.set = {(x,y) | y ∈ closure (X_x)}`.

Consumers of the theorem (`E7`, `E7_prop_main`, the cell decomposition) want the same
statement for a set `X : SemiPf k` in `ℝ^k` with no distinguished splitting, expressed
with the ordinary topological closure `closure X.set`.  The two agree, and this file
proves it: take the splitting `p = 0`, `q = k`, and identify `ℝ^{0+k}` with `ℝ^k` by the
value-preserving equivalence `zeroEquiv k : Fin k ≃ Fin (0 + k)`.  Over the single point
of `ℝ^0` the fibrewise closure is just the closure of the (whole) set, so pulling back
along that identification turns `fiberClosure` into `closure`.

Only the *shape* of the semi-Pfaffian presentation has to be transported, and
`Work.WilE7.star_proj` already provides the two facts needed for that
(`sp_reindex_set_pull`: reindexing a `SemiPf` set corresponds to pulling back along the
coordinate homeomorphism `pullHomeo`, and `sp_reindex_deg`: reindexing preserves the
degree).  The format is `k + r` and the chain `r` is untouched by a reindexing, so the
format is preserved as well.
-/

/-! ### The value-preserving identification `Fin k ≃ Fin (0 + k)` -/

/-- The value-preserving identification `Fin k ≃ Fin (0 + k)`. -/
def zeroEquiv (k : ℕ) : Fin k ≃ Fin (0 + k) := finEquiv (Nat.zero_add k).symm

@[simp] theorem zeroEquiv_apply_val (k : ℕ) (i : Fin k) : ((zeroEquiv k) i).val = i.val :=
  rfl

@[simp] theorem zeroEquiv_symm_apply_val (k : ℕ) (j : Fin (0 + k)) :
    ((zeroEquiv k).symm j).val = j.val := rfl

/-- On the last `k` coordinates of `ℝ^{0+k}`, `projSnd 0 k` is the pullback along
`zeroEquiv k`. -/
theorem projSnd_zero_eq (k : ℕ) (y : Fin (0 + k) → ℝ) :
    projSnd 0 k y = fun i => y (zeroEquiv k i) := by
  funext i
  rw [projSnd]
  congr 1
  exact Fin.ext (by simp [Fin.natAdd])

/-- The coordinate map `z ↦ z ∘ (zeroEquiv k).symm` is a section of `projSnd 0 k`. -/
theorem projSnd_zero_symm (k : ℕ) (z : Fin k → ℝ) :
    projSnd 0 k (fun j => z ((zeroEquiv k).symm j)) = z := by
  funext i
  rw [projSnd]
  congr 1
  exact Fin.ext (by simp [Fin.natAdd])

/-- `Fin.append u ·` for `u : Fin 0 → ℝ` is the section of `projSnd 0 k`, written
coordinatewise. -/
theorem append_zero_eq (k : ℕ) (u : Fin 0 → ℝ) (y : Fin k → ℝ) :
    (fun i => Fin.append u y (zeroEquiv k i)) = y := by
  funext i
  have h : zeroEquiv k i = Fin.natAdd 0 i := Fin.ext (by simp [Fin.natAdd])
  rw [h, Fin.append_right]

/-- `projSnd p q` of an appended point is the appended tail. -/
theorem projSnd_append {p q : ℕ} (x : Fin p → ℝ) (y : Fin q → ℝ) :
    projSnd p q (Fin.append x y) = y := by
  funext j
  simp [projSnd, Fin.append_right]

/-! ### Fibrewise closure with an empty first factor -/

/-- Over `ℝ^0` (a single point) the fibre of the `projSnd 0 k`-pullback of `S` is `S`
itself: every point of `ℝ^{0+k}` is an append of the unique point of `ℝ^0` and its own
tail. -/
theorem fiber_projSnd_zero {k : ℕ} (S : Set (Fin k → ℝ)) (u : Fin 0 → ℝ) :
    fiber (p := 0) (q := k) {y : Fin (0 + k) → ℝ | projSnd 0 k y ∈ S} u = S := by
  ext y
  simp only [fiber, Set.mem_ofPred_eq]
  rw [projSnd_append]

/-- With an empty first factor, the fibrewise closure of a `projSnd`-pullback is the
`projSnd`-pullback of the ordinary closure. -/
theorem fiberClosure_zero_fst {k : ℕ} (S : Set (Fin k → ℝ)) :
    fiberClosure (p := 0) (q := k) {y : Fin (0 + k) → ℝ | projSnd 0 k y ∈ S} =
      {z : Fin (0 + k) → ℝ | projSnd 0 k z ∈ closure S} := by
  ext z
  simp only [fiberClosure, Set.mem_ofPred_eq]
  rw [fiber_projSnd_zero S (projFirst 0 k z)]

/-! ### Transporting a `SemiPf` set across the identification -/

/-- The `zeroEquiv k`-reindexed set is the `projSnd 0 k`-pullback of the original one. -/
theorem reindex_zero_set {k : ℕ} (X : SemiPf k) :
    (SemiPf.reindex (zeroEquiv k) X).set =
      {y : Fin (0 + k) → ℝ | projSnd 0 k y ∈ X.set} := by
  rw [sp_reindex_set]
  ext y
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← projSnd_zero_eq]

/-- Pulling the `zeroEquiv k`-reindexed set back along the coordinate homeomorphism
`pullHomeo (zeroEquiv k).symm` recovers the original set. -/
theorem preimage_reindex_zero_set {k : ℕ} (X : SemiPf k) :
    pullHomeo (zeroEquiv k).symm ⁻¹' (SemiPf.reindex (zeroEquiv k) X).set = X.set := by
  rw [reindex_zero_set]
  ext z
  rw [Set.mem_preimage, Set.mem_ofPred_eq, pullHomeo_apply, projSnd_zero_symm]

/-- **The bridge.**  Pulling the fibrewise closure of the `zeroEquiv k`-reindexed set
back along the coordinate homeomorphism gives the ordinary closure. -/
theorem preimage_fiberClosure_zero {k : ℕ} (X : SemiPf k) :
    pullHomeo (zeroEquiv k).symm ⁻¹' (fiberClosure (SemiPf.reindex (zeroEquiv k) X).set) =
      closure X.set := by
  rw [reindex_zero_set, fiberClosure_zero_fst]
  ext z
  rw [Set.mem_preimage, Set.mem_ofPred_eq, pullHomeo_apply, projSnd_zero_symm]

/-! ### The un-split form of `E6` -/

theorem E6closure
    (hE6 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = WilkiesDesign.E.fiberClosure X.set ∧
        Y'.set = WilkiesDesign.E.fiberClosure X.set \ X.set)
    (F : ℕ) : ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ Y Y' : WilkiesDesign.E.SemiPf k, Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
        Y'.deg ≤ b.eval X.deg ∧ Y.set = closure X.set ∧ Y'.set = closure X.set \ X.set := by
  obtain ⟨a, b, hb⟩ := hE6 F
  refine ⟨a, b, fun k X hX => ?_⟩
  let e : Fin k ≃ Fin (0 + k) := zeroEquiv k
  -- The reindexed set has the same format: the chain length is untouched.
  have hXfmt : (SemiPf.reindex e X).fmt ≤ F := by
    have hx : k + X.r ≤ F := hX
    have h' : (0 + k) + X.r ≤ F := by omega
    simpa only [SemiPf.fmt, SemiPf.reindex, e, zeroEquiv] using h'
  obtain ⟨Y, Y', hYf, hYd, hY'f, hY'd, hYs, hY's⟩ := hb 0 k (SemiPf.reindex e X) hXfmt
  refine ⟨SemiPf.reindex e.symm Y, SemiPf.reindex e.symm Y', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- format of `Y`
    have h' : (0 + k) + Y.r ≤ a := hYf
    have h'' : k + Y.r ≤ a := by omega
    simpa only [SemiPf.fmt, SemiPf.reindex, e, zeroEquiv] using h''
  · -- degree of `Y`
    calc (SemiPf.reindex e.symm Y).deg = Y.deg := sp_reindex_deg e.symm Y
      _ ≤ b.eval (SemiPf.reindex e X).deg := hYd
      _ = b.eval X.deg := by rw [sp_reindex_deg e X]
  · -- format of `Y'`
    have h' : (0 + k) + Y'.r ≤ a := hY'f
    have h'' : k + Y'.r ≤ a := by omega
    simpa only [SemiPf.fmt, SemiPf.reindex, e, zeroEquiv] using h''
  · -- degree of `Y'`
    calc (SemiPf.reindex e.symm Y').deg = Y'.deg := sp_reindex_deg e.symm Y'
      _ ≤ b.eval (SemiPf.reindex e X).deg := hY'd
      _ = b.eval X.deg := by rw [sp_reindex_deg e X]
  · -- the closure
    calc (SemiPf.reindex e.symm Y).set
        = pullHomeo e.symm ⁻¹' Y.set := sp_reindex_set_pull e.symm Y
      _ = pullHomeo e.symm ⁻¹' (fiberClosure (SemiPf.reindex e X).set) := by rw [hYs]
      _ = closure X.set := preimage_fiberClosure_zero X
  · -- the frontier
    calc (SemiPf.reindex e.symm Y').set
        = pullHomeo e.symm ⁻¹' Y'.set := sp_reindex_set_pull e.symm Y'
      _ = pullHomeo e.symm ⁻¹'
            (fiberClosure (SemiPf.reindex e X).set \ (SemiPf.reindex e X).set) := by rw [hY's]
      _ = (pullHomeo e.symm ⁻¹' (fiberClosure (SemiPf.reindex e X).set)) \
            (pullHomeo e.symm ⁻¹' (SemiPf.reindex e X).set) := Set.preimage_sdiff _ _ _
      _ = closure X.set \ X.set := by
            rw [preimage_fiberClosure_zero X, preimage_reindex_zero_set X]

end Work.WilE7
