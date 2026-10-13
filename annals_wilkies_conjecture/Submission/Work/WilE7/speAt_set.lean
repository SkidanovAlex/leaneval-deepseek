/-
  WilE7, fiber finiteness: the set of the specialization is the fibre.

  `Work.WilE7.speAt_set`: specializing a semi-Pfaffian set `X ⊆ ℝ^{p+q}` at a base point
  `x ∈ cubeC p` produces a semi-Pfaffian set in `ℝ^q` whose set is exactly the fibre of `X.set`
  over `x`, i.e. `{y | Fin.append x y ∈ X.set}`.

  The two ingredients are

  * `mem_cubeC_append`  : for `x ∈ cubeC p`, the glued point `(x, y)` lies in `cubeC (p+q)` iff
    `y ∈ cubeC q`;
  * `speBasicAt_holds`  : the specialized basic set holds at `y` iff the original basic set holds
    at `(x, y)`, which is `eaEval_speAt` (`Submission/Work/WilE7/SpeAt.lean`) read through the
    `List.map` defining `speBasicAt`.

  The remaining step is bookkeeping: `(speSemiPfAt x X).basics = X.basics.map (speBasicAt x)`,
  so an existential over the mapped list is an existential over the original list.
-/
import Mathlib
import Submission.Work.WilE7.SpeAt

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-- `speBasicAt` and `holds` interact as expected: the specialized basic set holds at the fibre
point `y` iff the original basic set holds at the glued point `(x, y)`. -/
theorem speBasicAt_holds {p q r : ℕ} (x : Fin p → ℝ) (c : EAChain (p + q) r)
    (B : Basic (p + q) r) (y : Fin q → ℝ) :
    (speBasicAt (q := q) x B).holds (speChainAt x c) y ↔ B.holds c (Fin.append x y) := by
  unfold Basic.holds speBasicAt
  simp only [List.forall_mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by rw [← eaEval_speAt]; exact h1 f hf,
           fun g hg => by rw [← eaEval_speAt]; exact h2 g hg⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun f hf => by rw [eaEval_speAt]; exact h1 f hf,
           fun g hg => by rw [eaEval_speAt]; exact h2 g hg⟩

/-- For `x` in the cube, the glued point `(x, y)` lies in the cube iff `y` does. -/
theorem mem_cubeC_append {p q : ℕ} (x : Fin p → ℝ) (hx : x ∈ cubeC p) (y : Fin q → ℝ) :
    Fin.append x y ∈ cubeC (p + q) ↔ y ∈ cubeC q := by
  constructor
  · intro h l
    have h1 := h (Fin.natAdd p l)
    rwa [Fin.append_right] at h1
  · intro hy i
    refine Fin.addCases (motive := fun i => |Fin.append x y i| ≤ 1)
      (fun i₀ => ?_) (fun l => ?_) i
    · rw [Fin.append_left]; exact hx i₀
    · rw [Fin.append_right]; exact hy l

theorem speAt_set {p q : ℕ} (x : Fin p → ℝ) (X : WilkiesDesign.E.SemiPf (p + q))
    (hx : x ∈ WilkiesDesign.E.cubeC p) :
    (Work.WilE7.speSemiPfAt x X).set = WilkiesDesign.E.fiber X.set x := by
  ext y
  show (y ∈ cubeC q ∧ ∃ B ∈ X.basics.map (speBasicAt (q := q) x),
        B.holds (speChainAt x X.c) y)
    ↔ (Fin.append x y ∈ cubeC (p + q) ∧ ∃ B ∈ X.basics, B.holds X.c (Fin.append x y))
  constructor
  · rintro ⟨hyq, B, hB, hh⟩
    rw [List.mem_map] at hB
    obtain ⟨B', hB', rfl⟩ := hB
    exact ⟨(mem_cubeC_append x hx y).mpr hyq, B', hB', (speBasicAt_holds x X.c B' y).mp hh⟩
  · rintro ⟨hc, B, hB, hh⟩
    exact ⟨(mem_cubeC_append x hx y).mp hc, speBasicAt x B, List.mem_map.mpr ⟨B, hB, rfl⟩,
      (speBasicAt_holds x X.c B y).mpr hh⟩

end Work.WilE7
