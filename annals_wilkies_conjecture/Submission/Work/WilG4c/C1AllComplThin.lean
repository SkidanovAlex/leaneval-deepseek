import Mathlib
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilG4c.C1SliceProjThin
import Submission.Work.WilG4c.ReidxPullGraphMem
import Submission.Work.WilG4c.ReidxPullContDiffAt

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-!
## `C1AllComplThin`

The complement of `C1All` in the slab is thin.  The work is split in three:

* `Work.WilG4c.C1SliceProjThin` — the general o-minimal fact: for a definable family whose
  `y`-slices are `C¹` on an open set `U` over an open parameter set `W`, the parameters at
  which some fibre point is a non-`C¹` point of the joint function form a thin set;
* `Work.WilG4c.ReidxPullGraphMem` — the graph of the `(p+1)`-parameter reindexing of the
  `y`-pullback is `Ω`-bounded (from `YPullbackGraphUniform`);
* `Work.WilG4c.ReidxPullContDiffAt` — reading the pullback through that reindexing preserves
  `ContDiffAt`.
-/

/-- The `y`-pullback reindexed as a `(p+1)`-parameter, `n`-cube family: the parameter `w`
splits as `(l, x) = (Fin.init w, Fin.last w)`, and the cube variable is `y`. -/
private def reidxPull {k p n : ℕ} (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k) :
    (Fin (p + 1) → ℝ) → (Fin n → ℝ) → ℝ :=
  fun w y => F i (fun j : Fin p => w (Fin.castSucc j))
    (Fin.cons (w (Fin.last p))
      (fun j : Fin n => ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y))

/-- The open cube is open. -/
private theorem openCube_isOpen_C1 (n : ℕ) : IsOpen (openCube n) := by
  have h : openCube n = ⋂ i : Fin n, {t : Fin n → ℝ | t i ∈ Set.Ioo (0 : ℝ) 1} := by
    ext t; simp [openCube, Set.mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

/-- The slab `{w | w (last p) ∈ I}` is open. -/
private theorem slab_isOpen_C1 (p : ℕ) : IsOpen {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I} := by
  have h : {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I}
      = (fun w : Fin (p + 1) → ℝ => w (Fin.last p)) ⁻¹' (Set.Ioo (0 : ℝ) 1) := by
    ext w; simp [I]
  rw [h]
  exact isOpen_Ioo.preimage (continuous_apply _)

/-- The `C¹`-slices hypothesis descends to the reindexed family. -/
private theorem hsm_C1 {k p n : ℕ} (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k)
    (hψsm : ∀ l : Fin p → ℝ, ∀ x ∈ I,
      ContDiffOn ℝ 1 (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
        (openCube n)) :
    ∀ w ∈ {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I},
      ContDiffOn ℝ 1 (reidxPull F ψ i w) (openCube n) :=
  fun w hw => hψsm (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) hw

/-- The two descriptions of the bad slab agree. -/
private theorem badSet_C1 {k p n : ℕ} (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k)
    (htrans : ∀ w : Fin (p + 1) → ℝ, ∀ y : Fin n → ℝ,
      (ContDiffAt ℝ 1 (famFunHat (Work.WilkG4c.yPullback F ψ i))
        (xPt (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y) ↔
      ContDiffAt ℝ 1 (Work.WilG4c.famFun (reidxPull F ψ i)) (Fin.append w y))) :
    {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧
        w ∉ C1All (Work.WilkG4c.yPullback F ψ i)} =
      {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧
        ∃ y ∈ openCube n,
          ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun (reidxPull F ψ i)) (Fin.append w y)} := by
  ext w
  have hS : interior {z | ContDiffAt ℝ 1 (famFunHat (Work.WilkG4c.yPullback F ψ i)) z}
      = {z | ContDiffAt ℝ 1 (famFunHat (Work.WilkG4c.yPullback F ψ i)) z} :=
    (isOpen_contDiffAt_set (famFunHat (Work.WilkG4c.yPullback F ψ i))).interior_eq
  constructor
  · rintro ⟨hw, hnot⟩
    have hnot' : ¬ (∀ y : Fin n → ℝ, y ∈ openCube n →
        xPt (fun i : Fin p => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
          interior {z | ContDiffAt ℝ 1 (famFunHat (Work.WilkG4c.yPullback F ψ i)) z}) := hnot
    push_neg at hnot'
    obtain ⟨y, hy, hbad⟩ := hnot'
    rw [hS] at hbad
    exact ⟨hw, y, hy, fun hc => hbad ((htrans w y).mpr hc)⟩
  · rintro ⟨hw, y, hy, hbad⟩
    refine ⟨hw, ?_⟩
    intro hC1
    have hbad' : ¬ ContDiffAt ℝ 1 (famFunHat (Work.WilkG4c.yPullback F ψ i))
        (xPt (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y) :=
      fun hc => hbad ((htrans w y).mp hc)
    have h1 : xPt (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y ∈
        interior {z | ContDiffAt ℝ 1 (famFunHat (Work.WilkG4c.yPullback F ψ i)) z} := hC1 y hy
    rw [hS] at h1
    exact hbad' h1

/-- The complement of `C1All` is thin in the slab `x ∈ I`: for a family member whose graph is `Ω`-bounded and a `y`-chart `ψ` whose composite is `C^1` on the cube for every `(l,x)` with `x ∈ I`, the set of `(l,x)` with `x ∈ I` at which some fibre point is a non-`C¹` point of the joint function is thin. -/
theorem C1AllComplThin (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (p n k : ℕ)
    (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
    (i : Fin k) (F0 Dg aψ Dgψ : ℕ)
    (hG : WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 Dg (p + (n + 1) + 1))
    (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1))
    (hψsm : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I,
      ContDiffOn ℝ 1 (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
        (WilkiesDesign.openCube n)) :
    interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧
      w ∉ Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i)} = ∅ := by
  obtain ⟨F1, D1, hg⟩ := Work.WilG4c.ReidxPullGraphMem S p n k F0 Dg aψ Dgψ F ψ i hG hψg
  have htrans := Work.WilG4c.ReidxPullContDiffAt (F := F) (ψ := ψ) (i := i)
  have H := Work.WilG4c.C1SliceProjThin S hcd (p + 1) n F1 D1 (reidxPull F ψ i) hg
    {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I} (slab_isOpen_C1 p)
    (WilkiesDesign.openCube n) (openCube_isOpen_C1 n) (hsm_C1 F ψ i hψsm)
  rw [badSet_C1 F ψ i htrans]
  simpa only [Set.mem_ofPred_eq] using H

end Work.WilkG4c
