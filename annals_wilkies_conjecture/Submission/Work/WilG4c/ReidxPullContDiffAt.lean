import Mathlib
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.StepLipHighAux

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

/-!
## Reindexing the `y`-pullback of a family from `p` to `p+1` parameters

The two joint functions compared in `ReidxPullContDiffAt` live on the two (different, but
canonically identified) spaces `ℝ^{p+(n+1)}` and `ℝ^{(p+1)+n}`; the second is obtained from
the first by the coordinate reindexing `Work.WilkG4c.reidx p n` of `StepLipDefs`, which is
the permutation `(l | x, y) ↦ (l, x | y)`.

The mathematical content of `ReidxPullContDiffAt` is that the two joint functions are
*the same function* after this reindexing, so that `C¹`-ness transfers through the
(coordinate-permutation) linear isometry.  This section builds that linear isometry and the
pointwise/global identities.

* `reidxCastAdd`, `reidxNatAddZero`, `reidxNatAddSucc` : the values of `reidx` on the
  `Fin.castAdd`/`Fin.natAdd` blocks.
* `reidxVal` : `reidx` preserves the numeric value of an index; hence `reidxEquiv` is the
  value preserving equivalence `Fin (p+(n+1)) ≃ Fin ((p+1)+n)`.
* `reidxLinEquiv` : the linear equivalence `u ↦ u ∘ reidx p n` of the two function spaces.
-/

/-- The reindexing `reidx p n` on the parameter block is the parameter block of
`ℝ^{(p+1)+n}`. -/
theorem reidxCastAdd (p n : ℕ) (i : Fin p) :
    Work.WilkG4c.reidx p n (Fin.castAdd (n + 1) i) = Fin.castAdd n (Fin.castSucc i) := by
  simp [Work.WilkG4c.reidx, Fin.addCases_left]

/-- The distinguished `x`-coordinate of `ℝ^{p+(n+1)}` is the *last* coordinate of the
parameter block of `ℝ^{(p+1)+n}`. -/
theorem reidxNatAddZero (p n : ℕ) :
    Work.WilkG4c.reidx p n (Fin.natAdd p (0 : Fin (n + 1))) = Fin.castAdd n (Fin.last p) := by
  simp [Work.WilkG4c.reidx, Fin.addCases_right, Fin.cases_zero]

/-- The `y`-block of `ℝ^{p+(n+1)}` is the `y`-block of `ℝ^{(p+1)+n}`. -/
theorem reidxNatAddSucc (p n : ℕ) (j : Fin n) :
    Work.WilkG4c.reidx p n (Fin.natAdd p j.succ) = Fin.natAdd (p + 1) j := by
  simp [Work.WilkG4c.reidx, Fin.addCases_right, Fin.cases_succ]

/-- `Work.WilkG4c.reidx` preserves the numeric value of an index. -/
theorem reidxVal (p n : ℕ) (k : Fin (p + (n + 1))) :
    (Work.WilkG4c.reidx p n k).val = k.val := by
  unfold Work.WilkG4c.reidx
  refine Fin.addCases (m := p) (n := n + 1) ?_ ?_ k
  · intro i; simp [Fin.addCases_left]
  · intro j
    refine Fin.cases ?_ ?_ j
    · simp [Fin.cases_zero]
    · intro j'; simp [Fin.cases_succ, Fin.val_natAdd, Fin.val_succ]; omega

/-- The value preserving equivalence `Fin (p+(n+1)) ≃ Fin ((p+1)+n)` whose underlying map is
the reindexing `Work.WilkG4c.reidx p n`. -/
noncomputable def reidxEquiv (p n : ℕ) : Fin (p + (n + 1)) ≃ Fin (p + 1 + n) where
  toFun := Work.WilkG4c.reidx p n
  invFun k := ⟨k.val, by omega⟩
  left_inv k := Fin.ext (reidxVal p n k)
  right_inv k := Fin.ext
    (by simpa using reidxVal p n (⟨k.val, by omega⟩ : Fin (p + (n + 1))))

@[simp] theorem reidxEquiv_apply (p n : ℕ) (k : Fin (p + (n + 1))) :
    reidxEquiv p n k = Work.WilkG4c.reidx p n k := rfl

/-- The coordinate reindexing `u ↦ u ∘ reidx p n` between the two function spaces. -/
noncomputable def reidxLinEquiv (p n : ℕ) :
    ((Fin (p + 1 + n) → ℝ) ≃ₗ[ℝ] (Fin (p + (n + 1)) → ℝ)) where
  toFun u := fun k => u (Work.WilkG4c.reidx p n k)
  map_add' u v := by funext k; rfl
  map_smul' c u := by funext k; rfl
  invFun v := fun j => v ((reidxEquiv p n).symm j)
  left_inv u := by
    funext k
    show u (Work.WilkG4c.reidx p n ((reidxEquiv p n).symm k)) = u k
    congr 1
    exact Equiv.apply_symm_apply (reidxEquiv p n) k
  right_inv v := by
    funext j
    show v ((reidxEquiv p n).symm (Work.WilkG4c.reidx p n j)) = v j
    congr 1
    exact Equiv.symm_apply_apply (reidxEquiv p n) j

@[simp] theorem reidxLinEquiv_apply (p n : ℕ) (u : Fin (p + 1 + n) → ℝ) :
    reidxLinEquiv p n u = fun k => u (Work.WilkG4c.reidx p n k) := rfl

/-- **The reindexed `y`-pullback family.**  This is the family whose graph is the one appearing
on the right-hand side of `ReidxPullContDiffAt`: the `y`-pullback read with the parameter
`w = (l, x)` of `ℝ^{p+1}` and the `y`-coordinates kept separate. -/
def reidxPullFamily {k p n : ℕ} (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k) :
    (Fin (p + 1) → ℝ) → (Fin n → ℝ) → ℝ :=
  fun w y => F i (fun j : Fin p => w (Fin.castSucc j))
    (Fin.cons (w (Fin.last p))
      (fun j : Fin n =>
        ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y))

/-- **The two joint functions agree after the reindexing.**  Reading `famFunHat (yPullback F ψ i)`
on the reindexed coordinates `u ↦ u ∘ reidx p n` gives exactly the joint function of the
reindexed family `reidxPullFamily F ψ i`. -/
theorem famFunHat_yPullback_comp_reidx {k p n : ℕ} (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k) :
    Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i) ∘
        ⇑(reidxLinEquiv p n).toContinuousLinearEquiv
      = Work.WilG4c.famFun (reidxPullFamily F ψ i) := by
  funext u
  show Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i)
      (fun k => u (Work.WilkG4c.reidx p n k)) = _
  have hz_l : (fun i : Fin p => u (Work.WilkG4c.reidx p n (Fin.castAdd (n + 1) i)))
      = (fun j : Fin p => u (Fin.castAdd n j.castSucc)) := by
    funext i; rw [reidxCastAdd]
  have hz0 : u (Work.WilkG4c.reidx p n (Fin.natAdd p (0 : Fin (n + 1))))
      = u (Fin.castAdd n (Fin.last p)) := by
    rw [reidxNatAddZero]
  have hz_tail : (Fin.tail (fun j : Fin (n + 1) => u (Work.WilkG4c.reidx p n (Fin.natAdd p j))))
      = (fun j : Fin n => u (Fin.natAdd (p + 1) j)) := by
    funext j
    show u (Work.WilkG4c.reidx p n (Fin.natAdd p j.succ)) = u (Fin.natAdd (p + 1) j)
    rw [reidxNatAddSucc]
  simp only [Work.WilkG4c.famFunHat, Work.WilkG4c.yPullback, Work.WilkG4c.pullbackMap,
    Work.WilG4c.famFun, reidxPullFamily, hz_l, hz0, hz_tail]

/-- **The point matching the two encodings.**  The reindexed `(p+1)`-parameter point
`Fin.append w y` is carried by the coordinate reindexing to `xPt (l,x) y`, i.e.
`(Fin.append w y) ∘ reidx p n = xPt ...`. -/
theorem reidxLinEquiv_apply_append {p n : ℕ} (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) :
    (reidxLinEquiv p n).toContinuousLinearEquiv (Fin.append w y)
      = Work.WilkG4c.xPt (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y :=
  Work.WilkG4c.append_comp_reidx w y

/-- Reading the `y`-pullback through the `(p+1)`-parameter reindexing: `C¹`-ness of the joint function `famFunHat (yPullback F ψ i)` at `xPt l x y` is the same as `C¹`-ness of the joint function `famFun (reindexed family)` at `Fin.append w y` (where `w = Fin.snoc l x`). -/
theorem ReidxPullContDiffAt {k p n : ℕ} (F : Work.WilkG4c.Family k p (n + 1))
    (ψ : Work.WilkG4c.ChartTuple (p + 1) n) (i : Fin k)
    (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) :
    ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i))
        (Work.WilkG4c.xPt (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y) ↔
      ContDiffAt ℝ 1 (Work.WilG4c.famFun
        (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
          F i (fun j : Fin p => w (Fin.castSucc j))
            (Fin.cons (w (Fin.last p))
              (fun j : Fin n =>
                ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y))))
        (Fin.append w y) := by
  have hfun : Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i) ∘
      ⇑(reidxLinEquiv p n).toContinuousLinearEquiv
      = Work.WilG4c.famFun (fun (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) =>
          F i (fun j : Fin p => w (Fin.castSucc j))
            (Fin.cons (w (Fin.last p))
              (fun j : Fin n =>
                ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y))) :=
    famFunHat_yPullback_comp_reidx F ψ i
  have hpt : (reidxLinEquiv p n).toContinuousLinearEquiv.symm
      (Work.WilkG4c.xPt (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y)
      = Fin.append w y := by
    rw [← reidxLinEquiv_apply_append w y, ContinuousLinearEquiv.symm_apply_apply]
  constructor
  · intro h
    have h2 := (ContinuousLinearEquiv.contDiffAt_comp_iff
      (reidxLinEquiv p n).toContinuousLinearEquiv).mpr h
    rwa [hfun, hpt] at h2
  · intro h
    have h2 : ContDiffAt ℝ 1
        (Work.WilkG4c.famFunHat (Work.WilkG4c.yPullback F ψ i) ∘
          ⇑(reidxLinEquiv p n).toContinuousLinearEquiv)
        ((reidxLinEquiv p n).toContinuousLinearEquiv.symm
          (Work.WilkG4c.xPt (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y)) := by
      rwa [hfun, hpt]
    exact (ContinuousLinearEquiv.contDiffAt_comp_iff
      (reidxLinEquiv p n).toContinuousLinearEquiv).mp h2

end Work.WilG4c
