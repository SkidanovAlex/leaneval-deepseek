/-
  WilG4c / SliceCoresMain / `slice_cores`.

  The *fibre cores* of a family member `f : ℝ^p × ℝ^N → ℝ` (`Work.WilG4c.FibreCoreDefs`):
  every `l`-fibre of a joint core `jointCore f a` of `famFun f` is the corresponding core
  `fibCore (f l) a` of the slice `z ↦ f l z`.  Here `CoreIx N` indexes the four families

  * `fbad i`     — the fibre of `g` in direction `i` is not differentiable (`fibBad g i`),
  * `fbadJ i i'` — the same for the junk partial `junkP g i`,
  * `discJ i`    — the junk partial `junkP g i` is discontinuous (`disc (junkP g i)`),
  * `disc0`      — `g` itself is discontinuous (`disc g`),

  and the two readings are

  * `fibCore g`, the *fibre* reading of `g` inside `ℝ^N`, and
  * `jointCore f`, the *joint* reading of `famFun f` in `ℝ^{p+N}`, taking only fibre directions
    `Fin.natAdd p ·` (and, for the discontinuity pieces, the *fibre-wise* discontinuity
    `fibDisc`, which keeps the parameter fixed inside the quantifier).

  The engine of the statement is the single-coordinate nature of `junkP`
  (`fibreMap h i y = fun t ↦ h (Function.update y i t)`) together with the compatibility of
  `Function.update` with `Fin.append`:

      Function.update (Fin.append l z) (Fin.natAdd p i) t = Fin.append l (Function.update z i t),

  which makes the lifted fibre direction `Fin.natAdd p i` act exactly like `i` inside the slice
  `z ↦ f l z`.  The first conjunct of `slice_cores` is `junkP_slice` below; the second is the
  four-case `CoreIx` analysis, each case an instance of `fibreOf_fibBad_natAdd` /
  `fibreOf_fibDisc` combined with the corresponding slice identity.
-/
import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c.SliceCoresMain

open WilkiesDesign WilkiesDesign.CG
open Work.WilG1.Cell

/-! ## The `Function.update` / `Fin.append` compatibility

`Fin.append l z` splits the coordinates of `ℝ^{p+N}` into the parameter part (`Fin.castAdd N ·`)
and the fibre part (`Fin.natAdd p ·`).  Updating the *fibre* coordinate `Fin.natAdd p i` of
`Fin.append l z` is the same as updating the coordinate `i` of `z` and re-appending the fixed
parameter `l`. -/
theorem append_update_natAdd {p N : ℕ} (l : Fin p → ℝ) (z : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    Function.update (Fin.append l z) (Fin.natAdd p i) t
      = Fin.append l (Function.update z i t) := by
  funext k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · -- parameter coordinate: `update` does not touch it
    have hne : (Fin.castAdd N a : Fin (p + N)) ≠ Fin.natAdd p i := by
      intro h
      have h1 := Fin.castAdd_lt N a
      rw [h, Fin.val_natAdd] at h1
      omega
    rw [Function.update_of_ne hne, Fin.append_left, Fin.append_left]
  · -- fibre coordinate: both sides reduce to the same `update` of `z`
    rw [Function.update_apply, Fin.append_right, Fin.append_right, Function.update_apply]
    simp only [Fin.natAdd_inj]

/-- The joint function `famFun f` evaluated at a concatenated point is the slice `f l`. -/
theorem famFun_append {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (l : Fin p → ℝ)
    (u : Fin N → ℝ) : famFun f (Fin.append l u) = f l u := by
  simp [famFun, Fin.append_left, Fin.append_right]

/-! ## The slice identity for `junkP`

`junkP` is a one-coordinate derivative, so for a *fibre* direction `Fin.natAdd p i` the junk
partial of `famFun f` at `Fin.append l z` is the junk partial of the slice `f l` at `z`. -/
theorem junkP_slice {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (i : Fin N) (l : Fin p → ℝ) :
    (fun z : Fin N → ℝ => junkP (famFun f) (Fin.natAdd p i) (Fin.append l z))
      = fun z : Fin N → ℝ => junkP (fun z : Fin N → ℝ => f l z) i z := by
  funext z
  change deriv (fibreMap (famFun f) (Fin.natAdd p i) (Fin.append l z))
        ((Fin.append l z) (Fin.natAdd p i))
      = deriv (fibreMap (fun z : Fin N → ℝ => f l z) i z) (z i)
  rw [Fin.append_right]
  have hthis : fibreMap (famFun f) (Fin.natAdd p i) (Fin.append l z)
      = fibreMap (fun z : Fin N → ℝ => f l z) i z := by
    funext t
    change famFun f (Function.update (Fin.append l z) (Fin.natAdd p i) t)
        = (fun z : Fin N → ℝ => f l z) (Function.update z i t)
    rw [append_update_natAdd, famFun_append]
  rw [hthis]

/-- The fibre maps of `famFun f` in a lifted fibre direction and of the slice `f l` agree. -/
theorem fibreMap_famFun_slice {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (i : Fin N)
    (l : Fin p → ℝ) (y : Fin N → ℝ) :
    fibreMap (famFun f) (Fin.natAdd p i) (Fin.append l y)
      = fibreMap (fun z : Fin N → ℝ => f l z) i y := by
  funext t
  change famFun f (Function.update (Fin.append l y) (Fin.natAdd p i) t)
      = (fun z : Fin N → ℝ => f l z) (Function.update y i t)
  rw [append_update_natAdd, famFun_append]

/-- The same for the junk partial in a lifted fibre direction: the slice of
`junkP (famFun f) (Fin.natAdd p i)` is `junkP (f l) i`. -/
theorem fibreMap_junkP_famFun_slice {p N : ℕ} (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) (i i' : Fin N)
    (l : Fin p → ℝ) (y : Fin N → ℝ) :
    fibreMap (junkP (famFun f) (Fin.natAdd p i)) (Fin.natAdd p i') (Fin.append l y)
      = fibreMap (junkP (fun z : Fin N → ℝ => f l z) i) i' y := by
  funext t
  change junkP (famFun f) (Fin.natAdd p i)
        (Function.update (Fin.append l y) (Fin.natAdd p i') t)
      = junkP (fun z : Fin N → ℝ => f l z) i (Function.update y i' t)
  rw [append_update_natAdd]
  exact congr_fun (junkP_slice f i l) (Function.update y i' t)

/-! ## Slicing the joint cores

The fibre over a parameter `l` of a joint `fibBad` (in a fibre direction) and of a joint
fibre-wise discontinuity `fibDisc`. -/
theorem fibreOf_fibBad_natAdd {p N : ℕ} (H : (Fin (p + N) → ℝ) → ℝ) (i : Fin N) (l : Fin p → ℝ) :
    fibreOf (fibBad H (Fin.natAdd p i)) l
      = {y : Fin N → ℝ |
          ¬ DifferentiableAt ℝ (fibreMap H (Fin.natAdd p i) (Fin.append l y)) (y i)} := by
  ext y
  simp only [fibreOf, fibBad, Set.mem_ofPred_eq, Fin.append_right]

theorem fibreOf_fibDisc {p N : ℕ} (H : (Fin (p + N) → ℝ) → ℝ) (l : Fin p → ℝ) :
    fibreOf (fibDisc H) l
      = {y : Fin N → ℝ | ¬ ContinuousAt (fun z : Fin N → ℝ => H (Fin.append l z)) y} := by
  ext y
  simp only [fibreOf, fibDisc, Set.mem_ofPred_eq, Fin.append_left, Fin.append_right]

/-! ## The main statement -/
theorem slice_cores (p N : ℕ) (f : (Fin p → ℝ) → (Fin N → ℝ) → ℝ) :
    (∀ (i : Fin N) (l : Fin p → ℝ),
      (fun z : Fin N → ℝ => Work.WilG1.Cell.junkP (Work.WilG4c.famFun f)
        (Fin.natAdd p i) (Fin.append l z))
        = fun z : Fin N → ℝ => Work.WilG1.Cell.junkP (fun z : Fin N → ℝ => f l z) i z) ∧
    (∀ (a : Work.WilG4c.CoreIx N) (l : Fin p → ℝ),
      Work.WilG4c.fibreOf (Work.WilG4c.jointCore f a) l
        = Work.WilG4c.fibCore (fun z : Fin N → ℝ => f l z) a) := by
  refine ⟨?_, ?_⟩
  · -- first conjunct: the slice identity for `junkP`
    intro i l
    exact junkP_slice f i l
  · -- second conjunct: each fibre core is the fibre of the corresponding joint core
    intro a l
    cases a with
    | fbad i =>
      -- `fibBad (famFun f) (Fin.natAdd p i)` slices to `fibBad (f l) i`
      ext y
      simp only [fibreOf, jointCore, fibCore, fibBad, Set.mem_ofPred_eq, Fin.append_right,
        fibreMap_famFun_slice]
    | fbadJ i i' =>
      -- `fibBad (junkP (famFun f) (Fin.natAdd p i)) (Fin.natAdd p i')` slices to
      -- `fibBad (junkP (f l) i) i'`
      ext y
      simp only [fibreOf, jointCore, fibCore, fibBad, Set.mem_ofPred_eq, Fin.append_right,
        fibreMap_junkP_famFun_slice]
    | discJ i =>
      -- `fibDisc (junkP (famFun f) (Fin.natAdd p i))` slices to `disc (junkP (f l) i)`
      ext y
      simp only [fibreOf, jointCore, fibCore, fibDisc, disc, Set.mem_ofPred_eq, Fin.append_left,
        Fin.append_right, junkP_slice f i l]
    | disc0 =>
      -- `fibDisc (famFun f)` slices to `disc (f l)`
      ext y
      simp only [fibreOf, jointCore, fibCore, fibDisc, disc, Set.mem_ofPred_eq, Fin.append_left,
        Fin.append_right, famFun_append]

end Work.WilG4c.SliceCoresMain
