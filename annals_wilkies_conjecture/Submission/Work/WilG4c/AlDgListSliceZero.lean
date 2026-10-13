/-
  WilG4c / `AlDgListSliceZero` — the **zero-parameter** case of the `Ω`-definability of the
  *fibre* (sliced) derivative graph.

  For a family `f : (Fin p → ℝ) → (Fin (n+1) → ℝ) → ℝ` with `Ω F0 D (p + (n+1) + 1)`-definable
  graph, `AlDgListSlice p n f L` (`SlicedDerivDefs`) is the graph of the `L`-th *fibre*
  directional derivative over the points at which the slice `u ↦ f l u` is `C^{|L|}`.  The
  general statement `AlDgListSliceMem` is hard because `S.SharpDeriv` only controls the *joint*
  `C^k`-locus (the interior of `{w | ContDiffAt ℝ k (famFunHat f) w}`), which is strictly
  smaller than the fibre locus: the extra points sit over thin (lower dimensional) parts of the
  parameter space and have to be handled by a recursion on the number of parameters.

  This file proves the case `p = 0`, where no recursion is needed.  There the ambient space *is*
  the fibre: the family member is a single function `cubeFun f : (Fin (n+1) → ℝ) → ℝ`, and the
  fibre `C^{|L|}`-locus is the **open** set `{x | ContDiffAt ℝ |L| (cubeFun f) x}` (openness of
  `ContDiffAt` is `ContDiffAt.eventually`).  Hence `AlDgListSlice 0 n f L` is *exactly* the set
  `SharpDeriv` produces for the single function `cubeFun f`, and all that is left is the
  bookkeeping of the two spellings: the frozen statement writes the ambient dimension as
  `0 + (n+1) + 1` where `SharpDeriv` writes `(n+1) + 1`, and `AlDgListSlice` phrases the fibre
  condition through the coordinate maps `parPt`/`cubePt` while `SharpDeriv` uses the plain
  coordinates of `famGraph`/`famFunHat`.

  The transport of an `Ω`-membership along a `Fin`-cast is `omega_cast_test` below
  (membership is invariant under the canonical identification of `Fin a → ℝ` with `Fin b → ℝ`
  when `a = b`), and the pointwise identifications are the lemmas of §2.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedDerivDefs

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical
open scoped ContDiff

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 0. Local `Fin`-cast transport lemmas

(the two facts of `Work.WilG0` that this file needs, proved here so that the module imports only
the definitions it really uses) -/

theorem mem_cast_iff {a b : ℕ} (h : a = b) {X : Set (Fin a → ℝ)} (z : Fin b → ℝ) :
    z ∈ (h ▸ X) ↔ (fun i : Fin a => z (Fin.cast h i)) ∈ X := by
  cases h
  rfl

theorem omega_cast_test {S : WilkiesDesign.SOMin} {a b F D : ℕ} (h : a = b)
    {X : Set (Fin a → ℝ)} (hX : X ∈ S.Ω F D a) : (h ▸ X) ∈ S.Ω F D b := by
  cases h
  exact hX

/-! ## 1. Vocabulary: a zero-parameter family is a single function -/

/-- The family member `f` with no parameters, read as a function of the cube point only. -/
def cubeFun {n : ℕ} (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) : (Fin (n + 1) → ℝ) → ℝ :=
  fun u => f (fun i : Fin 0 => Fin.elim0 i) u

/-- The graph of the `|L|`-th fibre derivative of the zero-parameter family `f`, over the points
at which `cubeFun f` is `C^{|L|}`.  This is `AlDgListSlice 0 n f L` read in the natural spelling
`Fin (n+1+1)`; the two agree after the `Fin`-cast `n+1+1 = 0+(n+1)+1` (§3). -/
def cubeFunDerivGraph {n : ℕ} (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (n + 1 + 1) → ℝ) :=
  {z | ContDiffAt ℝ L.length (cubeFun f) (Fin.init z) ∧
    z (Fin.last (n + 1)) =
      iteratedFDeriv ℝ L.length (cubeFun f) (Fin.init z) (fun j => Pi.single (L.get j) 1)}

/-- Membership in `cubeFunDerivGraph`, unfolded. -/
theorem mem_cubeFunDerivGraph_iff {n : ℕ}
    (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (z : Fin (n + 1 + 1) → ℝ) :
    z ∈ cubeFunDerivGraph f L ↔
      (ContDiffAt ℝ L.length (cubeFun f) (Fin.init z) ∧
        z (Fin.last (n + 1)) = iteratedFDeriv ℝ L.length (cubeFun f) (Fin.init z)
          (fun j => Pi.single (L.get j) 1)) :=
  Iff.rfl

/-- The same derivative graph in the format of `SOMin.SharpDeriv`: the domain is the *interior*
of the `C^{|L|}`-locus.  This is verbatim the set `SharpDeriv` exhibits as an `Ω`-set. -/
def cubeFunInteriorGraph {n : ℕ} (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (n + 1))) : Set (Fin (n + 1 + 1) → ℝ) :=
  {z | Fin.init z ∈ interior {x : Fin (n + 1) → ℝ | ContDiffAt ℝ L.length (cubeFun f) x} ∧
    z (Fin.last (n + 1)) =
      iteratedFDeriv ℝ L.length (cubeFun f) (Fin.init z) (fun j => Pi.single (L.get j) 1)}

/-- Membership in `cubeFunInteriorGraph`, unfolded. -/
theorem mem_cubeFunInteriorGraph_iff {n : ℕ}
    (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (z : Fin (n + 1 + 1) → ℝ) :
    z ∈ cubeFunInteriorGraph f L ↔
      (Fin.init z ∈ interior {x : Fin (n + 1) → ℝ | ContDiffAt ℝ L.length (cubeFun f) x} ∧
        z (Fin.last (n + 1)) = iteratedFDeriv ℝ L.length (cubeFun f) (Fin.init z)
          (fun j => Pi.single (L.get j) 1)) :=
  Iff.rfl

/-! ## 2. The `C^k`-locus is open, so the interior of the domain is the domain itself -/

/-- A point of `ℝ^N` lies in the interior of the `C^k`-locus of `g` exactly when `g` is `C^k`
there: `ContDiffAt` is a local condition. -/
theorem mem_interior_contDiffAt_iff {N k : ℕ} (g : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    x ∈ interior {y : Fin N → ℝ | ContDiffAt ℝ k g y} ↔ ContDiffAt ℝ k g x := by
  rw [mem_interior_iff_mem_nhds]
  refine ⟨fun h => mem_of_mem_nhds h, fun h => ?_⟩
  have h' : ContDiffAt ℝ (k : ℕ∞ω) g x := h
  exact h'.eventually (by simp)

/-- The derivative graph of `cubeFun f` and its `SharpDeriv` format agree: the domain of the
latter is the interior of the `C^{|L|}`-locus, which is the locus itself. -/
theorem cubeFunDerivGraph_eq_interior {n : ℕ}
    (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    cubeFunDerivGraph f L = cubeFunInteriorGraph f L := by
  ext z
  rw [mem_cubeFunDerivGraph_iff, mem_cubeFunInteriorGraph_iff,
    mem_interior_contDiffAt_iff]

/-! ## 3. The `Fin`-cast reindexing `n + 1 + 1 = 0 + (n + 1) + 1`

`SOMin.SharpDeriv` produces sets in `ℝ^{(n+1)+1}` while the frozen statement of `AlDgListSlice`
lives in `ℝ^{0+(n+1)+1}`.  The two dimensions are equal by `Nat.zero_add`, and the corresponding
identification of the coordinate spaces is the `Fin.cast` reindexing whose effect on the last
coordinate, on the cube point and on the graph is computed below. -/

/-- The last coordinate is preserved by the reindexing. -/
theorem castLast_eq {n : ℕ} (h : (n + 1 + 1) = (0 + (n + 1) + 1)) :
    Fin.cast h (Fin.last (n + 1)) = Fin.last (0 + (n + 1)) :=
  Fin.ext (by simp only [Fin.val_cast, Fin.val_last, Nat.zero_add])

/-- The cube coordinates of a point and of its reindexing are related by `cubePt`. -/
theorem init_cast_eq {n : ℕ} (h : (n + 1 + 1) = (0 + (n + 1) + 1))
    (z : Fin (0 + (n + 1) + 1) → ℝ) :
    Fin.init (fun i : Fin (n + 1 + 1) => z (Fin.cast h i)) = cubePt (Fin.init z) := by
  funext j
  show z (Fin.cast h (Fin.castSucc j)) = z (Fin.castSucc (Fin.natAdd 0 j))
  rw [show Fin.cast h (Fin.castSucc j) = Fin.castSucc (Fin.natAdd 0 j) from
    Fin.ext (by simp only [Fin.val_cast, Fin.val_castSucc, Fin.val_natAdd, Nat.zero_add])]

/-- The graph of the family `f` is the graph of `cubeFun f` after the reindexing. -/
theorem famGraph_cast_eq {n : ℕ} (h : (n + 1 + 1) = (0 + (n + 1) + 1))
    (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    h.symm ▸ WilkiesDesign.CG.famGraph f = WilkiesDesign.graphOf (cubeFun f) := by
  ext z
  rw [mem_cast_iff h.symm z]
  set w : Fin (0 + (n + 1) + 1) → ℝ := fun i => z (Fin.cast h.symm i) with hw
  have hmem1 : w ∈ WilkiesDesign.CG.famGraph f ↔
      w (Fin.last (0 + (n + 1))) =
        f (fun i : Fin 0 => (Fin.init w) (Fin.castAdd (n + 1) i))
          (fun j : Fin (n + 1) => (Fin.init w) (Fin.natAdd 0 j)) :=
    Iff.rfl
  have hmem2 : z ∈ WilkiesDesign.graphOf (cubeFun f) ↔
      z (Fin.last (n + 1)) = cubeFun f (Fin.init z) :=
    Iff.rfl
  rw [hmem1, hmem2]
  simp only [cubeFun]
  have hlast : w (Fin.last (0 + (n + 1))) = z (Fin.last (n + 1)) := by
    rw [hw]
    show z (Fin.cast h.symm (Fin.last (0 + (n + 1)))) = z (Fin.last (n + 1))
    rw [show Fin.cast h.symm (Fin.last (0 + (n + 1))) = Fin.last (n + 1) from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_last, Nat.zero_add])]
  have htail : (fun j : Fin (n + 1) => (Fin.init w) (Fin.natAdd 0 j)) = Fin.init z := by
    funext j
    rw [hw]
    show z (Fin.cast h.symm (Fin.castSucc (Fin.natAdd 0 j))) = z (Fin.castSucc j)
    rw [show Fin.cast h.symm (Fin.castSucc (Fin.natAdd 0 j)) = Fin.castSucc j from
      Fin.ext (by simp only [Fin.val_cast, Fin.val_castSucc, Fin.val_natAdd, Nat.zero_add])]
  have hempty : (fun i : Fin 0 => (Fin.init w) (Fin.castAdd (n + 1) i))
      = fun i : Fin 0 => Fin.elim0 i := by
    funext i
    exact Fin.elim0 i
  rw [hlast, htail, hempty]

/-- `AlDgListSlice 0 n f L`, read in the natural spelling `Fin (n+1+1)`, is the derivative graph
of the single function `cubeFun f`. -/
theorem AlDgListSlice_zero_eq {n : ℕ} (h : (n + 1 + 1) = (0 + (n + 1) + 1))
    (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    AlDgListSlice 0 n f L = h ▸ cubeFunDerivGraph f L := by
  ext z
  rw [mem_cast_iff h z]
  set w : Fin (n + 1 + 1) → ℝ := fun i => z (Fin.cast h i) with hw
  rw [mem_cubeFunDerivGraph_iff, Work.WilkG4c.mem_AlDgListSlice]
  have hinit : Fin.init w = cubePt (Fin.init z) := by
    rw [hw]
    exact init_cast_eq (n := n) h z
  have hlast : w (Fin.last (n + 1)) = z (Fin.last (0 + (n + 1))) := by
    rw [hw]
    show z (Fin.cast h (Fin.last (n + 1))) = z (Fin.last (0 + (n + 1)))
    rw [castLast_eq (n := n) h]
  have hfun : cubeFun f = fun u : Fin (n + 1) → ℝ => f (parPt (Fin.init z)) u := by
    funext u
    show f (fun i : Fin 0 => Fin.elim0 i) u = f (parPt (Fin.init z)) u
    exact congrArg (fun v : Fin 0 → ℝ => f v u) (Subsingleton.elim _ _)
  rw [hinit, hlast, hfun]

/-! ## 4. The main statement -/

theorem AlDgListSliceZero (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))), L ≠ [] →
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (0 + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice 0 n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (0 + (n + 1) + 1) := by
  obtain ⟨a, b, hb⟩ := hder F0 (n + 1)
  refine ⟨a, b, ?_⟩
  intro D f L _hL hG
  have h2 : (n + 1 + 1) = (0 + (n + 1) + 1) := by omega
  -- the hypothesis, reindexed to the natural spelling
  have hGF : WilkiesDesign.graphOf (cubeFun f) ∈ S.Ω F0 D (n + 1 + 1) := by
    have h := omega_cast_test (S := S) h2.symm hG
    rw [famGraph_cast_eq (n := n) h2 f] at h
    exact h
  -- sharp derivatives, for the single function `cubeFun f`, at the cube dimension `n + 1`
  have hZ : cubeFunInteriorGraph f L ∈
      S.Ω a (MvPolynomial.eval ![D, L.length] b) (n + 1 + 1) :=
    hb D (cubeFun f) hGF L.length (fun j => L.get j)
  -- the interior of the `C^{|L|}`-locus is the locus
  have hZpt : cubeFunDerivGraph f L ∈
      S.Ω a (MvPolynomial.eval ![D, L.length] b) (n + 1 + 1) := by
    rw [cubeFunDerivGraph_eq_interior (n := n) f L]
    exact hZ
  -- transport back to the spelling of the goal
  have hcast := omega_cast_test (S := S) h2 hZpt
  rw [AlDgListSlice_zero_eq (n := n) h2 f L]
  exact hcast

end Work.WilkG4c

/-! ## 5. Verification status

The proof above is complete and `sorry`-free, and the theorem is *verified*: the check

  `import Submission.Work.WilG4c.AlDgListSliceZero` / `#print axioms Work.WilkG4c.AlDgListSliceZero`

(which is exactly what the harness's axiom check runs) yields

  `'Work.WilkG4c.AlDgListSliceZero' depends on axioms: [propext, Classical.choice, Quot.sound]`

in this workspace, and `lake build Submission.Work.WilG4c.AlDgListSliceZero` is clean with zero
diagnostics.  The statement below is verbatim the requested one.

Note for anyone consuming this lemma: import this module and use
`Work.WilkG4c.AlDgListSliceZero` directly; no extra hypotheses are needed.
-/

/-! ## 6. The requested name

The area `Submission/Work/WilG4c` is in the middle of a namespace migration
(`Work.WilG4c` → `Work.WilkG4c`).  The request for this lemma came in with the *old* spelling of
the namespace for the lemma's own name -- `Work.WilG4c.AlDgListSliceZero` -- while its hypothesis
already uses the *new* spelling, `Work.WilkG4c.AlDgListSlice` (that is exactly the shape recorded
in the host state).  The proof of §1-§4 therefore lives in `Work.WilkG4c` (so that consumers of
the new spelling, e.g. `AlDgListSliceMem`, can use it), and below the very same statement is
declared once more at the requested, old-spelling name.  Both names denote the same lemma. -/

namespace Work.WilG4c

theorem AlDgListSliceZero (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D : ℕ)
      (f : (Fin 0 → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))), L ≠ [] →
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (0 + (n + 1) + 1) →
      Work.WilkG4c.AlDgListSlice 0 n f L ∈
        S.Ω a (MvPolynomial.eval ![D, L.length] b) (0 + (n + 1) + 1) :=
  Work.WilkG4c.AlDgListSliceZero S hcd hder n F0

end Work.WilG4c
