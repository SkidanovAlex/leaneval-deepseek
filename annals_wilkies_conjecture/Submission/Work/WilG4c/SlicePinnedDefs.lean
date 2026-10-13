/-
  WilG4c — `SlicePinnedDefs`: the *pinned* (slice) spelling of the fibre derivative graph,
  the vocabulary of `Work.WilkG4c.surrogateSliceFamGraph_mem`.

  `surrogateSlice p n f γ M l x` (module `SlicedSurrogateDefs`) tests smoothness of the *slice*
  `slice (f l) x` — the fibre of `f l` at the distinguished coordinate `x` — at `γ l x`, and
  reads the `|M|`-th directional derivative there.  That condition is the *pinned parameter*
  fibre condition of the family

      `pinFam p n f : (Fin (p+1) → ℝ) → (Fin n → ℝ) → ℝ`,
      `pinFam p n f (l, x) y = f l (x, y)`,

  i.e. of `f` with the distinguished `x` moved into the parameter list: for `u = Fin.snoc l x`
  one has `pinFam p n f u = slice (f l) x` (`pinFam_snoc`).

  `pinDg p n f M` is the graph of that pinned fibre derivative, spelled in the ambient
  coordinates `(l, x, y, s)` of `ℝ^{p+(n+1)+1}` — the layout in which `Work.WilkG4c.surrogateComp`
  consumes its input set `A`.  It is the set whose `Ω`-membership is the crux input of
  `surrogateSliceFamGraph_mem`; the bridge to the `AlDgListSlice` spelling of
  `SlicedDerivDefs` is the dimension-cast identification
  `pinDg p n f M = ((p+1)+n+1 = p+(n+1)+1) ▸ AlDgListSlice (p+1) n (pinFam p n f) M`.
-/
import Mathlib
import Submission.Work.WilG4c.SlicedSurrogateDefs
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The pinned family -/

/-- `pinFam p n f` is `f` with the distinguished coordinate `x` moved into the parameter list:
`pinFam p n f (l, x) y = f l (x, y)`.  Hence `pinFam p n f (Fin.snoc l x) = slice (f l) x`
(`pinFam_snoc`), which is the function whose fibre smoothness `surrogateSlice` tests. -/
def pinFam (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    (Fin (p + 1) → ℝ) → (Fin n → ℝ) → ℝ :=
  fun u y => f (fun i : Fin p => u (Fin.castSucc i)) (Fin.cons (u (Fin.last p)) y)

@[simp] theorem pinFam_apply (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (u : Fin (p + 1) → ℝ) (y : Fin n → ℝ) :
    pinFam p n f u y = f (fun i : Fin p => u (Fin.castSucc i)) (Fin.cons (u (Fin.last p)) y) :=
  rfl

/-- The pinned family at the parameter `(l, x)` is exactly the slice of `f l` at `x`. -/
theorem pinFam_snoc (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ) :
    pinFam p n f (Fin.snoc l x) = slice (f l) x := by
  funext y
  simp [pinFam, slice, pt]

/-! ## 2. The pinned (slice) derivative graph -/

/-- The parameters `l` of a point of `ℝ^{p + (n+1)}` (its first `p` coordinates). -/
def pinL (p n : ℕ) (z : Fin (p + (n + 1)) → ℝ) : Fin p → ℝ := fun i => z (Fin.castAdd (n + 1) i)

/-- The distinguished coordinate `x` of a point of `ℝ^{p + (n+1)}` (its `p`-th coordinate). -/
def pinX (p n : ℕ) (z : Fin (p + (n + 1)) → ℝ) : ℝ := z (Fin.natAdd p (0 : Fin (n + 1)))

/-- The cube coordinates `y` of a point of `ℝ^{p + (n+1)}` (its last `n` coordinates). -/
def pinY (p n : ℕ) (z : Fin (p + (n + 1)) → ℝ) : Fin n → ℝ := fun j => z (Fin.natAdd p j.succ)

/-- **The pinned slice derivative graph.**  `pinDg p n f M` is the set of points
`(l, x, y, s) ∈ ℝ^{p+(n+1)+1}` such that the slice `y' ↦ f l (x, y')` is `C^{|M|}` at `y`, and
`s` is its `|M|`-th directional derivative in the directions `M`. -/
def pinDg (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (M : List (Fin n)) :
    Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | ContDiffAt ℝ M.length
          (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z))) (pinY p n (Fin.init z)) ∧
       z (Fin.last (p + (n + 1))) =
         iteratedFDeriv ℝ M.length
           (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z))) (pinY p n (Fin.init z))
           (fun j => Pi.single (M.get j) 1)}

@[simp] theorem mem_pinDg {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {M : List (Fin n)} {z : Fin (p + (n + 1) + 1) → ℝ} :
    z ∈ pinDg p n f M ↔
      ContDiffAt ℝ M.length
        (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z))) (pinY p n (Fin.init z)) ∧
      z (Fin.last (p + (n + 1))) =
        iteratedFDeriv ℝ M.length
          (slice (f (pinL p n (Fin.init z))) (pinX p n (Fin.init z))) (pinY p n (Fin.init z))
          (fun j => Pi.single (M.get j) 1) :=
  Iff.rfl

/-- The projection of `pinDg` is the locus of parameters/points at which the slice is `C^{|M|}`:
the `if`-condition of `surrogateSlice`. -/
theorem projLast_pinDg (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (M : List (Fin n)) :
    projLast (pinDg p n f M) =
      {w : Fin (p + (n + 1)) → ℝ |
        ContDiffAt ℝ M.length (slice (f (pinL p n w)) (pinX p n w)) (pinY p n w)} := by
  ext w
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_pinDg, Fin.init_snoc] at ht
    simpa using ht.1
  · intro hw
    exact ⟨iteratedFDeriv ℝ M.length (slice (f (pinL p n w)) (pinX p n w)) (pinY p n w)
      (fun j => Pi.single (M.get j) 1), by
      rw [mem_pinDg, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hw, rfl⟩⟩

/-- Membership of a `snoc`-ed point in `pinDg`, i.e. the graph form of `pinDg`. -/
theorem snoc_mem_pinDg {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {M : List (Fin n)} {w : Fin (p + (n + 1)) → ℝ} {s : ℝ} :
    Fin.snoc w s ∈ pinDg p n f M ↔
      ContDiffAt ℝ M.length (slice (f (pinL p n w)) (pinX p n w)) (pinY p n w) ∧
      s = iteratedFDeriv ℝ M.length (slice (f (pinL p n w)) (pinX p n w)) (pinY p n w)
        (fun j => Pi.single (M.get j) 1) := by
  rw [mem_pinDg, Fin.init_snoc, Fin.snoc_last]

/-! ## 3. The splitting of `xPt l x y` -/

@[simp] theorem pinL_xPt {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    pinL p n (xPt l x y) = l := by
  funext i
  simp [pinL, xPt, Fin.append_left]

@[simp] theorem pinX_xPt {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    pinX p n (xPt l x y) = x := by
  simp [pinX, xPt, Fin.append_right, pt]

@[simp] theorem pinY_xPt {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    pinY p n (xPt l x y) = y := by
  funext j
  simp [pinY, xPt, Fin.append_right, pt]

/-! ## 4. The fibre derivative graph in arbitrary cube dimension

`SlicedDerivDefs` spells the fibre (`l`-pinned) derivative graph only for cube dimension `n + 1`
(`AlDgListSlice p n`).  The surrogate of §5.4 tests smoothness of a *slice*, i.e. of the fibre of
a family with an arbitrary cube dimension (`pinFam` has cube dimension `n`, which may be `0`), so
the graph is needed for every cube dimension `m`.  `SliceDerivGraph p m f L` is that set, and
`sliceDerivGraph_eq_AlDgListSlice` records that on cube dimension `n+1` it *is*
`AlDgListSlice p n`, so the `Ω`-definability input `AlDgListSlice_mem` covers the case `m ≥ 1`. -/

/-- The parameter block of a point of `ℝ^{p+m}` (its first `p` coordinates). -/
def parM (p m : ℕ) (w : Fin (p + m) → ℝ) : Fin p → ℝ := fun i => w (Fin.castAdd m i)

/-- The cube block of a point of `ℝ^{p+m}` (its last `m` coordinates). -/
def cubeM (p m : ℕ) (w : Fin (p + m) → ℝ) : Fin m → ℝ := fun j => w (Fin.natAdd p j)

/-- **The fibre derivative graph in cube dimension `m`.**  `SliceDerivGraph p m f L` is the set
of points `(w, s) ∈ ℝ^{p+m+1}` such that the `l`-pinned member `y ↦ f l y` (with `l` the first `p`
coordinates of `w`) is `C^{|L|}` at the cube point `y` (the last `m` coordinates of `w`), and `s`
is its `|L|`-th directional derivative in the directions `L`. -/
def SliceDerivGraph (p m : ℕ) (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ) (L : List (Fin m)) :
    Set (Fin (p + m + 1) → ℝ) :=
  {z | ContDiffAt ℝ L.length (fun y : Fin m → ℝ => f (parM p m (Fin.init z)) y)
          (cubeM p m (Fin.init z)) ∧
       z (Fin.last (p + m)) =
         iteratedFDeriv ℝ L.length (fun y : Fin m → ℝ => f (parM p m (Fin.init z)) y)
           (cubeM p m (Fin.init z)) (fun j => Pi.single (L.get j) 1)}

/-- Membership in `SliceDerivGraph`, unfolded. -/
theorem mem_SliceDerivGraph {p m : ℕ} {f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ}
    {L : List (Fin m)} {z : Fin (p + m + 1) → ℝ} :
    z ∈ SliceDerivGraph p m f L ↔
      ContDiffAt ℝ L.length (fun y : Fin m → ℝ => f (parM p m (Fin.init z)) y)
        (cubeM p m (Fin.init z)) ∧
      z (Fin.last (p + m)) =
        iteratedFDeriv ℝ L.length (fun y : Fin m → ℝ => f (parM p m (Fin.init z)) y)
          (cubeM p m (Fin.init z)) (fun j => Pi.single (L.get j) 1) :=
  Iff.rfl

/-- On cube dimension `n + 1`, `SliceDerivGraph` is verbatim `AlDgListSlice`: the two definitions
have the same body (`parM p (n+1) = parPt`, `cubeM p (n+1) = cubePt`). -/
theorem sliceDerivGraph_eq_AlDgListSlice (p n : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    SliceDerivGraph p (n + 1) f L = AlDgListSlice p n f L := by
  ext z
  dsimp only [SliceDerivGraph, AlDgListSlice, parM, cubeM, parPt, cubePt]
  exact Iff.rfl

/-- The projection of `SliceDerivGraph` is the `l`-pinned fibre `C^{|L|}`-locus. -/
theorem projLast_SliceDerivGraph (p m : ℕ) (f : (Fin p → ℝ) → (Fin m → ℝ) → ℝ)
    (L : List (Fin m)) :
    projLast (SliceDerivGraph p m f L) =
      {w : Fin (p + m) → ℝ |
        ContDiffAt ℝ L.length (fun y : Fin m → ℝ => f (parM p m w) y) (cubeM p m w)} := by
  ext w
  constructor
  · rintro ⟨t, ht⟩
    rw [mem_SliceDerivGraph, Fin.init_snoc] at ht
    exact ht.1
  · intro hw
    exact ⟨iteratedFDeriv ℝ L.length (fun y : Fin m → ℝ => f (parM p m w) y) (cubeM p m w)
      (fun j => Pi.single (L.get j) 1), by
      rw [mem_SliceDerivGraph, Fin.init_snoc, Fin.snoc_last]
      exact ⟨hw, rfl⟩⟩

/-! ## 5. The padded family and the dummy coordinate

`SliceDerivGraph` / `AlDgListSlice` only come with a *cube* dimension of the form `n + 1 ≥ 1`,
while the pinned family `pinFam p n f` has cube dimension `n`, which may be `0`.  `padFam p n f`
is the pinned family with one *ignored* cube coordinate appended (`padFam p n f u z =
pinFam p n f u (Fin.init z)`), so that it does have cube dimension `n + 1`: the fibre condition
and the fibre derivative of `padFam p n f` at `(u, z)` are those of `pinFam p n f` at
`(u, Fin.init z)`, while the extra coordinate is never read.  `delDummy` deletes that coordinate,
identifying the pinned graph `pinDg p n f M` with the pullback of `AlDgListSlice (p+1) n (padFam …)`
along `delDummy` (`pinDg_eq_coordPre_AlDgListSlice`). -/

/-- `pinFam p n f` with an extra, ignored cube coordinate: `padFam p n f (l,x) (y, ·) = f l (x, y)`. -/
def padFam (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    (Fin (p + 1) → ℝ) → (Fin (n + 1) → ℝ) → ℝ :=
  fun u z => f (fun i : Fin p => u (Fin.castSucc i)) (Fin.cons (u (Fin.last p)) (Fin.init z))

@[simp] theorem padFam_apply (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (u : Fin (p + 1) → ℝ) (z : Fin (n + 1) → ℝ) :
    padFam p n f u z = f (fun i : Fin p => u (Fin.castSucc i))
      (Fin.cons (u (Fin.last p)) (Fin.init z)) := rfl

/-- At the parameter `(l, x)` the padded family is the slice of `f l` at `x`, read through `init`. -/
theorem padFam_snoc (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ) :
    padFam p n f (Fin.snoc l x) = fun z : Fin (n + 1) → ℝ => slice (f l) x (Fin.init z) := by
  funext z
  simp [padFam, slice, pt, Fin.snoc_castSucc, Fin.snoc_last]

/-- The index map deleting the dummy cube coordinate, from the ambient layout
`(l, x, y, dummy, s)` of `padFam` to the layout `(l, x, y, s)` of `pinDg`. -/
def delDummy (p n : ℕ) : Fin ((p + 1) + (n + 1) + 1) → Fin (p + (n + 1) + 1) :=
  fun i => if h : i.val < p + n + 1 then ⟨i.val, by omega⟩ else ⟨p + n + 1, by omega⟩

end Work.WilkG4c
