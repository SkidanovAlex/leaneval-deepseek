import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.cutSetup` — the cell/lift data of the "cut" construction (Pisa 7.38)

Vocabulary of the construction of `exists_desc_plaque_algebra`: the "cell system" (an open
partition of a `μ`-conull subset of `X₃` into small-diameter cells with `μ`-thin boundary,
equipped with a locally `U`-equivariant lift to `SL₃(ℝ)`) and the associated countable family
of generators `gen`.

The construction itself lives in sibling modules; here we only fix names.
-/

open MeasureTheory Topology Filter
open scoped ENNReal Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The singleton `{g}` as a set. -/
abbrev sing (g : SL3) : Set SL3 := {g}

/-- The left `U`-saturation of a set of group elements. -/
def sat (U : Subgroup SL3) (O : Set SL3) : Set SL3 := {h | ∃ u ∈ U, ∃ o ∈ O, u * o = h}

/-- Right translation of a set by a group element. -/
def shift (A : Set SL3) (g : SL3) : Set SL3 := {h | ∃ a ∈ A, a * g = h}

/-- **The cell system of Pisa 7.38.**  A finite family of pairwise disjoint *open* subsets of
`X₃` covering a `μ`-conull set, each of diameter at most `ρ` (measured with the displacement
neighbourhoods `V ρ`), with `μ`-thin boundary, together with a choice of lift `lift i y ∈ SL₃(ℝ)`
of every `y ∈ cell i` which is *locally `U`-equivariant*: for `x, y` in the same cell with
`y = u • x` and `u ∈ U`, the lifts satisfy `lift i y = u * lift i x`. -/
structure CutData (μ : MeasureTheory.Measure X3) (U : Subgroup SL3) (ε : ℝ) where
  /-- number of cells -/
  N : ℕ
  /-- the cells -/
  cell : Fin N → Set X3
  hopen : ∀ i, IsOpen (cell i)
  hdisj : ∀ i j, i ≠ j → Disjoint (cell i) (cell j)
  /-- the exceptional piece (X∖Y); it carries the leftover mass and is one of the pieces of the
  Pisa-7.31 partition, but it is **not** one of the cut cells -/
  bad : Set X3
  hbad_meas : MeasurableSet bad
  /-- The exceptional piece is **open**: this is what makes the "bad-level" constraints of the
  descending σ-algebra open at their points (see `CUT_PLAN3.md`). -/
  hbad_open : IsOpen bad
  hbad_disj : ∀ i, Disjoint (cell i) bad
  /-- The cells and `bad` cover everything outside a null set (the "shell" `∂(⋃ cell)`). -/
  hcover : μ ((⋃ i, cell i) ∪ bad)ᶜ = 0
  /-- the diameter scale -/
  ρ : ℝ
  hρ : 0 < ρ
  /-- a reference lift of each cell -/
  g : Fin N → SL3
  hg_mem : ∀ i, mkX (g i) ∈ cell i
  /-- the pointwise lift -/
  lift : Fin N → X3 → SL3
  lift_mk : ∀ i (y : X3), y ∈ cell i → mkX (lift i y) = y
  lift_bdd : ∀ i (y : X3) (hy : y ∈ cell i), lift i y ∈ shift (V (10 * ρ)) (g i)
  /-- The lift is the **unique** element of the ball `V (10 ρ) · (g i)` mapping to `y`.  This is
  the form in which the injectivity radius of the cell centre enters; see `CUT_PLAN3.md`. -/
  lift_uniq : ∀ i (y : X3) (hy : y ∈ cell i) (w : SL3), mkX w = y →
    w ∈ shift (V (10 * ρ)) (g i) → w = lift i y
  -- Local `U`-equivariance of the lift; `u` must be *small* (see CUT_PLAN.md, correction c5).
  lift_eq : ∀ i (x : X3), x ∈ cell i → (∀ u ∈ U, u • x = x → u = 1) →
    ∀ (y : X3), y ∈ cell i → ∀ u ∈ V (10 * ρ), u ∈ U → y = u • x →
      lift i y = u * lift i x
  /-- the thin-boundary constant -/
  c : ℝ
  hthin : ∀ η : ℝ, 0 < η →
    μ (⋃ i, (fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ (frontier (cell i))))
      ≤ ENNReal.ofReal (c * η)
  hthin_bad : ∀ η : ℝ, 0 < η →
    μ ((fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ (frontier bad)))
      ≤ ENNReal.ofReal (c * η)
  hbad_small : μ bad < ENNReal.ofReal ε


variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3} {ε : ℝ}

/-- **The generators.**  For a countable family `O : ℕ → Set SL3` of open sets and a cell index
`i`, the `(i,m)`-th generator of the cut σ-algebra is the image of the `U`-saturation of `O m`
inside the lift of the cell `i`, intersected with that cell.  *The cell index must be part of the
indexing* — merging the cells into one generator loses the cell and makes the atoms too big (this
was caught by the referees of `atom_gen`).  Its atoms, together with the cell partition, are the
leaf pieces `U • x ∩ cell i`. -/
def genCell (S : CutData μ U ε) (O : ℕ → Set SL3) (i : Fin S.N) (m : ℕ) : Set X3 :=
  mkX '' (sat U (O m) ∩ shift (V (10 * S.ρ)) (S.g i)) ∩ S.cell i

/-- `V ρ` is open. -/
theorem isOpen_V (ρ : ℝ) : IsOpen (V ρ) := by
  have h : V ρ = ⋂ i : Fin 3, ⋂ j : Fin 3,
      {g : SL3 | |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ρ} := by
    ext g; simp [V]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_lt (by fun_prop) continuous_const

/-- `mkX` is an open map. -/
theorem isOpenMap_mkX : IsOpenMap (mkX : SL3 → X3) := QuotientGroup.isOpenMap_coe

/-- The `U`-saturation of an open set is open. -/
theorem isOpen_sat {O : Set SL3} (hO : IsOpen O) : IsOpen (sat U O) := by
  have h : sat U O = ⋃ u ∈ (U : Set SL3), (fun o : SL3 => u * o) '' O := by
    ext g
    simp only [sat, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨u, hu, o, ho, rfl⟩; exact ⟨u, hu, o, ho, rfl⟩
    · rintro ⟨u, hu, o, ho, rfl⟩; exact ⟨u, hu, o, ho, rfl⟩
  rw [h]
  exact isOpen_biUnion fun u _ => (Homeomorph.mulLeft u).isOpenMap O hO

/-- Right translation of an open set is open. -/
theorem isOpen_shift {A : Set SL3} (hA : IsOpen A) (g : SL3) : IsOpen (shift A g) :=
  (Homeomorph.mulRight g).isOpenMap A hA

/-- Each generator of the cut is open (hence Borel). -/
theorem isOpen_genCell (S : CutData μ U ε) (O : ℕ → Set SL3) (hO : ∀ m, IsOpen (O m))
    (i : Fin S.N) (m : ℕ) : IsOpen (genCell S O i m) := by
  refine IsOpen.inter ?_ (S.hopen i)
  exact isOpenMap_mkX (sat U (O m) ∩ shift (V (10 * S.ρ)) (S.g i))
    (IsOpen.inter (isOpen_sat (U := U) (hO m)) (isOpen_shift (isOpen_V (10 * S.ρ)) (S.g i)))

end Work.EKLC6Core
