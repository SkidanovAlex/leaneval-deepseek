/-
  WilG4a — vocabulary for the lemma `Work.WilG4a.f1affine1_of_signConst`.

  The target is BNZ Corollary 5.5 (`n = 1`): an `ε`-cover of the *domain* `Λ × I` by affine
  charts `x = α l + β l · t` whose graphs are `Ω`-definable, along which every composite
  `t ↦ F i l (α l + β l · t)` is `C^r` with all derivatives of order `≤ r` bounded by `1`.

  The construction that the workspace uses (`Submission/Work/WilG4a/lipschitz_charts.lean`)
  is the one recorded here: cut the strip `{z | z(last) ∈ I}` into `Ω`-definable cells each
  of which is either

  * *good*: on its fibres every slice `x ↦ F i l x` is `C^{r+1}` with derivatives up to
    order `r+1` of constant sign, and the fibre is a point or an interval, or
  * *degenerate*: all fibres are subsingletons.

  The dichotomy is what makes the bad loci harmless: a cell on which some slice fails to be
  regular has degenerate fibres (this is the content of the one-variable theory), so its
  points are covered, within `ε`, by the neighbouring good cells' charts.

  The charts are built from the fibre end points (`Aend`/`Bend`) and the Whitney cover of
  `I` (`G3_affine_cover`); the derivative bound is `affine_reparam_bound`.
-/
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-- The strip `{z : z (Fin.last p) ∈ I}`: points of `ℝ^{p+1}` whose variable lies in
`I = (0,1)`. -/
def strip (p : ℕ) : Set (Fin (p + 1) → ℝ) := {z | z (Fin.last p) ∈ I}

@[simp] theorem mem_strip {p : ℕ} (z : Fin (p + 1) → ℝ) :
    z ∈ strip p ↔ z (Fin.last p) ∈ I := Iff.rfl

theorem strip_mem_iff_snoc {p : ℕ} (l : Fin p → ℝ) (x : ℝ) :
    Fin.snoc l x ∈ strip p ↔ x ∈ I := by
  simp [strip]

/-- `SameSignOn j g s` holds when the `j`-th iterated derivative of `g` on `s` is everywhere
`≥ 0`, or everywhere `≤ 0`. -/
def SameSignOn (j : ℕ) (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ x ∈ s, 0 ≤ iteratedDeriv j g x) ∨ (∀ x ∈ s, iteratedDeriv j g x ≤ 0)

/-- **Good cell.**  A cell `κ ⊆ ℝ^{p+1}` on which, for every parameter `l`, the fibres
`{x | (l,x) ∈ κ}` are points or open intervals inside `I`, and for each family member `i`
the slice `x ↦ F i l x` is `C^{r+1}` on the fibre with constant-signed derivatives of order
`≤ r+1` there. -/
def GoodCell_w {p : ℕ} (k r : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
    (κ : Set (Fin (p + 1) → ℝ)) : Prop :=
  κ ⊆ strip p ∧
  (∀ l : Fin p → ℝ, (fibre κ l).Subsingleton ∨
      ∃ a b : ℝ, fibre κ l = Set.Ioo a b) ∧
  (∀ (i : Fin k) (l : Fin p → ℝ),
      ContDiffOn ℝ (r + 1) (fun x : ℝ => F i l x) (fibre κ l) ∧
      ∀ j ≤ r + 1, SameSignOn j (fun x : ℝ => F i l x) (fibre κ l))

/-- **Degenerate cell**: all fibres are subsingletons. -/
def DegCell {p : ℕ} (κ : Set (Fin (p + 1) → ℝ)) : Prop :=
  ∀ l : Fin p → ℝ, (fibre κ l).Subsingleton

/-- **`Λ`-uniform good cell.**  `GoodCellOn` is `GoodCell_w` with the fibre required to be a
non-degenerate interval for every parameter of `Λ` (not merely a point or an interval).  This is
the hypothesis under which the affine chart of `goodCell_affine_charts` is defined everywhere on
`Λ`. -/
def GoodCellOn {p : ℕ} (k r : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (Λ : Set (Fin p → ℝ))
    (κ : Set (Fin (p + 1) → ℝ)) : Prop :=
  κ ⊆ strip p ∧
  (∀ l ∈ Λ, ∃ a b : ℝ, a < b ∧ fibre κ l = Set.Ioo a b) ∧
  (∀ (i : Fin k) (l : Fin p → ℝ),
      ContDiffOn ℝ (r + 1) (fun x : ℝ => F i l x) (fibre κ l) ∧
      ∀ j ≤ r + 1, SameSignOn j (fun x : ℝ => F i l x) (fibre κ l))

/-- The cell decomposition with `Λ`-uniform good cells. -/
def CellDecompOn (S : SOMin) (p : ℕ) : Prop :=
  ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ),
    ∀ (D r k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
      ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc ∧
        ∃ (κ : Fin m → Set (Fin (p + 1) → ℝ)),
          (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1)) ∧
          (∀ σ, GoodCellOn k r F Λ (κ σ) ∨ DegCell (κ σ)) ∧
          (∀ l ∈ Λ, ∀ x ∈ I, ∃ σ, Fin.snoc l x ∈ κ σ)

/-- The cell decomposition consumed by the assembly of `f1affine1_of_signConst`: a finite
`Ω`-definable family of cells covering the strip points over `Λ`, each good or degenerate. -/
def CellDecomp (S : SOMin) (p : ℕ) : Prop :=
  ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ),
    ∀ (D r k : ℕ) (Λ : Set (Fin p → ℝ))
      (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
      ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc ∧
        ∃ (κ : Fin m → Set (Fin (p + 1) → ℝ)),
          (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1)) ∧
          (∀ σ, GoodCell_w k r F (κ σ) ∨ DegCell (κ σ)) ∧
          (∀ l ∈ Λ, ∀ x ∈ I, ∃ σ, Fin.snoc l x ∈ κ σ)

end Work.WilG4a
