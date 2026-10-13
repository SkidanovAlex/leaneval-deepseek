/-
  Area G4b: the "bounded `x`-derivative from bounded `y`-derivatives" reduction
  (BNZ Lemma 5.6 / Binyamini–Novikov, *The Yomdin–Gromov algebraic lemma revisited*,
  Lemma 16).

  This file fixes the vocabulary of the area: the `C¹` locus, directional derivatives,
  the derivative graph, the `Λ`-set whose fibres encode unboundedness of `∂₀ f` over a
  fibre, and the exceptional ("bad") set `badSet` of `G4_bdd_dx`.

  Everything else in `Submission/Work/WilG4b` imports this file.
-/
import Submission.Work.Wilkies.CG.Spec
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4b
open WilkiesDesign WilkiesConjecture

/-! ## Directional derivatives and the `C¹` locus -/

/-- The `C¹` locus of `f`: the set of points at which `f` is `C¹`.  (This is open, so it
coincides with the interior appearing in the frozen statements.) -/
def c1Loc {m : ℕ} (f : (Fin m → ℝ) → ℝ) : Set (Fin m → ℝ) :=
  interior {z | ContDiffAt ℝ 1 f z}

/-- The directional derivative of `f` in the direction of the `i`-th coordinate. -/
def dDir {m : ℕ} (f : (Fin m → ℝ) → ℝ) (i : Fin m) (z : Fin m → ℝ) : ℝ :=
  fderiv ℝ f z (Pi.single i 1)

/-- The graph of the directional derivative `∂ᵢ f`, taken over the `C¹` locus. -/
def derivGraph {m : ℕ} (f : (Fin m → ℝ) → ℝ) (i : Fin m) : Set (Fin (m + 1) → ℝ) :=
  {z | Fin.init z ∈ c1Loc f ∧ z (Fin.last m) = dDir f i (Fin.init z)}

/-- The pair `(x, M)` as a point of `ℝ²`. -/
def pair (x M : ℝ) : Fin 2 → ℝ := ![x, M]

@[simp] theorem pair_zero (x M : ℝ) : pair x M 0 = x := rfl
@[simp] theorem pair_one (x M : ℝ) : pair x M 1 = M := rfl

/-! ## The `Λ`-set and the bad set -/

/-- `Λ_f`: the pairs `(x, M)` such that the fibre of `f` over `x` (inside the open cube and
the `C¹` locus) contains a point with `M < |∂₀ f|`.  The fibre of `Λ_f` over `x` is
`(-∞, S(x))` where `S(x)` is the supremum of `|∂₀ f|` over that fibre; in particular the
fibre is unbounded in `M` exactly when `∂₀ f` is unbounded over the fibre. -/
def lamSet {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) : Set (Fin 2 → ℝ) :=
  {z | ∃ y ∈ openCube m, Fin.cons (z 0) y ∈ c1Loc f ∧ z 1 < |dDir f 0 (Fin.cons (z 0) y)|}

/-- The set of `x` at which `∂₀ f` is unbounded on the fibre over `x` (inside the open cube
and the `C¹` locus). -/
def badCore {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) : Set (Fin 1 → ℝ) :=
  {x | ∀ M : ℝ, pair (x 0) M ∈ lamSet f}

/-- The exceptional set of `G4_bdd_dx`: the points of `(0,1) \ s` at which `∂₀ f` is
unbounded on the fibre. -/
def badSet {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (s : Finset ℝ) : Set (Fin 1 → ℝ) :=
  {x | x 0 ∈ Set.Ioo 0 1 ∧ x 0 ∉ (s : Set ℝ) ∧ x ∈ badCore f}

/-- The property of `x` that `G4_bdd_dx` concludes for all `x` outside its exceptional set:
`∂₀ f` is bounded on the fibre over `x`. -/
def GoodX {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (x : ℝ) : Prop :=
  ∃ B : ℝ, ∀ y ∈ openCube m, Fin.cons x y ∈ c1Loc f → |dDir f 0 (Fin.cons x y)| ≤ B

/-- `badSet` is contained in `badCore`, lifted to the reals. -/
theorem badSet_subset_badCore {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (s : Finset ℝ) :
    badSet f s ⊆ badCore f := fun _ hx => hx.2.2

/-! ## The dominance choice set, the graph of `γ`, and the derivative-threshold set -/

/-- The choice set of the reduction at threshold `M`: `C¹` points `(x,y)` of the cube, over
`x ∈ (c,d)`, at which `|∂₀ f|` dominates the `y`-partials by the factor `M`.  This is the
set which the definable-choice lemma is applied to: its `Ω`-format and degree do not depend
on `M` (nor on `c`, `d`, which enter only as coefficients of polynomials). -/
def ESet {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (c d M : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {z | z ∈ c1Loc f ∧ z 0 ∈ Set.Ioo c d ∧ Fin.tail z ∈ openCube n ∧
      ∃ u : ℝ, 0 ≤ u ∧ (∀ j : Fin n, |fderiv ℝ f z (Pi.single j.succ 1)| ≤ u) ∧
        M * (1 + n * u) < |fderiv ℝ f z (Pi.single 0 1)|}

/-- The graph of a choice function `γ`, in the coordinates `(x, y)` of `ℝ^{1+n}`
(matching the output of `G1_choice` with `p = 1`). -/
def gammaGraph {n : ℕ} (γ : (Fin 1 → ℝ) → (Fin n → ℝ)) : Set (Fin (1 + n) → ℝ) :=
  {z | ∀ j : Fin n, z (Fin.natAdd 1 j) = γ (fun _ => z 0) j}

/-- The augmented choice set of the reduction.  A point `v : Fin (n+3) → ℝ` encodes
`x = v 0`, `y = (v 1, …, v n)`, `w = v (n+1)`, `u = v (n+2)`, subject to: `x ∈ (c,d)`;
`y` in the open cube; `(x,y,w)` in the graph of `f`; `u ≥ 0`; the `x`-derivative at `(x,y)`
dominates `M * (1 + n*u)`; and each `y`-partial at `(x,y)` is bounded by `u` in absolute
value.  The definable-choice lemma is applied to this set with parameters `(x, M)`; its
`Ω`-format and degree are independent of `c`, `d`, `M` (and `u` is chosen last, so that the
chosen fibre is a genuine definable function of the parameters). -/
def StarSet {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (c d M : ℝ) : Set (Fin (n + 3) → ℝ) :=
  {v | v 0 ∈ Set.Ioo c d ∧
       (fun i : Fin n => v (Fin.castAdd 2 i.succ)) ∈ openCube n ∧
       Fin.init v ∈ graphOf f ∧
       0 ≤ v (Fin.last (n + 2)) ∧
       (∃ w₀ : ℝ, Fin.snoc (Fin.init (Fin.init v)) w₀ ∈ derivGraph f 0 ∧
          M * (1 + n * v (Fin.last (n + 2))) < |w₀|) ∧
       (∀ j : Fin n, ∃ wj : ℝ, Fin.snoc (Fin.init (Fin.init v)) wj ∈ derivGraph f j.succ ∧
          |wj| ≤ v (Fin.last (n + 2)))}

/-- The `t` at which `G` is `C¹` and its derivative exceeds `K` in absolute value.  (The
`C¹` condition is part of the set because `SharpDeriv` only controls the derivative on that
locus.) -/
def thrSet (G : ℝ → ℝ) (K : ℝ) : Set ℝ := {t | ContDiffAt ℝ 1 G t ∧ K < |deriv G t|}

/-- The `C¹` locus of a function of one real variable. -/
def c1Set (G : ℝ → ℝ) : Set ℝ := {t | ContDiffAt ℝ 1 G t}

lemma lamSet_pair {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (x M : ℝ) :
    pair x M ∈ lamSet f ↔
      ∃ y ∈ openCube m, Fin.cons x y ∈ c1Loc f ∧ M < |dDir f 0 (Fin.cons x y)| := by
  simp only [lamSet, Set.mem_ofPred_eq, pair_zero, pair_one]

lemma badCore_iff {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (x : Fin 1 → ℝ) :
    x ∈ badCore f ↔ ∀ M : ℝ,
      ∃ y ∈ openCube m, Fin.cons (x 0) y ∈ c1Loc f ∧
        M < |dDir f 0 (Fin.cons (x 0) y)| := by
  simp only [badCore, Set.mem_ofPred_eq, lamSet_pair]

/-! ## The elementary reduction

`G4_bdd_dx` follows as soon as we know that `badSet` is finite; this file records that
reduction, so that the whole area is about finiteness of `badSet`. -/

theorem goodX_of_not_badCore {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ} {x : Fin 1 → ℝ}
    (h : x ∉ badCore f) : GoodX f (x 0) := by
  rw [badCore_iff] at h
  push Not at h
  obtain ⟨M, hM⟩ := h
  refine ⟨M, fun y hy hc => ?_⟩
  by_contra hcon
  exact hcon (hM y hy hc)

/-- If the bad set is finite, then `G4_bdd_dx` holds (with the exceptional set `s ∪ badSet`). -/
theorem exists_goodX_of_finite_badSet {m : ℕ} (f : (Fin (m + 1) → ℝ) → ℝ) (s : Finset ℝ)
    (hfin : (badSet f s).Finite) :
    ∃ s' : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s' → GoodX f x := by
  classical
  refine ⟨s ∪ hfin.toFinset.image (fun z : Fin 1 → ℝ => z 0), fun x hx hxs => ?_⟩
  rw [Finset.mem_union, not_or] at hxs
  obtain ⟨hxs, hxbad⟩ := hxs
  refine goodX_of_not_badCore (x := fun _ : Fin 1 => x) ?_
  intro hc
  refine hxbad (Finset.mem_image.mpr ?_)
  exact ⟨fun _ : Fin 1 => x, hfin.mem_toFinset.mpr ⟨hx, by simpa using hxs, hc⟩, rfl⟩

/-! ## The `n = 0` case

For `n = 0` the fibre is a single point, so `∂₀ f` is automatically bounded there. -/

theorem badCore_zero {f : (Fin (0 + 1) → ℝ) → ℝ} : badCore f = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false, badCore_iff, not_forall]
  refine ⟨|dDir f 0 (Fin.cons (x 0) (fun i : Fin 0 => i.elim0))| + 1, ?_⟩
  rintro ⟨y, -, hc, hlt⟩
  have hy : y = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  rw [hy] at hlt
  linarith

end Work.WilG4b
