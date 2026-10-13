/-
  WilG4c — vocabulary for the `CurveFamAlpha` lemma (BNZ §5.4, the `γ`-choice for a general
  multiindex, with the threshold alternative).

  `CurveFamAlpha` is the general-`(j,M)` version of `CurveFam` (`CurveFamDefs.lean`): instead of
  a near-maximiser of `∂₀ f` it selects a definable `γ` for the directional derivative of
  order `j + |M|` in the directions `midx p n j M`, subject to the *threshold alternative*
  `threshAlt` (either `|∂^{α}| ≥ 2E`, or `±∂^{α} ≤ -2E`, or a near-maximiser).

  The selection set is the *exact* set appearing in the hypothesis of `CurveFamAlpha`:

      `AlZset p n f L E = {w : y-part ∈ openCube n} ∩ AlLoc ∩ (AlAlt1 ∪ AlAlt2 ∪ AlViolᶜ)`

  where (with `N = p + (n+1)`, `w ∈ ℝ^N`)

  * `AlLoc p n f k`  — the interior of the `C^k`-locus of `famFunHat f` (BNZ "at which `f` is
    `C^k`"), a subset of `ℝ^N`;
  * `AlDgList p n f L` — the graph of `w ↦ iterDir L (famFunHat f) w` over `AlLoc`, a subset of
    `ℝ^{N+1}`; it is the set that `SOMin.SharpDeriv` exhibits as an `Ω`-set (`AlSDList` is the
    `iteratedFDeriv`-spelling, i.e. *verbatim* `SharpDeriv`'s set);
  * `AlAlt1` / `AlAlt2` — the first two disjuncts of `threshAlt`: `∂^{α} ≥ 2E`, `∂^{α} ≤ -2E`;
  * `AlViol` — the set of `w` for which some `y' ∈ openCube n` with `zPt w y'` in the `C^k`-locus
    has `2|∂^{α}(w)| < |∂^{α}(zPt w y')|`; its complement is the near-maximiser disjunct.  It is
    built exactly like `badSet` of `CurveFam`, in the ambient `(w | y' | s | s')`.

  `AlZset` is `Ω`-definable, so `ChoiceHyp` yields a definable selector `γ`; the characterization
  `mem_AlZset_iff` then identifies the conclusion of `CurveFamAlpha` with the nonemptiness of the
  fibre of `AlZset`, which is what the hypothesis of the lemma supplies.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.Hyps
import Submission.Work.WilG4c.CurveFamDefs
import Submission.Work.WilG4c.CurveFam.mem_badSet_iff
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilG5

/-! ## 1. The `C^k`-locus and the derivative graph of a list of directions -/

/-- `AlLoc p n f k`: the interior of the `C^k`-locus of the family member `f`, read as a set in
`ℝ^{p + (n+1)}` (parameters first, then the cube point). -/
def AlLoc (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ) :
    Set (Fin (p + (n + 1)) → ℝ) :=
  interior {x | ContDiffAt ℝ k (famFunHat f) x}

/-- `AlDgList p n f L`: the graph of the iterated directional derivative `iterDir L (famFunHat f)`
over the interior of the `C^{|L|}`-locus, as a subset of `ℝ^{p + (n+1) + 1}`. -/
def AlDgList (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) : Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | Fin.init z ∈ AlLoc p n f L.length ∧
    z (Fin.last (p + (n + 1))) = iterDir L (famFunHat f) (Fin.init z)}

/-- `AlSDList p n f L`: the same set with the derivative evaluated as
`iteratedFDeriv ℝ |L| (famFunHat f) · (fun i => Pi.single (L.get i) 1)` — i.e. *verbatim* the
set that `SOMin.SharpDeriv` exhibits as an `Ω`-set. -/
def AlSDList (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) : Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | Fin.init z ∈ AlLoc p n f L.length ∧
    z (Fin.last (p + (n + 1))) =
      iteratedFDeriv ℝ L.length (famFunHat f) (Fin.init z) (fun i => Pi.single (L.get i) 1)}

/-! ## 2. The two threshold alternatives -/

/-- The first disjunct of `threshAlt`, as a subset of `ℝ`: `{u | 2E ≤ u 0}`. -/
def AlGeE (E : ℝ) : Set (Fin 1 → ℝ) := {u | 2 * E ≤ u 0}

/-- The second disjunct of `threshAlt`, as a subset of `ℝ`: `{u | u 0 ≤ -2E}`. -/
def AlLeE (E : ℝ) : Set (Fin 1 → ℝ) := {u | u 0 ≤ -(2 * E)}

/-- The coordinate `s` inside `Fin (N+1)`: the last one. -/
def AlSIdx (N : ℕ) : Fin 1 → Fin (N + 1) := fun _ => Fin.last N

/-- The set of `w` at which the stored derivative value `s` satisfies `2E ≤ s`. -/
def AlAlt1 (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) (E : ℝ) : Set (Fin (p + (n + 1)) → ℝ) :=
  projN 1 (AlDgList p n f L ∩ coordPre (AlSIdx (p + (n + 1))) (AlGeE E))

/-- The set of `w` at which the stored derivative value `s` satisfies `s ≤ -2E`. -/
def AlAlt2 (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) (E : ℝ) : Set (Fin (p + (n + 1)) → ℝ) :=
  projN 1 (AlDgList p n f L ∩ coordPre (AlSIdx (p + (n + 1))) (AlLeE E))

/-! ## 3. The violation set of the near-maximality disjunct -/

/-- The ambient `(w | y' | s | s')` version of the violation set, built exactly like `badSet1`
but with the order-`|L|` derivative graph `AlDgList` in place of `DgSet`. -/
def AlViol1 (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) : Set (Fin (p + (n + 1) + n + 2) → ℝ) :=
  coordPre (iwIdx p n) (AlDgList p n f L) ∩ coordPre (izIdx p n) (AlDgList p n f L) ∩
    coordPre (icIdx p n) cmpSet ∩ coordPre (cubeIdx p n) (openCube n)

/-- The set of `w` which are *beaten* on the fibre: some `y' ∈ openCube n` with `zPt w y'` in the
`C^{|L|}`-locus has `2|∂^{α}(w)| < |∂^{α}(zPt w y')|`. -/
def AlViol (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) : Set (Fin (p + (n + 1)) → ℝ) :=
  projN (n + 2) (AlViol1 p n f L)

/-! ## 4. The selection set -/

/-- `AlZset p n f L E`: the selection set of `CurveFamAlpha` — the `w = (l,x,y)` with
`y ∈ openCube n`, `w` in the interior of the `C^{|L|}`-locus, and one of the three disjuncts of
`threshAlt` holding for the directional derivative `iterDir L (famFunHat f)`. -/
def AlZset (p n : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (L : List (Fin (p + (n + 1)))) (E : ℝ) : Set (Fin (p + (n + 1)) → ℝ) :=
  coordPre (yIdx p n) (openCube n) ∩ AlLoc p n f L.length ∩
    (AlAlt1 p n f L E ∪ AlAlt2 p n f L E ∪ (AlViol p n f L)ᶜ)

/-! ## 5. Explicit (deliberately loose) format/degree bounds

`β` is the degree assigned to `AlDgList p n f L` by `SharpDeriv` (namely
`MvPolynomial.eval ![D, |L|] b1`), and `a1` its format. -/

/-- A format bound for `AlViol` (the analogue of `Fbad`). -/
def AlFviol (p n a1 : ℕ) : ℕ := a1 + 600 * (p + n + 2) + 5000

/-- A degree bound for `AlViol` (the analogue of `Dbad`). -/
def AlDviol (p n β : ℕ) : ℕ := 2 * β + 600 * (p + n + 2) + 5000

/-- A format bound for the threshold sets `AlAlt1`, `AlAlt2`. -/
def AlFalt (p n a1 : ℕ) : ℕ := max a1 (20 + 64 * ((p + (n + 1) + 1) + 1) + 64) + 2

/-- A degree bound for the threshold sets `AlAlt1`, `AlAlt2`. -/
def AlDalt (p n β : ℕ) : ℕ := β + (4 + 32 * ((p + (n + 1) + 1) + 1) + 32)

/-- A format bound for the union `AlAlt1 ∪ AlAlt2 ∪ AlViolᶜ`. -/
def AlFu (p n a1 : ℕ) : ℕ := max (AlFalt p n a1) (max (AlFalt p n a1) (AlFviol p n a1 + 1))

/-- A degree bound for the union `AlAlt1 ∪ AlAlt2 ∪ AlViolᶜ`. -/
def AlDu (p n β : ℕ) : ℕ := AlDalt p n β + AlDalt p n β + (AlDviol p n β + 1)

/-- A format bound for `AlZset`. -/
def AlFzs (p n a1 : ℕ) : ℕ :=
  max ((4 * n + 24) + 64 * ((p + (n + 1)) + n) + 64) (max (a1 + 1) (AlFu p n a1)) + 2

/-- A degree bound for `AlZset`. -/
def AlDzs (p n β : ℕ) : ℕ :=
  AlDu p n β + β + ((16 * n + 16) + 32 * ((p + (n + 1)) + n) + 32)

/-! ## 6. Trivial membership lemmas -/

@[simp] theorem mem_AlLoc {p n k : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlLoc p n f k ↔ w ∈ interior {x | ContDiffAt ℝ k (famFunHat f) x} := Iff.rfl

theorem mem_AlDgList {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {z : Fin (p + (n + 1) + 1) → ℝ} :
    z ∈ AlDgList p n f L ↔ Fin.init z ∈ AlLoc p n f L.length ∧
      z (Fin.last (p + (n + 1))) = iterDir L (famFunHat f) (Fin.init z) := Iff.rfl

theorem mem_AlSDList {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {z : Fin (p + (n + 1) + 1) → ℝ} :
    z ∈ AlSDList p n f L ↔ Fin.init z ∈ AlLoc p n f L.length ∧
      z (Fin.last (p + (n + 1))) =
        iteratedFDeriv ℝ L.length (famFunHat f) (Fin.init z)
          (fun i => Pi.single (L.get i) 1) := Iff.rfl

theorem mem_AlAlt1 {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {E : ℝ} {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlAlt1 p n f L E ↔ ∃ v : Fin 1 → ℝ,
      Fin.append w v ∈ AlDgList p n f L ∩ coordPre (AlSIdx (p + (n + 1))) (AlGeE E) :=
  Iff.rfl

theorem mem_AlAlt2 {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {E : ℝ} {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlAlt2 p n f L E ↔ ∃ v : Fin 1 → ℝ,
      Fin.append w v ∈ AlDgList p n f L ∩ coordPre (AlSIdx (p + (n + 1))) (AlLeE E) :=
  Iff.rfl

theorem mem_AlZset {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {E : ℝ} {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlZset p n f L E ↔ (fun j : Fin n => w (yIdx p n j)) ∈ openCube n ∧
      w ∈ AlLoc p n f L.length ∧
      (w ∈ AlAlt1 p n f L E ∨ w ∈ AlAlt2 p n f L E ∨ w ∈ (AlViol p n f L)ᶜ) := by
  simp only [AlZset, Set.mem_inter_iff, coordPre, Set.mem_ofPred_eq, Set.mem_union,
    Set.mem_compl_iff]
  tauto

/-! ## 6b. Elementary `Fin`/`projN` facts -/

/-- `Fin.append w v` for `v : Fin 1 → ℝ` is `Fin.snoc w (v 0)`. -/
theorem append_one {N : ℕ} (w : Fin N → ℝ) (v : Fin 1 → ℝ) :
    Fin.append w v = Fin.snoc w (v 0) := by
  funext i
  refine Fin.lastCases (motive := fun i =>
    Fin.append w v i = (Fin.snoc w (v 0) : Fin (N + 1) → ℝ) i) ?_ ?_ i
  · rw [Fin.snoc_last,
      show Fin.last N = Fin.natAdd N (0 : Fin 1) from Fin.ext rfl, Fin.append_right]
  · intro j
    rw [Fin.snoc_castSucc,
      show Fin.castSucc j = Fin.castAdd 1 j from Fin.ext rfl, Fin.append_left]

/-- `projN 1` in `snoc` form. -/
theorem projN_one {N : ℕ} (A : Set (Fin (N + 1) → ℝ)) :
    projN 1 A = {w : Fin N → ℝ | ∃ s : ℝ, Fin.snoc w s ∈ A} := by
  ext w
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v 0, by rwa [append_one] at hv⟩
  · rintro ⟨s, hs⟩
    exact ⟨fun _ => s, by rwa [append_one]⟩

/-- The membership of `Fin.snoc w s` in the derivative graph. -/
theorem snoc_mem_AlDgList {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {w : Fin (p + (n + 1)) → ℝ} {s : ℝ} :
    Fin.snoc w s ∈ AlDgList p n f L ↔ w ∈ AlLoc p n f L.length ∧
      s = iterDir L (famFunHat f) w := by
  rw [mem_AlDgList, Fin.init_snoc, Fin.snoc_last]

/-- Membership in the first threshold set. -/
theorem mem_AlAlt1_iff {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {E : ℝ} {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlAlt1 p n f L E ↔ w ∈ AlLoc p n f L.length ∧
      2 * E ≤ iterDir L (famFunHat f) w := by
  rw [AlAlt1, projN_one]
  constructor
  · rintro ⟨s, hs⟩
    rw [Set.mem_inter_iff, coordPre, Set.mem_ofPred_eq] at hs
    obtain ⟨hdg, hge⟩ := hs
    rw [snoc_mem_AlDgList] at hdg
    obtain ⟨hl, hsv⟩ := hdg
    have hge' : 2 * E ≤ s := by
      have h := hge
      simp only [AlGeE, Set.mem_ofPred_eq, Function.comp_apply, AlSIdx, Fin.snoc_last] at h
      exact h
    exact ⟨hl, by rw [← hsv]; exact hge'⟩
  · rintro ⟨hl, hge⟩
    refine ⟨iterDir L (famFunHat f) w, ?_⟩
    rw [Set.mem_inter_iff, coordPre, Set.mem_ofPred_eq, snoc_mem_AlDgList]
    refine ⟨⟨hl, rfl⟩, ?_⟩
    simpa only [AlGeE, Set.mem_ofPred_eq, Function.comp_apply, AlSIdx, Fin.snoc_last] using hge

/-- Membership in the second threshold set. -/
theorem mem_AlAlt2_iff {p n : ℕ} {f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ}
    {L : List (Fin (p + (n + 1)))} {E : ℝ} {w : Fin (p + (n + 1)) → ℝ} :
    w ∈ AlAlt2 p n f L E ↔ w ∈ AlLoc p n f L.length ∧
      iterDir L (famFunHat f) w ≤ -(2 * E) := by
  rw [AlAlt2, projN_one]
  constructor
  · rintro ⟨s, hs⟩
    rw [Set.mem_inter_iff, coordPre, Set.mem_ofPred_eq] at hs
    obtain ⟨hdg, hle⟩ := hs
    rw [snoc_mem_AlDgList] at hdg
    obtain ⟨hl, hsv⟩ := hdg
    have hle' : s ≤ -(2 * E) := by
      have h := hle
      simp only [AlLeE, Set.mem_ofPred_eq, Function.comp_apply, AlSIdx, Fin.snoc_last] at h
      exact h
    exact ⟨hl, by rw [← hsv]; exact hle'⟩
  · rintro ⟨hl, hle⟩
    refine ⟨iterDir L (famFunHat f) w, ?_⟩
    rw [Set.mem_inter_iff, coordPre, Set.mem_ofPred_eq, snoc_mem_AlDgList]
    refine ⟨⟨hl, rfl⟩, ?_⟩
    simpa only [AlLeE, Set.mem_ofPred_eq, Function.comp_apply, AlSIdx, Fin.snoc_last] using hle

/-- The threefold union as a `Fin 3`-indexed union (the form `SOMin.union` produces). -/
theorem iUnion_fin_three {α : Type*} (A B C : Set α) :
    Set.iUnion (fun i : Fin 3 => ![A, B, C] i) = A ∪ B ∪ C := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩

/-- The threefold intersection as a `Fin 3`-indexed intersection. -/
theorem iInter_fin_three {α : Type*} (A B C : Set α) :
    Set.iInter (fun i : Fin 3 => ![A, B, C] i) = A ∩ B ∩ C := by
  ext z
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

end Work.WilkG4c
