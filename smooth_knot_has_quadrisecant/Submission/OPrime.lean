import Mathlib
import ChallengeDeps
import Submission.QuadrisecantChord
import Submission.SecantSpace
import Submission.TrisecantLocus
import Submission.TrisecantStructure
import Submission.SecantDisk

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology unitInterval

/-!
# Layer A1 — the class-level set `O'` (topologically non-trivial trisecants)

Kuperberg (§"Topological non-triviality"): *Let `O'` be the subset of `O`
consisting of topologically non-trivial trisecants and quadrisecants which
are non-trivial at the middle secant.*  With the data-level vocabulary of
`SecantDisk.lean` (D2: `TrisecantTrivial` — a trisecant chord with middle is
trivial when one of its endpoint-to-middle sub-secants is a trivial secant;
`QuadrisecantMiddleSecantTrivial` — a quadrisecant is trivial at the middle
secant when the chord between its two middles is trivial), this module glues
`O'` to the existing class/attached-data vocabulary of `TrisecantLocus` /
`TrisecantStructure`:

1. **`NontrivialTrisecantData r`** — the attached data `(p, m)` (ordered
   chord `p` with strict middle `m`) whose trisecant is *topologically
   non-trivial*: `¬ TrisecantTrivial r p.1.1 p.1.2 m`.
2. **`ClassNontrivialTrisecant r c`** — the secant class `c` carries a
   topologically non-trivial trisecant: some representative `p` of the class
   and strict middle `m` with `¬ TrisecantTrivial …`.  Representative
   independence holds (`NontrivialData_rep`, via the two-element fibre
   `mobiusCover_fiber` and the D1/D2 endpoint swap), so the class-level
   notion is well-defined and equals the projection of the attached data
   (`ClassNontrivialTrisecant_mobiusCover`,
   `nontrivialTrisecantData_image_eq`).
3. **`ClassNontrivialMiddleSecant r c`** — the class carries a quadrisecant
   structure (two distinct strict middles `z w`) whose middle secant
   `(z,w)` is topologically non-trivial (`¬ QuadrisecantMiddleSecantTrivial
   r z w`).  Under `QuadrisecantFree` this clause is empty
   (`not_ClassNontrivialMiddleSecant_of_quadrisecantFree`).
4. **`OPrime r : Set OpenMobius`** — the union of the two clauses,
   Kuperberg's `O'`; membership API (`mem_OPrime_iff`, and
   `mem_OPrime_iff_of_quadrisecantFree` reducing it to the trisecant
   clause) and the glue `OPrime_subset_trisecantSet` (`O' ⊆ O`, each clause
   implies `HasMiddleOnClass`).

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- The **attached trisecant data kept by `O'`**: an ordered chord `d.1`
(two distinct parameters) together with a strict middle point `d.2` whose
trisecant is topologically *non-trivial* (`¬ TrisecantTrivial` — neither
endpoint-to-middle sub-secant is a trivial secant). -/
def NontrivialTrisecantData (r : ℝ → Space) : Set (OrderedPairs × AddCircle period) :=
  {d | IsMiddleOnChord r d.1.1.1 d.1.1.2 d.2 ∧
    ¬ TrisecantTrivial r d.1.1.1 d.1.1.2 d.2}

/-- Membership in `NontrivialTrisecantData`, unfolded. -/
lemma mem_NontrivialTrisecantData_iff (r : ℝ → Space)
    (d : OrderedPairs × AddCircle period) :
    d ∈ NontrivialTrisecantData r ↔
      IsMiddleOnChord r d.1.1.1 d.1.1.2 d.2 ∧ ¬ TrisecantTrivial r d.1.1.1 d.1.1.2 d.2 := by
  simp [NontrivialTrisecantData]

/-- A secant class `c` **carries a topologically non-trivial trisecant**:
some ordered representative `p` of the class has a strict middle `m` whose
trisecant is non-trivial. -/
def ClassNontrivialTrisecant (r : ℝ → Space) (c : OpenMobius) : Prop :=
  ∃ p : OrderedPairs, mobiusCover p = c ∧
    ∃ m : AddCircle period,
      IsMiddleOnChord r p.1.1 p.1.2 m ∧ ¬ TrisecantTrivial r p.1.1 p.1.2 m

/-- **Representative independence of the non-trivial-trisecant data**: for
two ordered representatives of the same class, strict-middleness AND
non-triviality of the trisecant are equivalent (the two representatives are
`p` or `swapOrdered p`, and the D1/D2 endpoint swaps are equivalences). -/
lemma NontrivialData_rep {r : ℝ → Space} (p q : OrderedPairs)
    (hpq : mobiusCover p = mobiusCover q) (m : AddCircle period) :
    (IsMiddleOnChord r p.1.1 p.1.2 m ∧ ¬ TrisecantTrivial r p.1.1 p.1.2 m) ↔
      (IsMiddleOnChord r q.1.1 q.1.2 m ∧ ¬ TrisecantTrivial r q.1.1 q.1.2 m) := by
  have hfib := mobiusCover_fiber p
  have hq : q ∈ ({p, swapOrdered p} : Set OrderedPairs) := by
    rw [← hfib]
    exact hpq.symm
  simp at hq
  rcases hq with rfl | hq
  · rfl
  · rw [hq]
    constructor
    · rintro ⟨hm, hnt⟩
      constructor
      · simpa [swapOrdered] using (IsMiddleOnChord_swap r p m).mpr hm
      · intro ht
        apply hnt
        exact (TrisecantTrivial_swap_endpoints r p.1.1 p.1.2 m).mpr (by simpa [swapOrdered] using ht)
    · rintro ⟨hm, hnt⟩
      constructor
      · simpa [swapOrdered] using (IsMiddleOnChord_swap r p m).mp hm
      · intro ht
        apply hnt
        simpa [swapOrdered] using (TrisecantTrivial_swap_endpoints r p.1.1 p.1.2 m).mp ht

/-- Membership of `ClassNontrivialTrisecant` at the class of an ordered pair
is exactly the data property at that pair (with some middle). -/
lemma ClassNontrivialTrisecant_mobiusCover {r : ℝ → Space} (p : OrderedPairs) :
    ClassNontrivialTrisecant r (mobiusCover p) ↔
      ∃ m : AddCircle period,
        IsMiddleOnChord r p.1.1 p.1.2 m ∧ ¬ TrisecantTrivial r p.1.1 p.1.2 m := by
  constructor
  · rintro ⟨q, hq, m, hm, hnt⟩
    exact ⟨m, (NontrivialData_rep p q hq.symm m).mpr ⟨hm, hnt⟩⟩
  · rintro ⟨m, hm, hnt⟩
    exact ⟨p, rfl, m, hm, hnt⟩

/-- The projection of the attached non-trivial data onto the band is exactly
the set of classes carrying a non-trivial trisecant. -/
lemma nontrivialTrisecantData_image_eq {r : ℝ → Space} :
    (fun d : OrderedPairs × AddCircle period => mobiusCover d.1) '' NontrivialTrisecantData r =
      {c : OpenMobius | ClassNontrivialTrisecant r c} := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (ClassNontrivialTrisecant_mobiusCover d.1).2 ⟨d.2, (mem_NontrivialTrisecantData_iff r d).mp hd⟩
  · intro hc
    rcases hc with ⟨p, hp, m, hm, hnt⟩
    refine ⟨(p, m), ?_, hp⟩
    exact (mem_NontrivialTrisecantData_iff r (p, m)).2 ⟨hm, hnt⟩

/-- A class carrying a non-trivial trisecant is a trisecant class (glue with
`HasMiddleOnClass` / `O`). -/
lemma ClassNontrivialTrisecant_imp_HasMiddleOnClass {r : ℝ → Space} (c : OpenMobius) :
    ClassNontrivialTrisecant r c → HasMiddleOnClass r c := by
  rintro ⟨p, hp, m, hm, hnt⟩
  exact ⟨m, p, hp, hm⟩

/-- A secant class `c` carries a **quadrisecant structure whose middle secant
is topologically non-trivial**: two distinct strict middles `z w` of its
chord with `¬ QuadrisecantMiddleSecantTrivial r z w`. -/
def ClassNontrivialMiddleSecant (r : ℝ → Space) (c : OpenMobius) : Prop :=
  ∃ p : OrderedPairs, mobiusCover p = c ∧
    ∃ z w : AddCircle period, z ≠ w ∧
      IsMiddleOnChord r p.1.1 p.1.2 z ∧ IsMiddleOnChord r p.1.1 p.1.2 w ∧
      ¬ QuadrisecantMiddleSecantTrivial r z w

/-- A class with a non-trivial middle secant is a trisecant class. -/
lemma ClassNontrivialMiddleSecant_imp_HasMiddleOnClass {r : ℝ → Space} (c : OpenMobius) :
    ClassNontrivialMiddleSecant r c → HasMiddleOnClass r c := by
  rintro ⟨p, hp, z, w, hzw, hz, hw, hnt⟩
  exact ⟨z, p, hp, hz⟩

/-- **Kuperberg's `O'`**: the subset of `O` consisting of topologically
non-trivial trisecants and of quadrisecants which are non-trivial at the
middle secant (a class belongs when it carries one of the two structures). -/
def OPrime (r : ℝ → Space) : Set OpenMobius :=
  {c : OpenMobius | ClassNontrivialTrisecant r c ∨ ClassNontrivialMiddleSecant r c}

/-- Membership in `O'`, unfolded. -/
lemma mem_OPrime_iff (r : ℝ → Space) (c : OpenMobius) :
    c ∈ OPrime r ↔ ClassNontrivialTrisecant r c ∨ ClassNontrivialMiddleSecant r c := by
  simp [OPrime]

/-- `O'` is a subset of `O` (`trisecantSet`): every non-trivial structure is
in particular a trisecant. -/
lemma OPrime_subset_trisecantSet {r : ℝ → Space} :
    OPrime r ⊆ trisecantSet r := by
  intro c hc
  rcases (mem_OPrime_iff r c).mp hc with htr | hquad
  · exact ClassNontrivialTrisecant_imp_HasMiddleOnClass c htr
  · exact ClassNontrivialMiddleSecant_imp_HasMiddleOnClass c hquad

/-- Under the no-quadrisecant hypothesis the middle-secant clause of `O'` is
empty: a class carrying two distinct middles would be a quadrisecant. -/
lemma not_ClassNontrivialMiddleSecant_of_quadrisecantFree {r : ℝ → Space}
    (h : IsSmoothKnot r) (hqf : QuadrisecantFree r) (c : OpenMobius) :
    ¬ ClassNontrivialMiddleSecant r c := by
  intro hc
  rcases hc with ⟨p, hp, z, w, hzw, hz, hw, hnt⟩
  have htwo : HasTwoMiddlePointsOnClass r c := ⟨z, w, hzw, p, hp, hz, hw⟩
  exact hqf ((quadrisecantChord_iff_exists_class h).2 ⟨c, htwo⟩)

/-- Under the no-quadrisecant hypothesis, membership in `O'` is exactly the
non-trivial-trisecant clause. -/
lemma mem_OPrime_iff_of_quadrisecantFree {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (c : OpenMobius) :
    c ∈ OPrime r ↔ ClassNontrivialTrisecant r c := by
  rw [mem_OPrime_iff]
  constructor
  · rintro (htr | hquad)
    · exact htr
    · exact False.elim (not_ClassNontrivialMiddleSecant_of_quadrisecantFree h hqf c hquad)
  · intro htr
    exact Or.inl htr

end LeanEval.KnotTheory.Quadrisecant
