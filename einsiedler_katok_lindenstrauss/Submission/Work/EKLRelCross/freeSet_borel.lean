import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# `Work.EKLRelCross.freeSet_borel` — the set of points with free `U`-orbit is Borel

For a closed subgroup `U ≤ SL₃(ℝ)` we show that

  `{x : X₃ | ∀ u ∈ U, u • x = x → u = 1}`

is a Borel subset of `X₃ = SL₃(ℝ)/SL₃(ℤ)`.

**Proof.**  The complement is `⋃ m ⋃ n π(S m n)`, where

  `S m n = {(u,x) ∈ (U ∩ {‖·‖ ≤ m}) × X₃ | ‖u - 1‖ ≥ 1/(n+1), u • x = x}`

is the trace on the compact set `K m = U ∩ {‖·‖ ≤ m}` of a closed subset of `SL₃(ℝ) × X₃`.
Since `K m` is compact, the projection `K m × X₃ → X₃` is a closed map
(`isClosedMap_snd_of_compactSpace`), so every `π(S m n)` is closed, and a countable union of
closed sets is Borel.

That every non-free point is captured is elementary: if `u ≠ 1` there is an entry `u i j` with
`u i j ≠ 1 i j`, hence `1/(n+1) ≤ |u i j - 1 i j|` for some `n` (Archimedes), and, the entries of
`u` being finitely many reals, `|u i j| ≤ m` for some `m`.  (No local-freeness input is needed for
*this* statement — `Work.EKLComp.locallyFree_compacta` is the companion fact used elsewhere.)

Here `‖·‖` is the entrywise maximum `‖u‖ = max |u i j|`, i.e. the `V δ`-condition of the frozen
contract, stated with entrywise absolute values.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## The pieces of the non-free set -/

/-- Entrywise bound: `u` lies in the closed entrywise box of radius `m`. -/
def fsbBox (m : ℝ) (u : SL3) : Prop :=
  ∀ i j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ m

/-- `u` is entrywise at distance `≥ 1/(n+1)` from the identity. -/
def fsbFar (n : ℕ) (u : SL3) : Prop :=
  ∃ i j, 1 / ((n : ℝ) + 1) ≤
    |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|

/-- The `(m,n)`-th piece of the non-free set: the set of points fixed by some `u ∈ U` which lies in
the entrywise box of radius `m` and at distance `≥ 1/(n+1)` from the identity. -/
def fsbBadSet (U : Subgroup SL3) (m n : ℕ) : Set X3 :=
  {x : X3 | ∃ u ∈ U, fsbBox (m : ℝ) u ∧ fsbFar n u ∧ u • x = x}

/-! ## The pieces are closed -/

/-- `{u | fsbFar n u}` is closed, being a finite union of closed entrywise conditions. -/
lemma fsb_isClosed_far (n : ℕ) : IsClosed {u : SL3 | fsbFar n u} := by
  rw [show {u : SL3 | fsbFar n u} = ⋃ i : Fin 3, ⋃ j : Fin 3,
      {u : SL3 | 1 / ((n : ℝ) + 1) ≤
        |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|} from by
    ext u; simp only [fsbFar, Set.mem_ofPred_eq, Set.mem_iUnion]]
  refine isClosed_iUnion_of_finite (fun i => isClosed_iUnion_of_finite (fun j => ?_))
  exact isClosed_le continuous_const (by fun_prop)

/-- The intersection of the entrywise box with the closed subgroup `U` is compact. -/
lemma fsb_isCompact_box (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) (m : ℝ) :
    IsCompact ({u : SL3 | fsbBox m u} ∩ (U : Set SL3)) := by
  have hbox : IsCompact {u : SL3 | fsbBox m u} := by
    rw [show {u : SL3 | fsbBox m u} = {u : SL3 | ∀ i j,
        -m ≤ (u : Matrix (Fin 3) (Fin 3) ℝ) i j ∧ (u : Matrix (Fin 3) (Fin 3) ℝ) i j ≤ m} from by
      ext u
      simp only [fsbBox, Set.mem_ofPred_eq]
      constructor
      · intro h i j; exact abs_le.mp (h i j)
      · intro h i j; exact abs_le.mpr (h i j)]
    exact Work.EKLProd.sl3EntryBox_compact (fun _ _ => -m) (fun _ _ => m)
  exact hbox.inter_right hUcl

/-- Each `fsbBadSet U m n` is closed: it is the image, under the projection along the compact
factor `U ∩ {‖·‖ ≤ m}`, of a closed subset of `SL₃(ℝ) × X₃`. -/
lemma fsb_isClosed_badSet (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3)) (m n : ℕ) :
    IsClosed (fsbBadSet U m n) := by
  haveI : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI : T2Space X3 := inferInstance
  set K : Set SL3 := {u : SL3 | fsbBox (m : ℝ) u} ∩ (U : Set SL3) with hKdef
  have hKc : IsCompact K := fsb_isCompact_box U hUcl (m : ℝ)
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set T : Set (K × X3) :=
    {p : K × X3 | fsbFar n (p.1 : SL3)} ∩ {p : K × X3 | ((p.1 : SL3) ∈ U)} ∩
      {p : K × X3 | (p.1 : SL3) • p.2 = p.2} with hTdef
  have h1 : IsClosed {p : K × X3 | fsbFar n (p.1 : SL3)} :=
    (fsb_isClosed_far n).preimage (by fun_prop)
  have h2 : IsClosed {p : K × X3 | ((p.1 : SL3) ∈ U)} := hUcl.preimage (by fun_prop)
  have h3 : IsClosed {p : K × X3 | (p.1 : SL3) • p.2 = p.2} :=
    isClosed_eq (by fun_prop) continuous_snd
  have hT : IsClosed T := by rw [hTdef]; exact (h1.inter h2).inter h3
  have himg : IsClosed (Prod.snd '' T) :=
    isClosedMap_snd_of_compactSpace (X := K) (Y := X3) T hT
  have heq : fsbBadSet U m n = Prod.snd '' T := by
    ext x
    constructor
    · rintro ⟨u, huU, hubox, hfar, hfix⟩
      exact ⟨((⟨u, ⟨hubox, huU⟩⟩ : K), x), ⟨⟨hfar, huU⟩, hfix⟩, rfl⟩
    · rintro ⟨p, hp, hpx⟩
      rw [← hpx]
      exact ⟨(p.1 : SL3), hp.1.2, (p.1 : K).2.1, hp.1.1, hp.2⟩
  rw [heq]; exact himg

/-- The non-free set is the countable union of the closed pieces `fsbBadSet U m n`. -/
lemma fsb_nonfree_eq_iUnion (U : Subgroup SL3) :
    {x : X3 | ∃ u ∈ U, u ≠ 1 ∧ u • x = x} =
      ⋃ m : ℕ, ⋃ n : ℕ, fsbBadSet U m n := by
  ext x
  constructor
  · rintro ⟨u, huU, hne, hfix⟩
    -- a natural bound `m` on all entries of `u`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, fsbBox (m : ℝ) u := by
      refine ⟨Finset.univ.sup
        (fun p : Fin 3 × Fin 3 => ⌈|(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|⌉₊), fun i j => ?_⟩
      have h1 : ⌈|(u : Matrix (Fin 3) (Fin 3) ℝ) i j|⌉₊ ≤ Finset.univ.sup
          (fun p : Fin 3 × Fin 3 => ⌈|(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|⌉₊) :=
        Finset.le_sup (s := Finset.univ)
          (f := fun p : Fin 3 × Fin 3 => ⌈|(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|⌉₊)
          (Finset.mem_univ (i, j))
      have h2 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
          (⌈|(u : Matrix (Fin 3) (Fin 3) ℝ) i j|⌉₊ : ℝ) := Nat.le_ceil _
      exact le_trans h2 (by exact_mod_cast h1)
    -- an `n` witnessing that `u` differs from `1` in some entry
    obtain ⟨n, hn⟩ : ∃ n : ℕ, fsbFar n u := by
      have h1 : (u : Matrix (Fin 3) (Fin 3) ℝ) ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
        intro h; exact hne (Subtype.ext h)
      obtain ⟨i, j, hij⟩ : ∃ i j,
          (u : Matrix (Fin 3) (Fin 3) ℝ) i j ≠ (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        by_contra h
        push Not at h
        exact h1 (funext fun i => funext fun j => h i j)
      have hpos : 0 < |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_pos.mpr (sub_ne_zero.mpr hij)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact ⟨n, i, j, le_of_lt hn⟩
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨n, u, huU, hm, hn, hfix⟩⟩
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨m, hx⟩ := hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨n, hx⟩ := hx
    obtain ⟨u, huU, hubox, hfar, hfix⟩ := hx
    refine ⟨u, huU, ?_, hfix⟩
    rintro rfl
    obtain ⟨i, j, hle⟩ := hfar
    have h0 : |((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| = 0 := by simp
    rw [h0] at hle
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-! ## The main result -/

/-- The set of points of `X₃ = SL₃(ℝ)/SL₃(ℤ)` whose `U`-orbit is free is Borel, for a closed subgroup `U ≤ SL₃(ℝ)`. Proof route: the complement is `⋃ n ⋃ m π(S n m)` where `S n m = {(u,x) | u ∈ U, ‖u‖ ≤ m, ‖u - 1‖ ≥ 1/n, u • x = x}` is closed in the compact-fibre product `(U ∩ {‖·‖ ≤ m}) × X₃`; projecting along the compact factor of a closed set gives a closed set, and every non-free point is captured because the stabiliser of every point is discrete at `1` (`Work.EKLComp.locallyFree_compacta`) so `u ≠ 1` implies `‖u - 1‖ ≥ 1/n` for some `n` and `‖u‖ ≤ m` for some `m`. Here `‖·‖` is any fixed matrix norm, e.g. the maximum of the absolute values of the matrix entries (the `V δ`-condition is stated with entrywise absolute values). -/
theorem freeSet_borel {U : Subgroup Work.EKLContract.SL3} (hUcl : IsClosed (U : Set Work.EKLContract.SL3)) :
    MeasurableSet {x : Work.EKLContract.X3 | ∀ u ∈ U, u • x = x → u = 1} := by
  have hset : {x : X3 | ∀ u ∈ U, u • x = x → u = 1} =
      (⋃ m : ℕ, ⋃ n : ℕ, fsbBadSet U m n)ᶜ := by
    rw [← fsb_nonfree_eq_iUnion U]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    constructor
    · rintro h ⟨u, huU, hne, hfix⟩; exact hne (h u huU hfix)
    · rintro h u huU hfix; by_contra hne; exact h ⟨u, huU, hne, hfix⟩
  rw [hset]
  exact (MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun n =>
    (fsb_isClosed_badSet U hUcl m n).measurableSet).compl

end Work.EKLRelCross
