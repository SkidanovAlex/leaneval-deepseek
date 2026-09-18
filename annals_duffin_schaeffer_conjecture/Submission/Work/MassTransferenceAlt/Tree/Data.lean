/-
# The Cantor tree of the mass transference principle: interface

A `TreeData d c ρ η` packages the output of the inductive Beresnevich–Velani
construction: an infinite nested tree of balls of the family `(c i, ρ i)`, whose
levels `lev n` carry the local-level properties `IsLoc` (properties (P1)–(P5)),
together with the mass functional `Mass` on the nodes.

The construction (existence of a `TreeData`) is proved in
`Submission.Work.MassTransferenceAlt.Tree.Local` / `Tree.Exists`;
the estimates about it are in `Tree.Mass` and `Tree.Estimate`.

* `nsubRoot η` is the number of sub-levels of the local level of the root `[0,1]`.
* `vf d ρ i = (2 ρ i) ^ d` is the `f`-volume of the `i`-th ball.
* `Mass T n (some i)` is the mass of the node `i` at level `n`, `Mass T 0 none = 1`
  is the mass of the root; the recursive definition distributes the mass of a
  node among its children in proportion to their `f`-volumes.
* `Anc T N n i` is the ancestor of the ball `i` of level `N` at level `n`.
-/
import Submission.Work.MassTransferenceAlt.Tree.Defs

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Work.MassTransferenceAlt

/-- The number of sub-levels of the local level of the root. -/
noncomputable def nsubRoot (η : ℝ) : ℕ := Nat.floor (64 * η) + 1

lemma nsubRoot_pos (η : ℝ) : 1 ≤ nsubRoot η := Nat.le_add_left 1 _

lemma lt_nsubRoot {η : ℝ} : 64 * η < (nsubRoot η : ℝ) := by
  rw [nsubRoot]; push_cast; exact Nat.lt_floor_add_one _

/-- The `f`-volume of the `i`-th ball. -/
noncomputable def vf (d : ℝ) (ρ : ℕ → ℝ) (i : ℕ) : ℝ := (2 * ρ i) ^ d

lemma vf_pos {d : ℝ} {ρ : ℕ → ℝ} {i : ℕ} (h : 0 < ρ i) : 0 < vf d ρ i :=
  Real.rpow_pos_of_pos (by linarith) _

/-- **The data produced by the Cantor construction.** -/
structure TreeData (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) : Type where
  /-- the balls of level `n` -/
  lev : ℕ → Finset ℕ
  /-- the indices used at levels `≤ n` -/
  used : ℕ → Finset ℕ
  /-- the parent of a ball of level `n+1` -/
  par : ℕ → ℕ → Option ℕ
  /-- the sub-level index of a ball of level `n` -/
  sub : ℕ → ℕ → ℕ
  /-- the root local level: the children of `[0,1] = Iv (1/2) (1/2)`, with
  `nsubRoot η` sub-levels -/
  root_loc : IsLoc d c ρ (1/2) (1/2) (lev 0) (sub 0) (nsubRoot η)
  /-- the total `f`-volume of the first level is at least `η` -/
  root_mass : η ≤ ∑ i ∈ lev 0, vf d ρ i
  /-- every ball of the construction is admissible -/
  good : ∀ n i, i ∈ lev n → Good d c ρ i
  /-- parents of a ball of level `n+1` are balls of level `n` -/
  par_mem : ∀ n i, i ∈ lev (n+1) → ∃ B ∈ lev n, par (n+1) i = some B
  /-- the local level of any ball of level `n` satisfies `IsLoc` with `nsub d (ρ B)`
  sub-levels -/
  loc : ∀ n (B : ℕ), B ∈ lev n →
      IsLoc d c ρ (c B) (ρ B) ((lev (n+1)).filter (fun i => par (n+1) i = some B))
        (sub (n+1)) (nsub d (ρ B))
  /-- the used index sets grow exactly by the level sets -/
  used_zero : used 0 = lev 0
  used_succ : ∀ n, used (n+1) = used n ∪ lev (n+1)
  /-- freshly used indices -/
  fresh : ∀ n i, i ∈ lev (n+1) → i ∉ used n

/-- **The mass functional.**  `Mass T n (some i)` is the mass of the node `i` of level
`n`; `Mass T 0 none = 1` is the mass of the root.  The mass of a node is distributed
among its children in proportion to their `f`-volumes. -/
noncomputable def Mass (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    ℕ → Option ℕ → ℝ
  | 0 => fun x => match x with
      | none => 1
      | some i => if i ∈ T.lev 0 then vf d ρ i / (∑ j ∈ T.lev 0, vf d ρ j) else 0
  | (n+1) => fun x => match x with
      | none => 0
      | some i =>
          if i ∈ T.lev (n+1) then
            (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter
              (fun j => T.par (n+1) j = T.par (n+1) i), vf d ρ j))
              * Mass d c ρ η T n (T.par (n+1) i)
          else 0

/-- **The ancestor map.**  For `1 ≤ n ≤ N`, `Anc d c ρ η T N n i` is the (unique)
ancestor in `lev n` of the ball `i` of `lev N`.  The value for `n = 0` or `n > N` is
junk (`none`). -/
noncomputable def Anc (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _ => none
  | (N+1), n, i =>
      if n = 0 then none else if n = N + 1 then some i
      else (T.par (N+1) i).bind (fun j => Anc d c ρ η T N n j)

@[simp] lemma anc_self (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N i : ℕ) :
    Anc d c ρ η T (N+1) (N+1) i = some i := by
  rw [Anc]; simp

@[simp] lemma anc_zero (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (N i : ℕ) :
    Anc d c ρ η T N 0 i = none := by
  cases N with
  | zero => rfl
  | succ N => rw [Anc]; simp

lemma anc_step (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) {N n i : ℕ}
    (hn0 : 0 < n) (hnN : n ≤ N) :
    Anc d c ρ η T (N+1) n i = (T.par (N+1) i).bind (fun j => Anc d c ρ η T N n j) := by
  rw [Anc]
  have h1 : n ≠ 0 := by omega
  have h2 : n ≠ N + 1 := by omega
  simp [h1, h2]


/-- The interval `Iv x rA` meets the ball of index `i`; this is the decidable form (a
linear inequality in the centres and radii) of `(Iv x rA ∩ Iv (c i) (ρ i)).Nonempty`,
used to index `Finset.filter`. -/
@[reducible] def hits (c ρ : ℕ → ℝ) (x rA : ℝ) (i : ℕ) : Prop := |x - c i| ≤ rA + ρ i

lemma hits_iff {c ρ : ℕ → ℝ} {x rA : ℝ} (hrA : 0 ≤ rA) {i : ℕ} (hi : 0 ≤ ρ i) :
    (Iv x rA ∩ Iv (c i) (ρ i)).Nonempty ↔ hits c ρ x rA i := by
  rw [← Set.not_disjoint_iff_nonempty_inter, disjoint_Iv_iff hrA hi, not_lt, hits]

lemma hits_of_mem {c ρ : ℕ → ℝ} {x rA : ℝ} {i : ℕ} {z : ℝ} (hz1 : z ∈ Iv x rA)
    (hz2 : z ∈ Iv (c i) (ρ i)) : hits c ρ x rA i := by
  rw [hits]
  rw [mem_Iv] at hz1 hz2
  calc |x - c i| = |(x - z) + (z - c i)| := by ring_nf
    _ ≤ |x - z| + |z - c i| := abs_add_le _ _
    _ ≤ rA + ρ i := by linarith [abs_sub_comm x z]

/-- The union of the intervals of a level. -/
def levSet {d : ℝ} {c ρ : ℕ → ℝ} {η : ℝ} (T : TreeData d c ρ η) (n : ℕ) : Set ℝ :=
  ⋃ i ∈ (T.lev n : Set ℕ), Iv (c i) (ρ i)

/-- The Cantor set: the intersection of the level sets. -/
def cantor {d : ℝ} {c ρ : ℕ → ℝ} {η : ℝ} (T : TreeData d c ρ η) : Set ℝ := ⋂ n, levSet T n

lemma cantor_subset_levSet {d : ℝ} {c ρ : ℕ → ℝ} {η : ℝ} (T : TreeData d c ρ η) (n : ℕ) :
    cantor T ⊆ levSet T n := Set.iInter_subset _ n

end Work.MassTransferenceAlt
