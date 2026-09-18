import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-!
# The masses of a level of the Cantor tree sum to one

The mass functional `Work.MassTransferenceAlt.Mass` distributes the mass of a node of the
Beresnevich–Velani Cantor tree among its children in proportion to the `f`-volumes
`vf d ρ i = (2 ρ i) ^ d`.  Here we prove that this is mass preserving: for every `n`, the
masses of the balls of level `n` add up to the mass of the root, namely `1`.

The proof has three ingredients, all in this file:

* `massSum_lev_zero` — the base case: by definition the root distributes its mass `1` over
  the balls of level `0` in proportion to their `f`-volumes; the level is non-empty and all
  its `f`-volumes are positive, so the proportional weights sum to `1`;
* `massSum_children` — conservation at a single node: summing the masses of the children of
  a ball `B` of level `n` returns the mass of `B`, because each child contributes
  `vf i / (∑_{children} vf j)` times the mass of its parent;
* `massSum_lev_succ` — the balls of level `n + 1` partition into the (non-empty) families
  of children of the balls of level `n`, so the previous point sums the level `n + 1` mass
  back to the level `n` mass.

`MassSum` is then immediate by induction.
-/

/-- Unfolding of the mass functional on the root level, at a node. -/
lemma mass_zero_eq (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (i : ℕ) :
    Mass d c ρ η T 0 (some i) =
      (if i ∈ T.lev 0 then vf d ρ i / (∑ j ∈ T.lev 0, vf d ρ j) else 0) := rfl

/-- Unfolding of the mass functional at a node of a successor level. -/
lemma mass_succ_eq (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n i : ℕ) :
    Mass d c ρ η T (n+1) (some i) =
      (if i ∈ T.lev (n+1) then
        (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter
          (fun j => T.par (n+1) j = T.par (n+1) i), vf d ρ j))
          * Mass d c ρ η T n (T.par (n+1) i)
        else 0) := rfl

/-- **The base case.**  The masses of the balls of level `0` sum to the mass of the root. -/
lemma massSum_lev_zero (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) :
    ∑ i ∈ T.lev 0, Mass d c ρ η T 0 (some i) = 1 := by
  classical
  -- the local level of the root has `nsubRoot η ≥ 1` sub-levels, all of them non-empty,
  -- and all its balls have positive radius
  have hloc := T.root_loc
  have hne : (T.lev 0).Nonempty := by
    obtain ⟨i, hi, _⟩ :=
      hloc.2.2.2.2.2.2.1 0 (lt_of_lt_of_le Nat.zero_lt_one (nsubRoot_pos η))
    exact ⟨i, hi⟩
  have hpos : ∀ i ∈ T.lev 0, 0 < vf d ρ i := fun i hi => vf_pos (hloc.1 i hi)
  have hSpos : 0 < ∑ j ∈ T.lev 0, vf d ρ j :=
    Finset.sum_pos' (fun i hi => (hpos i hi).le) (hne.imp fun i hi => ⟨hi, hpos i hi⟩)
  -- hence the proportional weights `vf i / ∑ vf j` sum to `1`
  have hsum : ∑ i ∈ T.lev 0, Mass d c ρ η T 0 (some i)
      = ∑ i ∈ T.lev 0, vf d ρ i / (∑ j ∈ T.lev 0, vf d ρ j) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mass_zero_eq, if_pos hi]
  rw [hsum, ← Finset.sum_div]
  exact div_self (ne_of_gt hSpos)

/-- **Conservation of mass at a single node.**  The masses of the children of a ball `B`
of level `n` sum to the mass of `B`. -/
lemma massSum_children (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η)
    (n B : ℕ) (hB : B ∈ T.lev n) :
    ∑ i ∈ (T.lev (n+1)).filter (fun i => T.par (n+1) i = some B),
        Mass d c ρ η T (n+1) (some i) = Mass d c ρ η T n (some B) := by
  classical
  set F : Finset ℕ := (T.lev (n+1)).filter (fun i => T.par (n+1) i = some B) with hF
  have hloc := T.loc n B hB
  have hmemF : ∀ i ∈ F, i ∈ T.lev (n+1) ∧ T.par (n+1) i = some B :=
    fun i hi => Finset.mem_filter.mp (hF ▸ hi)
  -- the children of `B` all have positive `f`-volume
  have hvf : ∀ i ∈ F, 0 < vf d ρ i := by
    intro i hi
    exact vf_pos (hloc.1 i (hF ▸ hi))
  -- and there is at least one of them (the local level has `nsub d (ρ B) ≥ 1` sub-levels)
  have hne : F.Nonempty := by
    obtain ⟨i, hi, _⟩ :=
      hloc.2.2.2.2.2.2.1 0 (lt_of_lt_of_le Nat.zero_lt_one (nsub_pos d (ρ B)))
    exact ⟨i, hF.symm ▸ hi⟩
  have hSpos : 0 < ∑ j ∈ F, vf d ρ j :=
    Finset.sum_pos' (fun i hi => (hvf i hi).le) (hne.imp fun i hi => ⟨hi, hvf i hi⟩)
  -- each child contributes its relative `f`-volume times the mass of its parent
  have hterm : ∀ i ∈ F, Mass d c ρ η T (n+1) (some i)
      = (vf d ρ i / (∑ j ∈ F, vf d ρ j)) * Mass d c ρ η T n (some B) := by
    intro i hi
    obtain ⟨hilev, hpar⟩ := hmemF i hi
    have hfilt : (T.lev (n+1)).filter (fun j => T.par (n+1) j = T.par (n+1) i) = F := by
      rw [hF]
      refine Finset.filter_congr (fun j _ => ?_)
      rw [hpar]
    rw [mass_succ_eq, if_pos hilev, hfilt, hpar]
  calc ∑ i ∈ F, Mass d c ρ η T (n+1) (some i)
      = ∑ i ∈ F, (vf d ρ i / (∑ j ∈ F, vf d ρ j)) * Mass d c ρ η T n (some B) :=
        Finset.sum_congr rfl hterm
    _ = (∑ i ∈ F, vf d ρ i / (∑ j ∈ F, vf d ρ j)) * Mass d c ρ η T n (some B) := by
        rw [← Finset.sum_mul]
    _ = Mass d c ρ η T n (some B) := by
        rw [← Finset.sum_div, div_self (ne_of_gt hSpos), one_mul]

/-- **Conservation of mass from one level to the next.**  The balls of level `n + 1` are
partitioned by their parents, which are balls of level `n`; summing the mass of each family
of children with `massSum_children` gives the sum of the masses of the level `n` balls. -/
lemma massSum_lev_succ (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : TreeData d c ρ η) (n : ℕ) :
    ∑ i ∈ T.lev (n+1), Mass d c ρ η T (n+1) (some i)
      = ∑ B ∈ T.lev n, Mass d c ρ η T n (some B) := by
  classical
  -- a (numerical) parent function; on `T.lev (n+1)` it recovers the parent of `par_mem`
  set g : ℕ → ℕ := fun i => (T.par (n+1) i).getD 0 with hg
  have hgmem : ∀ i ∈ T.lev (n+1), g i ∈ T.lev n := by
    intro i hi
    obtain ⟨B, hB, hpar⟩ := T.par_mem n i hi
    simp only [hg]
    rw [hpar]
    simpa using hB
  -- sum over the fibres of `g`, which are exactly the families of children
  have key := Finset.sum_fiberwise_of_maps_to (s := T.lev (n+1)) (t := T.lev n)
    (g := g) hgmem (fun i => Mass d c ρ η T (n+1) (some i))
  rw [← key]
  refine Finset.sum_congr rfl (fun B hB => ?_)
  have hfilter : (T.lev (n+1)).filter (fun i => g i = B)
      = (T.lev (n+1)).filter (fun i => T.par (n+1) i = some B) := by
    refine Finset.filter_congr (fun i hi => ?_)
    constructor
    · intro h
      obtain ⟨B', hB', hpar⟩ := T.par_mem n i hi
      have h2 : g i = B' := by simp only [hg]; rw [hpar]; rfl
      rw [h] at h2
      rw [hpar, h2]
    · intro h
      simp only [hg]
      rw [h]
      rfl
  rw [hfilter]
  exact massSum_children d c ρ η T n B hB

/-- **The masses of a level sum to one.**  The mass distributed over the nodes of any
level is exactly the mass of the root, namely `1`. -/
lemma MassSum (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (T : Work.MassTransferenceAlt.TreeData d c ρ η)
    (n : ℕ) :
    ∑ i ∈ T.lev n, Work.MassTransferenceAlt.Mass d c ρ η T n (some i) = 1 := by
  induction n with
  | zero => exact massSum_lev_zero d c ρ η T
  | succ n ih => exact (massSum_lev_succ d c ρ η T n).trans ih

end Work.MassTransferenceAlt.Tree
