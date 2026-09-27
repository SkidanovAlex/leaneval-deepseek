import Mathlib
import Submission.Work.Noncompact.CompressionTube.SpineDefs
import Submission.Work.Noncompact.CompressionTube.hop_base
import Submission.Work.Noncompact.CompressionTube.collar_family
import Submission.Work.Noncompact.CompressionTube.exists_level_arc_of_collar_shell

/-!
# The state and the level invariant of the collar (gate) architecture

This file fixes the *interface* of the collar architecture for the spine recursion
(`exists_collar_family` for the collars `L`, `U`), namely

* `LSt B` -- the data of one level: the start points `q`, the arcs `γ` and the *exit times* `τ`
  (the parameter at which the arc leaves the collar `L m`);
* `LInv K L U lev m st` -- the level-`m` invariant: for every strand `b` with `lev b ≤ m`, the arc
  `γ b` runs from `q b` through the collar `L m` (up to `τ b`), leaves it, ends in the shell
  `Shell K (m+1)` inside `U m`, stays in `int (K (m+2)) \ K m`, avoids the base points, the level-`m`
  arcs of different strands are disjoint, etc.;
* `LStep K L lev m st st'` -- the *cross-level* conditions: the new start points extend the old
  arcs, the new arcs avoid the old collar `L m` and the old *spikes* `γ b '' Ioc (τ b) 1`;
* `spineData_of_seq` -- the extraction: a sequence of levels satisfying `LInv` and `LStep` yields
  `SpineData`;
* `spineData_of_base_step` -- the assembly: `SpineData` follows from a level-`0` datum and a step
  producing the level-`(m+1)` datum from the level-`m` one.

The two remaining hypotheses of `spineData_of_base_step` (`base` and `step`) are exactly what the
collar routing produces; they are stated in `collar_level.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **The level of a base point** with respect to the exhaustion `K`: the index `i` with
`b ∉ K i` and `b ∈ K (i+1)`. -/
noncomputable def levK {M : Type*} [TopologicalSpace M] {B : Set M} (K : ℕ → Set M)
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M)) (b : B) : ℕ :=
  kLevel K (exists_mem_of_iUnion_eq_univ hKuniv) (b : M)

theorem levK_notMem {M : Type*} [TopologicalSpace M] {K : ℕ → Set M} {B : Set M}
    (hK0 : K 0 = ∅) (hKuniv : (⋃ i, K i) = (Set.univ : Set M)) (b : B) :
    (b : M) ∉ K (levK K hKuniv b) :=
  kLevel_notMem (exists_mem_of_iUnion_eq_univ hKuniv) hK0

theorem levK_mem_succ {M : Type*} [TopologicalSpace M] {K : ℕ → Set M} {B : Set M}
    (hK0 : K 0 = ∅) (hKuniv : (⋃ i, K i) = (Set.univ : Set M)) (b : B) :
    (b : M) ∈ K (levK K hKuniv b + 1) :=
  kLevel_mem (exists_mem_of_iUnion_eq_univ hKuniv) hK0

/-- **The data of one level**: the start points `q`, the arcs `γ` and the exit times `τ`.  The
functions are total on `B`; on the strands which are not active at the level in question the values
are irrelevant (junk). -/
structure LSt {M : Type*} (B : Set M) where
  /-- The start points of the level. -/
  q : B → M
  /-- The arcs of the level. -/
  γ : B → ℝ → M
  /-- The exit times from the level's collar. -/
  τ : B → ℝ

/-- **The level-`m` invariant.**  Everything is required only for the strands active at level `m`,
i.e. with `lev b ≤ m`. -/
structure LInv {M : Type*} [TopologicalSpace M] (K : ℕ → Set M) (L U : ℕ → Set M) {B : Set M}
    (lev : B → ℕ) (m : ℕ) (st : LSt B) : Prop where
  /-- The arcs are continuous. -/
  arc_cont : ∀ b : B, lev b ≤ m → Continuous (st.γ b)
  /-- The arcs are injective on `Icc 0 1`. -/
  arc_inj : ∀ b : B, lev b ≤ m → Set.InjOn (st.γ b) (Set.Icc (0:ℝ) 1)
  /-- The arcs start at the start points. -/
  arc_zero : ∀ b : B, lev b ≤ m → st.γ b 0 = st.q b
  /-- The exit time lies strictly inside `(0,1)`. -/
  tau_mem : ∀ b : B, lev b ≤ m → st.τ b ∈ Set.Ioo (0:ℝ) 1
  /-- The inside piece lies in the collar. -/
  inside_L : ∀ b : B, lev b ≤ m → ∀ u, u ∈ Set.Icc (0:ℝ) (st.τ b) → st.γ b u ∈ L m
  /-- The arc leaves the collar at the exit time. -/
  outside_notL : ∀ b : B, lev b ≤ m → ∀ u, u ∈ Set.Ioc (st.τ b) 1 → st.γ b u ∉ L m
  /-- The outside piece lies in the collar set `U m`. -/
  outside_U : ∀ b : B, lev b ≤ m → ∀ u, u ∈ Set.Ioc (st.τ b) 1 → st.γ b u ∈ U m
  /-- The tip lies in the next shell. -/
  tip_shell : ∀ b : B, lev b ≤ m → st.γ b 1 ∈ interior (K (m+2)) \ K (m+1)
  /-- The whole arc lies in `interior (K (m+2)) \ K m`. -/
  arc_sub : ∀ b : B, lev b ≤ m → ∀ u, u ∈ Set.Icc (0:ℝ) 1 →
    st.γ b u ∈ interior (K (m+2)) \ K m
  /-- The arc avoids every base point other than its own. -/
  arc_notB : ∀ b b' : B, lev b ≤ m → b' ≠ b → ∀ u, u ∈ Set.Icc (0:ℝ) 1 →
    st.γ b u ≠ (b' : M)
  /-- The start point lies in the shell of its own level. -/
  q_mem : ∀ b : B, lev b ≤ m → st.q b ∈ K (m+1) \ K m
  /-- The start points of the strands with a strictly smaller level lie in the interior shell. -/
  q_int : ∀ b : B, lev b ≤ m → lev b < m → st.q b ∈ interior (K (m+1)) \ K m
  /-- A strand active exactly at this level starts at its own base point. -/
  q_eq : ∀ b : B, lev b ≤ m → lev b = m → st.q b = (b : M)
  /-- The arcs of different strands at the same level are disjoint. -/
  arc_disj : ∀ b b' : B, lev b ≤ m → lev b' ≤ m → b ≠ b' →
    Disjoint (st.γ b '' Set.Icc (0:ℝ) 1) (st.γ b' '' Set.Icc (0:ℝ) 1)

/-- **The cross-level conditions** between the level-`m` datum `st` and the level-`(m+1)` datum
`st'`. -/
structure LStep {M : Type*} [TopologicalSpace M] (K : ℕ → Set M) (L : ℕ → Set M) {B : Set M}
    (lev : B → ℕ) (m : ℕ) (st st' : LSt B) : Prop where
  /-- The new start points extend the old arcs. -/
  compat : ∀ b : B, lev b ≤ m → st'.q b = st.γ b 1
  /-- The new arcs avoid the old collar. -/
  hout : ∀ b : B, lev b ≤ m + 1 → ∀ u, u ∈ Set.Icc (0:ℝ) 1 → st'.γ b u ∉ L m
  /-- The new arcs avoid the old spikes. -/
  hspike : ∀ b b' : B, lev b ≤ m → lev b' ≤ m + 1 → b ≠ b' → ∀ u, u ∈ Set.Icc (0:ℝ) 1 →
    st'.γ b' u ∉ st.γ b '' Set.Ioc (st.τ b) 1

/-- **The extraction.**  A sequence of levels whose data satisfies the level invariant and the
cross-level conditions yields `SpineData`. -/
theorem spineData_of_seq {M : Type*} [TopologicalSpace M] {K : ℕ → Set M} {B : Set M}
    {L U : ℕ → Set M} (hK0 : K 0 = ∅)
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M)) (S : ℕ → LSt B)
    (hInv : ∀ m, LInv K L U (levK K hKuniv) m (S m))
    (hStep : ∀ m, LStep K L (levK K hKuniv) m (S m) (S (m+1))) :
    SpineData K B (fun b : B => levK K hKuniv b) (fun b i => (S i).q b)
      (fun b i => (S i).γ b) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b; exact levK_notMem hK0 hKuniv b
  · intro b; exact levK_mem_succ hK0 hKuniv b
  · intro b i hi
    exact (hInv i).q_int b (le_of_lt hi) hi
  · intro b
    exact (hInv (levK K hKuniv b)).q_eq b le_rfl rfl
  · intro b i hi; exact (hInv i).arc_cont b hi
  · intro b i hi; exact (hInv i).arc_inj b hi
  · intro b i hi
    exact ⟨(hInv i).arc_zero b hi, ((hStep i).compat b hi).symm⟩
  · intro b i hi t ht
    exact ((hInv i).arc_sub b hi t ht).1
  · intro b i hi
    rw [Set.disjoint_left]
    rintro x ⟨t, ht, rfl⟩ hxK
    exact ((hInv i).arc_sub b hi t ht).2 hxK
  · intro b b' i hi hi' hne
    exact (hInv i).arc_disj b b' hi hi' hne
  · intro b b' i hi hi' hne
    rw [Set.disjoint_left]
    rintro x ⟨hx1, hx2⟩ hx3
    obtain ⟨t, ht, rfl⟩ := hx1
    obtain ⟨t', ht', ht'eq⟩ := hx3
    -- the new arc avoids the old collar
    have hnotL : (S i).γ b t ∉ L i := by
      rw [← ht'eq]
      exact (hStep i).hout b' (by omega) t' ht'
    have hnotspike : (S i).γ b t ∉ (S i).γ b '' Set.Ioc ((S i).τ b) 1 := by
      rw [← ht'eq]
      exact (hStep i).hspike b b' hi (by omega) hne t' ht'
    by_cases hle : t ≤ (S i).τ b
    · exact hnotL ((hInv i).inside_L b hi t ⟨ht.1, hle⟩)
    · exact hnotspike ⟨t, ⟨lt_of_not_ge hle, ht.2⟩, rfl⟩
  · intro b b' i hi hne hmem
    obtain ⟨t, ht, ht'⟩ := hmem
    exact (hInv i).arc_notB b b' hi (fun h => hne h.symm) t ht ht'

/-- **The assembly.**  `SpineData` follows from a level-`0` datum satisfying the invariant and a
step producing, from any level-`m` datum satisfying the invariant, a level-`(m+1)` datum satisfying
the invariant and the cross-level conditions. -/
theorem spineData_of_base_step {M : Type*} [TopologicalSpace M] {K : ℕ → Set M} {B : Set M}
    {L U : ℕ → Set M} (hK0 : K 0 = ∅)
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (base : ∃ st : LSt B, LInv K L U (levK K hKuniv) 0 st)
    (step : ∀ (m : ℕ) (st : LSt B), LInv K L U (levK K hKuniv) m st →
      ∃ st' : LSt B, LInv K L U (levK K hKuniv) (m+1) st' ∧
        LStep K L (levK K hKuniv) m st st') :
    ∃ (lev : B → ℕ) (q : B → ℕ → M) (γ : B → ℕ → ℝ → M),
      SpineData K B lev q γ := by
  classical
  obtain ⟨st0, hst0⟩ := base
  let hrec : ∀ m : ℕ, {st : LSt B // LInv K L U (levK K hKuniv) m st} := fun m =>
    Nat.rec (motive := fun m => {st : LSt B // LInv K L U (levK K hKuniv) m st})
      ⟨st0, hst0⟩
      (fun m ih => ⟨(step m ih.1 ih.2).choose, (step m ih.1 ih.2).choose_spec.1⟩) m
  let S : ℕ → LSt B := fun m => (hrec m).1
  have hS : ∀ m, LInv K L U (levK K hKuniv) m (S m) := fun m => (hrec m).2
  have hstep : ∀ m, LStep K L (levK K hKuniv) m (S m) (S (m+1)) := by
    intro m
    have h := (step m (S m) (hS m)).choose_spec.2
    have heq : S (m+1) = (step m (S m) (hS m)).choose := rfl
    rw [heq]
    exact h
  exact ⟨_, _, _, spineData_of_seq hK0 hKuniv S hS hstep⟩

end Work.Noncompact.CompressionTube
