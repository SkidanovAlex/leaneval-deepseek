/-
# Existence of the Cantor tree

This file assembles the inductive construction of `TreeData d c ρ η`, given the local level
construction (`existsLocal1`) as a hypothesis `hlocal`: the first level is the local level of
the root `[0,1]`, and each subsequent level is obtained by applying the local construction to
every parent simultaneously (the fold `foldExists`), keeping the indices used so far
forbidden.

* `FSt`/`FOk` : state and invariant of the fold over the parents;
* `foldExists`, `foldChildren` : the fold;
* `GSt`/`GOk` : state and invariant of the level recursion;
* `initExists`, `stepExists`, `stepSt`, `seqN`, `mkTree`, `existsTreeData` : the recursion and
  the resulting `TreeData`.
-/
import Submission.Work.MassTransferenceAlt.Tree.Data

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace Work.MassTransferenceAlt

/-! ### The fold over the parents of one level -/

/-- Auxiliary state of the fold over the parents of a level. -/
structure FSt where
  /-- the children built so far -/
  ch : Finset ℕ
  /-- the indices used so far (including the forbidden set) -/
  used : Finset ℕ
  /-- the parents already given their local level -/
  done : Finset ℕ
  /-- the parent map -/
  par : ℕ → Option ℕ
  /-- the sub-level map -/
  sub : ℕ → ℕ

/-- Invariant of the fold. -/
def FOk (d : ℝ) (c ρ : ℕ → ℝ) (T : Finset ℕ) (s : FSt) : Prop :=
  (∀ i ∈ s.ch, ∃ B ∈ s.done, s.par i = some B) ∧
  (s.ch ∪ T ⊆ s.used) ∧ Disjoint s.ch T ∧
  (∀ i ∈ s.ch, Good d c ρ i) ∧
  (∀ B ∈ s.done, IsLoc d c ρ (c B) (ρ B)
      ((s.ch).filter (fun i => s.par i = some B)) s.sub (nsub d (ρ B)))

/-- **The fold.**  Processing the parents one by one, each parent `B` is given its local
level of `nsub d (ρ B)` sub-levels, with the indices used so far forbidden. -/
theorem foldExists (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (P T : Finset ℕ) (hGood : ∀ B ∈ P, Good d c ρ B) :
    ∃ s : FSt, FOk d c ρ T s ∧ s.done = P := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      refine ⟨⟨∅, T, ∅, fun _ => none, fun _ => 0⟩, ?_, rfl⟩
      refine ⟨?_, by simp, by simp, by simp, ?_⟩
      · intro i hi; exact absurd hi (Finset.notMem_empty i)
      · intro B hB; exact absurd hB (Finset.notMem_empty B)
  | insert a S ha ih =>
      obtain ⟨s, hs, hdone⟩ := ih (fun B hB => hGood B (Finset.mem_insert_of_mem hB))
      have haGood : Good d c ρ a := hGood a (Finset.mem_insert_self a S)
      obtain ⟨F, subl, hfresh, hloc⟩ := hlocal (c a) (ρ a) haGood.1
        (le_trans haGood.2.1 (Rabs_le_one hd1)) haGood.2.2.1 haGood.2.2.2 s.used
        (nsub d (ρ a)) (nsub_pos d (ρ a))
      obtain ⟨hpar, hsubT, hcT, hgood, hlocold⟩ := hs
      have hFused : ∀ i ∈ F, i ∉ s.used := hfresh
      have hFch2 : ∀ i ∈ s.ch, i ∉ F := fun i hi hiF =>
        hFused i hiF (hsubT (Finset.mem_union_left _ hi))
      have hdoneSa : s.done = S := hdone
      set par' : ℕ → Option ℕ := fun i => if i ∈ F then some a else s.par i with hpar'def
      set sub' : ℕ → ℕ := fun i => if i ∈ F then subl i else s.sub i with hsub'def
      have hpar'S : ∀ i ∈ s.ch, par' i = s.par i := fun i hi => by
        rw [hpar'def]; exact if_neg (hFch2 i hi)
      have hpar'F : ∀ i ∈ F, par' i = some a := fun i hi => by
        rw [hpar'def]; exact if_pos hi
      have hsub'S : ∀ i ∈ s.ch, sub' i = s.sub i := fun i hi => by
        rw [hsub'def]; exact if_neg (hFch2 i hi)
      have hsub'F : ∀ i ∈ F, sub' i = subl i := fun i hi => by
        rw [hsub'def]; exact if_pos hi
      let s' : FSt := ⟨s.ch ∪ F, s.used ∪ F, insert a s.done, par', sub'⟩
      have hch : s'.ch = s.ch ∪ F := rfl
      have hused : s'.used = s.used ∪ F := rfl
      have hdone' : s'.done = insert a s.done := rfl
      have hpar'' : ∀ i, s'.par i = par' i := fun i => rfl
      have hsub'' : ∀ i, s'.sub i = sub' i := fun i => rfl
      refine ⟨s', ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro i hi
          rw [hch] at hi
          rw [hpar'', hdone']
          rw [Finset.mem_union] at hi
          rcases hi with hi | hi
          · obtain ⟨B, hB, hparB⟩ := hpar i hi
            exact ⟨B, Finset.mem_insert_of_mem (hdoneSa ▸ hB), by rw [hpar'S i hi]; exact hparB⟩
          · exact ⟨a, Finset.mem_insert_self a s.done, hpar'F i hi⟩
        · intro i hi
          rw [hused]
          rw [hch] at hi
          rcases Finset.mem_union.mp hi with hi | hi
          · rcases Finset.mem_union.mp hi with hi | hi
            · exact Finset.mem_union_left _ (hsubT (Finset.mem_union_left _ hi))
            · exact Finset.mem_union_right _ hi
          · exact Finset.mem_union_left _ (hsubT (Finset.mem_union_right _ hi))
        · rw [Finset.disjoint_left] at ⊢
          intro i hi hiT
          simp only [hch, Finset.mem_union] at hi
          rcases hi with hi | hi
          · exact (Finset.disjoint_left.mp hcT) hi hiT
          · exact hFused i hi (hsubT (Finset.mem_union_right _ hiT))
        · intro i hi
          simp only [hch, Finset.mem_union] at hi
          rcases hi with hi | hi
          · exact hgood i hi
          · obtain ⟨h1, h2, h3, -, -, -, -, -, -⟩ := hloc
            have hle : ρ i ≤ Rabs d := le_trans (h2 i hi) (thrC_le_Rabs d (ρ a) (nsub d (ρ a)))
            have hmem : Iv (c i) (ρ i) ⊆ Fenl d c ρ i :=
              Iv_mono (self_le_rpow hd0 hd1 (h1 i hi) hle)
            refine ⟨h1 i hi, hle, ?_, ?_⟩
            · have hz : c i - ρ i ∈ Iv (c i) (ρ i) := by
                rw [mem_Iv, show c i - ρ i - c i = -ρ i by ring, abs_neg,
                  abs_of_nonneg (h1 i hi).le]
              have h5 := h3 i hi (hmem hz)
              rw [Iv, Set.mem_Icc] at h5
              exact le_trans haGood.2.2.1 h5.1
            · have hz : c i + ρ i ∈ Iv (c i) (ρ i) := by
                rw [mem_Iv, show c i + ρ i - c i = ρ i by ring, abs_of_nonneg (h1 i hi).le]
              have h5 := h3 i hi (hmem hz)
              rw [Iv, Set.mem_Icc] at h5
              exact le_trans h5.2 haGood.2.2.2
        · intro B hB
          rw [hdone'] at hB
          rw [Finset.mem_insert] at hB
          by_cases hBa : B = a
          · -- the new parent: its children are exactly `F`
            have hfilter : (s'.ch).filter (fun i => s'.par i = some B) = F := by
              rw [hch]
              ext i
              rw [Finset.mem_filter, Finset.mem_union]
              constructor
              · rintro ⟨hi | hi, hiff⟩
                · rw [hpar'' i, hpar'S i hi] at hiff
                  obtain ⟨B', hB', hparB'⟩ := hpar i hi
                  rw [hparB'] at hiff
                  have hBB : B = B' := Option.some.inj hiff.symm
                  have hBS : B ∈ S := hBB ▸ (hdoneSa ▸ hB')
                  rw [hBa] at hBS
                  exact absurd hBS ha
                · rw [hpar'' i, hpar'F i hi] at hiff
                  exact hi
              · intro hiF
                refine ⟨Or.inr hiF, ?_⟩
                rw [hpar'', hpar'F i hiF, hBa]
            rw [hfilter, hBa]
            obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hloc
            refine ⟨h1, h2, h3, ?_, h5, ?_, ?_, ?_, ?_⟩
            · intro i hi j hj hij hsij
              rw [hsub'' i, hsub'' j] at hsij
              exact h4 i hi j hj hij (by rwa [hsub'F i hi, hsub'F j hj] at hsij)
            · intro i hi
              rw [hsub'' i, hsub'F i hi]; exact h6 i hi
            · intro k hk
              obtain ⟨i, hi, hik⟩ := h7 k hk
              exact ⟨i, hi, by rw [hsub'' i, hsub'F i hi]; exact hik⟩
            · intro k hk
              have hfc : (F.filter (fun i => s'.sub i = k)) = F.filter (fun i => subl i = k) := by
                apply Finset.filter_congr
                intro i hi
                rw [hsub'' i, hsub'F i hi]
              rw [hfc]
              exact h8 k hk
            · intro i hi j hj hij
              rw [hsub'' i, hsub'' j, hsub'F i hi, hsub'F j hj] at hij ⊢
              exact h9 i hi j hj hij
          · -- an old parent: its children are unchanged
            push_neg at hBa
            have hB' : B ∈ s.done := by
              rcases hB with h | h
              · exact absurd h hBa
              · exact h
            obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hlocold B hB'
            have hfilter : (s'.ch).filter (fun i => s'.par i = some B)
                = (s.ch).filter (fun i => s.par i = some B) := by
              rw [hch]
              ext i
              rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter]
              constructor
              · rintro ⟨hi | hi, hiff⟩
                · exact ⟨hi, by rw [hpar'' i, hpar'S i hi] at hiff; exact hiff⟩
                · rw [hpar'' i, hpar'F i hi] at hiff
                  have hBa' : B = a := Option.some.inj hiff.symm
                  exact absurd hBa' hBa
              · rintro ⟨hi, hiff⟩
                exact ⟨Or.inl hi, by rw [hpar'', hpar'S i hi]; exact hiff⟩
            rw [hfilter]
            refine ⟨h1, h2, h3, ?_, h5, ?_, ?_, ?_, ?_⟩
            · intro i hi j hj hij hsij
              rw [hsub'' i, hsub'' j] at hsij
              exact h4 i hi j hj hij (by rwa [hsub'S i (Finset.mem_of_mem_filter i hi),
                hsub'S j (Finset.mem_of_mem_filter j hj)] at hsij)
            · intro i hi
              rw [hsub'' i, hsub'S i (Finset.mem_of_mem_filter i hi)]; exact h6 i hi
            · intro k hk
              obtain ⟨i, hi, hik⟩ := h7 k hk
              exact ⟨i, hi, by rw [hsub'' i, hsub'S i (Finset.mem_of_mem_filter i hi)]; exact hik⟩
            · intro k hk
              have hfc : ((s.ch).filter (fun i => s.par i = some B)).filter (fun i => s'.sub i = k)
                  = ((s.ch).filter (fun i => s.par i = some B)).filter (fun i => s.sub i = k) := by
                apply Finset.filter_congr
                intro i hi
                rw [hsub'' i, hsub'S i (Finset.mem_of_mem_filter i hi)]
              rw [hfc]
              exact h8 k hk
            · intro i hi j hj hij
              rw [hsub'' i, hsub'' j, hsub'S i (Finset.mem_of_mem_filter i hi),
                hsub'S j (Finset.mem_of_mem_filter j hj)] at hij ⊢
              exact h9 i hi j hj hij
      · rw [hdone', hdoneSa]

/-- **The fold**, in the form used for the level recursion. -/
theorem foldChildren (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (P T : Finset ℕ) (hGood : ∀ B ∈ P, Good d c ρ B) :
    ∃ (ch : Finset ℕ) (used : Finset ℕ) (par : ℕ → Option ℕ) (sub : ℕ → ℕ),
      (∀ B ∈ P, IsLoc d c ρ (c B) (ρ B) (ch.filter (fun i => par i = some B)) sub
        (nsub d (ρ B))) ∧
      (∀ i ∈ ch, ∃ B ∈ P, par i = some B) ∧
      (∀ B ∈ P, (ch.filter (fun i => par i = some B)).Nonempty) ∧
      Disjoint ch T ∧ (∀ i ∈ ch, Good d c ρ i) := by
  obtain ⟨s, hs, hdone⟩ := foldExists d hd0 hd1 c ρ hlocal P T hGood
  obtain ⟨hpar, -, hcT, hgood, hloc⟩ := hs
  refine ⟨s.ch, s.used, s.par, s.sub, ?_, ?_, ?_, hcT, hgood⟩
  · intro B hB; exact hloc B (hdone ▸ hB)
  · intro i hi
    obtain ⟨B, hB, hparB⟩ := hpar i hi
    exact ⟨B, hdone ▸ hB, hparB⟩
  · intro B hB
    obtain ⟨-, -, -, -, -, -, hsurj, -, -⟩ := hloc B (hdone ▸ hB)
    obtain ⟨i, hi, -⟩ := hsurj 0 (nsub_pos d (ρ B))
    exact ⟨i, hi⟩


/-! ### The level recursion -/

/-- The state of the construction at one level: the current level, the previous level, the
indices used so far, and the parent and sub-level maps of the current level. -/
structure GSt where
  lev : Finset ℕ
  plev : Finset ℕ
  used : Finset ℕ
  par : ℕ → Option ℕ
  sub : ℕ → ℕ

/-- Validity of a state. -/
def GOk (d : ℝ) (c ρ : ℕ → ℝ) (η : ℝ) (s : GSt) : Prop :=
  (∀ i ∈ s.lev, Good d c ρ i) ∧ s.lev ⊆ s.used ∧
  (s.plev = ∅ → IsLoc d c ρ (1/2) (1/2) s.lev s.sub (nsubRoot η)) ∧
  (∀ B ∈ s.plev, IsLoc d c ρ (c B) (ρ B)
      ((s.lev).filter (fun i => s.par i = some B)) s.sub (nsub d (ρ B)))

lemma lev_nonempty_of_GOk {d : ℝ} {c ρ : ℕ → ℝ} {η : ℝ} {s : GSt} (hs : GOk d c ρ η s) :
    s.lev.Nonempty := by
  by_cases h : s.plev = ∅
  · have hloc := hs.2.2.1 h
    obtain ⟨-, -, -, -, -, -, hsurj, -, -⟩ := hloc
    obtain ⟨i, hi, -⟩ := hsurj 0 (by have := nsubRoot_pos η; omega)
    exact ⟨i, hi⟩
  · obtain ⟨B, hB⟩ := Finset.nonempty_iff_ne_empty.mpr h
    have hloc := hs.2.2.2 B hB
    obtain ⟨-, -, -, -, -, -, hsurj, -, -⟩ := hloc
    obtain ⟨i, hi, -⟩ := hsurj 0 (by have := nsub_pos d (ρ B); omega)
    exact ⟨i, Finset.mem_of_mem_filter i hi⟩

/-- **The first level**: the local level of the root `[0,1]`, with `nsubRoot η` sub-levels. -/
theorem initExists (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (hη : 0 < η) :
    ∃ s : GSt, GOk d c ρ η s ∧ s.plev = ∅ ∧ s.used = s.lev := by
  obtain ⟨F, sub, -, hloc⟩ := hlocal (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ∅ (nsubRoot η) (nsubRoot_pos η)
  refine ⟨⟨F, ∅, F, fun _ => none, sub⟩, ⟨?_, Finset.Subset.refl _, ?_, ?_⟩, rfl, rfl⟩
  · intro i hi
    obtain ⟨h1, h2, h3, -, -, -, -, -, -⟩ := hloc
    have hle : ρ i ≤ Rabs d := le_trans (h2 i hi) (thrC_le_Rabs d (1/2) (nsubRoot η))
    have hsub : Iv (c i) (ρ i) ⊆ Fenl d c ρ i := Iv_mono (self_le_rpow hd0 hd1 (h1 i hi) hle)
    have hlo : c i - ρ i ∈ Iv (1/2) (1/2) := h3 i hi (hsub (by
      rw [mem_Iv, show c i - ρ i - c i = -ρ i by ring, abs_neg, abs_of_nonneg (h1 i hi).le]))
    have hhi : c i + ρ i ∈ Iv (1/2) (1/2) := h3 i hi (hsub (by
      rw [mem_Iv, show c i + ρ i - c i = ρ i by ring, abs_of_nonneg (h1 i hi).le]))
    refine ⟨h1 i hi, hle, ?_, ?_⟩
    · rw [Iv, Set.mem_Icc] at hlo; norm_num at hlo; linarith [hlo.1]
    · rw [Iv, Set.mem_Icc] at hhi; norm_num at hhi; exact hhi.2
  · intro _; exact hloc
  · intro B hB; exact absurd hB (Finset.notMem_empty B)

/-- **One step of the level recursion.** -/
theorem stepExists (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (s : GSt) (hs : GOk d c ρ η s) :
    ∃ s' : GSt, GOk d c ρ η s' ∧ s'.plev = s.lev ∧ s'.used = s.used ∪ s'.lev ∧
      (∀ i ∈ s'.lev, i ∉ s.used) ∧
      (∀ i ∈ s'.lev, ∃ B ∈ s.lev, s'.par i = some B) ∧
      (∀ B ∈ s.lev, IsLoc d c ρ (c B) (ρ B)
        ((s'.lev).filter (fun i => s'.par i = some B)) s'.sub (nsub d (ρ B))) := by
  obtain ⟨ch, used, par, sub, hloc, hpar, hne, hdisj, hgood⟩ :=
    foldChildren d hd0 hd1 c ρ hlocal s.lev s.used (fun B hB => hs.1 B hB)
  refine ⟨⟨ch, s.lev, s.used ∪ ch, par, sub⟩, ⟨hgood, ?_, ?_, ?_⟩, rfl, rfl, ?_, hpar, hloc⟩
  · intro i hi; exact Finset.mem_union_right _ hi
  · intro hemp
    exact False.elim ((lev_nonempty_of_GOk hs).ne_empty hemp)
  · intro B hB; exact hloc B hB
  · intro i hi
    exact (Finset.disjoint_left.mp hdisj) hi

/-- The state sequence, by recursion on the level. -/
noncomputable def initSt (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (hη : 0 < η) : {s : GSt // GOk d c ρ η s} :=
  ⟨(initExists d hd0 hd1 c ρ hlocal η hη).choose,
    (initExists d hd0 hd1 c ρ hlocal η hη).choose_spec.1⟩

noncomputable def stepSt (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (s : {s : GSt // GOk d c ρ η s}) : {s : GSt // GOk d c ρ η s} :=
  ⟨(stepExists d hd0 hd1 c ρ hlocal η s.val s.property).choose,
    (stepExists d hd0 hd1 c ρ hlocal η s.val s.property).choose_spec.1⟩

theorem stepSt_spec (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (s : {s : GSt // GOk d c ρ η s}) :
    GOk d c ρ η (stepSt d hd0 hd1 c ρ hlocal η s).val ∧
    (stepSt d hd0 hd1 c ρ hlocal η s).val.plev = s.val.lev ∧
    (stepSt d hd0 hd1 c ρ hlocal η s).val.used
      = s.val.used ∪ (stepSt d hd0 hd1 c ρ hlocal η s).val.lev ∧
    (∀ i ∈ (stepSt d hd0 hd1 c ρ hlocal η s).val.lev, i ∉ s.val.used) ∧
    (∀ i ∈ (stepSt d hd0 hd1 c ρ hlocal η s).val.lev,
      ∃ B ∈ s.val.lev, (stepSt d hd0 hd1 c ρ hlocal η s).val.par i = some B) ∧
    (∀ B ∈ s.val.lev, IsLoc d c ρ (c B) (ρ B)
      (((stepSt d hd0 hd1 c ρ hlocal η s).val.lev).filter
        (fun i => (stepSt d hd0 hd1 c ρ hlocal η s).val.par i = some B))
      (stepSt d hd0 hd1 c ρ hlocal η s).val.sub (nsub d (ρ B))) :=
  (stepExists d hd0 hd1 c ρ hlocal η s.val s.property).choose_spec

noncomputable def seqN (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (hη : 0 < η) : ℕ → {s : GSt // GOk d c ρ η s}
  | 0 => initSt d hd0 hd1 c ρ hlocal η hη
  | (n+1) => stepSt d hd0 hd1 c ρ hlocal η (seqN d hd0 hd1 c ρ hlocal η hη n)


lemma initSt_spec (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (hη : 0 < η) :
    GOk d c ρ η (initSt d hd0 hd1 c ρ hlocal η hη).val ∧
    (initSt d hd0 hd1 c ρ hlocal η hη).val.plev = ∅ ∧
    (initSt d hd0 hd1 c ρ hlocal η hη).val.used = (initSt d hd0 hd1 c ρ hlocal η hη).val.lev :=
  (initExists d hd0 hd1 c ρ hlocal η hη).choose_spec

lemma seqN_zero (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (hη : 0 < η) :
    seqN d hd0 hd1 c ρ hlocal η hη 0 = initSt d hd0 hd1 c ρ hlocal η hη := rfl

lemma seqN_succ (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (hη : 0 < η) (n : ℕ) :
    seqN d hd0 hd1 c ρ hlocal η hη (n+1)
      = stepSt d hd0 hd1 c ρ hlocal η (seqN d hd0 hd1 c ρ hlocal η hη n) := rfl

/-- **The mass of the root level.**  If the children of `[0,1]` form a local level with
`nsubRoot η` sub-levels, their total `f`-volume is at least `η`. -/
lemma rootBound (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) {F : Finset ℕ}
    {sub : ℕ → ℕ} (hloc : IsLoc d c ρ (1/2) (1/2) F sub (nsubRoot η)) :
    η ≤ ∑ i ∈ F, vf d ρ i := by
  classical
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hloc
  have hcov : ∑ i ∈ F, (ρ i) ^ d
      = ∑ k ∈ Finset.range (nsubRoot η), ∑ i ∈ F.filter (fun i => sub i = k), (ρ i) ^ d := by
    have hd : (↑(Finset.range (nsubRoot η)) : Set ℕ).PairwiseDisjoint
        (fun k => F.filter (fun i => sub i = k)) := by
      intro k _ k' _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [Finset.mem_filter] at hi hi'
      exact hne (by rw [← hi.2, ← hi'.2])
    have hb : (Finset.range (nsubRoot η)).biUnion (fun k => F.filter (fun i => sub i = k)) = F := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨k, -, hi, -⟩; exact hi
      · intro hi
        exact ⟨sub i, h6 i hi, hi, rfl⟩
    rw [← Finset.sum_biUnion hd, hb]
  have hlow : ∑ k ∈ Finset.range (nsubRoot η),
      ∑ i ∈ F.filter (fun i => sub i = k), (ρ i) ^ d
      ≥ ((nsubRoot η : ℝ)) / 32 := by
    have h2' : ∀ k ∈ Finset.range (nsubRoot η),
        (1:ℝ) / 32 ≤ ∑ i ∈ F.filter (fun i => sub i = k), (ρ i) ^ d := by
      intro k hk
      have hk' : k < nsubRoot η := Finset.mem_range.mp hk
      have := h8 k hk'
      norm_num at this ⊢
      linarith
    calc ∑ k ∈ Finset.range (nsubRoot η),
          ∑ i ∈ F.filter (fun i => sub i = k), (ρ i) ^ d
        ≥ ∑ _k ∈ Finset.range (nsubRoot η), (1:ℝ)/32 := by
          refine Finset.sum_le_sum fun k hk => h2' k hk
      _ = (nsubRoot η : ℝ) / 32 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hvfb : ∑ i ∈ F, vf d ρ i = (2:ℝ)^d * ∑ i ∈ F, (ρ i)^d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [vf, Real.mul_rpow (by norm_num) (by have := h1 i ‹i ∈ F›; positivity)]
  have hnr : 64 * η < ((nsubRoot η : ℕ) : ℝ) := lt_nsubRoot
  have hpow : (1:ℝ) ≤ (2:ℝ)^d := by
    rw [← Real.one_rpow d]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num) hd0.le
  rw [hvfb]
  have hmain : (2:ℝ)^d * (((nsubRoot η : ℕ) : ℝ) / 32) ≥ η := by
    rcases lt_or_ge η 0 with h0 | h0
    · have : (0:ℝ) ≤ (2:ℝ)^d * (((nsubRoot η : ℕ) : ℝ) / 32) := by positivity
      linarith
    · have h1 : 2 * η ≤ ((nsubRoot η : ℕ) : ℝ) / 32 := by
        have := lt_nsubRoot (η := η); linarith
      have h2 : (1:ℝ) ≤ (2:ℝ)^d := hpow
      nlinarith [h1, h2, h0]
  calc η ≤ (2:ℝ)^d * (((nsubRoot η : ℕ) : ℝ) / 32) := hmain
    _ ≤ (2:ℝ)^d * ∑ i ∈ F, (ρ i) ^ d := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hcov]
        exact hlow


/-- **Existence of the Cantor tree.** -/
theorem existsTreeData (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ)
    (hlocal : ∀ (B R : ℝ), 0 < R → R ≤ 1 → 0 ≤ B - R → B + R ≤ 1 → ∀ (T : Finset ℕ) (L : ℕ),
      1 ≤ L → ∃ (F : Finset ℕ) (sub : ℕ → ℕ), (∀ i ∈ F, i ∉ T) ∧ IsLoc d c ρ B R F sub L)
    (η : ℝ) (hη : 0 < η) :
    Nonempty (TreeData d c ρ η) := by
  classical
  obtain ⟨hinit, hplev, hused0⟩ := initSt_spec d hd0 hd1 c ρ hlocal η hη
  refine ⟨⟨fun n => (seqN d hd0 hd1 c ρ hlocal η hη n).val.lev,
    fun n => (seqN d hd0 hd1 c ρ hlocal η hη n).val.used,
    fun n => match n with
      | 0 => fun _ => none
      | (k+1) => (seqN d hd0 hd1 c ρ hlocal η hη (k+1)).val.par,
    fun n => (seqN d hd0 hd1 c ρ hlocal η hη n).val.sub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- the root local level
    exact hinit.2.2.1 hplev
  · -- the root mass
    exact rootBound d hd0 hd1 c ρ η (hinit.2.2.1 hplev)
  · -- every ball is admissible
    intro n i hi
    exact (seqN d hd0 hd1 c ρ hlocal η hη n).property.1 i hi
  · -- the parents of level `n+1` lie in level `n`
    intro n i hi
    exact (stepSt_spec d hd0 hd1 c ρ hlocal η (seqN d hd0 hd1 c ρ hlocal η hη n)).2.2.2.2.1 i hi
  · -- the local level of every ball
    intro n B hB
    exact (stepSt_spec d hd0 hd1 c ρ hlocal η (seqN d hd0 hd1 c ρ hlocal η hη n)).2.2.2.2.2 B hB
  · -- `used 0 = lev 0`
    exact hused0
  · -- `used (n+1) = used n ∪ lev (n+1)`
    intro n
    exact (stepSt_spec d hd0 hd1 c ρ hlocal η (seqN d hd0 hd1 c ρ hlocal η hη n)).2.2.1
  · -- freshness
    intro n i hi
    exact (stepSt_spec d hd0 hd1 c ρ hlocal η (seqN d hd0 hd1 c ρ hlocal η hη n)).2.2.2.1 i hi

end Work.MassTransferenceAlt
