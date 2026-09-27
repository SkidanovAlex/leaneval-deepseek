import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_state
import Submission.Work.Noncompact.CompressionTube.collar_peel

/-!
# The level-`0` datum of the collar construction

The base case of the collar recursion (`LInv K L U (levK …) 0 st`).  There is no previous level, so
the "previous collar" of the peel lemma is `P = ∅` and there are no slits and no obstacles: all the
work is done by `peel_arcs` with `P := ∅`, applied to the start points `s i` = the base points of
level `0` (`b ∈ B` with `levK b = 0`, i.e. `b ∈ K 1`), the collar `L 0` and the shell `Shell K 1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **The level-`0` datum.** -/
theorem collar_base_LInv {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    {K : ℕ → Set M} {B : Set M}
    (hB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite)
    (hKc : ∀ i, IsCompact (K i)) (hK0 : K 0 = ∅) (hKsub : ∀ i, K i ⊆ interior (K (i+1)))
    (hKuniv : (⋃ i, K i) = (Set.univ : Set M))
    (hM : ¬ CompactSpace M)
    {L U : ℕ → Set M} (hLc : ∀ j, IsClosed (L j)) (hAL : ∀ j, K (j+1) ⊆ interior (L j))
    (hLB : ∀ j, L j ⊆ interior (K (j+2)))
    (hUo : ∀ j, IsOpen (U j)) (hUL : ∀ j, Disjoint (U j) (L j))
    (hpieces : ∀ j z, z ∈ frontier (L j) →
      ∃ (x : M) (b : Work.Whitney.PathTools.ChartBall n M Set.univ x),
        z ∈ b.K ∧ b.c.symm '' Metric.ball (b.c x) b.ρ ⊆ U j) :
    ∃ st : LSt B, LInv K L U (levK K hKuniv) 0 st := by
  classical
  -- the active set at level 0 and its enumeration
  haveI hfin1 : Fintype ↥(B ∩ K 1) := (hB (K 1) (hKc 1)).fintype
  haveI : Fintype {b : B // levK K hKuniv b ≤ 0} := by
    refine Fintype.ofInjective
      (fun b : {b : B // levK K hKuniv b ≤ 0} =>
        (⟨(b.1 : M), ⟨b.1.2, ?_⟩⟩ : ↥(B ∩ K 1))) ?_
    · have h3 : levK K hKuniv b.1 = 0 := by have := b.2; omega
      have h4 := levK_mem_succ hK0 hKuniv b.1
      rwa [h3] at h4
    · intro b b' h
      have h1 : (b.1 : M) = (b'.1 : M) := congrArg (fun x : ↥(B ∩ K 1) => (x : M)) h
      exact Subtype.ext (Subtype.ext h1)
  set A := {b : B // levK K hKuniv b ≤ 0} with hAdef
  set k : ℕ := Fintype.card A with hkdef
  set e : A ≃ Fin k := Fintype.equivFin A with hedef
  set s : Fin k → M := fun i => ((e.symm i).1 : M) with hsdef
  have hsmem : ∀ i : Fin k, levK K hKuniv (e.symm i).1 = 0 := by
    intro i
    have h2 : levK K hKuniv ((e.symm i).1) ≤ 0 := (e.symm i).2
    have h3 : ((e.symm i).1 : M) = s i := rfl
    omega
  have hsB : ∀ i : Fin k, s i ∈ B := by
    intro i
    have h2 : ((e.symm i).1 : M) ∈ B := (e.symm i).1.2
    simpa only [hsdef, Equiv.apply_symm_apply] using h2
  have hsK1 : ∀ i : Fin k, s i ∈ K 1 := by
    intro i
    have h4 := levK_mem_succ hK0 hKuniv ((e.symm i).1)
    have h5 : levK K hKuniv ((e.symm i).1) + 1 = 1 := by
      have : levK K hKuniv ((e.symm i).1) = 0 := by have := (e.symm i).2; omega
      omega
    rw [h5] at h4
    simpa only [hsdef, Equiv.apply_symm_apply] using h4
  have hsinj : Function.Injective s := by
    intro i i' h
    have h1 : e.symm i = e.symm i' := Subtype.ext (Subtype.ext h)
    exact e.symm.injective h1
  -- the avoidance sets
  set F : Fin k → Set M := fun i =>
    ((B ∩ K 2 : Set M) \ {s i}) ∪ {x : M | ∃ i' : Fin k, i' ≠ i ∧ x = s i'} with hFdef
  have hFfin : ∀ i : Fin k, (F i).Finite := by
    intro i
    refine (Set.Finite.union ?_ ?_)
    · exact (hB (K 2) (hKc 2)).sdiff
    · exact (Set.finite_range (fun i' : Fin k => s i')).subset (fun x hx => by
        obtain ⟨i', _, rfl⟩ := hx; exact ⟨i', rfl⟩)
  have hsF : ∀ i : Fin k, s i ∉ F i := by
    intro i h
    rcases h with h | ⟨i', hne, heq⟩
    · exact h.2 rfl
    · exact hne (hsinj heq.symm ▸ rfl)
  have hFs : ∀ i i' : Fin k, i ≠ i' → s i' ∈ F i := fun i i' hne => Or.inr ⟨i', hne.symm, rfl⟩
  -- the peel lemma
  obtain ⟨α, σ, hcont, hinj, hzero, hσ, hin, hout, houtU, houtSh, htipSh, htipU, htipF, hcomp,
    hincomp, hnotF, havβ, havslit, havown, hdisj, hstart⟩ :=
    peel_arcs (n := n) hn (P := (∅ : Set M)) (L := L 0) (K := K 2) (U := U 0)
      (Shell := Shell K 1) isClosed_empty
      (fun x _ => by
        have hc : connectedComponentIn ((∅ : Set M)ᶜ) x = Set.univ := by
          rw [Set.compl_empty]
          exact le_antisymm (Set.subset_univ _)
            (isPreconnected_univ.subset_connectedComponentIn (Set.mem_univ x) subset_rfl)
        rw [hc, closure_univ]
        intro hcon
        exact hM (isCompact_univ_iff.mp hcon))
      (hLc 0) (hKc 2) ((hLB 0).trans interior_subset)
      (hUo 0) (hUL 0) (isOpen_shell K (hKc 1).isClosed)
      (frontier_collar_subset_shell (hLc 0) (hAL 0) (hLB 0))
      (hpieces 0)
      (hsint := fun i => hAL 0 (hsK1 i)) (hsinj := hsinj) (hsP := fun i => Set.notMem_empty _)
      (F := F) (hF := hFfin) (hsF := hsF) (hFs := hFs)
      (slt := fun j : Fin 0 => (Fin.elim0 j : ℝ → M))
      (hsltc := fun (j : Fin 0) => Fin.elim0 j)
      (hsltinj := fun (j : Fin 0) => Fin.elim0 j)
      (hsltbody := fun (j : Fin 0) => Fin.elim0 j)
      (hsltroot := fun (j : Fin 0) => Fin.elim0 j)
      (hsltU := fun (j : Fin 0) => Fin.elim0 j)
      (hsltdisj := fun (j j' : Fin 0) => Fin.elim0 j)
      (clip := fun j : Fin 0 => Fin.elim0 j)
      (hclip := fun (j : Fin 0) => Fin.elim0 j)
      (hsnotslt := fun (i : Fin k) (j : Fin 0) => Fin.elim0 j)
      (β := fun j : Fin 0 => (Fin.elim0 j : ℝ → M))
      (hβc := fun (j : Fin 0) => Fin.elim0 j)
      (hβsub := fun (j : Fin 0) => Fin.elim0 j)
      (hβ0F := fun (i : Fin k) (j : Fin 0) => Fin.elim0 j)
      (hβfront := fun (i : Fin k) (j : Fin 0) => Fin.elim0 j)
  -- the arc stays in `int (K (0+2))`
  have harcK : ∀ i u, u ∈ Set.Icc (0:ℝ) 1 → α i u ∈ interior (K 2) := by
    intro i u hu
    by_cases hlt : u ≤ σ i
    · exact hLB 0 (hin i u ⟨hu.1, hlt⟩)
    · have hu' : u ∈ Set.Ioc (σ i) 1 := ⟨lt_of_not_ge hlt, hu.2⟩
      rw [Shell] at houtSh
      exact (houtSh i u hu').1
  refine ⟨⟨fun b => if hb : levK K hKuniv b ≤ 0 then s (e ⟨b, hb⟩) else (b : M),
    fun b => if hb : levK K hKuniv b ≤ 0 then α (e ⟨b, hb⟩) else fun _ => (b : M),
    fun b => if hb : levK K hKuniv b ≤ 0 then σ (e ⟨b, hb⟩) else 1/2⟩, ?_⟩
  have hsval : ∀ (b : B) (hb : levK K hKuniv b ≤ 0), s (e ⟨b, hb⟩) = (b : M) := by
    intro b hb
    show ((e.symm (e ⟨b, hb⟩)).1 : M) = (b : M)
    rw [Equiv.symm_apply_apply e ⟨b, hb⟩]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- arc_cont
    intro b hb
    simp only [dif_pos hb]
    exact hcont _
  · -- arc_inj
    intro b hb
    simp only [dif_pos hb]
    exact hinj _
  · -- arc_zero
    intro b hb
    simp only [dif_pos hb]
    exact hzero _
  · -- tau_mem
    intro b hb
    simp only [dif_pos hb]
    exact hσ _
  · -- inside_L
    intro b hb u hu
    simp only [dif_pos hb] at hu ⊢
    exact hin _ u hu
  · -- outside_notL
    intro b hb u hu
    simp only [dif_pos hb] at hu ⊢
    exact hout _ u hu
  · -- outside_U
    intro b hb u hu
    simp only [dif_pos hb] at hu ⊢
    exact houtU _ u hu
  · -- tip_shell
    intro b hb
    simp only [dif_pos hb]
    exact htipSh _
  · -- arc_sub
    intro b hb u hu
    simp only [dif_pos hb]
    refine ⟨harcK _ u hu, ?_⟩
    rw [hK0]
    exact Set.notMem_empty _
  · -- arc_notB
    intro b b' hb hne u hu
    simp only [dif_pos hb]
    intro heq
    have hmemF : α (e ⟨b, hb⟩) u ∉ F (e ⟨b, hb⟩) := hnotF _ u hu
    refine hmemF (Or.inl ⟨⟨heq ▸ (b' : B).2, interior_subset (harcK _ u hu)⟩, ?_⟩)
    · intro hc
      have h2 : ((b' : B) : M) = ((b : B) : M) := by rw [← heq, hc, hsval b hb]
      exact hne (Subtype.ext h2)
  · -- q_mem
    intro b hb
    simp only [dif_pos hb]
    exact ⟨hsK1 _, by rw [hK0]; exact Set.notMem_empty _⟩
  · -- q_int
    intro b hb hlt
    exact absurd hlt (by omega)
  · -- q_eq
    intro b hb heq
    simp only [dif_pos hb]
    exact hsval b hb
  · -- arc_disj
    intro b b' hb hb' hne
    simp only [dif_pos hb, dif_pos hb']
    refine hdisj _ _ (fun hc => hne ?_)
    have h1 : (⟨b, hb⟩ : A) = ⟨b', hb'⟩ := e.injective hc
    exact Subtype.ext (congrArg (fun x : A => (x.1 : M)) h1)

end Work.Noncompact.CompressionTube
