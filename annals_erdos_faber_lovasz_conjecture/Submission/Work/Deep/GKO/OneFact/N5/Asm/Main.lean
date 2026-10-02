import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.OneFact.N5.Defs
import Submission.Work.Deep.GKO.OneFact.N5.insideNearPerfectClasses
import Submission.Work.Deep.GKO.OneFact.matchingAbsorber
import Submission.Work.Deep.GKO.OneFact.exists_balancedCut
import Submission.Work.Deep.GKO.OneFact.hasOneFactorization_sup
import Submission.Work.Deep.GKO.OneFact.N5.Asm.Params
import Submission.Work.Deep.GKO.OneFact.N5.Asm.Helpers

/-!
# The assembly of the elementary one-factorization route (N5)

`main_of_children` assembles `Work.Deep.GKO.OneFactLowerRegStatement` from the pieces of the
elementary route:

* the balanced cut `exists_balancedCut` (proved),
* Vizing on the inside graph `insideNearPerfectClasses` (proved),
* the completion of the good classes `completeGoodClasses` (hypothesis `h_cac`),
* the matching absorber `matchingAbsorber` (proved),
* the gluing `hasOneFactorization_sup` (proved),

plus the three auxiliary results of this chapter, taken here as hypotheses so that the assembly
can be checked on its own: the numeric thresholds (`h_thr`), the regularity and factorization of
a disjoint union of perfect matchings (`h_reg`) and the degree bound for a disjoint union of
matchings (`h_db`).  The file
`Submission/Work/Deep/GKO/OneFact/N5/oneFactLowerReg_elementary.lean` discharges them and states
the result as `Work.Deep.GKO.OneFactLowerRegStatement`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open scoped BigOperators
open Classical

namespace Work.Deep.GKO.OneFact.N5.Asm

open Work.Deep.GKO.OneFact

theorem main_of_children
    (h_thr : ∀ (α p : ℝ), 0 < α → 0 < p → p ≤ 1 →
      ∀ ε β : ℝ, 0 < ε → ε ≤ 1 / 2 → ε ≤ p / 2 → ε ≤ α / 16 → β = p - ε →
        ∃ Nthr : ℕ, ∀ n ≥ Nthr, ∀ r : ℕ, α * (n : ℝ) ≤ (r : ℝ) → r ≤ n →
          ArithOK α n r ε β)
    (h_reg : ∀ {n c : ℕ} {G : SimpleGraph (Fin n)} (P : Fin c → SimpleGraph (Fin n)),
      (∀ i, Work.Deep.GKO.IsPerfectMatching' G (P i)) →
      (∀ i j, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet) →
      Work.Deep.GKO.IsRegularOf (⨆ i, P i) c ∧ (⨆ i, P i) ≤ G ∧
        Work.Deep.GKO.HasOneFactorization (⨆ i, P i) c)
    (h_db : ∀ {n : ℕ} {ι : Type} [Fintype ι] (M : ι → SimpleGraph (Fin n)),
      (∀ i, Work.Deep.GKO.IsMatching' (M i)) →
      (∀ i j, i ≠ j → Disjoint (M i).edgeSet (M j).edgeSet) →
      ∀ (S : Set ι) (v : Fin n), (∀ i, (∃ w, (M i).Adj v w) → i ∈ S) →
      Nat.card ((⨆ i, M i).neighborSet v) ≤ S.ncard)
    (h_cac : ∀ {n : ℕ} (A B : Finset (Fin n)), Disjoint A B → A ∪ B = Finset.univ →
      A.card = B.card → ∀ {c : ℕ} (N : Fin c → SimpleGraph (Fin n)),
      (∀ j, Work.Deep.GKO.IsMatching' (N j)) →
      (∀ j u v, (N j).Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) →
      (∀ i j, i ≠ j → Disjoint (N i).edgeSet (N j).edgeSet) →
      ∀ (K₀ : SimpleGraph (Fin n)),
      (∀ u v, K₀.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) →
      ∀ (q ε : ℝ) (s m L D₀ : ℕ), 0 < q → 0 < ε → 0 < L →
      Work.Deep.GKO.BipLowerReg K₀ A B q ε →
      (∀ j, (uncov (N j)).card ≤ s) →
      (∀ v, (Finset.univ.filter fun j => v ∈ uncov (N j)).card ≤ m) →
      (∀ v, D₀ ≤ Nat.card (K₀.neighborSet v)) →
      ((m + L : ℕ) : ℝ) ≤ q * ε * (n : ℝ) / 2 →
      ε * (n : ℝ) + ((3 * (5 * n * m / L) + 14 * s + m + L + 1 : ℕ) : ℝ) < (D₀ : ℝ) →
      ∃ P : Fin c → SimpleGraph (Fin n),
        (∀ j, Work.Deep.GKO.IsPerfectMatching' (N j ⊔ K₀) (P j)) ∧
        (∀ i j, i ≠ j → Disjoint (P i).edgeSet (P j).edgeSet) ∧
        (∀ v, ({j : Fin c | v ∉ uncov (N j) ∧ Rematched (N j) (P j) v} : Set (Fin c)).ncard
          ≤ L)) :
    Work.Deep.GKO.OneFactLowerRegStatement := by
  intro p hp0 hp1 α hα
  refine ⟨min (min (p / 2) (α / 16)) (1 / 2), ?_, ?_⟩
  · positivity
  intro ε hεpos hεε₀
  have hεhalf : ε ≤ 1 / 2 := hεε₀.trans (min_le_right _ _)
  have hεp : ε ≤ p / 2 := hεε₀.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεα : ε ≤ α / 16 := hεε₀.trans ((min_le_left _ _).trans (min_le_right _ _))
  set β : ℝ := p - ε with hβdef
  have hβpos : 0 < β := by rw [hβdef]; linarith
  obtain ⟨Nthr, hNthr⟩ := h_thr α p hα hp0 hp1 ε β hεpos hεhalf hεp hεα hβdef
  refine ⟨max Nthr 4, ?_⟩
  intro n hn hnEven G hlr r hreg hrn
  have hnThr : Nthr ≤ n := (le_max_left _ _).trans hn
  have hn4 : 4 ≤ n := (le_max_right _ _).trans hn
  have hrn_nat : r ≤ n := by
    obtain ⟨v⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h2 : Nat.card (G.neighborSet v) ≤ n := by
      have h3 : (G.neighborSet v).ncard ≤ n := by
        have h4 : (G.neighborSet v).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
        rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h4
      rwa [Nat.card_coe_set_eq]
    rw [← hreg v]
    exact h2
  have harith := hNthr n hnThr r hrn hrn_nat
  -- ## the balanced cut
  obtain ⟨A, hAcard, hAbal⟩ := exists_balancedCut hnEven G hreg
  set B : Finset (Fin n) := Finset.univ \ A with hBdef
  have hAB : Disjoint A B := by rw [hBdef]; exact Finset.disjoint_sdiff
  have hcov : A ∪ B = Finset.univ := by
    rw [hBdef]; exact Finset.union_sdiff_of_subset (Finset.subset_univ A)
  have hBcard : B.card = n / 2 := by
    have h1 : B.card = (Finset.univ : Finset (Fin n)).card - (A ∩ Finset.univ).card := by
      rw [hBdef]; exact Finset.card_sdiff
    rw [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hAcard] at h1
    obtain ⟨m, hm⟩ := hnEven
    omega
  have hcard : A.card = B.card := by rw [hAcard, hBcard]
  have hmemAB : ∀ x : Fin n, x ∈ A ∨ x ∈ B := by
    intro x
    have h := (Finset.ext_iff.mp hcov) x
    exact Finset.mem_union.mp (h.mpr (Finset.mem_univ x))
  have hbalA : ∀ v : Fin n,
      |((Work.Deep.GKO.degIn G v A : ℕ) : ℝ) - (r : ℝ) / 2| ≤ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) :=
    fun v => (hAbal v).1
  have hbalB : ∀ v : Fin n,
      |((Work.Deep.GKO.degIn G v B : ℕ) : ℝ) - (r : ℝ) / 2| ≤ 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
    intro v
    rw [hBdef]
    exact (hAbal v).2
  -- ## the cross graph
  set K0 : SimpleGraph (Fin n) := crossRestr G A B with hK0def
  have hK0bip : ∀ u v, K0.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) :=
    fun u v h => crossRestr_adj_mem h
  have hK0leG : K0 ≤ G := crossRestr_le G A B
  have hlr0 : Work.Deep.GKO.BipLowerReg K0 A B β ε := by
    intro S hSA T hTB hS hT
    have hdisj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      exact (Finset.disjoint_left.mp hAB) (hSA hxS) (hTB hxT)
    have h1 : (p - ε) * (S.card : ℝ) * (T.card : ℝ) ≤ (Work.Deep.GKO.crossEdges G S T : ℝ) :=
      hlr S T hdisj hS hT
    rw [hβdef, hK0def, crossEdges_crossRestr G hSA hTB]
    exact h1
  -- ## the inside colouring (Vizing on the inside graph)
  have hupA : ∀ v ∈ A, Work.Deep.GKO.degIn G v A ≤ Asm.dpar n r := by
    intro v _
    apply Nat.le_floor
    have h := hbalA v
    rw [abs_le] at h
    linarith [h.2]
  have hupB : ∀ v ∈ B, Work.Deep.GKO.degIn G v B ≤ Asm.dpar n r := by
    intro v _
    apply Nat.le_floor
    have h := hbalB v
    rw [abs_le] at h
    linarith [h.2]
  have hloA : ∀ v ∈ A, Asm.dpar n r ≤ Work.Deep.GKO.degIn G v A + Asm.tpar n := by
    intro v _
    have h := hbalA v
    rw [abs_le] at h
    have h1 : ((Asm.dpar n r : ℕ) : ℝ) ≤ (r : ℝ) / 2 + 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [Asm.dpar]; exact Nat.floor_le (by positivity)
    have h2 : ((Asm.tpar n : ℕ) : ℝ) ≥ 4 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [Asm.tpar]
      have hc := Nat.le_ceil (4 * (n : ℝ) ^ ((2 : ℝ) / 3))
      push_cast
      linarith
    have h3 : ((Asm.dpar n r : ℕ) : ℝ)
        ≤ ((Work.Deep.GKO.degIn G v A + Asm.tpar n : ℕ) : ℝ) := by
      push_cast
      linarith [h.1, h1, h2]
    exact_mod_cast h3
  have hloB : ∀ v ∈ B, Asm.dpar n r ≤ Work.Deep.GKO.degIn G v B + Asm.tpar n := by
    intro v _
    have h := hbalB v
    rw [abs_le] at h
    have h1 : ((Asm.dpar n r : ℕ) : ℝ) ≤ (r : ℝ) / 2 + 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [Asm.dpar]; exact Nat.floor_le (by positivity)
    have h2 : ((Asm.tpar n : ℕ) : ℝ) ≥ 4 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
      rw [Asm.tpar]
      have hc := Nat.le_ceil (4 * (n : ℝ) ^ ((2 : ℝ) / 3))
      push_cast
      linarith
    have h3 : ((Asm.dpar n r : ℕ) : ℝ)
        ≤ ((Work.Deep.GKO.degIn G v B + Asm.tpar n : ℕ) : ℝ) := by
      push_cast
      linarith [h.1, h1, h2]
    exact_mod_cast h3
  obtain ⟨N, hNmatching, hNleG, hNin, hNdisj, hNcover, hNuncov⟩ :=
    insideNearPerfectClasses (d := Asm.dpar n r) (t := Asm.tpar n) A B hAB hcov G
      hupA hupB hloA hloB
  -- ## the good and the bad classes
  set goodF : Finset (Fin (Asm.dpar n r + 1)) :=
    Finset.univ.filter (fun j => (uncov (N j)).card ≤ Asm.spar α n) with hgoodFdef
  set badF : Finset (Fin (Asm.dpar n r + 1)) :=
    Finset.univ.filter (fun j => ¬ ((uncov (N j)).card ≤ Asm.spar α n)) with hbadFdef
  have hsplit : goodF.card + badF.card = Asm.dpar n r + 1 := by
    rw [hgoodFdef, hbadFdef, Finset.card_filter_add_card_filter_not]
    simp
  have hbad_le : badF.card ≤ Asm.bpar α n := by
    have h1 : badF.card * (Asm.spar α n + 1) ≤ n * Asm.mpar n := by
      rw [hbadFdef]
      refine bad_count_le N (fun v => ?_)
      simpa [Asm.mpar] using hNuncov v
    rw [Asm.bpar]
    rw [Nat.le_div_iff_mul_le (by omega : 0 < Asm.spar α n + 1)]
    exact h1
  -- enumeration of the good classes
  let e : goodF ≃ Fin goodF.card := Finset.equivFin goodF
  set g : Fin goodF.card → Fin (Asm.dpar n r + 1) := fun i => (e.symm i).val with hgdef
  have hgmem : ∀ i, g i ∈ goodF := fun i => (e.symm i).2
  have hginj : Function.Injective g := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hgood_of_mem : ∀ j, j ∈ goodF → (uncov (N j)).card ≤ Asm.spar α n :=
    fun j hj => (Finset.mem_filter.mp hj).2
  have hbad_of_notmem : ∀ j, j ∉ goodF → j ∈ badF := by
    intro j hj
    rw [hgoodFdef, Finset.mem_filter] at hj
    rw [hbadFdef, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hcon
    exact hj ⟨Finset.mem_univ _, hcon⟩
  have hgrange : ∀ j : Fin (Asm.dpar n r + 1), j ∈ goodF ↔ ∃ i, g i = j := by
    intro j
    constructor
    · intro hj
      exact ⟨e ⟨j, hj⟩, by rw [hgdef]; simp⟩
    · rintro ⟨i, rfl⟩
      exact hgmem i
  set N' : Fin goodF.card → SimpleGraph (Fin n) := fun i => N (g i) with hN'def
  have hN'match : ∀ i, Work.Deep.GKO.IsMatching' (N' i) := fun i => hNmatching (g i)
  have hN'in : ∀ i u v, (N' i).Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) :=
    fun i u v h => hNin (g i) u v h
  have hN'disj : ∀ i j, i ≠ j → Disjoint (N' i).edgeSet (N' j).edgeSet := by
    intro i j hij
    exact hNdisj (g i) (g j) (fun h => hij (hginj h))
  have hN'U : ∀ j, (uncov (N' j)).card ≤ Asm.spar α n := fun j => hgood_of_mem (g j) (hgmem j)
  have hN'miss : ∀ v, (Finset.univ.filter fun i => v ∈ uncov (N' i)).card ≤ Asm.mpar n := by
    intro v
    have himg : (Finset.univ.filter fun i => v ∈ uncov (N' i)).image g
        ⊆ (Finset.univ.filter fun j : Fin (Asm.dpar n r + 1) => v ∈ uncov (N j)) := by
      intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
    calc (Finset.univ.filter fun i => v ∈ uncov (N' i)).card
        = ((Finset.univ.filter fun i => v ∈ uncov (N' i)).image g).card :=
          (Finset.card_image_of_injective _ hginj).symm
      _ ≤ _ := Finset.card_le_card himg
      _ ≤ Asm.mpar n := by simpa [Asm.mpar] using hNuncov v
  have hN'missSet : ∀ v : Fin n,
      ({i : Fin goodF.card | v ∈ uncov (N' i)} : Set (Fin goodF.card)).ncard ≤ Asm.mpar n := by
    intro v
    have h1 : ({i : Fin goodF.card | v ∈ uncov (N' i)} : Set (Fin goodF.card)).ncard
        = (Finset.univ.filter fun i : Fin goodF.card => v ∈ uncov (N' i)).card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext x
      simp
    rw [h1]
    exact hN'miss v
  -- the degree of `K0`
  have hK0deg : ∀ v : Fin n, Asm.D0par n r ≤ Nat.card (K0.neighborSet v) := by
    intro v
    have hlow : (r : ℝ) / 2 - 2 * (n : ℝ) ^ ((2 : ℝ) / 3)
        ≤ ((Nat.card (K0.neighborSet v) : ℕ) : ℝ) := by
      rcases hmemAB v with hv | hv
      · rw [hK0def, natCard_neighborSet_crossRestr_mem_left G hAB hv]
        have h := hbalB v
        rw [abs_le] at h
        linarith [h.1]
      · rw [hK0def, natCard_neighborSet_crossRestr_mem_right G hAB hv]
        have h := hbalA v
        rw [abs_le] at h
        linarith [h.1]
    by_cases hpos : 0 ≤ (r : ℝ) / 2 - 2 * (n : ℝ) ^ ((2 : ℝ) / 3)
    · have h1 : ((Asm.D0par n r : ℕ) : ℝ) ≤ (r : ℝ) / 2 - 2 * (n : ℝ) ^ ((2 : ℝ) / 3) := by
        rw [Asm.D0par]; exact Nat.floor_le hpos
      exact_mod_cast (h1.trans hlow)
    · have h0 : Asm.D0par n r = 0 := by
        rw [Asm.D0par]; exact Nat.floor_of_nonpos (le_of_not_ge hpos)
      rw [h0]; exact Nat.zero_le _
  -- ## the room conditions
  have hLpos : 0 < Asm.Lpar β ε n := harith.1
  have hroomq : ((Asm.mpar n + Asm.Lpar β ε n : ℕ) : ℝ) ≤ β * ε * (n : ℝ) / 2 := by
    have h1 := harith.2.1
    linarith
  have hroomD : ε * (n : ℝ) + ((3 * (5 * n * Asm.mpar n / Asm.Lpar β ε n) + 14 * Asm.spar α n
      + Asm.mpar n + Asm.Lpar β ε n + 1 : ℕ) : ℝ) < (Asm.D0par n r : ℝ) := harith.2.2.1
  -- ## completing the good classes
  obtain ⟨P', hP'perf, hP'disj, hP'lost⟩ :=
    h_cac A B hAB hcov hcard N' hN'match hN'in hN'disj K0 hK0bip
      β ε (Asm.spar α n) (Asm.mpar n) (Asm.Lpar β ε n) (Asm.D0par n r)
      hβpos hεpos hLpos hlr0 hN'U hN'miss hK0deg hroomq hroomD
  -- ## the residual graphs
  set G1 : SimpleGraph (Fin n) := ⨆ i : Fin goodF.card, P' i with hG1def
  set Hc : SimpleGraph (Fin n) := K0 \ G1 with hHcdef
  set Hl : SimpleGraph (Fin n) :=
    (⨆ j : {j : Fin (Asm.dpar n r + 1) // j ∈ badF}, N j.val) ⊔
      (⨆ i : Fin goodF.card, N' i \ P' i) with hHldef
  have hG1leG : G1 ≤ G := by
    rw [hG1def]
    refine iSup_le fun i => ?_
    exact (hP'perf i).1.trans (sup_le (hNleG (g i)) hK0leG)
  have hHlleG : Hl ≤ G := by
    rw [hHldef]
    refine sup_le ?_ ?_
    · refine iSup_le fun j => ?_
      exact hNleG j.val
    · refine iSup_le fun i => ?_
      refine le_trans ?_ (hNleG (g i))
      intro a b hab
      exact ((SimpleGraph.sdiff_adj (N' i) (P' i) a b).mp hab).1
  have hHcleG : Hc ≤ G := by
    rw [hHcdef]
    refine le_trans ?_ hK0leG
    intro a b hab
    exact ((SimpleGraph.sdiff_adj K0 G1 a b).mp hab).1
  have hGEq : G1 ⊔ (Hc ⊔ Hl) = G := by
    refine le_antisymm ?_ ?_
    · exact sup_le hG1leG (sup_le hHcleG hHlleG)
    · rw [SimpleGraph.le_iff_adj]
      intro u v huv
      rw [SimpleGraph.sup_adj, SimpleGraph.sup_adj]
      rcases hmemAB u with hu | hu <;> rcases hmemAB v with hv | hv
      · obtain ⟨j, hj⟩ := hNcover u v huv (Or.inl ⟨hu, hv⟩)
        by_cases hgood : j ∈ goodF
        · obtain ⟨i, hi⟩ := (hgrange j).mp hgood
          have hi' : (N' i).Adj u v := by show (N (g i)).Adj u v; rw [hi]; exact hj
          by_cases hP : (P' i).Adj u v
          · exact Or.inl ((SimpleGraph.iSup_adj).mpr ⟨i, hP⟩)
          · refine Or.inr (Or.inr ?_)
            rw [hHldef, SimpleGraph.sup_adj]
            exact Or.inr ((SimpleGraph.iSup_adj).mpr
              ⟨i, (SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hi', hP⟩⟩)
        · refine Or.inr (Or.inr ?_)
          rw [hHldef, SimpleGraph.sup_adj]
          exact Or.inl ((SimpleGraph.iSup_adj).mpr ⟨⟨j, hbad_of_notmem j hgood⟩, hj⟩)
      · -- mixed: cross edge
        have hKuv : K0.Adj u v := by
          rw [hK0def]; exact crossRestr_adj_of hu hv huv
        by_cases hG1 : G1.Adj u v
        · exact Or.inl hG1
        · refine Or.inr (Or.inl ?_)
          rw [hHcdef]
          exact (SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hKuv, hG1⟩
      · have hKuv : K0.Adj u v := by
          rw [hK0def]
          exact (crossRestr_adj_of (a := v) (b := u) hv hu ((G.adj_comm u v).mp huv)).symm
        by_cases hG1 : G1.Adj u v
        · exact Or.inl hG1
        · refine Or.inr (Or.inl ?_)
          rw [hHcdef]
          exact (SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hKuv, hG1⟩
      · obtain ⟨j, hj⟩ := hNcover u v huv (Or.inr ⟨hu, hv⟩)
        by_cases hgood : j ∈ goodF
        · obtain ⟨i, hi⟩ := (hgrange j).mp hgood
          have hi' : (N' i).Adj u v := by show (N (g i)).Adj u v; rw [hi]; exact hj
          by_cases hP : (P' i).Adj u v
          · exact Or.inl ((SimpleGraph.iSup_adj).mpr ⟨i, hP⟩)
          · refine Or.inr (Or.inr ?_)
            rw [hHldef, SimpleGraph.sup_adj]
            exact Or.inr ((SimpleGraph.iSup_adj).mpr
              ⟨i, (SimpleGraph.sdiff_adj _ _ _ _).mpr ⟨hi', hP⟩⟩)
        · refine Or.inr (Or.inr ?_)
          rw [hHldef, SimpleGraph.sup_adj]
          exact Or.inl ((SimpleGraph.iSup_adj).mpr ⟨⟨j, hbad_of_notmem j hgood⟩, hj⟩)
  -- ## the residual graphs are edge-disjoint
  have hNdisjK0 : ∀ j : Fin (Asm.dpar n r + 1), Disjoint ((N j).edgeSet) K0.edgeSet :=
    fun j => disjoint_of_inside_cross hAB (hNin j) hK0bip
  have hdiscG1Hc : Disjoint G1 Hc := by
    rw [hHcdef, SimpleGraph.disjoint_left]
    intro a b h hc
    exact ((SimpleGraph.sdiff_adj K0 G1 a b).mp hc).2 h
  have hdiscG1Bad : Disjoint G1 (⨆ j : {j : Fin (Asm.dpar n r + 1) // j ∈ badF}, N j.val) := by
    rw [hG1def, SimpleGraph.disjoint_left]
    intro a b h1 h2
    rw [SimpleGraph.iSup_adj] at h1 h2
    obtain ⟨i, hi⟩ := h1
    obtain ⟨j, hj⟩ := h2
    have hne : g i ≠ j.val := by
      intro heq
      have hgoodi := hgood_of_mem (g i) (hgmem i)
      have hbadj : ¬ ((uncov (N (g i))).card ≤ Asm.spar α n) := by
        rw [heq]
        exact (Finset.mem_filter.mp j.2).2
      exact hbadj hgoodi
    rcases (SimpleGraph.sup_adj (N' i) K0 a b).mp ((hP'perf i).1 hi) with hN' | hK
    · exact (Set.disjoint_left.mp (hNdisj (g i) j.val hne))
        ((SimpleGraph.mem_edgeSet _).mpr hN') ((SimpleGraph.mem_edgeSet _).mpr hj)
    · exact (Set.disjoint_left.mp (hNdisjK0 j.val))
        ((SimpleGraph.mem_edgeSet _).mpr hj) ((SimpleGraph.mem_edgeSet _).mpr hK)
  have hdiscG1Good : Disjoint G1 (⨆ i : Fin goodF.card, N' i \ P' i) := by
    rw [hG1def, SimpleGraph.disjoint_left]
    intro a b h1 h2
    rw [SimpleGraph.iSup_adj] at h1 h2
    obtain ⟨i, hi⟩ := h1
    obtain ⟨i', hi'⟩ := h2
    have hi'2 : (N' i').Adj a b := ((SimpleGraph.sdiff_adj (N' i') (P' i') a b).mp hi').1
    rcases eq_or_ne i i' with rfl | hne
    · exact ((SimpleGraph.sdiff_adj (N' i) (P' i) a b).mp hi').2 hi
    · have hPsub := (SimpleGraph.sup_adj (N' i) K0 a b).mp ((hP'perf i).1 hi)
      rcases hPsub with hN' | hK
      · exact (Set.disjoint_left.mp (hN'disj i i' hne))
          ((SimpleGraph.mem_edgeSet _).mpr hN') ((SimpleGraph.mem_edgeSet _).mpr hi'2)
      · exact (Set.disjoint_left.mp (hNdisjK0 (g i')))
          ((SimpleGraph.mem_edgeSet _).mpr hi'2) ((SimpleGraph.mem_edgeSet _).mpr hK)
  have hdiscG1Hl : Disjoint G1 Hl := by
    rw [hHldef, disjoint_sup_right]
    exact ⟨hdiscG1Bad, hdiscG1Good⟩
  have hdisc : Disjoint G1.edgeSet (Hc ⊔ Hl).edgeSet := by
    rw [SimpleGraph.edgeSet_sup, Set.disjoint_union_right]
    exact ⟨(SimpleGraph.disjoint_edgeSet).mpr hdiscG1Hc, (SimpleGraph.disjoint_edgeSet).mpr hdiscG1Hl⟩
  have hHlinside : ∀ u v, Hl.Adj u v → (u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B) := by
    intro u v huv
    rw [hHldef, SimpleGraph.sup_adj] at huv
    rcases huv with hbad | hgood
    · rw [SimpleGraph.iSup_adj] at hbad
      obtain ⟨j, hj⟩ := hbad
      exact hNin j.val u v hj
    · rw [SimpleGraph.iSup_adj] at hgood
      obtain ⟨i, hi⟩ := hgood
      exact hN'in i u v ((SimpleGraph.sdiff_adj (N' i) (P' i) u v).mp hi).1
  have hHccross : ∀ u v, Hc.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u v huv
    rw [hHcdef] at huv
    exact hK0bip u v ((SimpleGraph.sdiff_adj K0 G1 u v).mp huv).1
  have hdiscHcHl : Disjoint Hc.edgeSet Hl.edgeSet :=
    (disjoint_of_inside_cross hAB hHlinside hHccross).symm
  have hNK : ∀ i : Fin goodF.card, Disjoint ((N' i).edgeSet) K0.edgeSet := by
    intro i
    refine disjoint_of_inside_cross hAB (hN'in i) hK0bip
  -- ## the degree bounds
  have hBadDeg : ∀ v : Fin n,
      Nat.card ((⨆ j : {j : Fin (Asm.dpar n r + 1) // j ∈ badF}, N j.val).neighborSet v)
        ≤ badF.card := by
    intro v
    have hdb := h_db (M := fun j : {j : Fin (Asm.dpar n r + 1) // j ∈ badF} => N j.val)
      (fun j => hNmatching j.val)
      (fun i j hij => hNdisj i.val j.val (fun h => hij (Subtype.ext h)))
      (Set.univ : Set {j : Fin (Asm.dpar n r + 1) // j ∈ badF}) v (fun i _ => Set.mem_univ i)
    rw [Set.ncard_univ] at hdb
    have hcard : Nat.card {j : Fin (Asm.dpar n r + 1) // j ∈ badF} = badF.card := by
      calc Nat.card {j : Fin (Asm.dpar n r + 1) // j ∈ badF}
          = Nat.card (Fin badF.card) := Nat.card_congr (Finset.equivFin badF)
        _ = badF.card := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    rwa [hcard] at hdb
  have hGoodDeg : ∀ v : Fin n,
      Nat.card ((⨆ i : Fin goodF.card, N' i \ P' i).neighborSet v) ≤ Asm.Lpar β ε n := by
    intro v
    have hdb := h_db (M := fun i : Fin goodF.card => N' i \ P' i)
      (fun i => isMatching'_sdiff (M := N' i) (hN'match i))
      (fun i j hij => Disjoint.mono
        (SimpleGraph.edgeSet_mono
          (fun a b h => ((SimpleGraph.sdiff_adj (N' i) (P' i) a b).mp h).1))
        (SimpleGraph.edgeSet_mono
          (fun a b h => ((SimpleGraph.sdiff_adj (N' j) (P' j) a b).mp h).1))
        (hN'disj i j hij))
      ({i : Fin goodF.card | v ∉ uncov (N' i) ∧ Rematched (N' i) (P' i) v} : Set (Fin goodF.card))
      v (fun i hcon => ?_)
    · exact hdb.trans (hP'lost v)
    · obtain ⟨w, hw⟩ := hcon
      have hw' := (SimpleGraph.sdiff_adj (N' i) (P' i) v w).mp hw
      refine ⟨?_, ?_⟩
      · intro hunc
        rw [mem_uncov] at hunc
        exact hunc w hw'.1
      · obtain ⟨w', hw'mate, huniq⟩ := (hP'perf i).2 v
        have hne : w' ≠ w := fun h => hw'.2 (h ▸ hw'mate)
        refine ⟨w', hw'mate, ?_⟩
        intro hNadj
        exact hne (hN'match i v w' w hNadj hw'.1)
  have hInter : ∀ v : Fin n,
      Nat.card (K0.neighborSet v ∩ G1.neighborSet v : Set (Fin n))
        ≤ Asm.mpar n + Asm.Lpar β ε n := by
    intro v
    have hdb := h_db (M := fun i : Fin goodF.card => P' i ⊓ K0)
      (fun i => isMatching'_inf (M := P' i) (isMatching'_of_isPerfectMatching (G := N' i ⊔ K0) (P := P' i) (hP'perf i)))
      (fun i j hij => Disjoint.mono (SimpleGraph.edgeSet_mono inf_le_left)
        (SimpleGraph.edgeSet_mono inf_le_left) (hP'disj i j hij))
      ({i : Fin goodF.card | v ∈ uncov (N' i) ∨ Rematched (N' i) (P' i) v} : Set (Fin goodF.card))
      v (fun i hcon => ?_)
    · have hset : (⨆ i : Fin goodF.card, (P' i ⊓ K0)).neighborSet v
          = K0.neighborSet v ∩ G1.neighborSet v := by
        rw [hG1def]
        rw [SimpleGraph.neighborSet_iSup, SimpleGraph.neighborSet_iSup]
        simp only [SimpleGraph.neighborSet_inf]
        rw [Set.inter_iUnion]
        simp only [Set.inter_comm]
      rw [hset] at hdb
      refine hdb.trans ?_
      have hsub : ({i : Fin goodF.card | v ∈ uncov (N' i) ∨ Rematched (N' i) (P' i) v}
            : Set (Fin goodF.card))
          ⊆ ({i : Fin goodF.card | v ∈ uncov (N' i)}
              ∪ {i : Fin goodF.card | v ∉ uncov (N' i) ∧ Rematched (N' i) (P' i) v}
                : Set (Fin goodF.card)) := by
        intro i hi
        rcases hi with h | h
        · exact Or.inl h
        · by_cases hu : v ∈ uncov (N' i)
          · exact Or.inl hu
          · exact Or.inr ⟨hu, h⟩
      refine le_trans (Set.ncard_le_ncard hsub) ?_
      refine le_trans (Set.ncard_union_le _ _) ?_
      exact add_le_add (hN'missSet v) (hP'lost v)
    · obtain ⟨w, hw⟩ := hcon
      obtain ⟨hPiw, hKiw⟩ := (SimpleGraph.inf_adj (P' i) K0 v w).mp hw
      by_cases hunc : v ∈ uncov (N' i)
      · exact Or.inl hunc
      · refine Or.inr ⟨w, hPiw, ?_⟩
        intro hNiw
        exact (Set.disjoint_left.mp (hNK i))
          ((SimpleGraph.mem_edgeSet _).mpr hNiw) ((SimpleGraph.mem_edgeSet _).mpr hKiw)
  have hHldeg : ∀ v : Fin n, Nat.card (Hl.neighborSet v) ≤ badF.card + Asm.Lpar β ε n := by
    intro v
    have h1 := hBadDeg v
    have h2 := hGoodDeg v
    rw [hHldef, SimpleGraph.neighborSet_sup, Nat.card_coe_set_eq]
    refine le_trans (Set.ncard_union_le _ _) ?_
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact add_le_add h1 h2
  have hHcdeg : ∀ v : Fin n,
      Asm.D0par n r - (Asm.mpar n + Asm.Lpar β ε n) ≤ Nat.card (Hc.neighborSet v) := by
    intro v
    have h1 : (K0.neighborSet v).ncard
        ≤ ((K0 \ G1).neighborSet v).ncard + (K0.neighborSet v ∩ G1.neighborSet v).ncard := by
      have hsub : K0.neighborSet v ⊆
          (K0 \ G1).neighborSet v ∪ (K0.neighborSet v ∩ G1.neighborSet v) := by
        intro z hz
        have hKz : K0.Adj v z := (SimpleGraph.mem_neighborSet K0 v z).mp hz
        by_cases h : (K0 \ G1).Adj v z
        · exact Or.inl ((SimpleGraph.mem_neighborSet _ v z).mpr h)
        · refine Or.inr ⟨hz, ?_⟩
          by_contra hg
          rw [SimpleGraph.sdiff_adj] at h
          exact h ⟨hKz, hg⟩
      exact le_trans (Set.ncard_le_ncard hsub) (Set.ncard_union_le _ _)
    have h2 : Asm.D0par n r ≤ (K0.neighborSet v).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact hK0deg v
    have h3 : ((K0.neighborSet v ∩ G1.neighborSet v : Set (Fin n))).ncard
        ≤ Asm.mpar n + Asm.Lpar β ε n := by
      rw [← Nat.card_coe_set_eq]
      exact hInter v
    have h4 : Asm.D0par n r - (Asm.mpar n + Asm.Lpar β ε n)
        ≤ ((K0 \ G1).neighborSet v).ncard := by omega
    rw [hHcdef, Nat.card_coe_set_eq]
    exact h4
  -- ## the lower regularity of the deleted cross graph
  have hHlr : Work.Deep.GKO.BipLowerReg Hc A B (β / 2) ε := by
    intro S hSA T hTB hS hT
    have hsum1 : Work.Deep.GKO.crossEdges K0 S T
        ≤ Work.Deep.GKO.crossEdges Hc S T + S.card * (Asm.mpar n + Asm.Lpar β ε n) := by
      rw [crossEdges_eq_sum_degIn, crossEdges_eq_sum_degIn]
      calc ∑ u ∈ S, Work.Deep.GKO.degIn K0 u T
          ≤ ∑ u ∈ S, (Work.Deep.GKO.degIn Hc u T
              + Nat.card (K0.neighborSet u ∩ G1.neighborSet u : Set (Fin n))) :=
            Finset.sum_le_sum fun u _ => degIn_le_degIn_sdiff_add K0 G1 u T
        _ = ∑ u ∈ S, Work.Deep.GKO.degIn Hc u T
              + ∑ u ∈ S, Nat.card (K0.neighborSet u ∩ G1.neighborSet u : Set (Fin n)) :=
            Finset.sum_add_distrib
        _ ≤ ∑ u ∈ S, Work.Deep.GKO.degIn Hc u T
              + ∑ _u ∈ S, (Asm.mpar n + Asm.Lpar β ε n) :=
            add_le_add (le_refl _) (Finset.sum_le_sum fun u _ => hInter u)
        _ = ∑ u ∈ S, Work.Deep.GKO.degIn Hc u T
              + S.card * (Asm.mpar n + Asm.Lpar β ε n) := by
            rw [Finset.sum_const, smul_eq_mul]
    have hK0low : (β : ℝ) * (S.card : ℝ) * (T.card : ℝ)
        ≤ (Work.Deep.GKO.crossEdges K0 S T : ℝ) := hlr0 S hSA T hTB hS hT
    have hHcup : (Work.Deep.GKO.crossEdges K0 S T : ℝ)
        ≤ (Work.Deep.GKO.crossEdges Hc S T : ℝ)
          + (S.card : ℝ) * (Asm.mpar n + Asm.Lpar β ε n : ℕ) := by
      exact_mod_cast hsum1
    have hmL : (Asm.mpar n + Asm.Lpar β ε n : ℕ) ≤ (β / 2) * (T.card : ℝ) := by
      have h1 : ((Asm.mpar n + Asm.Lpar β ε n : ℕ) : ℝ) ≤ β * ε * (n : ℝ) / 4 := harith.2.1
      have h2 : ε * (n : ℝ) ≤ (T.card : ℝ) := hT
      nlinarith [h1, h2, hβpos]
    have hSnn : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
    have hfin : (β / 2) * (S.card : ℝ) * (T.card : ℝ)
        ≤ (Work.Deep.GKO.crossEdges Hc S T : ℝ) := by
      nlinarith [hK0low, hHcup,
        mul_le_mul_of_nonneg_left hmL hSnn, hSnn,
        show (0 : ℝ) ≤ (T.card : ℝ) by positivity, hβpos]
    exact hfin
  -- ## regularity of the leftover
  have hP'perfG : ∀ i, Work.Deep.GKO.IsPerfectMatching' G (P' i) := fun i =>
    ⟨(hP'perf i).1.trans (sup_le (hNleG (g i)) hK0leG), (hP'perf i).2⟩
  have hregG1 := h_reg P' hP'perfG hP'disj
  have hc_le_r : goodF.card ≤ r := by
    have h2 : Asm.dpar n r + 1 ≤ r := harith.2.2.2.1
    omega
  have hregHl : Work.Deep.GKO.IsRegularOf (Hc ⊔ Hl) (r - goodF.card) := by
    intro v
    have hG1regv : Nat.card (G1.neighborSet v) = goodF.card := by
      have h := hregG1.1 v
      rwa [← hG1def] at h
    have hd : Nat.card ((G1 ⊔ (Hc ⊔ Hl)).neighborSet v)
        = Nat.card (G1.neighborSet v) + Nat.card ((Hc ⊔ Hl).neighborSet v) :=
      card_neighborSet_sup_of_disjoint hdisc v
    rw [hGEq, hreg v, hG1regv] at hd
    omega
  -- ## the absorber
  have hroom1 : 8 * (Nat.sqrt ((badF.card + Asm.Lpar β ε n) * n) + 3)
      ≤ Asm.D0par n r - (Asm.mpar n + Asm.Lpar β ε n) :=
    harith.2.2.2.2.1 badF.card hbad_le
  have hroom3 : ((Nat.sqrt ((badF.card + Asm.Lpar β ε n) * n) + 3 : ℕ) : ℝ)
      < (β / 2) * ε * (n : ℝ) := harith.2.2.2.2.2.1 badF.card hbad_le
  have hroom2 : 2 * ε * (n : ℝ)
      ≤ ((Asm.D0par n r - (Asm.mpar n + Asm.Lpar β ε n) : ℕ) : ℝ) :=
    harith.2.2.2.2.2.2 badF.card hbad_le
  have hFamHas : Work.Deep.GKO.HasOneFactorization (Hc ⊔ Hl) (r - goodF.card) :=
    matchingAbsorber (D := Asm.D0par n r - (Asm.mpar n + Asm.Lpar β ε n))
      (d₀ := badF.card + Asm.Lpar β ε n) (k := r - goodF.card) (q := β / 2) (ε := ε)
      hnEven A B hAB hcov hcard Hc Hl hdiscHcHl hHccross (by linarith) hεpos
      hHcdeg hHlr hHldeg hregHl hroom1 hroom2 hroom3
  -- ## gluing the two factorizations
  have hG1fac : Work.Deep.GKO.HasOneFactorization G1 goodF.card := by
    have h := hregG1.2.2
    rwa [← hG1def] at h
  have hglue := hasOneFactorization_sup hdisc hG1fac hFamHas
  rw [hGEq, Nat.add_sub_cancel' hc_le_r] at hglue
  exact hglue

end Work.Deep.GKO.OneFact.N5.Asm
