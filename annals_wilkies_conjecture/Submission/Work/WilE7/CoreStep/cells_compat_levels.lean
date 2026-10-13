import Mathlib
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.star_central
import Submission.Work.WilE7.CoreStep.bandCell_subset_or_disjoint_of_interior
import Submission.Work.WilE7.decomp_of_sections

namespace Work.WilE7.CoreStep

/-- **Elementary topology step.**  Let `K`, `A` be subsets of a topological space and let
`κ ⊆ K` be preconnected.  If `A ∩ K` is open in the subspace `K` and `κ` avoids the part of the
boundary of `A` lying in `K` (that is `κ ∩ (closure A \ A) ∩ K = ∅`), then `κ` is contained in `A`
or disjoint from `A`.

Indeed, choose an ambient open set `V` with `V ∩ K = A ∩ K`; then `V` and `(closure A)ᶜ` are
disjoint on `κ` and cover `κ`, so preconnectedness puts `κ` inside one of them.  Either alternative
gives the conclusion because `κ ⊆ K`. -/
lemma preconnected_subset_or_disjoint_of_open_subtype {X : Type*} [TopologicalSpace X]
    {K A κ : Set X} (hκ : IsPreconnected κ) (hκK : κ ⊆ K)
    (hAopen : IsOpen {z : ↥K | (z : X) ∈ A})
    (hdisj : Disjoint κ ((closure A \ A) ∩ K)) :
    κ ⊆ A ∨ Disjoint κ A := by
  obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hAopen
  -- points of `κ` lying in `V` lie in `A`
  have hVA : κ ∩ V ⊆ A := by
    rintro z ⟨hzκ, hzV⟩
    have hmem : (⟨z, hκK hzκ⟩ : ↥K) ∈ Subtype.val ⁻¹' V := hzV
    rw [hVeq] at hmem
    exact hmem
  -- `κ` is covered by the two ambient open pieces `V` and `(closure A)ᶜ`
  have hcover : κ ⊆ V ∪ (closure A)ᶜ := by
    intro z hzκ
    by_cases hzA : z ∈ A
    · left
      have hmem : (⟨z, hκK hzκ⟩ : ↥K) ∈ ({z : ↥K | (z : X) ∈ A}) := hzA
      rwa [← hVeq] at hmem
    · right
      rw [Set.mem_compl_iff]
      intro hzcl
      exact (Set.disjoint_left.mp hdisj hzκ) ⟨⟨hzcl, hzA⟩, hκK hzκ⟩
  have hdisj2 : κ ∩ (V ∩ (closure A)ᶜ) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzκ, hzV, hzcl⟩
    exact hzcl (subset_closure (hVA ⟨hzκ, hzV⟩))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hκ) V (closure A)ᶜ hVopen
      isClosed_closure.isOpen_compl hcover hdisj2 with hsub | hsub
  · exact Or.inl fun z hz => hVA ⟨hz, hsub hz⟩
  · exact Or.inr (Set.disjoint_left.mpr fun z hzκ hzA => hsub hzκ (subset_closure hzA))

/-- A band cell between two consecutive levels is disjoint from the union of all `q+2` level
graphs intersected with the cylinder: a point of the band has last coordinate lying strictly
between the two consecutive levels, hence different from *every* level
(`Work.WilE7.CoreStep.lvl_ne_of_between`). -/
lemma bd_disjoint_iUnion_gr {p q : ℕ} {C : Set (Fin p → ℝ)}
    (s : Fin q → (Fin p → ℝ) → ℝ)
    (hsmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hsbnd : ∀ x ∈ C, ∀ j : Fin q, |s j x| < 1)
    (i : Fin (q + 1)) :
    Disjoint
      (Work.WilE7.bd C (fun x => Work.WilE7.lvl s x (Fin.castSucc i))
        (fun x => Work.WilE7.lvl s x i.succ))
      (⋃ j : Fin (q + 2),
        Work.WilE7.gr C (fun x => Work.WilE7.lvl s x j) ∩ Work.WilE7.cyl C) := by
  rw [Set.disjoint_left]
  rintro z hzB hzU
  rw [Work.WilE7.bd, Set.mem_ofPred_eq] at hzB
  obtain ⟨hzC, h1, h2⟩ := hzB
  rw [Set.mem_iUnion] at hzU
  obtain ⟨j, hjg, -⟩ := hzU
  rw [Work.WilE7.gr, Set.mem_ofPred_eq] at hjg
  obtain ⟨-, hj2⟩ := hjg
  exact (lvl_ne_of_between s hsmono (fun k x hx => hsbnd x hx k) hzC h1 h2 j) hj2

/-- The graph cell of a level lies in the cylinder: the level function takes its values in
`[-1,1]`. -/
lemma gr_subset_cyl {p q : ℕ} {C : Set (Fin p → ℝ)}
    (s : Fin q → (Fin p → ℝ) → ℝ)
    (hsbnd : ∀ x ∈ C, ∀ j : Fin q, |s j x| < 1)
    (i : Fin (q + 2)) :
    Work.WilE7.gr C (fun x => Work.WilE7.lvl s x i) ⊆ Work.WilE7.cyl C := by
  intro z hz
  rw [Work.WilE7.gr, Set.mem_ofPred_eq] at hz
  obtain ⟨hzC, hzlast⟩ := hz
  rw [Work.WilE7.cyl, Set.mem_ofPred_eq]
  refine ⟨hzC, ?_⟩
  rw [hzlast]
  exact Work.WilE7.abs_lvl_le_one (fun j => hsbnd (Fin.init z) hzC j) i

/-- A band cell between two consecutive levels is preconnected. -/
lemma isPreconnected_bd {p q : ℕ} {C : Set (Fin p → ℝ)}
    (hCpre : IsPreconnected C)
    (s : Fin q → (Fin p → ℝ) → ℝ)
    (hcont : ∀ j : Fin q, ContinuousOn (s j) C)
    (hsmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hsbnd : ∀ x ∈ C, ∀ j : Fin q, |s j x| < 1)
    (i : Fin (q + 1)) :
    IsPreconnected (Work.WilE7.bd C (fun x => Work.WilE7.lvl s x (Fin.castSucc i))
      (fun x => Work.WilE7.lvl s x i.succ)) := by
  have hab : ∀ x ∈ C, Work.WilE7.lvl s x (Fin.castSucc i) < Work.WilE7.lvl s x i.succ :=
    fun x hx => (Work.WilE7.strictMono_lvl (hsmono x hx) (fun j => hsbnd x hx j))
      Fin.castSucc_lt_succ
  rw [show Work.WilE7.bd C (fun x => Work.WilE7.lvl s x (Fin.castSucc i))
        (fun x => Work.WilE7.lvl s x i.succ)
      = {z : Fin (p + 1) → ℝ | Fin.init z ∈ C ∧
          (Work.WilE7.lvl s (Fin.init z) (Fin.castSucc i) : EReal)
            < ((z (Fin.last p) : ℝ) : EReal) ∧
          ((z (Fin.last p) : ℝ) : EReal)
            < (Work.WilE7.lvl s (Fin.init z) i.succ : EReal)} by
    ext z; simp only [Work.WilE7.bd, Set.mem_ofPred_eq, EReal.coe_lt_coe_iff]]
  exact Work.WilE7.isPreconnected_band_fin hCpre
    (fun x => (Work.WilE7.lvl s x (Fin.castSucc i) : EReal))
    (fun x => (Work.WilE7.lvl s x i.succ : EReal))
    (continuous_coe_real_ereal.comp_continuousOn
      (Work.WilE7.continuous_lvl hcont (Fin.castSucc i)))
    (continuous_coe_real_ereal.comp_continuousOn
      (Work.WilE7.continuous_lvl hcont i.succ))
    (fun x hx => EReal.coe_lt_coe_iff.mpr (hab x hx))

theorem cells_compat_levels {p q : ℕ} {C : Set (Fin p → ℝ)}
    (hCell : WilkiesDesign.IsCell p C)
    (s : Fin q → (Fin p → ℝ) → ℝ)
    (hcont : ∀ j : Fin q, ContinuousOn (s j) C)
    (hsmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hsbnd : ∀ x ∈ C, ∀ j : Fin q, |s j x| < 1)
    (A : Set (Fin (p + 1) → ℝ))
    (hAopen : IsOpen {z : ↥(Work.WilE7.cyl C) | (z : Fin (p + 1) → ℝ) ∈ A})
    (hgraph : ∀ i : Fin (q + 2),
      Work.WilE7.gr C (fun x => Work.WilE7.lvl s x i) ∩ Work.WilE7.cyl C ⊆ A ∨
        Disjoint (Work.WilE7.gr C (fun x => Work.WilE7.lvl s x i) ∩ Work.WilE7.cyl C) A)
    (hbound : (closure A \ A) ∩ Work.WilE7.cyl C ⊆
      ⋃ i : Fin (q + 2),
        Work.WilE7.gr C (fun x => Work.WilE7.lvl s x i) ∩ Work.WilE7.cyl C) :
    ∀ κ ∈ Work.WilE7.cfs C s, κ ⊆ A ∨ Disjoint κ A := by
  intro κ hκ
  rw [Work.WilE7.mem_cfs] at hκ
  rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · -- a graph cell: read the conclusion off the compatibility hypothesis `hgraph`
    have hgc := gr_subset_cyl s hsbnd i
    rcases hgraph i with h | h
    · exact Or.inl fun z hz => h ⟨hz, hgc hz⟩
    · exact Or.inr (Set.disjoint_left.mpr fun z hz hzA =>
        (Set.disjoint_left.mp h) ⟨hz, hgc hz⟩ hzA)
  · -- a band cell: preconnected, inside the cylinder, and disjoint from the level graphs
    refine preconnected_subset_or_disjoint_of_open_subtype ?_ ?_ hAopen ?_
    · exact isPreconnected_bd (Work.WilE7.isPreconnected_of_isCell hCell) s hcont hsmono hsbnd i
    · exact Work.WilE7.cfs_subset_cyl (fun x hx => hsmono x hx)
        (fun x hx j => hsbnd x hx j) _ (Work.WilE7.mem_cfs.mpr (Or.inr ⟨i, rfl⟩))
    · exact Set.disjoint_of_subset_right hbound (bd_disjoint_iUnion_gr s hsmono hsbnd i)

end Work.WilE7.CoreStep