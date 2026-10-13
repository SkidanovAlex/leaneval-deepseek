import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.cells
import Submission.Work.WilE7.singleton_cylDecomp
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.decomp_cover
import Submission.Work.WilE7.decomp_cell_eq_of_mem
import Submission.Work.WilE7.decomp_isCell
import Submission.Work.WilE7.decomp_initImage

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesDesign WilkiesDesign.E

/-! ## Helpers for the assembly

The cell family `cfs C s` (see `DecompDefs`) consists of the graphs of the `q+2`
levels `-1, s 0, …, s (q-1), 1` and the `q+1` open bands between consecutive
levels.  The two lemmas below provide the two inclusions of the statement that
the family covers the cylinder. -/

/-- Every cell of `cfs C s` lies in the cylinder `cyl C`. -/
theorem cfs_subset_cyl {n q : ℕ} {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ x ∈ C, ∀ j, |s j x| < 1) :
    ∀ κ ∈ cfs C s, κ ⊆ cyl C := by
  intro κ hκ z hz
  rw [mem_cfs] at hκ
  rcases hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · obtain ⟨hx, ht⟩ := hz
    exact ⟨hx, by rw [ht]; exact abs_lvl_le_one (hbnd _ hx) i⟩
  · obtain ⟨hx, ha, hb⟩ := hz
    refine ⟨hx, abs_le.mpr ⟨?_, ?_⟩⟩
    · exact le_of_lt (lt_of_le_of_lt
        (neg_le_of_abs_le (abs_lvl_le_one (hbnd _ hx) (Fin.castSucc i))) ha)
    · exact le_of_lt (lt_of_lt_of_le hb
        (le_of_abs_le (abs_lvl_le_one (hbnd _ hx) i.succ)))

/-- The members of `cfs C s` cover the cylinder `cyl C`. -/
theorem sUnion_cfs {n q : ℕ} {C : Set (Fin n → ℝ)} {s : Fin q → (Fin n → ℝ) → ℝ}
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ x ∈ C, ∀ j, |s j x| < 1) :
    ⋃₀ (cfs C s : Set (Set (Fin (n+1) → ℝ))) = cyl C := by
  apply le_antisymm
  · intro z hz
    rw [Set.mem_sUnion] at hz
    obtain ⟨κ, hκ, hzκ⟩ := hz
    exact cfs_subset_cyl hmono hbnd κ hκ hzκ
  · intro z hz
    rw [Set.mem_sUnion]
    have hx : Fin.init z ∈ C := hz.1
    have hcov := decomp_cover (C := C) (s := s) hx (hmono _ hx) (hbnd _ hx) hz.2
    rwa [Fin.snoc_init_self] at hcov

/-! ## The main theorem -/

theorem decomp_of_sections {n q : ℕ} {C : Set (Fin n → ℝ)}
    (hC : WilkiesDesign.IsCell n C) (hCne : C.Nonempty)
    {s : Fin q → (Fin n → ℝ) → ℝ} (hs : ∀ j, ContinuousOn (s j) C)
    (hmono : ∀ x ∈ C, StrictMono fun j : Fin q => s j x)
    (hbnd : ∀ x ∈ C, ∀ j, |s j x| < 1) :
    ∃ C' : Finset (Set (Fin (n + 1) → ℝ)),
      WilkiesDesign.E.IsCylDecompOn (n + 1)
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ |z (Fin.last n)| ≤ 1} C' ∧
      C'.card ≤ 2 * q + 3 ∧
      (∀ κ ∈ C', WilkiesDesign.IsCell (n + 1) κ) ∧
      (∀ j : Fin q,
        {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = s j (Fin.init z)} ∈ C') ∧
      (∀ κ ∈ C',
        (∃ f : (Fin n → ℝ) → ℝ, ContinuousOn f C ∧
            κ = {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ z (Fin.last n) = f (Fin.init z)}) ∨
        (∃ a b : (Fin n → ℝ) → ℝ, ContinuousOn a C ∧ ContinuousOn b C ∧
            (∀ x ∈ C, a x < b x) ∧
            κ = {z : Fin (n + 1) → ℝ | Fin.init z ∈ C ∧ a (Fin.init z) < z (Fin.last n) ∧
                  z (Fin.last n) < b (Fin.init z)})) := by
  refine ⟨cfs C s, ?_, ?_, ?_, ?_, ?_⟩
  · show WilkiesDesign.E.IsCylDecompOn (n + 1) (cyl C) (cfs C s)
    refine ⟨decomp_isCell hC hCne hs hmono hbnd, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      show Disjoint a b
      rw [Set.disjoint_left]
      intro z hza hzb
      exact hab (decomp_cell_eq_of_mem hmono hbnd ha hb hza hzb)
    · exact sUnion_cfs hmono hbnd
    · have hinit : Fin.init '' cyl C = C := by
        ext x; constructor
        · rintro ⟨z, hz, rfl⟩; exact hz.1
        · intro hx
          exact ⟨Fin.snoc x 0, ⟨by simpa using hx, by simp⟩, by simp⟩
      have himg : (cfs C s).image (fun c => Fin.init '' c) = {C} := by
        ext κ; constructor
        · intro h
          rw [Finset.mem_image] at h
          obtain ⟨c, hc, rfl⟩ := h
          rw [Finset.mem_singleton]
          exact decomp_initImage hmono hbnd c hc
        · intro h
          rw [Finset.mem_singleton] at h
          rw [h]
          have hcell : gr C (fun x => lvl s x 0) ∈ cfs C s := by
            rw [cfs, Finset.mem_union]; left; rw [mem_gcs]; exact ⟨0, rfl⟩
          rw [Finset.mem_image]
          exact ⟨gr C (fun x => lvl s x 0), hcell, decomp_initImage hmono hbnd _ hcell⟩
      rw [hinit, himg]
      exact singleton_cylDecomp.1 C hC hCne
  · rw [cfs]
    calc (gcs C s ∪ bcs C s).card ≤ (gcs C s).card + (bcs C s).card := Finset.card_union_le _ _
      _ ≤ (Finset.univ : Finset (Fin (q+2))).card + (Finset.univ : Finset (Fin (q+1))).card :=
          Nat.add_le_add (by rw [gcs]; exact Finset.card_image_le)
            (by rw [bcs]; exact Finset.card_image_le)
      _ = 2 * q + 3 := by
          simp only [Finset.card_univ, Fintype.card_fin]; omega
  · intro κ hκ
    exact (decomp_isCell hC hCne hs hmono hbnd κ hκ).1
  · intro j
    rw [cfs, Finset.mem_union]
    left
    rw [mem_gcs]
    refine ⟨Fin.succ (Fin.castSucc j), ?_⟩
    have : (fun x => lvl s x (Fin.succ (Fin.castSucc j))) = s j := by funext x; simp
    rw [this]
    rfl
  · intro κ hκ
    rcases mem_cfs.mp hκ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ⟨fun x => lvl s x i, continuous_lvl hs i, rfl⟩
    · refine Or.inr ⟨fun x => lvl s x (Fin.castSucc i), fun x => lvl s x i.succ,
        continuous_lvl hs _, continuous_lvl hs _, ?_, rfl⟩
      intro x hx
      exact (strictMono_lvl (hmono x hx) (hbnd x hx)) Fin.castSucc_lt_succ

end Work.WilE7
