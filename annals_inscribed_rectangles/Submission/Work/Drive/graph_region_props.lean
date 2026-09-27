import Mathlib
import Submission.Work.Drive.BoxParityDefs

namespace Work.Drive

open scoped Topology
open Set

open Submission.Drive

/-- The `i`-th coordinate of a point of the graph of `η` (over the `i`-th coordinate) recovers the
parameter. -/
private lemma coord_graph {m : ℕ} (i : Fin (m + 1)) {η : ℝ → Amb m} (hη : ∀ u, η u i = 0)
    (u : ℝ) : (u • EuclideanSpace.single i (1 : ℝ) + η u : Amb m) i = u := by
  simp [PiLp.add_apply, PiLp.smul_apply, hη]

/-- Off the graph of `η`, the difference `x - (x i) • e_i - η (x i)` vanishes exactly on the graph. -/
private lemma graph_sub_eq_zero {m : ℕ} (i : Fin (m + 1)) {η : ℝ → Amb m} (hη : ∀ u, η u i = 0)
    (u : ℝ) :
    (u • EuclideanSpace.single i (1 : ℝ) + η u : Amb m)
      - ((u • EuclideanSpace.single i (1 : ℝ) + η u : Amb m) i) • EuclideanSpace.single i (1 : ℝ)
      - η ((u • EuclideanSpace.single i (1 : ℝ) + η u : Amb m) i) = 0 := by
  have h1 := coord_graph i hη u
  rw [h1]
  abel

/-- The parametrisation of the graph of `η` is continuous. -/
private lemma graph_continuous {m : ℕ} (i : Fin (m + 1)) {η : ℝ → Amb m} (hηc : Continuous η) :
    Continuous (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u) :=
  (continuous_id.smul continuous_const).add hηc

theorem graph_region_props {m : ℕ} {F : Work.Drive.Amb m → Work.Drive.Tgt m} {p : Work.Drive.Amb m}
    (i : Fin (m + 1)) (η : ℝ → Work.Drive.Amb m) {δ ρ δ' ρ' : ℝ}
    (hηc : Continuous η) (hρ' : 0 < ρ') (hδ' : 0 < δ') (hδ'δ : δ' < δ) (hρ'ρ : ρ' < ρ)
    (hη : ∀ u, η u i = 0) (hzero : ∀ u, |u - p i| < δ → F (u • EuclideanSpace.single i 1 + η u) = 0)
    (hnf : ∀ x, |x i - p i| < δ → ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ →
      (F x = 0 ↔ x = (x i) • EuclideanSpace.single i 1 + η (x i))) :
    (Work.Drive.zeroSet F ∩ {x : Work.Drive.Amb m | |x i - p i| < δ' ∧
        ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ'}
        = {x : Work.Drive.Amb m | x ∈ Submission.Drive.unitBox m ∧
            (∃ u, |u - p i| < δ' ∧ x = u • EuclideanSpace.single i 1 + η u)}) ∧
    (Work.Drive.zeroSet F ∩ closure {x : Work.Drive.Amb m | |x i - p i| < δ' ∧
        ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ'}
        = {x : Work.Drive.Amb m | x ∈ Submission.Drive.unitBox m ∧
            (∃ u, |u - p i| ≤ δ' ∧ x = u • EuclideanSpace.single i 1 + η u)}) ∧
    (Work.Drive.zeroSet F ∩ frontier {x : Work.Drive.Amb m | |x i - p i| < δ' ∧
        ‖x - (x i) • EuclideanSpace.single i 1 - η (x i)‖ < ρ'}
        ⊆ {(p i - δ') • EuclideanSpace.single i 1 + η (p i - δ'),
           (p i + δ') • EuclideanSpace.single i 1 + η (p i + δ')}) := by
  have hc1 : Continuous (fun x : Amb m => |x i - p i|) := by fun_prop
  have hc2 : Continuous
      (fun x : Amb m => ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖) := by fun_prop
  have hAopen : IsOpen {x : Amb m | |x i - p i| < δ' ∧
      ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ'} := by
    apply IsOpen.inter
    · exact isOpen_lt hc1 continuous_const
    · exact isOpen_lt hc2 continuous_const
  have hAclB : closure {x : Amb m | |x i - p i| < δ' ∧
        ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ'}
      ⊆ {x : Amb m | |x i - p i| ≤ δ' ∧
        ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ ≤ ρ'} := by
    apply closure_minimal
    · rintro x ⟨h1, h2⟩
      exact ⟨le_of_lt h1, le_of_lt h2⟩
    · apply IsClosed.inter
      · exact isClosed_le hc1 continuous_const
      · exact isClosed_le hc2 continuous_const
  have hγc : Continuous (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u) :=
    graph_continuous i hηc
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: the open piece
    apply Set.Subset.antisymm
    · rintro x ⟨hxz, hxi, hxd⟩
      obtain ⟨hxbox, hxF⟩ := hxz
      have h1 : |x i - p i| < δ := lt_trans hxi hδ'δ
      have h2 : ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ := lt_trans hxd hρ'ρ
      have heq : x = (x i) • EuclideanSpace.single i (1 : ℝ) + η (x i) := (hnf x h1 h2).mp hxF
      exact ⟨hxbox, ⟨x i, hxi, heq⟩⟩
    · rintro x ⟨hxbox, u, hu, rfl⟩
      refine ⟨⟨hxbox, hzero u (lt_trans hu hδ'δ)⟩, ?_, ?_⟩
      · rwa [coord_graph i hη u]
      · rw [graph_sub_eq_zero i hη u, norm_zero]
        exact hρ'
  · -- Part 2: the closure
    apply Set.Subset.antisymm
    · rintro x ⟨hxz, hxcl⟩
      obtain ⟨hxbox, hxF⟩ := hxz
      obtain ⟨hxi, hxd⟩ := hAclB hxcl
      have h1 : |x i - p i| < δ := lt_of_le_of_lt hxi hδ'δ
      have h2 : ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ := lt_of_le_of_lt hxd hρ'ρ
      have heq : x = (x i) • EuclideanSpace.single i (1 : ℝ) + η (x i) := (hnf x h1 h2).mp hxF
      exact ⟨hxbox, ⟨x i, hxi, heq⟩⟩
    · rintro x ⟨hxbox, u, hu, rfl⟩
      refine ⟨⟨hxbox, hzero u (lt_of_le_of_lt hu hδ'δ)⟩, ?_⟩
      -- the point γ u lies in the closure of the open piece
      have hSI : {u : ℝ | |u - p i| < δ'} = Set.Ioo (p i - δ') (p i + δ') := by
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_Ioo, abs_lt]
        constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
      have hu_cl : u ∈ closure {u : ℝ | |u - p i| < δ'} := by
        rw [hSI, closure_Ioo (by linarith)]
        rw [Set.mem_Icc]
        rw [abs_le] at hu
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hsub : (fun u : ℝ => u • EuclideanSpace.single i (1 : ℝ) + η u) ''
            {u : ℝ | |u - p i| < δ'}
          ⊆ {x : Amb m | |x i - p i| < δ' ∧
            ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ'} := by
        rintro y ⟨t, ht, rfl⟩
        exact ⟨by rwa [coord_graph i hη t], by rw [graph_sub_eq_zero i hη t, norm_zero]; exact hρ'⟩
      exact closure_mono hsub (image_closure_subset_closure_image hγc ⟨u, hu_cl, rfl⟩)
  · -- Part 3: the frontier collapses to the two endpoints
    intro x hx
    obtain ⟨hxz, hxfr⟩ := hx
    obtain ⟨hxbox, hxF⟩ := hxz
    have hxsplit : x ∈ closure {x : Amb m | |x i - p i| < δ' ∧
          ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ'} ∧
        x ∉ interior {x : Amb m | |x i - p i| < δ' ∧
          ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ'} := by
      have h := hxfr
      rw [← closure_sdiff_interior] at h
      exact h
    obtain ⟨hxcl, hxni⟩ := hxsplit
    obtain ⟨hxi, hxd⟩ := hAclB hxcl
    have h1 : |x i - p i| < δ := lt_of_le_of_lt hxi hδ'δ
    have h2 : ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ := lt_of_le_of_lt hxd hρ'ρ
    have heq : x = (x i) • EuclideanSpace.single i (1 : ℝ) + η (x i) := (hnf x h1 h2).mp hxF
    have hxieq : |x i - p i| = δ' := by
      rcases lt_or_eq_of_le hxi with hlt | heq'
      · exfalso
        have hdx : x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i) = 0 := by
          nth_rewrite 1 [heq]; abel
        have hxA : x ∈ {x : Amb m | |x i - p i| < δ' ∧
            ‖x - (x i) • EuclideanSpace.single i (1 : ℝ) - η (x i)‖ < ρ'} :=
          ⟨hlt, by rw [hdx, norm_zero]; exact hρ'⟩
        exact hxni (by rw [hAopen.interior_eq]; exact hxA)
      · exact heq'
    rcases (abs_eq hδ'.le).mp hxieq with hcase | hcase
    · right
      have hxi' : x i = p i + δ' := by linarith
      rw [hxi'] at heq
      exact heq
    · left
      have hxi' : x i = p i - δ' := by linarith
      rw [hxi'] at heq
      exact heq

end Work.Drive
