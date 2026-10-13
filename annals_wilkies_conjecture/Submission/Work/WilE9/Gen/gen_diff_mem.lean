/-
  Work.WilE9.Gen.gen_diff_mem — membership lemmas: the generic quantifier/projection steps,
  the atoms at a `snoc`ed point, the chain, and the coordinates of the chain points.
-/
import Submission.Work.WilE9.Gen.gen_diff_gen
import Submission.Work.WilE9.Glue.a7_core
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Gen

namespace DiffSet

open WilkiesDesign WilkiesDesign.E

/-! ## 11. Membership lemmas: quantifiers and projections -/

lemma mem_forall_last {m : ℕ} {X : Set (Fin (m + 1) → ℝ)} (w : Fin m → ℝ) :
    w ∈ (projLast Xᶜ)ᶜ ↔ ∀ t : ℝ, Fin.snoc w t ∈ X := by
  rw [Set.mem_compl_iff, projLast]
  simp only [Set.mem_ofPred_eq, not_exists, Set.mem_compl_iff, not_not]

lemma mem_forall_block {m k : ℕ} {X : Set (Fin (m + k) → ℝ)} (w : Fin m → ℝ) :
    w ∈ (Work.WilG0.projLastIter m k Xᶜ)ᶜ ↔
      ∀ u : Fin k → ℝ, Work.WilG0.snocIt m k w u ∈ X := by
  rw [Set.mem_compl_iff, Work.WilG0.projLastIter_eq m k Xᶜ]
  simp only [Set.mem_ofPred_eq, not_exists, Set.mem_compl_iff, not_not]

lemma mem_projLast {m : ℕ} {X : Set (Fin (m + 1) → ℝ)} (w : Fin m → ℝ) :
    w ∈ projLast X ↔ ∃ t : ℝ, Fin.snoc w t ∈ X := by
  rw [projLast]
  simp only [Set.mem_ofPred_eq]

/-! ## 12. Membership: the atoms at a `snoc`ed point -/

lemma dmem_A3 (n : ℕ) {z : Fin (dd4 n) → ℝ} {h : ℝ} :
    (Fin.snoc z h : Fin (dd3 n) → ℝ) ∈ dA3 n ↔ 0 < |h| := by
  rw [dA3, Set.mem_ofPred_eq, snoc_dhI3, abs_pos]

lemma dmem_A4 (n : ℕ) {z : Fin (dd4 n) → ℝ} {h : ℝ} :
    (Fin.snoc z h : Fin (dd3 n) → ℝ) ∈ dA4 n ↔ |h| < z (ddI4 n) := by
  rw [dA4, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, snoc_ddI3, snoc_dhI3]
  constructor
  · rintro ⟨h1, h2⟩
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩
  · intro hh
    rw [abs_lt] at hh
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma dmem_A5 {n : ℕ} {i : Fin n} {z : Fin (dd3 n) → ℝ} {u : Fin n → ℝ} :
    (Work.WilG0.snocIt (dd3 n) n z u) ∈ dA5 n i ↔
      ∀ j : Fin n, u j = z (dvI3 n (Fin.castSucc j)) + z (dhI3 n) *
        (if j = i then (1 : ℝ) else 0) := by
  rw [dA5]
  constructor
  · intro h j
    have hj := Set.mem_iInter.mp h j
    rw [Set.mem_ofPred_eq, snocIt_dxI2, snocIt_dvI2, snocIt_dhI2] at hj
    exact hj
  · intro h
    rw [Set.mem_iInter]
    intro j
    rw [Set.mem_ofPred_eq, snocIt_dxI2, snocIt_dvI2, snocIt_dhI2]
    exact h j

lemma dmem_GB {n : ℕ} {G : Set (Fin (n + 1) → ℝ)} {z : Fin (dd1 n) → ℝ} {v' : ℝ} :
    (Fin.snoc z v' : Fin (dd0 n) → ℝ) ∈ dGB n G ↔
      Fin.snoc (fun j : Fin n => z (dxI1 n j)) v' ∈ G := by
  simp only [dGB, Set.mem_ofPred_eq, snoc_dxI0, snoc_dvpI0]

lemma dmem_GA {n : ℕ} {G : Set (Fin (n + 1) → ℝ)} {z : Fin (dd2 n) → ℝ} {y : ℝ} :
    (Fin.snoc z y : Fin (dd1 n) → ℝ) ∈ dGA n G ↔
      Fin.snoc (fun j : Fin n => z (dvI2 n (Fin.castSucc j))) y ∈ G := by
  simp only [dGA, Set.mem_ofPred_eq, snoc_dvI1, snoc_dyI1]

lemma dmem_A7 (n : ℕ) {z : Fin (dd1 n) → ℝ} {v' : ℝ} :
    (Fin.snoc z v' : Fin (dd0 n) → ℝ) ∈ dA7 n ↔
      |z (dvI1 n (Fin.last n)) - (v' - z (dyI1 n)) / z (dhI1 n)| < z (deI1 n) := by
  rw [dA7, Set.mem_ofPred_eq, snoc_deI0, snoc_dhI0, snoc_dvpI0, snoc_dyI0, snoc_dvI0]
  rw [Glue.a7_core]

/-! ## 13. Membership lemmas for the chain -/

lemma mem_E1_iff (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) {z : Fin (dd1 n) → ℝ} :
    z ∈ dE1 n G ↔ ∀ v' : ℝ, Fin.snoc (fun j : Fin n => z (dxI1 n j)) v' ∈ G →
      |z (dvI1 n (Fin.last n)) - (v' - z (dyI1 n)) / z (dhI1 n)| < z (deI1 n) := by
  rw [dE1, mem_forall_last]
  refine forall_congr' (fun v' => ?_)
  rw [dD1, Set.mem_union, Set.mem_compl_iff, dmem_GB, dmem_A7]
  constructor
  · intro H hGB; rcases H with H | H
    · exact absurd hGB H
    · exact H
  · intro H
    by_cases hGB : Fin.snoc (fun j : Fin n => z (dxI1 n j)) v' ∈ G
    · exact Or.inr (H hGB)
    · exact Or.inl hGB

lemma mem_E2_iff (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) {z : Fin (dd2 n) → ℝ} :
    z ∈ dE2 n G ↔ ∀ y : ℝ, Fin.snoc (fun j : Fin n => z (dvI2 n (Fin.castSucc j))) y ∈ G →
      Fin.snoc z y ∈ dE1 n G := by
  rw [dE2, mem_forall_last]
  refine forall_congr' (fun y => ?_)
  rw [dD2, Set.mem_union, Set.mem_compl_iff, dmem_GA]
  constructor
  · intro H hGA; rcases H with H | H
    · exact absurd hGA H
    · exact H
  · intro H
    by_cases hGA : Fin.snoc (fun j : Fin n => z (dvI2 n (Fin.castSucc j))) y ∈ G
    · exact Or.inr (H hGA)
    · exact Or.inl hGA

lemma mem_E3_iff (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) {z : Fin (dd3 n) → ℝ} :
    z ∈ dE3 n i G ↔ ∀ u : Fin n → ℝ,
      (∀ j : Fin n, u j = z (dvI3 n (Fin.castSucc j)) + z (dhI3 n) *
        (if j = i then (1 : ℝ) else 0)) →
      Work.WilG0.snocIt (dd3 n) n z u ∈ dE2 n G := by
  rw [dE3, mem_forall_block]
  refine forall_congr' (fun u => ?_)
  rw [dD3, Set.mem_union, Set.mem_compl_iff, dmem_A5]
  constructor
  · intro H hA5; rcases H with H | H
    · exact absurd hA5 H
    · exact H
  · intro H
    by_cases hA5 : ∀ j : Fin n, u j = z (dvI3 n (Fin.castSucc j)) + z (dhI3 n) *
        (if j = i then (1 : ℝ) else 0)
    · exact Or.inr (H hA5)
    · exact Or.inl hA5

lemma mem_E4_iff (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) {z : Fin (dd4 n) → ℝ} :
    z ∈ dE4 n i G ↔ ∀ h : ℝ, 0 < |h| → |h| < z (ddI4 n) →
      Fin.snoc z h ∈ dE3 n i G := by
  rw [dE4, mem_forall_last]
  refine forall_congr' (fun h => ?_)
  rw [dD4, Set.mem_union, Set.mem_union, Set.mem_compl_iff, Set.mem_compl_iff,
    dmem_A3, dmem_A4]
  constructor
  · intro H h1 h2; rcases H with H | H
    · exact absurd h1 H
    · rcases H with H | H
      · exact absurd h2 H
      · exact H
  · intro H
    by_cases h1 : 0 < |h|
    · by_cases h2 : |h| < z (ddI4 n)
      · exact Or.inr (Or.inr (H h1 h2))
      · exact Or.inr (Or.inl h2)
    · exact Or.inl h1

lemma mem_E5_iff (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) {z : Fin (dd5 n) → ℝ} :
    z ∈ dE5 n i G ↔ ∃ δ : ℝ, 0 < δ ∧ Fin.snoc z δ ∈ dE4 n i G := by
  rw [dE5, mem_projLast]
  refine exists_congr (fun δ => ?_)
  simp only [Set.mem_inter_iff, dA2, Set.mem_ofPred_eq, snoc_ddI4]

lemma mem_E6_iff (n : ℕ) (i : Fin n) (G : Set (Fin (n + 1) → ℝ)) {w : Fin (n + 1) → ℝ} :
    w ∈ dE6 n i G ↔ ∀ ε : ℝ, 0 < ε → Fin.snoc w ε ∈ dE5 n i G := by
  rw [dE6, mem_forall_last]
  refine forall_congr' (fun ε => ?_)
  rw [Set.mem_union, Set.mem_compl_iff, dA1, Set.mem_ofPred_eq, snoc_deI5]
  constructor
  · intro H hε; rcases H with H | H
    · exact absurd hε H
    · exact H
  · intro H
    by_cases hε : 0 < ε
    · exact Or.inr (H hε)
    · exact Or.inl hε

/-! ## 14. Reading the coordinates of the chain points -/

lemma acc4_ddI4 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ : ℝ) :
    (Fin.snoc (Fin.snoc w ε) δ : Fin (dd4 n) → ℝ) (ddI4 n) = δ :=
  snoc_ddI4 n (Fin.snoc w ε) δ

lemma acc3_vI3g (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (k : Fin (n + 1)) :
    (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h : Fin (dd3 n) → ℝ) (dvI3 n k) = w k := by
  simp only [dvI3, dvI4, dvI5, dvI6, Fin.snoc_castSucc]

lemma acc3_vI3 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (j : Fin n) :
    (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h : Fin (dd3 n) → ℝ) (dvI3 n (Fin.castSucc j))
      = Fin.init w j := by
  rw [acc3_vI3g]
  rfl

lemma acc3_hI3 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) :
    (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h : Fin (dd3 n) → ℝ) (dhI3 n) = h :=
  snoc_dhI3 n (Fin.snoc (Fin.snoc w ε) δ) h

lemma acc2_vI2 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (j : Fin n) :
    (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u)
      (dvI2 n (Fin.castSucc j)) = Fin.init w j := by
  rw [snocIt_dvI2]
  exact acc3_vI3 n w ε δ h j

lemma acc2_xI2 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (j : Fin n) :
    (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u)
      (dxI2 n j) = u j :=
  snocIt_dxI2 n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u j

lemma acc1_vI2 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y : ℝ)
    (j : Fin n) :
    (Fin.snoc (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y :
      Fin (dd1 n) → ℝ) (dvI1 n (Fin.castSucc j)) = Fin.init w j := by
  rw [snoc_dvI1]
  exact acc2_vI2 n w ε δ h u j

lemma acc1_xI1 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y : ℝ)
    (j : Fin n) :
    (Fin.snoc (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y :
      Fin (dd1 n) → ℝ) (dxI1 n j) = u j := by
  rw [snoc_dxI1]
  exact acc2_xI2 n w ε δ h u j

lemma acc1_yI1 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y : ℝ) :
    (Fin.snoc (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y :
      Fin (dd1 n) → ℝ) (dyI1 n) = y :=
  snoc_dyI1 n (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y

lemma acc1_vI1 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y : ℝ)
    (k : Fin (n + 1)) :
    (Fin.snoc (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y :
      Fin (dd1 n) → ℝ) (dvI1 n k) = w k := by
  rw [snoc_dvI1, snocIt_dvI2]
  exact acc3_vI3g n w ε δ h k

lemma acc1_hI1 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y : ℝ) :
    (Fin.snoc (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y :
      Fin (dd1 n) → ℝ) (dhI1 n) = h := by
  rw [snoc_dhI1, snocIt_dhI2]
  exact acc3_hI3 n w ε δ h

lemma acc1_eI1 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y : ℝ) :
    (Fin.snoc (Work.WilG0.snocIt (dd3 n) n (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y :
      Fin (dd1 n) → ℝ) (deI1 n) = ε := by
  rw [snoc_deI1, snocIt_deI2, snoc_deI3, snoc_deI4, snoc_deI5]

lemma acc0_xI0 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y v' : ℝ)
    (j : Fin n) :
    (Fin.snoc (Fin.snoc (Work.WilG0.snocIt (dd3 n) n
      (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y) v' : Fin (dd0 n) → ℝ) (dxI0 n j) = u j := by
  rw [snoc_dxI0, snoc_dxI1]
  exact acc2_xI2 n w ε δ h u j

lemma acc0_vpI0 (n : ℕ) (w : Fin (n + 1) → ℝ) (ε δ h : ℝ) (u : Fin n → ℝ) (y v' : ℝ) :
    (Fin.snoc (Fin.snoc (Work.WilG0.snocIt (dd3 n) n
      (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y) v' : Fin (dd0 n) → ℝ) (dvpI0 n) = v' :=
  snoc_dvpI0 n (Fin.snoc (Work.WilG0.snocIt (dd3 n) n
    (Fin.snoc (Fin.snoc (Fin.snoc w ε) δ) h) u) y) v'

end DiffSet

end Work.WilE9.Gen
