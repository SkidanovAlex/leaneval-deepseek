import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG4a.iteratedDeriv_snoc
import Submission.Work.WilG4a.signConst_ivt
import Submission.Work.WilG4a.continuousOn_iteratedDeriv
import Submission.Work.WilG4a.slice_contDiffAt
import Submission.Work.WilG4a.mvpoly_eval_mono
import Submission.Work.WilG4a.degree_poly_comp
import Submission.Work.WilG4a.count_poly_comp
import Submission.Work.WilG4a.badLocus_derivZeroSet_uniform
import Submission.Work.WilG4a.exists_cell_partition_refining

open Classical WilkiesDesign WilkiesConjecture

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.WilG4a

theorem signConst_decomposition (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p : ℕ) (F0 : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ), ∀ (D r k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc ∧ ∃ (κ : Fin m → Set (Fin (p + 1) → ℝ)), (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1)) ∧ (∀ z : Fin (p + 1) → ℝ, ∃ σ, z ∈ κ σ) ∧ (∀ σ σ' : Fin m, σ ≠ σ' → Disjoint (κ σ) (κ σ')) ∧ (∀ σ (l : Fin p → ℝ), (∃ x : ℝ, Fin.snoc l x ∈ κ σ) → (∃ x : ℝ, Work.WilG4a.fibre (κ σ) l = {x}) ∨ (∃ a b : EReal, Work.WilG4a.fibre (κ σ) l = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b})) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) j) ∨ κ σ ⊆ Work.WilG4a.badLocus (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 1 → ∀ (l : Fin p → ℝ) (u v : ℝ), u < v → Set.Ioo u v ⊆ Work.WilG4a.fibre (κ σ) l → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) (r + 2)) → (Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) → (∀ x ∈ Set.Ioo u v, ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x) ∧ ((∀ x ∈ Set.Ioo u v, 0 ≤ iteratedDeriv j (fun y : ℝ => F i l y) x) ∨ (∀ x ∈ Set.Ioo u v, iteratedDeriv j (fun y : ℝ => F i l y) x ≤ 0))) := by
  obtain ⟨aU, B, hU⟩ := badLocus_derivZeroSet_uniform S hder p F0
  obtain ⟨aC, bC, cC, hC⟩ := exists_cell_partition_refining S hcd aU (p + 1)
  obtain ⟨b, hb⟩ := degree_poly_comp B cC
  obtain ⟨cc, hcc⟩ := count_poly_comp bC B
  refine ⟨aC, b, cc, ?_⟩
  intro D r k F hF
  let X : Fin 2 × Fin k × Fin (r + 3) → Set (Fin (p + 1) → ℝ) :=
    fun t => if t.1 = 0 then badLocus (F t.2.1) t.2.2.val else derivZeroSet (F t.2.1) t.2.2.val
  have hX : ∀ t : Fin 2 × Fin k × Fin (r + 3),
      X t ∈ S.Ω aU (MvPolynomial.eval ![D, r] B) (p + 1) := by
    intro t
    have hlt : t.2.2.val ≤ r + 2 := by have := t.2.2.isLt; omega
    have hU' := hU D r (F t.2.1) (hF t.2.1) t.2.2.val hlt
    dsimp only [X]
    split_ifs with h0
    · exact hU'.1
    · exact hU'.2
  obtain ⟨m, hmcard, κ, hκΩ, hκcell, hκcov, hκdisj, hκref⟩ :=
    hC (MvPolynomial.eval ![D, r] B) (Fin 2 × Fin k × Fin (r + 3)) X hX
  have hcard : Fintype.card (Fin 2 × Fin k × Fin (r + 3)) = 2 * (k * (r + 3)) := by
    simp [Fintype.card_prod]
  have hmle : (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc := by
    have h1 := hmcard
    rw [hcard] at h1
    exact le_trans (by exact_mod_cast h1) (hcc D r k)
  refine ⟨m, hmle, κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    have h := hκΩ σ
    rw [← hb D r] at h
    exact h
  · exact hκcov
  · intro σ σ' hne
    exact hκdisj σ σ' hne
  · intro σ l _
    exact isCell_fiber p (hκcell σ) l
  · intro σ i j hj
    have hj' : j < r + 3 := by omega
    have hX0 : X ((0 : Fin 2), i, (⟨j, hj'⟩ : Fin (r + 3))) = badLocus (F i) j := by simp [X]
    have h := hκref ((0 : Fin 2), i, (⟨j, hj'⟩ : Fin (r + 3))) σ
    rw [hX0] at h
    exact h
  · intro σ i j hj
    have hj' : j < r + 3 := by omega
    have hX1 : X ((1 : Fin 2), i, (⟨j, hj'⟩ : Fin (r + 3))) = derivZeroSet (F i) j := by
      have hne : ¬ ((1 : Fin 2) = 0) := by decide
      simp [X, hne]
    have h := hκref ((1 : Fin 2), i, (⟨j, hj'⟩ : Fin (r + 3))) σ
    rw [hX1] at h
    exact h
  · intro σ i j hj l u v huv hfib hbad hdz
    have hmemb : ∀ x ∈ Set.Ioo u v, Fin.snoc l x ∈ κ σ := by
      intro x hx
      simpa [fibre] using hfib hx
    have hsmooth : ∀ x ∈ Set.Ioo u v,
        Fin.snoc l x ∈ interior {w : Fin (p + 1) → ℝ | ContDiffAt ℝ (r + 2) (famFun (F i)) w} := by
      intro x hx
      have hxnot : Fin.snoc l x ∉ badLocus (F i) (r + 2) :=
        fun hmem => (Set.disjoint_left.mp hbad) (hmemb x hx) hmem
      simpa [badLocus, smoothLocus] using hxnot
    have hj2 : j ≤ r + 2 := by omega
    have hj1 : j + 1 ≤ r + 2 := by omega
    have hcd_r2 : ∀ x ∈ Set.Ioo u v, ContDiffAt ℝ (r + 2) (famFun (F i)) (Fin.snoc l x) :=
      fun x hx => interior_subset (hsmooth x hx)
    have hcd_j : ∀ x ∈ Set.Ioo u v, ContDiffAt ℝ j (famFun (F i)) (Fin.snoc l x) := by
      intro x hx
      exact (hcd_r2 x hx).of_le (by exact_mod_cast hj2)
    have hslice : ∀ x ∈ Set.Ioo u v,
        iteratedDeriv j (fun y : ℝ => F i l y) x =
          iteratedFDeriv ℝ j (famFun (F i)) (Fin.snoc l x)
            (fun _ : Fin j => Pi.single (xDir p) 1) := by
      intro x hx
      have h := iteratedDeriv_snoc p (famFun (F i)) l x j (hcd_j x hx)
      simpa only [famFun_apply, xDir] using h
    have h1 : ∀ x ∈ Set.Ioo u v, ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x := by
      intro x hx
      have h := slice_contDiffAt p (famFun (F i)) (r + 2) l x (hsmooth x hx)
      have h' : ContDiffAt ℝ (((r + 2 : ℕ)) : WithTop ℕ∞) (fun y : ℝ => F i l y) x := by
        simpa only [famFun_apply] using h
      exact h'.of_le (by exact_mod_cast (le_refl (r + 2)))
    refine ⟨h1, ?_⟩
    have hcont : ContinuousOn (fun x : ℝ => iteratedDeriv j (fun y : ℝ => F i l y) x)
        (Set.Ioo u v) :=
      continuousOn_iteratedDeriv (f := fun y : ℝ => F i l y) isOpen_Ioo
        (fun x hx => (h1 x hx).of_le (by exact_mod_cast hj1))
    rcases hdz with hdisj | hsub
    · refine signConst_ivt huv _ hcont (fun x hx => ?_)
      have hxK : Fin.snoc l x ∈ κ σ := hmemb x hx
      have hmem : Fin.snoc l x ∉ derivZeroSet (F i) j :=
        fun h => (Set.disjoint_left.mp hdisj) hxK h
      intro hzero
      exact hmem (by
        refine ⟨?_, ?_⟩
        · refine interior_mono ?_ (hsmooth x hx)
          intro w hw
          have hw' : ContDiffAt ℝ (r + 2) (famFun (F i)) w := hw
          show ContDiffAt ℝ (j : WithTop ℕ∞) (famFun (F i)) w
          exact hw'.of_le (show ((j : ℕ) : WithTop ℕ∞) ≤ ↑(r + 2) by exact_mod_cast hj2)
        · rw [← hslice x hx]; exact hzero)
    · right
      intro x hx
      obtain ⟨-, h0⟩ := hsub (hmemb x hx)
      rw [hslice x hx]
      exact h0.le

end Work.WilG4a
