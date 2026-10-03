import Mathlib
import Submission.Work.FIArea7.P231Defs
import Submission.Work.FIArea7.P231.LBilinStar_eq_epsSums
import Submission.Work.FIArea7.P231M.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea7.P231M

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The Dirichlet symbol is bounded by `1` -/

theorem normDirichletSymLeOne (e w : GaussianInt) :
    ‖(((Work.FIArea7.DirichletSym e w : ℤ)) : ℂ)‖ ≤ 1 := by
  have h : |(((Work.FIArea7.DirichletSym e w : ℤ)) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast Work.FIArea7.abs_dirichletSym_le_one e w
  rwa [Complex.norm_intCast]

/-! ## 2. The number of primary primitive elements of norm `c` -/

theorem primaryPrimSetCardLeTau (c : ℕ) :
    (Work.FIArea7.primaryPrimSet c).card ≤ c.divisors.card := by
  refine le_trans (Finset.card_le_card ?_) (Work.FIArea7.primarySet_card_le_tau c)
  intro z hz
  rw [Work.FIArea7.mem_primaryPrimSet] at hz
  rw [Work.FIArea7.mem_primarySet]
  exact ⟨hz.1, hz.2.1⟩

/-! ## 3. Vanishing and congruence of `epsSummand` -/

lemma epsSummand_eq_zero_of_left_zero {σ w z : GaussianInt} {A B : GaussianInt → ℂ}
    (h : A w = 0) : Work.FIArea7.epsSummand σ A B w z = 0 := by
  rw [Work.FIArea7.epsSummand]
  split
  · simp [h]
  · rfl

lemma epsSummand_eq_zero_of_right_zero {σ w z : GaussianInt} {A B : GaussianInt → ℂ}
    (h : B z = 0) : Work.FIArea7.epsSummand σ A B w z = 0 := by
  rw [Work.FIArea7.epsSummand]
  split
  · simp [h]
  · rfl

lemma epsSummand_congr_left {σ w z : GaussianInt} {A A' B : GaussianInt → ℂ}
    (h : A w = A' w) : Work.FIArea7.epsSummand σ A B w z = Work.FIArea7.epsSummand σ A' B w z := by
  rw [Work.FIArea7.epsSummand, Work.FIArea7.epsSummand]
  split <;> simp [h]

lemma epsSummand_congr_right {σ w z : GaussianInt} {A B B' : GaussianInt → ℂ}
    (h : B z = B' z) : Work.FIArea7.epsSummand σ A B w z = Work.FIArea7.epsSummand σ A B' w z := by
  rw [Work.FIArea7.epsSummand, Work.FIArea7.epsSummand]
  split <;> simp [h]

lemma epsSummand_eq_zero_of_not_prim_left {σ w z : GaussianInt} {A B : GaussianInt → ℂ}
    (hw : Work.FIPlan.IsPrimary w) (hz : Work.FIPlan.IsPrimary z)
    (hnp : ¬ IsCoprime w.re w.im) : Work.FIArea7.epsSummand σ A B w z = 0 := by
  rw [Work.FIArea7.epsSummand]
  split
  · have h0 : Work.FIArea7.JKSym (w * z) = 0 :=
      Work.FIArea7.P231.JKSym_mul_eq_zero_of_not_isCoprime_primary' hw hz hnp
    simp [h0]
  · rfl

/-! ## 4. The coefficients restricted to the discs -/

@[simp] lemma restrDisc_apply_of_notMem {N : ℕ} {B : GaussianInt → ℂ} {z : GaussianInt}
    (hz : z ∉ Work.FIArea7.primaryDisc N) : restrDisc N B z = 0 := by
  show (if z ∈ Work.FIArea7.primaryDisc N then B z else 0) = 0
  rw [if_neg hz]

@[simp] lemma restrDisc_apply_of_mem {N : ℕ} {B : GaussianInt → ℂ} {z : GaussianInt}
    (hz : z ∈ Work.FIArea7.primaryDisc N) : restrDisc N B z = B z := by
  show (if z ∈ Work.FIArea7.primaryDisc N then B z else 0) = B z
  rw [if_pos hz]

@[simp] lemma restrPrim_apply_of_notMem {M : ℕ} {A : GaussianInt → ℂ} {w : GaussianInt}
    (hw : w ∉ primDisc M) : restrPrim M A w = 0 := by
  show (if w ∈ primDisc M then A w else 0) = 0
  rw [if_neg hw]

@[simp] lemma restrPrim_apply_of_mem {M : ℕ} {A : GaussianInt → ℂ} {w : GaussianInt}
    (hw : w ∈ primDisc M) : restrPrim M A w = A w := by
  show (if w ∈ primDisc M then A w else 0) = A w
  rw [if_pos hw]

lemma primaryDisc_subset_gBox (M : ℕ) :
    Work.FIArea7.primaryDisc M ⊆ Work.FIPlan.gBox ((M : ℤ)) :=
  fun _ hz => (Finset.mem_filter.mp hz).1

lemma primDisc_subset_gBox (M : ℕ) :
    primDisc M ⊆ Work.FIPlan.gBox ((M : ℤ)) :=
  fun _ hw => (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1

/-! ## 5. The box sums with restricted coefficients = the sums over the primary discs -/

theorem epsSumsGboxEqPrimaryDisc (σ : GaussianInt) (M N : ℕ) (A B : GaussianInt → ℂ) :
    (∑ w ∈ Work.FIPlan.gBox ((M : ℤ)), ∑ z ∈ Work.FIPlan.gBox ((N : ℤ)),
        Work.FIArea7.epsSummand σ (restrPrim M A) (restrDisc N B) w z)
      = ∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
          Work.FIArea7.epsSummand σ A B w z := by
  classical
  -- (A) for fixed `w`, replace the `z`-box sum by the primary disc
  have stepA : ∀ w : GaussianInt,
      (∑ z ∈ Work.FIPlan.gBox ((N : ℤ)),
          Work.FIArea7.epsSummand σ (restrPrim M A) (restrDisc N B) w z)
        = ∑ z ∈ Work.FIArea7.primaryDisc N,
            Work.FIArea7.epsSummand σ (restrPrim M A) B w z := by
    intro w
    have h2 : (∑ z ∈ Work.FIPlan.gBox ((N : ℤ)),
          Work.FIArea7.epsSummand σ (restrPrim M A) (restrDisc N B) w z)
        = ∑ z ∈ Work.FIArea7.primaryDisc N,
            Work.FIArea7.epsSummand σ (restrPrim M A) (restrDisc N B) w z :=
      (Finset.sum_subset (primaryDisc_subset_gBox N)
        (fun z _ hz => epsSummand_eq_zero_of_right_zero (restrDisc_apply_of_notMem hz))).symm
    rw [h2]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [epsSummand_congr_right (restrDisc_apply_of_mem hz)]
  -- (B) for fixed `z`, replace the `w`-box sum (restricted coefficient) by `primDisc M`
  have stepB : ∀ z : GaussianInt,
      (∑ w ∈ Work.FIPlan.gBox ((M : ℤ)),
          Work.FIArea7.epsSummand σ (restrPrim M A) B w z)
        = ∑ w ∈ primDisc M, Work.FIArea7.epsSummand σ A B w z := by
    intro z
    have h1 : (∑ w ∈ Work.FIPlan.gBox ((M : ℤ)),
          Work.FIArea7.epsSummand σ (restrPrim M A) B w z)
        = ∑ w ∈ primDisc M, Work.FIArea7.epsSummand σ (restrPrim M A) B w z :=
      (Finset.sum_subset (primDisc_subset_gBox M)
        (fun w _ hw => epsSummand_eq_zero_of_left_zero (restrPrim_apply_of_notMem hw))).symm
    rw [h1]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [epsSummand_congr_left (restrPrim_apply_of_mem hw)]
  -- (C) for a primary `z`, the non-primitive primary `w` contribute nothing
  have stepC : ∀ z ∈ Work.FIArea7.primaryDisc N,
      (∑ w ∈ Work.FIArea7.primaryDisc M, Work.FIArea7.epsSummand σ A B w z)
        = ∑ w ∈ primDisc M, Work.FIArea7.epsSummand σ A B w z := by
    intro z hz
    have hzP : Work.FIPlan.IsPrimary z := (Work.FIArea7.mem_primaryDisc.mp hz).1
    have hmain : (∑ w ∈ primDisc M, Work.FIArea7.epsSummand σ A B w z)
        = ∑ w ∈ Work.FIArea7.primaryDisc M, Work.FIArea7.epsSummand σ A B w z := by
      refine Finset.sum_subset (fun w hw => ?_) (fun w hwP hwnot => ?_)
      · exact Work.FIArea7.mem_primaryDisc.mpr
          ⟨(mem_primDisc.mp hw).1, (mem_primDisc.mp hw).2.2⟩
      · have hwPP : Work.FIPlan.IsPrimary w := (Work.FIArea7.mem_primaryDisc.mp hwP).1
        have hgn : Work.FIPlan.gnorm w ≤ M := (Work.FIArea7.mem_primaryDisc.mp hwP).2
        have hnp : ¬ IsCoprime w.re w.im := fun hc =>
          hwnot (mem_primDisc.mpr ⟨hwPP, hc, hgn⟩)
        exact epsSummand_eq_zero_of_not_prim_left hwPP hzP hnp
    exact hmain.symm
  calc (∑ w ∈ Work.FIPlan.gBox ((M : ℤ)), ∑ z ∈ Work.FIPlan.gBox ((N : ℤ)),
        Work.FIArea7.epsSummand σ (restrPrim M A) (restrDisc N B) w z)
      = ∑ w ∈ Work.FIPlan.gBox ((M : ℤ)), ∑ z ∈ Work.FIArea7.primaryDisc N,
          Work.FIArea7.epsSummand σ (restrPrim M A) B w z :=
        Finset.sum_congr rfl (fun w _ => stepA w)
    _ = ∑ z ∈ Work.FIArea7.primaryDisc N, ∑ w ∈ Work.FIPlan.gBox ((M : ℤ)),
          Work.FIArea7.epsSummand σ (restrPrim M A) B w z := Finset.sum_comm
    _ = ∑ z ∈ Work.FIArea7.primaryDisc N, ∑ w ∈ primDisc M,
          Work.FIArea7.epsSummand σ A B w z :=
        Finset.sum_congr rfl (fun z _ => stepB z)
    _ = ∑ z ∈ Work.FIArea7.primaryDisc N, ∑ w ∈ Work.FIArea7.primaryDisc M,
          Work.FIArea7.epsSummand σ A B w z :=
        Finset.sum_congr rfl (fun z hz => (stepC z hz).symm)
    _ = ∑ w ∈ Work.FIArea7.primaryDisc M, ∑ z ∈ Work.FIArea7.primaryDisc N,
          Work.FIArea7.epsSummand σ A B w z := Finset.sum_comm

end

end Work.FIArea7.P231M
