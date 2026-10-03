import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.prop_11_1_dual
import Submission.Work.FIArea4.prop_11_1_reduce
import Submission.Work.FIArea4.Vflip.VflipAux
import Submission.Work.FIArea4.Vflip.FlipSetup

set_option maxHeartbeats 4000000

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Reduction of the full box `[1,2R]×[1,2S]` to the dyadic boxes (FI §11–12)

This module contains the (purely combinatorial) reduction that lets a *dyadic-box* estimate be
applied to the full box of `Work.FIPlan.Vvar`.  It follows `Work.FIArea4.prop_11_1_reduce`'s
`reduce_core` verbatim, replacing `braceV` by the bracket `p14T12` of Proposition 12.1.

The key point is that only **three** parts are produced (the two strips and all the dyadic cells
together), so that the class sums split by Cauchy–Schwarz with the constant `3`; within the cells
one uses the *weighted* Cauchy–Schwarz with weights `p14T12 D (2^j) (2^k) ε`, whose sum over the
cells is controlled by `p14T12_dyadic_sum_le`. -/

/-- Splitting off the point `1` from `Icc 1 M`. -/
private lemma vfm_Icc_one_split {M : ℕ} (hM : 1 ≤ M) {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ m ∈ Finset.Icc 1 M, f m = f 1 + ∑ m ∈ Finset.Icc 2 M, f m := by
  have h : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, Finset.sum_insert]
  simp only [Finset.mem_Icc]; omega

/-- The dyadic tiling of `Icc 2 (2^{J+1})`. -/
private lemma vfm_Icc_two_pow_tile (J : ℕ) {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ m ∈ Finset.Icc 2 (2^(J+1)), f m
      = ∑ j ∈ Finset.range (J+1), ∑ m ∈ Finset.Ioc (2^j) (2 * 2^j), f m := by
  induction J with
  | zero => norm_num
  | succ J ih =>
      have hset : Finset.Icc 2 (2^(J+1+1))
          = Finset.Icc 2 (2^(J+1)) ∪ Finset.Ioc (2^(J+1)) (2 * 2^(J+1)) := by
        have hp : (2:ℕ)^(J+1+1) = 2 * 2^(J+1) := by rw [pow_succ]; ring
        rw [hp]
        ext m; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
        constructor
        · rintro ⟨h1, h2⟩
          rcases le_or_gt m (2^(J+1)) with h | h
          · exact Or.inl ⟨h1, h⟩
          · exact Or.inr ⟨h, h2⟩
        · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
          · exact ⟨h1, by
              have hpos : (0:ℕ) < 2^(J+1) := by positivity
              nlinarith⟩
          · exact ⟨by omega, h2⟩
      have hdisj : Disjoint (Finset.Icc 2 (2^(J+1))) (Finset.Ioc (2^(J+1)) (2 * 2^(J+1))) := by
        rw [Finset.disjoint_left]; intro m hm hm2
        simp only [Finset.mem_Icc] at hm; simp only [Finset.mem_Ioc] at hm2; omega
      have hR : (∑ j ∈ Finset.range (J+1+1), ∑ m ∈ Finset.Ioc (2^j) (2 * 2^j), f m)
          = (∑ j ∈ Finset.range (J+1), ∑ m ∈ Finset.Ioc (2^j) (2 * 2^j), f m)
            + ∑ m ∈ Finset.Ioc (2^(J+1)) (2 * 2^(J+1)), f m := by
        rw [show J+1+1 = (J+1)+1 from rfl, Finset.sum_range_succ]
      rw [hset, Finset.sum_union hdisj, ih, hR]

/-- **Box decomposition.**  A double sum over the box `[1,2R] × [1,2S]` of a function vanishing
outside the box splits into the two strips (`r = 1` and `r ≠ 1, s = 1`) and the dyadic rectangles
`(2^j, 2·2^j] × (2^k, 2·2^k]`. -/
private lemma vfm_box_decomp (R S : ℕ) {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M)
    (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hg : ∀ r s, ¬(r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)) → g r s = 0) :
    (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), g r s)
      = (∑ s ∈ Finset.Icc 1 (2*S), g 1 s)
        + (∑ r ∈ Finset.Icc 2 (2*R), g r 1)
        + ∑ jk ∈ (Finset.range (Nat.log2 (2*R)+1)) ×ˢ (Finset.range (Nat.log2 (2*S)+1)),
            ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
              g r s := by
  classical
  have hMR1 : 1 ≤ 2^(Nat.log2 (2*R)+1) := by
    have hpos : (0:ℕ) < 2^(Nat.log2 (2*R)+1) := by positivity
    omega
  have hMS1 : 1 ≤ 2^(Nat.log2 (2*S)+1) := by
    have hpos : (0:ℕ) < 2^(Nat.log2 (2*S)+1) := by positivity
    omega
  have hMR : 2*R ≤ 2^(Nat.log2 (2*R)+1) := le_of_lt Nat.lt_log2_self
  have hMS : 2*S ≤ 2^(Nat.log2 (2*S)+1) := le_of_lt Nat.lt_log2_self
  have hz2 : ∀ r, (∑ s ∈ Finset.Icc 1 (2*S), g r s)
      = (∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s) := by
    intro r
    refine Finset.sum_subset ?_ ?_
    · intro s hs; simp only [Finset.mem_Icc] at hs ⊢
      exact ⟨hs.1, le_trans hs.2 hMS⟩
    · intro s _ hs'
      exact hg r s (fun h => hs' h.2)
  have step1 : (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), g r s)
      = ∑ r ∈ Finset.Icc 1 (2^(Nat.log2 (2*R)+1)),
          ∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s := by
    rw [Finset.sum_congr rfl (fun r _ => hz2 r)]
    refine Finset.sum_subset ?_ ?_
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢
      exact ⟨hr.1, le_trans hr.2 hMR⟩
    · intro r _ hr'
      exact Finset.sum_eq_zero (fun s _ => hg r s (fun h => hr' h.1))
  have step2 : (∑ r ∈ Finset.Icc 1 (2^(Nat.log2 (2*R)+1)),
        ∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s)
      = (∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g 1 s)
        + ∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)),
            ∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s :=
    vfm_Icc_one_split hMR1 (fun r => ∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s)
  have step3 : (∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)),
        ∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s)
      = (∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)), g r 1)
        + ∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)),
            ∑ s ∈ Finset.Icc 2 (2^(Nat.log2 (2*S)+1)), g r s := by
    rw [Finset.sum_congr rfl (fun r _ => vfm_Icc_one_split hMS1 (fun s => g r s))]
    rw [Finset.sum_add_distrib]
  have step4 : (∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)),
        ∑ s ∈ Finset.Icc 2 (2^(Nat.log2 (2*S)+1)), g r s)
      = ∑ jk ∈ (Finset.range (Nat.log2 (2*R)+1)) ×ˢ (Finset.range (Nat.log2 (2*S)+1)),
            ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1),
              ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2), g r s := by
    rw [Finset.sum_product]
    rw [vfm_Icc_two_pow_tile (Nat.log2 (2*R))
          (fun r => ∑ s ∈ Finset.Icc 2 (2^(Nat.log2 (2*S)+1)), g r s)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_congr rfl
          (fun r _ => vfm_Icc_two_pow_tile (Nat.log2 (2*S)) (fun s => g r s))]
    rw [Finset.sum_comm]
  have trimA : (∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g 1 s)
      = ∑ s ∈ Finset.Icc 1 (2*S), g 1 s := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro s hs; simp only [Finset.mem_Icc] at hs ⊢
      exact ⟨hs.1, le_trans hs.2 hMS⟩
    · intro s _ hs'
      exact hg 1 s (fun h => hs' h.2)
  have trimB : (∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)), g r 1)
      = ∑ r ∈ Finset.Icc 2 (2*R), g r 1 := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢
      exact ⟨hr.1, le_trans hr.2 hMR⟩
    · intro r hr hs'
      refine hg r 1 (fun h => hs' ?_)
      simp only [Finset.mem_Icc] at hr h ⊢
      exact ⟨hr.1, h.1.2⟩
  rw [step1, step2, step3, step4, trimA, trimB]
  ac_rfl

/-- Swapping a sum over `jk` with a dependent double sum. -/
private lemma vfm_sum_sigma_comm {M : Type*} [AddCommMonoid M] {κ : Type*}
    (s : Finset ℕ) (t : ℕ → Finset ℕ) (u : Finset κ) (f : ℕ → ℕ → κ → M) :
    (∑ d ∈ s, ∑ a ∈ t d, ∑ jk ∈ u, f d a jk) = ∑ jk ∈ u, ∑ d ∈ s, ∑ a ∈ t d, f d a jk := by
  have h1 : (∑ d ∈ s, ∑ a ∈ t d, ∑ jk ∈ u, f d a jk)
      = ∑ x ∈ s.sigma t, ∑ jk ∈ u, f x.1 x.2 jk :=
    Finset.sum_sigma' s t (fun d a => ∑ jk ∈ u, f d a jk)
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun jk _ => ?_)
  exact (Finset.sum_sigma' s t (fun d a => f d a jk)).symm

/-- Pulling a constant out of a (`d`-dependent) double sum. -/
private lemma vfm_mul_sum_ind {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → Finset ℕ) (c : ℝ) (f : ι → ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t i, c * f i j) = c * (∑ i ∈ s, ∑ j ∈ t i, f i j) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum (t i) (f i) c).symm)

/-- `p14T12 D R S ε > 0` for `1 ≤ D`. -/
private lemma vfm_p14T12_pos {D : ℕ} (hD : 1 ≤ D) (R S : ℕ) (ε : ℝ) :
    0 < Work.FIArea4.p14T12 D R S ε := by
  unfold Work.FIArea4.p14T12
  have h : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  positivity

/-- `p14T12 D R S ε ≥ D`, `≥ R`, `≥ S`. -/
private lemma vfm_p14T12_ge_D {D : ℕ} (hD : 1 ≤ D) (R S : ℕ) (ε : ℝ) :
    (D:ℝ) ≤ Work.FIArea4.p14T12 D R S ε := by
  unfold Work.FIArea4.p14T12
  have h1 : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
      * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ) := by positivity
  have h2 : (0:ℝ) ≤ ((D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)
      + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) := by positivity
  linarith

private lemma vfm_p14T12_ge_R {D : ℕ} (hD : 1 ≤ D) {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {ε : ℝ} (hε : 0 ≤ ε) : (R:ℝ) ≤ Work.FIArea4.p14T12 D R S ε := by
  have hRd : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hSd : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hS34 : (1:ℝ) ≤ (S:ℝ)^((3:ℝ)/4) := Real.one_le_rpow hSd (by norm_num)
  have hX1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) := by nlinarith
  have hXe : (1:ℝ) ≤ ((R:ℝ)*(S:ℝ))^ε := Real.one_le_rpow hX1 hε
  have hkey : (R:ℝ) ≤ (R:ℝ) * (S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := by
    have h1 : (R:ℝ) ≤ (R:ℝ) * (S:ℝ)^((3:ℝ)/4) := by
      calc (R:ℝ) = (R:ℝ) * 1 := by ring
        _ ≤ (R:ℝ) * (S:ℝ)^((3:ℝ)/4) := mul_le_mul_of_nonneg_left hS34 (by linarith)
    calc (R:ℝ) ≤ (R:ℝ) * (S:ℝ)^((3:ℝ)/4) := h1
      _ = (R:ℝ) * (S:ℝ)^((3:ℝ)/4) * 1 := by ring
      _ ≤ (R:ℝ) * (S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) :=
          mul_le_mul_of_nonneg_left hXe (by positivity)
  calc (R:ℝ) ≤ (R:ℝ) * (S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := hkey
    _ ≤ Work.FIArea4.p14T12 D R S ε := by
        unfold Work.FIArea4.p14T12
        have h0 : (0:ℝ) ≤ (D:ℝ) + (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
            * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ) := by positivity
        have hexp : ((D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)
            + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε)
            = (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^ε)
            + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε)
            + (S:ℝ)*(R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := by ring
        rw [hexp]
        have h1 : (0:ℝ) ≤ (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^ε) := by positivity
        have h2 : (0:ℝ) ≤ (S:ℝ)*(R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := by positivity
        linarith

private lemma vfm_p14T12_ge_S {D : ℕ} (hD : 1 ≤ D) {R S : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    {ε : ℝ} (hε : 0 ≤ ε) : (S:ℝ) ≤ Work.FIArea4.p14T12 D R S ε := by
  have hRd : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hSd : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hR34 : (1:ℝ) ≤ (R:ℝ)^((3:ℝ)/4) := Real.one_le_rpow hRd (by norm_num)
  have hX1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) := by nlinarith
  have hXe : (1:ℝ) ≤ ((R:ℝ)*(S:ℝ))^ε := Real.one_le_rpow hX1 hε
  have hkey : (S:ℝ) ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := by
    have h1 : (S:ℝ) ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) := by
      calc (S:ℝ) = (S:ℝ) * 1 := by ring
        _ ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) := mul_le_mul_of_nonneg_left hR34 (by linarith)
    calc (S:ℝ) ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) := h1
      _ = (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * 1 := by ring
      _ ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) :=
          mul_le_mul_of_nonneg_left hXe (by positivity)
  calc (S:ℝ) ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := hkey
    _ ≤ Work.FIArea4.p14T12 D R S ε := by
        unfold Work.FIArea4.p14T12
        have h0 : (0:ℝ) ≤ (D:ℝ) + (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
            * (Real.log (2*(R:ℝ)*(S:ℝ))+1)^(4:ℕ) := by positivity
        have hexp : ((D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)
            + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) + (S:ℝ)*(R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε)
            = (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^ε)
            + (R:ℝ)*(S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε)
            + (S:ℝ)*(R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := by ring
        rw [hexp]
        have h1 : (0:ℝ) ≤ (D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2) * (((R:ℝ)*(S:ℝ))^ε) := by positivity
        have h2 : (0:ℝ) ≤ (R:ℝ)*(S:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := by positivity
        linarith

/-- At most one `j` satisfies `2^j < r ≤ 2·2^j` inside `range (JR+1)`. -/
private lemma vfm_cell_card_le_one (r s JR JS : ℕ) :
    (((Finset.range (JR+1)) ×ˢ (Finset.range (JS+1))).filter
      (fun jk => 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_product] at ha hb
  obtain ⟨-, ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨-, hb1, hb2, hb3, hb4⟩ := hb
  have hja : a.1 = b.1 := by
    have h1 : 2^a.1 < 2^(b.1+1) := by
      calc 2^a.1 < r := ha1
        _ ≤ 2 * 2^b.1 := hb2
        _ = 2^(b.1+1) := by rw [pow_succ]; ring
    have h2 : 2^b.1 < 2^(a.1+1) := by
      calc 2^b.1 < r := hb1
        _ ≤ 2 * 2^a.1 := ha2
        _ = 2^(a.1+1) := by rw [pow_succ]; ring
    have h3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
    have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  have hkb : a.2 = b.2 := by
    have h1 : 2^a.2 < 2^(b.2+1) := by
      calc 2^a.2 < s := ha3
        _ ≤ 2 * 2^b.2 := hb4
        _ = 2^(b.2+1) := by rw [pow_succ]; ring
    have h2 : 2^b.2 < 2^(a.2+1) := by
      calc 2^b.2 < s := hb3
        _ ≤ 2 * 2^a.2 := ha4
        _ = 2^(a.2+1) := by rw [pow_succ]; ring
    have h3 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
    have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2
    omega
  exact Prod.ext hja hkb

/-- Extending the range of `p14Ener` by zero terms. -/
private lemma vfm_Ener_extend {R S R' S' : ℕ} (β : ℕ → ℕ → ℂ)
    (h : ∀ r s, β r s ≠ 0 → r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)) :
    Work.FIArea4.p14Ener R S β = Work.FIArea4.p14Ener (max R R') (max S S') β := by
  unfold Work.FIArea4.p14Ener
  have hinner : ∀ r, (∑ s ∈ Finset.Icc 1 (2*S),
        ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (β r s))
      = (∑ s ∈ Finset.Icc 1 (2*max S S'),
        ((r.divisors.card : ℕ) : ℝ) * Complex.normSq (β r s)) := by
    intro r
    refine Finset.sum_subset ?_ ?_
    · intro s hs; simp only [Finset.mem_Icc] at hs ⊢; omega
    · intro s hs hs'
      have hz : β r s = 0 := by
        by_contra hc
        exact hs' (h r s hc).2
      rw [hz]; simp
  rw [Finset.sum_congr rfl (fun r _ => hinner r)]
  refine Finset.sum_subset ?_ ?_
  · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
  · intro r hr hr'
    refine Finset.sum_eq_zero (fun s _ => ?_)
    have hz : β r s = 0 := by
      by_contra hc
      exact hr' (h r s hc).1
    rw [hz]; simp

/-- `p14Ener` only depends on the support of `β`. -/
private lemma vfm_Ener_eq_of_supp {R S R' S' : ℕ} (β : ℕ → ℕ → ℂ)
    (h : ∀ r s, β r s ≠ 0 → r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S))
    (h' : ∀ r s, β r s ≠ 0 → r ∈ Finset.Icc 1 (2*R') ∧ s ∈ Finset.Icc 1 (2*S')) :
    Work.FIArea4.p14Ener R S β = Work.FIArea4.p14Ener R' S' β := by
  rw [vfm_Ener_extend β h (R' := R') (S' := S'),
    vfm_Ener_extend β h' (R' := R) (S' := S), max_comm R R', max_comm S S']

/-- **Reduction of the full box to the dyadic boxes.**  Given the dyadic-box estimate `hcell` of
Proposition 12.1, the crude small-box estimate `hmed` (`D > R*S`), the strip estimate `hstrip` and
the small-`D` estimate `hsmall`, one obtains the estimate for the *full* box
`[1,2R]×[1,2S]`. -/
theorem vfm_large_full {ε : ℝ} (hε : 0 < ε)
    (hcell : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D ≤ R * S → R * S < D * D →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        Work.FIPlan.Vvar R S D α ≤ C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α)
    (hmed : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      R * S < D → (∀ r s, β r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D β ≤ C * (D : ℝ) * Work.FIArea4.p14L2 R S β)
    (hstrip : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      (∀ r s, β r s ≠ 0 → r = 1 ∨ s = 1) →
        Work.FIPlan.Vvar R S D β ≤ C * ((R : ℝ) + (S : ℝ) + (D : ℝ)) * Work.FIArea4.p14L2 R S β)
    (hsmall : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D * D ≤ R * S →
        Work.FIPlan.Vvar R S D α ≤ C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α)
    (hdyad : ∃ C : ℝ, 0 < C ∧ ∀ (D R S JR JS : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S →
      (2:ℕ)^JR ≤ 2*R → (2:ℕ)^JS ≤ 2*S →
      (∑ j ∈ Finset.range (JR+1), ∑ k ∈ Finset.range (JS+1),
        Work.FIArea4.p14T12 D ((2:ℕ)^j) ((2:ℕ)^k) ε) ≤ C * Work.FIArea4.p14T12 D R S ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      D ≤ R * S → R * S < D * D →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤ C * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S α := by
  classical
  obtain ⟨Ccell, hCcell, hcell'⟩ := hcell
  obtain ⟨Cmed, hCmed, hmed'⟩ := hmed
  obtain ⟨Cstrip, hCstrip, hstrip'⟩ := hstrip
  obtain ⟨Csmall, hCsmall, hsmall'⟩ := hsmall
  obtain ⟨Cdyad, hCdyad, hdyad'⟩ := hdyad
  refine ⟨3 * (6 * Cstrip + Cdyad * (Ccell + Cmed + Csmall)) + 1, by positivity, ?_⟩
  intro D R S α hD hR hS hDle hRS hcop
  let a0 : ℕ → ℕ → ℂ := fun r s =>
    if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then α r s else 0
  have ha0box : ∀ r s, a0 r s ≠ 0 → r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) := by
    intro r s hh
    by_contra hc
    exact hh (by simp only [a0]; rw [if_neg hc])
  have ha0cop : ∀ r s, a0 r s ≠ 0 → Nat.Coprime r (2 * s) := by
    intro r s hh
    have hb := ha0box r s hh
    have he : a0 r s = α r s := by simp only [a0]; rw [if_pos hb]
    rw [he] at hh
    exact hcop r s hh
  have hVeq : Work.FIPlan.Vvar R S D α = Work.FIPlan.Vvar R S D a0 := by
    unfold Work.FIPlan.Vvar
    refine Finset.sum_congr rfl (fun d _ => ?_)
    unfold Work.FIPlan.Evar
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun r hr => ?_)
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hr1 : r ∈ Finset.Icc 1 (2*R) := (Finset.mem_filter.mp hr).1
    have hs1 : s ∈ Finset.Icc 1 (2*S) := (Finset.mem_filter.mp hs).1
    have he : a0 r s = α r s := by simp only [a0]; rw [if_pos ⟨hr1, hs1⟩]
    rw [he]
  have hEeq : Work.FIArea4.p14Ener R S a0 = Work.FIArea4.p14Ener R S α := by
    unfold Work.FIArea4.p14Ener
    refine Finset.sum_congr rfl (fun r hr => ?_)
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have he : a0 r s = α r s := by simp only [a0]; rw [if_pos ⟨hr, hs⟩]
    rw [he]
  rw [hVeq, ← hEeq]
  let Idx : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log2 (2*R)+1) ×ˢ Finset.range (Nat.log2 (2*S)+1)
  let αA : ℕ → ℕ → ℂ := fun r s => if r = 1 then a0 r s else 0
  let αB : ℕ → ℕ → ℂ := fun r s => if r ≠ 1 ∧ s = 1 then a0 r s else 0
  let αjk : ℕ × ℕ → ℕ → ℕ → ℂ := fun jk r s =>
    if 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2 then a0 r s else 0
  let uA : ℕ → ℕ → ℂ := fun d a => ∑ s ∈ Finset.Icc 1 (2*S), a0 1 s * Mentry d a 1 s
  let uB : ℕ → ℕ → ℂ := fun d a => ∑ r ∈ Finset.Icc 2 (2*R), a0 r 1 * Mentry d a r 1
  let uJ : ℕ × ℕ → ℕ → ℕ → ℂ := fun jk d a =>
    ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
      a0 r s * Mentry d a r s
  let uC : ℕ → ℕ → ℂ := fun d a => ∑ jk ∈ Idx, uJ jk d a
  have hinner : ∀ d a : ℕ,
      (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), a0 r s * Mentry d a r s)
        = uA d a + uB d a + uC d a := by
    intro d a
    have hbd := vfm_box_decomp R S (fun r s => a0 r s * Mentry d a r s) hR hS
      (fun r s hh => by
        by_cases hb : a0 r s = 0
        · rw [hb, zero_mul]
        · exact absurd (ha0box r s hb) hh)
    rw [hbd]
  have hV : Work.FIPlan.Vvar R S D a0
      = ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
          Complex.normSq (uA d a + uB d a + uC d a) := by
    rw [Work.FIPlan.Vvar]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Work.FIArea4.Evar_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    exact hinner d a
  have hV3 : Work.FIPlan.Vvar R S D a0 ≤ 3 * (
      (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
      + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
      + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))) := by
    rw [hV]
    calc ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            Complex.normSq (uA d a + uB d a + uC d a)
        ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            3 * (Complex.normSq (uA d a) + Complex.normSq (uB d a) + Complex.normSq (uC d a)) :=
          Finset.sum_le_sum (fun d _ => Finset.sum_le_sum
            (fun a _ => Work.FIArea4.normSq_add3_le _ _ _))
      _ = 3 * ((∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))) := by
          rw [Finset.sum_congr rfl (fun d _ => Work.FIArea4.sum3_factor (Finset.range d)
                (fun a => Complex.normSq (uA d a)) (fun a => Complex.normSq (uB d a))
                (fun a => Complex.normSq (uC d a)))]
          exact Work.FIArea4.sum3_factor (Finset.Ioc D (2*D))
                (fun d => ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
                (fun d => ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
                (fun d => ∑ a ∈ Finset.range d, Complex.normSq (uC d a))
  have hmemR : (1:ℕ) ∈ Finset.Icc 1 (2*R) := by simp only [Finset.mem_Icc]; omega
  have hAeq : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
      = Work.FIPlan.Vvar R S D αA := by
    rw [Work.FIPlan.Vvar]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Work.FIArea4.Evar_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [Finset.sum_eq_single_of_mem (s := Finset.Icc 1 (2*R))
        (f := fun r => ∑ s ∈ Finset.Icc 1 (2*S), αA r s * Mentry d a r s) 1 hmemR
        (fun r _ hr => Finset.sum_eq_zero (fun s _ => by
          rw [show αA r s = 0 from by simp only [αA]; exact if_neg hr]; ring))]
    simp only [uA]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [show αA 1 s = a0 1 s from by simp [αA]]
  have hAsupp : ∀ r s, αA r s ≠ 0 → r = 1 ∨ s = 1 := by
    intro r s hh; left
    by_contra hc
    exact hh (by simp only [αA]; exact if_neg hc)
  have hBmem : (1:ℕ) ∈ Finset.Icc 1 (2*S) := by simp only [Finset.mem_Icc]; omega
  have hBeq : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
      = Work.FIPlan.Vvar R S D αB := by
    rw [Work.FIPlan.Vvar]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Work.FIArea4.Evar_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    have hBinner : (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S),
          αB r s * Mentry d a r s)
        = ∑ r ∈ Finset.Icc 1 (2*R), αB r 1 * Mentry d a r 1 := by
      refine Finset.sum_congr rfl (fun r _ => ?_)
      refine Finset.sum_eq_single_of_mem (s := Finset.Icc 1 (2*S))
        (f := fun s => αB r s * Mentry d a r s) 1 hBmem (fun s _ hs => ?_)
      rw [show αB r s = 0 from by simp only [αB]; rw [if_neg (fun h => hs h.2)]]
      ring
    rw [hBinner]
    rw [vfm_Icc_one_split (show 1 ≤ 2*R by omega) (fun r => αB r 1 * Mentry d a r 1)]
    have h0 : αB 1 1 * Mentry d a 1 1 = 0 := by
      rw [show αB 1 1 = 0 from by simp [αB]]
      ring
    rw [h0, zero_add]
    simp only [uB]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr1 : r ≠ 1 := by rw [Finset.mem_Icc] at hr; omega
    rw [show αB r 1 = a0 r 1 from by simp only [αB]; exact if_pos ⟨hr1, trivial⟩]
  have hBsupp : ∀ r s, αB r s ≠ 0 → r = 1 ∨ s = 1 := by
    intro r s hh; right
    by_contra hc
    exact hh (by simp only [αB]; exact if_neg (fun h => hc h.2))
  have hTpos := vfm_p14T12_pos hD R S ε
  have hT0 : (0:ℝ) ≤ Work.FIArea4.p14T12 D R S ε := hTpos.le
  have hRSD : ((R:ℝ)+(S:ℝ)+(D:ℝ)) ≤ 3 * Work.FIArea4.p14T12 D R S ε := by
    have h1 := vfm_p14T12_ge_R hD hR hS hε.le
    have h2 := vfm_p14T12_ge_S hD hR hS hε.le
    have h3 := vfm_p14T12_ge_D hD R S ε
    linarith
  have hEnn : 0 ≤ Work.FIArea4.p14Ener R S a0 := by
    unfold Work.FIArea4.p14Ener
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg
      (fun s _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)))
  have hL2leE : ∀ β : ℕ → ℕ → ℂ, Work.FIArea4.p14L2 R S β ≤ Work.FIArea4.p14Ener R S β :=
    fun β => p14L2_le_p14Ener R S β
  have hA : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
      ≤ 3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0 := by
    have h1 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
        ≤ Cstrip * ((R:ℝ)+(S:ℝ)+(D:ℝ)) * Work.FIArea4.p14L2 R S αA := by
      rw [hAeq]; exact hstrip' D R S αA hD hR hS hAsupp
    have h2 : Work.FIArea4.p14L2 R S αA ≤ Work.FIArea4.p14Ener R S a0 := by
      calc Work.FIArea4.p14L2 R S αA ≤ Work.FIArea4.p14Ener R S αA := hL2leE αA
        _ ≤ Work.FIArea4.p14Ener R S a0 := by
            unfold Work.FIArea4.p14Ener
            refine Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => ?_))
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            by_cases hh : r = 1
            · simp only [αA, if_pos hh]
              exact le_refl _
            · simp only [αA, if_neg hh, Complex.normSq_zero]
              exact Complex.normSq_nonneg _
    calc (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
        ≤ Cstrip * ((R:ℝ)+(S:ℝ)+(D:ℝ)) * Work.FIArea4.p14L2 R S αA := h1
      _ ≤ Cstrip * (3 * Work.FIArea4.p14T12 D R S ε) * Work.FIArea4.p14Ener R S a0 := by
          calc Cstrip * ((R:ℝ)+(S:ℝ)+(D:ℝ)) * Work.FIArea4.p14L2 R S αA
              ≤ (Cstrip * (3 * Work.FIArea4.p14T12 D R S ε)) * Work.FIArea4.p14L2 R S αA :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRSD hCstrip.le) (p14L2_nonneg R S αA)
            _ ≤ (Cstrip * (3 * Work.FIArea4.p14T12 D R S ε)) * Work.FIArea4.p14Ener R S a0 :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0 := by ring
  have hB : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
      ≤ 3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0 := by
    have h1 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
        ≤ Cstrip * ((R:ℝ)+(S:ℝ)+(D:ℝ)) * Work.FIArea4.p14L2 R S αB := by
      rw [hBeq]; exact hstrip' D R S αB hD hR hS hBsupp
    have h2 : Work.FIArea4.p14L2 R S αB ≤ Work.FIArea4.p14Ener R S a0 := by
      calc Work.FIArea4.p14L2 R S αB ≤ Work.FIArea4.p14Ener R S αB := hL2leE αB
        _ ≤ Work.FIArea4.p14Ener R S a0 := by
            unfold Work.FIArea4.p14Ener
            refine Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => ?_))
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            by_cases hh : r ≠ 1 ∧ s = 1
            · simp only [αB, if_pos hh]
              exact le_refl _
            · simp only [αB, if_neg hh, Complex.normSq_zero]
              exact Complex.normSq_nonneg _
    calc (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
        ≤ Cstrip * ((R:ℝ)+(S:ℝ)+(D:ℝ)) * Work.FIArea4.p14L2 R S αB := h1
      _ ≤ Cstrip * (3 * Work.FIArea4.p14T12 D R S ε) * Work.FIArea4.p14Ener R S a0 := by
          calc Cstrip * ((R:ℝ)+(S:ℝ)+(D:ℝ)) * Work.FIArea4.p14L2 R S αB
              ≤ (Cstrip * (3 * Work.FIArea4.p14T12 D R S ε)) * Work.FIArea4.p14L2 R S αB :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRSD hCstrip.le) (p14L2_nonneg R S αB)
            _ ≤ (Cstrip * (3 * Work.FIArea4.p14T12 D R S ε)) * Work.FIArea4.p14Ener R S a0 :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0 := by ring
  have hEsum : (∑ jk ∈ Idx, Work.FIArea4.p14Ener R S (αjk jk))
      ≤ Work.FIArea4.p14Ener R S a0 := by
    simp only [Work.FIArea4.p14Ener]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun r _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun s _ => ?_)
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have h1 : (∑ jk ∈ Idx, Complex.normSq (αjk jk r s))
        = ∑ jk ∈ Idx, (if 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2
            then Complex.normSq (a0 r s) else 0) := by
      refine Finset.sum_congr rfl (fun jk _ => ?_)
      by_cases hc : 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2
      · rw [if_pos hc, show αjk jk r s = a0 r s from by simp only [αjk]; exact if_pos hc]
      · rw [if_neg hc, show αjk jk r s = 0 from by simp only [αjk]; rw [if_neg hc],
          Complex.normSq_zero]
    rw [h1]
    have h2 : (∑ jk ∈ Idx, (if 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2
            then Complex.normSq (a0 r s) else 0))
        = ((Idx.filter (fun jk => 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s
            ∧ s ≤ 2 * 2^jk.2)).card : ℝ) * Complex.normSq (a0 r s) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [h2]
    have hcard : ((Idx.filter (fun jk => 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s
        ∧ s ≤ 2 * 2^jk.2)).card : ℝ) ≤ 1 := by
      have hc := vfm_cell_card_le_one r s (Nat.log2 (2*R)) (Nat.log2 (2*S))
      simp only [Idx] at hc ⊢
      exact_mod_cast hc
    nlinarith [hcard, Complex.normSq_nonneg (a0 r s)]
  have hJbound : ∀ jk ∈ Idx,
      (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
        ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
          * Work.FIArea4.p14Ener R S (αjk jk) := by
    intro jk _
    have h1j : 1 ≤ (2:ℕ)^jk.1 := Nat.one_le_two_pow
    have h2j : 1 ≤ (2:ℕ)^jk.2 := Nat.one_le_two_pow
    have hsuppcell : ∀ r s, αjk jk r s ≠ 0 → (2:ℕ)^jk.1 < r ∧ r ≤ 2 * (2:ℕ)^jk.1
        ∧ (2:ℕ)^jk.2 < s ∧ s ≤ 2 * (2:ℕ)^jk.2 := by
      intro r s hh
      by_cases hc : 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2
      · exact hc
      · exact absurd (show αjk jk r s = 0 from by simp only [αjk]; exact if_neg hc) hh
    have hcopjk : ∀ r s, αjk jk r s ≠ 0 → Nat.Coprime r (2 * s) := by
      intro r s hh
      apply ha0cop r s
      by_cases hc : 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2
      · rwa [show αjk jk r s = a0 r s from by simp only [αjk]; rw [if_pos hc]] at hh
      · exact absurd (show αjk jk r s = 0 from by simp only [αjk]; exact if_neg hc) hh
    have hsuppR : ∀ r s, αjk jk r s ≠ 0 → r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) := by
      intro r s hh
      apply ha0box r s
      by_cases hc : 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2
      · rwa [show αjk jk r s = a0 r s from by simp only [αjk]; rw [if_pos hc]] at hh
      · exact absurd (show αjk jk r s = 0 from by simp only [αjk]; exact if_neg hc) hh
    have hsuppcell' : ∀ r s, αjk jk r s ≠ 0 → r ∈ Finset.Icc 1 (2 * 2^jk.1)
        ∧ s ∈ Finset.Icc 1 (2 * 2^jk.2) := by
      intro r s hh
      obtain ⟨h1, h2, h3, h4⟩ := hsuppcell r s hh
      exact ⟨by simp only [Finset.mem_Icc]; omega, by simp only [Finset.mem_Icc]; omega⟩
    have hEnerconv : Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk)
        = Work.FIArea4.p14Ener R S (αjk jk) :=
      vfm_Ener_eq_of_supp (αjk jk) hsuppcell' hsuppR
    have hJeq : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
        = Work.FIPlan.Vvar (2^jk.1) (2^jk.2) D (αjk jk) := by
      rw [Work.FIPlan.Vvar]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Work.FIArea4.Evar_eq]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      congr 1
      have hL : (∑ r ∈ Finset.Icc 1 (2 * 2^jk.1), ∑ s ∈ Finset.Icc 1 (2 * 2^jk.2),
            αjk jk r s * Mentry d a r s)
          = ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1),
              ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2), αjk jk r s * Mentry d a r s := by
        have hinner : ∀ r, (∑ s ∈ Finset.Icc 1 (2 * 2^jk.2), αjk jk r s * Mentry d a r s)
            = (∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2), αjk jk r s * Mentry d a r s) := by
          intro r
          refine (Finset.sum_subset ?_ ?_).symm
          · intro s hs; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hs ⊢; omega
          · intro s hs hs'
            have hz : αjk jk r s = 0 := by
              simp only [αjk]
              exact if_neg (fun hc => hs' (Finset.mem_Ioc.mpr ⟨hc.2.2.1, hc.2.2.2⟩))
            rw [hz]; ring
        calc (∑ r ∈ Finset.Icc 1 (2 * 2^jk.1), ∑ s ∈ Finset.Icc 1 (2 * 2^jk.2),
              αjk jk r s * Mentry d a r s)
            = ∑ r ∈ Finset.Icc 1 (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
                αjk jk r s * Mentry d a r s := Finset.sum_congr rfl (fun r _ => hinner r)
          _ = ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1),
                ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2), αjk jk r s * Mentry d a r s :=
              (Finset.sum_subset (by intro r hr; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hr ⊢; omega)
                (fun r hr hr' => Finset.sum_eq_zero (fun s _ => by
                  have hz : αjk jk r s = 0 := by
                    simp only [αjk]
                    exact if_neg (fun hc => hr' (Finset.mem_Ioc.mpr ⟨hc.1, hc.2.1⟩))
                  rw [hz]; ring))).symm
      rw [hL]
      refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
      rw [Finset.mem_Ioc] at hr hs
      rw [show αjk jk r s = a0 r s from by
        simp only [αjk]; exact if_pos ⟨hr.1, hr.2, hs.1, hs.2⟩]
    rw [hJeq]
    have hCsum0 : (0:ℝ) ≤ Ccell + Cmed + Csmall := by
      linarith [hCcell.le, hCmed.le, hCsmall.le]
    have hTcell := vfm_p14T12_pos hD (2^jk.1) (2^jk.2) ε
    have hEcell : (0:ℝ) ≤ Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) :=
      p14Ener_nonneg _ _ _
    have hgoal : Work.FIPlan.Vvar (2^jk.1) (2^jk.2) D (αjk jk)
        ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
          * Work.FIArea4.p14Ener R S (αjk jk) := by
      by_cases hbig : D * D ≤ (2:ℕ)^jk.1 * (2:ℕ)^jk.2
      · have h := hsmall' D (2^jk.1) (2^jk.2) (αjk jk) hD h1j h2j hbig
        have hstep : Csmall * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
              * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk)
            ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
              * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) := by
          have hTE : (0:ℝ) ≤ Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) := mul_nonneg hTcell.le hEcell
          have hle' : Csmall ≤ Ccell + Cmed + Csmall := by linarith [hCcell.le, hCmed.le]
          nlinarith [hTE, hle', mul_le_mul_of_nonneg_right hle' hTE]
        rw [hEnerconv] at h hstep
        linarith [h, hstep]
      · push_neg at hbig
        by_cases hmid : D ≤ (2:ℕ)^jk.1 * (2:ℕ)^jk.2
        · have h := hcell' D (2^jk.1) (2^jk.2) (αjk jk) hD h1j h2j hmid hbig hcopjk hsuppcell
          have hstep : Ccell * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk)
              ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) := by
            have hTE : (0:ℝ) ≤ Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) :=
              mul_nonneg hTcell.le hEcell
            have hle' : Ccell ≤ Ccell + Cmed + Csmall := by linarith [hCcell.le, hCmed.le]
            nlinarith [hTE, hle', mul_le_mul_of_nonneg_right hle' hTE]
          rw [hEnerconv] at h hstep
          linarith [h, hstep]
        · push_neg at hmid
          have h := hmed' D (2^jk.1) (2^jk.2) (αjk jk) hD h1j h2j hmid hcopjk
          have hDleT := vfm_p14T12_ge_D hD (2^jk.1) (2^jk.2) ε
          have hL2le : Work.FIArea4.p14L2 (2^jk.1) (2^jk.2) (αjk jk)
              ≤ Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) :=
            p14L2_le_p14Ener _ _ _
          have hstep : Cmed * (D:ℝ) * Work.FIArea4.p14L2 (2^jk.1) (2^jk.2) (αjk jk)
              ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) := by
            have hL2nn := p14L2_nonneg (2^jk.1) (2^jk.2) (αjk jk)
            have hDnn : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
            have hle' : Cmed ≤ Ccell + Cmed + Csmall := by linarith [hCcell.le, hCmed.le]
            have hCsnn : (0:ℝ) ≤ Ccell + Cmed + Csmall := by
              linarith [hCcell.le, hCmed.le, hCsmall.le]
            have h1 : Cmed * (D:ℝ) ≤ (Ccell + Cmed + Csmall) * (D:ℝ) :=
              mul_le_mul_of_nonneg_right hle' hDnn
            have h2 : (Ccell + Cmed + Csmall) * (D:ℝ)
                ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε :=
              mul_le_mul_of_nonneg_left hDleT hCsnn
            have hstep1 : Cmed * (D:ℝ) * Work.FIArea4.p14L2 (2^jk.1) (2^jk.2) (αjk jk)
                ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                  * Work.FIArea4.p14L2 (2^jk.1) (2^jk.2) (αjk jk) :=
              mul_le_mul_of_nonneg_right (h1.trans h2) hL2nn
            have hstep2 : (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                  * Work.FIArea4.p14L2 (2^jk.1) (2^jk.2) (αjk jk)
                ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                  * Work.FIArea4.p14Ener (2^jk.1) (2^jk.2) (αjk jk) :=
              mul_le_mul_of_nonneg_left hL2le (by positivity)
            linarith [hstep1, hstep2]
          rw [hEnerconv] at hstep
          linarith [h, hstep]
    exact hgoal
  have hC : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))
      ≤ Cdyad * (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D R S ε
        * Work.FIArea4.p14Ener R S a0 := by
    have hwpos : ∀ jk ∈ Idx, 0 < Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε :=
      fun jk _ => vfm_p14T12_pos hD _ _ ε
    have hcs : ∀ d a, Complex.normSq (∑ jk ∈ Idx, uJ jk d a)
        ≤ (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
          * (∑ jk ∈ Idx, Complex.normSq (uJ jk d a)
              / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε) :=
      fun d a => Work.FIArea4.normSq_sum_le_weighted Idx (fun jk => uJ jk d a)
        (fun jk => Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε) hwpos
    simp only [uC]
    have h1 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
          Complex.normSq (∑ jk ∈ Idx, uJ jk d a))
        ≤ (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
          * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              ∑ jk ∈ Idx, Complex.normSq (uJ jk d a)
                / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε) := by
      calc (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              Complex.normSq (∑ jk ∈ Idx, uJ jk d a))
          ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
                * (∑ jk ∈ Idx, Complex.normSq (uJ jk d a)
                    / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε) :=
              Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun a _ => hcs d a))
        _ = (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
              * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
                  ∑ jk ∈ Idx, Complex.normSq (uJ jk d a)
                    / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε) := by
              rw [vfm_mul_sum_ind (Finset.Ioc D (2*D)) (fun d => Finset.range d)
                (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
                (fun d a => ∑ jk ∈ Idx, Complex.normSq (uJ jk d a)
                    / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)]
    refine h1.trans ?_
    have hWle : (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
        ≤ Cdyad * Work.FIArea4.p14T12 D R S ε := by
      have h1 := Nat.log2_self_le (by omega : 2*R ≠ 0)
      have h2 := Nat.log2_self_le (by omega : 2*S ≠ 0)
      have hd := hdyad' D R S (Nat.log2 (2*R)) (Nat.log2 (2*S)) hD hR hS hDle h1 h2
      simpa only [Idx, Finset.sum_product] using hd
    have hWnn : (0:ℝ) ≤ ∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε :=
      Finset.sum_nonneg (fun jk hjk => (hwpos jk hjk).le)
    have hsplit : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
          ∑ jk ∈ Idx, Complex.normSq (uJ jk d a)
            / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
        = ∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            Complex.normSq (uJ jk d a))
            / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε := by
      rw [vfm_sum_sigma_comm (Finset.Ioc D (2*D)) (fun d => Finset.range d) Idx
            (fun d a jk => Complex.normSq (uJ jk d a)
              / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)]
      refine Finset.sum_congr rfl (fun jk _ => ?_)
      rw [show (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              Complex.normSq (uJ jk d a) / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
          = (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
              / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε from by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.sum_div]]
    rw [hsplit]
    have h2 : (∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            Complex.normSq (uJ jk d a)) / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
        ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14Ener R S a0 := by
      calc (∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              Complex.normSq (uJ jk d a)) / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
          ≤ ∑ jk ∈ Idx, (Ccell + Cmed + Csmall) * Work.FIArea4.p14Ener R S (αjk jk) := by
            refine Finset.sum_le_sum (fun jk hjk => ?_)
            rw [div_le_iff₀ (hwpos jk hjk)]
            calc (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
                ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε
                  * Work.FIArea4.p14Ener R S (αjk jk) := hJbound jk hjk
              _ = ((Ccell + Cmed + Csmall) * Work.FIArea4.p14Ener R S (αjk jk))
                  * Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε := by ring
        _ = (Ccell + Cmed + Csmall) * (∑ jk ∈ Idx, Work.FIArea4.p14Ener R S (αjk jk)) := by
            rw [Finset.mul_sum]
        _ ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14Ener R S a0 :=
            mul_le_mul_of_nonneg_left hEsum (by linarith [hCcell.le, hCmed.le, hCsmall.le])
    calc (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
          * (∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              Complex.normSq (uJ jk d a)) / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
        ≤ (Cdyad * Work.FIArea4.p14T12 D R S ε)
          * ((Ccell + Cmed + Csmall) * Work.FIArea4.p14Ener R S a0) := by
          have hXnn : (0:ℝ) ≤ (Ccell + Cmed + Csmall) * Work.FIArea4.p14Ener R S a0 :=
            mul_nonneg (by linarith [hCcell.le, hCmed.le, hCsmall.le])
              (p14Ener_nonneg R S a0)
          calc (∑ jk ∈ Idx, Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
                * (∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
                    Complex.normSq (uJ jk d a)) / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε)
              ≤ (Cdyad * Work.FIArea4.p14T12 D R S ε)
                * (∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
                    Complex.normSq (uJ jk d a)) / Work.FIArea4.p14T12 D (2^jk.1) (2^jk.2) ε) :=
                mul_le_mul_of_nonneg_right hWle
                  (Finset.sum_nonneg (fun jk hjk => div_nonneg
                    (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg
                      (fun a _ => Complex.normSq_nonneg _))) (hwpos jk hjk).le))
            _ ≤ (Cdyad * Work.FIArea4.p14T12 D R S ε)
                * ((Ccell + Cmed + Csmall) * Work.FIArea4.p14Ener R S a0) :=
                mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Cdyad * (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D R S ε
          * Work.FIArea4.p14Ener R S a0 := by ring
  calc Work.FIPlan.Vvar R S D a0
      ≤ 3 * ((∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
          + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
          + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))) := hV3
    _ ≤ 3 * (3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0
          + 3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0
          + Cdyad * (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D R S ε
              * Work.FIArea4.p14Ener R S a0) := by
          have h := add_le_add (add_le_add hA hB) hC
          linarith [h]
    _ ≤ (3 * (6 * Cstrip + Cdyad * (Ccell + Cmed + Csmall)) + 1)
          * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0 := by
          have hX : 3 * (3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0
              + 3 * Cstrip * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0
              + Cdyad * (Ccell + Cmed + Csmall) * Work.FIArea4.p14T12 D R S ε
                  * Work.FIArea4.p14Ener R S a0)
              = 3 * (6 * Cstrip + Cdyad * (Ccell + Cmed + Csmall))
                  * Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0 := by ring
          rw [hX]
          have hTE : (0:ℝ) ≤ Work.FIArea4.p14T12 D R S ε * Work.FIArea4.p14Ener R S a0 :=
            mul_nonneg hT0 hEnn
          nlinarith [hTE]

end

end Work.FIArea4.Vflip
