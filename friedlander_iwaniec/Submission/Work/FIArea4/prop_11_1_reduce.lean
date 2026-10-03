import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.prop_11_1_dual
import Submission.Work.FIArea4.Evar_le_trivial
import Submission.Work.FIArea4.sum_Ioc_Evar_le_braceV_support_r_one
import Submission.Work.FIArea4.sum_Ioc_Evar_le_braceV_support_s_one
import Submission.Work.FIArea4.braceV_dyadic_sum_le

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary lemmas used by the reduction -/

/-- **Weighted Cauchy–Schwarz.**  For complex `x i` and positive real weights `w i`,
`‖∑ x i‖² ≤ (∑ w i)·(∑ ‖x i‖² / w i)`. -/
lemma normSq_sum_le_weighted {ι : Type*} (s : Finset ι) (x : ι → ℂ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    Complex.normSq (∑ i ∈ s, x i) ≤ (∑ i ∈ s, w i) * (∑ i ∈ s, Complex.normSq (x i) / w i) := by
  set c : ι → ℂ := fun i => (Real.sqrt (w i) : ℂ) with hc
  set d : ι → ℂ := fun i => x i / (Real.sqrt (w i) : ℂ) with hd
  have hcd : ∑ i ∈ s, x i = ∑ i ∈ s, c i * d i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : (Real.sqrt (w i) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (hw i hi))
    rw [hc, hd]
    field_simp
  have hnormc : ∀ i ∈ s, Complex.normSq (c i) = w i := by
    intro i hi
    rw [hc, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt (le_of_lt (hw i hi))
  have hnormd : ∀ i ∈ s, Complex.normSq (d i) = Complex.normSq (x i) / w i := by
    intro i hi
    rw [hd, Complex.normSq_div, hnormc i hi]
  have e1 : (∑ i ∈ s, Complex.normSq (c i)) = ∑ i ∈ s, w i := Finset.sum_congr rfl hnormc
  have e2 : (∑ i ∈ s, Complex.normSq (d i)) = ∑ i ∈ s, Complex.normSq (x i) / w i :=
    Finset.sum_congr rfl hnormd
  have hA0 : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg (fun i hi => le_of_lt (hw i hi))
  have hB0 : 0 ≤ ∑ i ∈ s, Complex.normSq (x i) / w i :=
    Finset.sum_nonneg (fun i hi => div_nonneg (Complex.normSq_nonneg _) (le_of_lt (hw i hi)))
  calc Complex.normSq (∑ i ∈ s, x i) = Complex.normSq (∑ i ∈ s, c i * d i) := by rw [hcd]
    _ = ‖∑ i ∈ s, c i * d i‖ ^ 2 := Complex.normSq_eq_norm_sq _
    _ ≤ (Real.sqrt (∑ i ∈ s, Complex.normSq (c i))
          * Real.sqrt (∑ i ∈ s, Complex.normSq (d i))) ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact Work.FIArea4.norm_sum_mul_le s c d
    _ = (Real.sqrt (∑ i ∈ s, w i) * Real.sqrt (∑ i ∈ s, Complex.normSq (x i) / w i)) ^ 2 := by
        rw [e1, e2]
    _ = (∑ i ∈ s, w i) * (∑ i ∈ s, Complex.normSq (x i) / w i) := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]

/-- `‖x+y+z‖² ≤ 3(‖x‖²+‖y‖²+‖z‖²)`. -/
lemma normSq_add3_le (x y z : ℂ) :
    Complex.normSq (x + y + z) ≤ 3 * (Complex.normSq x + Complex.normSq y + Complex.normSq z) := by
  have h1 : Complex.normSq (x+y+z) = ‖x+y+z‖^2 := Complex.normSq_eq_norm_sq _
  have h2 : ‖x+y+z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    calc ‖x+y+z‖ = ‖(x+y)+z‖ := by ring_nf
      _ ≤ ‖x+y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by linarith [norm_add_le x y]
  have h3 : (‖x‖+‖y‖+‖z‖)^2 ≤ 3*(‖x‖^2+‖y‖^2+‖z‖^2) := by
    nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg z, sq_nonneg (‖x‖-‖y‖),
      sq_nonneg (‖y‖-‖z‖), sq_nonneg (‖x‖-‖z‖)]
  have e : Complex.normSq x + Complex.normSq y + Complex.normSq z = ‖x‖^2+‖y‖^2+‖z‖^2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rw [h1, e]
  calc ‖x+y+z‖^2 ≤ (‖x‖+‖y‖+‖z‖)^2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ 3*(‖x‖^2+‖y‖^2+‖z‖^2) := h3

/-- Factoring `3` out of a sum of three-part terms. -/
lemma sum3_factor {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g h : ι → ℝ) :
    (∑ i ∈ s, 3 * (f i + g i + h i)) = 3 * ((∑ i ∈ s, f i) + (∑ i ∈ s, g i) + (∑ i ∈ s, h i)) := by
  have e : ∀ i, 3 * (f i + g i + h i) = 3*f i + 3*g i + 3*h i := fun i => by ring
  simp only [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Splitting off the point `1` from `Icc 1 M`. -/
lemma sum_Icc_one_split {M : ℕ} (hM : 1 ≤ M) {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ m ∈ Finset.Icc 1 M, f m = f 1 + ∑ m ∈ Finset.Icc 2 M, f m := by
  have h : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, Finset.sum_insert]
  simp only [Finset.mem_Icc]; omega

/-- The dyadic tiling of `Icc 2 (2^{J+1})`. -/
lemma sum_Icc_two_pow_tile (J : ℕ) {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
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


/-- **Box decomposition.**  A double sum over the box `[1,2R] × [1,2S]` of a function that
vanishes outside the box splits into the two strips (`r = 1` and `s = 1`) and the dyadic
rectangles `(2^j, 2·2^j] × (2^k, 2·2^k]`. -/
private lemma box_decomp (R S : ℕ) {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M)
    (_hR : 1 ≤ R) (_hS : 1 ≤ S)
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
    sum_Icc_one_split hMR1 (fun r => ∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s)
  have step3 : (∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)),
        ∑ s ∈ Finset.Icc 1 (2^(Nat.log2 (2*S)+1)), g r s)
      = (∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)), g r 1)
        + ∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)),
            ∑ s ∈ Finset.Icc 2 (2^(Nat.log2 (2*S)+1)), g r s := by
    rw [Finset.sum_congr rfl (fun r _ => sum_Icc_one_split hMS1 (fun s => g r s))]
    rw [Finset.sum_add_distrib]
  have step4 : (∑ r ∈ Finset.Icc 2 (2^(Nat.log2 (2*R)+1)),
        ∑ s ∈ Finset.Icc 2 (2^(Nat.log2 (2*S)+1)), g r s)
      = ∑ jk ∈ (Finset.range (Nat.log2 (2*R)+1)) ×ˢ (Finset.range (Nat.log2 (2*S)+1)),
            ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1),
              ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2), g r s := by
    rw [Finset.sum_product]
    rw [sum_Icc_two_pow_tile (Nat.log2 (2*R))
          (fun r => ∑ s ∈ Finset.Icc 2 (2^(Nat.log2 (2*S)+1)), g r s)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_congr rfl
          (fun r _ => sum_Icc_two_pow_tile (Nat.log2 (2*S)) (fun s => g r s))]
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

/-- Pulling a constant out of a (`d`-dependent) double sum. -/
private lemma mul_sum_ind {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (t : ι → Finset ℕ) (c : ℝ) (f : ι → ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ t i, c * f i j) = c * (∑ i ∈ s, ∑ j ∈ t i, f i j) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => (Finset.mul_sum (t i) (f i) c).symm)

/-- Swapping a sum over `jk` with a dependent double sum. -/
private lemma sum_sigma_comm {M : Type*} [AddCommMonoid M] {κ : Type*}
    (s : Finset ℕ) (t : ℕ → Finset ℕ) (u : Finset κ) (f : ℕ → ℕ → κ → M) :
    (∑ d ∈ s, ∑ a ∈ t d, ∑ jk ∈ u, f d a jk) = ∑ jk ∈ u, ∑ d ∈ s, ∑ a ∈ t d, f d a jk := by
  have h1 : (∑ d ∈ s, ∑ a ∈ t d, ∑ jk ∈ u, f d a jk)
      = ∑ x ∈ s.sigma t, ∑ jk ∈ u, f x.1 x.2 jk :=
    Finset.sum_sigma' s t (fun d a => ∑ jk ∈ u, f d a jk)
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun jk _ => ?_)
  exact (Finset.sum_sigma' s t (fun d a => f d a jk)).symm

/-- `braceV` is positive for `D, R, S ≥ 1`. -/
private lemma braceV_pos {D R S : ℕ} (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (ε : ℝ) :
    0 < braceV D R S ε := by
  unfold braceV
  have h1 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have h2 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have h3 : (0:ℝ) < (S:ℝ) := by exact_mod_cast (by omega : 0 < S)
  positivity

-- ===== the three analytic inputs (delegated to sibling modules) =====
-- ===================================================================

/-- **Core reduction.** -/
private lemma reduce_core (ε : ℝ) (hε : 0 < ε) (Cd Cb : ℝ) (hCd : 0 < Cd) (hCb : 0 < Cb)
    (hCdprop : ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        Vdyad D R S α ≤ Cd * braceV D R S ε *
          (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s)))
    (hCbprop : ∀ (D R S JR JS : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (2:ℕ)^JR ≤ 2 * R → (2:ℕ)^JS ≤ 2 * S →
        (∑ j ∈ Finset.range (JR + 1), ∑ k ∈ Finset.range (JS + 1),
          braceV D ((2:ℕ)^j) ((2:ℕ)^k) ε) ≤ Cb * braceV D R S ε)
    (D R S : ℕ) (β : ℕ → ℕ → ℂ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hβ : ∀ r s, β r s ≠ 0 → r ∈ Finset.Icc 1 (2 * R) ∧ s ∈ Finset.Icc 1 (2 * S)) :
    Work.FIPlan.Vvar R S D β ≤ (3 * max 9 (Cb * Cd)) * braceV D R S ε *
      (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (β r s)) := by
  classical
  let Idx : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log2 (2*R)+1) ×ˢ Finset.range (Nat.log2 (2*S)+1)
  let βA : ℕ → ℕ → ℂ := fun r s => if r = 1 then β r s else 0
  let βB : ℕ → ℕ → ℂ := fun r s => if r ≠ 1 ∧ s = 1 then β r s else 0
  let βjk : ℕ × ℕ → ℕ → ℕ → ℂ := fun jk r s =>
    if 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2 then β r s else 0
  let uA : ℕ → ℕ → ℂ := fun d a => ∑ s ∈ Finset.Icc 1 (2*S), β 1 s * Mentry d a 1 s
  let uB : ℕ → ℕ → ℂ := fun d a => ∑ r ∈ Finset.Icc 2 (2*R), β r 1 * Mentry d a r 1
  let uJ : ℕ × ℕ → ℕ → ℕ → ℂ := fun jk d a =>
    ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
      β r s * Mentry d a r s
  let uC : ℕ → ℕ → ℂ := fun d a => ∑ jk ∈ Idx, uJ jk d a
  let EA : ℝ := ∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (βA r s)
  let EB : ℝ := ∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (βB r s)
  let EJ : ℕ × ℕ → ℝ := fun jk =>
    ∑ r ∈ Finset.Icc 1 (2 * 2^jk.1), ∑ s ∈ Finset.Icc 1 (2 * 2^jk.2), Complex.normSq (βjk jk r s)
  let EC : ℝ := ∑ jk ∈ Idx, EJ jk
  let E : ℝ := ∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β r s)
  have hmemR : (1:ℕ) ∈ Finset.Icc 1 (2*R) := by simp only [Finset.mem_Icc]; omega
  have hmemS : (1:ℕ) ∈ Finset.Icc 1 (2*S) := by simp only [Finset.mem_Icc]; omega
  have hsuppA : ∀ r s, βA r s ≠ 0 → r = 1 := by
    intro r s h
    by_cases hc : r = 1
    · exact hc
    · exact absurd (show βA r s = 0 from if_neg hc) h
  have hsuppB : ∀ r s, βB r s ≠ 0 → s = 1 := by
    intro r s h
    by_cases hc : r ≠ 1 ∧ s = 1
    · exact hc.2
    · exact absurd (show βB r s = 0 from if_neg hc) h
  -- (1) the class sum splits into the three groups
  have hinner : ∀ d a : ℕ,
      (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), β r s * Mentry d a r s)
        = uA d a + uB d a + uC d a := by
    intro d a
    simpa only [uA, uB, uC, uJ, Idx] using
      (box_decomp R S (fun r s => β r s * Mentry d a r s) hR hS (fun r s hh => by
        by_cases hb : β r s = 0
        · rw [hb, zero_mul]
        · exact absurd (hβ r s hb) hh))
  -- (2) Vvar as the sum of the three-part class sums
  have hV : Work.FIPlan.Vvar R S D β
      = ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
          Complex.normSq (uA d a + uB d a + uC d a) := by
    rw [Work.FIPlan.Vvar]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Work.FIArea4.Evar_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    exact hinner d a
  have hV3 : Work.FIPlan.Vvar R S D β
      ≤ 3 * ((∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))) := by
    rw [hV]
    calc ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            Complex.normSq (uA d a + uB d a + uC d a)
        ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            3 * (Complex.normSq (uA d a) + Complex.normSq (uB d a) + Complex.normSq (uC d a)) :=
          Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun a _ => normSq_add3_le _ _ _))
      _ = 3 * ((∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))) := by
          rw [Finset.sum_congr rfl (fun d _ => sum3_factor (Finset.range d)
                (fun a => Complex.normSq (uA d a)) (fun a => Complex.normSq (uB d a))
                (fun a => Complex.normSq (uC d a)))]
          exact sum3_factor (Finset.Ioc D (2*D))
                (fun d => ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
                (fun d => ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
                (fun d => ∑ a ∈ Finset.range d, Complex.normSq (uC d a))
  have hEAnn : 0 ≤ EA := by
    simp only [EA]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hEBnn : 0 ≤ EB := by
    simp only [EB]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have hECnn : 0 ≤ EC := by
    simp only [EC]
    exact Finset.sum_nonneg (fun jk _ => by
      simp only [EJ]
      exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _)))
  -- (4) the strip bounds
  have hVAeq : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
      = ∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S d βA := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Work.FIArea4.Evar_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [show uA d a = ∑ s ∈ Finset.Icc 1 (2*S), βA 1 s * Mentry d a 1 s from by
      simp only [uA]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      simp [βA]]
    exact (Finset.sum_eq_single_of_mem (s := Finset.Icc 1 (2*R))
        (f := fun r => ∑ s ∈ Finset.Icc 1 (2*S), βA r s * Mentry d a r s) 1 hmemR
        (fun r _ hr => Finset.sum_eq_zero (fun s _ => by
          rw [show βA r s = 0 from if_neg hr]; ring))).symm
  have hVA : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
      ≤ 3 * braceV D R S ε * EA := by
    rw [hVAeq]
    simpa only [EA] using sum_Ioc_Evar_le_braceV_support_r_one D R S βA ε hD hR hS hε hsuppA
  have hVBeq : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
      = ∑ d ∈ Finset.Ioc D (2*D), Work.FIPlan.Evar R S d βB := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Work.FIArea4.Evar_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [Finset.sum_comm]
    rw [show uB d a = ∑ r ∈ Finset.Icc 1 (2*R), βB r 1 * Mentry d a r 1 from by
      rw [sum_Icc_one_split (show 1 ≤ 2*R by omega) (fun r => βB r 1 * Mentry d a r 1)]
      have h0 : βB 1 1 * Mentry d a 1 1 = 0 := by
        rw [show βB 1 1 = 0 from if_neg (fun hc => hc.1 rfl)]; ring
      rw [h0, zero_add]
      simp only [uB]
      refine Finset.sum_congr rfl (fun r hr => ?_)
      have hr1 : r ≠ 1 := by simp only [Finset.mem_Icc] at hr; omega
      rw [show βB r 1 = β r 1 from if_pos ⟨hr1, rfl⟩]]
    exact (Finset.sum_eq_single_of_mem (s := Finset.Icc 1 (2*S))
        (f := fun s => ∑ r ∈ Finset.Icc 1 (2*R), βB r s * Mentry d a r s) 1 hmemS
        (fun s _ hs => Finset.sum_eq_zero (fun r _ => by
          rw [show βB r s = 0 from if_neg (fun hc => hs hc.2)]; ring))).symm
  have hVB : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
      ≤ 3 * braceV D R S ε * EB := by
    rw [hVBeq]
    simpa only [EB] using sum_Ioc_Evar_le_braceV_support_s_one D R S βB ε hD hR hS hε hsuppB
  -- (5) the dyadic-piece bounds
  have hVJ : ∀ jk, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
      ≤ Cd * braceV D (2^jk.1) (2^jk.2) ε * EJ jk := by
    intro jk
    have h1jk : 1 ≤ (2:ℕ)^jk.1 := Nat.one_le_two_pow
    have h2jk : 1 ≤ (2:ℕ)^jk.2 := Nat.one_le_two_pow
    have hsupp : ∀ r s, βjk jk r s ≠ 0 →
        (2:ℕ)^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ (2:ℕ)^jk.2 < s ∧ s ≤ 2 * 2^jk.2 := by
      intro r s h
      by_cases hc : 2^jk.1 < r ∧ r ≤ 2 * 2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2 * 2^jk.2
      · exact hc
      · exact absurd (show βjk jk r s = 0 from if_neg hc) h
    have hd := hCdprop D ((2:ℕ)^jk.1) ((2:ℕ)^jk.2) (βjk jk) hD h1jk h2jk hsupp
    have hVJeq : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
        = Vdyad D ((2:ℕ)^jk.1) ((2:ℕ)^jk.2) (βjk jk) := by
      simp only [Vdyad, uJ]
      refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => ?_))
      congr 1
      refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
      simp only [Finset.mem_Ioc] at hr hs
      rw [show β r s * Mentry d a r s = βjk jk r s * Mentry d a r s from by
        rw [show βjk jk r s = β r s from if_pos ⟨hr.1, hr.2, hs.1, hs.2⟩]]
    rw [hVJeq]
    simpa only [EJ] using hd
  -- (6) the weighted Cauchy–Schwarz for the dyadic pieces
  have hWpos : ∀ jk ∈ Idx, 0 < braceV D (2^jk.1) (2^jk.2) ε :=
    fun jk _ => braceV_pos hD Nat.one_le_two_pow Nat.one_le_two_pow ε
  have hsplit : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
        ∑ jk ∈ Idx, Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε)
      = ∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
          Complex.normSq (uJ jk d a)) / braceV D (2^jk.1) (2^jk.2) ε := by
    rw [sum_sigma_comm (Finset.Ioc D (2*D)) (fun d => Finset.range d) Idx
          (fun d a jk => Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε)]
    refine Finset.sum_congr rfl (fun jk _ => ?_)
    rw [show (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε)
        = (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
            / braceV D (2^jk.1) (2^jk.2) ε from by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [Finset.sum_div]]
  have hVC : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))
      ≤ (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε) * (Cd * EC) := by
    simp only [uC]
    have hcs : ∀ d a, Complex.normSq (∑ jk ∈ Idx, uJ jk d a)
        ≤ (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε)
          * (∑ jk ∈ Idx, Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε) :=
      fun d a => normSq_sum_le_weighted Idx (fun jk => uJ jk d a)
        (fun jk => braceV D (2^jk.1) (2^jk.2) ε) hWpos
    have h1 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
          Complex.normSq (∑ jk ∈ Idx, uJ jk d a))
        ≤ (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε)
          * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              ∑ jk ∈ Idx, Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε) := by
      calc (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              Complex.normSq (∑ jk ∈ Idx, uJ jk d a))
          ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
              (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε)
                * (∑ jk ∈ Idx,
                    Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε) :=
              Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun a _ => hcs d a))
        _ = (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε)
              * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
                  ∑ jk ∈ Idx,
                    Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε) :=
              mul_sum_ind (Finset.Ioc D (2*D)) (fun d => Finset.range d)
                (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε)
                (fun d a => ∑ jk ∈ Idx,
                  Complex.normSq (uJ jk d a) / braceV D (2^jk.1) (2^jk.2) ε)
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _
      (Finset.sum_nonneg (fun jk hjk => le_of_lt (hWpos jk hjk)))
    rw [hsplit]
    calc ∑ jk ∈ Idx, (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d,
            Complex.normSq (uJ jk d a)) / braceV D (2^jk.1) (2^jk.2) ε
        ≤ ∑ jk ∈ Idx, Cd * EJ jk := by
          refine Finset.sum_le_sum (fun jk hjk => ?_)
          rw [div_le_iff₀ (hWpos jk hjk)]
          calc (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uJ jk d a))
              ≤ Cd * braceV D (2^jk.1) (2^jk.2) ε * EJ jk := hVJ jk
            _ = (Cd * EJ jk) * braceV D (2^jk.1) (2^jk.2) ε := by ring
      _ = Cd * (∑ jk ∈ Idx, EJ jk) := by rw [Finset.mul_sum]
      _ = Cd * EC := by simp only [EC]
  -- (7) the brace comparison
  have hWle : (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε) ≤ Cb * braceV D R S ε := by
    have h1 : (2:ℕ)^(Nat.log2 (2*R)) ≤ 2*R :=
      Nat.log2_self_le (by omega : 2*R ≠ 0)
    have h2 : (2:ℕ)^(Nat.log2 (2*S)) ≤ 2*S :=
      Nat.log2_self_le (by omega : 2*S ≠ 0)
    have hd := hCbprop D R S (Nat.log2 (2*R)) (Nat.log2 (2*S)) hD hR hS h1 h2
    simpa only [Idx, Finset.sum_product] using hd
  -- (8) the energy identity
  have hEJ : ∀ jk, EJ jk = ∑ r ∈ Finset.Ioc (2^jk.1) (2*2^jk.1),
      ∑ s ∈ Finset.Ioc (2^jk.2) (2*2^jk.2), Complex.normSq (β r s) := by
    intro jk
    have hA : 1 ≤ (2:ℕ)^jk.1 := Nat.one_le_two_pow
    have hB : 1 ≤ (2:ℕ)^jk.2 := Nat.one_le_two_pow
    have hcond : ∀ r s, (2^jk.1 < r ∧ r ≤ 2*2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2*2^jk.2) →
        βjk jk r s = β r s := fun r s hc => if_pos hc
    simp only [EJ]
    have hstep1 : (∑ r ∈ Finset.Icc 1 (2 * 2^jk.1), ∑ s ∈ Finset.Icc 1 (2 * 2^jk.2),
          Complex.normSq (βjk jk r s))
        = ∑ r ∈ Finset.Icc 1 (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
          Complex.normSq (βjk jk r s) := by
      refine Finset.sum_congr rfl (fun r _ => (Finset.sum_subset ?_ ?_).symm)
      · intro s hs
        rw [Finset.mem_Ioc] at hs
        rw [Finset.mem_Icc]
        exact ⟨le_of_lt (lt_of_le_of_lt hB hs.1), hs.2⟩
      · intro s hs hs'
        have hc : ¬(2^jk.1 < r ∧ r ≤ 2*2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2*2^jk.2) := by
          intro hc
          exact hs' (Finset.mem_Ioc.mpr ⟨hc.2.2.1, hc.2.2.2⟩)
        rw [show βjk jk r s = 0 from if_neg hc, Complex.normSq_zero]
    have hstep2 : (∑ r ∈ Finset.Icc 1 (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
          Complex.normSq (βjk jk r s))
        = ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
          Complex.normSq (βjk jk r s) := by
      refine (Finset.sum_subset ?_ ?_).symm
      · intro r hr
        rw [Finset.mem_Ioc] at hr
        rw [Finset.mem_Icc]
        exact ⟨le_of_lt (lt_of_le_of_lt hA hr.1), hr.2⟩
      · intro r hr hr'
        refine Finset.sum_eq_zero (fun s _ => ?_)
        have hc : ¬(2^jk.1 < r ∧ r ≤ 2*2^jk.1 ∧ 2^jk.2 < s ∧ s ≤ 2*2^jk.2) := by
          intro hc
          exact hr' (Finset.mem_Ioc.mpr ⟨hc.1, hc.2.1⟩)
        rw [show βjk jk r s = 0 from if_neg hc, Complex.normSq_zero]
    have hstep3 : (∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
          Complex.normSq (βjk jk r s))
        = ∑ r ∈ Finset.Ioc (2^jk.1) (2 * 2^jk.1), ∑ s ∈ Finset.Ioc (2^jk.2) (2 * 2^jk.2),
          Complex.normSq (β r s) := by
      refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
      simp only [Finset.mem_Ioc] at hr hs
      rw [hcond r s ⟨hr.1, hr.2, hs.1, hs.2⟩]
    exact (hstep1.trans hstep2).trans hstep3
  have hEA : EA = ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β 1 s) := by
    simp only [EA]
    rw [Finset.sum_eq_single_of_mem (s := Finset.Icc 1 (2*R))
        (f := fun r => ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (βA r s)) 1 hmemR
        (fun r _ hr => Finset.sum_eq_zero (fun s _ => by
          rw [show βA r s = 0 from if_neg hr, Complex.normSq_zero]))]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp [βA]
  have hEB : EB = ∑ r ∈ Finset.Icc 2 (2*R), Complex.normSq (β r 1) := by
    simp only [EB]
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single_of_mem (s := Finset.Icc 1 (2*S))
        (f := fun s => ∑ r ∈ Finset.Icc 1 (2*R), Complex.normSq (βB r s)) 1 hmemS
        (fun s _ hs => Finset.sum_eq_zero (fun r _ => by
          rw [show βB r s = 0 from if_neg (fun hc => hs hc.2), Complex.normSq_zero]))]
    rw [sum_Icc_one_split (show 1 ≤ 2*R by omega) (fun r => Complex.normSq (βB r 1))]
    rw [show Complex.normSq (βB 1 1) = 0 from by
      rw [show βB 1 1 = 0 from if_neg (fun hc => hc.1 rfl), Complex.normSq_zero], zero_add]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    have hr1 : r ≠ 1 := by simp only [Finset.mem_Icc] at hr; omega
    rw [show βB r 1 = β r 1 from if_pos ⟨hr1, rfl⟩]
  have hEC : EC = ∑ jk ∈ Idx, ∑ r ∈ Finset.Ioc (2^jk.1) (2*2^jk.1),
      ∑ s ∈ Finset.Ioc (2^jk.2) (2*2^jk.2), Complex.normSq (β r s) := by
    simp only [EC]
    exact Finset.sum_congr rfl (fun jk _ => hEJ jk)
  have hE : E = EA + EB + EC := by
    have hdb := box_decomp R S (fun r s => Complex.normSq (β r s)) hR hS (fun r s hg => by
      by_cases hb : β r s = 0
      · rw [hb, Complex.normSq_zero]
      · exact absurd (hβ r s hb) hg)
    change (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (β r s))
      = EA + EB + EC
    rw [hdb, ← hEA, ← hEB, ← hEC]
  -- (9) final combination
  calc Work.FIPlan.Vvar R S D β
      ≤ 3 * ((∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uA d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uB d a))
            + (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (uC d a))) := hV3
    _ ≤ 3 * (3 * braceV D R S ε * EA + 3 * braceV D R S ε * EB
            + (∑ jk ∈ Idx, braceV D (2^jk.1) (2^jk.2) ε) * (Cd * EC)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
        exact add_le_add (add_le_add hVA hVB) hVC
    _ ≤ 3 * (3 * braceV D R S ε * EA + 3 * braceV D R S ε * EB
            + (Cb * braceV D R S ε) * (Cd * EC)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
        exact add_le_add (add_le_add le_rfl le_rfl)
          (mul_le_mul_of_nonneg_right hWle (mul_nonneg (le_of_lt hCd) hECnn))
    _ = 3 * braceV D R S ε * (3 * EA + 3 * EB + Cb * Cd * EC) := by ring
    _ ≤ 3 * braceV D R S ε * (max 9 (Cb * Cd) * (EA + EB + EC)) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (le_of_lt (braceV_pos hD hR hS ε)))
        have h1 : (3:ℝ) ≤ max 9 (Cb * Cd) :=
          le_trans (by norm_num) (le_max_left (9:ℝ) (Cb * Cd))
        have h2 : Cb * Cd ≤ max 9 (Cb * Cd) := le_max_right _ _
        have a1 : 3 * EA ≤ max 9 (Cb * Cd) * EA := mul_le_mul_of_nonneg_right h1 hEAnn
        have a2 : 3 * EB ≤ max 9 (Cb * Cd) * EB := mul_le_mul_of_nonneg_right h1 hEBnn
        have a3 : Cb * Cd * EC ≤ max 9 (Cb * Cd) * EC := mul_le_mul_of_nonneg_right h2 hECnn
        nlinarith [a1, a2, a3]
    _ = (3 * max 9 (Cb * Cd)) * braceV D R S ε * E := by rw [hE]; ring

/-- Reduction of the full-box Friedlander–Iwaniec variance estimate `Work.FIArea4.prop_11_1`
to the dyadic-box estimate `prop_11_1_dyadic` (the paper's box (11.6)). -/
theorem prop_11_1_reduce
    (hcore : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        Work.FIArea4.Vdyad D R S α ≤ C * Work.FIArea4.braceV D R S ε *
          (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S), Complex.normSq (α r s))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        Work.FIPlan.Vvar R S D α ≤
          C * ((D : ℝ) ^ (-(1 : ℝ) / 2) * (R : ℝ) * (S : ℝ)
                + ((D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))
                    + (R : ℝ) * (S : ℝ) ^ ((3 : ℝ) / 4)
                    + (S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4))
                  * (((R : ℝ) * (S : ℝ)) ^ ε))
            * (∑ r ∈ Finset.Icc 1 (2 * R), ∑ s ∈ Finset.Icc 1 (2 * S),
                Complex.normSq (α r s)) := by
  intro ε hε
  obtain ⟨Cd, hCd, hCdprop⟩ := hcore ε hε
  obtain ⟨Cb, hCb, hCbprop⟩ := braceV_dyadic_sum_le ε hε
  refine ⟨3 * max 9 (Cb * Cd), by positivity, ?_⟩
  intro D R S α hD hR hS
  have hVeq : Work.FIPlan.Vvar R S D
        (fun r s => if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then α r s else 0)
      = Work.FIPlan.Vvar R S D α := by
    simp only [Work.FIPlan.Vvar]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [Work.FIArea4.Evar_eq, Work.FIArea4.Evar_eq]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
    change (if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then α r s else 0)
      * Mentry d a r s = α r s * Mentry d a r s
    rw [if_pos ⟨hr, hs⟩]
  have hEeq : (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S),
        Complex.normSq ((fun r s => if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)
          then α r s else 0) r s))
      = (∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), Complex.normSq (α r s)) := by
    refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
    change Complex.normSq (if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)
      then α r s else 0) = Complex.normSq (α r s)
    rw [if_pos ⟨hr, hs⟩]
  rw [← hVeq, ← hEeq]
  exact reduce_core ε hε Cd Cb hCd hCb hCdprop hCbprop D R S _ hD hR hS
    (fun r s h => by
      by_cases hc : r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)
      · exact hc
      · refine absurd ?_ h
        change (if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then α r s else 0) = 0
        rw [if_neg hc])

end

end Work.FIArea4
