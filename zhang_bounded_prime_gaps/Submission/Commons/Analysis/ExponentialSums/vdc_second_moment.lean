import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Data.Int.SuccPred

open Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false

namespace Commons.Analysis.ExponentialSums

noncomputable section

namespace vdc2

/-- u-support interval of length M starting at a+1 -/
def vdc2_I (a : ℤ) (M : ℕ) : Finset ℤ := Finset.Icc (a + 1) (a + (M : ℤ))
/-- shift indices 0..H-1 -/
def vdc2_A (H : ℕ) : Finset ℤ := Finset.Icc (0 : ℤ) ((H : ℤ) - 1)
/-- shift window -(H-1)..(H-1) (H ≥ 1 in use) -/
def vdc2_Win (H : ℕ) : Finset ℤ := Finset.Icc (-((H : ℤ) - 1)) ((H : ℤ) - 1)
/-- big summation window J ⊇ ∪_i (I - i) for i ∈ A -/
def vdc2_J (a : ℤ) (M H : ℕ) : Finset ℤ := Finset.Icc (a + 1 - (H : ℤ)) (a + (M : ℤ))
/-- real weight w(t) = H - |t| -/
def vdc2_w (H : ℕ) (t : ℤ) : ℝ := (H : ℝ) - ‖(t : ℝ)‖
/-- correlation sum over the interval -/
def vdc2_corr (a : ℤ) (M : ℕ) (u : ℤ → ℂ) (t : ℤ) : ℂ :=
  ∑ n ∈ vdc2_I a M, u (n + t) * conj (u n)
/-- windowed transform -/
def vdc2_T (H : ℕ) (u : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑ i ∈ vdc2_A H, u (m + i)

/-- problem-statement window equals H≥1-based window -/
lemma vdc2_win_eq (H : ℕ) (hH : 1 ≤ H) :
    vdc2_Win H = Finset.Icc (-((H - 1 : ℕ) : ℤ)) (((H - 1 : ℕ) : ℤ)) := by
  ext t
  simp only [vdc2_Win, Finset.mem_Icc]
  omega

/-- translation reindexing over a finset of integers -/
lemma vdc2_translate_sum {β : Type*} [AddCommMonoid β] (f : ℤ → β) (S : Finset ℤ) (c : ℤ) :
    (∑ m ∈ S, f (m + c)) = ∑ n ∈ S.image (fun m => m + c), f n := by
  have hinj : Set.InjOn (fun m : ℤ => m + c) ↑S := by
    intro m1 hm1 m2 hm2 h
    exact add_right_cancel h
  exact (Finset.sum_image (s := S) (g := fun m : ℤ => m + c) (f := f) hinj).symm

/-- support: u vanishes outside the interval -/
lemma vdc2_support {a : ℤ} {M : ℕ} (u : ℤ → ℂ)
    (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) :
    ∀ n : ℤ, n ∉ vdc2_I a M → u n = 0 := by
  intro n hn
  by_contra h
  exact hn (hu0 n h)

/-- interval arithmetic: for n in I and i in A, n - i lies in J -/
lemma vdc2_mem_sub_J {a : ℤ} {M H : ℕ} {n i : ℤ}
    (hn : n ∈ vdc2_I a M) (hi : i ∈ vdc2_A H) : n - i ∈ vdc2_J a M H := by
  simp only [vdc2_I, vdc2_A, vdc2_J, Finset.mem_Icc] at hn hi ⊢
  constructor <;> omega

/-- image-translation contains the interval: I ⊆ J.image (· + i) for i ∈ A -/
lemma vdc2_I_sub_image_J {a : ℤ} {M H : ℕ} {i : ℤ}
    (hi : i ∈ vdc2_A H) :
    vdc2_I a M ⊆ (vdc2_J a M H).image (fun m : ℤ => m + i) := by
  intro n hn
  refine Finset.mem_image.mpr ⟨n - i, ?_, ?_⟩
  · exact vdc2_mem_sub_J hn hi
  · omega

/-- sum over J of u(m+i) equals sum over I of u -/
lemma vdc2_sum_J_shift_eq_sum_I {a : ℤ} {M H : ℕ} (u : ℤ → ℂ)
    (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) {i : ℤ} (hi : i ∈ vdc2_A H) :
    (∑ m ∈ vdc2_J a M H, u (m + i)) = ∑ n ∈ vdc2_I a M, u n := by
  calc
    (∑ m ∈ vdc2_J a M H, u (m + i))
        = ∑ n ∈ (vdc2_J a M H).image (fun m : ℤ => m + i), u n :=
          vdc2_translate_sum u (vdc2_J a M H) i
    _ = ∑ n ∈ vdc2_I a M, u n := by
          exact (Finset.sum_subset (vdc2_I_sub_image_J (a := a) (M := M) (H := H) hi)
            (by intro x hx hnx; exact vdc2_support u hu0 x hnx)).symm

/-- u(m + i) conj u(m + j)-type sum over J equals the correlation -/
lemma vdc2_sum_J_conj_eq_corr {a : ℤ} {M H : ℕ} (u : ℤ → ℂ)
    (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) {p : ℤ × ℤ}
    (_hp1 : p.1 ∈ vdc2_A H) (hp2 : p.2 ∈ vdc2_A H) :
    (∑ m ∈ vdc2_J a M H, u (m + p.1) * conj (u (m + p.2))) =
      vdc2_corr a M u (p.1 - p.2) := by
  unfold vdc2_corr
  calc
    (∑ m ∈ vdc2_J a M H, u (m + p.1) * conj (u (m + p.2)))
        = ∑ m ∈ vdc2_J a M H,
            u ((m + p.2) + (p.1 - p.2)) * conj (u (m + p.2)) := by
          apply Finset.sum_congr rfl
          intro m hm
          congr 2
          ring
    _ = ∑ n ∈ (vdc2_J a M H).image (fun m : ℤ => m + p.2),
            u (n + (p.1 - p.2)) * conj (u n) := by
          exact vdc2_translate_sum (fun n : ℤ => u (n + (p.1 - p.2)) * conj (u n))
            (vdc2_J a M H) p.2
    _ = ∑ n ∈ vdc2_I a M, u (n + (p.1 - p.2)) * conj (u n) := by
          exact (Finset.sum_subset (vdc2_I_sub_image_J (a := a) (M := M) (H := H) hp2)
            (by
              intro x hx hnx
              have hzero : u x = 0 := vdc2_support u hu0 x hnx
              rw [hzero]
              simp)).symm

/-- expand the double product into product of sums -/
lemma vdc2_inner_eq_T {H : ℕ} (u : ℤ → ℂ) (m : ℤ) :
    (∑ p ∈ (vdc2_A H).product (vdc2_A H), u (m + p.1) * conj (u (m + p.2))) =
      vdc2_T H u m * conj (vdc2_T H u m) := by
  calc
    (∑ p ∈ (vdc2_A H).product (vdc2_A H), u (m + p.1) * conj (u (m + p.2)))
        = ∑ i ∈ vdc2_A H, ∑ j ∈ vdc2_A H, u (m + i) * conj (u (m + j)) := by
          simpa using (Finset.sum_product (s := vdc2_A H) (t := vdc2_A H)
            (f := fun p : ℤ × ℤ => u (m + p.1) * conj (u (m + p.2))))
    _ = (∑ i ∈ vdc2_A H, u (m + i)) * (∑ j ∈ vdc2_A H, conj (u (m + j))) := by
          have hprod : (∑ i ∈ vdc2_A H, u (m + i)) * (∑ j ∈ vdc2_A H, conj (u (m + j)))
              = ∑ i ∈ vdc2_A H, ∑ j ∈ vdc2_A H, u (m + i) * conj (u (m + j)) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
          exact hprod.symm
    _ = (∑ i ∈ vdc2_A H, u (m + i)) * conj (∑ j ∈ vdc2_A H, u (m + j)) := by
          congr 2
          rw [map_sum]
    _ = vdc2_T H u m * conj (vdc2_T H u m) := by
          rfl

/-- z * conj z equals the squared norm as a complex number -/
lemma vdc2_self_conj (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj']
  norm_num

/-- sum of real casts = cast of real sum (ofReal as ring hom) -/
lemma vdc2_sum_ofReal {s : Finset ℤ} (f : ℤ → ℝ) :
    (∑ m ∈ s, (f m : ℂ)) = ((∑ m ∈ s, f m : ℝ) : ℂ) := by
  exact (map_sum Complex.ofRealHom f s).symm

/-- norm of nonneg real cast -/
lemma vdc2_norm_ofReal (r : ℝ) (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  exact (RCLike.norm_ofReal r).trans (abs_of_nonneg hr)

/-- the norm of the whole double sum equals the real sum of squared norms -/
lemma vdc2_D_norm_eq_Q {a : ℤ} {M H : ℕ} (u : ℤ → ℂ) :
    ‖(∑ m ∈ vdc2_J a M H, ∑ p ∈ (vdc2_A H).product (vdc2_A H),
        u (m + p.1) * conj (u (m + p.2)))‖ =
      (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ) := by
  have h0 : 0 ≤ (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ) := by
    exact Finset.sum_nonneg (fun m hm => sq_nonneg _)
  have h1 : (∑ m ∈ vdc2_J a M H, ∑ p ∈ (vdc2_A H).product (vdc2_A H),
        u (m + p.1) * conj (u (m + p.2)))
      = ∑ m ∈ vdc2_J a M H, vdc2_T H u m * conj (vdc2_T H u m) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact vdc2_inner_eq_T u m
  have h2 : (∑ m ∈ vdc2_J a M H, vdc2_T H u m * conj (vdc2_T H u m))
      = ∑ m ∈ vdc2_J a M H, ((‖vdc2_T H u m‖ ^ 2 : ℝ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact vdc2_self_conj (vdc2_T H u m)
  calc
    ‖(∑ m ∈ vdc2_J a M H, ∑ p ∈ (vdc2_A H).product (vdc2_A H),
          u (m + p.1) * conj (u (m + p.2)))‖
        = ‖(∑ m ∈ vdc2_J a M H, vdc2_T H u m * conj (vdc2_T H u m))‖ := by
          rw [h1]
    _ = ‖(∑ m ∈ vdc2_J a M H, ((‖vdc2_T H u m‖ ^ 2 : ℝ) : ℂ))‖ := by
          rw [h2]
    _ = ‖((∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [vdc2_sum_ofReal]
    _ = (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ) := by
          exact vdc2_norm_ofReal _ h0

/-- double sum reorders; equals the pair-sum of correlations -/
lemma vdc2_D_eq_sum_corr {a : ℤ} {M H : ℕ} (u : ℤ → ℂ)
    (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) :
    (∑ m ∈ vdc2_J a M H, ∑ p ∈ (vdc2_A H).product (vdc2_A H),
        u (m + p.1) * conj (u (m + p.2))) =
      ∑ p ∈ (vdc2_A H).product (vdc2_A H), vdc2_corr a M u (p.1 - p.2) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact vdc2_sum_J_conj_eq_corr u hu0 (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2

/-- second-part inequality: real sum of squared windowed norms ≤ weighted correlations -/
lemma vdc2_Q_le_weighted {a : ℤ} {M H : ℕ} (u : ℤ → ℂ)
    (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) :
    (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ) ≤
      ∑ p ∈ (vdc2_A H).product (vdc2_A H), ‖vdc2_corr a M u (p.1 - p.2)‖ := by
  have hnorm : (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ)
      = ‖∑ p ∈ (vdc2_A H).product (vdc2_A H),
            ∑ m ∈ vdc2_J a M H, u (m + p.1) * conj (u (m + p.2))‖ := by
    calc
      (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ)
          = ‖(∑ m ∈ vdc2_J a M H, ∑ p ∈ (vdc2_A H).product (vdc2_A H),
              u (m + p.1) * conj (u (m + p.2)))‖ := by
            exact (vdc2_D_norm_eq_Q u).symm
      _ = ‖∑ p ∈ (vdc2_A H).product (vdc2_A H),
              (∑ m ∈ vdc2_J a M H, u (m + p.1) * conj (u (m + p.2)))‖ := by
            congr 1
            exact Finset.sum_comm
  calc
    (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ)
        = ‖∑ p ∈ (vdc2_A H).product (vdc2_A H),
              ∑ m ∈ vdc2_J a M H, u (m + p.1) * conj (u (m + p.2))‖ := hnorm
    _ ≤ ∑ p ∈ (vdc2_A H).product (vdc2_A H),
            ‖∑ m ∈ vdc2_J a M H, u (m + p.1) * conj (u (m + p.2))‖ := by
          exact norm_sum_le ((vdc2_A H).product (vdc2_A H))
            (fun p => ∑ m ∈ vdc2_J a M H, u (m + p.1) * conj (u (m + p.2)))
    _ = ∑ p ∈ (vdc2_A H).product (vdc2_A H), ‖vdc2_corr a M u (p.1 - p.2)‖ := by
          apply Finset.sum_congr rfl
          intro p hp
          congr 1
          exact vdc2_sum_J_conj_eq_corr u hu0 (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2


  /-- S = the plain sum of u over I -/
  def vdc2_S (a : ℤ) (M : ℕ) (u : ℤ → ℂ) : ℂ := ∑ n ∈ vdc2_I a M, u n

  /-- pairs (i,j) in A×A with i - j = h -/
  def vdc2fiber (H : ℕ) (h : ℤ) : Finset (ℤ × ℤ) :=
    ((vdc2_A H).product (vdc2_A H)).filter (fun p : ℤ × ℤ => p.1 - p.2 = h)

  /-- difference of a pair from A×A lies in the window -/
  lemma vdc2fiber_mem_Win {H : ℕ} {p : ℤ × ℤ}
      (hp : p ∈ (vdc2_A H).product (vdc2_A H)) : p.1 - p.2 ∈ vdc2_Win H := by
    have h1 : p.1 ∈ Finset.Icc (0 : ℤ) ((H : ℤ) - 1) := by
      simpa [vdc2_A] using (Finset.mem_product.mp hp).1
    have h2 : p.2 ∈ Finset.Icc (0 : ℤ) ((H : ℤ) - 1) := by
      simpa [vdc2_A] using (Finset.mem_product.mp hp).2
    rw [Finset.mem_Icc] at h1 h2
    unfold vdc2_Win
    rw [Finset.mem_Icc]
    constructor <;> omega

  /-- |t| ≤ H-1 for a window element -/
  lemma vdc2_natAbs_le_win {H : ℕ} {h : ℤ} (hh : h ∈ vdc2_Win H) : h.natAbs ≤ H - 1 := by
    rw [vdc2_Win, Finset.mem_Icc] at hh
    have habs : |h| ≤ (H : ℤ) - 1 := by
      rw [abs_le]
      constructor <;> omega
    have hnz : (h.natAbs : ℤ) ≤ (H : ℤ) - 1 := by
      rwa [Int.abs_eq_natAbs] at habs
    have hH1 : 1 ≤ H := by omega
    have hcast : ((H - 1 : ℕ) : ℤ) = (H : ℤ) - 1 := by omega
    rw [← hcast] at hnz
    exact_mod_cast hnz

  /-- fiber cardinal for a nonnegative difference -/
  lemma vdc2fiber_card_ofNat (H : ℕ) (m : ℕ) : (vdc2fiber H (m : ℤ)).card = H - m := by
    have hF : (vdc2fiber H (m : ℤ)).card =
        (Finset.Icc (0 : ℤ) ((H : ℤ) - 1 - (m : ℤ))).card := by
      refine (Finset.card_bij (s := Finset.Icc (0 : ℤ) ((H : ℤ) - 1 - (m : ℤ)))
          (t := vdc2fiber H (m : ℤ))
          (i := fun u _hu => (u + (m : ℤ), u)) ?hi ?hinj ?hsurj).symm
      · intro u hu
        rw [Finset.mem_Icc] at hu
        rw [vdc2fiber, vdc2_A]
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_product.mpr (by
            constructor
            · change u + (m : ℤ) ∈ Finset.Icc (0 : ℤ) ((H : ℤ) - 1)
              rw [Finset.mem_Icc]
              constructor <;> omega
            · change u ∈ Finset.Icc (0 : ℤ) ((H : ℤ) - 1)
              rw [Finset.mem_Icc]
              constructor <;> omega)
        · change (u + (m : ℤ)) - u = (m : ℤ)
          omega
      · intro u1 hu1 u2 hu2 heq
        exact congrArg Prod.snd heq
      · intro p hp
        rw [vdc2fiber, vdc2_A] at hp
        rw [Finset.mem_filter] at hp
        have hp' := hp.1
        have hd : p.1 - p.2 = (m : ℤ) := hp.2
        have hu1 : p.1 ∈ Finset.Icc (0 : ℤ) ((H : ℤ) - 1) := (Finset.mem_product.mp hp').1
        have hu2 : p.2 ∈ Finset.Icc (0 : ℤ) ((H : ℤ) - 1) := (Finset.mem_product.mp hp').2
        rw [Finset.mem_Icc] at hu1 hu2
        refine ⟨p.2, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          constructor <;> omega
        · ext <;> omega
    rw [hF]
    change (Finset.Icc (0 : ℤ) ((H : ℤ) - 1 - (m : ℤ))).card = H - m
    rw [Int.card_Icc]
    have hq : (H : ℤ) - 1 - (m : ℤ) + 1 - 0 = (H : ℤ) - (m : ℤ) := by omega
    rw [hq]
    exact Int.toNat_sub H m

  /-- fiber cardinal is symmetric in the sign of the difference -/
  lemma vdc2fiber_card_neg (H : ℕ) (h : ℤ) : (vdc2fiber H (-h)).card = (vdc2fiber H h).card := by
    refine Finset.card_bij (s := vdc2fiber H (-h)) (t := vdc2fiber H h)
      (i := fun p _hp => (p.2, p.1)) ?hi ?hinj ?hsurj
    · intro p hp
      have hp' : p ∈ (vdc2_A H).product (vdc2_A H) ∧ p.1 - p.2 = -h := by
        rw [vdc2fiber] at hp
        rw [Finset.mem_filter] at hp
        exact hp
      rw [vdc2fiber]
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr ⟨
          (by simpa using (Finset.mem_product.mp hp'.1).2),
          (by simpa using (Finset.mem_product.mp hp'.1).1)⟩
      · change p.2 - p.1 = h
        omega
    · intro p1 hp1 p2 hp2 heq
      have h1 : p1.2 = p2.2 := congrArg Prod.fst heq
      have h2 : p1.1 = p2.1 := congrArg Prod.snd heq
      exact Prod.ext h2 h1
    · intro q hq
      have hq' : q ∈ (vdc2_A H).product (vdc2_A H) ∧ q.1 - q.2 = h := by
        rw [vdc2fiber] at hq
        rw [Finset.mem_filter] at hq
        exact hq
      refine ⟨(q.2, q.1), ?_, ?_⟩
      · rw [vdc2fiber]
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_product.mpr ⟨
            (by simpa using (Finset.mem_product.mp hq'.1).2),
            (by simpa using (Finset.mem_product.mp hq'.1).1)⟩
        · change q.2 - q.1 = -h
          omega
      · rfl

  /-- fiber cardinal equals H - |h| -/
  lemma vdc2fiber_card (H : ℕ) (h : ℤ) : (vdc2fiber H h).card = H - h.natAbs := by
    rcases h with m | m
    · change (vdc2fiber H (m : ℤ)).card = H - m
      exact vdc2fiber_card_ofNat H m
    · change (vdc2fiber H (-((m : ℤ) + 1))).card = H - (m + 1)
      rw [vdc2fiber_card_neg H ((m : ℤ) + 1)]
      simpa using vdc2fiber_card_ofNat H (m + 1)

  /-- weight equals nat difference of card (on the window) -/
  lemma vdc2_w_eq_cast {H : ℕ} {h : ℤ} (hh : h ∈ vdc2_Win H) :
      vdc2_w H h = ((H - h.natAbs : ℕ) : ℝ) := by
    unfold vdc2_w
    have hn : ‖(h : ℝ)‖ = (h.natAbs : ℝ) := by
      rw [Real.norm_eq_abs]
      have hcast : |(h : ℝ)| = ((|h| : ℤ) : ℝ) := by rw [Int.cast_abs]
      rw [hcast]
      congr 1
      exact Int.abs_eq_natAbs h
    rw [hn]
    have hle1 : h.natAbs ≤ H - 1 := vdc2_natAbs_le_win hh
    have hle : h.natAbs ≤ H := by omega
    rw [Nat.cast_sub hle]

  /-- pair sum over A×A equals weighted sum over the window (real-valued) -/
  lemma vdc2_pair_sum_eq_weighted (H : ℕ) (x : ℤ → ℝ) :
      (∑ p ∈ (vdc2_A H).product (vdc2_A H), x (p.1 - p.2)) =
        ∑ h ∈ vdc2_Win H, vdc2_w H h * x h := by
    calc
      (∑ p ∈ (vdc2_A H).product (vdc2_A H), x (p.1 - p.2))
          = ∑ q ∈ (vdc2_Win H).sigma (fun h : ℤ => vdc2fiber H h), x (q.2.1 - q.2.2) := by
            refine Finset.sum_bij
              (s := (vdc2_A H).product (vdc2_A H))
              (t := (vdc2_Win H).sigma (fun h : ℤ => vdc2fiber H h))
              (f := fun p : ℤ × ℤ => x (p.1 - p.2))
              (g := fun q : (Σ _ : ℤ, ℤ × ℤ) => x (q.2.1 - q.2.2))
              (i := fun p _hp => ⟨p.1 - p.2, p⟩) ?hi ?hinj ?hsurj ?hval
            · intro p hp
              exact Finset.mem_sigma.mpr ⟨vdc2fiber_mem_Win hp, by
                rw [vdc2fiber]
                exact Finset.mem_filter.mpr ⟨hp, rfl⟩⟩
            · intro p1 hp1 p2 hp2 heq
              exact congrArg (fun z : (Σ _ : ℤ, ℤ × ℤ) => z.2) heq
            · intro q hq
              have hqf : q.2 ∈ vdc2fiber H q.1 := (Finset.mem_sigma.mp hq).2
              have hqp : q.2 ∈ (vdc2_A H).product (vdc2_A H) ∧ q.2.1 - q.2.2 = q.1 := by
                rw [vdc2fiber] at hqf
                rw [Finset.mem_filter] at hqf
                exact hqf
              refine ⟨q.2, hqp.1, ?_⟩
              · ext
                · simpa using hqp.2
                · rfl
            · intro p hp
              rfl
      _ = ∑ h ∈ vdc2_Win H, ∑ p ∈ vdc2fiber H h, x (p.1 - p.2) := by
            exact Finset.sum_sigma (vdc2_Win H) (fun h : ℤ => vdc2fiber H h)
              (fun q : (Σ _ : ℤ, ℤ × ℤ) => x (q.2.1 - q.2.2))
      _ = ∑ h ∈ vdc2_Win H, ∑ p ∈ vdc2fiber H h, x h := by
            apply Finset.sum_congr rfl
            intro h hh
            apply Finset.sum_congr rfl
            intro p hp
            congr
            have hp' : p ∈ (vdc2_A H).product (vdc2_A H) ∧ p.1 - p.2 = h := by
              rw [vdc2fiber] at hp
              rw [Finset.mem_filter] at hp
              exact hp
            exact hp'.2
      _ = ∑ h ∈ vdc2_Win H, ((vdc2fiber H h).card : ℝ) * x h := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [Finset.sum_const]
            rw [nsmul_eq_mul]
      _ = ∑ h ∈ vdc2_Win H, vdc2_w H h * x h := by
            apply Finset.sum_congr rfl
            intro h hh
            rw [vdc2fiber_card]
            rw [vdc2_w_eq_cast hh]

  /-- cardinal of the shift-index set -/
  lemma vdc2_A_card (H : ℕ) : (vdc2_A H).card = H := by
    unfold vdc2_A
    rw [Int.card_Icc]
    have h : (H : ℤ) - 1 + 1 - 0 = (H : ℤ) := by omega
    rw [h]
    exact Int.toNat_natCast H

  /-- cardinal of the big window -/
  lemma vdc2_J_card (a : ℤ) (M H : ℕ) : (vdc2_J a M H).card = M + H := by
    unfold vdc2_J
    rw [Int.card_Icc]
    have h : (a + (M : ℤ)) + 1 - (a + 1 - (H : ℤ)) = (M : ℤ) + (H : ℤ) := by omega
    rw [h]
    rw [← Nat.cast_add]
    exact Int.toNat_natCast (M + H)

  /-- norm of a natural scalar multiple -/
  lemma vdc2_norm_nat_mul (H : ℕ) (z : ℂ) : ‖(H : ℂ) * z‖ = (H : ℝ) * ‖z‖ := by
    rw [norm_mul]
    congr 1
    rw [← Complex.ofReal_natCast]
    exact (RCLike.norm_ofReal (H : ℝ)).trans (abs_of_nonneg (Nat.cast_nonneg H))

  /-- finite-sum Cauchy-Schwarz bound (complex) -/
  lemma vdc2_norm_sum_sq_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
      (‖∑ i ∈ s, f i‖ ^ 2 : ℝ) ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
    calc
      (‖∑ i ∈ s, f i‖ ^ 2 : ℝ) ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
      _ ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
        exact sq_sum_le_card_mul_sum_sq

  /-- sum of windowed sums equals H times S -/
  lemma vdc2_sum_T_eq {a : ℤ} {M H : ℕ} (u : ℤ → ℂ)
      (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) :
      (∑ m ∈ vdc2_J a M H, vdc2_T H u m) = (H : ℂ) * vdc2_S a M u := by
    calc
      (∑ m ∈ vdc2_J a M H, vdc2_T H u m)
          = ∑ i ∈ vdc2_A H, ∑ m ∈ vdc2_J a M H, u (m + i) := by
            change (∑ m ∈ vdc2_J a M H, ∑ i ∈ vdc2_A H, u (m + i)) =
              ∑ i ∈ vdc2_A H, ∑ m ∈ vdc2_J a M H, u (m + i)
            rw [Finset.sum_comm]
      _ = ∑ i ∈ vdc2_A H, vdc2_S a M u := by
            apply Finset.sum_congr rfl
            intro i hi
            exact vdc2_sum_J_shift_eq_sum_I u hu0 hi
      _ = (H : ℂ) * vdc2_S a M u := by
            rw [Finset.sum_const]
            rw [vdc2_A_card]
            rw [nsmul_eq_mul]

  /-- first bound: |S|² ≤ ((M+H)/H²) · Q  where Q = Σ_m |T m|² -/
  lemma vdc2_S_sq_le {a : ℤ} {M H : ℕ} (hM : 1 ≤ M) (hH : 1 ≤ H) (u : ℤ → ℂ)
      (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) :
      (‖vdc2_S a M u‖ ^ 2 : ℝ) ≤
        (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) *
          (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ) := by
    let x : ℝ := ‖vdc2_S a M u‖ ^ 2
    let Q : ℝ := ∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2
    change x ≤ (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) * Q
    have hcs : ‖(∑ m ∈ vdc2_J a M H, vdc2_T H u m)‖ ^ 2 ≤ (vdc2_J a M H).card * Q := by
      simpa [Q] using (vdc2_norm_sum_sq_le (s := vdc2_J a M H) (f := vdc2_T H u))
    have hsum : (∑ m ∈ vdc2_J a M H, vdc2_T H u m) = (H : ℂ) * vdc2_S a M u :=
      vdc2_sum_T_eq u hu0
    have hcardJ : (vdc2_J a M H).card = M + H := vdc2_J_card a M H
    have hnorm : ‖(H : ℂ) * vdc2_S a M u‖ ^ 2 = (H : ℝ) ^ 2 * x := by
      rw [vdc2_norm_nat_mul]
      simp [x, pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hHpos : 0 < (H : ℝ) := by exact_mod_cast hH
    have hH2pos : 0 < (H : ℝ) ^ 2 := pow_pos hHpos 2
    have hmain : (H : ℝ) ^ 2 * x ≤ ((M : ℝ) + (H : ℝ)) * Q := by
      rw [hsum] at hcs
      rw [hnorm] at hcs
      rw [hcardJ, Nat.cast_add] at hcs
      exact hcs
    calc
      x ≤ (((M : ℝ) + (H : ℝ)) * Q) / (H : ℝ) ^ 2 := by
        exact (le_div_iff₀ hH2pos).mpr (by simpa [mul_comm] using hmain)
      _ = (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) * Q := by
        field_simp [pow_two, (ne_of_gt hHpos).symm]


  /-- second-part bound: Q ≤ the weighted correlation sum -/
  lemma vdc2_Q_le_C {a : ℤ} {M H : ℕ} (u : ℤ → ℂ)
      (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ vdc2_I a M) :
      (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ) ≤
        ∑ t ∈ vdc2_Win H, vdc2_w H t * ‖vdc2_corr a M u t‖ := by
    calc
      (∑ m ∈ vdc2_J a M H, ‖vdc2_T H u m‖ ^ 2 : ℝ)
          ≤ ∑ p ∈ (vdc2_A H).product (vdc2_A H), ‖vdc2_corr a M u (p.1 - p.2)‖ :=
            vdc2_Q_le_weighted u hu0
      _ = ∑ t ∈ vdc2_Win H, vdc2_w H t * ‖vdc2_corr a M u t‖ := by
            exact vdc2_pair_sum_eq_weighted H (fun t : ℤ => ‖vdc2_corr a M u t‖)
end vdc2

end

/-- **Second moment (van der Corput) bound.** -/
theorem vdc_second_moment {a : ℤ} {M H : ℕ} (hM : 1 ≤ M) (hH : 1 ≤ H)
    (u : ℤ → ℂ) (hu0 : ∀ n : ℤ, u n ≠ 0 → n ∈ Finset.Icc (a + 1) (a + (M : ℤ))) :
    (‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), u n‖ : ℝ) ^ 2 ≤
      (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) *
        ∑ t ∈ Finset.Icc (-((H - 1 : ℕ) : ℤ)) ((H - 1 : ℕ) : ℤ),
          ((H : ℝ) - ‖(t : ℝ)‖) *
            ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)), u (n + t) * conj (u n)‖ := by
  rw [← vdc2.vdc2_win_eq H hH]
  change (‖vdc2.vdc2_S a M u‖ ^ 2 : ℝ) ≤
      (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) *
        ∑ t ∈ vdc2.vdc2_Win H, vdc2.vdc2_w H t * ‖vdc2.vdc2_corr a M u t‖
  have hcoef : 0 ≤ (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) := by
    exact div_nonneg (by positivity) (sq_nonneg _)
  have h1 := vdc2.vdc2_S_sq_le hM hH u hu0
  have h2 := vdc2.vdc2_Q_le_C (a := a) (M := M) (H := H) u hu0
  have hqle : (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) *
        (∑ m ∈ vdc2.vdc2_J a M H, ‖vdc2.vdc2_T H u m‖ ^ 2 : ℝ) ≤
      (((M : ℝ) + (H : ℝ)) / (H : ℝ) ^ 2) *
        ∑ t ∈ vdc2.vdc2_Win H, vdc2.vdc2_w H t * ‖vdc2.vdc2_corr a M u t‖ :=
    mul_le_mul_of_nonneg_left h2 hcoef
  exact le_trans h1 hqle

end Commons.Analysis.ExponentialSums

