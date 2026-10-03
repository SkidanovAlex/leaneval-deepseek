import Mathlib
import Submission.Work.Peluse.SwapC.concatAssemble

/-!
# The expansion of `‖gauge‖²` for the concatenation step

The gauge of the concatenation step (`Work.Peluse.SwapC.gauge`) is the `Rest`-product of the
hypothesis, averaged over the index `i` and over the pair of shift tuples, with the normalising
factor of `pboxSum` in front.  Squaring its modulus and summing over the base variable `y` expands
into the *doubled* `Rest`-product over two independent indices (`Work.Peluse.SwapC.pairObj`), the
object that `concat_ident` recognises as the box inner product over the `2s` doubled slots.

This file contains that elementary expansion, together with the two bookkeeping lemmas it needs:
`Rest` is finitely supported (it dies at the first basic shift), and the first increment of the
`concatStep` slot tuple is bounded by `2·M·|qH|`.
-/

namespace Work.Peluse.SwapC

open scoped BigOperators

/-- The product of two doubly nested finite sums. -/
lemma mul_nested_sum_prod {P : Type} [Fintype P] {R : Type} [NonUnitalNonAssocSemiring R]
    (A B : P → P → R) :
    (∑ a, ∑ b, A a b) * (∑ c, ∑ d, B c d) = ∑ a, ∑ b, ∑ c, ∑ d, A a b * B c d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]

/-- The `Rest`-product vanishes outside the support of `f`: the sign pattern with a single `1` at
the first coordinate isolates the basic shift `y + v 0`. -/
lemma Rest_eq_zero_of_natAbs_gt {d : ℕ} (hd : 0 < d) (v : Fin d → ℤ) (f : ℤ → ℂ) {N : ℕ}
    (hN : Work.Peluse.SupportIn f N) {y : ℤ} (hy : N + (v ⟨0, hd⟩).natAbs < y.natAbs) :
    Rest v f y = 0 := by
  have htri : y.natAbs ≤ (y + v ⟨0, hd⟩).natAbs + (v ⟨0, hd⟩).natAbs := by
    have h := Int.natAbs_add_le (y + v ⟨0, hd⟩) (-(v ⟨0, hd⟩))
    simpa [Int.natAbs_neg, add_assoc] using h
  have hy' : N < (y + v ⟨0, hd⟩).natAbs := by omega
  have hf0 : f (y + v ⟨0, hd⟩) = 0 := hN _ hy'
  rw [Rest]
  refine Finset.prod_eq_zero (i := fun i : Fin d => decide (i = ⟨0, hd⟩)) ?_ ?_
  · rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have h2 : (fun i : Fin d => decide (i = ⟨0, hd⟩)) ⟨0, hd⟩
        = (0 : Fin d → Bool) ⟨0, hd⟩ := by rw [h]
    simp at h2
  · have hsh : cornerShift v (fun _ => 0) (fun i : Fin d => decide (i = ⟨0, hd⟩)) = v ⟨0, hd⟩ := by
      rw [cornerShift]
      rw [Finset.sum_eq_single ⟨0, hd⟩]
      · simp
      · intro i _ hi
        have : (decide (i = ⟨0, hd⟩) : Bool) = false := by
          simp [hi]
        simp [this]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsh, hf0]
    exact Function.iterate_fixed (by simp) (weight (fun i : Fin d => decide (i = ⟨0, hd⟩)))

/-- The first component of the `concatStep` increment tuple is bounded by `2·M·|qH|`. -/
lemma incr_zero_natAbs_le (s M : ℕ) (qH : ℤ) (q₁ q₂ : Fin s → ℤ)
    (H H' : Fin (s+1) → Fin M × Fin M) :
    (incr s M qH q₁ q₂ H H' 0).natAbs ≤ 2 * M * qH.natAbs := by
  rw [incr]
  simp only [Fin.cons_zero]
  rw [pdir_zero_right, pdir_zero_right]
  have hc1 : ((H 0).1 : ℕ) + 1 ≤ M := by
    have := (H 0).1.isLt; omega
  have hc2 : ((H' 0).1 : ℕ) + 1 ≤ M := by
    have := (H' 0).1.isLt; omega
  have hkey : qH * ((((H 0).1 : ℕ) : ℤ) + 1) - qH * ((((H' 0).1 : ℕ) : ℤ) + 1)
      = qH * (((((H 0).1 : ℕ) + 1 : ℕ) : ℤ) - ((((H' 0).1 : ℕ) + 1 : ℕ) : ℤ)) := by
    push_cast; ring
  rw [hkey, Int.natAbs_mul]
  have hd : ((((((H 0).1 : ℕ) + 1 : ℕ) : ℤ) - ((((H' 0).1 : ℕ) + 1 : ℕ) : ℤ))).natAbs ≤ M :=
    Int.natAbs_coe_sub_coe_le_of_le hc1 hc2
  calc qH.natAbs * ((((((H 0).1 : ℕ) + 1 : ℕ) : ℤ) - ((((H' 0).1 : ℕ) + 1 : ℕ) : ℤ))).natAbs
      ≤ qH.natAbs * M := Nat.mul_le_mul_left _ hd
    _ = M * qH.natAbs := Nat.mul_comm _ _
    _ ≤ 2 * (M * qH.natAbs) := Nat.le_mul_of_pos_left _ (by norm_num)
    _ = 2 * M * qH.natAbs := by ring

/-- A `tsum` over a finite sum of functions with a common finite support set. -/
lemma tsum_sum_of_vanishing {ι : Type} [Fintype ι] {T : Finset ℤ} (g : ι → ℤ → ℂ)
    (h : ∀ i y, y ∉ T → g i y = 0) :
    (∑' y : ℤ, ∑ i : ι, g i y) = ∑ i : ι, ∑' y : ℤ, g i y := by
  classical
  rw [tsum_eq_sum (s := T) (f := fun y => ∑ i : ι, g i y)
      (fun y hy => Finset.sum_eq_zero fun i _ => h i y hy)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (tsum_eq_sum (s := T) (f := g i) (fun y hy => h i y hy)).symm

/-- A `tsum` over six nested finite sums of functions with a common finite support set. -/
lemma tsum_sum6_of_vanishing {A B C D E F : Type} [Fintype A] [Fintype B] [Fintype C]
    [Fintype D] [Fintype E] [Fintype F] {T : Finset ℤ}
    (g : A → B → C → D → E → F → ℤ → ℂ)
    (h : ∀ a b c d e f y, y ∉ T → g a b c d e f y = 0) :
    (∑' y : ℤ, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y)
      = ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, ∑' y : ℤ, g a b c d e f y := by
  classical
  have h1 : (∑' y : ℤ, ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y)
      = ∑ a, ∑' y : ℤ, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y :=
    tsum_sum_of_vanishing (T := T) (g := fun a y => ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y)
      (fun a y hy => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
        Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e _ =>
          Finset.sum_eq_zero fun f _ => h a b c d e f y hy)
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h2 : (∑' y : ℤ, ∑ b, ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y)
      = ∑ b, ∑' y : ℤ, ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y :=
    tsum_sum_of_vanishing (T := T) (g := fun b y => ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y)
      (fun b y hy => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ =>
        Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun f _ => h a b c d e f y hy)
  rw [h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h3 : (∑' y : ℤ, ∑ c, ∑ d, ∑ e, ∑ f, g a b c d e f y)
      = ∑ c, ∑' y : ℤ, ∑ d, ∑ e, ∑ f, g a b c d e f y :=
    tsum_sum_of_vanishing (T := T) (g := fun c y => ∑ d, ∑ e, ∑ f, g a b c d e f y)
      (fun c y hy => Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e _ =>
        Finset.sum_eq_zero fun f _ => h a b c d e f y hy)
  rw [h3]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h4 : (∑' y : ℤ, ∑ d, ∑ e, ∑ f, g a b c d e f y)
      = ∑ d, ∑' y : ℤ, ∑ e, ∑ f, g a b c d e f y :=
    tsum_sum_of_vanishing (T := T) (g := fun d y => ∑ e, ∑ f, g a b c d e f y)
      (fun d y hy => Finset.sum_eq_zero fun e _ =>
        Finset.sum_eq_zero fun f _ => h a b c d e f y hy)
  rw [h4]
  refine Finset.sum_congr rfl fun d _ => ?_
  have h5 : (∑' y : ℤ, ∑ e, ∑ f, g a b c d e f y)
      = ∑ e, ∑' y : ℤ, ∑ f, g a b c d e f y :=
    tsum_sum_of_vanishing (T := T) (g := fun e y => ∑ f, g a b c d e f y)
      (fun e y hy => Finset.sum_eq_zero fun f _ => h a b c d e f y hy)
  rw [h5]
  refine Finset.sum_congr rfl fun e _ => ?_
  have h6 : (∑' y : ℤ, ∑ f, g a b c d e f y)
      = ∑ f, ∑' y : ℤ, g a b c d e f y :=
    tsum_sum_of_vanishing (T := T) (g := fun f y => g a b c d e f y)
      (fun f y hy => h a b c d e f y hy)
  rw [h6]

/-- **The expansion of `‖gauge‖²`**: the squared modulus of the gauge is the average over the two
indices of the doubled `Rest`-product, with the norms of the two normalising factors pulled out.
This is the object that `concat_ident` turns into the box inner product. -/
theorem gauge_sq_eq {I : Type} [Fintype I] [Nonempty I] (s M : ℕ) (qH : I → ℤ)
    (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ) (hsup : Work.Peluse.FinSuppZ f) :
    (∑' y : ℤ, ‖Work.Peluse.SwapC.gauge s M qH q₁ q₂ f y‖ ^ 2)
      = ‖(((M : ℂ) ^ 4)⁻¹) ^ (s + 1)‖ ^ 2 * ‖(((Fintype.card I : ℂ))⁻¹)‖ ^ 2 *
        ∑ i₀ : I, ∑ i₁ : I, ∑ H₀ : Fin (s + 1) → Fin M × Fin M,
          ∑ H₀' : Fin (s + 1) → Fin M × Fin M, ∑ H₁ : Fin (s + 1) → Fin M × Fin M,
            ∑ H₁' : Fin (s + 1) → Fin M × Fin M,
              Work.Peluse.SwapC.pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ H₁' := by
  classical
  obtain ⟨N, hN⟩ := hsup
  -- a finite set containing the support of every `Rest`-product occurring in the gauge
  set Bq : ℕ := ∑ i : I, (qH i).natAbs with hBq
  set K : ℕ := N + 2 * M * Bq with hK
  set T : Finset ℤ := Finset.Icc (-(K : ℤ)) K with hT
  have hmemT : ∀ y : ℤ, y ∉ T → K < y.natAbs := by
    intro y hy
    have hy' : ¬ (-(K : ℤ) ≤ y ∧ y ≤ (K : ℤ)) := by
      intro h
      exact hy (by rw [hT, Finset.mem_Icc]; exact h)
    by_cases hcase : y < -(K : ℤ)
    · have h1 : (K : ℤ) < -y := by omega
      have h2 : ((-y).natAbs : ℤ) = -y := Int.natAbs_of_nonneg (by omega)
      have h3 : (K : ℤ) < (y.natAbs : ℤ) := by
        rw [← Int.natAbs_neg y, h2]; exact h1
      exact Int.ofNat_lt.mp h3
    · push Not at hcase
      have h1 : (K : ℤ) < y := by
        by_contra hc
        push Not at hc
        exact hy' ⟨hcase, hc⟩
      have h2 : (y.natAbs : ℤ) = y := Int.natAbs_of_nonneg (by omega)
      have h3 : (K : ℤ) < (y.natAbs : ℤ) := by rw [h2]; exact h1
      exact Int.ofNat_lt.mp h3
  have hRzero : ∀ (i : I) (H H' : Fin (s+1) → Fin M × Fin M) (y : ℤ),
      y ∉ T → Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y = 0 := by
    intro i H H' y hy
    refine Rest_eq_zero_of_natAbs_gt (d := s+1) (Nat.succ_pos s)
      (incr s M (qH i) (q₁ i) (q₂ i) H H') f hN ?_
    have hqi : (qH i).natAbs ≤ Bq := by
      rw [hBq]
      exact Finset.single_le_sum (f := fun j : I => (qH j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have hb : (incr s M (qH i) (q₁ i) (q₂ i) H H' ⟨0, Nat.succ_pos s⟩).natAbs
        ≤ 2 * M * (qH i).natAbs :=
      incr_zero_natAbs_le s M (qH i) (q₁ i) (q₂ i) H H'
    have hb2 : (incr s M (qH i) (q₁ i) (q₂ i) H H' ⟨0, Nat.succ_pos s⟩).natAbs
        ≤ 2 * M * Bq := le_trans hb (Nat.mul_le_mul_left (2 * M) hqi)
    have hle : N + (incr s M (qH i) (q₁ i) (q₂ i) H H' ⟨0, Nat.succ_pos s⟩).natAbs ≤ K := by
      rw [hK]; exact Nat.add_le_add_left hb2 N
    exact lt_of_le_of_lt hle (hmemT y hy)
  -- the inner sum of the gauge
  set Sfun : ℤ → ℂ := fun y => ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M,
      ∑ H' : Fin (s+1) → Fin M × Fin M, Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y
    with hSfun
  have hSu : ∀ y : ℤ, Sfun y = ∑ i : I, ∑ H : Fin (s+1) → Fin M × Fin M,
      ∑ H' : Fin (s+1) → Fin M × Fin M, Rest (incr s M (qH i) (q₁ i) (q₂ i) H H') f y :=
    fun y => by rw [hSfun]
  -- step 1: pull the two normalising constants out of the norm
  have hnorm : ∀ y : ℤ, ‖gauge s M qH q₁ q₂ f y‖ ^ 2
      = ‖(((M : ℂ) ^ 4)⁻¹) ^ (s + 1)‖ ^ 2 * ‖(((Fintype.card I : ℂ))⁻¹)‖ ^ 2 *
        ‖Sfun y‖ ^ 2 := by
    intro y
    rw [hSfun]
    simp only [gauge, norm_mul]
    ring
  have hstep1 : (∑' y : ℤ, ‖gauge s M qH q₁ q₂ f y‖ ^ 2)
      = ‖(((M : ℂ) ^ 4)⁻¹) ^ (s + 1)‖ ^ 2 * ‖(((Fintype.card I : ℂ))⁻¹)‖ ^ 2 *
        (∑' y : ℤ, ‖Sfun y‖ ^ 2) := by
    rw [tsum_congr hnorm, tsum_mul_left]
  -- step 2: expand `‖Sfun‖²` into the doubled `Rest`-product
  have hconj : ∀ y : ℤ, (↑(‖Sfun y‖ ^ 2) : ℂ) = Sfun y * star (Sfun y) := by
    intro y
    rw [Complex.sq_norm]
    exact (Complex.mul_conj (Sfun y)).symm
  have hW : ∀ y : ℤ, Sfun y * star (Sfun y)
      = ∑ i₀ : I, ∑ i₁ : I, ∑ H₀ : Fin (s+1) → Fin M × Fin M,
          ∑ H₀' : Fin (s+1) → Fin M × Fin M, ∑ H₁ : Fin (s+1) → Fin M × Fin M,
            ∑ H₁' : Fin (s+1) → Fin M × Fin M,
              Rest (incr s M (qH i₀) (q₁ i₀) (q₂ i₀) H₀ H₀') f y *
                star (Rest (incr s M (qH i₁) (q₁ i₁) (q₂ i₁) H₁ H₁') f y) := by
    intro y
    rw [hSu y]
    simp only [star_sum]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun i₁ _ => ?_
    exact mul_nested_sum_prod
      (fun H₀ H₀' => Rest (incr s M (qH i₀) (q₁ i₀) (q₂ i₀) H₀ H₀') f y)
      (fun H₁ H₁' => star (Rest (incr s M (qH i₁) (q₁ i₁) (q₂ i₁) H₁ H₁') f y))
  have hterm0 : ∀ (i₀ i₁ : I) (H₀ H₀' H₁ H₁' : Fin (s+1) → Fin M × Fin M) (y : ℤ),
      y ∉ T → Rest (incr s M (qH i₀) (q₁ i₀) (q₂ i₀) H₀ H₀') f y *
        star (Rest (incr s M (qH i₁) (q₁ i₁) (q₂ i₁) H₁ H₁') f y) = 0 := by
    intro i₀ i₁ H₀ H₀' H₁ H₁' y hy
    rw [hRzero i₀ H₀ H₀' y hy, zero_mul]
  have hstep2 : (↑(∑' y : ℤ, ‖Sfun y‖ ^ 2) : ℂ)
      = ∑ i₀ : I, ∑ i₁ : I, ∑ H₀ : Fin (s + 1) → Fin M × Fin M,
          ∑ H₀' : Fin (s + 1) → Fin M × Fin M, ∑ H₁ : Fin (s + 1) → Fin M × Fin M,
            ∑ H₁' : Fin (s + 1) → Fin M × Fin M,
              pairObj s M qH q₁ q₂ f i₀ i₁ H₀ H₀' H₁ H₁' := by
    rw [Complex.ofReal_tsum]
    rw [tsum_congr hconj]
    rw [tsum_congr hW]
    rw [tsum_sum6_of_vanishing (T := T)
      (g := fun i₀ i₁ H₀ H₀' H₁ H₁' y =>
        Rest (incr s M (qH i₀) (q₁ i₀) (q₂ i₀) H₀ H₀') f y *
          star (Rest (incr s M (qH i₁) (q₁ i₁) (q₂ i₁) H₁ H₁') f y))
      (fun i₀ i₁ H₀ H₀' H₁ H₁' y hy => hterm0 i₀ i₁ H₀ H₀' H₁ H₁' y hy)]
    refine Finset.sum_congr rfl fun i₀ _ => ?_
    refine Finset.sum_congr rfl fun i₁ _ => ?_
    refine Finset.sum_congr rfl fun H₀ _ => ?_
    refine Finset.sum_congr rfl fun H₀' _ => ?_
    refine Finset.sum_congr rfl fun H₁ _ => ?_
    refine Finset.sum_congr rfl fun H₁' _ => ?_
    rfl
  -- assembly
  rw [hstep1, Complex.ofReal_mul, Complex.ofReal_mul, hstep2, Complex.ofReal_pow,
    Complex.ofReal_pow]

end Work.Peluse.SwapC
