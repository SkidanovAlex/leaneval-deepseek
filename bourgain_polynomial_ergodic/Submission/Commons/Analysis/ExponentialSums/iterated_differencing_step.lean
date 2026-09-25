import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Basic

namespace Commons.Analysis.ExponentialSums

open Finset
open scoped BigOperators

/-- `Finset.sum` over `range L` with an additive indicator `x + h < L` reduces to `range (L - h)`. -/
lemma sum_range_ite_add_lt {M : Type*} [AddCommMonoid M] (L h : ℕ) (f : ℕ → M) :
    (∑ x ∈ Finset.range L, (if x + h < L then f x else 0))
      = ∑ x ∈ Finset.range (L - h), f x := by
  have h1 : (∑ x ∈ Finset.range (L - h), (if x + h < L then f x else 0))
      = ∑ x ∈ Finset.range (L - h), f x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    rw [if_pos]
    omega
  have h2 : (∑ x ∈ Finset.range (L - h), (if x + h < L then f x else 0))
      = ∑ x ∈ Finset.range L, (if x + h < L then f x else 0) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro x hxL hxs
      rw [Finset.mem_range] at hxL
      simp only [Finset.mem_range, not_lt] at hxs
      rw [if_neg (by omega)]
  rw [← h1, ← h2]

/-- Swap the order of a triangular double sum over `range`. -/
lemma sum_range_triangular_swap {M : Type*} [AddCommMonoid M] (L : ℕ) (g : ℕ → ℕ → M) :
    (∑ x ∈ Finset.range L, ∑ h ∈ Finset.range (L - x), g x h)
      = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), g x h := by
  calc (∑ x ∈ Finset.range L, ∑ h ∈ Finset.range (L - x), g x h)
      = ∑ x ∈ Finset.range L, ∑ h ∈ Finset.range L,
          (if h + x < L then g x h else 0) :=
        Finset.sum_congr rfl (fun x _ => (sum_range_ite_add_lt L x (fun h => g x h)).symm)
    _ = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range L,
          (if h + x < L then g x h else 0) := Finset.sum_comm
    _ = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range L,
          (if x + h < L then g x h else 0) := by
        apply Finset.sum_congr rfl; intro h _
        apply Finset.sum_congr rfl; intro x _
        rw [Nat.add_comm h x]
    _ = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), g x h :=
        Finset.sum_congr rfl (fun h _ => sum_range_ite_add_lt L h (fun x => g x h))

/-- The "shifted-pair" sum indexed by `{(h,x) : h + x < L}` equals the nested `range`-sum. -/
lemma sum_T_eq (L : ℕ) (v : ℕ → ℕ → ℂ) :
    (∑ q ∈ (Finset.range L ×ˢ Finset.range L).filter (fun q : ℕ × ℕ => q.2 + q.1 < L),
        v q.1 q.2)
      = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), v h x := by
  have hprod : (∑ q ∈ (Finset.range L ×ˢ Finset.range L).filter (fun q : ℕ × ℕ => q.2 + q.1 < L),
        v q.1 q.2)
      = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range L,
          (if x + h < L then v h x else 0) := by
    rw [Finset.sum_filter, Finset.sum_product]
  rw [hprod]
  apply Finset.sum_congr rfl
  intro h _
  exact sum_range_ite_add_lt L h (fun x => v h x)

/-- The lower-triangular correlation sum equals `D = Σ_h Σ_x w(x+h) conj(w x)`. -/
lemma sum_Bge_eq (L : ℕ) (w : ℕ → ℂ) :
    (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.2 ≤ p.1),
        w p.1 * star (w p.2))
      = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x) := by
  rw [← sum_T_eq L (fun h x => w (x + h) * star (w x))]
  refine Finset.sum_bij (fun p _ => (p.1 - p.2, p.2)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    omega
  · intro p1 hp1 p2 hp2 heq
    have h1 : p1.2 ≤ p1.1 := (Finset.mem_filter.mp hp1).2
    have h2 : p2.2 ≤ p2.1 := (Finset.mem_filter.mp hp2).2
    simp only [Prod.mk.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    ext <;> omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    refine ⟨(q.1 + q.2, q.2), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · ext <;> omega
  · intro p hp
    have hp' : p.2 ≤ p.1 := (Finset.mem_filter.mp hp).2
    show w p.1 * star (w p.2) = w (p.2 + (p.1 - p.2)) * star (w p.2)
    rw [show p.2 + (p.1 - p.2) = p.1 from by omega]

/-- The upper-triangular correlation sum equals `conj D`. -/
lemma sum_Ble_eq (L : ℕ) (w : ℕ → ℂ) :
    (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.1 ≤ p.2),
        w p.1 * star (w p.2))
      = star (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)) := by
  have hstep : (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.1 ≤ p.2),
        w p.1 * star (w p.2))
      = ∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w x * star (w (x + h)) := by
    rw [← sum_T_eq L (fun h x => w x * star (w (x + h)))]
    refine Finset.sum_bij (fun p _ => (p.2 - p.1, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
      omega
    · intro p1 hp1 p2 hp2 heq
      have h1 : p1.1 ≤ p1.2 := (Finset.mem_filter.mp hp1).2
      have h2 : p2.1 ≤ p2.2 := (Finset.mem_filter.mp hp2).2
      simp only [Prod.mk.injEq] at heq
      obtain ⟨e1, e2⟩ := heq
      ext <;> omega
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
      refine ⟨(q.2, q.1 + q.2), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        omega
      · ext <;> omega
    · intro p hp
      have hp' : p.1 ≤ p.2 := (Finset.mem_filter.mp hp).2
      show w p.1 * star (w p.2) = w p.1 * star (w (p.1 + (p.2 - p.1)))
      rw [show p.1 + (p.2 - p.1) = p.2 from by omega]
  rw [hstep, star_sum]
  apply Finset.sum_congr rfl; intro h _
  rw [star_sum]
  apply Finset.sum_congr rfl; intro x _
  rw [star_mul, star_star]

/-- The diagonal correlation sum equals `Σ_x w x conj(w x)`. -/
lemma sum_Beq_eq (L : ℕ) (w : ℕ → ℂ) :
    (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.1 = p.2),
        w p.1 * star (w p.2))
      = ∑ x ∈ Finset.range L, w x * star (w x) := by
  have hprod : (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.1 = p.2),
        w p.1 * star (w p.2))
      = ∑ x ∈ Finset.range L, ∑ y ∈ Finset.range L,
          (if x = y then w x * star (w y) else 0) := by
    rw [Finset.sum_filter, Finset.sum_product]
  rw [hprod]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_ite_eq, if_pos hx]

/-- The full double sum splits into the two triangles minus the diagonal. -/
lemma sum_triangle_split (L : ℕ) (w : ℕ → ℂ) :
    (∑ p ∈ (Finset.range L ×ˢ Finset.range L), w p.1 * star (w p.2))
      = (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.2 ≤ p.1),
          w p.1 * star (w p.2))
        + (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.1 ≤ p.2),
          w p.1 * star (w p.2))
        - (∑ p ∈ (Finset.range L ×ˢ Finset.range L).filter (fun p : ℕ × ℕ => p.1 = p.2),
          w p.1 * star (w p.2)) := by
  have hpt : ∀ p ∈ (Finset.range L ×ˢ Finset.range L), w p.1 * star (w p.2)
      = (if p.2 ≤ p.1 then w p.1 * star (w p.2) else 0)
        + (if p.1 ≤ p.2 then w p.1 * star (w p.2) else 0)
        - (if p.1 = p.2 then w p.1 * star (w p.2) else 0) := by
    intro p _
    by_cases h1 : p.2 ≤ p.1
    · by_cases h2 : p.1 ≤ p.2
      · have he : p.1 = p.2 := le_antisymm h2 h1
        simp [he]
      · have hne : ¬ (p.1 = p.2) := by omega
        simp [h1, h2, hne]
    · have h2 : p.1 ≤ p.2 := by omega
      have hne : ¬ (p.1 = p.2) := by omega
      simp [h1, h2, hne]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.sum_filter (s := (Finset.range L ×ˢ Finset.range L))
        (p := fun p : ℕ × ℕ => p.2 ≤ p.1) (f := fun p => w p.1 * star (w p.2)),
      ← Finset.sum_filter (s := (Finset.range L ×ˢ Finset.range L))
        (p := fun p : ℕ × ℕ => p.1 ≤ p.2) (f := fun p => w p.1 * star (w p.2)),
      ← Finset.sum_filter (s := (Finset.range L ×ˢ Finset.range L))
        (p := fun p : ℕ × ℕ => p.1 = p.2) (f := fun p => w p.1 * star (w p.2))]

open Finset in
theorem iterated_differencing_step (L : ℕ) (w : ℕ → ℂ) :
    ‖∑ x ∈ Finset.range L, w x‖ ^ 2
      ≤ 2 * ∑ h ∈ Finset.range L,
          ‖∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)‖ := by
  classical
  have hW : (∑ p ∈ (Finset.range L ×ˢ Finset.range L), w p.1 * star (w p.2))
      = ((‖∑ x ∈ Finset.range L, w x‖ ^ 2 : ℝ) : ℂ) := by
    have hprod : (∑ p ∈ (Finset.range L ×ˢ Finset.range L), w p.1 * star (w p.2))
        = ∑ x ∈ Finset.range L, ∑ y ∈ Finset.range L, w x * star (w y) := by
      rw [Finset.sum_product]
    rw [hprod, ← Finset.sum_mul_sum, ← star_sum, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rfl
  have hcomplex : ((‖∑ x ∈ Finset.range L, w x‖ ^ 2 : ℝ) : ℂ)
      = (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))
        + star (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))
        - ∑ x ∈ Finset.range L, w x * star (w x) := by
    rw [← hW, sum_triangle_split, sum_Bge_eq, sum_Ble_eq, sum_Beq_eq]
  have hD_re : ((∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))).re
      = ∑ h ∈ Finset.range L,
          (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re :=
    Complex.re_sum _ _
  have hC0_re : ((∑ x ∈ Finset.range L, w x * star (w x))).re
      = ∑ x ∈ Finset.range L, ‖w x‖ ^ 2 := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hx : w x * star (w x) = ((Complex.normSq (w x) : ℝ) : ℂ) := by
      simpa using Complex.mul_conj (w x)
    rw [hx, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hreal : ‖∑ x ∈ Finset.range L, w x‖ ^ 2
      = 2 * (∑ h ∈ Finset.range L,
              (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re)
        - ∑ x ∈ Finset.range L, ‖w x‖ ^ 2 := by
    have h1 := congrArg Complex.re hcomplex
    simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re] at h1
    have hsr : (star (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x))).re
        = (∑ h ∈ Finset.range L, ∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re :=
      Complex.conj_re _
    rw [hsr, hD_re, hC0_re] at h1
    rw [h1, two_mul]
  calc ‖∑ x ∈ Finset.range L, w x‖ ^ 2
      = 2 * (∑ h ∈ Finset.range L,
              (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re)
        - ∑ x ∈ Finset.range L, ‖w x‖ ^ 2 := hreal
    _ ≤ 2 * (∑ h ∈ Finset.range L,
              (∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)).re) := by
        have hnn : (0 : ℝ) ≤ ∑ x ∈ Finset.range L, ‖w x‖ ^ 2 :=
          Finset.sum_nonneg (fun x _ => sq_nonneg _)
        linarith
    _ ≤ 2 * (∑ h ∈ Finset.range L,
              ‖∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum (fun h _ => Complex.re_le_norm _)
    _ = 2 * ∑ h ∈ Finset.range L,
          ‖∑ x ∈ Finset.range (L - h), w (x + h) * star (w x)‖ := rfl

end Commons.Analysis.ExponentialSums