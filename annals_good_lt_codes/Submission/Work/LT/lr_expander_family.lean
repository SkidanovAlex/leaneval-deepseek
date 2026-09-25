import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.sl3_gap
import Submission.Work.LT.sl3_card_le
import Submission.Work.LT.dirichlet_left
import Submission.Work.LT.quad_symm_left
import Submission.Work.LT.sum_mul_sum_le_left
import Submission.Work.LT.alpha_dirichlet
import Submission.Work.LT.alpha_quad
import Submission.Work.LT.op_contract_meanzero
import Submission.Work.LT.lr_family_defs

/-!
# `lr_expander_family`: expanding families for the left-right Cayley complex

The lists required by `lr_expander_family` are built from the lazy symmetric generating list of
`SL₃(ℤ/p)`.  The alphabet `alpha g` has `48` letters indexed by `Fin 12 × Bool × Bool`: the `12`
generators, their `12` inverses, and `24` identities.  The single-step left walk contracts
mean-zero functions by `theta c`, where `c` is the Kazhdan constant supplied by `sl3_gap`; taking
all words of a fixed length `k` gives the `k`-th power of the walk, and the right walk follows
from the left walk by composing with `x ↦ x⁻¹`.

Nothing in the construction depends on `p` beyond the existence of the gap, so a single `k` and a
single degree `Δ = 48 ^ k` serve every `m`.
-/

namespace Work.LT.RF

open Finset

variable {G : Type*} [Group G] [Fintype G]

/-! ### Elementary summation lemmas -/

/-- Unnormalised left-averaging walk sum of a list. -/
noncomputable def uOp {G : Type*} [Group G] {ι : Type*} [Fintype ι] (v : ι → G) (f : G → ℝ) :
    G → ℝ := fun x => ∑ a, f (v a * x)

lemma lOp_apply {ι : Type*} [Fintype ι] (v : ι → G) (f : G → ℝ) (x : G) :
    lOp v f x = uOp v f x / (Fintype.card ι : ℝ) := rfl

lemma sum_mulLeft (a : G) (F : G → ℝ) : (∑ x, F (a * x)) = ∑ x, F x :=
  Equiv.sum_comp (Equiv.mulLeft a) F

lemma sum_mulRight (a : G) (F : G → ℝ) : (∑ x, F (x * a)) = ∑ x, F x :=
  Equiv.sum_comp (Equiv.mulRight a) F

lemma sum_comp_inv (F : G → ℝ) : (∑ x, F x⁻¹) = ∑ x, F x :=
  Equiv.sum_comp (Equiv.inv G) F

omit [Group G] in
lemma l2_nonneg (f : G → ℝ) : 0 ≤ l2 f := by
  simp only [l2]
  exact Finset.sum_nonneg fun x _ => sq_nonneg _

lemma l2_inv (f : G → ℝ) : l2 (fun x => f x⁻¹) = l2 f := by
  simp only [l2]
  exact sum_comp_inv fun y => f y ^ 2

lemma uOp_mean_zero {ι : Type*} [Fintype ι] (v : ι → G) (f : G → ℝ)
    (hf : ∑ x, f x = 0) : ∑ x, uOp v f x = 0 := by
  simp only [uOp]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun a _ => by rw [sum_mulLeft (v a) f, hf]

lemma lOp_mean_zero {ι : Type*} [Fintype ι] (v : ι → G) (f : G → ℝ)
    (hf : ∑ x, f x = 0) : ∑ x, lOp v f x = 0 := by
  have h : lOp v f = fun x => uOp v f x / (Fintype.card ι : ℝ) := funext (lOp_apply v f)
  rw [h, ← Finset.sum_div, uOp_mean_zero v f hf, zero_div]

lemma rOp_mean_zero {ι : Type*} [Fintype ι] (v : ι → G) (f : G → ℝ)
    (hf : ∑ x, f x = 0) : ∑ x, rOp v f x = 0 := by
  simp only [rOp]
  rw [← Finset.sum_div]
  have h : (∑ x, ∑ a, f (x * v a)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun a _ => by rw [sum_mulRight (v a) f, hf]
  rw [h, zero_div]

lemma sum_lOp_mul {ι : Type*} [Fintype ι] (v : ι → G) (f h : G → ℝ) :
    (∑ x, lOp v f x * h x) = (∑ a, ∑ x, f (v a * x) * h x) / (Fintype.card ι : ℝ) := by
  calc ∑ x, lOp v f x * h x
      = ∑ x, (uOp v f x / (Fintype.card ι : ℝ)) * h x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [lOp_apply]
    _ = ∑ x, (∑ a, f (v a * x) * h x) / (Fintype.card ι : ℝ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [uOp]
        rw [div_mul_eq_mul_div, Finset.sum_mul]
    _ = (∑ x, ∑ a, f (v a * x) * h x) / (Fintype.card ι : ℝ) := by rw [Finset.sum_div]
    _ = (∑ a, ∑ x, f (v a * x) * h x) / (Fintype.card ι : ℝ) := by rw [Finset.sum_comm]

lemma lOp_symm {ι : Type*} [Fintype ι] (v : ι → G) (η : ι ≃ ι) (hη : ∀ a, v (η a) = (v a)⁻¹)
    (u w : G → ℝ) :
    (∑ x, lOp v u x * w x) = ∑ x, lOp v w x * u x := by
  rw [sum_lOp_mul v u w, sum_lOp_mul v w u, quad_symm_left v η hη u w]

/-! ### The lazy alphabet and the single-step walk -/

/-- The contraction constant of the lazy walk. -/
noncomputable def theta (c : ℝ) : ℝ := max (1 - c / 48) 0

lemma theta_nonneg (c : ℝ) : 0 ≤ theta c := le_max_right _ _

lemma theta_lt_one {c : ℝ} (hc : 0 < c) : theta c < 1 := max_lt (by linarith) one_pos

lemma card_alpha : Fintype.card (Fin 12 × Bool × Bool) = 48 := by
  norm_num [Fintype.card_prod, Fintype.card_bool]

lemma card_alpha_cast : ((Fintype.card (Fin 12 × Bool × Bool) : ℕ) : ℝ) = 48 := by
  rw [card_alpha]; norm_num

/-- The quadratic form of the lazy alphabet is at most `(1 - c/48)‖f‖²` on mean-zero `f`. -/
lemma alpha_quad_le (g : Fin 12 → G) (c : ℝ) (_hc : 0 < c)
    (hgap : ∀ f : G → ℝ, (∑ x, f x = 0) →
      c * l2 f ≤ ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2)
    (f : G → ℝ) (hf : ∑ x, f x = 0) :
    (∑ x, lOp (alpha g) f x * f x) ≤ (1 - c / 48) * l2 f := by
  have hs := alpha_dirichlet g f
  have hq := sum_lOp_mul (alpha g) f f
  have hcs := card_alpha_cast
  have hd : (∑ a : Fin 12 × Bool × Bool, ∑ x, (f (alpha g a * x) - f x) ^ 2)
      = 2 * (48 : ℝ) * l2 f
        - 2 * ∑ a : Fin 12 × Bool × Bool, ∑ x, f (alpha g a * x) * f x := by
    simpa only [hcs, l2] using dirichlet_left (alpha g) f
  have hkey : (∑ a : Fin 12 × Bool × Bool, ∑ x, f (alpha g a * x) * f x)
      = 48 * l2 f - ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2 := by
    linarith [hd, hs]
  rw [hq, hcs, hkey]
  have hD2 : c * l2 f ≤ ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2 := hgap f hf
  calc (48 * l2 f - ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2) / 48
      = l2 f - (∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2) / 48 := by ring
    _ ≤ l2 f - c * l2 f / 48 := by linarith
    _ = (1 - c / 48) * l2 f := by ring

/-- The quadratic form of the lazy alphabet is nonnegative (the walk is lazy). -/
lemma alpha_quad_nonneg (g : Fin 12 → G) (f : G → ℝ) :
    0 ≤ ∑ x, lOp (alpha g) f x * f x := by
  have hq := sum_lOp_mul (alpha g) f
  have ha := alpha_quad g f
  have hcs := card_alpha_cast
  have hCS : -((12 : ℝ) * l2 f) ≤ ∑ i : Fin 12, ∑ x, f (g i * x) * f x := by
    have h := sum_mul_sum_le_left g f
    simp only [Fintype.card_fin] at h
    have he : (∑ a : Fin 12, ∑ x, f x * f (g a * x))
        = ∑ a : Fin 12, ∑ x, f (g a * x) * f x :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [he] at h
    push_cast at h
    simp only [l2]
    exact h
  rw [hq, hcs, ha]
  apply div_nonneg _ (by norm_num)
  linarith

/-- Contraction of the single-step lazy walk. -/
lemma alpha_contract (g : Fin 12 → G) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ f : G → ℝ, (∑ x, f x = 0) →
      c * l2 f ≤ ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2)
    (f : G → ℝ) (hf : ∑ x, f x = 0) :
    l2 (lOp (alpha g) f) ≤ (theta c) ^ 2 * l2 f := by
  have hmain := op_contract_meanzero (lOp (alpha g)) (theta c) (theta_nonneg c)
    (fun u w => lOp_symm (alpha g) eta (alpha_eta g) u w)
    (fun u => alpha_quad_nonneg g u)
    (fun u hu => by
      refine le_trans (alpha_quad_le g c hc hgap u hu) ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (l2_nonneg u))
    (fun u hu => lOp_mean_zero (alpha g) u hu) f hf
  simpa only [l2] using hmain

/-- The right walk is the left walk of the inverted function, composed with inversion. -/
lemma rOp_eq {ι : Type*} [Fintype ι] (v : ι → G) (η : ι ≃ ι) (hη : ∀ a, v (η a) = (v a)⁻¹)
    (f : G → ℝ) :
    rOp v f = fun x => lOp v (fun y => f y⁻¹) x⁻¹ := by
  funext x
  simp only [rOp, lOp_apply, uOp]
  congr 1
  rw [← Equiv.sum_comp η (fun a => f ((v a * x⁻¹)⁻¹))]
  exact Finset.sum_congr rfl fun a _ => by simp [hη a, mul_inv_rev]

/-- Contraction of the single-step right walk (via the left walk and inversion). -/
lemma rOp_alpha_contract (g : Fin 12 → G) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ f : G → ℝ, (∑ x, f x = 0) →
      c * l2 f ≤ ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2)
    (f : G → ℝ) (hf : ∑ x, f x = 0) :
    l2 (rOp (alpha g) f) ≤ (theta c) ^ 2 * l2 f := by
  have h1 : rOp (alpha g) f = fun x => lOp (alpha g) (fun y => f y⁻¹) x⁻¹ :=
    rOp_eq (alpha g) eta (alpha_eta g) f
  have hmz : (∑ x, (fun y : G => f y⁻¹) x) = 0 := by
    rw [sum_comp_inv f, hf]
  rw [h1]
  calc l2 (fun x => lOp (alpha g) (fun y => f y⁻¹) x⁻¹)
      = l2 (lOp (alpha g) (fun y => f y⁻¹)) := l2_inv _
    _ ≤ (theta c) ^ 2 * l2 (fun y => f y⁻¹) := alpha_contract g c hc hgap _ hmz
    _ = (theta c) ^ 2 * l2 f := by rw [l2_inv]

/-! ### Words of a fixed length -/

lemma card_wIdx (k : ℕ) : Fintype.card (wIdx k) = 48 ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin, card_alpha]

omit [Fintype G] in
lemma word_cons (g : Fin 12 → G) (k : ℕ) (a : Fin 12 × Bool × Bool) (u : wIdx k) :
    word g (k+1) (Fin.cons a u) = alpha g a * word g k u := by
  simp only [word, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.map_cons, List.prod_cons]

lemma consEquiv_apply' (k : ℕ) (p : (Fin 12 × Bool × Bool) × wIdx k) :
    Fin.consEquiv (fun _ : Fin (k+1) => Fin 12 × Bool × Bool) p = Fin.cons p.1 p.2 := by
  funext i
  rw [Fin.consEquiv_apply]

lemma lOp_word_zero (g : Fin 12 → G) (f : G → ℝ) : lOp (word g 0) f = f := by
  funext x
  have hcard : Fintype.card (wIdx 0) = 1 := by rw [card_wIdx]; norm_num
  have hword : ∀ w : wIdx 0, word g 0 w = 1 := by
    intro w
    simp only [word, List.ofFn_eq_map, List.finRange_zero, List.map_nil, List.prod_nil]
  have hsum : uOp (word g 0) f x = f x := by
    simp only [uOp]
    calc (∑ w : wIdx 0, f (word g 0 w * x)) = ∑ _w : wIdx 0, f x := by
          refine Finset.sum_congr rfl fun w _ => by rw [hword w, one_mul]
      _ = (Fintype.card (wIdx 0) : ℝ) * f x := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = f x := by rw [hcard]; norm_num
  rw [lOp_apply, hsum, hcard]; norm_num

lemma rOp_word_zero (g : Fin 12 → G) (f : G → ℝ) : rOp (word g 0) f = f := by
  funext x
  have hcard : Fintype.card (wIdx 0) = 1 := by rw [card_wIdx]; norm_num
  have hword : ∀ w : wIdx 0, word g 0 w = 1 := by
    intro w
    simp only [word, List.ofFn_eq_map, List.finRange_zero, List.map_nil, List.prod_nil]
  simp only [rOp]
  rw [Finset.sum_congr rfl (fun w _ => by rw [hword w, mul_one]),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  norm_num

lemma uOp_word_succ (g : Fin 12 → G) (k : ℕ) (f : G → ℝ) :
    uOp (word g (k+1)) f = uOp (word g k) (uOp (alpha g) f) := by
  funext x
  have h1 : (∑ w : wIdx (k+1), f (word g (k+1) w * x))
      = ∑ u : wIdx k, ∑ a : Fin 12 × Bool × Bool, f (word g (k+1) (Fin.cons a u) * x) := by
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => Fin 12 × Bool × Bool))
      (fun w => f (word g (k+1) w * x))]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [consEquiv_apply']
  simp only [uOp]
  rw [h1]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun a _ => by
    rw [word_cons, mul_assoc]

/-- Splitting a common denominator out of a sum of sums. -/
lemma sum_div_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (F : ι → κ → ℝ) (C : ℝ) :
    (∑ i, (∑ a, F i a) / C) = (∑ i, ∑ a, F i a) / C := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]

/-- Normalising a list inside `uOp`. -/
lemma uOp_lOp {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → G) (α : κ → G) (f : G → ℝ) :
    uOp v (lOp α f)
      = fun x => uOp v (uOp α f) x / (Fintype.card κ : ℝ) := by
  funext x
  simp only [uOp, lOp_apply]
  exact sum_div_sum (fun i a => f (α a * (v i * x))) _

lemma lOp_word_succ (g : Fin 12 → G) (k : ℕ) (f : G → ℝ) :
    lOp (word g (k+1)) f = lOp (word g k) (lOp (alpha g) f) := by
  funext x
  have hL : lOp (word g (k+1)) f x
      = uOp (word g k) (uOp (alpha g) f) x / ((Fintype.card (wIdx (k+1)) : ℕ) : ℝ) := by
    rw [lOp_apply, congrFun (uOp_word_succ g k f) x]
  have hR : lOp (word g k) (lOp (alpha g) f) x
      = uOp (word g k) (uOp (alpha g) f) x / ((Fintype.card (Fin 12 × Bool × Bool) : ℕ) : ℝ)
          / ((Fintype.card (wIdx k) : ℕ) : ℝ) := by
    rw [lOp_apply, congrFun (uOp_lOp (word g k) (alpha g) f) x]
  rw [hL, hR, card_wIdx, card_wIdx, card_alpha_cast, pow_succ]
  push_cast
  rw [div_div]
  ring

lemma rOp_word_succ_num (g : Fin 12 → G) (k : ℕ) (f : G → ℝ) (x : G) :
    (∑ w : wIdx (k+1), f (x * word g (k+1) w))
      = ∑ i : Fin 12 × Bool × Bool, ∑ a : wIdx k, f ((x * alpha g i) * word g k a) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k+1) => Fin 12 × Bool × Bool))
    (fun w => f (x * word g (k+1) w))]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by
    rw [consEquiv_apply', word_cons, ← mul_assoc]

lemma rOp_word_succ (g : Fin 12 → G) (k : ℕ) (f : G → ℝ) :
    rOp (word g (k+1)) f = rOp (alpha g) (rOp (word g k) f) := by
  funext x
  have hL : rOp (word g (k+1)) f x
      = (∑ i : Fin 12 × Bool × Bool, ∑ a : wIdx k, f ((x * alpha g i) * word g k a))
          / ((Fintype.card (wIdx (k+1)) : ℕ) : ℝ) := by
    simp only [rOp]
    rw [rOp_word_succ_num]
  have hR : rOp (alpha g) (rOp (word g k) f) x
      = (∑ i : Fin 12 × Bool × Bool, ∑ a : wIdx k, f ((x * alpha g i) * word g k a))
          / ((Fintype.card (wIdx k) : ℕ) : ℝ)
          / ((Fintype.card (Fin 12 × Bool × Bool) : ℕ) : ℝ) := by
    simp only [rOp]
    rw [sum_div_sum (fun i (a : wIdx k) => f ((x * alpha g i) * word g k a)) _]
  rw [hL, hR, card_wIdx, card_wIdx, card_alpha_cast, pow_succ]
  rw [Nat.cast_mul, Nat.cast_ofNat, div_div]

/-! ### Powers of the walk -/

lemma l2_lOp_word_le (g : Fin 12 → G) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ f : G → ℝ, (∑ x, f x = 0) →
      c * l2 f ≤ ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2) :
    ∀ (k : ℕ) (f : G → ℝ), (∑ x, f x = 0) →
      l2 (lOp (word g k) f) ≤ ((theta c) ^ 2) ^ k * l2 f := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rw [pow_zero, one_mul, lOp_word_zero g f]
  | succ k ih =>
    intro f hf
    rw [lOp_word_succ g k f]
    have hmz : ∑ x, lOp (alpha g) f x = 0 := lOp_mean_zero (alpha g) f hf
    calc l2 (lOp (word g k) (lOp (alpha g) f))
        ≤ ((theta c) ^ 2) ^ k * l2 (lOp (alpha g) f) := ih _ hmz
      _ ≤ ((theta c) ^ 2) ^ k * ((theta c) ^ 2 * l2 f) :=
          mul_le_mul_of_nonneg_left (alpha_contract g c hc hgap f hf) (by positivity)
      _ = ((theta c) ^ 2) ^ (k + 1) * l2 f := by rw [pow_succ]; ring

lemma l2_rOp_word_le (g : Fin 12 → G) (c : ℝ) (hc : 0 < c)
    (hgap : ∀ f : G → ℝ, (∑ x, f x = 0) →
      c * l2 f ≤ ∑ i : Fin 12, ∑ x, (f (g i * x) - f x) ^ 2) :
    ∀ (k : ℕ) (f : G → ℝ), (∑ x, f x = 0) →
      l2 (rOp (word g k) f) ≤ ((theta c) ^ 2) ^ k * l2 f := by
  intro k
  induction k with
  | zero =>
    intro f hf
    rw [pow_zero, one_mul, rOp_word_zero g f]
  | succ k ih =>
    intro f hf
    rw [rOp_word_succ g k f]
    have hmz : ∑ x, rOp (word g k) f x = 0 := rOp_mean_zero (word g k) f hf
    calc l2 (rOp (alpha g) (rOp (word g k) f))
        ≤ (theta c) ^ 2 * l2 (rOp (word g k) f) := rOp_alpha_contract g c hc hgap _ hmz
      _ ≤ (theta c) ^ 2 * (((theta c) ^ 2) ^ k * l2 f) :=
          mul_le_mul_of_nonneg_left (ih f hf) (by positivity)
      _ = ((theta c) ^ 2) ^ (k + 1) * l2 f := by rw [pow_succ]; ring

/-! ### Transport back to a `Fin Δ`-indexed list -/

lemma leftExpander_of_lOp {ι : Type*} [Fintype ι] (B : ι → G) (μ : ℝ)
    (h : ∀ f : G → ℝ, (∑ x, f x = 0) → l2 (lOp B f) ≤ μ ^ 2 * l2 f) :
    leftExpander (fun i : Fin (Fintype.card ι) => B ((Fintype.equivFin ι).symm i)) μ := by
  intro x hx
  have hsum : ∀ g : G, (∑ i : Fin (Fintype.card ι), x (B ((Fintype.equivFin ι).symm i) * g))
      = uOp B x g := by
    intro g
    rw [← Equiv.sum_comp (Fintype.equivFin ι)
      (fun i => x (B ((Fintype.equivFin ι).symm i) * g))]
    simp only [Equiv.symm_apply_apply, uOp]
  calc ∑ g, ((∑ i : Fin (Fintype.card ι),
            x (B ((Fintype.equivFin ι).symm i) * g)) / (Fintype.card ι : ℝ)) ^ 2
      = ∑ g, lOp B x g ^ 2 := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hsum g, lOp_apply]
    _ ≤ μ ^ 2 * ∑ g, x g ^ 2 := by simpa only [l2] using h x hx

lemma rightExpander_of_rOp {ι : Type*} [Fintype ι] (B : ι → G) (μ : ℝ)
    (h : ∀ f : G → ℝ, (∑ x, f x = 0) → l2 (rOp B f) ≤ μ ^ 2 * l2 f) :
    rightExpander (fun i : Fin (Fintype.card ι) => B ((Fintype.equivFin ι).symm i)) μ := by
  intro x hx
  have hsum : ∀ g : G, (∑ i : Fin (Fintype.card ι), x (g * B ((Fintype.equivFin ι).symm i)))
      = ∑ a : ι, x (g * B a) := by
    intro g
    rw [← Equiv.sum_comp (Fintype.equivFin ι)
      (fun i => x (g * B ((Fintype.equivFin ι).symm i)))]
    simp only [Equiv.symm_apply_apply]
  calc ∑ g, ((∑ i : Fin (Fintype.card ι),
            x (g * B ((Fintype.equivFin ι).symm i))) / (Fintype.card ι : ℝ)) ^ 2
      = ∑ g, rOp B x g ^ 2 := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hsum g]
        simp only [rOp]
    _ ≤ μ ^ 2 * ∑ g, x g ^ 2 := by simpa only [l2] using h x hx

/-- The bijection `Fin 12 ≃ Fin 6 × Bool` used to read the `12` generators as `sl3Gen`. -/
noncomputable def e12 : Fin 12 ≃ Fin 6 × Bool :=
  (finCongr (by norm_num : 6 * 2 = 12)).symm.trans
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl (Fin 6)) finTwoEquiv))

end Work.LT.RF

namespace Work.LT

open RF

/-- **Expanders for the complex.** For every `μ > 0` and `D0` there is a degree `Δ ≥ D0` and,
for every `m`, a finite group of order `≥ m` with a length-`Δ` list `A` whose left and right
walks both contract mean-zero functions by `μ` (lazy `SL₃(ℤ/p)` generators, all words of a
fixed length, padded by repetition). -/
theorem lr_expander_family (μ : ℝ) (hμ : 0 < μ) (D0 : ℕ) :
    ∃ Δ : ℕ, 0 < Δ ∧ D0 ≤ Δ ∧ ∀ m : ℕ,
      ∃ (G : Type) (_ : Group G) (_ : Fintype G), m ≤ Fintype.card G ∧
        ∃ A : Fin Δ → G, leftExpander A μ ∧ rightExpander A μ := by
  obtain ⟨c, hc, hgap⟩ := sl3_gap
  have hθ0 : 0 ≤ theta c := theta_nonneg c
  have hθ1 : theta c < 1 := theta_lt_one hc
  obtain ⟨k1, hk1⟩ : ∃ k : ℕ, (theta c) ^ k ≤ μ := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hμ hθ1
    exact ⟨k, le_of_lt hk⟩
  obtain ⟨k2, hk2⟩ : ∃ k : ℕ, D0 ≤ 48 ^ k :=
    ⟨D0, le_trans (le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by norm_num) D0)⟩
  obtain ⟨k, hkμ, hkD⟩ : ∃ k : ℕ, (theta c) ^ k ≤ μ ∧ D0 ≤ 48 ^ k :=
    ⟨max k1 k2,
      le_trans (pow_le_pow_of_le_one hθ0 (le_of_lt hθ1) (le_max_left _ _)) hk1,
      le_trans hk2 (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))⟩
  refine ⟨Fintype.card (wIdx k), ?_, ?_, fun m => ?_⟩
  · rw [card_wIdx]; positivity
  · rw [card_wIdx]; exact hkD
  · obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (max m 3)
    haveI : Fact p.Prime := ⟨hpprime⟩
    have h3 : 3 ≤ p := le_trans (le_max_right m 3) hpge
    have hp2 : p ≠ 2 := by omega
    have hpm : m ≤ p := le_trans (le_max_left m 3) hpge
    refine ⟨Matrix.SpecialLinearGroup (Fin 3) (ZMod p), inferInstance, inferInstance, ?_⟩
    refine ⟨le_trans hpm (sl3_card_le p), ?_⟩
    set gg : Fin 12 → Matrix.SpecialLinearGroup (Fin 3) (ZMod p) :=
      fun i => sl3Gen p (e12 i) with hgg
    have hgapg : ∀ f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℝ, (∑ x, f x = 0) →
        c * l2 f ≤ ∑ i : Fin 12, ∑ x, (f (gg i * x) - f x) ^ 2 := by
      intro f hf
      have h := hgap p hp2 f hf
      have he : (∑ i : Fin 12, ∑ x, (f (gg i * x) - f x) ^ 2)
          = ∑ q : Fin 6 × Bool, ∑ x, (f (sl3Gen p q * x) - f x) ^ 2 :=
        Fintype.sum_equiv e12 _ _ fun i => by simp [hgg]
      rw [he]
      exact h
    have hpow : ((theta c) ^ 2) ^ k ≤ μ ^ 2 := by
      rw [← pow_mul, mul_comm 2 k, pow_mul]
      exact pow_le_pow_left₀ (pow_nonneg hθ0 k) hkμ 2
    refine ⟨fun i : Fin (Fintype.card (wIdx k)) => word gg k ((Fintype.equivFin (wIdx k)).symm i),
      ?_, ?_⟩
    · refine leftExpander_of_lOp (word gg k) μ ?_
      intro f hf
      exact le_trans (l2_lOp_word_le gg c hc hgapg k f hf)
        (mul_le_mul_of_nonneg_right hpow (l2_nonneg f))
    · refine rightExpander_of_rOp (word gg k) μ ?_
      intro f hf
      exact le_trans (l2_rOp_word_le gg c hc hgapg k f hf)
        (mul_le_mul_of_nonneg_right hpow (l2_nonneg f))

end Work.LT
