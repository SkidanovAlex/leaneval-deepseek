/-
Auxiliary lemmas for the Gowers--Cauchy--Schwarz inequality of the Gowers box norm
(`Submission/Work/Peluse/BoxNorm/prodCubeSum_norm_le.lean`), on top of the definitions in
`Submission/Work/Peluse/BoxNorm/WinDefs.lean` and the first-coordinate recursion
`winForm_succ`.

Contains: the low-dimensional evaluation `winForm_one` of the box form, the non-negativity of the
box form of a single function (`winForm_const_nonneg`), the recursion
`winForm_const_norm_succ` for the modulus of the box form of a single function, the elementary
sum reorderings used by the Cauchy--Schwarz step, and the identity `winForm_shift_prod` expressing
a box form with slots `u_ω (· + a) · conj (u_ω (· + a'))` as a sum of `ω`-products.
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.winForm_succ

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace Work.Peluse.BoxNorm

noncomputable section

open Work.Peluse

lemma winForm_congr {t : ℕ} {Q : Fin t → Finset ℤ} {W : Finset ℤ}
    {φ ψ : (Fin t → Bool) → ℤ → ℂ} (h : ∀ ω y, φ ω y = ψ ω y) :
    winForm t Q W φ = winForm t Q W ψ := by
  simp only [winForm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
    Finset.sum_congr rfl fun x _ => Finset.prod_congr rfl fun ω _ => ?_
  rw [h]

lemma finOne_false (ω : Fin 0 → Bool) : (Fin.cases false ω : Fin 1 → Bool) = fun _ => false := by
  funext i; fin_cases i; simp [Fin.cases_zero]

lemma finOne_true (ω : Fin 0 → Bool) : (Fin.cases true ω : Fin 1 → Bool) = fun _ => true := by
  funext i; fin_cases i; simp [Fin.cases_zero]

lemma winForm_zero (Q : Fin 0 → Finset ℤ) (W : Finset ℤ) (ψ : (Fin 0 → Bool) → ℤ → ℂ) :
    winForm 0 Q W ψ = ∑ x ∈ W, ψ (fun i => Fin.elim0 i) x := by
  simp only [winForm, Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [weight_eq_sum, Fin.sum_univ_zero, Tuple.total, Function.iterate_zero_apply,
    add_zero]
  exact congrArg (fun ω : Fin 0 → Bool => ψ ω x) (Subsingleton.elim _ _)

lemma pairSum_star {ι : Type*} [Fintype ι] (Φ : ι → ℂ) :
    ∑ a : ι, ∑ b : ι, Φ a * star (Φ b) = ((‖∑ a : ι, Φ a‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Finset.sum_mul_sum]
  simp only [Complex.star_def]
  rw [← map_sum (starRingEnd ℂ), Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma sum_three_comm {A : Type*} [Fintype A] (W : Finset ℤ) (F : A → A → ℤ → ℂ) :
    (∑ a : A, ∑ a' : A, ∑ x ∈ W, F a a' x)
      = ∑ x ∈ W, ∑ a : A, ∑ a' : A, F a a' x := by
  have h1 : (∑ a : A, ∑ a' : A, ∑ x ∈ W, F a a' x)
      = ∑ a' : A, ∑ a : A, ∑ x ∈ W, F a a' x :=
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a a' => ∑ x ∈ W, F a a' x)
  have h2 : ∀ a' : A, (∑ a : A, ∑ x ∈ W, F a a' x) = ∑ x ∈ W, ∑ a : A, F a a' x :=
    fun a' => Finset.sum_comm (s := Finset.univ) (t := W) (f := fun a x => F a a' x)
  have h3 : (∑ a' : A, ∑ a : A, ∑ x ∈ W, F a a' x)
      = ∑ a' : A, ∑ x ∈ W, ∑ a : A, F a a' x :=
    Finset.sum_congr rfl (fun a' _ => h2 a')
  have h4 : (∑ a' : A, ∑ x ∈ W, ∑ a : A, F a a' x)
      = ∑ x ∈ W, ∑ a' : A, ∑ a : A, F a a' x :=
    Finset.sum_comm (s := Finset.univ) (t := W) (f := fun a' x => ∑ a : A, F a a' x)
  have h5 : (∑ x ∈ W, ∑ a' : A, ∑ a : A, F a a' x)
      = ∑ x ∈ W, ∑ a : A, ∑ a' : A, F a a' x :=
    Finset.sum_congr rfl (fun x _ => Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a' a => F a a' x))
  rw [h1, h3, h4, h5]

lemma sum_sum_mul_star {A : Type*} [Fintype A] (W : Finset ℤ) (u v : A → ℤ → ℂ) :
    (∑ a : A, ∑ a' : A, ∑ x ∈ W, u a' x * star (v a x))
      = ∑ x ∈ W, (∑ a : A, u a x) * star (∑ a : A, v a x) := by
  rw [sum_three_comm W (fun a a' x => u a' x * star (v a x))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (∑ a : A, ∑ a' : A, u a' x * star (v a x))
      = ∑ a' : A, ∑ a : A, u a' x * star (v a x) :=
    Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a a' => u a' x * star (v a x))
  have h2 : (∑ a : A, u a x) * star (∑ a : A, v a x)
      = ∑ a : A, ∑ a' : A, u a x * star (v a' x) := by
    rw [star_sum, Finset.sum_mul_sum]
  rw [h1, h2]

lemma winForm_one (Q : Fin 1 → Finset ℤ) (W : Finset ℤ) (φ : (Fin 1 → Bool) → ℤ → ℂ) :
    winForm 1 Q W φ
      = ∑ x ∈ W, (∑ a' : {x : ℤ // x ∈ Q 0}, φ (fun _ => false) (x + a'.1)) *
          star (∑ a : {x : ℤ // x ∈ Q 0}, φ (fun _ => true) (x + a.1)) := by
  have h3 := winForm_succ 0 Q W φ
  rw [h3]
  refine Eq.trans ?_ (sum_sum_mul_star W
    (fun (a : {x : ℤ // x ∈ Q 0}) x => φ (fun _ => false) (x + a.1))
    (fun (a : {x : ℤ // x ∈ Q 0}) x => φ (fun _ => true) (x + a.1)))
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [winForm_zero]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [finOne_false, finOne_true]

lemma norm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  have h2 : ‖(((r : ℝ)) : ℂ)‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (((r : ℝ)) : ℂ)]

lemma sum_eq_ofReal_norm' {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (h : ∀ i ∈ s, z i = ((‖z i‖ : ℝ) : ℂ)) :
    (∑ i ∈ s, z i) = ((∑ i ∈ s, ‖z i‖ : ℝ) : ℂ) := by
  rw [Finset.sum_congr rfl h, Complex.ofReal_sum]

lemma norm_sum_of_norm {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (h : ∀ i ∈ s, z i = ((‖z i‖ : ℝ) : ℂ)) :
    ‖∑ i ∈ s, z i‖ = ∑ i ∈ s, ‖z i‖ := by
  rw [sum_eq_ofReal_norm' s z h]
  exact norm_ofReal_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)

lemma winForm_const_one (Q : Fin 1 → Finset ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    winForm 1 Q W (fun _ => g)
      = ((∑ x ∈ W, ‖∑ a : {x : ℤ // x ∈ Q 0}, g (x + a.1)‖ ^ 2 : ℝ) : ℂ) := by
  rw [winForm_one, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [star_sum, Finset.sum_mul_sum]
  exact pairSum_star (fun a : {x_1 : ℤ // x_1 ∈ Q 0} => g (x + a.1))

lemma winForm_const_one_norm (Q : Fin 1 → Finset ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    ‖winForm 1 Q W (fun _ => g)‖ = ∑ x ∈ W, ‖∑ a : {x : ℤ // x ∈ Q 0}, g (x + a.1)‖ ^ 2 := by
  have h1 : winForm 1 Q W (fun _ => g)
      = ((∑ x ∈ W, ‖∑ a : {x : ℤ // x ∈ Q 0}, g (x + a.1)‖ ^ 2 : ℝ) : ℂ) :=
    winForm_const_one Q W g
  rw [h1]
  exact norm_ofReal_of_nonneg (Finset.sum_nonneg fun x _ => sq_nonneg _)

lemma winForm_const_succ {n : ℕ} (Q : Fin (n+1) → Finset ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    winForm (n+1) Q W (fun _ => g)
      = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          winForm n (fun i : Fin n => Q i.succ) W
            (fun _ y => g (y + a'.1) * star (g (y + a.1))) := by
  have h := winForm_succ n Q W (fun _ : Fin (n+1) → Bool => g)
  rw [h]

lemma winForm_const_nonneg : ∀ (n : ℕ) (_ : 1 ≤ n) (Q : Fin n → Finset ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ), ∃ r : ℝ, 0 ≤ r ∧ winForm n Q W (fun _ => g) = ((r : ℝ) : ℂ) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ m ih =>
    intro hm Q W g
    cases m with
    | zero =>
      exact ⟨_, Finset.sum_nonneg (fun x _ => sq_nonneg _), winForm_const_one Q W g⟩
    | succ k =>
      have hstep : ∀ a a' : {x : ℤ // x ∈ Q 0},
          winForm (k+1) (fun i : Fin (k+1) => Q i.succ) W
            (fun _ y => g (y + a'.1) * star (g (y + a.1)))
          = ((‖winForm (k+1) (fun i : Fin (k+1) => Q i.succ) W
                (fun _ y => g (y + a'.1) * star (g (y + a.1)))‖ : ℝ) : ℂ) := by
        intro a a'
        obtain ⟨r, hr, hz⟩ := ih (by omega) (fun i : Fin (k+1) => Q i.succ) W
          (fun y => g (y + a'.1) * star (g (y + a.1)))
        rw [hz, norm_ofReal_of_nonneg hr]
      refine ⟨∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
        ‖winForm (k+1) (fun i : Fin (k+1) => Q i.succ) W
            (fun _ y => g (y + a'.1) * star (g (y + a.1)))‖, ?_, ?_⟩
      · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun a' _ => norm_nonneg _
      · rw [winForm_const_succ, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun a' _ => hstep a a'

lemma winForm_const_eq_norm {n : ℕ} (hn : 1 ≤ n) (Q : Fin n → Finset ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ) :
    winForm n Q W (fun _ => g) = ((‖winForm n Q W (fun _ => g)‖ : ℝ) : ℂ) := by
  obtain ⟨r, hr, hz⟩ := winForm_const_nonneg n hn Q W g
  rw [hz, norm_ofReal_of_nonneg hr]

lemma winForm_const_norm_succ {n : ℕ} (hn : 1 ≤ n) (Q : Fin (n+1) → Finset ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ) :
    ‖winForm (n+1) Q W (fun _ => g)‖
      = ∑ a : {x : ℤ // x ∈ Q 0}, ∑ a' : {x : ℤ // x ∈ Q 0},
          ‖winForm n (fun i : Fin n => Q i.succ) W
            (fun _ y => g (y + a'.1) * star (g (y + a.1)))‖ := by
  have hnn : ∀ a a' : {x : ℤ // x ∈ Q 0},
      winForm n (fun i : Fin n => Q i.succ) W
          (fun _ y => g (y + a'.1) * star (g (y + a.1)))
        = ((‖winForm n (fun i : Fin n => Q i.succ) W
              (fun _ y => g (y + a'.1) * star (g (y + a.1)))‖ : ℝ) : ℂ) :=
    fun a a' => winForm_const_eq_norm hn _ W _
  rw [winForm_const_succ]
  rw [norm_sum_of_norm Finset.univ
    (fun a : {x : ℤ // x ∈ Q 0} => ∑ a' : {x : ℤ // x ∈ Q 0},
      winForm n (fun i : Fin n => Q i.succ) W (fun _ y => g (y + a'.1) * star (g (y + a.1))))
    (fun a _ => by
      rw [norm_sum_of_norm Finset.univ
        (fun a' : {x : ℤ // x ∈ Q 0} => winForm n (fun i : Fin n => Q i.succ) W
          (fun _ y => g (y + a'.1) * star (g (y + a.1)))) (fun a' _ => hnn a a')]
      exact sum_eq_ofReal_norm' Finset.univ _ (fun a' _ => hnn a a'))]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact norm_sum_of_norm Finset.univ _ (fun a' _ => hnn a a')

lemma prod_star_split {n : ℕ} (u v : (Fin n → Bool) → ℂ) :
    (∏ ω : Fin n → Bool, (star^[weight ω]) (u ω * star (v ω)))
      = (∏ ω : Fin n → Bool, (star^[weight ω]) (u ω))
        * star (∏ ω : Fin n → Bool, (star^[weight ω]) (v ω)) := by
  rw [star_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ω _ => by
    rw [star_iterate_mul, star_iterate_conj]

lemma winNorm_pow (n : ℕ) (Q : Fin n → Finset ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    winNorm n Q W g ^ (2 ^ n) = ‖winForm n Q W (fun _ => g)‖ := by
  rw [winNorm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  have h : (1 / (2 : ℝ) ^ n) * ((2 ^ n : ℕ) : ℝ) = 1 := by
    push_cast; field_simp
  rw [h, Real.rpow_one]

/-- The `ω`-product of a family of the form `u_ω · conj v_ω` splits into the product of the
`u_ω` and the conjugate of the product of the `v_ω`. -/
lemma cube_prod_mul_star {n : ℕ} (u v : (Fin n → Bool) → ℂ) :
    (∏ ω : Fin n → Bool, (star^[weight ω]) (u ω * star (v ω)))
      = (∏ ω, (star^[weight ω]) (u ω)) * star (∏ ω, (star^[weight ω]) (v ω)) :=
  prod_star_split u v

/-- The box form of a shifted slot `u_ω (· + a) · conj (u_ω (· + a'))` is the sum of the product
of the two "half products". -/
lemma winForm_shift_prod {n : ℕ} (Q : Fin n → Finset ℤ) (W : Finset ℤ)
    (u : (Fin n → Bool) → ℤ → ℂ) (a a' : ℤ) :
    winForm n Q W (fun ω y => u ω (y + a) * star (u ω (y + a')))
      = ∑ z : Tuple n Q, ∑ z' : Tuple n Q, ∑ x ∈ W,
          (∏ ω : Fin n → Bool,
              (star^[weight ω]) (u ω (x + Tuple.total (Tuple.corner z z' ω) + a)))
            * star (∏ ω : Fin n → Bool,
                (star^[weight ω]) (u ω (x + Tuple.total (Tuple.corner z z' ω) + a'))) := by
  simp only [winForm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ =>
    Finset.sum_congr rfl fun x _ => ?_
  exact cube_prod_mul_star (fun ω => u ω (x + Tuple.total (Tuple.corner z z' ω) + a))
    (fun ω => u ω (x + Tuple.total (Tuple.corner z z' ω) + a'))

end

end Work.Peluse.BoxNorm
