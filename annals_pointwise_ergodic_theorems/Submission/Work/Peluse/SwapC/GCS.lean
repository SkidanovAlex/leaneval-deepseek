/-
The index-set-agnostic Gowers--Cauchy--Schwarz inequality for the general box form.

`cWinForm n X ν W φ` is the box form of order `n` over the *single* index type `X`, with the
per-coordinate direction maps `ν k : X → ℤ` and the window `W`:

  `∑_{z,z' : Fin n → X} ∑_{x ∈ W} ∏_{ω : Fin n → Bool} C^{|ω|} φ_ω (x + cornerShift (ν ∘ z) (ν ∘ z') ω)`.

It is `Work.Peluse.SwapC.gWinForm n (fun _ => X) ν W φ`, and the Gowers--Cauchy--Schwarz
inequality `cWinForm_norm_le` is the mirror of
`Submission/Work/Peluse/BoxNorm/prodCubeSum_norm_le.lean` with the coordinate sets
`{x : ℤ // x ∈ Q i}` replaced by the single type `X` and the shifts `(z i).1` by `ν i (z i)`; the
proof (Cauchy--Schwarz at `d = 1`, splitting the first coordinate, Cauchy--Schwarz, induction and
generalised Hölder) is index-set agnostic, so it carries over verbatim.

The passage from `cWinForm` to the genuinely general `gWinForm` (with a dependent coordinate
family) is `cWinForm_eq_gWinForm`, which is `gWinForm_eq_cornerShift` of `GTransfer`.

## Main results

* `Work.Peluse.SwapC.cWinForm_norm_le`
-/
import Mathlib
import Submission.Work.Peluse.SwapC.GTransfer
import Submission.Work.Peluse.SwapC.gWinForm_succ
import Submission.Work.Peluse.SwapC.gWinForm_one
import Submission.Work.Peluse.SwapC.gWinForm_const_one
import Submission.Work.Peluse.SwapC.gWinForm_const_one_norm
import Submission.Work.Peluse.SwapC.gWinForm_shift_prod_two

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.BoxNorm

/-! ## The box form over a single index type -/

/-- The box form of order `n` over the index type `X` with direction maps `ν` and window `W`. -/
def cWinForm (n : ℕ) (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
    (φ : (Fin n → Bool) → ℤ → ℂ) : ℂ :=
  ∑ z : Fin n → X, ∑ z' : Fin n → X, ∑ x ∈ W,
    ∏ ω : Fin n → Bool,
      (star^[weight ω]) (φ ω (x + cornerShift (fun k => ν k (z k)) (fun k => ν k (z' k)) ω))

/-- The `2^n`-th root of the box form of a single function. -/
def cWinNorm (n : ℕ) (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ) : ℝ :=
  ‖cWinForm n X ν W (fun _ => g)‖ ^ (1 / (2 : ℝ) ^ n)

lemma cWinNorm_nonneg {n : ℕ} {X : Type} [Fintype X] {ν : Fin n → X → ℤ} {W : Finset ℤ}
    {g : ℤ → ℂ} : 0 ≤ cWinNorm n X ν W g := Real.rpow_nonneg (norm_nonneg _) _

/-- The "half product" of the box form. -/
def cHalf (n : ℕ) (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (u : (Fin n → Bool) → ℤ → ℂ)
    (z z' : Fin n → X) (x a : ℤ) : ℂ :=
  ∏ ω : Fin n → Bool,
    (star^[weight ω]) (u ω (x + cornerShift (fun k => ν k (z k)) (fun k => ν k (z' k)) ω + a))

lemma cWinForm_eq_gWinForm (n : ℕ) (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
    (φ : (Fin n → Bool) → ℤ → ℂ) :
    cWinForm n X ν W φ = gWinForm n (fun _ : Fin n => X) ν W φ := by
  rw [gWinForm_eq_cornerShift]
  rfl

lemma cHalf_eq_gHalf (n : ℕ) (X : Type) [Fintype X] (ν : Fin n → X → ℤ)
    (u : (Fin n → Bool) → ℤ → ℂ) (z z' : Fin n → X) (x a : ℤ) :
    cHalf n X ν u z z' x a = gHalf n (fun _ : Fin n => X) ν u z z' x a := by
  refine Finset.prod_congr rfl (fun ω _ => ?_)
  rw [gtotal_gcorner]

/-! ## The base cases -/

lemma cWinForm_one (X : Type) [Fintype X] (ν : Fin 1 → X → ℤ) (W : Finset ℤ)
    (φ : (Fin 1 → Bool) → ℤ → ℂ) :
    cWinForm 1 X ν W φ
      = ∑ x ∈ W, (∑ a' : X, φ (fun _ => false) (x + ν 0 a'))
          * star (∑ a : X, φ (fun _ => true) (x + ν 0 a)) := by
  rw [cWinForm_eq_gWinForm]
  exact gWinForm_one (fun _ : Fin 1 => X) ν W φ

lemma cWinForm_const_one (X : Type) [Fintype X] (ν : Fin 1 → X → ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ) :
    cWinForm 1 X ν W (fun _ => g)
      = ((∑ x ∈ W, ‖∑ a : X, g (x + ν 0 a)‖ ^ 2 : ℝ) : ℂ) := by
  rw [cWinForm_eq_gWinForm]
  exact gWinForm_const_one (fun _ : Fin 1 => X) ν W g

lemma cWinForm_const_one_norm (X : Type) [Fintype X] (ν : Fin 1 → X → ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ) :
    ‖cWinForm 1 X ν W (fun _ => g)‖ = ∑ x ∈ W, ‖∑ a : X, g (x + ν 0 a)‖ ^ 2 := by
  rw [cWinForm_eq_gWinForm]
  exact gWinForm_const_one_norm (fun _ : Fin 1 => X) ν W g

lemma cWinNorm_one_sq (X : Type) [Fintype X] (ν : Fin 1 → X → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    cWinNorm 1 X ν W g ^ 2 = ‖cWinForm 1 X ν W (fun _ => g)‖ := by
  have h : (1 / (2 : ℝ) ^ 1) * ((2 : ℕ) : ℝ) = 1 := by norm_num
  rw [cWinNorm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), h, Real.rpow_one]

/-! ## The recursion and the Cauchy--Schwarz block -/

lemma cWinForm_succ {n : ℕ} (X : Type) [Fintype X] (ν : Fin (n+1) → X → ℤ) (W : Finset ℤ)
    (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    cWinForm (n+1) X ν W φ
      = ∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => φ (Fin.cons false ω) (y + ν 0 a')
              * star (φ (Fin.cons true ω) (y + ν 0 a))) := by
  rw [cWinForm_eq_gWinForm]
  rw [gWinForm_succ (n := n) (fun _ : Fin (n+1) => X) ν W φ]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => ?_))
  rw [← cWinForm_eq_gWinForm]

lemma cWinForm_shift_prod_two {n : ℕ} (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
    (u v : (Fin n → Bool) → ℤ → ℂ) (a a' : ℤ) :
    cWinForm n X ν W (fun ω y => u ω (y + a) * star (v ω (y + a')))
      = ∑ z : Fin n → X, ∑ z' : Fin n → X, ∑ x ∈ W,
          cHalf n X ν u z z' x a * star (cHalf n X ν v z z' x a') := by
  rw [cWinForm_eq_gWinForm]
  rw [gWinForm_shift_prod_two (fun _ : Fin n => X) ν W u v a a']
  refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun z' _ =>
    Finset.sum_congr rfl (fun x _ => ?_)))
  rw [cHalf_eq_gHalf, cHalf_eq_gHalf]

/-- The `A × A`-sum of the box form of a shifted product family is the sum of the squared moduli of
the summed half-products. -/
theorem cWinForm_shift_sum_star {n : ℕ} (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
    (u : (Fin n → Bool) → ℤ → ℂ) {A : Type*} [Fintype A] (γ : A → ℤ) :
    (∑ a : A, ∑ a' : A, cWinForm n X ν W (fun ω y => u ω (y + γ a) * star (u ω (y + γ a'))))
      = ∑ p : (Fin n → X) × (Fin n → X), ∑ x ∈ W,
          ((‖∑ a : A, cHalf n X ν u p.1 p.2 x (γ a)‖ ^ 2 : ℝ) : ℂ) := by
  have hL : (∑ a : A, ∑ a' : A,
        cWinForm n X ν W (fun ω y => u ω (y + γ a) * star (u ω (y + γ a'))))
      = ∑ a : A, ∑ a' : A, ∑ z : Fin n → X, ∑ z' : Fin n → X, ∑ x ∈ W,
          cHalf n X ν u z z' x (γ a) * star (cHalf n X ν u z z' x (γ a')) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [cWinForm_shift_prod_two X ν W u u (γ a) (γ a')]
  rw [hL]
  have hstep : (∑ a : A, ∑ a' : A, ∑ z : Fin n → X, ∑ z' : Fin n → X, ∑ x ∈ W,
        cHalf n X ν u z z' x (γ a) * star (cHalf n X ν u z z' x (γ a')))
      = ∑ a : A, ∑ a' : A, ∑ p : (Fin n → X) × (Fin n → X), ∑ x ∈ W,
        cHalf n X ν u p.1 p.2 x (γ a) * star (cHalf n X ν u p.1 p.2 x (γ a')) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    exact (Fintype.sum_prod_type' (fun (z z' : Fin n → X) => ∑ x ∈ W,
      cHalf n X ν u z z' x (γ a) * star (cHalf n X ν u z z' x (γ a')))).symm
  rw [hstep]
  rw [sum_reorder_prod W (fun (a : A) (a' : A) (p : (Fin n → X) × (Fin n → X)) (x : ℤ) =>
        cHalf n X ν u p.1 p.2 x (γ a) * star (cHalf n X ν u p.1 p.2 x (γ a')))]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => ?_
  exact pairSum_star (fun a : A => cHalf n X ν u p.1 p.2 x (γ a))

theorem cWinForm_succ_prod_sum {n : ℕ} (X : Type) [Fintype X] (ν : Fin (n+1) → X → ℤ)
    (W : Finset ℤ) (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    cWinForm (n+1) X ν W φ
      = ∑ p : (Fin n → X) × (Fin n → X), ∑ x ∈ W,
          (∑ a' : X, cHalf n X (fun i : Fin n => ν i.succ)
              (fun ω y => φ (Fin.cons false ω) y) p.1 p.2 x (ν 0 a'))
            * star (∑ a : X, cHalf n X (fun i : Fin n => ν i.succ)
                (fun ω y => φ (Fin.cons true ω) y) p.1 p.2 x (ν 0 a)) := by
  have hstep : (∑ a : X, ∑ a' : X,
        cWinForm n X (fun i : Fin n => ν i.succ) W
          (fun ω y => φ (Fin.cons false ω) (y + ν 0 a')
            * star (φ (Fin.cons true ω) (y + ν 0 a))))
      = ∑ a : X, ∑ a' : X, ∑ p : (Fin n → X) × (Fin n → X), ∑ x ∈ W,
          cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons false ω) y)
              p.1 p.2 x (ν 0 a')
            * star (cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons true ω) y)
                p.1 p.2 x (ν 0 a)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    exact (cWinForm_shift_prod_two X (fun i : Fin n => ν i.succ) W
        (fun ω y => φ (Fin.cons false ω) y) (fun ω y => φ (Fin.cons true ω) y)
        (ν 0 a') (ν 0 a)).trans
      (Fintype.sum_prod_type' (fun (z z' : Fin n → X) => ∑ x ∈ W,
        cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons false ω) y)
            z z' x (ν 0 a')
          * star (cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons true ω) y)
              z z' x (ν 0 a)))).symm
  rw [cWinForm_succ, hstep]
  exact sum_factor_star W
    (fun (a' : X) (p : (Fin n → X) × (Fin n → X)) (x : ℤ) =>
      cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons false ω) y)
        p.1 p.2 x (ν 0 a'))
    (fun (a : X) (p : (Fin n → X) × (Fin n → X)) (x : ℤ) =>
      cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons true ω) y)
        p.1 p.2 x (ν 0 a))

/-- The Cauchy--Schwarz step of the induction. -/
theorem cWinForm_succ_cs {n : ℕ} (X : Type) [Fintype X] (ν : Fin (n+1) → X → ℤ) (W : Finset ℤ)
    (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    ‖cWinForm (n+1) X ν W φ‖ ^ 2
      ≤ ‖(∑ a : X, ∑ a' : X,
            cWinForm n X (fun i : Fin n => ν i.succ) W
              (fun ω y => φ (Fin.cons false ω) (y + ν 0 a)
                * star (φ (Fin.cons false ω) (y + ν 0 a'))))‖
        * ‖(∑ a : X, ∑ a' : X,
            cWinForm n X (fun i : Fin n => ν i.succ) W
              (fun ω y => φ (Fin.cons true ω) (y + ν 0 a)
                * star (φ (Fin.cons true ω) (y + ν 0 a'))))‖ := by
  classical
  let S : Finset (((Fin n → X) × (Fin n → X)) × ℤ) :=
    (Finset.univ : Finset ((Fin n → X) × (Fin n → X))) ×ˢ W
  let U : (((Fin n → X) × (Fin n → X)) × ℤ) → ℂ := fun i => ∑ a' : X,
    cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons false ω) y)
      i.1.1 i.1.2 i.2 (ν 0 a')
  let V : (((Fin n → X) × (Fin n → X)) × ℤ) → ℂ := fun i => ∑ a : X,
    cHalf n X (fun i : Fin n => ν i.succ) (fun ω y => φ (Fin.cons true ω) y)
      i.1.1 i.1.2 i.2 (ν 0 a)
  have hL : cWinForm (n+1) X ν W φ = ∑ i ∈ S, U i * star (V i) := by
    rw [cWinForm_succ_prod_sum]
    exact (Finset.sum_product (Finset.univ : Finset ((Fin n → X) × (Fin n → X))) W
      (fun i => U i * star (V i))).symm
  have hfalse : ‖(∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => φ (Fin.cons false ω) (y + ν 0 a)
              * star (φ (Fin.cons false ω) (y + ν 0 a'))))‖
      = ∑ i ∈ S, ‖U i‖ ^ 2 := by
    have h1 : (∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => φ (Fin.cons false ω) (y + ν 0 a)
              * star (φ (Fin.cons false ω) (y + ν 0 a'))))
        = (∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => (fun ω y => φ (Fin.cons false ω) y) ω (y + ν 0 a)
              * star ((fun ω y => φ (Fin.cons false ω) y) ω (y + ν 0 a')))) := rfl
    rw [h1, cWinForm_shift_sum_star X (fun i : Fin n => ν i.succ) W
      (fun ω y => φ (Fin.cons false ω) y) (fun a : X => ν 0 a)]
    have hsplit : (∑ p : (Fin n → X) × (Fin n → X), ∑ x ∈ W,
          ((‖∑ a : X, cHalf n X (fun i : Fin n => ν i.succ)
            (fun ω y => φ (Fin.cons false ω) y) p.1 p.2 x (ν 0 a)‖ ^ 2 : ℝ) : ℂ))
        = ∑ i ∈ S, ((‖U i‖ ^ 2 : ℝ) : ℂ) :=
      (Finset.sum_product (Finset.univ : Finset ((Fin n → X) × (Fin n → X))) W
        (fun i => ((‖U i‖ ^ 2 : ℝ) : ℂ))).symm
    rw [hsplit]
    exact norm_ofReal_sum_eq S (fun i => ‖U i‖ ^ 2) (fun i _ => sq_nonneg _)
  have htrue : ‖(∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => φ (Fin.cons true ω) (y + ν 0 a)
              * star (φ (Fin.cons true ω) (y + ν 0 a'))))‖
      = ∑ i ∈ S, ‖V i‖ ^ 2 := by
    have h1 : (∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => φ (Fin.cons true ω) (y + ν 0 a)
              * star (φ (Fin.cons true ω) (y + ν 0 a'))))
        = (∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => (fun ω y => φ (Fin.cons true ω) y) ω (y + ν 0 a)
              * star ((fun ω y => φ (Fin.cons true ω) y) ω (y + ν 0 a')))) := rfl
    rw [h1, cWinForm_shift_sum_star X (fun i : Fin n => ν i.succ) W
      (fun ω y => φ (Fin.cons true ω) y) (fun a : X => ν 0 a)]
    have hsplit : (∑ p : (Fin n → X) × (Fin n → X), ∑ x ∈ W,
          ((‖∑ a : X, cHalf n X (fun i : Fin n => ν i.succ)
            (fun ω y => φ (Fin.cons true ω) y) p.1 p.2 x (ν 0 a)‖ ^ 2 : ℝ) : ℂ))
        = ∑ i ∈ S, ((‖V i‖ ^ 2 : ℝ) : ℂ) :=
      (Finset.sum_product (Finset.univ : Finset ((Fin n → X) × (Fin n → X))) W
        (fun i => ((‖V i‖ ^ 2 : ℝ) : ℂ))).symm
    rw [hsplit]
    exact norm_ofReal_sum_eq S (fun i => ‖V i‖ ^ 2) (fun i _ => sq_nonneg _)
  rw [hL, hfalse, htrue]
  exact cauchySchwarzC S U V

/-! ## The constant family -/

lemma cWinForm_const_succ {n : ℕ} (X : Type) [Fintype X] (ν : Fin (n+1) → X → ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ) :
    cWinForm (n+1) X ν W (fun _ => g)
      = ∑ a : X, ∑ a' : X,
          cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a))) := by
  rw [cWinForm_succ]

/-- The box form of a single function is a nonnegative real. -/
lemma cWinForm_const_nonneg : ∀ (n : ℕ) (_ : 1 ≤ n) (X : Type) [Fintype X]
    (ν : Fin n → X → ℤ) (W : Finset ℤ) (g : ℤ → ℂ),
    ∃ r : ℝ, 0 ≤ r ∧ cWinForm n X ν W (fun _ => g) = ((r : ℝ) : ℂ) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ m ih =>
    intro hm
    cases m with
    | zero =>
      intro X inst ν W g
      exact ⟨_, Finset.sum_nonneg (fun x _ => sq_nonneg _), cWinForm_const_one X ν W g⟩
    | succ k =>
      intro X inst ν W g
      have hstep : ∀ a a' : X,
          cWinForm (k+1) X (fun i : Fin (k+1) => ν i.succ) W
            (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a)))
          = ((‖cWinForm (k+1) X (fun i : Fin (k+1) => ν i.succ) W
                (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a)))‖ : ℝ) : ℂ) := by
        intro a a'
        obtain ⟨r, hr, hz⟩ := ih (by omega) X (fun i : Fin (k+1) => ν i.succ) W
          (fun y => g (y + ν 0 a') * star (g (y + ν 0 a)))
        rw [hz, norm_ofReal_of_nonneg hr]
      refine ⟨∑ a : X, ∑ a' : X,
        ‖cWinForm (k+1) X (fun i : Fin (k+1) => ν i.succ) W
          (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a)))‖, ?_, ?_⟩
      · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun a' _ => norm_nonneg _
      · rw [cWinForm_const_succ]
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun a' _ => hstep a a'

lemma cWinForm_const_eq_norm {n : ℕ} (hn : 1 ≤ n) (X : Type) [Fintype X]
    (ν : Fin n → X → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    cWinForm n X ν W (fun _ => g) = ((‖cWinForm n X ν W (fun _ => g)‖ : ℝ) : ℂ) := by
  obtain ⟨r, hr, hz⟩ := cWinForm_const_nonneg n hn X ν W g
  rw [hz, norm_ofReal_of_nonneg hr]

lemma cWinForm_const_norm_succ {n : ℕ} (hn : 1 ≤ n) (X : Type) [Fintype X]
    (ν : Fin (n+1) → X → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    ‖cWinForm (n+1) X ν W (fun _ => g)‖
      = ∑ a : X, ∑ a' : X,
          ‖cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a)))‖ := by
  have hnn : ∀ a a' : X,
      cWinForm n X (fun i : Fin n => ν i.succ) W
          (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a)))
        = ((‖cWinForm n X (fun i : Fin n => ν i.succ) W
              (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a)))‖ : ℝ) : ℂ) :=
    fun a a' => cWinForm_const_eq_norm hn X _ W _
  rw [cWinForm_const_succ]
  rw [norm_sum_of_norm Finset.univ
    (fun a : X => ∑ a' : X,
      cWinForm n X (fun i : Fin n => ν i.succ) W
        (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a))))
    (fun a _ => by
      rw [norm_sum_of_norm Finset.univ
        (fun a' : X => cWinForm n X (fun i : Fin n => ν i.succ) W
          (fun _ y => g (y + ν 0 a') * star (g (y + ν 0 a)))) (fun a' _ => hnn a a')]
      exact sum_eq_ofReal_norm' Finset.univ _ (fun a' _ => hnn a a'))]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact norm_sum_of_norm Finset.univ _ (fun a' _ => hnn a a')

lemma cWinNorm_pow (n : ℕ) (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
    (g : ℤ → ℂ) :
    cWinNorm n X ν W g ^ (2 ^ n) = ‖cWinForm n X ν W (fun _ => g)‖ := by
  rw [cWinNorm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  have h : (1 / (2 : ℝ) ^ n) * ((2 ^ n : ℕ) : ℝ) = 1 := by
    push_cast; field_simp
  rw [h, Real.rpow_one]

/-! ## The induction -/

/-- The `t = 1` case of the Gowers--Cauchy--Schwarz inequality. -/
theorem cWinForm_norm_le_one (X : Type) [Fintype X] (ν : Fin 1 → X → ℤ) (W : Finset ℤ)
    (φ : (Fin 1 → Bool) → ℤ → ℂ) :
    ‖cWinForm 1 X ν W φ‖ ≤ ∏ ω : Fin 1 → Bool, cWinNorm 1 X ν W (φ ω) := by
  have hPf : 0 ≤ ∏ ω : Fin 1 → Bool, cWinNorm 1 X ν W (φ ω) :=
    Finset.prod_nonneg fun ω _ => cWinNorm_nonneg
  have hcs := cauchySchwarzC W
    (fun x => ∑ a' : X, φ (fun _ => false) (x + ν 0 a'))
    (fun x => ∑ a : X, φ (fun _ => true) (x + ν 0 a))
  have hsq : ‖cWinForm 1 X ν W φ‖ ^ 2
      ≤ (∏ ω : Fin 1 → Bool, cWinNorm 1 X ν W (φ ω)) ^ 2 := by
    rw [prod_fin_one_bool, mul_pow, cWinNorm_one_sq, cWinNorm_one_sq,
      cWinForm_const_one_norm, cWinForm_const_one_norm]
    rw [cWinForm_one]
    exact le_trans hcs (le_of_eq (mul_comm _ _))
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hPf] at h

theorem sum_cWinForm_le {n : ℕ} (hn : 1 ≤ n)
    (ih : ∀ (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
      (ψ : (Fin n → Bool) → ℤ → ℂ), ‖cWinForm n X ν W ψ‖ ≤ ∏ ω, cWinNorm n X ν W (ψ ω))
    (X : Type) [Fintype X] (ν : Fin (n+1) → X → ℤ) (W : Finset ℤ)
    (g : (Fin n → Bool) → ℤ → ℂ) :
    ‖(∑ a : X, ∑ a' : X,
        cWinForm n X (fun i : Fin n => ν i.succ) W
          (fun ω y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a'))))‖
      ≤ (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (g ω)) ^ 2 := by
  have h1 : ‖(∑ a : X, ∑ a' : X,
        cWinForm n X (fun i : Fin n => ν i.succ) W
          (fun ω y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a'))))‖
      ≤ ∑ a : X, ∑ a' : X,
          ‖cWinForm n X (fun i : Fin n => ν i.succ) W
            (fun ω y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a')))‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun a _ => norm_sum_le _ _
  have h2 : (∑ a : X, ∑ a' : X,
        ‖cWinForm n X (fun i : Fin n => ν i.succ) W
          (fun ω y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a')))‖)
      ≤ ∑ a : X, ∑ a' : X, ∏ ω : Fin n → Bool,
          cWinNorm n X (fun i : Fin n => ν i.succ) W
            (fun y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a'))) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ =>
      ih X (fun i : Fin n => ν i.succ) W _
  have h3 : (∑ a : X, ∑ a' : X, ∏ ω : Fin n → Bool,
        cWinNorm n X (fun i : Fin n => ν i.succ) W
          (fun y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a'))))
      ≤ ∏ ω : Fin n → Bool,
          (∑ p : X × X, (cWinNorm n X (fun i : Fin n => ν i.succ) W
            (fun y => g ω (y + ν 0 p.1) * star (g ω (y + ν 0 p.2)))) ^ (2 ^ n))
            ^ (1 / (2 : ℝ) ^ n) := by
    have hgen := genHolder (t := n) (X := X × X)
      (a := fun ω (p : X × X) => cWinNorm n X (fun i : Fin n => ν i.succ) W
        (fun y => g ω (y + ν 0 p.1) * star (g ω (y + ν 0 p.2))))
      (fun ω p => cWinNorm_nonneg)
    rw [Fintype.sum_prod_type] at hgen
    exact hgen
  have h4 : (∏ ω : Fin n → Bool,
        (∑ p : X × X, (cWinNorm n X (fun i : Fin n => ν i.succ) W
          (fun y => g ω (y + ν 0 p.1) * star (g ω (y + ν 0 p.2)))) ^ (2 ^ n))
          ^ (1 / (2 : ℝ) ^ n))
      ≤ ∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (g ω) ^ 2 := by
    refine Finset.prod_le_prod₀
      (fun ω _ => Real.rpow_nonneg (Finset.sum_nonneg fun p _ =>
        pow_nonneg cWinNorm_nonneg _) _) fun ω _ => ?_
    have hsum : (∑ p : X × X, (cWinNorm n X (fun i : Fin n => ν i.succ) W
          (fun y => g ω (y + ν 0 p.1) * star (g ω (y + ν 0 p.2)))) ^ (2 ^ n))
        = ‖cWinForm (n+1) X ν W (fun _ => g ω)‖ := by
      rw [Fintype.sum_prod_type]
      have h1' : ∀ a a' : X,
          (cWinNorm n X (fun i : Fin n => ν i.succ) W
            (fun y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a')))) ^ (2 ^ n)
          = ‖cWinForm n X (fun i : Fin n => ν i.succ) W
              (fun _ y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a')))‖ :=
        fun a a' => cWinNorm_pow n X _ W _
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => h1' a a'))]
      have hswap := sum_prod_swap (A := X)
        (fun a a' => ‖cWinForm n X (fun i : Fin n => ν i.succ) W
              (fun _ y => g ω (y + ν 0 a) * star (g ω (y + ν 0 a')))‖)
      rw [hswap, ← cWinForm_const_norm_succ (n := n) hn X ν W (g ω)]
    rw [hsum, ← cWinNorm_pow (n+1) X ν W (g ω)]
    have hgoal : (cWinNorm (n+1) X ν W (g ω) ^ (2 ^ (n+1) : ℕ) : ℝ) ^ (1 / (2 : ℝ) ^ n)
        = cWinNorm (n+1) X ν W (g ω) ^ 2 := by
      rw [← Real.rpow_natCast (cWinNorm (n+1) X ν W (g ω)) (2 ^ (n+1)),
        ← Real.rpow_mul cWinNorm_nonneg,
        ← Real.rpow_natCast (cWinNorm (n+1) X ν W (g ω)) 2]
      congr 1
      push_cast
      rw [pow_succ]
      field_simp
    exact le_of_eq hgoal
  have h4' : (∏ ω : Fin n → Bool,
        (∑ p : X × X, (cWinNorm n X (fun i : Fin n => ν i.succ) W
          (fun y => g ω (y + ν 0 p.1) * star (g ω (y + ν 0 p.2)))) ^ (2 ^ n))
          ^ (1 / (2 : ℝ) ^ n))
      ≤ (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (g ω)) ^ 2 := by
    rw [← Finset.prod_pow]
    exact h4
  exact le_trans h1 (le_trans h2 (le_trans h3 h4'))

theorem cWinForm_norm_succ_step {n : ℕ} (hn : 1 ≤ n)
    (ih : ∀ (X : Type) [Fintype X] (ν : Fin n → X → ℤ) (W : Finset ℤ)
      (ψ : (Fin n → Bool) → ℤ → ℂ), ‖cWinForm n X ν W ψ‖ ≤ ∏ ω, cWinNorm n X ν W (ψ ω))
    (X : Type) [Fintype X] (ν : Fin (n+1) → X → ℤ) (W : Finset ℤ)
    (φ : (Fin (n+1) → Bool) → ℤ → ℂ) :
    ‖cWinForm (n+1) X ν W φ‖
      ≤ (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons false ω)))
        * (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons true ω))) := by
  have hcs := cWinForm_succ_cs X ν W φ
  have hf := sum_cWinForm_le hn ih X ν W (fun ω y => φ (Fin.cons false ω) y)
  have ht := sum_cWinForm_le hn ih X ν W (fun ω y => φ (Fin.cons true ω) y)
  have hPf : 0 ≤ ∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons false ω)) :=
    Finset.prod_nonneg fun ω _ => cWinNorm_nonneg
  have hPt : 0 ≤ ∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons true ω)) :=
    Finset.prod_nonneg fun ω _ => cWinNorm_nonneg
  have hsq : ‖cWinForm (n+1) X ν W φ‖ ^ 2
      ≤ ((∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons false ω)))
        * (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons true ω)))) ^ 2 := by
    refine le_trans hcs ?_
    calc ‖(∑ a : X, ∑ a' : X,
              cWinForm n X (fun i : Fin n => ν i.succ) W
                (fun ω y => φ (Fin.cons false ω) (y + ν 0 a)
                  * star (φ (Fin.cons false ω) (y + ν 0 a'))))‖
          * ‖(∑ a : X, ∑ a' : X,
              cWinForm n X (fun i : Fin n => ν i.succ) W
                (fun ω y => φ (Fin.cons true ω) (y + ν 0 a)
                  * star (φ (Fin.cons true ω) (y + ν 0 a'))))‖
        ≤ (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons false ω))) ^ 2
          * (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons true ω))) ^ 2 :=
          mul_le_mul hf ht (norm_nonneg _) (sq_nonneg _)
      _ = ((∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons false ω)))
          * (∏ ω : Fin n → Bool, cWinNorm (n+1) X ν W (φ (Fin.cons true ω)))) ^ 2 := by
          ring
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hPf hPt)] at h

/-- **The index-set-agnostic Gowers--Cauchy--Schwarz inequality.** -/
theorem cWinForm_norm_le : ∀ (t : ℕ) (_ : 1 ≤ t) (X : Type) [Fintype X]
    (ν : Fin t → X → ℤ) (W : Finset ℤ) (φ : (Fin t → Bool) → ℤ → ℂ),
    ‖cWinForm t X ν W φ‖ ≤ ∏ ω : Fin t → Bool, cWinNorm t X ν W (φ ω) := by
  intro t
  induction t with
  | zero => intro ht; omega
  | succ n ih =>
    intro hn
    cases n with
    | zero => intro X inst ν W φ; exact cWinForm_norm_le_one X ν W φ
    | succ k =>
      intro X inst ν W φ
      have hstep := cWinForm_norm_succ_step (n := k+1) (by omega)
        (fun X' inst' ν' W' ψ => ih (by omega) X' ν' W' ψ) X ν W φ
      rw [prod_fin_succ_bool (m := k+1) (F := fun ω => cWinNorm (k+2) X ν W (φ ω))]
      exact hstep

end

end Work.Peluse.SwapC
