/-
The recursion and the `t = 1` base case for the flat Gowers cube sum `cubeSum` of
`Work.Peluse.Concat.GowersDefs`.

For the *constant* family `F ω = g` the flat cube sum is a nonnegative real: this is the recursion
of Peluse's Lemma 2.2 (the `2^t`-th power of the box norm),

* `cubeSum (fun _ => g) = |∑_x g x|^2` for `t = 1`,
* `N_t(g) = ∑_{u₀,u₁} N_{t-1}(y ↦ g (u₀,y) · conj (g (u₁,y)))` for `t ≥ 1`,

where `N_t(g) = ‖cubeSum (fun _ => g)‖`.  Everything is an induction on `t`: the recursion
`cubeSum_const_succ` (from `GowersDefs`) splits the level `t+1` cube sum into the level `t` cube
sums of the `(u₀,u₁)`-convolutions, and each of those is a nonnegative real by the induction
hypothesis.
-/
import Mathlib
import Submission.Work.Peluse.Concat.GowersDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

/-! ## Elementary facts about the real and the complex numbers -/

/-- `z * conj z` is the (nonnegative) real `‖z‖ ^ 2`. -/
private lemma mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [← starRingEnd_apply z, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The norm of the coercion of a nonnegative real number. -/
private lemma norm_ofReal_of_nonneg (r : ℝ) (hr : 0 ≤ r) : ‖((r : ℂ))‖ = r := by
  have h1 : ‖((r : ℂ))‖ ^ 2 = r ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact h
  · linarith [norm_nonneg ((r : ℂ))]

/-- A double sum of coerced real numbers is the coercion of the double sum. -/
private lemma sum_ofReal_double {ι κ : Type*} [Fintype ι] [Fintype κ] (r : ι → κ → ℝ) :
    (∑ i : ι, ∑ j : κ, ((r i j : ℝ) : ℂ)) = ((∑ i : ι, ∑ j : κ, r i j : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_sum Finset.univ (fun j => r i j)).symm

/-- The norm of a double sum of coerced nonnegative real numbers is the double sum. -/
private lemma norm_sum_ofReal_double {ι κ : Type*} [Fintype ι] [Fintype κ] (r : ι → κ → ℝ)
    (hr : ∀ i j, 0 ≤ r i j) :
    ‖∑ i : ι, ∑ j : κ, ((r i j : ℝ) : ℂ)‖ = ∑ i : ι, ∑ j : κ, r i j := by
  rw [sum_ofReal_double]
  exact norm_ofReal_of_nonneg _ (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hr i j)

/-! ## The base case `t = 1` -/

/-- The evaluation equivalence `(Fin 1 → Y) ≃ Y`. -/
private def fin1Equiv (Y : Type) : (Fin 1 → Y) ≃ Y where
  toFun f := f 0
  invFun y := fun _ => y
  left_inv f := by funext i; fin_cases i; rfl
  right_inv y := rfl

private lemma weight_fin1 (ω : Fin 1 → Bool) :
    Work.Peluse.weight ω = if ω 0 then 1 else 0 := by
  rw [Work.Peluse.weight, Finset.card_filter]
  rw [Fintype.sum_subsingleton (fun i : Fin 1 => if ω i then (1:ℕ) else 0) 0]

private lemma mix_fin1 {X : Type} (ω : Fin 1 → Bool) (u v : Fin 1 → X) :
    mix ω u v = if ω 0 then v else u := by
  funext i
  rw [show i = 0 from Fin.eq_zero i]
  by_cases h : ω 0 <;> simp [mix, h]

set_option linter.unusedSimpArgs false in
private lemma cubeProd_const_fin1 {X : Type} (g : (Fin 1 → X) → ℂ) (u v : Fin 1 → X) :
    cubeProd (fun (_ : Fin 1 → Bool) => g) u v = g u * star (g v) := by
  rw [cubeProd]
  rw [Fintype.prod_equiv (fin1Equiv Bool)
    (fun ω : Fin 1 → Bool => (star^[Work.Peluse.weight ω]) (g (mix ω u v)))
    (fun c : Bool => (star^[if c then (1:ℕ) else 0]) (g (if c then v else u)))
    (fun ω => by
      rw [show (fin1Equiv Bool) ω = ω 0 from rfl]
      rw [weight_fin1 ω, mix_fin1 ω u v])]
  rw [Fintype.prod_bool]
  simp only [if_true, if_false, Function.iterate_one, Function.iterate_zero_apply]
  exact mul_comm _ _

/-- The `t = 1` case: the flat cube sum of a constant family is `|∑ g| ^ 2`. -/
private lemma cubeSum_const_fin1 (X : Type) [Fintype X] (g : (Fin 1 → X) → ℂ) :
    cubeSum (fun (_ : Fin 1 → Bool) => g)
      = (∑ x : X, g (fun _ : Fin 1 => x)) * star (∑ x : X, g (fun _ : Fin 1 => x)) := by
  have hsum : cubeSum (fun (_ : Fin 1 → Bool) => g)
      = ∑ x : X, ∑ y : X, g (fun _ : Fin 1 => x) * star (g (fun _ : Fin 1 => y)) := by
    rw [cubeSum]
    rw [Fintype.sum_equiv (fin1Equiv X)
      (fun u : Fin 1 → X => ∑ v : Fin 1 → X, cubeProd (fun (_ : Fin 1 → Bool) => g) u v)
      (fun x : X => ∑ v : Fin 1 → X,
        cubeProd (fun (_ : Fin 1 → Bool) => g) (fun _ : Fin 1 => x) v)
      (fun u => by
        rw [show (fin1Equiv X) u = u 0 from rfl]
        refine Finset.sum_congr rfl fun v _ => ?_
        exact congrArg (fun w => cubeProd (fun (_ : Fin 1 → Bool) => g) w v)
          (by funext i; exact congr_arg u (Fin.eq_zero i)))]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fintype.sum_equiv (fin1Equiv X)
      (fun v : Fin 1 → X => cubeProd (fun (_ : Fin 1 → Bool) => g) (fun _ : Fin 1 => x) v)
      (fun y : X => g (fun _ : Fin 1 => x) * star (g (fun _ : Fin 1 => y)))
      (fun v => by
        rw [show (fin1Equiv X) v = v 0 from rfl]
        rw [cubeProd_const_fin1]
        exact congrArg (fun w => g (fun _ : Fin 1 => x) * star (g w))
          (by funext i; exact congr_arg v (Fin.eq_zero i)))]
  rw [hsum, ← Finset.sum_mul_sum]
  congr 1
  exact (Work.Peluse.Concat.star_sum Finset.univ
    (fun x : X => g (fun _ : Fin 1 => x))).symm

/-! ## The induction -/

/-- The flat cube sum of a constant family, as a function of the number of coordinates. -/
private def CS (t : ℕ) (X : Type) [Fintype X] (g : (Fin t → X) → ℂ) : ℂ :=
  cubeSum (fun (_ : Fin t → Bool) => g)

private lemma CS_eq (t : ℕ) (X : Type) [Fintype X] (g : (Fin t → X) → ℂ) :
    CS t X g = cubeSum (fun (_ : Fin t → Bool) => g) := rfl

private lemma NPow_eq (t : ℕ) (X : Type) [Fintype X] (g : (Fin t → X) → ℂ) :
    NPow t g = ‖CS t X g‖ := rfl

private lemma cubeSum_fin_one (X : Type) [Fintype X] (g : (Fin 1 → X) → ℂ) :
    cubeSum (fun (_ : Fin 1 → Bool) => g)
      = ((‖∑ x : X, g (fun _ : Fin 1 => x)‖ ^ 2 : ℝ) : ℂ) := by
  rw [cubeSum_const_fin1 X g, mul_star_self]

private lemma CS_fin_one (X : Type) [Fintype X] (g : (Fin 1 → X) → ℂ) :
    CS 1 X g = ((‖∑ x : X, g (fun _ : Fin 1 => x)‖ ^ 2 : ℝ) : ℂ) := by
  rw [CS_eq, cubeSum_fin_one]

private lemma NPow_fin_one (X : Type) [Fintype X] (g : (Fin 1 → X) → ℂ) :
    NPow 1 g = ‖∑ x : X, g (fun _ : Fin 1 => x)‖ ^ 2 := by
  rw [NPow_eq, CS_fin_one]
  exact norm_ofReal_of_nonneg _ (sq_nonneg _)

private lemma CS_one (X : Type) [Fintype X] (g : (Fin 1 → X) → ℂ) :
    CS 1 X g = ((NPow 1 g : ℝ) : ℂ) := by
  rw [CS_fin_one, NPow_fin_one]

/-- The recursion for the cube sum: from the `t`-level statement, the `t+1`-level cube sum of a
constant family is the coercion of the double sum of the `t`-level box norm powers of the
`(u₀,u₁)`-convolutions. -/
private lemma CS_succ_sum (t : ℕ) (X : Type) [Fintype X] (g : (Fin (t+1) → X) → ℂ)
    (ih : ∀ (Y : Type) [Fintype Y] (h : (Fin t → Y) → ℂ), CS t Y h = ((NPow t h : ℝ) : ℂ)) :
    CS (t+1) X g
      = ∑ u0 : X, ∑ u1 : X, ((NPow t (fun y : Fin t → X =>
          g (Fin.cons u0 y) * star (g (Fin.cons u1 y))) : ℝ) : ℂ) := by
  rw [CS_eq, cubeSum_const_succ t g]
  exact Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ih X _

/-- From the `t`-level statement, the `t+1`-level cube sum of a constant family is a nonnegative
real, namely `NPow (t+1) g`. -/
private lemma CS_ofReal (t : ℕ) (X : Type) [Fintype X] (g : (Fin (t+1) → X) → ℂ)
    (ih : ∀ (Y : Type) [Fintype Y] (h : (Fin t → Y) → ℂ), CS t Y h = ((NPow t h : ℝ) : ℂ)) :
    CS (t+1) X g = ((NPow (t+1) g : ℝ) : ℂ) := by
  have hsum := CS_succ_sum t X g ih
  have hN : NPow (t+1) g
      = ∑ u0 : X, ∑ u1 : X, NPow t (fun y : Fin t → X =>
          g (Fin.cons u0 y) * star (g (Fin.cons u1 y))) := by
    rw [NPow_eq, hsum]
    exact norm_sum_ofReal_double
      (fun u0 u1 => NPow t (fun y : Fin t → X =>
        g (Fin.cons u0 y) * star (g (Fin.cons u1 y))))
      (fun _ _ => norm_nonneg _)
  rw [hsum, hN]
  exact sum_ofReal_double _

/-- The recursive step for the box norm powers. -/
private lemma NPow_succ_eq (t : ℕ) (X : Type) [Fintype X] (g : (Fin (t+1) → X) → ℂ)
    (ih : ∀ (Y : Type) [Fintype Y] (h : (Fin t → Y) → ℂ), CS t Y h = ((NPow t h : ℝ) : ℂ)) :
    NPow (t+1) g
      = ∑ u0 : X, ∑ u1 : X,
          NPow t (fun y : Fin t → X =>
            g (Fin.cons u0 y) * star (g (Fin.cons u1 y))) := by
  rw [NPow_eq, CS_succ_sum t X g ih]
  exact norm_sum_ofReal_double
    (fun u0 u1 => NPow t (fun y : Fin t → X =>
      g (Fin.cons u0 y) * star (g (Fin.cons u1 y))))
    (fun _ _ => norm_nonneg _)

/-- The `t`-level `cubeSum` of a constant family is the coercion of the `t`-th box norm power. -/
private lemma CS_ofReal_all : ∀ t : ℕ, 1 ≤ t →
    ∀ (X : Type) [Fintype X] (g : (Fin t → X) → ℂ), CS t X g = ((NPow t g : ℝ) : ℂ) := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
    intro _ X _ g
    cases n with
    | zero => exact CS_one X g
    | succ k => exact CS_ofReal (k+1) X g (ih (by omega))

theorem gcsRecurse :
    (∀ (X : Type) [Fintype X] (g : (Fin 1 → X) → ℂ),
        Work.Peluse.Concat.cubeSum (fun (_ : Fin 1 → Bool) => g)
          = ↑(‖∑ x : X, g (fun _ : Fin 1 => x)‖ ^ 2))
    ∧ (∀ (X : Type) [Fintype X] (t : ℕ), 1 ≤ t → ∀ (g : (Fin t → X) → ℂ),
        Work.Peluse.Concat.cubeSum (fun (_ : Fin t → Bool) => g)
          = ↑(Work.Peluse.Concat.NPow t g))
    ∧ (∀ (X : Type) [Fintype X] (t : ℕ), 1 ≤ t → ∀ (g : (Fin (t+1) → X) → ℂ),
        Work.Peluse.Concat.NPow (t+1) g = ∑ u0 : X, ∑ u1 : X,
          Work.Peluse.Concat.NPow t
            (fun y : Fin t → X => g (Fin.cons u0 y) * star (g (Fin.cons u1 y)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X hX g
    exact cubeSum_fin_one X g
  · intro X hX t ht g
    exact CS_ofReal_all t ht X g
  · intro X hX t ht g
    exact NPow_succ_eq t X g (fun Y hY h => CS_ofReal_all t ht Y h)



end

end Work.Peluse.Concat
