import Mathlib
import Submission.Work.Peluse.Concat.gcsRecurse
import Submission.Work.Peluse.Ulower.flatCubeTools
import Submission.Work.Peluse.Ulower.cubeSumPerm

/-!
# Dropping a one-sided modulus weight from the flat cube sum

The two main tools for the flat-cube transform `Work.Peluse.Ulower.flatCubeTransform`.

* `npowWeightDrop` : the weight `ρ(·)` (a `[0,1]`-valued function of the *inner* variable) can be
  dropped from the aggregate `∑_{u₀,u₁} NPow j (y ↦ ρ y · F u₀ y · conj (F u₁ y))`.  This is the
  "aggregate" statement behind the failing pointwise version; it is proved by the `Fin.cons`
  recursion `Concat.gcsRecurse.2.2`, the base case `j = 1` being the weighted Gram inequality
  `weightedFrobSwap_le`.
* `npowBlind` : a *blind factor* `φ` (one that ignores one of the coordinates) of modulus `≤ 1` can
  be dropped from `NPow t (f · φ)`.  At coordinate `0` this is `npowWeightDrop` plus the recursion;
  for an arbitrary coordinate one transports along the transposition
  (`npowPermInv`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse.Concat

/-! ## Elementary complex identities -/

lemma norm_ofReal_nonneg (r : ℝ) (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]

lemma star_ofReal' (r : ℝ) : star (((r : ℝ)) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

lemma star_ofReal_mul' (r : ℝ) (z : ℂ) :
    star (((r : ℝ) : ℂ) * z) = ((r : ℝ) : ℂ) * star z := by
  rw [star_mul, star_ofReal', mul_comm]

/-- The four-factor identity behind the induction step of `npowWeightDrop`. -/
lemma key_ident (r s : ℝ) (a b c d : ℂ) :
    (((r : ℝ) : ℂ) * (a * star c)) * star (((s : ℝ) : ℂ) * (b * star d))
      = ((r * s : ℝ) : ℂ) * ((a * star b) * star (c * star d)) := by
  rw [star_ofReal_mul', star_mul, star_mul, star_star]
  push_cast
  ring

/-- The weight-free four-factor identity. -/
lemma key_ident_nw (a b c d : ℂ) :
    (a * star b) * star (c * star d) = (a * star c) * star (b * star d) := by
  rw [star_mul, star_mul, star_star]
  ring

/-- The `t = 1` case: the flat cube sum of a constant family is `|∑ g| ^ 2`. -/
lemma NPow_fin_one {X : Type} [Fintype X] (H : (Fin 1 → X) → ℂ) :
    Concat.NPow 1 H = ‖∑ x : X, H (fun _ : Fin 1 => x)‖ ^ 2 := by
  unfold Concat.NPow
  rw [Concat.gcsRecurse.1 X H]
  exact norm_ofReal_nonneg _ (sq_nonneg _)

/-- The summation identity `∑_{u₀,u₁,v₀,v₁} = ∑_{v₀,v₁,u₀,u₁}`. -/
lemma sum_swap_four {M : Type*} [AddCommMonoid M] {X : Type} [Fintype X]
    (f : X → X → X → X → M) :
    (∑ u0 : X, ∑ u1 : X, ∑ v0 : X, ∑ v1 : X, f u0 u1 v0 v1)
      = ∑ v0 : X, ∑ v1 : X, ∑ u0 : X, ∑ u1 : X, f u0 u1 v0 v1 := by
  calc (∑ u0 : X, ∑ u1 : X, ∑ v0 : X, ∑ v1 : X, f u0 u1 v0 v1)
      = ∑ u0 : X, ∑ v0 : X, ∑ u1 : X, ∑ v1 : X, f u0 u1 v0 v1 :=
        Finset.sum_congr rfl fun u0 _ => Finset.sum_comm
    _ = ∑ v0 : X, ∑ u0 : X, ∑ u1 : X, ∑ v1 : X, f u0 u1 v0 v1 := Finset.sum_comm
    _ = ∑ v0 : X, ∑ v1 : X, ∑ u0 : X, ∑ u1 : X, f u0 u1 v0 v1 := by
        refine Finset.sum_congr rfl fun v0 _ => ?_
        calc (∑ u0 : X, ∑ u1 : X, ∑ v1 : X, f u0 u1 v0 v1)
            = ∑ u0 : X, ∑ v1 : X, ∑ u1 : X, f u0 u1 v0 v1 :=
              Finset.sum_congr rfl fun u0 _ => Finset.sum_comm
          _ = ∑ v1 : X, ∑ u0 : X, ∑ u1 : X, f u0 u1 v0 v1 := Finset.sum_comm

/-! ## The aggregate weight-dropping lemma -/

theorem npowWeightDrop : ∀ (j : ℕ), 1 ≤ j → ∀ {X : Type} [Fintype X]
    (F : (Fin (j+1) → X) → ℂ) (ρ : (Fin j → X) → ℝ)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1),
    (∑ u0 : X, ∑ u1 : X, Concat.NPow j (fun y : Fin j → X =>
        ((ρ y : ℝ) : ℂ) * (F (Fin.cons u0 y) * star (F (Fin.cons u1 y)))))
      ≤ ∑ u0 : X, ∑ u1 : X, Concat.NPow j (fun y : Fin j → X =>
        F (Fin.cons u0 y) * star (F (Fin.cons u1 y))) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro X instX F ρ hρ0 hρ1
    have h := weightedFrobSwap_le (fun u x : X => F (Fin.cons u (fun _ : Fin 1 => x)))
      (fun x : X => ρ (fun _ : Fin 1 => x)) (fun x => hρ0 _) (fun x => hρ1 _)
    simpa only [NPow_fin_one] using h
  | succ k hk ih =>
    intro X instX F ρ hρ0 hρ1
    set Fv : X → X → (Fin (k+1) → X) → ℂ := fun v0 v1 w =>
      F (Fin.cons (w 0) (Fin.cons v0 (Fin.tail w)))
        * star (F (Fin.cons (w 0) (Fin.cons v1 (Fin.tail w)))) with hFv
    have hpt : ∀ (u0 u1 v0 v1 : X),
        (fun z : Fin k → X =>
          ((ρ (Fin.cons v0 z) * ρ (Fin.cons v1 z) : ℝ) : ℂ)
            * (Fv v0 v1 (Fin.cons u0 z) * star (Fv v0 v1 (Fin.cons u1 z))))
        = fun z : Fin k → X =>
          (((ρ (Fin.cons v0 z) : ℝ)) : ℂ)
            * (F (Fin.cons u0 (Fin.cons v0 z)) * star (F (Fin.cons u1 (Fin.cons v0 z))))
            * star ((((ρ (Fin.cons v1 z) : ℝ)) : ℂ)
              * (F (Fin.cons u0 (Fin.cons v1 z))
                * star (F (Fin.cons u1 (Fin.cons v1 z))))) := by
      intro u0 u1 v0 v1
      funext z
      simp only [hFv, Fin.cons_zero, Fin.tail_cons]
      exact (key_ident (ρ (Fin.cons v0 z)) (ρ (Fin.cons v1 z))
        (F (Fin.cons u0 (Fin.cons v0 z))) (F (Fin.cons u0 (Fin.cons v1 z)))
        (F (Fin.cons u1 (Fin.cons v0 z))) (F (Fin.cons u1 (Fin.cons v1 z)))).symm
    have hpt2 : ∀ (u0 u1 v0 v1 : X),
        (fun z : Fin k → X => Fv v0 v1 (Fin.cons u0 z) * star (Fv v0 v1 (Fin.cons u1 z)))
        = fun z : Fin k → X =>
          (F (Fin.cons u0 (Fin.cons v0 z)) * star (F (Fin.cons u1 (Fin.cons v0 z))))
            * star (F (Fin.cons u0 (Fin.cons v1 z))
              * star (F (Fin.cons u1 (Fin.cons v1 z)))) := by
      intro u0 u1 v0 v1
      funext z
      simp only [hFv, Fin.cons_zero, Fin.tail_cons]
      exact key_ident_nw (F (Fin.cons u0 (Fin.cons v0 z)))
        (F (Fin.cons u0 (Fin.cons v1 z))) (F (Fin.cons u1 (Fin.cons v0 z)))
        (F (Fin.cons u1 (Fin.cons v1 z)))
    calc (∑ u0 : X, ∑ u1 : X, Concat.NPow (k+1) (fun y : Fin (k+1) → X =>
            ((ρ y : ℝ) : ℂ) * (F (Fin.cons u0 y) * star (F (Fin.cons u1 y)))))
        = ∑ u0 : X, ∑ u1 : X, ∑ v0 : X, ∑ v1 : X, Concat.NPow k (fun z : Fin k → X =>
            ((((ρ (Fin.cons v0 z) : ℝ)) : ℂ)
              * (F (Fin.cons u0 (Fin.cons v0 z)) * star (F (Fin.cons u1 (Fin.cons v0 z)))))
            * star ((((ρ (Fin.cons v1 z) : ℝ)) : ℂ)
              * (F (Fin.cons u0 (Fin.cons v1 z))
                * star (F (Fin.cons u1 (Fin.cons v1 z)))))) := by
          refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_
          rw [Concat.gcsRecurse.2.2 X k hk]
      _ = ∑ v0 : X, ∑ v1 : X, ∑ u0 : X, ∑ u1 : X, Concat.NPow k (fun z : Fin k → X =>
            ((((ρ (Fin.cons v0 z) : ℝ)) : ℂ)
              * (F (Fin.cons u0 (Fin.cons v0 z)) * star (F (Fin.cons u1 (Fin.cons v0 z)))))
            * star ((((ρ (Fin.cons v1 z) : ℝ)) : ℂ)
              * (F (Fin.cons u0 (Fin.cons v1 z))
                * star (F (Fin.cons u1 (Fin.cons v1 z)))))) :=
          sum_swap_four _
      _ = ∑ v0 : X, ∑ v1 : X, ∑ u0 : X, ∑ u1 : X, Concat.NPow k (fun z : Fin k → X =>
            ((ρ (Fin.cons v0 z) * ρ (Fin.cons v1 z) : ℝ) : ℂ)
              * (Fv v0 v1 (Fin.cons u0 z) * star (Fv v0 v1 (Fin.cons u1 z)))) := by
          refine Finset.sum_congr rfl fun v0 _ => Finset.sum_congr rfl fun v1 _ =>
            Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_
          rw [hpt u0 u1 v0 v1]
      _ ≤ ∑ v0 : X, ∑ v1 : X, ∑ u0 : X, ∑ u1 : X, Concat.NPow k (fun z : Fin k → X =>
            Fv v0 v1 (Fin.cons u0 z) * star (Fv v0 v1 (Fin.cons u1 z))) := by
          refine Finset.sum_le_sum fun v0 _ => Finset.sum_le_sum fun v1 _ => ?_
          exact ih (Fv v0 v1) (fun z : Fin k → X => ρ (Fin.cons v0 z) * ρ (Fin.cons v1 z))
            (fun z => mul_nonneg (hρ0 _) (hρ0 _))
            (fun z => by
              nlinarith [hρ0 (Fin.cons v0 z), hρ0 (Fin.cons v1 z), hρ1 (Fin.cons v0 z),
                hρ1 (Fin.cons v1 z)])
      _ = ∑ v0 : X, ∑ v1 : X, ∑ u0 : X, ∑ u1 : X, Concat.NPow k (fun z : Fin k → X =>
            (F (Fin.cons u0 (Fin.cons v0 z)) * star (F (Fin.cons u1 (Fin.cons v0 z))))
              * star (F (Fin.cons u0 (Fin.cons v1 z))
                * star (F (Fin.cons u1 (Fin.cons v1 z))))) := by
          refine Finset.sum_congr rfl fun v0 _ => Finset.sum_congr rfl fun v1 _ =>
            Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_
          rw [hpt2 u0 u1 v0 v1]
      _ = ∑ u0 : X, ∑ u1 : X, ∑ v0 : X, ∑ v1 : X, Concat.NPow k (fun z : Fin k → X =>
            (F (Fin.cons u0 (Fin.cons v0 z)) * star (F (Fin.cons u1 (Fin.cons v0 z))))
              * star (F (Fin.cons u0 (Fin.cons v1 z))
                * star (F (Fin.cons u1 (Fin.cons v1 z))))) :=
          (sum_swap_four _).symm
      _ = ∑ u0 : X, ∑ u1 : X, Concat.NPow (k+1) (fun y : Fin (k+1) → X =>
            F (Fin.cons u0 y) * star (F (Fin.cons u1 y))) := by
          refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_
          rw [Concat.gcsRecurse.2.2 X k hk]

/-! ## Blind factors -/

lemma mul_star_self (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma norm_star_iterate (n : ℕ) (z : ℂ) : ‖(star^[n]) z‖ = ‖z‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', norm_star, ih]

/-- `Function.update` at the head position of `Fin.cons`. -/
lemma update_cons_eq_cons {k : ℕ} {X : Type} (u u₀ : X) (y : Fin k → X) :
    Function.update ((Fin.cons u₀ y : Fin (k+1) → X)) 0 u
      = (Fin.cons u y : Fin (k+1) → X) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [Function.update_self, Fin.cons_zero]
  · intro j
    rw [Function.update_of_ne (Fin.succ_ne_zero j), Fin.cons_succ, Fin.cons_succ]

/-- Transporting a coordinate-`i` blindness to coordinate `0` along the transposition. -/
lemma precomp_swap_update {k : ℕ} {X : Type} (i : Fin (k+1)) (v : Fin (k+1) → X) (u : X) :
    precomp (Equiv.swap i 0) (Function.update v 0 u)
      = Function.update (precomp (Equiv.swap i 0) v) i u := by
  funext j
  by_cases h : j = i
  · rw [h]
    show (Function.update v 0 u) (Equiv.swap i 0 i)
      = Function.update (precomp (Equiv.swap i 0) v) i u i
    rw [Equiv.swap_apply_left, Function.update_self, Function.update_self]
  · have hj : (Equiv.swap i 0) j ≠ 0 := by
      intro h0
      exact h (Equiv.injective _ (by rw [h0, Equiv.swap_apply_left]))
    show (Function.update v 0 u) (Equiv.swap i 0 j)
      = Function.update (precomp (Equiv.swap i 0) v) i u j
    rw [Function.update_of_ne hj, Function.update_of_ne h]
    rfl

/-- **Blind factor at coordinate `0`.** -/
theorem npowBlindZero (k : ℕ) {X : Type} [Fintype X] [Nonempty X]
    (f φ : (Fin (k+1) → X) → ℂ) (hφ : ∀ v, ‖φ v‖ ≤ 1)
    (hblind : ∀ (v : Fin (k+1) → X) (u : X), φ (Function.update v 0 u) = φ v) :
    Concat.NPow (k+1) (fun v => f v * φ v) ≤ Concat.NPow (k+1) f := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`
    subst hk0
    have hconst : ∀ v : Fin 1 → X,
        φ v = φ (fun _ : Fin 1 => Classical.choice ‹Nonempty X›) := by
      intro v
      have h1 : Function.update v 0 (Classical.choice ‹Nonempty X›)
          = (fun _ : Fin 1 => Classical.choice ‹Nonempty X›) := by
        funext j
        fin_cases j
        simp [Function.update]
      rw [← hblind v (Classical.choice ‹Nonempty X›), h1]
    rw [NPow_fin_one, NPow_fin_one]
    have hsum : (∑ x : X, f (fun _ : Fin 1 => x) * φ (fun _ : Fin 1 => x))
        = φ (fun _ : Fin 1 => Classical.choice ‹Nonempty X›)
            * ∑ x : X, f (fun _ : Fin 1 => x) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hconst (fun _ : Fin 1 => x)]
      ring
    rw [hsum]
    have hc : ‖φ (fun _ : Fin 1 => Classical.choice ‹Nonempty X›)‖ ≤ 1 := hφ _
    have hc2 : ‖φ (fun _ : Fin 1 => Classical.choice ‹Nonempty X›)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (φ (fun _ : Fin 1 => Classical.choice ‹Nonempty X›)), hc]
    calc ‖φ (fun _ : Fin 1 => Classical.choice ‹Nonempty X›)
            * ∑ x : X, f (fun _ : Fin 1 => x)‖ ^ 2
        = ‖φ (fun _ : Fin 1 => Classical.choice ‹Nonempty X›)‖ ^ 2
            * ‖∑ x : X, f (fun _ : Fin 1 => x)‖ ^ 2 := by
          rw [norm_mul]; ring
      _ ≤ 1 * ‖∑ x : X, f (fun _ : Fin 1 => x)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hc2 (sq_nonneg _)
      _ = ‖∑ x : X, f (fun _ : Fin 1 => x)‖ ^ 2 := one_mul _
  · -- `k ≥ 1`
    have hψ : ∀ (u : X) (y : Fin k → X),
        φ (Fin.cons u y) = φ (Fin.cons (Classical.choice ‹Nonempty X›) y) := by
      intro u y
      rw [← update_cons_eq_cons u (Classical.choice ‹Nonempty X›) y]
      exact hblind _ u
    have hpt : ∀ (u0 u1 : X),
        (fun y : Fin k → X => (f (Fin.cons u0 y) * φ (Fin.cons u0 y))
            * star (f (Fin.cons u1 y) * φ (Fin.cons u1 y)))
        = fun y : Fin k → X =>
            ((‖φ (Fin.cons (Classical.choice ‹Nonempty X›) y)‖ ^ 2 : ℝ) : ℂ)
              * (f (Fin.cons u0 y) * star (f (Fin.cons u1 y))) := by
      intro u0 u1
      funext y
      set ψ : ℂ := φ (Fin.cons (Classical.choice ‹Nonempty X›) y) with hψdef
      calc (f (Fin.cons u0 y) * φ (Fin.cons u0 y))
              * star (f (Fin.cons u1 y) * φ (Fin.cons u1 y))
          = f (Fin.cons u0 y) * (ψ * star ψ) * star (f (Fin.cons u1 y)) := by
            rw [hψ u0 y, hψ u1 y, star_mul, ← hψdef]
            ring
        _ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) * (f (Fin.cons u0 y) * star (f (Fin.cons u1 y))) := by
            rw [hψdef, mul_star_self]
            ring
    calc Concat.NPow (k+1) (fun v => f v * φ v)
        = ∑ u0 : X, ∑ u1 : X, Concat.NPow k (fun y : Fin k → X =>
            (f (Fin.cons u0 y) * φ (Fin.cons u0 y))
              * star (f (Fin.cons u1 y) * φ (Fin.cons u1 y))) := by
          rw [Concat.gcsRecurse.2.2 X k hkpos]
      _ = ∑ u0 : X, ∑ u1 : X, Concat.NPow k (fun y : Fin k → X =>
            ((‖φ (Fin.cons (Classical.choice ‹Nonempty X›) y)‖ ^ 2 : ℝ) : ℂ)
              * (f (Fin.cons u0 y) * star (f (Fin.cons u1 y)))) := by
          refine Finset.sum_congr rfl fun u0 _ => Finset.sum_congr rfl fun u1 _ => ?_
          rw [hpt u0 u1]
      _ ≤ ∑ u0 : X, ∑ u1 : X, Concat.NPow k (fun y : Fin k → X =>
            f (Fin.cons u0 y) * star (f (Fin.cons u1 y))) :=
          npowWeightDrop k hkpos f
            (fun y => ‖φ (Fin.cons (Classical.choice ‹Nonempty X›) y)‖ ^ 2)
            (fun y => sq_nonneg _)
            (fun y => by
              have h1 : ‖φ (Fin.cons (Classical.choice ‹Nonempty X›) y)‖ ≤ 1 :=
                hφ _
              nlinarith [norm_nonneg (φ (Fin.cons (Classical.choice ‹Nonempty X›) y))])
      _ = Concat.NPow (k+1) f := by
          rw [Concat.gcsRecurse.2.2 X k hkpos]

/-- **Blind factor at an arbitrary coordinate.** -/
theorem npowBlind {t : ℕ} (ht : 1 ≤ t) {X : Type} [Fintype X] [Nonempty X]
    (i : Fin t) (f φ : (Fin t → X) → ℂ) (hφ : ∀ v, ‖φ v‖ ≤ 1)
    (hblind : ∀ (v : Fin t → X) (u : X), φ (Function.update v i u) = φ v) :
    Concat.NPow t (fun v => f v * φ v) ≤ Concat.NPow t f := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  set τ : Equiv.Perm (Fin (k+1)) := Equiv.swap i 0 with hτ
  have hb : ∀ (v : Fin (k+1) → X) (u : X),
      (fun w => φ (precomp τ w)) (Function.update v 0 u)
        = (fun w => φ (precomp τ w)) v := by
    intro v u
    show φ (precomp τ (Function.update v 0 u)) = φ (precomp τ v)
    rw [precomp_swap_update i v u]
    exact hblind _ u
  have h1 := npowBlindZero k (fun w => f (precomp τ w)) (fun w => φ (precomp τ w))
    (fun w => hφ _) hb
  rw [show (fun w : Fin (k+1) → X => f (precomp τ w) * φ (precomp τ w))
      = (fun w => (fun v => f v * φ v) (precomp τ w)) from rfl] at h1
  rw [npowPermInv τ (fun v => f v * φ v)] at h1
  rw [npowPermInv τ f] at h1
  exact h1

/-- **Dropping a whole `Finset` of blind factors.** -/
theorem npowBlindProd {t : ℕ} (ht : 1 ≤ t) {X : Type} [Fintype X] [Nonempty X]
    (Φ : (Fin t → Bool) → (Fin t → X) → ℂ) (hΦ : ∀ α v, ‖Φ α v‖ ≤ 1)
    (hblind : ∀ α : Fin t → Bool, α ≠ (fun _ => false) → ∃ i : Fin t,
      ∀ (v : Fin t → X) (u : X), Φ α (Function.update v i u) = Φ α v) :
    ∀ (A : Finset (Fin t → Bool)) (f : (Fin t → X) → ℂ),
      (∀ α ∈ A, α ≠ (fun _ => false)) →
      Concat.NPow t (fun v => f v * ∏ α ∈ A, Φ α v) ≤ Concat.NPow t f := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro f _
    simp
  | insert α A hα ih =>
    intro f hA
    have hA' : ∀ β ∈ A, β ≠ (fun _ => false) := fun β hβ =>
      hA β (Finset.mem_insert_of_mem hβ)
    have hα0 : α ≠ (fun _ => false) := hA α (Finset.mem_insert_self α A)
    obtain ⟨i, hi⟩ := hblind α hα0
    refine le_trans ?_ (ih f hA')
    have heq : (fun v : Fin t → X => f v * ∏ β ∈ insert α A, Φ β v)
        = (fun v : Fin t → X => (f v * ∏ β ∈ A, Φ β v) * Φ α v) := by
      funext v
      rw [Finset.prod_insert hα]
      ring
    rw [heq]
    exact npowBlind ht i (fun v => f v * ∏ β ∈ A, Φ β v) (Φ α) (fun v => hΦ α v) hi

end

end Work.Peluse.Ulower
