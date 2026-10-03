/-
# `Submission.Work.FIChain.sum_T_eq_levelSum`

The identity

`∑_{b ≤ x, sy < b} μ(b) · ∑_{e ≤ x} s3MPT(n,b,e,u) = (1/u) · s3MPLevelSum(n,u)`

which is the purely formal (Fubini + definition-unfolding) step relating the comparison
integrand `s3MPT` of the `n`-expanded `(1.7)`-main half to the level sum `s3MPLevelSum`.

The content is: `s3MPT` is a product of the five `0/1` indicators of the level window
conditions times `ρ(b·e) · (1/u) · Σ_{d ≤ ⌊u⌋} μ(d)·g̃(b·e·d)` (see `s3MPT_eq_ite`), so the
`(b,e)`-sum can be rewritten as a triple `(b,e,d)`-sum of a single summand supported on the
`b`-window, and the three sums can be interchanged.
-/
import Mathlib
import Submission.Work.FIChain.s3MainLevelAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Boolean bookkeeping -/

/-- A product of five `0/1` indicators is the `0/1` indicator of the conjunction, with the two
remaining factors kept aside. -/
private lemma prod_ite_indicators (A B C D G : Prop) [Decidable A] [Decidable B] [Decidable C]
    [Decidable D] [Decidable G] (E F : ℝ) :
    (if A then (1:ℝ) else 0) * (if B then 1 else 0) * (if C then 1 else 0) * (if D then 1 else 0)
      * E * F * (if G then 1 else 0) = (if A ∧ B ∧ C ∧ D ∧ G then (1:ℝ) else 0) * (E * F) := by
  by_cases hA : A <;> by_cases hB : B <;> by_cases hC : C <;> by_cases hD : D <;>
    by_cases hG : G <;> simp [hA, hB, hC, hD, hG]

/-- An `if`-filtered sum is the indicator times the plain sum. -/
private lemma sum_ite_eq_ite_mul_sum (P : Prop) [Decidable P] (s : Finset ℕ) (f : ℕ → ℝ) :
    ∑ d ∈ s, (if P then f d else 0) = (if P then (1:ℝ) else 0) * ∑ d ∈ s, f d := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by by_cases h : P <;> simp [h]

/-! ## 2. Unfolding `s3MPT` on the `b`-window -/

/-- Membership in the level window, in the order of the (`b·e`-split) conditions of `s3MPT`. -/
private lemma mem_s3LevelWindow_iff (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ)
    (e b : ℕ) (hb1 : 1 ≤ b) (hbx : b ≤ x) (hbsy : sy < (b:ℝ)) (hnx : n ≤ x) :
    b ∈ s3LevelWindow x z sz Cm sy n u e ↔
      ((b:ℝ)*(e:ℝ)*z ≤ (x:ℝ) ∧ (b:ℝ)*(e:ℝ)*z < (n:ℝ) ∧ (n:ℝ) ≤ (b:ℝ)*(e:ℝ)*sz ∧
        (n ≤ x) ∧ (b:ℝ)*(e:ℝ)*(Cm:ℝ)*u < (n:ℝ)) := by
  rw [mem_s3LevelWindow]
  have r1 : (e:ℝ)*(b:ℝ)*z = (b:ℝ)*(e:ℝ)*z := by ring
  have r2 : (e:ℝ)*(b:ℝ)*sz = (b:ℝ)*(e:ℝ)*sz := by ring
  have r3 : (e:ℝ)*(b:ℝ)*(Cm:ℝ)*u = (b:ℝ)*(e:ℝ)*(Cm:ℝ)*u := by ring
  constructor
  · rintro ⟨g1, g2, g3, g4, g5, g6, g7⟩
    exact ⟨by rwa [r1] at g4, by rwa [r1] at g6, by rwa [r2] at g5, hnx, by rwa [r3] at g7⟩
  · rintro ⟨g4, g6, g5, _, g7⟩
    exact ⟨hb1, hbx, hbsy, by rwa [r1], by rwa [r2], by rwa [r1], by rwa [r3]⟩

/-- `s3MPT` is the indicator of the level window times `ρ(b·e)·(1/u)·Σ_{d ≤ ⌊u⌋} μ(d)·g̃(b·e·d)`. -/
private lemma s3MPT_eq_ite (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ)
    (b e : ℕ) (hb1 : 1 ≤ b) (hbx : b ≤ x) (hbsy : sy < (b:ℝ)) (hnx : n ≤ x) :
    s3MPT lam x z sz Cm n b e u
      = (if b ∈ s3LevelWindow x z sz Cm sy n u e then (1:ℝ) else 0)
        * (Submission.ASP.rhoOf lam (b*e) * ((1/u) * ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
            (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b*e)*d))) := by
  have hiff := mem_s3LevelWindow_iff x z sz Cm sy n u e b hb1 hbx hbsy hnx
  rw [s3MPT]
  rw [prod_ite_indicators ((b:ℝ)*(e:ℝ)*z ≤ (x:ℝ)) ((b:ℝ)*(e:ℝ)*z < (n:ℝ))
        ((n:ℝ) ≤ (b:ℝ)*(e:ℝ)*sz) (n ≤ x) ((b:ℝ)*(e:ℝ)*(Cm:ℝ)*u < (n:ℝ))
        (Submission.ASP.rhoOf lam (b*e))
        ((1/u) * ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b*e)*d))]
  by_cases hW : b ∈ s3LevelWindow x z sz Cm sy n u e
  · rw [if_pos hW]
    obtain ⟨h1, h2, h3, _, h4⟩ := hiff.mp hW
    rw [if_pos ⟨h1, h2, h3, hnx, h4⟩]
  · rw [if_neg hW]
    have h5 : ¬ ((b:ℝ)*(e:ℝ)*z ≤ (x:ℝ) ∧ (b:ℝ)*(e:ℝ)*z < (n:ℝ) ∧
        (n:ℝ) ≤ (b:ℝ)*(e:ℝ)*sz ∧ (n ≤ x) ∧ (b:ℝ)*(e:ℝ)*(Cm:ℝ)*u < (n:ℝ)) :=
      fun h => hW (hiff.mpr h)
    rw [if_neg h5]

/-- The termwise form used for the `b`-sum: `μ(b)·s3MPT` is the `d`-sum of a summand supported
on the level window, with `ρ` and `g̃` in the `(e·b)`-form needed by the level sum. -/
private lemma s3MPT_mul_eq (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ)
    (b e : ℕ) (hb : b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b:ℕ):ℝ))) (hnx : n ≤ x) :
    (ArithmeticFunction.moebius b : ℝ) * s3MPT lam x z sz Cm n b e u
      = ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
          (if b ∈ s3LevelWindow x z sz Cm sy n u e then
            (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)) else 0) := by
  obtain ⟨hbI, hbsy⟩ := Finset.mem_filter.mp hb
  obtain ⟨hb1, hbx⟩ := Finset.mem_Icc.mp hbI
  rw [s3MPT_eq_ite lam x z sz Cm sy n u b e hb1 hbx hbsy hnx]
  rw [sum_ite_eq_ite_mul_sum (b ∈ s3LevelWindow x z sz Cm sy n u e) (Finset.Icc 1 ⌊u⌋₊)
        (fun d => (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)))]
  have h2 : (∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
        (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
          * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)))
      = (1/u) * (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (b*e)
          * ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
              ((ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil ((b*e)*d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    have hρ : Submission.ASP.rhoOf lam (e*b) = Submission.ASP.rhoOf lam (b*e) := by
      rw [Nat.mul_comm e b]
    have hg : Submission.ASP.FIgtil (e*b*d) = Submission.ASP.FIgtil ((b*e)*d) := by
      rw [Nat.mul_comm e b]
    rw [hρ, hg]
    ring
  rw [h2]
  ring

/-! ## 3. Interchanging the sums and collapsing the window -/

/-- The triple sum with an `if`-window over the middle index can be interchanged with the
two inner sums and the window summed over directly, since the window sits inside `s`. -/
private lemma sum_comm_filter_window (s t D : Finset ℕ) (W : ℕ → Finset ℕ) (g : ℕ → ℕ → ℕ → ℝ)
    (hsub : ∀ e, W e ⊆ s) :
    (∑ b ∈ s, ∑ e ∈ t, ∑ d ∈ D, (if b ∈ W e then g b e d else 0))
      = ∑ e ∈ t, ∑ d ∈ D, ∑ b ∈ W e, g b e d := by
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_ite_mem]
  apply Finset.sum_congr
  · rw [Finset.inter_eq_right.mpr (hsub e)]
  · intro b _
    rfl

/-! ## 4. The identity -/

lemma sum_T_eq_levelSum (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ)
    (hn : n ∈ Finset.Icc 1 x) :
    ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b : ℕ) : ℝ)),
        (ArithmeticFunction.moebius b : ℝ) * ∑ e ∈ Finset.Icc 1 x, Work.FIChain.s3MPT lam x z sz Cm n b e u
      = (1 / u) * Work.FIChain.s3MPLevelSum lam x z sz Cm sy n u := by
  have hnx : n ≤ x := (Finset.mem_Icc.mp hn).2
  -- the `(b,e)`-sum is the triple `(b,e,d)`-sum of the window-supported summand
  have hL :
      (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b:ℕ):ℝ)),
          (ArithmeticFunction.moebius b : ℝ) * ∑ e ∈ Finset.Icc 1 x,
            s3MPT lam x z sz Cm n b e u)
      = ∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b:ℕ):ℝ)),
          ∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
            (if b ∈ s3LevelWindow x z sz Cm sy n u e then
              (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
                * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)) else 0) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact s3MPT_mul_eq lam x z sz Cm sy n u b e hb hnx
  -- interchange and collapse
  have hM :
      (∑ b ∈ (Finset.Icc 1 x).filter (fun b => sy < ((b:ℕ):ℝ)),
          ∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
            (if b ∈ s3LevelWindow x z sz Cm sy n u e then
              (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
                * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)) else 0))
      = ∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
          ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
            (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)) :=
    sum_comm_filter_window ((Finset.Icc 1 x).filter (fun b => sy < ((b:ℕ):ℝ)))
      (Finset.Icc 1 x) (Finset.Icc 1 ⌊u⌋₊) (fun e => s3LevelWindow x z sz Cm sy n u e)
      (fun b e d => (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
        * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)))
      (fun e b hb => Finset.mem_filter.mpr
        ⟨s3LevelWindow_subset x z sz Cm sy n u e hb, (mem_s3LevelWindow.mp hb).2.2.1⟩)
  -- the level sum pulls the `1/u` out
  have hR :
      (1/u) * s3MPLevelSum lam x z sz Cm sy n u
      = ∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
          ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
            (1/u) * ((ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e*b)
              * (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e*b*d)) := by
    rw [s3MPLevelSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  rw [hR]
  rw [← hM]
  exact hL

end

end Work.FIChain
