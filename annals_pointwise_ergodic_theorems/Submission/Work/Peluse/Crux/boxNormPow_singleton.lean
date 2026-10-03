import Mathlib
import Submission.Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow
import Submission.Work.Peluse.BoxNorm.boxNormPow_shift

/-!
# The box norm in a single constant direction

For the "degenerate" family of sets `Q i = {c}` (all `t` directions equal to the singleton `{c}`),
the `2^t`-th power of Peluse's Gowers box norm collapses to an ordinary average of `‖g‖^{2^t}`:

`‖g‖^{2^t}_{□^t_{c,…,c}(S)} = (1/|S|) ∑_x ‖g x‖^{2^t}`.

The reason is that the cube term `∏_{ω} C^{|ω|} g (x + ω·h + (1-ω)·h')` has all its `2^t`
arguments equal to `x + t·c` (the shift tuples `h, h'` are forced to be the constant tuple `c`),
and `∏_{ω} C^{|ω|} z = ‖z‖^{2^t}` for every `z : ℂ` when `t ≥ 1` (`prod_star_weight` below).

The `x`-sum is then reindexed by the translation `x ↦ x + t·c` (`Equiv.addRight`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Crux

/-- `weight` as a sum of indicators. -/
private lemma weight_eq_sumC {t : ℕ} (ω : Fin t → Bool) :
    Work.Peluse.weight ω = ∑ i : Fin t, if ω i then 1 else 0 := by
  rw [Work.Peluse.weight, Finset.card_filter]

/-- `weight` splits off the first coordinate. -/
private lemma weight_consC {k : ℕ} (b : Bool) (τ : Fin k → Bool) :
    Work.Peluse.weight (Fin.cons b τ) = Work.Peluse.weight τ + (if b then 1 else 0) := by
  have h1 : Work.Peluse.weight (Fin.cons b τ)
      = ∑ i : Fin (k+1), if (Fin.cons b τ : Fin (k+1) → Bool) i then 1 else 0 :=
    weight_eq_sumC _
  have h2 : Work.Peluse.weight τ = ∑ i : Fin k, if τ i then 1 else 0 := weight_eq_sumC _
  rw [h1, h2, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact add_comm _ _

/-- Recursion for `∏_{ω} (star^[|ω|]) z` when one more coordinate is added. -/
private lemma prod_star_weight_succC (k : ℕ) (z : ℂ) :
    (∏ ω : Fin (k+1) → Bool, (star^[Work.Peluse.weight ω]) z)
      = (∏ τ : Fin k → Bool, (star^[Work.Peluse.weight τ]) z)
        * star (∏ τ : Fin k → Bool, (star^[Work.Peluse.weight τ]) z) := by
  rw [Work.Peluse.BoxNorm.Aux.prod_cons_equiv, Fintype.prod_bool, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [weight_consC, if_neg (by decide : ¬ ((false:Bool) = true)), Nat.add_zero]
  · rw [show (∏ τ : Fin k → Bool, (star^[Work.Peluse.weight (Fin.cons true τ)]) z)
        = ∏ τ : Fin k → Bool, star ((star^[Work.Peluse.weight τ]) z) from
      Finset.prod_congr rfl (fun τ _ => by
        rw [weight_consC, if_pos (by decide : ((true:Bool) = true)),
          Function.iterate_succ_apply'])]
    exact (star_prod Finset.univ (fun τ : Fin k → Bool => (star^[Work.Peluse.weight τ]) z)).symm

/-- **The product of the conjugated cube terms is `‖z‖^{2^t}`.**  For `t ≥ 1`,
`∏_{ω : Fin t → Bool} (star^[|ω|]) z = ‖z‖^{2^t}` (as a real number). -/
private lemma prod_star_weight_auxC (k : ℕ) (z : ℂ) :
    (∏ ω : Fin (k+1) → Bool, (star^[Work.Peluse.weight ω]) z)
      = ((‖z‖ ^ (2 ^ (k+1)) : ℝ) : ℂ) := by
  induction k with
  | zero =>
      rw [prod_star_weight_succC 0 z]
      have hP0 : (∏ τ : Fin 0 → Bool, (star^[Work.Peluse.weight τ]) z) = z := by
        simp [Work.Peluse.weight]
      rw [hP0]
      have h := Complex.mul_conj z
      simp only [Complex.normSq_eq_norm_sq] at h
      simpa using h
  | succ k ih =>
      rw [prod_star_weight_succC (k+1) z, ih]
      have hstar : star ((↑(‖z‖ ^ (2 ^ (k+1)) : ℝ)) : ℂ)
          = ((↑(‖z‖ ^ (2 ^ (k+1)) : ℝ)) : ℂ) := by
        rw [Complex.star_def, Complex.conj_ofReal]
      rw [hstar, ← Complex.ofReal_mul]
      congr 1
      rw [show (2:ℕ)^(k+1+1) = 2^(k+1) * 2 from Nat.pow_succ 2 (k+1), pow_mul]
      ring

private lemma prod_star_weightC (t : ℕ) (ht : 1 ≤ t) (z : ℂ) :
    (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω]) z) = ((‖z‖ ^ (2 ^ t) : ℝ) : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  exact prod_star_weight_auxC k z

theorem boxNormPow_singleton {t : ℕ} (ht : 1 ≤ t) (c : ℤ) (S : Finset ℤ) (g : ℤ → ℂ)
    (hg : Work.Peluse.FinSuppZ g) :
    Work.Peluse.boxNormPow t (fun _ : Fin t => ({c} : Finset ℤ)) S g
      = ((S.card : ℝ))⁻¹ * (∑' x : ℤ, ‖g x‖ ^ (2 ^ t)) := by
  have _ := hg
  let c0 : {x : ℤ // x ∈ ({c} : Finset ℤ)} := ⟨c, Finset.mem_singleton_self c⟩
  let h0 : (i : Fin t) → {x : ℤ // x ∈ ({c} : Finset ℤ)} := fun _ => c0
  have hsub : ∀ h : (i : Fin t) → {x : ℤ // x ∈ ({c} : Finset ℤ)}, h = h0 := by
    intro h
    funext i
    exact Subtype.ext (Finset.mem_singleton.mp (h i).2)
  have hcorner : ∀ ω : Fin t → Bool,
      Work.Peluse.cornerShift (fun i => (h0 i).1) (fun i => (h0 i).1) ω = (t:ℤ) * c := by
    intro ω
    rw [Work.Peluse.cornerShift]
    have hfun : (fun i : Fin t => if ω i then (h0 i).1 else (h0 i).1) = fun _ => c := by
      funext i; simp [h0, c0]
    rw [hfun]
    simp [Finset.sum_const, Finset.card_univ]
  have hcollapse : (∑ h : (i : Fin t) → {x : ℤ // x ∈ ({c} : Finset ℤ)},
        ∑ h' : (i : Fin t) → {x : ℤ // x ∈ ({c} : Finset ℤ)},
          ∑' x : ℤ, ∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (g (x + Work.Peluse.cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)))
      = ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω]) (g (x + (t:ℤ)*c)) := by
    rw [Finset.sum_eq_single h0 (fun b _ hb => absurd (hsub b) hb)
      (fun hc => absurd (Finset.mem_univ h0) hc)]
    rw [Finset.sum_eq_single h0 (fun b _ hb => absurd (hsub b) hb)
      (fun hc => absurd (Finset.mem_univ h0) hc)]
    refine tsum_congr fun x => ?_
    refine Finset.prod_congr rfl fun ω _ => ?_
    rw [hcorner ω]
  have hprod : (∏ i : Fin t, ((({c} : Finset ℤ).card : ℂ))⁻¹) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    simp
  have hbox1 : Work.Peluse.boxSumPow t (fun _ : Fin t => ({c} : Finset ℤ)) S g
      = (S.card:ℂ)⁻¹ * (∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[Work.Peluse.weight ω]) (g (x + (t:ℤ)*c))) := by
    simp only [Work.Peluse.boxSumPow, Work.Peluse.prodCubeSum, hprod, hcollapse]
    ring
  have hbox2 : Work.Peluse.boxSumPow t (fun _ : Fin t => ({c} : Finset ℤ)) S g
      = (S.card:ℂ)⁻¹ * (∑' x : ℤ, ((‖g (x + (t:ℤ)*c)‖ ^ (2^t) : ℝ) : ℂ)) := by
    rw [hbox1]
    congr 1
    exact tsum_congr fun x => prod_star_weightC t ht (g (x + (t:ℤ)*c))
  have hbox3 : Work.Peluse.boxSumPow t (fun _ : Fin t => ({c} : Finset ℤ)) S g
      = ((((S.card:ℝ)⁻¹) * ∑' x : ℤ, ‖g (x + (t:ℤ)*c)‖ ^ (2^t) : ℝ) : ℂ) := by
    rw [hbox2, ← Complex.ofReal_tsum]
    rw [show (S.card:ℂ) = ((S.card:ℝ):ℂ) from by simp,
      ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  have hrnn : 0 ≤ (S.card:ℝ)⁻¹ * ∑' x : ℤ, ‖g (x + (t:ℤ)*c)‖ ^ (2^t) :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (tsum_nonneg fun x => pow_nonneg (norm_nonneg _) _)
  rw [Work.Peluse.boxNormPow, hbox3, Complex.norm_of_nonneg hrnn]
  congr 1
  simpa [Equiv.coe_addRight] using
    Equiv.tsum_eq (Equiv.addRight ((t:ℤ)*c)) (fun y : ℤ => ‖g y‖ ^ (2^t))

end Work.Peluse.Crux
