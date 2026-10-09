import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

namespace Commons.Analysis.TSum

open scoped BigOperators

/-- `(Fin (n+1) → ℕ) ≃ ℕ × (Fin n → ℕ)`, splitting off the value at `0`. -/
private def finSuccPiEquiv (n : ℕ) : (Fin (n + 1) → ℕ) ≃ ℕ × (Fin n → ℕ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    refine Prod.ext ?_ ?_
    · exact Fin.cons_zero (α := fun _ : Fin (n + 1) => ℕ) p.1 p.2
    · funext i; exact Fin.cons_succ (α := fun _ : Fin (n + 1) => ℕ) p.1 p.2 i

@[simp] private lemma finSuccPiEquiv_symm_apply (n : ℕ) (p : ℕ × (Fin n → ℕ)) :
    (finSuccPiEquiv n).symm p = Fin.cons p.1 p.2 := rfl

/-- Summability of a product of nonnegative summable series over a finite product. -/
private lemma summable_pi_prod_of_nonneg (n : ℕ) (u : Fin n → ℕ → ℝ)
    (h0 : ∀ j m, 0 ≤ u j m) (h : ∀ j, Summable (u j)) :
    Summable (fun σ : Fin n → ℕ => ∏ j, u j (σ j)) := by
  induction n with
  | zero =>
    have hfun : (fun σ : Fin 0 → ℕ => ∏ j, u j (σ j)) = fun _ => (1 : ℝ) := by
      funext σ; exact Fin.prod_univ_zero _
    rw [hfun]
    exact Summable.of_finite
  | succ n ih =>
    have htail : Summable (fun τ : Fin n → ℕ => ∏ i, u i.succ (τ i)) :=
      ih (fun i => u i.succ) (fun i m => h0 i.succ m) (fun i => h i.succ)
    have hmain : Summable
        (fun p : ℕ × (Fin n → ℕ) => u 0 p.1 * ∏ i, u i.succ (p.2 i)) :=
      Summable.mul_of_nonneg (h 0) htail (fun m => h0 0 m)
        (fun τ => Finset.prod_nonneg (fun i _ => h0 i.succ (τ i)))
    have hcongr : ((fun σ : Fin (n + 1) → ℕ => ∏ j, u j (σ j)) ∘ (finSuccPiEquiv n).symm)
        = fun p : ℕ × (Fin n → ℕ) => u 0 p.1 * ∏ i, u i.succ (p.2 i) := by
      funext p
      simp only [Function.comp_apply, finSuccPiEquiv_symm_apply]
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hcongr] at hmain
    exact (Equiv.summable_iff (finSuccPiEquiv n).symm).mp hmain

private lemma tsum_one_fin_zero : (∑' _ : Fin 0 → ℕ, (1 : ℂ)) = 1 :=
  tsum_eq_single (default : Fin 0 → ℕ)
    (fun b hb => absurd (Subsingleton.elim b (default : Fin 0 → ℕ)) hb)

/-- The main computation for `Fin n`. -/
private lemma tsum_pi_prod_fin (n : ℕ) (a : Fin n → ℕ → ℂ) (h : ∀ j, Summable (a j)) :
    (∑' σ : Fin n → ℕ, ∏ j, a j (σ j)) = ∏ j, ∑' m, a j m := by
  induction n with
  | zero =>
    have hfun : (fun σ : Fin 0 → ℕ => ∏ j, a j (σ j)) = fun _ => (1 : ℂ) := by
      funext σ; exact Fin.prod_univ_zero _
    rw [hfun, Fin.prod_univ_zero]
    exact tsum_one_fin_zero
  | succ n ih =>
    set F : (Fin n → ℕ) → ℂ := fun τ => ∏ i, a i.succ (τ i) with hF
    have hnormF : Summable (fun τ : Fin n → ℕ => ‖F τ‖) := by
      have hG : Summable (fun τ : Fin n → ℕ => ∏ i, ‖a i.succ (τ i)‖) :=
        summable_pi_prod_of_nonneg n (fun i m => ‖a i.succ m‖)
          (fun i m => norm_nonneg _) (fun i => (h i.succ).norm)
      refine hG.of_nonneg_of_le (fun τ => norm_nonneg _) (fun τ => ?_)
      rw [hF]
      simp
    have hval : (∑' p : ℕ × (Fin n → ℕ), a 0 p.1 * F p.2)
        = (∑' m : ℕ, a 0 m) * (∑' τ, F τ) :=
      (tsum_mul_tsum_of_summable_norm (h 0).norm hnormF).symm
    have hcongr : ∀ p : ℕ × (Fin n → ℕ),
        (fun σ : Fin (n + 1) → ℕ => ∏ j, a j (σ j)) ((finSuccPiEquiv n).symm p)
          = a 0 p.1 * F p.2 := by
      intro p
      simp only [finSuccPiEquiv_symm_apply]
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, hF]
    calc
      (∑' σ : Fin (n + 1) → ℕ, ∏ j, a j (σ j))
          = ∑' p : ℕ × (Fin n → ℕ), a 0 p.1 * F p.2 := by
            rw [← Equiv.tsum_eq (finSuccPiEquiv n).symm
                  (fun σ : Fin (n + 1) → ℕ => ∏ j, a j (σ j))]
            exact tsum_congr hcongr
      _ = (∑' m : ℕ, a 0 m) * (∑' τ, F τ) := hval
      _ = (∑' m : ℕ, a 0 m) * (∏ i : Fin n, ∑' m, a i.succ m) := by
            simp only [hF]
            rw [ih (fun i => a i.succ) (fun i => h i.succ)]
      _ = ∏ j : Fin (n + 1), ∑' m, a j m := by
            rw [Fin.prod_univ_succ]

theorem tsum_prod_fintype {ι : Type*} [Fintype ι] (a : ι → ℕ → ℂ)
    (h : ∀ j, Summable (a j)) :
    (∑' σ : ι → ℕ, ∏ j, a j (σ j)) = ∏ j, ∑' n : ℕ, a j n := by
  classical
  set e := Fintype.equivFin ι with he
  set b : Fin (Fintype.card ι) → ℕ → ℂ := fun i => a (e.symm i) with hb
  have hb' : ∀ i, Summable (b i) := fun i => h (e.symm i)
  have key := tsum_pi_prod_fin (Fintype.card ι) b hb'
  have hL : (∑' σ : ι → ℕ, ∏ j, a j (σ j))
      = ∑' τ : Fin (Fintype.card ι) → ℕ, ∏ i, b i (τ i) := by
    rw [← Equiv.tsum_eq (Equiv.arrowCongr e (Equiv.refl ℕ))
          (fun τ : Fin (Fintype.card ι) → ℕ => ∏ i, b i (τ i))]
    refine tsum_congr (fun σ => ?_)
    simp only [hb, Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
    exact (Equiv.prod_comp e.symm (fun j => a j (σ j))).symm
  have hR : (∏ i : Fin (Fintype.card ι), ∑' m, b i m) = ∏ j : ι, ∑' n, a j n := by
    simpa only [hb] using (Equiv.prod_comp e.symm (fun j : ι => ∑' n, a j n))
  calc
    (∑' σ : ι → ℕ, ∏ j, a j (σ j))
        = ∑' τ : Fin (Fintype.card ι) → ℕ, ∏ i, b i (τ i) := hL
    _ = ∏ i : Fin (Fintype.card ι), ∑' m, b i m := key
    _ = ∏ j : ι, ∑' n, a j n := hR

end Commons.Analysis.TSum