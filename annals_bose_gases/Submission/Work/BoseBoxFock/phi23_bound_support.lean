import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KsubStateAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.phi23_bound_support` — boundedness and box support of the block II.2 fibre

The fibre `phi23 p Θ A B` of `KsubStateAux` is the inner double integral of the block II.2 shape,

    phi23 p Θ A B x = ∫_y ∫_u star (Θ x) * star (A y) * star (B u)
                        * Θ (update (update x p.1 y) p.2 u) ,

i.e. the two free variables `y`, `u` are substituted into the slots `p.1`, `p.2` of the
configuration `x`.  The present file supplies the two facts the state-level step (S2) needs about
it (the analogue of `pairG_supports` for this fibre):

* **boundedness**: `∃ C, ∀ x, ‖phi23 p Θ A B x‖ ≤ C`;
* **support**: `support (phi23 p Θ A B) ⊆ boxPow n ℓ`.

Both are consequences of the *state* hypotheses (`Θ` everywhere bounded and supported in the
`n`-particle box) *alone*:

* the integrand carries the constant factor `star (Θ x)`, so `phi23 p Θ A B x = 0` as soon as
  `Θ x = 0`, i.e. for `x ∉ boxPow n ℓ` (this is the support statement, and it is purely pointwise:
  the integrand vanishes identically, so the iterated integral is `0`);
* for the bound, `Θ (update (update x p.1 y) p.2 u) = 0` whenever `y ∉ boxL ℓ` (the coordinate
  `p.1` of the updated configuration is `y`) or `u ∉ boxL ℓ` (`p.2 ↦ u`), so the integrand is
  supported in the box squared, which has finite measure; the pointwise bound
  `C_Θ · C_A · C_B · C_Θ` then gives the uniform bound `C_Θ² C_A C_B vol(boxL ℓ)²` through
  `norm_doubleIntegral_le` (no measurability or a.e. information about `Θ` is needed).

Everything here is `sorry`-free.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem phi23_bound_support {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C) :
    (∃ C : ℝ, ∀ x, ‖Work.BoseBoxFock.phi23 p Θ A B x‖ ≤ C)
      ∧ Function.support (Work.BoseBoxFock.phi23 p Θ A B) ⊆ Work.MB.boxPow n ℓ := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨CA, hCA⟩ := hAb
  obtain ⟨CB, hCB⟩ := hBb
  have hvol : volume (Work.BoseK15.corpusBox.boxL ℓ) < (⊤ : ENNReal) :=
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top
  have hbdd : ∃ C : ℝ, ∀ x, ‖phi23 p Θ A B x‖ ≤ C := by
    refine ⟨max 0 (max CΘ 0 * max CA 0 * max CB 0 * max CΘ 0
      * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal
      * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal), fun x => ?_⟩
    have hpt : ∀ y u : E3, ‖star (Θ x) * star (A y) * star (B u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)‖
        ≤ max CΘ 0 * max CA 0 * max CB 0 * max CΘ 0 := by
      intro y u
      rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star, norm_star]
      gcongr
      · exact le_trans (hCΘ x) (le_max_left _ _)
      · exact le_trans (hCA y) (le_max_left _ _)
      · exact le_trans (hCB u) (le_max_left _ _)
      · exact le_trans (hCΘ _) (le_max_left _ _)
    have hv1 : ∀ y : E3, y ∉ Work.BoseK15.corpusBox.boxL ℓ → ∀ u : E3,
        star (Θ x) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
      intro y hy u
      have hz : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.1)
          (by rw [Function.update_apply, if_neg hp, Function.update_self]; exact hy)
      rw [hz, mul_zero]
    have hv2 : ∀ y u : E3, u ∉ Work.BoseK15.corpusBox.boxL ℓ →
        star (Θ x) * star (A y) * star (B u)
          * Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 := by
      intro y u hu
      have hz : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.2)
          (by rw [Function.update_apply, if_pos rfl]; exact hu)
      rw [hz, mul_zero]
    have hmain := norm_doubleIntegral_le (F := fun y u : E3 =>
      star (Θ x) * star (A y) * star (B u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)) hvol hpt hv1 hv2
    have hbound : ‖phi23 p Θ A B x‖ ≤ max CΘ 0 * max CA 0 * max CB 0 * max CΘ 0
        * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal
        * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
      rw [phi23]
      exact hmain
    exact le_trans hbound (le_max_right _ _)
  have hsupp : Function.support (phi23 p Θ A B) ⊆ Work.MB.boxPow n ℓ := by
    intro x hx
    by_contra hxnot
    have hΘ0 : Θ x = 0 := by
      by_contra hz
      exact hxnot (hΘs (Function.mem_support.mpr hz))
    have hfun : (fun y : E3 => ∫ u : E3, star (Θ x) * star (A y) * star (B u)
        * Θ (Function.update (Function.update x p.1 y) p.2 u)) = fun _ => (0 : ℂ) := by
      funext y
      simp only [hΘ0, star_zero, zero_mul, integral_zero]
    have hzero : phi23 p Θ A B x = 0 := by
      rw [phi23]
      simp only [hfun, integral_zero]
    exact (Function.mem_support.mp hx) hzero
  exact ⟨hbdd, hsupp⟩

end Work.BoseBoxFock
