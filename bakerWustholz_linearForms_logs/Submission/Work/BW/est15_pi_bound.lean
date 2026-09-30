import Mathlib
import Submission.Work.BW.est15defs
import Submission.Work.BW.log_prod_Delta_le
import Submission.Work.BW.sum_gamInt_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Casting `piRat` to `ℂ` gives the product of the `Δ`-factors at the complex arguments
`γ_m(λ) = gam b k L (ι m) λ`, `λ_j = (lm.2.2 j : ℕ)`. -/
lemma piRat_cast_complex {n r : ℕ} (b : Fin n → ℤ) (k : Fin n) (L : Fin r → Fin n → ℤ)
    (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (t : Fin (r - 1) → ℕ)
    (lm : AuxIdx r h D0 Dj) :
    ((piRat b k L ι h D0 Dj t lm : ℚ) : ℂ) =
      ∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m) := by
  rw [piRat, Rat.cast_prod]
  exact Finset.prod_congr rfl fun m _ => by
    rw [← Delta_eq_deltaRat, gamInt_cast]

/-- At an arbitrary infinite place `w`, the absolute value of `piRat` is the complex norm of the
corresponding product of `Δ`-factors: `w ((q : ℚ) : K) = ‖(q : ℂ)‖` for rational `q`. -/
lemma infinitePlace_piRat {K : Type*} [Field K] [NumberField K] {n r : ℕ} (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ)
    (Dj : Fin r → ℕ) (t : Fin (r - 1) → ℕ) (lm : AuxIdx r h D0 Dj)
    (w : NumberField.InfinitePlace K) :
    w (((piRat b k L ι h D0 Dj t lm : ℚ) : K)) =
      ‖∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)‖ := by
  rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.apply, map_ratCast,
    piRat_cast_complex]

/-- `∑_m ‖gam b k L (ι m) λ‖ ≤ gamBound K b v σ` under the hypotheses: `sum_gamInt_le` with
`‖gam …‖ = |gamInt …|`. -/
lemma sum_norm_gam_le {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    ∑ m : Fin (r - 1), ‖gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))‖ ≤ gamBound K b v σ := by
  simpa only [Complex.norm_intCast, ← gamInt_cast] using sum_gamInt_le H lm

/-- The `Π`-factor of `coefPart` at an (arbitrary) infinite place `w`: `log |Π(t)|_w ≤ T'·(1 + log(1 + Λ/T'))` with `T' = ∑_m t_m` and `Λ = gamBound K b v σ`. Since `w ((q : ℚ) : K) = ‖q‖` for `q : ℚ` (`InfinitePlace.map_ratCast`) and `‖(q : ℂ)‖ = ‖q‖` (`Complex.norm_ratCast`), this is `Work.BW.log_prod_Delta_le` applied to `x m = gam b k L (ι m) λ` together with `Work.BW.sum_gamInt_le` (`∑_m ‖gam …‖ = ∑_m |gamInt …| ≤ Λ`) and monotonicity of `log`. For `T' = 0` both sides vanish. -/
theorem est15_pi_bound {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (t : Fin (r - 1) → ℕ)
    (w : NumberField.InfinitePlace K)
    (lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :
    Real.log (w (((piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm : ℚ) : K)))
      ≤ estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)) := by
  have hw := infinitePlace_piRat b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) t lm w
  have hS := sum_norm_gam_le (K := K) (b := b) (v := v) (σ := σ) H lm
  have hmain := log_prod_Delta_le
    (fun m : Fin (r - 1) => gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) t
  rw [hw]
  have hTnn : 0 ≤ estTp t :=
    Finset.sum_nonneg fun m _ => Nat.cast_nonneg _
  have hSnn : 0 ≤ ∑ m : Fin (r - 1), ‖gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))‖ :=
    Finset.sum_nonneg fun m _ => norm_nonneg _
  rcases eq_or_lt_of_le hTnn with hT0 | hTpos
  · rw [show estTp t = 0 from hT0.symm, zero_mul]
    rw [show (∑ m : Fin (r - 1), (t m : ℝ)) = 0 from hT0.symm] at hmain
    simpa using hmain
  · have h1 : 1 + (∑ m : Fin (r - 1), ‖gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))‖) / estTp t
        ≤ 1 + gamBound K b v σ / estTp t := by
      have h := div_le_div_of_nonneg_right hS hTpos.le
      linarith
    have h2 : Real.log (1 + (∑ m : Fin (r - 1), ‖gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))‖) / estTp t)
        ≤ Real.log (1 + gamBound K b v σ / estTp t) := by
      apply Real.log_le_log
      · have : 0 ≤ (∑ m : Fin (r - 1), ‖gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))‖) / estTp t :=
          div_nonneg hSnn hTpos.le
        linarith
      · exact h1
    calc Real.log ‖∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)‖
        ≤ estTp t * (1 + Real.log (1 + (∑ m : Fin (r - 1), ‖gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))‖) / estTp t)) := by
          simpa only [estTp] using hmain
      _ ≤ estTp t * (1 + Real.log (1 + gamBound K b v σ / estTp t)) :=
          mul_le_mul_of_nonneg_left (by linarith) hTpos.le

end Work.BW
