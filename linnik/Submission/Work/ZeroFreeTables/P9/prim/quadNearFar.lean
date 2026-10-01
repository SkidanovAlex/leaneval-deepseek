import Mathlib
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.prim.quadFarBound
import Submission.Work.ZeroFreeTables.P9.prim.zeroMultReLtOne

namespace Work.ZeroFreeTables.P9.prim

open DirichletCharacter Complex
open scoped Classical BigOperators


/-- If the second-order zero sum `u ↦ M u · (1/(s-u))²` is summable, then so is the
inverse-square mass `u ↦ M u · 1/(1+‖s-u‖²)`: the two differ only at the single point `u = s`,
where the former vanishes, and elsewhere `1/(1+‖s-u‖²) ≤ ‖(1/(s-u))²‖`. -/
private lemma summable_invSq_of_summable {M : ℂ → ℕ} {s : ℂ}
    (hsum : Summable (fun u : ℂ => (M u : ℂ) * (1 / (s - u)) ^ 2)) :
    Summable (fun u : ℂ => (M u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) := by
  refine Summable.of_norm_bounded_eventually
    (f := fun u : ℂ => (M u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)))
    (g := fun u : ℂ => ‖(M u : ℂ) * (1 / (s - u)) ^ 2‖) hsum.norm ?_
  rw [Filter.eventually_cofinite]
  refine Set.Finite.subset (Set.finite_singleton s) ?_
  intro u hu
  rw [Set.mem_ofPred_eq] at hu
  rw [Set.mem_singleton_iff]
  by_contra hne
  exact hu (by
    have hr : 0 < ‖s - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have hle : (1 : ℝ) / (1 + ‖s - u‖ ^ 2) ≤ 1 / ‖s - u‖ ^ 2 := by
      apply one_div_le_one_div_of_le (pow_pos hr 2)
      nlinarith [sq_nonneg ‖s - u‖]
    have hnorm_eq : ‖(1 / (s - u)) ^ 2‖ = 1 / ‖s - u‖ ^ 2 := by
      rw [one_div, norm_pow, norm_inv, inv_pow, one_div]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, hnorm_eq, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _))

theorem quadNearFar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hs : 1 < s.re) (hsδ : s.re ≤ 1 + δ / 2) (hsum : Summable (fun u : ℂ => (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2)) : -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re ≤ -(∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 2).re) + (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s := by
  classical
  set F : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re with hFdef
  set G : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * Work.ZeroFreeTables.P9.nearInd s δ u * ((1 / (s - u)) ^ 2).re with hGdef
  set Q : ℂ → ℝ := fun u => (Work.LinnikContract.zeroMult χ u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2)) with hQdef
  -- F is the real part of the summable complex family
  have hcongr : (fun u : ℂ => ((Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re) = F := by
    funext u
    rw [hFdef]
    show ((Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re
        = (Work.LinnikContract.zeroMult χ u : ℝ) * ((1 / (s - u)) ^ 2).re
    rw [show (Work.LinnikContract.zeroMult χ u : ℂ)
          = ((Work.LinnikContract.zeroMult χ u : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.re_ofReal_mul]
  have hF : Summable F := by
    have h := Complex.hasSum_re hsum.hasSum
    rw [hcongr] at h
    exact h.summable
  -- G is F weighted by a `[0,1]`-valued indicator, hence summable
  have hG : Summable G := by
    refine Summable.of_norm_bounded (f := G) (g := fun u => ‖F u‖) hF.norm ?_
    intro u
    have hGFeq : G u = Work.ZeroFreeTables.P9.nearInd s δ u * F u := by
      rw [hGdef, hFdef]; ring
    rw [hGFeq, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Work.ZeroFreeTables.P9.nearInd_nonneg s δ u), Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (Work.ZeroFreeTables.P9.nearInd_le_one s δ u)
  have hQ : Summable Q := by
    have h := summable_invSq_of_summable (M := fun u : ℂ => Work.LinnikContract.zeroMult χ u) hsum
    simpa only [hQdef] using h
  -- pointwise comparison
  have hpt : ∀ u : ℂ, 0 ≤ F u - G u + (1 + 4 / δ ^ 2) * Q u := by
    intro u
    have hMnn : (0 : ℝ) ≤ (Work.LinnikContract.zeroMult χ u : ℝ) := by positivity
    by_cases hM : Work.LinnikContract.zeroMult χ u = 0
    · simp [F, G, Q, hM]
    · have hMpos : (0 : ℝ) < (Work.LinnikContract.zeroMult χ u : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hM
      by_cases hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ
      · have : 0 ≤ (1 + 4 / δ ^ 2) * ((Work.LinnikContract.zeroMult χ u : ℝ)
            * (1 / (1 + ‖s - u‖ ^ 2))) := by positivity
        simp only [F, G, Q, Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hnear]
        nlinarith [this]
      · have hfar : δ < ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ := not_le.mp hnear
        have hu : u.re < 1 := zeroMultReLtOne χ hχ hprim hM
        have hb := quadFarBound hδ hs hu hfar
        have hge : 0 ≤ ((1 / (s - u)) ^ 2).re
            + (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2)) := by
          rw [mul_one_div]
          linarith [hb]
        have hstep : 0 ≤ (Work.LinnikContract.zeroMult χ u : ℝ)
            * (((1 / (s - u)) ^ 2).re + (1 + 4 / δ ^ 2) * (1 / (1 + ‖s - u‖ ^ 2))) :=
          mul_nonneg hMpos.le hge
        simp only [F, G, Q, Work.ZeroFreeTables.P9.nearInd_eq_ite, if_neg hnear]
        nlinarith [hstep]
  -- sum the pointwise bound
  have hS3 : Summable (fun u : ℂ => F u - G u + (1 + 4 / δ ^ 2) * Q u) :=
    (hF.sub hG).add (hQ.mul_left (1 + 4 / δ ^ 2))
  have hnn : 0 ≤ ∑' u : ℂ, (F u - G u + (1 + 4 / δ ^ 2) * Q u) :=
    tsum_nonneg (fun u => hpt u)
  have hsplit : ∑' u : ℂ, (F u - G u + (1 + 4 / δ ^ 2) * Q u)
      = (∑' u : ℂ, F u) - (∑' u : ℂ, G u) + (1 + 4 / δ ^ 2) * (∑' u : ℂ, Q u) := by
    rw [Summable.tsum_add (f := fun u : ℂ => F u - G u)
          (g := fun u : ℂ => (1 + 4 / δ ^ 2) * Q u) (hF.sub hG) (hQ.mul_left (1 + 4 / δ ^ 2)),
        Summable.tsum_sub (f := F) (g := G) hF hG,
        Summable.tsum_mul_left (1 + 4 / δ ^ 2) hQ]
  rw [hsplit] at hnn
  -- identify the goal's three sums
  have hre : (∑' u : ℂ, (Work.LinnikContract.zeroMult χ u : ℂ) * (1 / (s - u)) ^ 2).re
      = ∑' u : ℂ, F u := by
    rw [Complex.re_tsum hsum, hcongr]
  have hQts : Work.ZeroFreeTables.P9.invSqSum N χ s = ∑' u : ℂ, Q u := by
    rw [hQdef, Work.ZeroFreeTables.P9.invSqSum]
  rw [hre, hQts]
  linarith [hnn]

end Work.ZeroFreeTables.P9.prim
