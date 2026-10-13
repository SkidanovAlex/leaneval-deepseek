import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.HkMem_of_plain_slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The sharp (`sin(2θ)^{2r-γ}`) domination of a mixed slot by the plain slots

The sibling `Work.FTS.ClassC.plainSlot_domination` bounds the mixed slot `D_z^j D_θ^i f` by the
plain slots `D_z^j ∂_θ^r f` `(1 ≤ r ≤ i)` with the *fixed* conormal weight
`sin(2θ)^{-η}`.  This cannot be sharpened to the weight `sin(2θ)^{2r-γ}`: the coefficient `a_{i,r}`
of `∂_θ^r f` in `D_θ^i f` carries exactly `sin(2θ)^r`, so the mixed slot really vanishes like
`sin(2θ)^i` at the angular endpoints, and the corresponding square summand
`(D_z^j ∂_θ^r f)² w² sin(2θ)^{2r-γ}` is *much* smaller near `θ = 0, π/2` than the `η`-version.

The proof below keeps the sharp power `sin(2θ)^r` all the way: from the exact expansion
`D_z^j D_θ^i f = Σ_r a_{i,r}(θ) D_z^j ∂_θ^r f` and the divisibility bound
`|a_{i,r}(θ)| ≤ K_r sin(2θ)^r` we get
`|D_z^j D_θ^i f · W| ≤ Σ_r K_r · (|D_z^j ∂_θ^r f| · w · sin(2θ)^{r-γ/2})`,
and one Cauchy–Schwarz (with the *unfixed* factors `K_r`) produces exactly the claimed sum
`Σ_r (D_z^j ∂_θ^r f)² w² sin(2θ)^{2r-γ}`. -/

/-- `sin (2θ)` is non-negative on `Iθ`. -/
private theorem sin_two_nonneg_on_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2]
  exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2

/-- **The Cauchy–Schwarz step in its sharp form.**  For `t > 0`, a finite index set `s ⊆ ℕ` and
arbitrary factors `Kc r`, `A r`,

`(Σ_{r∈s} Kc r · (A r · t^{r-γ/2}))² ≤ (Σ_{r∈s} Kc r²) · Σ_{r∈s} (A r)² · t^{2r-γ}`,

using `t^{r-γ/2} · t^{r-γ/2} = t^{2r-γ}`.  Keeping the factors `Kc r` inside the Cauchy–Schwarz
sum (rather than majorising them by a single constant) is what allows the sharp conormal power
`t^{2r-γ}` on the right. -/
private theorem sum_sq_le_rpow_of_abs {s : Finset ℕ} {Kc A : ℕ → ℝ} {t γ : ℝ} (ht : 0 < t) :
    (∑ r ∈ s, Kc r * (A r * t ^ ((r : ℝ) - γ / 2))) ^ 2
      ≤ (∑ r ∈ s, (Kc r) ^ 2) * ∑ r ∈ s, (A r) ^ 2 * t ^ (2 * (r : ℝ) - γ) := by
  have hpow : ∀ r : ℕ, (A r * t ^ ((r : ℝ) - γ / 2)) ^ 2
      = (A r) ^ 2 * t ^ (2 * (r : ℝ) - γ) := by
    intro r
    have hexp : ((r : ℝ) - γ / 2) + ((r : ℝ) - γ / 2) = 2 * (r : ℝ) - γ := by ring
    have h2 : (t ^ ((r : ℝ) - γ / 2)) ^ 2 = t ^ (2 * (r : ℝ) - γ) := by
      rw [sq, ← Real.rpow_add ht, hexp]
    rw [mul_pow, h2]
  calc (∑ r ∈ s, Kc r * (A r * t ^ ((r : ℝ) - γ / 2))) ^ 2
      ≤ (∑ r ∈ s, (Kc r) ^ 2) * ∑ r ∈ s, (A r * t ^ ((r : ℝ) - γ / 2)) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq s Kc (fun r => A r * t ^ ((r : ℝ) - γ / 2))
    _ = (∑ r ∈ s, (Kc r) ^ 2) * ∑ r ∈ s, (A r) ^ 2 * t ^ (2 * (r : ℝ) - γ) := by
        rw [Finset.sum_congr rfl (fun r _ => hpow r)]

theorem mixedSlot_vanishing_weight_domination {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ C * ∑ r ∈ Finset.Icc 1 i,
            (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  classical
  -- the divisibility bounds for the angular coefficients
  have hcoef : ∀ r : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ θ : ℝ,
      |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
        ≤ K * |Real.sin (2 * θ)| ^ r :=
    fun r => Work.FTS.EllipticEst.remov.selfdth.DthCoef_sin_pow_bound (m + 1) r
  let Kc : ℕ → ℝ := fun r => Classical.choose (hcoef r)
  have hKcpos : ∀ r : ℕ, 0 < Kc r := fun r => (Classical.choose_spec (hcoef r)).1
  have hKcle : ∀ (r : ℕ) (θ : ℝ),
      |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
        ≤ Kc r * |Real.sin (2 * θ)| ^ r := fun r θ => (Classical.choose_spec (hcoef r)).2 θ
  refine ⟨∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2, ?_, ?_⟩
  · exact Finset.sum_pos' (fun r _ => sq_nonneg _)
      ⟨1, by simp [Finset.mem_Icc], pow_pos (hKcpos 1) 2⟩
  · intro z hz θ hθ
    have hw_nonneg : 0 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w]
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    by_cases hW : Work.Spaces.Wt α z θ = 0
    · -- the weight vanishes: both sides vanish
      have hzero : (Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2 = 0 := by
        rw [hW, mul_zero]
        simp
      rw [hzero]
      refine mul_nonneg (Finset.sum_nonneg fun r _ => sq_nonneg _) ?_
      refine Finset.sum_nonneg fun r _ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Real.rpow_nonneg (sin_two_nonneg_on_Iθ hθ) _)
    · obtain ⟨hzpos, hθ0, hθ1⟩ := Wt_ne_zero_quadrant hα hz hθ hW
      have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      have hsinabs : |Real.sin (2 * θ)| = Real.sin (2 * θ) := abs_of_pos hs
      -- the exact expansion of the mixed slot in the plain slots
      have hexp := mixed_eq_sum_dthCoef_succ hsm m j z θ hzpos hθ0 hθ1
      have hD_bound : |Work.Spaces.mixed j (m + 1) f z θ|
          ≤ ∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := by
        rw [hexp]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun r _ => ?_)
        calc |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ
              * Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
            = |Work.FTS.EllipticEst.remov.selfdth.dthCoef (m + 1) r θ|
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := abs_mul _ _
          _ ≤ (Kc r * |Real.sin (2 * θ)| ^ r)
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| :=
              mul_le_mul_of_nonneg_right (hKcle r θ) (abs_nonneg _)
          _ = Kc r * (Real.sin (2 * θ)) ^ r
              * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| := by rw [hsinabs]
      have hWt_abs : |Work.Spaces.Wt α z θ|
          = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
        rw [Work.Spaces.Wt, Work.Spaces.wTheta, abs_mul,
          abs_of_nonneg (le_of_lt (Real.rpow_pos_of_pos hs (-(Work.Spaces.gam α / 2)))),
          abs_of_nonneg hw_nonneg]
      -- the sharp power identity `t^r · t^{-γ/2} = t^{r-γ/2}`
      have hrpow_mul : ∀ r : ℕ,
          (Real.sin (2 * θ)) ^ r * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))
            = (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2) := by
        intro r
        have hexp : (r : ℝ) + (-(Work.Spaces.gam α / 2)) = (r : ℝ) - Work.Spaces.gam α / 2 := by
          ring
        rw [← Real.rpow_natCast (Real.sin (2 * θ)) r, ← Real.rpow_add hs, hexp]
      -- the sharp domination, with the `sin(2θ)^r` kept inside
      have key : |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ|
          ≤ ∑ r ∈ Finset.Icc 1 (m + 1),
              Kc r * ((|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z)
                * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2)) := by
        calc |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ|
            = |Work.Spaces.mixed j (m + 1) f z θ| * |Work.Spaces.Wt α z θ| := abs_mul _ _
          _ = |Work.Spaces.mixed j (m + 1) f z θ|
                * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by
              rw [hWt_abs]
          _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|)
              * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
              mul_le_mul_of_nonneg_right hD_bound
                (mul_nonneg hw_nonneg
                  (le_of_lt (Real.rpow_pos_of_pos hs (-(Work.Spaces.gam α / 2)))))
          _ = ∑ r ∈ Finset.Icc 1 (m + 1), Kc r * (Real.sin (2 * θ)) ^ r
                * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) :=
              Finset.sum_mul _ _ _
          _ = ∑ r ∈ Finset.Icc 1 (m + 1),
              Kc r * (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z
                * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2)) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              calc Kc r * (Real.sin (2 * θ)) ^ r
                    * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                    * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)))
                  = Kc r * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                    * Work.Spaces.w z
                    * ((Real.sin (2 * θ)) ^ r
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := by ring
                _ = Kc r * |Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ|
                    * Work.Spaces.w z
                    * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2) := by
                    rw [hrpow_mul r]
                _ = Kc r * (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z
                    * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2)) := by ring
      -- assembly: square, Cauchy–Schwarz, and read off the sharp weights
      calc (Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2
          = |Work.Spaces.mixed j (m + 1) f z θ * Work.Spaces.Wt α z θ| ^ 2 := by rw [sq_abs]
        _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1),
              Kc r * ((|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z)
                * (Real.sin (2 * θ)) ^ ((r : ℝ) - Work.Spaces.gam α / 2))) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) key 2
        _ ≤ (∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2)
              * ∑ r ∈ Finset.Icc 1 (m + 1),
                  (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
            sum_sq_le_rpow_of_abs (s := Finset.Icc 1 (m + 1)) hs
        _ = (∑ r ∈ Finset.Icc 1 (m + 1), (Kc r) ^ 2)
              * ∑ r ∈ Finset.Icc 1 (m + 1),
                  (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2
                    * (Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) := by
            have hfin : (∑ r ∈ Finset.Icc 1 (m + 1),
                  (|Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ| * Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
                = ∑ r ∈ Finset.Icc 1 (m + 1),
                  (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2
                    * (Work.Spaces.w z) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) :=
              Finset.sum_congr rfl fun r _ => by rw [mul_pow, sq_abs]
            rw [hfin]

end Work.FTS.ClassC
