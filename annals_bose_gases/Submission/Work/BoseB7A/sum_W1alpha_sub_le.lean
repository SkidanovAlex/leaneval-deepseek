import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7A.abs_W1_mul_alpha_sub_le
import Submission.Work.BoseB7A.sum_W1sq_shift_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7A.sum_W1alpha_sub_le`

The **shifted** companion of `Work.BoseB7A.sum_W1alpha_le`: over the high-momentum
region `P_H` (`F.PHset E`, the modes `k` with `‖k‖ ≥ ½K_H⁻¹a⁻¹`),

`Σ_{k∈P_H} |Ŵ₁(k)·α_{s−k}| ≤ 5ρ_z a K₀ ℓ³`   for every `s` with `f_L(s) ≠ 0`.

This is the sum that the `Q₃⁽²⁾`/`Q₃⁽³⁾` part of `lem:EstimatesOnQ3-js` needs: the
squeezing parameter is evaluated at the *shifted* momentum `s − k`, because the
squeezed mode `b_{s−k}` is the one that carries the `ξ_{sk}` off-diagonal pairing
(so the `α_{s−k}` of `Q3twoT`/`Q3threeT` cannot be replaced by `α_k`).

## The proof

Two ingredients (both proved in this directory and imported here):

* `Work.BoseB7A.abs_W1_mul_alpha_sub_le` — the pointwise bound

  `|Ŵ₁(k)α_{s−k}| ≤ 2ρ_z( Ŵ₁(k)²/‖k‖² + Ŵ₁(s−k)²/‖s−k‖² )`  (`k ∈ P_H`),

  whose only non-obvious input is the scale separation `‖k‖ ≤ 2‖s−k‖`: on `P_H`
  one has `‖k‖ ≥ ½K_H⁻¹a⁻¹` while `‖s‖ ≤ K_L√(μa) ≤ ¼K_H⁻¹a⁻¹`, so
  `‖s−k‖ ≥ ‖k‖ − ‖s‖ ≥ ‖k‖/2`; together with `|α_q| ≤ 2ρ_z|Ŵ₁(q)|/‖q‖²`
  (`abs_alphaCoef_le` + `𝒜_q ≥ ‖q‖²/2` on the quarter region `P_H^q`) and
  AM–GM, `|u||v| ≤ u²/4 + v²` gives the bound.

* `Work.BoseB7A.sum_W1sq_shift_le` — the reindexed lattice sum

  `Σ_{k∈P_H} Ŵ₁(s−k)²/‖s−k‖² ≤ ℓ³K₀a`,

  which is `Q3Kernel.sum_W1sq` (the field `ℓ⁻³Σ_{P_H^q}Ŵ₁²/‖q‖² ≤ K₀a`) pushed
  along the injection `k ↦ s − k`, whose image lies in the quarter region `P_H^q`
  (`PH_subset_PHq_sub.sub_mem_PHq`).

Summing the pointwise bound and splitting the sum gives

`Σ_{P_H}|Ŵ₁(k)α_{s−k}| ≤ 2ρ_z( ℓ³K₀a + ℓ³K₀a ) = 4ρ_zK₀aℓ³ ≤ 5ρ_z a K₀ℓ³`.

The diluteness threshold `t₀ = (1/4)²⁴` is exactly the one that makes the scale
separation `K_L√(μa) ≤ ¼K_H⁻¹a⁻¹` hold (`PH_subset_PHq_sub.ratio_small`); the
hypothesis `b₀ ≤ E.b` is not used by this estimate (as in `sum_W1alpha_le`).
-/

set_option linter.unusedVariables false

namespace Work.BoseB7A

open Work.BoseB7

/-- The unshifted `P_H` lattice sum of `Ŵ₁(k)²/‖k‖²` is `≤ ℓ³K₀a`: the field
`Q3Kernel.sum_W1sq` (stated on the larger quarter region `P_H^q ⊇ P_H`),
multiplied by `ℓ³ > 0`. -/
private lemma sum_W1sq_le (K₀ : ℝ)
    {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : FockData Mode) (T : TildeData F)
    (E : Q3Env Mode) (hv : FSParamsView E)
    (hK : Q3Kernel K₀ F T E) :
    ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 ≤ E.ell ^ 3 * (K₀ * E.aScat) := by
  have hell3 : 0 ≤ E.ell ^ 3 := (pow_pos (ell_pos E hv) 3).le
  have hsub : F.PHset E ⊆ (excited Mode).filter (F.PHq E.KH E.aScat) := by
    intro k hk
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hk).1,
        PH_subset_PHq F E hv k (Finset.mem_filter.mp hk).2⟩
  have hle : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hinv : E.ell ^ 3 * E.ell ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_natCast E.ell 3, ← Real.rpow_add (ell_pos E hv)]
    norm_num
  calc ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2
      ≤ ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
          E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 := hle
    _ = E.ell ^ 3 * (E.ell ^ (-(3 : ℝ)) *
          ∑ k ∈ (excited Mode).filter (F.PHq E.KH E.aScat),
            E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ E.ell ^ 3 * (K₀ * E.aScat) := mul_le_mul_of_nonneg_left hK.sum_W1sq hell3

theorem sum_W1alpha_sub_le (K₀ b₀ : ℝ) (hb₀ : 0 < b₀) (hK₀ : 0 ≤ K₀) :
    ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
        (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
        (E : Work.BoseB7.Q3Env Mode) (hv : Work.BoseB7.FSParamsView E),
        hv.t ≤ t₀ → b₀ ≤ E.b → Work.BoseB7A.Q3Kernel K₀ F T E →
        ∀ s : Mode, E.fL s ≠ 0 →
          ∑ k ∈ F.PHset E, |E.W1 k * E.alpha (s - k)| ≤ 5 * E.rho * E.aScat * K₀ * E.ell ^ 3 := by
  refine ⟨(1 / 4 : ℝ) ^ 24, by norm_num, ?_⟩
  intro Mode _ _ _ F T E hv hle _hb hK s hfL
  have hρ : 0 < E.rho := rho_pos E hv
  have ha : 0 < E.aScat := hv.a_pos
  have hell : 0 < E.ell := ell_pos E hv
  have hsum1 : ∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 ≤
      E.ell ^ 3 * (K₀ * E.aScat) := sum_W1sq_le K₀ F T E hv hK
  have hsum2 : ∑ k ∈ F.PHset E, E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2 ≤
      E.ell ^ 3 * (K₀ * E.aScat) := sum_W1sq_shift_le K₀ F T E hv hle hK s hfL
  calc ∑ k ∈ F.PHset E, |E.W1 k * E.alpha (s - k)|
      ≤ ∑ k ∈ F.PHset E, 2 * E.rho * (E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2 +
          E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2) :=
        Finset.sum_le_sum fun k hk =>
          abs_W1_mul_alpha_sub_le K₀ F T E hv hle hK hfL hk
    _ = 2 * E.rho * ((∑ k ∈ F.PHset E, E.W1 k ^ 2 / ‖F.kmom k‖ ^ 2) +
          ∑ k ∈ F.PHset E, E.W1 (s - k) ^ 2 / ‖F.kmom (s - k)‖ ^ 2) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * E.rho * (E.ell ^ 3 * (K₀ * E.aScat) + E.ell ^ 3 * (K₀ * E.aScat)) :=
        mul_le_mul_of_nonneg_left (add_le_add hsum1 hsum2) (by positivity)
    _ = 4 * E.rho * K₀ * E.aScat * E.ell ^ 3 := by ring
    _ ≤ 5 * E.rho * E.aScat * K₀ * E.ell ^ 3 := by
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hρ.le ha.le) hK₀)
          (pow_nonneg hell.le 3)]

end Work.BoseB7A
