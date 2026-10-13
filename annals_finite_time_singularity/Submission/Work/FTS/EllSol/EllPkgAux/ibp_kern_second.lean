/-
# `Work.FTS.EllSol.EllPkgAux.ibp_kern_second` — the second-order integration by parts for `Kern`

The three-image kernel is

  `Kern ρ θ s = ρ (θ - s) - ρ (θ + s) - ρ (θ + s - π)`

(`ThMollDefs`), the fold of the doubly odd extension of an angular slice.  Differentiating
in the *image* variable `s` we have

  `∂_s (Kern ρ θ) = -(ρ' (θ - ·) + ρ' (θ + ·) + ρ' (θ + · - π)) = -P`,
  `∂_s P        = -(ρ'' (θ - ·) - ρ'' (θ + ·) - ρ'' (θ + · - π)) = -Kern ρ'' θ`,

so two integrations by parts against a function `G` with `G 0 = G (π/2) = 0` and `G' = H`,
`H' = H2` move the two derivatives on `ρ` over to `G`:

  `∫_{Iθ} Kern ρ'' θ · G = ∫_{Iθ} P · H = ∫_{Iθ} Kern ρ θ · H2`,

the boundary terms of the two integrations by parts being

  `P (π/2) G (π/2) - P 0 G 0 = 0`  (hypotheses `hGp`, `hG0`)  and
  `Kern ρ θ (π/2) H (π/2) - Kern ρ θ 0 H 0 = -ρ (θ + π/2) H (π/2) + ρ (θ - π) H 0 = 0`
  (hypotheses `hv1`, `hv2`).

This is the order-2 companion of `ibp_kern_first`; every boundary term is killed by the vanishing
of the *kernel* at the two ends of `s` (a consequence of `hv1`, `hv2`), never by a vanishing value
of `H`.  Note that no hypothesis on `θ` is used: the identity is a statement about the interval
`[0, π/2]` in `s`, uniform in the parameter `θ` (verified numerically as well).

Everything is a direct application of `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`;
the only work is bookkeeping (`min`/`max`, `uIcc`, the set integral over `Iθ` versus the interval
integral over `0..π/2`, and the two boundary evaluations).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Submission.Work.FTS.EllSol.EllPkgAux.ThMollAux0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

theorem ibp_kern_second {ρ ρ' ρ'' G H H2 : ℝ → ℝ} {θ : ℝ}
    (hρ : ∀ t : ℝ, HasDerivAt ρ (ρ' t) t)
    (hρ' : ∀ t : ℝ, HasDerivAt ρ' (ρ'' t) t) (hρ'c : Continuous ρ') (hρ''c : Continuous ρ'')
    (hGc : ContinuousOn G Work.Spaces.Iθ)
    (hHG : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt G (H x) x)
    (hG0 : G 0 = 0) (hGp : G (Real.pi / 2) = 0)
    (hHc : ContinuousOn H Work.Spaces.Iθ)
    (hH2int : MeasureTheory.IntegrableOn H2 Work.Spaces.Iθ)
    (hH2 : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt H (H2 x) x)
    (hv1 : ρ (θ + Real.pi / 2) = 0) (hv2 : ρ (θ - Real.pi) = 0) :
    (∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern ρ'' θ s * G s)
      = ∫ s in Work.Spaces.Iθ, Work.FTS.EllSol.EllPkgAux.Kern ρ θ s * H2 s := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  -- `ρ` is continuous (it is differentiable everywhere)
  have hρc : Continuous ρ :=
    continuous_iff_continuousAt.mpr (fun t => (hρ t).continuousAt)
  -- the three pieces: the kernel `K`, the plus-kernel `P` of `ρ'`, and the kernel `Q` of `ρ''`
  set K : ℝ → ℝ := fun s => ρ (θ - s) - ρ (θ + s) - ρ (θ + s - Real.pi) with hKdef
  set P : ℝ → ℝ := fun s => ρ' (θ - s) + ρ' (θ + s) + ρ' (θ + s - Real.pi) with hPdef
  set Q : ℝ → ℝ := fun s => ρ'' (θ - s) - ρ'' (θ + s) - ρ'' (θ + s - Real.pi) with hQdef
  -- continuity of the three pieces
  have hKc : Continuous K := by
    rw [hKdef]
    exact ((hρc.comp (continuous_const.sub continuous_id)).sub
      (hρc.comp (continuous_const.add continuous_id))).sub
      (hρc.comp ((continuous_const.add continuous_id).sub continuous_const))
  have hPc : Continuous P := by
    rw [hPdef]
    exact ((hρ'c.comp (continuous_const.sub continuous_id)).add
      (hρ'c.comp (continuous_const.add continuous_id))).add
      (hρ'c.comp ((continuous_const.add continuous_id).sub continuous_const))
  have hQc : Continuous Q := by
    rw [hQdef]
    exact ((hρ''c.comp (continuous_const.sub continuous_id)).sub
      (hρ''c.comp (continuous_const.add continuous_id))).sub
      (hρ''c.comp ((continuous_const.add continuous_id).sub continuous_const))
  -- the `s`-derivatives of the three pieces
  have hsub : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ρ (θ - x)) (-(ρ' (θ - s))) s := by
    intro s
    have hin : HasDerivAt (fun x : ℝ => θ - x) (-1) s := (hasDerivAt_id s).const_sub θ
    have h2 := (hρ (θ - s)).comp s hin
    simpa only [Function.comp_def, mul_neg_one] using h2
  have hadd : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ρ (θ + x)) (ρ' (θ + s)) s := by
    intro s
    have hin : HasDerivAt (fun x : ℝ => θ + x) (1 : ℝ) s := (hasDerivAt_id s).const_add θ
    have h2 := (hρ (θ + s)).comp s hin
    simpa only [Function.comp_def, mul_one] using h2
  have hsh : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ρ (θ + x - Real.pi))
      (ρ' (θ + s - Real.pi)) s := by
    intro s
    have hin : HasDerivAt (fun x : ℝ => θ + x - Real.pi) (1 : ℝ) s :=
      ((hasDerivAt_id s).const_add θ).sub_const Real.pi
    have h2 := (hρ (θ + s - Real.pi)).comp s hin
    simpa only [Function.comp_def, mul_one] using h2
  have hsub' : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ρ' (θ - x)) (-(ρ'' (θ - s))) s := by
    intro s
    have hin : HasDerivAt (fun x : ℝ => θ - x) (-1) s := (hasDerivAt_id s).const_sub θ
    have h2 := (hρ' (θ - s)).comp s hin
    simpa only [Function.comp_def, mul_neg_one] using h2
  have hadd' : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ρ' (θ + x)) (ρ'' (θ + s)) s := by
    intro s
    have hin : HasDerivAt (fun x : ℝ => θ + x) (1 : ℝ) s := (hasDerivAt_id s).const_add θ
    have h2 := (hρ' (θ + s)).comp s hin
    simpa only [Function.comp_def, mul_one] using h2
  have hsh' : ∀ s : ℝ, HasDerivAt (fun x : ℝ => ρ' (θ + x - Real.pi))
      (ρ'' (θ + s - Real.pi)) s := by
    intro s
    have hin : HasDerivAt (fun x : ℝ => θ + x - Real.pi) (1 : ℝ) s :=
      ((hasDerivAt_id s).const_add θ).sub_const Real.pi
    have h2 := (hρ' (θ + s - Real.pi)).comp s hin
    simpa only [Function.comp_def, mul_one] using h2
  have hKder : ∀ s : ℝ, HasDerivAt K (-(P s)) s := by
    intro s
    have h4 : HasDerivAt (fun x : ℝ => ρ (θ - x) - ρ (θ + x) - ρ (θ + x - Real.pi))
        (-(ρ' (θ - s)) - ρ' (θ + s) - ρ' (θ + s - Real.pi)) s :=
      ((hsub s).sub (hadd s)).sub (hsh s)
    have h4' : HasDerivAt K (-(ρ' (θ - s)) - ρ' (θ + s) - ρ' (θ + s - Real.pi)) s := by
      rw [hKdef]; exact h4
    have hPd : -(P s) = -(ρ' (θ - s)) - ρ' (θ + s) - ρ' (θ + s - Real.pi) := by
      rw [hPdef]; ring
    rw [hPd]; exact h4'
  have hPder : ∀ s : ℝ, HasDerivAt P (-(Q s)) s := by
    intro s
    have h4 : HasDerivAt (fun x : ℝ => ρ' (θ - x) + ρ' (θ + x) + ρ' (θ + x - Real.pi))
        (-(ρ'' (θ - s)) + ρ'' (θ + s) + ρ'' (θ + s - Real.pi)) s :=
      ((hsub' s).add (hadd' s)).add (hsh' s)
    have h4' : HasDerivAt P (-(ρ'' (θ - s)) + ρ'' (θ + s) + ρ'' (θ + s - Real.pi)) s := by
      rw [hPdef]; exact h4
    have hQd : -(Q s) = -(ρ'' (θ - s)) + ρ'' (θ + s) + ρ'' (θ + s - Real.pi) := by
      rw [hQdef]; ring
    rw [hQd]; exact h4'
  -- boundary values of the kernel `K`
  have hK0 : K 0 = 0 := by
    simp only [hKdef, sub_zero, add_zero]
    rw [show ρ θ - ρ θ - ρ (θ - Real.pi) = -ρ (θ - Real.pi) from by ring, hv2, neg_zero]
  have hKp : K (Real.pi / 2) = 0 := by
    simp only [hKdef]
    rw [show θ + Real.pi / 2 - Real.pi = θ - Real.pi / 2 from by ring]
    rw [show ρ (θ - Real.pi / 2) - ρ (θ + Real.pi / 2) - ρ (θ - Real.pi / 2)
        = -ρ (θ + Real.pi / 2) from by ring, hv1, neg_zero]
  -- interval integrability of the four functions appearing as derivative slots
  have hHint : IntervalIntegrable H volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hle hHc
  have hGint : IntervalIntegrable G volume 0 (Real.pi / 2) :=
    ContinuousOn.intervalIntegrable_of_Icc hle hGc
  have hH2i : IntervalIntegrable H2 volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    exact hH2int
  have hPint : IntervalIntegrable (fun s : ℝ => -(P s)) volume 0 (Real.pi / 2) :=
    hPc.neg.intervalIntegrable 0 (Real.pi / 2)
  have hQint : IntervalIntegrable (fun s : ℝ => -(Q s)) volume 0 (Real.pi / 2) :=
    hQc.neg.intervalIntegrable 0 (Real.pi / 2)
  -- first integration by parts: `∫ P · H = ∫ Q · G`
  have hIBP1 : (∫ s in (0 : ℝ)..Real.pi / 2, P s * H s)
      = P (Real.pi / 2) * G (Real.pi / 2) - P 0 * G 0
        - ∫ s in (0 : ℝ)..Real.pi / 2, (-(Q s)) * G s :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (u := P) (u' := fun s : ℝ => -(Q s)) (v := G) (v' := H)
      hPc.continuousOn
      (by rw [Set.uIcc_of_le hle]; exact hGc)
      (fun x _ => hPder x)
      (fun x hx => hHG x (by rw [min_eq_left hle, max_eq_right hle] at hx; exact hx))
      hQint hHint
  -- second integration by parts: `∫ K · H2 = ∫ P · H`
  have hIBP2 : (∫ s in (0 : ℝ)..Real.pi / 2, K s * H2 s)
      = K (Real.pi / 2) * H (Real.pi / 2) - K 0 * H 0
        - ∫ s in (0 : ℝ)..Real.pi / 2, (-(P s)) * H s :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (u := K) (u' := fun s : ℝ => -(P s)) (v := H) (v' := H2)
      hKc.continuousOn
      (by rw [Set.uIcc_of_le hle]; exact hHc)
      (fun x _ => hKder x)
      (fun x hx => hH2 x (by rw [min_eq_left hle, max_eq_right hle] at hx; exact hx))
      hPint hH2i
  -- the two integrals after the sign bookkeeping
  have h1 : (∫ s in (0 : ℝ)..Real.pi / 2, Q s * G s)
      = ∫ s in (0 : ℝ)..Real.pi / 2, P s * H s := by
    have hneg : (∫ s in (0 : ℝ)..Real.pi / 2, (-(Q s)) * G s)
        = -(∫ s in (0 : ℝ)..Real.pi / 2, Q s * G s) := by
      rw [show (fun s : ℝ => (-(Q s)) * G s) = (fun s : ℝ => -(Q s * G s)) from by
            funext s; ring, intervalIntegral.integral_neg]
    rw [hIBP1, hGp, hG0, hneg]
    ring
  have h2 : (∫ s in (0 : ℝ)..Real.pi / 2, K s * H2 s)
      = ∫ s in (0 : ℝ)..Real.pi / 2, P s * H s := by
    have hneg : (∫ s in (0 : ℝ)..Real.pi / 2, (-(P s)) * H s)
        = -(∫ s in (0 : ℝ)..Real.pi / 2, P s * H s) := by
      rw [show (fun s : ℝ => (-(P s)) * H s) = (fun s : ℝ => -(P s * H s)) from by
            funext s; ring, intervalIntegral.integral_neg]
    rw [hIBP2, hKp, hK0, hneg]
    ring
  -- identify the explicit pieces with the `Kern` of `ρ''` and of `ρ`
  have hA : (∫ s in (0 : ℝ)..Real.pi / 2, Kern ρ'' θ s * G s)
      = ∫ s in (0 : ℝ)..Real.pi / 2, Q s * G s := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [Kern_apply, hQdef]
  have hB : (∫ s in (0 : ℝ)..Real.pi / 2, Kern ρ θ s * H2 s)
      = ∫ s in (0 : ℝ)..Real.pi / 2, K s * H2 s := by
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    rw [Kern_apply, hKdef]
  rw [setIntegral_Iθ_eq_interval (fun s => Kern ρ'' θ s * G s),
    setIntegral_Iθ_eq_interval (fun s => Kern ρ θ s * H2 s)]
  exact hA.trans (h1.trans (h2.symm.trans hB.symm))

end Work.FTS.EllSol.EllPkgAux
