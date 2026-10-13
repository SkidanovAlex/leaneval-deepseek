/-
Copyright: work module for the Elgindi finite-time singularity project.

# `I1Wk/Asm` — the assembly of `i1Paper_weakMixed`

This module glues the proved pieces into the chain that proves the requested theorem
`Work.FTS.EllipticEst.Cores.AeStep2Aux.i1Paper_weakMixed`.

Pieces (all proved, `sorry`-free, axioms `[propext, Classical.choice, Quot.sound]`):

* `I1Wk.truncZIbp2` — the radial IBP with test functions `χ = χ(z)` and `ψ = ψ(θ)`:
  `D_χψ = −Tr_χψ − M_χψ` with
  `D_χψ = ∫∫ χw²σθψ (z²∂_zzu)(∂_θθu)`, `Tr_χψ = ∫∫ (∂_z(χw²z²)/z)σθψ U B`,
  `M_χψ = ∫∫ χw²σθψ U (z∂_z∂_θθu)`, `U = z∂_zu`, `B = ∂_θθu`;
* `I1Wk.truncThetaIbpSep_split` — the slice identity `S2` integrated in `z`, split into the
  four iterated integrals: `M_χψ = −2ηA_χψ − κP_χψ − c·Def_χψ + ½W_χψ`, where
  `A_χψ = ∫_z χw²∫_θσθψU²`, `P_χψ = ∫_zχw²∫_θσθψV²` (`V = z∂_z∂_θu`), `Def_χψ ≥ 0` is the
  defect integral, `W_χψ = ∫_zχw²∫_θσθψ''U²`;
* `I1Wk.aeGradTrace0` — the traces of `U` vanish and the endpoint rate holds;
* `I1Wk.sliceWbound` — the bound of `W` by the endpoint partial energies.

Combining the first two gives the truncated identity proved below; dropping the two nonnegative
terms, Cauchy–Schwarz on the transfer term and the `ε`-argument over the two cut-off families
then give the target.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncZIbp2
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk.truncThetaIbpSep
import Submission.Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk

set_option autoImplicit false

theorem integral_nonneg_of_ae' {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ∀ᵐ x ∂(volume.restrict s), 0 ≤ f x) :
    0 ≤ ∫ x in s, f x := by
  by_cases h : Integrable f (volume.restrict s)
  · exact integral_nonneg_of_ae hf
  · rw [integral_undef h]

/-- **The truncated identity** — the radial IBP of `truncZIbp2` combined with the sliced
`θ`-identity of `truncThetaIbpSep_split`:

`D_χψ = −Tr_χψ + 2η·A_χψ + κ·P_χψ + (2η/(1+η))·Def_χψ − ½·W_χψ`. -/
theorem truncIdentity (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Set.Ioi (0:ℝ))
    (hχsupp' : Function.support χ ⊆ Set.Ioi (0:ℝ))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b)
    (hψsep1 : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2))
    (ho1 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0))
    (ho2 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
      (Set.Ioi 0))
    (ho3 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
      (Set.Ioi 0))
    (ho4 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
          * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z^2 * Work.Spaces.pzIter 2 u z θ) * (Work.Spaces.pthIter 2 u z θ))
      = - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z)
              * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
              * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ))
        + 2 * Work.Spaces.eta * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz u z θ)^2))
        + ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
        + (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
                    - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                      * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
        - (1/2) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
                * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2)) := by
  have h1 := truncZIbp2 u χ ψ hu hχ hχc hχsupp (hψ.of_le (by norm_num)) hψsep1
  have h4 := truncThetaIbpSep_split u χ ψ hu hχ hχc hχsupp' hψ hψc hψsep ho1 ho2 ho3 ho4
  linarith [h1, h4]

/-- `sin (2θ) ≥ 0` on the open interval. -/
theorem sin_two_nonneg_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · linarith [hθ.1]
  · linarith [hθ.2, Real.pi_pos]

/-- The `θ`-inner integral of a nonnegative integrand is nonnegative (on `Ioo 0 (π/2)`). -/
theorem inner_nonneg {f : ℝ → ℝ} (hf : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ f θ) :
    0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), f θ := by
  refine integral_nonneg_of_ae' ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Eventually.of_forall fun θ hθ => hf θ hθ

theorem inner_nonneg_z {f : ℝ → ℝ → ℝ}
    (hf : ∀ z θ, θ ∈ Set.Ioo 0 (Real.pi / 2) → 0 ≤ f z θ) :
    ∀ z, 0 ≤ ∫ θ in Set.Ioo 0 (Real.pi / 2), f z θ :=
  fun z => inner_nonneg (fun θ hθ => hf z θ hθ)

/-- **The truncated inequality** (dropping the two nonnegative terms of `truncIdentity`):

`D_χψ ≥ −Tr_χψ + κ·P_χψ − ½·W_χψ`,

with `P_χψ = ∫_z χw² ∫_θ σθψ V²`, `V = z∂_z∂_θu`. -/
theorem truncIneq (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hu : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Set.Ioi (0:ℝ))
    (hχsupp' : Function.support χ ⊆ Set.Ioi (0:ℝ))
    (hχnn : ∀ z, 0 ≤ χ z)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψsep : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < Real.pi / 2 ∧ tsupport ψ ⊆ Set.Ioo a b)
    (hψsep1 : tsupport ψ ⊆ Set.Ioo 0 (Real.pi / 2))
    (hψnn : ∀ θ, 0 ≤ ψ θ)
    (ho1 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0))
    (ho2 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
      (Set.Ioi 0))
    (ho3 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
          * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
              - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
                * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2))
      (Set.Ioi 0))
    (ho4 : MeasureTheory.IntegrableOn
      (fun z => χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
        (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
          * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2))
      (Set.Ioi 0)) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), χ z * (Work.Spaces.w z)^2
        * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z^2 * Work.Spaces.pzIter 2 u z θ) * (Work.Spaces.pthIter 2 u z θ))
      ≥ - (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
            (deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z)
              * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
              * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ))
        + ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
                * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ)^2))
        - (1/2) * (∫ z in Set.Ioi 0,
            χ z * (Work.Spaces.w z)^2 * (∫ θ in Set.Ioo 0 (Real.pi / 2),
              (Real.sin (2*θ)) ^ (-(Work.Spaces.eta))
                * deriv (deriv ψ) θ * (z * Work.Spaces.pz u z θ)^2)) := by
  have hid := truncIdentity u χ ψ hu hχ hχc hχsupp hχsupp' hψ hψc hψsep hψsep1
    ho1 ho2 ho3 ho4
  -- the two dropped terms are nonnegative
  have hA0 : 0 ≤ (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z)^2 *
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz u z θ)^2)) := by
    refine integral_nonneg_of_ae' ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    refine mul_nonneg (mul_nonneg (hχnn z) (sq_nonneg _)) ?_
    refine inner_nonneg fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Ioo hθ) _) (hψnn θ))
      (sq_nonneg _)
  have hD0 : 0 ≤ (∫ z in Set.Ioi 0, χ z * (Work.Spaces.w z)^2 *
      (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ
        * (z * Work.Spaces.pz (Work.Spaces.pth u) z θ
            - (1 + Work.Spaces.eta) * (z * Work.Spaces.pz u z θ)
              * Real.cos (2*θ) * (Real.sin (2*θ)) ^ (-(1:ℝ)))^2)) := by
    refine integral_nonneg_of_ae' ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun z hz => ?_
    refine mul_nonneg (mul_nonneg (hχnn z) (sq_nonneg _)) ?_
    refine inner_nonneg fun θ hθ => ?_
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (sin_two_nonneg_Ioo hθ) _)
      (hψnn θ)) (sq_nonneg _)
  have heta : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  have hc0 : 0 ≤ 2 * Work.Spaces.eta / (1 + Work.Spaces.eta) := by positivity
  linarith [hid, mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Work.Spaces.eta) hA0,
    mul_nonneg hc0 hD0]

/-- `∫_{Ioi 0}∫_{Ioo 0 (π/2)}` agrees with `AngSecond.IP`'s `∫_{Ici 0}∫_{Icc 0 (π/2)}`. -/
theorem iterated_Ioi_eq_IP (F : ℝ → ℝ → ℝ) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ)
      = ∫ z in Set.Ici 0, ∫ θ in Set.Icc 0 (Real.pi / 2), F z θ := by
  rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := 0))]
  congr 1 with z
  exact MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume))

/-- **Cauchy–Schwarz with the cut-off weight** `χ z · ψ θ`, in the iterated form used by the
assembly.  Obtained from the tree's `AngSecond.IP_cauchy_schwarz` by absorbing the weight into the
two factors with square roots. -/
theorem IP_sqrtCS (χ ψ : ℝ → ℝ) (U B : ℝ → ℝ → ℝ) (hχψ : ∀ z θ, 0 ≤ χ z * ψ θ)
    (h1 : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Real.sqrt (χ z * ψ θ) * U z θ)
      (fun z θ => Real.sqrt (χ z * ψ θ) * U z θ))
    (h2 : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Real.sqrt (χ z * ψ θ) * B z θ)
      (fun z θ => Real.sqrt (χ z * ψ θ) * B z θ))
    (h3 : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => Real.sqrt (χ z * ψ θ) * U z θ)
      (fun z θ => Real.sqrt (χ z * ψ θ) * B z θ)) :
    |∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
        χ z * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (Work.Spaces.w z)^2
          * (U z θ * B z θ)|
      ≤ Real.sqrt (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
              χ z * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (Work.Spaces.w z)^2
                * (U z θ)^2)
        * Real.sqrt (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2),
              χ z * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (Work.Spaces.w z)^2
                * (B z θ)^2) := by
  have hcs := Work.FTS.EllipticEst.AngSecond.IP_cauchy_schwarz h1 h2 h3
  simp only [Work.FTS.EllipticEst.AngSecond.IP, Work.FTS.EllipticEst.AngSecond.w2,
    Work.FTS.EllipticEst.AngSecond.sig, Work.Spaces.Iz, Work.Spaces.Iθ] at hcs ⊢
  -- the integrands agree pointwise up to the square roots
  have hcongr : ∀ G : ℝ → ℝ → ℝ, (∫ z in Set.Ici 0, ∫ θ in Set.Icc 0 (Real.pi/2),
        Real.sqrt (χ z * ψ θ) * G z θ * (Real.sqrt (χ z * ψ θ) * G z θ)
          * (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)))
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi/2),
          χ z * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (Work.Spaces.w z)^2 * (G z θ)^2 := by
    intro G
    rw [iterated_Ioi_eq_IP]
    refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    have hsq : Real.sqrt (χ z * ψ θ) * Real.sqrt (χ z * ψ θ) = χ z * ψ θ :=
      Real.mul_self_sqrt (hχψ z θ)
    rw [show Real.sqrt (χ z * ψ θ) * G z θ * (Real.sqrt (χ z * ψ θ) * G z θ)
        = (Real.sqrt (χ z * ψ θ) * Real.sqrt (χ z * ψ θ)) * (G z θ * G z θ) by ring,
      hsq, sq]
    ring
  have hcross : (∫ z in Set.Ici 0, ∫ θ in Set.Icc 0 (Real.pi/2),
        Real.sqrt (χ z * ψ θ) * U z θ * (Real.sqrt (χ z * ψ θ) * B z θ)
          * (Work.Spaces.w z)^2 * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)))
      = ∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi/2),
          χ z * (Real.sin (2*θ)) ^ (-(Work.Spaces.eta)) * ψ θ * (Work.Spaces.w z)^2
            * (U z θ * B z θ) := by
    rw [iterated_Ioi_eq_IP]
    refine setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
    have hsq : Real.sqrt (χ z * ψ θ) * Real.sqrt (χ z * ψ θ) = χ z * ψ θ :=
      Real.mul_self_sqrt (hχψ z θ)
    rw [show Real.sqrt (χ z * ψ θ) * U z θ * (Real.sqrt (χ z * ψ θ) * B z θ)
        = (Real.sqrt (χ z * ψ θ) * Real.sqrt (χ z * ψ θ)) * (U z θ * B z θ) by ring, hsq]
    ring
  rw [← hcongr U, ← hcongr B, ← hcross]
  exact hcs



/-- The pointwise split of the radial cutoff weight: for `z ≠ 0`,
`∂_z(χ w² z²)/z = χ' w² z + χ · (2(z−1)/(1+z)) · w²`. -/
theorem cw_split (χ : ℝ → ℝ) (z : ℝ) (hz : z ≠ 0) (hχd : DifferentiableAt ℝ χ z) :
    deriv (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2) z / z
      = deriv χ z * ((Work.Spaces.w z)^2 * z)
        + χ z * ((2*(z-1)/(1+z)) * (Work.Spaces.w z)^2) := by
  have hfun : (fun z' => χ z' * (Work.Spaces.w z')^2 * z'^2)
      =ᶠ[𝓝 z] fun z' => χ z' * ((1+z')^4 / z'^2) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    rw [Work.Spaces.w]
    field_simp
  rw [Filter.EventuallyEq.deriv_eq hfun]
  have hg : HasDerivAt (fun z' : ℝ => (1+z')^4 / z'^2)
      ((4*(1+z)^3 * z^2 - (1+z)^4 * (2*z)) / (z^2)^2) z := by
    have h1 : HasDerivAt (fun z' : ℝ => (1+z')^4) (4*(1+z)^3) z := by
      have h : HasDerivAt (fun z' : ℝ => 1 + z') 1 z :=
        ((hasDerivAt_const (x := z) (c := (1:ℝ))).add (hasDerivAt_id z)).congr_deriv
          (by norm_num)
      exact h.pow 4 |>.congr_deriv (by norm_num)
    have h2 : HasDerivAt (fun z' : ℝ => z'^2) (2*z) z :=
      (hasDerivAt_id z).pow 2 |>.congr_deriv (by norm_num)
    exact h1.div h2 (pow_ne_zero 2 hz) |>.congr_deriv (by ring)
  have hprod : HasDerivAt (fun z' : ℝ => χ z' * ((1+z')^4 / z'^2))
      (deriv χ z * ((1+z)^4 / z^2)
        + χ z * ((4*(1+z)^3 * z^2 - (1+z)^4 * (2*z)) / (z^2)^2)) z :=
    hχd.hasDerivAt.mul hg
  rw [hprod.deriv]
  have hz2 : (1+z)^4 / z^2 = (Work.Spaces.w z)^2 * z^2 := by
    rw [Work.Spaces.w]; field_simp
  have hz4 : (4*(1+z)^3 * z^2 - (1+z)^4 * (2*z)) / (z^2)^2
      = (2*(z-1)/(1+z)) * (Work.Spaces.w z)^2 * z := by
    rw [Work.Spaces.w]; field_simp; ring
  rw [hz2, hz4, div_eq_iff hz]
  ring

/-- `|cw z| ≤ 2` for `z ≥ 0`. -/
theorem abs_cw_le_two {z : ℝ} (hz : 0 ≤ z) : |2*(z-1)/(1+z)| ≤ 2 := by
  have h1 : 0 < 1 + z := by linarith
  rw [abs_div, abs_mul, abs_of_pos h1, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [div_le_iff₀ h1]
  have : |z - 1| ≤ z + 1 := by
    rw [abs_le]; constructor <;> linarith
  linarith

end Work.FTS.EllipticEst.Cores.AeStep2Aux.I1Wk
