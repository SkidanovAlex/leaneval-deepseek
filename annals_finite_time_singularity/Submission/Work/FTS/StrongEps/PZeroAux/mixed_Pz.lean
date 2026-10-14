import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstCrux
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45AslotLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_RegExport.RXB.l12dens_weighted_bound
import Submission.Work.FTS_RegExport.RXT.StarVopWlInf
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.SolutionDelivery.DatumOdd
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.VopcCore =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.EllSol.PkgK5.VopcCore`

The `V`-slot of the modulation system, in the *open* class, from the honesty of the second
angular derivative of the datum.

`Vop α Ξ = ∂_θΞ - tan θ · Ξ` is a purely *tangential* first-order operator, so its `ℋ^k`-norm is
controlled by `∂_θ²Ξ` alone (the extra angular order is paid for by the boundary traces of `Ξ`,
which are part of the hypotheses).

The proof is an assembly of three already delivered pieces:

* `VopAux.thetaPoincareOpenTrace` — with the traces of `D_z^jΞ` and `∂_θ²Ξ ∈ ℋ^k`, both `Ξ` and
  `∂_θΞ` are honestly in `ℋ^k` and their norms are bounded by `C·|∂_θ²Ξ|_{ℋ^k}`;
* `PkgK5.divSinK5` — `Ξ / sin 2θ ∈ ℋ^k` with `|Ξ/sin 2θ|_{ℋ^k} ≤ C·|∂_θΞ|_{ℋ^k}`;
* `Blocks.HkMul_ang_le` — multiplication by the bounded angular profile `sin²θ` preserves
  `ℋ^k`, with a constant loss.

The point is the *exact* algebraic identity on the open quadrant

  `Vop α Ξ = ∂_θΞ - 2 sin²θ · (Ξ / sin 2θ)`

(the factor `2 sin²θ / sin 2θ = tan θ`), which turns the singular-looking `tan θ · Ξ` into a
bounded angular profile times the honest quotient `Ξ/sin 2θ`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Local helpers -/

/-- Multiplication by the bounded angular profile `sin θ ^ 2` preserves `SmoothOpen`. -/
private theorem smoothOpen_sin_sq_mul {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.sin θ ^ 2 * f z θ) :=
  Work.FTS.Nonlinear.N4Fields.smoothOpen_angMul
    (fun θ => ((Real.contDiff_sin (n := ⊤)).pow 2).contDiffAt) hf

/-- **The algebraic identity behind the estimate.**  On the open quadrant
`0 < θ < π/2` (and for any `z`) the tangential operator `V` is the first angular derivative
minus a *bounded* angular profile times the quotient by `sin 2θ`:

  `Vop α Ξ = ∂_θΞ - 2 sin²θ · (Ξ / sin 2θ)`,

because `2 sin²θ / sin 2θ = sin θ / cos θ = tan θ`. -/
private theorem vop_eq (α : ℝ) {Ξ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) :
    Work.FTS.EllipticEst.Vop α Ξ z θ
      = Work.Spaces.pth Ξ z θ
        + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) := by
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]))
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hsin2 : Real.sin (2 * θ) ≠ 0 := by
    rw [Real.sin_two_mul]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hsin) hcos
  simp only [Work.FTS.EllipticEst.Vop, Real.tan_eq_sin_div_cos]
  rw [Real.sin_two_mul]
  field_simp
  ring

theorem VopcCore (k : ℕ) (hk : 1 ≤ k) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (Ξ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen Ξ →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      (∀ z : ℝ, 0 < z → ∀ j : ℕ, j ≤ k → ContDiffOn ℝ Work.Stability.smoothOrder
        (fun θ : ℝ => Work.Spaces.DzIter j Ξ z θ) (Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ξ) →
      Work.FTS.VocabO.HQo α k (Work.FTS.EllipticEst.Vop α Ξ) ∧
      Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
        ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by
  obtain ⟨C1, hC1pos, hpo⟩ := Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace k
  obtain ⟨C2, hC2pos, hdiv⟩ := divSinK5 k hk
  obtain ⟨C3, hC3pos, hang⟩ := Work.Blocks.HkMul_ang_le k
  refine ⟨max 1 (Real.sqrt 2 * (C1 + 2 * Real.sqrt C3 * C2 * C1)),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α Ξ hα hα4 hSO htrace hslice hmem
  have hα1 : α ≤ 1 := by linarith
  -- ### The three inputs
  obtain ⟨_, hmA, -, hnormA⟩ :=
    hpo α Ξ hα hα4 ((Work.FTS.EllipticEst.smoothOpen_iff_forall Ξ).mp hSO) htrace hmem
  obtain ⟨hmq, hnormq⟩ :=
    hdiv α Ξ hα hα1 hSO hslice (fun z hz j hj => (htrace j hj z hz).1)
      (fun z hz j hj => (htrace j hj z hz).2) hmA
  have hSOq : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Ξ z θ / Real.sin (2 * θ)) :=
    Work.FTS.EllipticEst.RPFresh.smoothOpen_div_sin hSO
  obtain ⟨-, -, hmg, hSqg⟩ :=
    (hang α (fun z θ => Ξ z θ / Real.sin (2 * θ)) hα hα1 hSOq).2.2 hmq
  -- ### The pieces of the decomposition `Vop α Ξ = ∂_θΞ - 2 sin²θ · (Ξ/sin 2θ)`
  have hSOA : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Ξ) := hSO.pth
  have hSOg : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))) :=
    smoothOpen_sin_sq_mul hSOq
  have hSOB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => 2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    hSOg.const_mul' 2
  have hSONegB : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))) :=
    hSOB.const_mul' (-1)
  have hSOD : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Spaces.pth Ξ z θ
        + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))) :=
    Work.FTS.EllipticEst.smoothOpen_add hSOA hSONegB
  have hmB : Work.Spaces.HkMem α k
      (fun z θ => 2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) :=
    Work.FTS.LocData.HkMem_const_mul α k 2 hmg
  have hmNegB : Work.Spaces.HkMem α k
      (fun z θ => (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))) :=
    Work.FTS.LocData.HkMem_const_mul α k (-1) hmB
  have hmD : Work.Spaces.HkMem α k
      (fun z θ => Work.Spaces.pth Ξ z θ
        + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))) :=
    Work.FTS.EllipticEst.HkMem_add_open hSOA hSONegB hmA hmNegB
  -- ### Transfer to `Vop α Ξ` on the open quadrant
  have hagree : Work.FTS.EllipticEst.AgreeOnQ
      (fun z θ => Work.Spaces.pth Ξ z θ
        + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))
      (Work.FTS.EllipticEst.Vop α Ξ) :=
    fun z θ _ hθ0 hθ1 => (vop_eq α (Ξ := Ξ) (z := z) (θ := θ) hθ0 hθ1).symm
  have hSOW : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.EllipticEst.Vop α Ξ) :=
    Work.FTS.EllipticEst.SmoothOpen.congr hSOD
      (fun z θ _ hθ0 hθ1 => (vop_eq α (Ξ := Ξ) (z := z) (θ := θ) hθ0 hθ1).symm)
  have hmW : Work.Spaces.HkMem α k (Work.FTS.EllipticEst.Vop α Ξ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hSOW hagree hmD
  refine ⟨⟨hSOW, hmW⟩, ?_⟩
  -- ### The norm estimate
  have hsmA : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth Ξ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.pth Ξ)).mp hSOA
  have hsmg : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))).mp hSOg
  have hsmB : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (fun z θ => 2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (fun z θ => 2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))).mp hSOB
  have hsmNegB : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry
        (fun z θ => (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (fun z θ => (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))).mp hSONegB
  have hPnn : 0 ≤ Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := Real.sqrt_nonneg _
  -- `|sin²θ · q| ≤ √C3 · |q|`
  have hg_le : Work.Spaces.HkNorm α k
        (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
      ≤ Real.sqrt C3 * (C2 * C1) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by
    have h1 : Work.Spaces.HkNorm α k
          (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
        ≤ Real.sqrt C3 * Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ)) := by
      show Real.sqrt (Work.Spaces.HkSq α k _) ≤ Real.sqrt C3 * Real.sqrt (Work.Spaces.HkSq α k _)
      rw [← Real.sqrt_mul hC3pos.le]
      exact Real.sqrt_le_sqrt hSqg
    have h2 : Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ))
        ≤ C2 * Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ) := hnormq
    calc Work.Spaces.HkNorm α k (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
        ≤ Real.sqrt C3 * Work.Spaces.HkNorm α k (fun z θ => Ξ z θ / Real.sin (2 * θ)) := h1
      _ ≤ Real.sqrt C3 * (C2 * Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ)) :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg C3)
      _ ≤ Real.sqrt C3 * (C2 * (C1 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hnormA hC2pos.le) (Real.sqrt_nonneg C3)
      _ = Real.sqrt C3 * (C2 * C1) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by ring
  -- `|2 sin²θ · q| ≤ 2√C3(C2 C1) |∂_θ²Ξ|`
  have hB_le : Work.Spaces.HkNorm α k
        (fun z θ => 2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))
      ≤ 2 * (Real.sqrt C3 * (C2 * C1)) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k 2 hsmg]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    calc 2 * Work.Spaces.HkNorm α k (fun z θ => Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))
        ≤ 2 * (Real.sqrt C3 * (C2 * C1) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)) :=
          mul_le_mul_of_nonneg_left hg_le (by norm_num)
      _ = 2 * (Real.sqrt C3 * (C2 * C1)) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by
          ring
  have hNegB_norm : Work.Spaces.HkNorm α k
        (fun z θ => (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))
      = Work.Spaces.HkNorm α k
        (fun z θ => 2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))) := by
    rw [Work.FTS.EllipticEst.HkNorm_const_mul α k (-1) hsmB]
    norm_num
  have hD_le : Work.Spaces.HkNorm α k
        (fun z θ => Work.Spaces.pth Ξ z θ
          + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))
      ≤ Real.sqrt 2 *
        (Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ)
          + Work.Spaces.HkNorm α k
            (fun z θ => (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))) :=
    Work.FTS.EllipticEst.HkNorm_add_le α k hsmA hsmNegB hmA hmNegB
  have hSqW : Work.Spaces.HkSq α k (Work.FTS.EllipticEst.Vop α Ξ)
      = Work.Spaces.HkSq α k (fun z θ => Work.Spaces.pth Ξ z θ
          + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α k
      (fun z θ _ hθ0 hθ1 => vop_eq α (Ξ := Ξ) (z := z) (θ := θ) hθ0 hθ1)
  have hnormW : Work.Spaces.HkNorm α k (Work.FTS.EllipticEst.Vop α Ξ)
      = Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pth Ξ z θ
          + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))) := by
    show Real.sqrt (Work.Spaces.HkSq α k _) = Real.sqrt (Work.Spaces.HkSq α k _)
    rw [hSqW]
  rw [hnormW]
  calc Work.Spaces.HkNorm α k (fun z θ => Work.Spaces.pth Ξ z θ
          + (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))
      ≤ Real.sqrt 2 *
        (Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ)
          + Work.Spaces.HkNorm α k
            (fun z θ => (-1) * (2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ)))))) := hD_le
    _ = Real.sqrt 2 *
        (Work.Spaces.HkNorm α k (Work.Spaces.pth Ξ)
          + Work.Spaces.HkNorm α k
            (fun z θ => 2 * (Real.sin θ ^ 2 * (Ξ z θ / Real.sin (2 * θ))))) := by
          rw [hNegB_norm]
    _ ≤ Real.sqrt 2 *
        (C1 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)
          + 2 * (Real.sqrt C3 * (C2 * C1)) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hnormA hB_le) (Real.sqrt_nonneg 2)
    _ = Real.sqrt 2 * (C1 + 2 * Real.sqrt C3 * C2 * C1)
          * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) := by ring
    _ ≤ max 1 (Real.sqrt 2 * (C1 + 2 * Real.sqrt C3 * C2 * C1))
          * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 Ξ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hPnn

end Work.FTS.EllSol.PkgK5
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.rhoProf_ae_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `rhoProf_ae_le` — the angular profile `rhoProf α k` is essentially bounded

The angular profile of the moment correction,

`rhoProf α k θ = ∑_{i ≤ k} (D_θ^i ρ (θ))² · (sin(2θ)^{−γ} + sin(2θ)^{−η})`,

(`Work.FTS.PhiStar.Honesty.CptApp.rhoProf`) is a *fixed* finite quantity: the profile
`ρ = crho⁻¹ · rhoAux` vanishes for `θ ≤ 1` and for `3/2 ≤ θ`, hence so does every one of
its `D_θ`-iterates (they are built from derivatives, and each iterate is zero on the open
complement of `[1, 3/2]` by `Filter.EventuallyEq.deriv_eq`).  Thus `rhoProf α k` vanishes
off the compact interval `[1, 3/2]`, while on that interval it is continuous (the factor
`sin(2θ)^{−γ} + sin(2θ)^{−η}` is bounded there since `sin(2θ) ∈ [sin 3, 1]`, and
`sin(2θ) > 0` on `[1, 3/2] ⊂ (0, π/2)`).  Compactness then gives the bound.
-/

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open Work.FTS.PhiStar.Honesty.CptApp

/-! ## The support of the moment profile `ρ` -/

theorem rhoAux_eq_zero_of_le_one {θ : ℝ} (h : θ ≤ 1) : rhoAux θ = 0 := by
  simp only [rhoAux, cut01,
    Real.smoothTransition.zero_of_nonpos (show 2 * θ - 2 ≤ 0 by linarith), zero_mul]

theorem rhoAux_eq_zero_of_three_halves_le {θ : ℝ} (h : 3 / 2 ≤ θ) : rhoAux θ = 0 := by
  simp only [rhoAux, cut01,
    Real.smoothTransition.zero_of_nonpos (show 3 - 2 * θ ≤ 0 by linarith), mul_zero]

theorem rho_eq_zero_of_le_one {θ : ℝ} (h : θ ≤ 1) : rho θ = 0 := by
  rw [rho, rhoAux_eq_zero_of_le_one h, mul_zero]

theorem rho_eq_zero_of_three_halves_le {θ : ℝ} (h : 3 / 2 ≤ θ) : rho θ = 0 := by
  rw [rho, rhoAux_eq_zero_of_three_halves_le h, mul_zero]


/-! ## The `D_θ`-iterates of `ρ` as functions of `θ` alone

`ρ` is a function of `θ` only, so `D_θ^i ρ` (applied to the lifted profile
`(z,θ) ↦ ρ θ`) is again a function of `θ` alone; it is the recursion
`rphi 0 = ρ`, `rphi (i+1) θ = sin(2θ) · (rphi i)' θ`. -/

/-- The `i`-th iterate `D_θ^i ρ` of the angular profile, as a function of `θ`. -/
def rphi : ℕ → ℝ → ℝ
  | 0 => rho
  | i + 1 => fun θ => Real.sin (2 * θ) * deriv (rphi i) θ


theorem rphi_succ (i : ℕ) :
    rphi (i + 1) = fun θ => Real.sin (2 * θ) * deriv (rphi i) θ := rfl

/-- The lifted iterates agree with `rphi`. -/
theorem DthIter_rho_val (i : ℕ) :
    ∀ θ : ℝ, Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ = rphi i θ := by
  induction i with
  | zero => intro θ; rfl
  | succ i ih =>
      intro θ
      rw [Work.Spaces.DthIter_succ, Work.Spaces.Dth]
      have h2 : Work.Spaces.pth
          (Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ')) 0 θ = deriv (rphi i) θ := by
        show deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ') θ
          = deriv (rphi i) θ
        congr 1
        funext θ'
        exact ih θ'
      rw [h2, rphi_succ]


/-- **The key support fact**: every `D_θ`-iterate of `ρ` vanishes for `θ < 1` and for
`3/2 < θ`. -/
theorem rphi_eq_zero (i : ℕ) :
    ∀ θ : ℝ, θ < 1 ∨ 3 / 2 < θ → rphi i θ = 0 := by
  induction i with
  | zero =>
      intro θ hθ
      rcases hθ with h | h
      · exact rho_eq_zero_of_le_one h.le
      · exact rho_eq_zero_of_three_halves_le h.le
  | succ i ih =>
      intro θ hθ
      have hderiv : deriv (rphi i) θ = 0 := by
        rcases hθ with h | h
        · have hnb : Set.Iio (1 : ℝ) ∈ 𝓝 θ := isOpen_Iio.mem_nhds h
          have hev : rphi i =ᶠ[𝓝 θ] (0 : ℝ → ℝ) := by
            filter_upwards [hnb] with x hx using ih x (Or.inl hx)
          simpa using hev.deriv_eq
        · have hnb : Set.Ioi (3 / 2 : ℝ) ∈ 𝓝 θ := isOpen_Ioi.mem_nhds h
          have hev : rphi i =ᶠ[𝓝 θ] (0 : ℝ → ℝ) := by
            filter_upwards [hnb] with x hx using ih x (Or.inr hx)
          simpa using hev.deriv_eq
      rw [rphi_succ]
      simp [hderiv]

/-- `rhoProf` vanishes off the compact interval `[1, 3/2]`. -/
theorem rhoProf_eq_zero_of_not_mem {α : ℝ} {k : ℕ} {θ : ℝ}
    (hθ : θ ∉ Set.Icc (1 : ℝ) (3 / 2)) : rhoProf α k θ = 0 := by
  have hlt : θ < 1 ∨ 3 / 2 < θ := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hθ
    exact hθ
  unfold rhoProf
  refine Finset.sum_eq_zero fun i _ => ?_
  have hφ : Work.Spaces.DthIter i (fun _ θ' : ℝ => rho θ') 0 θ = 0 := by
    rw [DthIter_rho_val i θ]
    exact rphi_eq_zero i θ hlt
  simp [hφ]

theorem rhoProf_ae_le (k : ℕ) (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.FTS.PhiStar.Honesty.CptApp.rhoProf α k θ ≤ C := by
  have hcont : ContinuousOn (rhoProf α k) (Set.Icc (1 : ℝ) (3 / 2)) :=
    (continuousOn_rhoProf α k).mono fun θ hθ =>
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_gt_three]⟩
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ 0, le_max_right _ _, ?_⟩
  refine Filter.Eventually.of_forall fun θ => ?_
  by_cases hθ : θ ∈ Set.Icc (1 : ℝ) (3 / 2)
  · have h1 : ‖rhoProf α k θ‖ ≤ C₁ := hC₁ θ hθ
    have h2 : rhoProf α k θ ≤ C₁ :=
      le_trans (le_abs_self _) (by simpa using h1)
    exact le_trans h2 (le_max_left _ _)
  · rw [rhoProf_eq_zero_of_not_mem hθ]
    exact le_max_right _ _

end Work.FTS.PhiStar.Honesty.CptApp.Est
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_K_psiSeries_of_level0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem ellWeakPos_K_psiSeries_of_level0 (K : ℕ) {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    (hF : Work.Spaces.HkMem α K F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.Series.psiSeries α F))
    (heq : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.FTS.PhiStar.Series.psiSeries α F) z θ = F z θ)
    (hFstar : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hσ : ∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 → Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter l (Work.Spaces.pthIter m
        (Work.FTS.PhiStar.Series.psiSeries α F))))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α F)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α F)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.TT.EllWeakPos α K F (Work.FTS.PhiStar.Series.psiSeries α F) := by
  -- The three elliptic honesty slots `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ` at level `K`, from the
  -- pure-radial family `hσ` and the vanishing-weight family `hV` through the grid majorant.
  obtain ⟨hmemA, hmemB, hmemMix⟩ :=
    HkMem_K_slots_of_vanishing_family K hα hγ hsm hσ hV
  -- The ten conjuncts of the weak class: the equation, the two Dirichlet traces (elementary for
  -- the mode series), the two moments (the source's is `hFstar`, the solution's is
  -- `Fstar_psiSeries_eq_zero`), the open-quadrant smoothness, and the four `HkMem` slots.
  exact ⟨heq, fun z => psiSeries_zero_theta_zero α F z,
    fun z => psiSeries_zero_theta_pi_half α F z, hFstar,
    fun z hz => Fstar_psiSeries_eq_zero hz (hcoef z hz) hFstar,
    fun n => Work.FTS.EllipticEst.SmoothOpen.forall hsm n, hF, hmemA, hmemB, hmemMix⟩

end Work.FTS.PhiStar.Honesty
end
-- ===== merged: Submission.Work.FTS.StrongEps.PZeroAux.mixed_Pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.PZeroAux

/-- **The mixed derivative of the projection `P₀`.**  On the open quadrant the iterated
operator `D_z^j D_θ^i` is linear, so it acts on `Pz f = f − (L₁₂ f 0 / pzNorm) • bump`
by the two terms of the definition. -/
theorem mixed_Pz {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (Work.FTS.StrongEps.Pz f) z θ
      = Work.Spaces.mixed j i f z θ
        - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
          * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
  -- the scalar of the correction
  set c : ℝ := Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm with hc
  -- the pointwise form of the projection
  have hPz : Work.FTS.StrongEps.Pz f
      = fun z θ => f z θ + (-c) * Work.FTS.StrongEps.bump z θ := by
    funext z θ
    rw [Work.FTS.StrongEps.Pz_apply, ← hc]
    ring
  -- the correction profile `(−c)·bump` is smooth on the open quadrant
  have hgsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) := by
    have hfun : Function.uncurry (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ)
        = fun p : ℝ × ℝ => (-c) * Function.uncurry Work.FTS.StrongEps.bump p := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [Work.FTS.EllipticEst.SmoothOpen, hfun]
    exact (contDiffOn_const (c := (-c)) (s := Work.FTS.EllipticEst.Q0)).mul
      Work.FTS.StrongEps.smoothOpen_bump
  -- unconditional scalar homogeneity of the correction term
  have hmul : Work.Spaces.mixed j i (fun z' θ' => (-c) * Work.FTS.StrongEps.bump z' θ') z θ
      = (-c) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
    simp only [Work.Spaces.mixed, DthIter_const_mul (-c) Work.FTS.StrongEps.bump i,
      DzIter_const_mul (-c) (Work.Spaces.DthIter i Work.FTS.StrongEps.bump) j]
  calc Work.Spaces.mixed j i (Work.FTS.StrongEps.Pz f) z θ
      = Work.Spaces.mixed j i
          (fun z θ => f z θ + (-c) * Work.FTS.StrongEps.bump z θ) z θ := by rw [hPz]
    _ = Work.Spaces.mixed j i f z θ
          + Work.Spaces.mixed j i (fun z θ => (-c) * Work.FTS.StrongEps.bump z θ) z θ :=
        Work.FTS.EllipticEst.SmoothOpen.mixed_add hsm hgsm j i z θ hz hθ.1 hθ.2
    _ = Work.Spaces.mixed j i f z θ
          + (-c) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by rw [hmul]
    _ = Work.Spaces.mixed j i f z θ
          - (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump z θ := by
        rw [hc]; ring

end Work.FTS.StrongEps.PZeroAux
end
