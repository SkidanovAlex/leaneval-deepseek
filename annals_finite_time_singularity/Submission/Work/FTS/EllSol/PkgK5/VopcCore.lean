import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.EllSol.PkgK5.divSinK5
import Submission.Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smooth
import Submission.Work.FTS.EllipticEst.RPFresh.straight_transfers

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
