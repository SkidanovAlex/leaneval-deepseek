import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `high_slice_chain_slots`: the high angular slots of `Ψ` are controlled by `|F|_k`

The target is the estimate

`∑_{j ∈ Icc 3 (k+1)} ∫_z w² ∫_θ (∂_θ^j Ψ)² sin(2θ)^{2j-4-γ} ≤ C · HkSq α k F`

for data of the weak class `EllWeakPos α k F Ψ`, `0 < α ≤ 1/4`, `k ≥ 2`, under the single
norm hypothesis `‖∂_θ²Ψ‖_{k-1} ≤ D ‖F‖_k`; the constant `C` depends only on `k` and `D`.

The mathematically essential point (`NOTES_high_slice_chain_FALSE.md`) is that the *sharp*
expansion of `D_θ` (`dthCoef`) has no `∂_θ^0`-term as soon as `D_θ` has been applied once
(`dthCoef_succ_zero`); hence `∂_θ^jΨ` (`j ≥ 3`) is a triangular combination of the
`D_θ`-slots `D_θ^r(∂_θ²Ψ)`, `1 ≤ r ≤ j-2`, of the *sibling* function `∂_θ²Ψ` — exactly the
slots whose `w² sin(2θ)^{-γ}`-masses are the summands of `HkSq α (k-1) (∂_θ²Ψ)`.  The
`j = 2` summand (the pure `γ`-slot of `∂_θ²Ψ`) is deliberately absent from the sum: it is
*not* controlled by `HkSq`, which is what made the sibling `high_slice_chain` false.

The two analytic/syntactic pieces are proved in the sibling modules

* `remov.high_chain_sum_self` — `∑_{m ∈ Icc 1 K} ∫_z w² ∫_θ (∂_θ^m v)² sin(2θ)^{2m-γ}
  ≤ C_K |v|²_{H^K}` for `v` smooth on the open quadrant with `HkMem α K v` (constant
  independent of `α`).  (The same statement is proved by the colleagues of
  `remov.high_chain_sum`; the `_self` copy is used here because the import cone of that
  module is temporarily broken by an unrelated, in-flight file of another area,
  `Submission.Work.EllipticEst.EllHyp_hkMem_V_fts`.  The statement is unchanged.)
* the reindexing `j = m + 2`, i.e. `∂_θ^{m+2}Ψ = ∂_θ^m (∂_θ²Ψ)`, which is proved locally
  below (`high_slice_sum_reindex_local`) so that this file's import cone stays clean.

Here we only assemble: `HkMem α (k-1) (∂_θ²Ψ)` is obtained from the given
`HkMem α k (∂_θ²Ψ)` (`EllWeakPos.memB`) by the open-quadrant descent
`Work.FTS.EllipticEst.TT.HkMem_descend_open`, the squared norms are compared with
`HkNorm`-bounds, and the two norms are matched by the given hypothesis.
-/

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The open quadrant `(0,∞) × (0,π/2)`; the regularity class of `EllWeakPos.smooth`. -/
abbrev Qd2 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_Qd2 : IsOpen Qd2 := isOpen_Ioi.prod isOpen_Ioo

/-! ## Elementary `HkNorm`/`HkSq` bookkeeping -/

/-- `HkSq` is the square of `HkNorm`. -/
theorem HkSq_eq_HkNorm_sq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k f = (Work.Spaces.HkNorm α k f) ^ 2 := by
  rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k f)]

/-- A bound of `HkNorm`s at possibly different orders gives the corresponding bound of
`HkSq`s. -/
theorem HkSq_le_of_HkNorm_le {α : ℝ} {k l : ℕ} {f g : ℝ → ℝ → ℝ} {D : ℝ} (_hD : 0 ≤ D)
    (h : Work.Spaces.HkNorm α k f ≤ D * Work.Spaces.HkNorm α l g) :
    Work.Spaces.HkSq α k f ≤ D ^ 2 * Work.Spaces.HkSq α l g := by
  rw [HkSq_eq_HkNorm_sq, HkSq_eq_HkNorm_sq]
  calc (Work.Spaces.HkNorm α k f) ^ 2
      ≤ (D * Work.Spaces.HkNorm α l g) ^ 2 :=
        pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α k f) h 2
    _ = D ^ 2 * (Work.Spaces.HkNorm α l g) ^ 2 := by ring

/-! ## Finite-order smoothness of `∂_θ` -/

/-- The partial `θ`-derivative of a function that is `C^{n+1}` on the open quadrant is `C^n`
there.  (`Work.Spaces.contDiffOn_uncurry_pth` is the corresponding `C^∞` statement, which is
*not* applicable: in the `ContDiff` notation `⊤` denotes analyticity `ω`, while the class of
`EllWeakPos` is finite-order smoothness.) -/
theorem contDiffOn_uncurry_pth_fin_Qd {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) Qd2) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) Qd2 := by
  have key : ∀ (z θ : ℝ), (z, θ) ∈ Qd2 →
      Work.Spaces.pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) :=
    fun z θ hzθ => Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (by norm_num : (n + 1 : WithTop ℕ∞) ≠ 0)).differentiableAt
        (isOpen_Qd2.mem_nhds hzθ))
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) Qd2 :=
    h.fderiv_of_isOpen isOpen_Qd2 (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) Qd2 :=
    hfd.clm_apply contDiffOn_const
  refine hcomp.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  exact key z θ hp

/-- `∂_θ²Ψ = pthIter 2 Ψ` is `C^n` on the open quadrant for every `n` as soon as `Ψ` is. -/
theorem smooth_pthIter_two (Ψ : ℝ → ℝ → ℝ)
    (h : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ) Qd2) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Qd2 := by
  intro n
  have h1 : ContDiffOn ℝ (n + 2) (Function.uncurry Ψ) Qd2 := h (n + 2)
  have h2 : ContDiffOn ℝ (n + 1) (Function.uncurry (Work.Spaces.pth Ψ)) Qd2 := by
    have := contDiffOn_uncurry_pth_fin_Qd (n := n + 1) h1
    simpa using this
  have h3 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth Ψ))) Qd2 := by
    have := contDiffOn_uncurry_pth_fin_Qd (n := n) h2
    simpa using this
  exact h3

/-! ## The reindexing of the high angular slots -/

/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
theorem pthIter_add_local (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- The on-the-nose exponent bookkeeping of the reindexing `j = m + 2`. -/
theorem two_mul_add_two_sub_four (m : ℕ) (α : ℝ) :
    2 * ((m + 2 : ℕ) : ℝ) - 4 - Work.Spaces.gam α = 2 * (m : ℝ) - Work.Spaces.gam α := by
  push_cast
  ring

/-- **Reindexing the high angular slots.**  For `k ≥ 2` the sum over `j ∈ Icc 3 (k+1)` of the
high angular slots of `Ψ` is the sum over `m ∈ Icc 1 (k-1)` of the same slots of
`v = ∂_θ²Ψ`: the substitution is `j = m + 2`, and on matched indices
`pthIter (m+2) Ψ = pthIter m (pthIter 2 Ψ)` while
`2 * ((m+2 : ℕ) : ℝ) - 4 - gam α = 2 * (m : ℝ) - gam α`. -/
theorem high_slice_sum_reindex_local (k : ℕ) (hk : 2 ≤ k) (α : ℝ) (Ψ : ℝ → ℝ → ℝ) :
    (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - Work.Spaces.gam α)))
    = (∑ m ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter m (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 * (m : ℝ) - Work.Spaces.gam α))) := by
  have himage : (Finset.Icc 1 (k - 1)).image (fun m => m + 2) = Finset.Icc 3 (k + 1) := by
    have h := Finset.image_add_right_Icc (α := ℕ) 1 (k - 1) 2
    have h2 : (k - 1) + 2 = k + 1 := by omega
    rw [show 1 + 2 = 3 from rfl, h2] at h
    exact h
  have hinj : Set.InjOn (fun m : ℕ => m + 2) (↑(Finset.Icc 1 (k - 1)) : Set ℕ) :=
    fun a _ b _ hab => Nat.add_right_cancel hab
  rw [← himage, Finset.sum_image hinj]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [pthIter_add_local m 2 Ψ, two_mul_add_two_sub_four m α]

/-! ## The target -/

theorem high_slice_chain_slots (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ) ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      (∑ j ∈ Finset.Icc 3 (k + 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter j Ψ z θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 * (j : ℝ) - 4 - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k F := by
  intro k hk
  obtain ⟨C0, hC0pos, hC0⟩ := high_chain_sum_self (k - 1)
  refine ⟨C0 * D ^ 2 + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hpos h1 h2
  -- the regularity of `v = ∂_θ²Ψ` on the open quadrant, at every finite order
  have hsmooth : ∀ n : ℕ, ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Qd2 :=
    smooth_pthIter_two Ψ (fun n => hpos.smooth n)
  -- `HkMem` descends from the given order `k` to the order `k-1` of the chain
  have hmemK : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := hpos.memB
  have hmemL : Work.Spaces.HkMem α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (Nat.sub_le k 1) hsmooth hmemK
  -- the angular chain at level `k-1`, uniform in `α`
  have hchain := hC0 α (Work.Spaces.pthIter 2 Ψ) hα hsmooth hmemL
  -- the reindexing `j = m + 2`
  have hreindex := high_slice_sum_reindex_local k hk α Ψ
  -- the norm hypothesis, squared
  have hsq : Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ D ^ 2 * Work.Spaces.HkSq α k F := HkSq_le_of_HkNorm_le hD.le h1
  rw [hreindex]
  refine le_trans hchain ?_
  refine le_trans (mul_le_mul_of_nonneg_left hsq hC0pos.le) ?_
  have hnn : 0 ≤ Work.Spaces.HkSq α k F := Work.Spaces.HkSq_nonneg α k F
  nlinarith [hC0pos, sq_nonneg D]

end Work.FTS.EllipticEst.remov
