import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.horSpec

/-!
# The flat (horospherical) contraction has a fixed point, attained at geometric rate

Let `ξ ∈ Sph n`, `g : PO n 1` with `bd g ξ = ξ`, and suppose that the induced map on the
horosphere at `ξ`,

`F y = yc ξ (g • hptOf ξ y 1)`,

scales flat distances by the factor `λ⁻¹` where `λ = lev ξ (g • 0) > 1` (this is the hypothesis
`hscale`: the flat action is a similarity of ratio `λ⁻¹`).

Then `F` is a strict contraction of the complete space `ξ^⊥` and hence has a fixed point `yinf`,
and moreover every iterate converges to it at the geometric rate:

`‖F^[k] z - yinf‖ = (λ^k)⁻¹ * ‖z - yinf‖`  for every `z ∈ ξ^⊥` and every `k`.

The proof is the Banach fixed point theorem for a contracting map on the complete subset
`ξ^⊥` of the Euclidean space `E n` (`ContractingWith.exists_fixedPoint'`), together with the
observation that `F` maps *all* of `E n` into `ξ^⊥` (`yc_inner_orth`). The rate statement is a
straight induction from the defining similarity identity.
-/

set_option linter.unusedVariables false

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

theorem flatContractionFixed {n : ℕ} (hI : Submission.Mostow.HypIsometryProp n)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (hg : Submission.Mostow.bd g ξ = ξ)
    (hℓ : 1 < Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n)))
    (hscale : ∀ (y y' : Submission.Mostow.E n), inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      ‖Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y (1:ℝ)) - Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y' (1:ℝ))‖
        = (Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n)))⁻¹ * ‖y - y'‖) :
    ∃ yinf : Submission.Mostow.E n, inner ℝ yinf ξ = 0 ∧
      Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ yinf (1:ℝ)) = yinf ∧
      ∀ (z : Submission.Mostow.E n), inner ℝ z ξ = 0 → ∀ k : ℕ,
        ‖(fun y : Submission.Mostow.E n => Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y (1:ℝ)))^[k] z - yinf‖
          = ((Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n))) ^ k)⁻¹ * ‖z - yinf‖ := by
  -- The flat contraction, and its ratio `lam = lev ξ (g • 0) > 1`.
  set F : Submission.Mostow.E n → Submission.Mostow.E n :=
    fun y => Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y (1:ℝ)) with hF
  set lam : ℝ := Work.Mostow.lev ξ (g • (0 : Submission.Mostow.E n)) with hlam
  -- `F` takes values in `ξ^⊥`.
  have hFmem : ∀ y : E n, inner ℝ (F y) ξ = 0 := fun y => yc_inner_orth hξ
  -- The similarity identity, stated for `F` and `lam`.
  have hsc' : ∀ y y' : E n, inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      ‖F y - F y'‖ = lam⁻¹ * ‖y - y'‖ := by
    intro y y' hy hy'
    simpa only [hF] using hscale y y' hy hy'
  have hlam_pos : 0 < lam := lt_trans zero_lt_one hℓ
  -- The flat space `ξ^⊥` is a complete subset of the Euclidean space `E n`.
  set s : Set (E n) := {y : E n | inner ℝ y ξ = 0} with hs
  have hsf : Set.MapsTo F s s := by
    intro y hy
    rw [hs] at hy ⊢
    exact hFmem y
  have hsc : IsComplete s := by
    rw [hs]
    exact (isClosed_eq (continuous_id.inner continuous_const) continuous_const).isComplete
  -- `F` restricted to `ξ^⊥` is a contraction with constant `lam⁻¹ < 1`.
  have hK1 : (⟨lam⁻¹, le_of_lt (inv_pos.mpr hlam_pos)⟩ : NNReal) < 1 := by
    show (lam⁻¹ : ℝ) < 1
    exact inv_lt_one_of_one_lt₀ hℓ
  have hcon : ContractingWith (⟨lam⁻¹, le_of_lt (inv_pos.mpr hlam_pos)⟩ : NNReal)
      (hsf.restrict F s s) := by
    refine ⟨hK1, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro y y'
    rw [Subtype.dist_eq, Subtype.dist_eq]
    have h1 : ((hsf.restrict F s s y : ↥s) : E n) = F (y : E n) :=
      Set.MapsTo.val_restrict_apply hsf y
    have h2 : ((hsf.restrict F s s y' : ↥s) : E n) = F (y' : E n) :=
      Set.MapsTo.val_restrict_apply hsf y'
    rw [h1, h2, dist_eq_norm, hsc' _ _ y.2 y'.2, dist_eq_norm]
    exact le_refl _
  -- Banach's fixed point theorem on the complete subset `ξ^⊥`.
  obtain ⟨yinf, hyinf_mem, hyinf_fix, -, -⟩ :=
    hcon.exists_fixedPoint' hsc hsf (show (0 : E n) ∈ s from by rw [hs]; simp)
      (by rw [edist_dist]; exact ENNReal.ofReal_ne_top)
  -- One step of `F` contracts the distance to `yinf` by `lam⁻¹`.
  have hstep : ∀ y : E n, inner ℝ y ξ = 0 → ‖F y - yinf‖ = lam⁻¹ * ‖y - yinf‖ := by
    intro y hy
    have h := hsc' y yinf hy hyinf_mem
    rwa [hyinf_fix] at h
  refine ⟨yinf, hyinf_mem, hyinf_fix, ?_⟩
  intro z hz k
  have hzmem : z ∈ s := by rw [hs]; exact hz
  have hiter : ∀ k : ℕ, F^[k] z ∈ s := by
    intro k
    induction k with
    | zero => simpa using hzmem
    | succ k ih => rw [Function.iterate_succ_apply']; exact hsf ih
  have hmain : ∀ k : ℕ, ‖F^[k] z - yinf‖ = (lam ^ k)⁻¹ * ‖z - yinf‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hstep _ (hiter k).out, ih, pow_succ, mul_inv,
        ← inv_pow lam k]
      ring
  exact hmain k

end Work.Mostow
