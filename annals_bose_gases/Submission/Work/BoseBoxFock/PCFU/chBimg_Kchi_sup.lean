import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PCFU.KfrU_pairing_uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseBoxFock.PCFU.chBimg_Kchi_sup` — a **uniform** sup bound on the `χ̂`-weighted `k`-frame

The `(B)`/`(D)` slots of the cubic dictionary (`ChWordChains`) carry the single-variable factor
`F = KχfrU − Ĉ`, and their estimate (§5.2 of `FINDING_PotCubicFreeU_exists_session15.md`) is the
pointwise (SV) bound, whose only content is a **sup bound** on the frame
`KχfrU v h μ fu N z = Σ_{k : Lab N} Ŵ₁(k)χ̂(ℓk)e^{i⟪κ_k,z⟫}`.  The present module supplies it:

    `∃ C, 0 ≤ C ∧ ∀ μ, 0 < μ → R ≤ ℓ·chiR0 → 2R ≤ ℓ → ∀ N z, ‖KχfrU v h μ fu N z‖ ≤ C`,

with `C` **independent of `μ`, `N`, `z`** (and of the cut-offs `fu`, in fact).

## Why this is true (and how it is proved)

`KχfrU` is a *finite* trigonometric polynomial with coefficients `w_k = Ŵ₁(k)χ̂(ℓk)`, so

    ‖KχfrU z‖ ≤ Σ_{k : Lab N} |w_k| ≤ (sup_k |Ŵ₁(k)|) · Σ_{k : Lab N} |χ̂(ℓk)| ,

and the two factors are bounded **uniformly**:

* `sup_k |Ŵ₁(k)| ≤ ∫|W₁|` (`KfrU_aux_W1h_abs_le`, from `|ζ| ≤ 1` and
  `|chat W| ≤ ∫|W|`; no hypotheses needed — both sides are `0` in the junk case), and
  `∫ |W₁| ≤ 2∫|g₀|` **in the dilute regime `R ≤ ℓ·chiR0`**: `W₁ = g₀/(χ⋆χ)(·/ℓ)` with `g₀` supported
  in `ball 0 R` (`tsupport_W1fun_subset`), where `(χ⋆χ)(·/ℓ) ≥ 1/2`
  (`convScale_ge_half_ball`), so `|W₁| ≤ 2|g₀|` pointwise and `g₀ ∈ L¹`
  (`g0_integrable`).  This is the point where the hypothesis `R ≤ ℓ·chiR0` is *used*; the second
  hypothesis `2R ≤ ℓ` of the target is not needed.
* `Σ_{k : Lab N} |χ̂(ℓ κ_k)| ≤ Cχ` is an **absolute** constant: `ℓ κ_k = 2π·(labVec N k)` is the
  `v, μ, N`-independent dual-lattice vector, and `χ̂` decays like `(1+‖p‖²)^{-3}`
  (`hatChih_sum_le`, `ChiReg_corpus`).

(⚠ The companion `Σ_k |Ŵ₁(k)|² ≤ Cℓ³` is **false** — `W1fun` need not be in `L²`
(FINDING §7) — so no `L²`-of-the-box route is available; the `ℓ¹`-in-`χ̂` route above is the one
that works.)

## The helper in this file

* `W1fun_integral_abs_uniform` — the uniform `L¹` bound `∫|W₁| ≤ 2∫|g₀|` in the dilute regime.
-/

/-- **The uniform `L¹` mass of the renormalised kernel.**  In the dilute regime `R ≤ ℓ·chiR0` the
denominator `(χ⋆χ)(·/ℓ)` is `≥ 1/2` on `ball 0 R ⊇ supp g₀`, so `|W₁| ≤ 2|g₀|` pointwise and the
`L¹` mass of `W₁` is dominated by twice that of `g₀` — *uniformly in* `ℓ`. -/
theorem W1fun_integral_abs_uniform {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    ∫ x : E3, |Work.BoseFixR.W1fun v h ℓ x| ≤ 2 * ∫ x : E3, |Submission.BoseGases.g0 v h x| := by
  have hg0int : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hpt : ∀ x : E3, |Work.BoseFixR.W1fun v h ℓ x| ≤ 2 * |Submission.BoseGases.g0 v h x| :=
    fun x => by
      simpa [Work.BoseFixR.W1fun] using
        Submission.BoseGases.wScaled_abs_le_two hℓ hR.le hRℓ
          (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) x
  have h2 := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x : E3 => abs_nonneg _))
    (hg0int.abs.const_mul 2) (Filter.Eventually.of_forall hpt)
  rwa [integral_const_mul] at h2

/-- **The uniform sup bound on the `χ̂`-weighted `k`-frame** — FS's `(B)`/`(D)` slot factor. -/
theorem chBimg_Kchi_sup (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hav : 0 < BoseGases.a v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (fu : Work.BoseBoxFix.LowCut) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : ℝ), 0 < μ →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
      2 * R ≤ Work.BoseBoxFock.ellH v μ →
      ∀ (N : ℕ) (z : EuclideanSpace ℝ (Fin 3)),
        ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z‖ ≤ C := by
  have _ := hv
  have _ := hv1
  have _ := hvrad
  obtain ⟨Cχ, hCχ0, hCχ⟩ := Work.BoseBoxFock.PCFU.hatChih_sum_le
  refine ⟨(2 * ∫ x : E3, |Submission.BoseGases.g0 v h x|) * Cχ, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (by norm_num) (integral_nonneg (fun x => abs_nonneg _))) hCχ0
  · intro μ hμ hRℓ _h2R N z
    -- `ellH v μ = sideAt μ (a v)` at the admissible `μ`, and the dilute regime in this form
    have hsidepos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
    have hellH : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
      rw [Work.BoseBoxFock.ellH, if_pos hsidepos]
    rw [hellH] at hRℓ
    -- the uniform `L¹` bound on `W₁`, hence on every coefficient `Ŵ₁(k)χ̂(ℓk)`
    have hW1 : ∫ x : E3, |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (BoseGases.a v)) x|
        ≤ 2 * ∫ x : E3, |Submission.BoseGases.g0 v h x| :=
      W1fun_integral_abs_uniform h hR hv_supp hsidepos hRℓ
    have hCw2 : 0 ≤ 2 * ∫ x : E3, |Submission.BoseGases.g0 v h x| :=
      mul_nonneg (by norm_num) (integral_nonneg (fun x => abs_nonneg _))
    -- the finite trigonometric sum, coefficient by coefficient
    calc ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z‖
        ≤ ∑ k : Lab N,
            ‖((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℂ))‖ :=
          norm_sum_le _ _
      _ = ∑ k : Lab N, |W1h v h μ fu N k * hatChih v μ N k| := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [norm_mul, Complex.norm_exp]
          simp
      _ ≤ ∑ k : Lab N, (2 * ∫ x : E3, |Submission.BoseGases.g0 v h x|) * |hatChih v μ N k| := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (le_trans (Work.BoseBoxFock.PCFU.KfrU_aux_W1h_abs_le h μ fu N k) hW1) (abs_nonneg _)
      _ = (2 * ∫ x : E3, |Submission.BoseGases.g0 v h x|)
            * ∑ k : Lab N, |hatChih v μ N k| := by
          rw [Finset.mul_sum]
      _ ≤ (2 * ∫ x : E3, |Submission.BoseGases.g0 v h x|) * Cχ :=
          mul_le_mul_of_nonneg_left (hCχ v μ N) hCw2

end Work.BoseBoxFock.PCFU
