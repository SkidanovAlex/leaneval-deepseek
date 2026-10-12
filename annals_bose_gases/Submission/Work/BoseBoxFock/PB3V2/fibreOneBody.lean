import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PB3Frame
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3V2.fibreOneBody` — the one-body ("one fibre") tail of the block-III frame

The block-III comparison of `Work.BoseBoxFock.pairRowB3` compares the *limit* slot form
`∫ χ_ℓ²‖mf ℓ f‖²` with the truncated frame sum `Σ_{k ∈ labSet N}‖⟪pinQInf ℓ k, f⟫‖²`.  The
difference is the **tail of the frame** above the cutoff, and this file proves the one-body
version of the tail bound that the assembly needs:

    ∫_w χ_ℓ(w)²‖mf ℓ f(w)‖² − Σ_{k ∈ labSet N}‖⟪pinQInf ℓ k, f⟫‖²
      ≤ Λ⁻² · (2π)⁻³ ∫_p ‖p‖²‖kinFT (χ_ℓ·mf ℓ φ)(p)‖² ,

for `f ∈ L²`, `φ ∈ C¹` agreeing with `f` on the box `boxL ℓ`, and every label `k` *outside*
`labSet N` carrying momentum at least `Λ`.

## Route (three steps, all from proved corpus lemmas)

1. **Parseval / tight frame.**  `PB3Frame` gives
   `HasSum (k ↦ ‖⟪pinQInf ℓ k, f⟫‖²) (∫ χ_ℓ²‖mf ℓ f‖²)`.  Splitting off the finite set
   `labSet N` (`Summable.sum_add_tsum_subtype_compl`) identifies the left-hand side of the target
   with the `tsum` of the same (nonnegative) family over the *complement* subtype
   `{k // k ∉ labSet N}`.
2. **Dictionary + agreement on the box.**  For each label, `norm_pinQInf_inner` reads the pairing as
   the Fourier sample of the windowed mean-free part, `‖⟪pinQInf ℓ k, f⟫‖² = ℓ⁻³‖ĝ(κ_k)‖²` with
   `ĝ = kinFT (χ_ℓ·mf ℓ f)`.  On the support of `χ_ℓ` (which lies in `boxL ℓ`) the mean-free parts
   of `f` and `φ` coincide — `χ_ℓ·mf ℓ f = χ_ℓ·mf ℓ φ` pointwise — so `ĝ = kinFT (χ_ℓ·mf ℓ φ)`.
3. **High-mode tail.**  For a finite set of labels all outside `labSet N` the hypothesis `hΛk`
   gives `Λ ≤ ‖κ_k‖`, and `L1Tails.highModeTail` bounds the finite partial sums by
   `ℓ³/Λ²·(2π)⁻³∫_p ‖p‖²‖ĝ(p)‖²`.  Multiplying by `ℓ⁻³` and passing to the supremum of finite
   partial sums (`Real.tsum_le_of_sum_le`) gives the bound for the complement `tsum`.

The continuity hypotheses enter only through `chiMf_contDiff` / `chiMf_tsupport_subset` (the
`C¹` windowed mean-free part is `C¹` with support in the box), and `MemLp` through `PB3Frame`.
-/

namespace Work.BoseBoxFock.PB3V2

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000

/-- **The windowed mean-free part only sees `f` on the box.**  If `f = φ` on `boxL ℓ` then
`χ_ℓ·mf ℓ f = χ_ℓ·mf ℓ φ` pointwise: the subtracted box means agree, and where `χ_ℓ ≠ 0` the
point `x` itself lies in the box, so `f x = φ x`. -/
theorem chiScale_mul_mf_congr {ℓ : ℝ} (hℓ : 0 < ℓ) {f φ : E3 → ℂ}
    (hagree : ∀ w ∈ Work.BoseK15.corpusBox.boxL ℓ, f w = φ w) (x : E3) :
    ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ f x
      = ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ φ x := by
  have hint : ∫ y in Work.BoseK15.corpusBox.boxL ℓ, f y
      = ∫ y in Work.BoseK15.corpusBox.boxL ℓ, φ y :=
    setIntegral_congr_fun (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ)
      hagree
  by_cases hx : Submission.BoseGases.chiScale ℓ x = 0
  · rw [hx, Complex.ofReal_zero, zero_mul, zero_mul]
  · have hmem : x ∈ Work.BoseK15.corpusBox.boxL ℓ :=
      Work.BoseBoxFock.support_chiScale_subset hℓ (Function.mem_support.mpr hx)
    have hfx : f x = φ x := hagree x hmem
    have hmfeq : Work.BoseBoxFock.mf ℓ f x = Work.BoseBoxFock.mf ℓ φ x := by
      simp only [Work.BoseBoxFock.mf, hfx, hint]
    rw [hmfeq]

theorem fibreOneBody {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ) {N : ℕ}
    (hΛk : ∀ k : Fin 3 → ℤ, k ∉ Work.BoseBoxFock.labSet N → Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ k‖)
    {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    {φ : EuclideanSpace ℝ (Fin 3) → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hagree : ∀ w ∈ Work.BoseK15.corpusBox.boxL ℓ, f w = φ w) :
    (∫ w : EuclideanSpace ℝ (Fin 3),
        (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖Work.BoseBoxFock.mf ℓ f w‖ ^ 2)
      - ∑ k ∈ Work.BoseBoxFock.labSet N,
          ‖∫ x : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k x) * f x‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
            ‖Submission.BoseGases.kinFT
              (fun w : EuclideanSpace ℝ (Fin 3) =>
                ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ φ w) p‖ ^ 2) := by
  classical
  set gg : E3 → ℂ :=
    fun x => ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ φ x with hggdef
  have hgc : ContDiff ℝ 1 gg := by
    rw [hggdef]; exact Work.BoseBoxFock.chiMf_contDiff hℓ hφ
  have hgs : tsupport gg ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
    rw [hggdef]; exact Work.BoseBoxFock.chiMf_tsupport_subset hℓ φ
  have hgg : ∀ x : E3,
      ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ f x = gg x := by
    intro x
    rw [chiScale_mul_mf_congr hℓ hagree x, hggdef]
  -- step 1: Parseval, and the splitting off of the finite label set
  have hHas : HasSum (fun k : Fin 3 → ℤ =>
      ‖∫ x : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k x) * f x‖ ^ 2)
      (∫ x : E3, (Submission.BoseGases.chiScale ℓ x) ^ 2 * ‖Work.BoseBoxFock.mf ℓ f x‖ ^ 2) :=
    (Work.BoseBoxFock.PB3Frame (ℓ := ℓ) hℓ (f := f) hf 0).2.1
  have hsumcompl : ∑ k ∈ Work.BoseBoxFock.labSet N,
        ‖∫ x : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k x) * f x‖ ^ 2
      + ∑' (k : {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N}),
        ‖∫ x : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k.1 x) * f x‖ ^ 2
      = ∫ x : E3, (Submission.BoseGases.chiScale ℓ x) ^ 2 * ‖Work.BoseBoxFock.mf ℓ f x‖ ^ 2 := by
    rw [← hHas.tsum_eq]
    exact hHas.summable.sum_add_tsum_subtype_compl (Work.BoseBoxFock.labSet N)
  -- steps 2 and 3: the finite partial sums of the complement
  have hkey : ∀ u : Finset {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N},
      ∑ k ∈ u, ‖∫ x : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k.1 x) * f x‖ ^ 2
        ≤ (Λ ^ 2)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 *
            ‖Submission.BoseGases.kinFT gg p‖ ^ 2) := by
    intro u
    have hfun : (fun x : E3 =>
        ((Submission.BoseGases.chiScale ℓ x : ℝ) : ℂ) * Work.BoseBoxFock.mf ℓ f x) = gg :=
      funext hgg
    have hterm : ∀ k ∈ u,
        ‖∫ x : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k.1 x) * f x‖ ^ 2
          = (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT gg (Work.BoseBoxFock.kappaL ℓ k.1)‖ ^ 2 := by
      intro k _
      rw [Work.BoseBoxFock.norm_pinQInf_inner (ℓ := ℓ) hℓ (f := f) hf k.1, hfun]
    have hS : ∀ n ∈ u.image (Subtype.val :
        {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N} → (Fin 3 → ℤ)),
        Λ ≤ ‖Work.BoseBoxFock.kappaL ℓ n‖ := by
      intro n hn
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hn
      exact hΛk k.1 k.2
    have htail := Work.BoseBoxFock.L1Tails.highModeTail hℓ hΛ hgc hgs
      (u.image (Subtype.val :
        {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N} → (Fin 3 → ℤ))) hS
    have hsum2 : ∑ k ∈ u, ‖Submission.BoseGases.kinFT gg (Work.BoseBoxFock.kappaL ℓ k.1)‖ ^ 2
        = ∑ n ∈ u.image (Subtype.val :
            {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N} → (Fin 3 → ℤ)),
            ‖Submission.BoseGases.kinFT gg (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 :=
      (Finset.sum_image (s := u) (g := (Subtype.val :
          {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N} → (Fin 3 → ℤ)))
        (f := fun n => ‖Submission.BoseGases.kinFT gg (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2)
        (fun a _ b _ h => Subtype.ext h)).symm
    calc ∑ k ∈ u, ‖∫ x : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k.1 x) * f x‖ ^ 2
        = (ℓ ^ 3)⁻¹ * ∑ k ∈ u,
            ‖Submission.BoseGases.kinFT gg (Work.BoseBoxFock.kappaL ℓ k.1)‖ ^ 2 := by
          rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      _ = (ℓ ^ 3)⁻¹ * ∑ n ∈ u.image (Subtype.val :
            {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N} → (Fin 3 → ℤ)),
            ‖Submission.BoseGases.kinFT gg (Work.BoseBoxFock.kappaL ℓ n)‖ ^ 2 := by rw [hsum2]
      _ ≤ (ℓ ^ 3)⁻¹ * (ℓ ^ 3 / Λ ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 *
            ‖Submission.BoseGases.kinFT gg p‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (Λ ^ 2)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 *
            ‖Submission.BoseGases.kinFT gg p‖ ^ 2) := by
          field_simp
  have hcompl : ∑' (k : {k : Fin 3 → ℤ // k ∉ Work.BoseBoxFock.labSet N}),
        ‖∫ x : E3, (starRingEnd ℂ) (Work.BoseBoxFock.pinQInf ℓ k.1 x) * f x‖ ^ 2
      ≤ (Λ ^ 2)⁻¹ * (((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ‖p‖ ^ 2 *
          ‖Submission.BoseGases.kinFT gg p‖ ^ 2) :=
    Real.tsum_le_of_sum_le (fun _ => by positivity) hkey
  linarith [hsumcompl, hcompl]

end Work.BoseBoxFock.PB3V2
