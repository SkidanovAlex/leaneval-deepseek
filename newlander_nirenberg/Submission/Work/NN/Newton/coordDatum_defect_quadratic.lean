import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.NormAux
import Submission.Work.NN.Newton.Defect.dOne_dbarCn_zcoord
import Submission.Work.NN.Newton.Defect.almostComplex_relation
import Submission.Work.NN.Newton.Defect.ddbar_coordDatum_expansion
import Submission.Work.NN.Newton.Defect.defect_algebra
import Submission.Work.NN.Newton.Defect.holderNorm_LD_field_fixed
import Submission.Work.NN.Newton.Defect.holderNorm_A_LD_fixed
import Submission.Work.NN.Newton.Defect.holderNorm_LD_field_field
import Submission.Work.NN.Newton.Defect.holderNorm_TA

/-!
# Integrability makes the flat `∂̄`-defect of the coordinate datum quadratic

The main identity proved here is pointwise: on the open polydisc `P_r`, for an almost complex
structure `J = Jstd + A` (`(Jstd + A)² = -1`) which is *integrable* (`proj02 J (d ∂̄_J u) = 0` for
every smooth `u`), the flat `∂̄`-defect of the coordinate datum `F^{(l)}_m = Lcoef A (·l) m` is
`-(i/8)·TA`, where `TA` is a sum of ten terms each of which is a product of an entry of `A` with an
entry of `DA`.  Hence the defect is `O(a²)` in the `C^{1,α}`-size `a` of `A`.

The route: the integrability identity `0 = proj02 J (d ∂̄_J z_l) z e_j e_k` is `(i/8)·E = 0` with
`E = 2·defectExpr + TA`; the differential relation `(DA_X) ∘ J + J ∘ (DA_X) = 0` obtained from
`J² = -1` is what turns the linear part `2·defectExpr` into the quadratic remainder `TA`.
-/

namespace Work.NN.Newton

open scoped ContDiff
open Set

noncomputable section

variable {n : ℕ}

/-- **The pointwise quadratic-defect identity.**  On the open polydisc, the flat `∂̄`-defect of the
coordinate datum of `z_l` equals `-(i/8)` times the explicit quadratic remainder `TA`. -/
theorem coordDatum_defect_pointwise
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) {r : ℝ} (hr : 0 < r)
    (hA : ∀ m : ℕ, ContDiffOn ℝ m A (polydiscR n r))
    (hac : ∀ z ∈ polydiscR n r, ∀ v,
      (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v)
    (hint : ∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
      ∀ z ∈ polydiscR n r, ∀ V W : Work.NN.Core.Cn n,
        Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
          (fun z' => Work.NN.Final.dOne
            (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z') z V W = 0)
    (l j k : Fin n) {z : Work.NN.Core.Cn n} (hz : z ∈ polydiscR n r) :
    Work.NN.Final.ddbar (Work.NN.Core.JstdCn n) (coordDatum A l) j k z
      = -(Complex.I / 8) * TA A z l j k := by
  have hA1 : ContDiffOn ℝ 1 A (polydiscR n r) := hA 1
  have hdA : DifferentiableAt ℝ A z :=
    (hA1.contDiffAt ((isOpen_polydiscR n r).mem_nhds hz)).differentiableAt (by norm_num)
  have hu : ∀ k : ℕ, ContDiff ℝ k (fun y : Work.NN.Core.Cn n => y l) := fun k =>
    (ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ).contDiff
  have hE0 := hint (fun y : Work.NN.Core.Cn n => y l) hu z hz (evec j) (evec k)
  -- `proj02` unfolds to one quarter of the alternating sum of the four `dOne` terms
  have key2 : (1 / 4) *
      (Work.NN.Final.dOne
          (fun z' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
            (fun y : Work.NN.Core.Cn n => y l) z') z (evec j) (evec k)
        + Complex.I * Work.NN.Final.dOne
          (fun z' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
            (fun y : Work.NN.Core.Cn n => y l) z') z
          ((Work.NN.Core.JstdCn n + A) z (evec j)) (evec k)
        + Complex.I * Work.NN.Final.dOne
          (fun z' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
            (fun y : Work.NN.Core.Cn n => y l) z') z (evec j)
          ((Work.NN.Core.JstdCn n + A) z (evec k))
        - Work.NN.Final.dOne
          (fun z' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A)
            (fun y : Work.NN.Core.Cn n => y l) z') z
          ((Work.NN.Core.JstdCn n + A) z (evec j)) ((Work.NN.Core.JstdCn n + A) z (evec k)))
      = (Complex.I / 8) * Eexpr A z l j k := by
    rw [Work.NN.Newton.Defect.dOne_dbarCn_zcoord A l hdA (evec j) (evec k),
      Work.NN.Newton.Defect.dOne_dbarCn_zcoord A l hdA
        ((Work.NN.Core.JstdCn n + A) z (evec j)) (evec k),
      Work.NN.Newton.Defect.dOne_dbarCn_zcoord A l hdA (evec j)
        ((Work.NN.Core.JstdCn n + A) z (evec k)),
      Work.NN.Newton.Defect.dOne_dbarCn_zcoord A l hdA
        ((Work.NN.Core.JstdCn n + A) z (evec j))
        ((Work.NN.Core.JstdCn n + A) z (evec k))]
    simp only [Eexpr]
    ring_nf
  have hEE : (Complex.I / 8) * Eexpr A z l j k = 0 := by
    rw [← key2]
    exact hE0
  have hE : Eexpr A z l j k = 0 := by
    rcases mul_eq_zero.mp hEE with h | h
    · exact absurd h (div_ne_zero Complex.I_ne_zero (by norm_num))
    · exact h
  have hrel : ∀ X Y : Work.NN.Core.Cn n,
      (fderiv ℝ A z X) ((Work.NN.Core.JstdCn n + A) z Y)
        = -((Work.NN.Core.JstdCn n + A) z ((fderiv ℝ A z X) Y)) :=
    fun X Y => Work.NN.Newton.Defect.almostComplex_relation A hr hA1 hac hz X Y
  rw [Work.NN.Newton.Defect.ddbar_coordDatum_expansion A l j k hdA,
    Work.NN.Newton.Defect.defect_algebra A z l j k hrel hE]
  ring

/-- **Integrability makes the flat `∂̄`-defect of the coordinate datum quadratic.**

Let `J = Jstd + A` be smooth, almost complex and integrable on the polydisc `P` of radius `r`, and
let `a` bound the `C^{1,α}`-norm on `P` of every coefficient `z ↦ A z w j` (`‖w‖ ≤ 1`).  The
coordinate datum of `z_l` is the `(0,1)`-form `F_m = Lcoef A z_l m = (i/2) (A z e_m)_l`; its flat
`∂̄`-defect `∂̄_j F_k - ∂̄_k F_j` is of size `a²` in `C^{0,α}(P)` (it is a bilinear expression in
`A` and `DA`, the linear part being the Nijenhuis tensor, which vanishes). -/
theorem coordDatum_defect_quadratic {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 / 2 ≤ r → r ≤ 4 →
      ∀ A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ m : ℕ, ContDiffOn ℝ m A
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          ∀ v : Work.NN.Core.Cn n,
            (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        (∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
          ∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
            ∀ V W : Work.NN.Core.Cn n,
              Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
                (fun z' => Work.NN.Final.dOne
                  (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z')
                z V W = 0) →
        ∀ a : ℝ, 0 ≤ a → a ≤ 1 →
        (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
          Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal a) →
        ∀ l j k : Fin n,
          Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Final.ddbar (Work.NN.Core.JstdCn n)
              (fun m y => Work.NN.Core.Lcoef A (fun y' => y' l) m y) j k z)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal (C * a ^ 2) := by
  refine ⟨13, by norm_num, ?_⟩
  intro r hr1 hr2 A hA hac hint a ha0 ha1 hcoef l j k
  have hr : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hAcoef : CVBound A α a (polydiscR n r) := hcoef
  have hAc : ∀ m : ℕ, ContDiffOn ℝ m A (polydiscR n r) := hA
  -- the pointwise identity, hence equality of the two `C^{0,α}`-norms
  have hpt : ∀ z ∈ polydiscR n r,
      Work.NN.Final.ddbar (Work.NN.Core.JstdCn n)
        (fun m y => Work.NN.Core.Lcoef A (fun y' => y' l) m y) j k z
        = -(Complex.I / 8) * TA A z l j k :=
    fun z hz => coordDatum_defect_pointwise A hr hA hac hint l j k hz
  have hcongr := Work.NN.Newton.holderNorm_congrOn (k := 0) (α := α) (Ω := polydiscR n r) hpt
  have hnorm : ‖(-(Complex.I / 8) : ℂ)‖ = 1 / 8 := by
    rw [norm_neg, norm_div, Complex.norm_I]
    norm_num
  calc Work.CR.Flat.holderNorm 0 α
        (fun z => Work.NN.Final.ddbar (Work.NN.Core.JstdCn n)
          (fun m y => Work.NN.Core.Lcoef A (fun y' => y' l) m y) j k z)
        (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
      = Work.CR.Flat.holderNorm 0 α (fun z => -(Complex.I / 8) * TA A z l j k)
          (polydiscR n r) := hcongr
    _ ≤ ENNReal.ofReal ‖(-(Complex.I / 8) : ℂ)‖
          * Work.CR.Flat.holderNorm 0 α (fun z => TA A z l j k) (polydiscR n r) :=
        Work.NN.Newton.holderNorm_zero_const_mul_le
    _ = ENNReal.ofReal (1 / 8)
          * Work.CR.Flat.holderNorm 0 α (fun z => TA A z l j k) (polydiscR n r) := by
        rw [hnorm]
    _ ≤ ENNReal.ofReal (1 / 8) * ENNReal.ofReal (100 * a ^ 2) :=
        mul_le_mul' le_rfl
          (Work.NN.Newton.Defect.holderNorm_TA A hα0 hα1 hr ha0 ha1 hAc hAcoef l j k)
    _ = ENNReal.ofReal (1 / 8 * (100 * a ^ 2)) :=
        (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal (13 * a ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [sq_nonneg a]

end

end Work.NN.Newton
