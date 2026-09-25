import Mathlib
import Submission.Work.NN.Newton.cddBundle
import Submission.Work.NN.Final.clos2_ddbarStd

namespace Work.NN.Newton

/-- The flat `∂̄`-defect `coordDefect A p = ddbar Jstd (coordDatum A p)` of the coordinate datum
is `∂̄`-closed (a `(0,3)`-form vanishing) on `P_r`, and its `C^{0,α}`-norm is quadratic in the
perturbation size `a`.

* the cyclic identity is pointwise `Work.NN.Final.clos2_ddbarStd` (module
  `Submission.Work.NN.Final.clos2_ddbarStd`, needs an extra import) applied to the array
  `coordDatum A p`, whose components are `ContDiffAt ℝ 2` at every `z ∈ P_r` by
  `Work.NN.Newton.coordDatum_contDiffAt` (in `newtonCorrDefs`);
* the `C^{0,α}` bound is `Work.NN.Newton.coordDatum_defect_quadratic` (`hn`, `hα0`, `hα1`, the
  smoothness, almost-complexity and integrability hypotheses, `0 ≤ a`, `a ≤ 1` and the coefficient
  bound all match verbatim), so `C` can be taken to be that lemma's constant.
Antisymmetry and smoothness of `coordDefect` are already proved in `newtonCorrDefs`
(`coordDefect_antisymm`, `coordDefect_contDiffOn`) and are not needed here. -/
theorem coordDefectData {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r → r ≤ 4 →
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
        (∀ p j k l : Fin n, ∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          Work.CR.Flat.dbarCoord j (coordDefect A p l k) z
            - Work.CR.Flat.dbarCoord l (coordDefect A p j k) z
            + Work.CR.Flat.dbarCoord k (coordDefect A p j l) z = 0) ∧
        (∀ p j k : Fin n, Work.CR.Flat.holderNorm 0 α (coordDefect A p j k)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal (C * a ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := zcddQuadBound hn hα0 hα1
  refine ⟨C, hCpos, ?_⟩
  intro r hr1 hr4 A hA hac hint a ha0 ha1 hbound
  have hdiff : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r),
      DifferentiableAt ℝ A z := by
    intro z hz
    have h1 : ContDiffAt ℝ 1 A z :=
      (hA 1).contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 (fun _ => r)).mem_nhds hz)
    exact h1.differentiableAt (by norm_num)
  have hpt : ∀ p j k : Fin n, ∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
      coordDefect A p j k z = -(Complex.I / 8) * cdQuad A z p j k := by
    intro p j k z hz
    have hrel : cdRel A z p := zcddRel hA hac hz p
    have hproj := zcddProj02 A z p j k (hdiff z hz)
    have hzero : Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
        (fun z' => Work.NN.Final.dOne
          (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) (cdLam p) z'') z')
        z (cdEvec j) (cdEvec k) = 0 := by
      simpa using hint (cdLam p) (fun k => (cdLam p).contDiff) z hz (cdEvec j) (cdEvec k)
    have hE : cdE A z p j k = 0 := by
      have h2 : (Complex.I / 8) * cdE A z p j k = 0 := by rw [← hproj]; exact hzero
      rcases mul_eq_zero.mp h2 with h | h
      · exfalso
        apply Complex.I_ne_zero
        have : Complex.I / 8 * 8 = 0 := by rw [h]; ring
        simpa using this
      · exact h
    have h3 := zcddEexpr A z p j k hrel
    have hD : cdDefA A z p j k = -(1 / 2) * cdQuad A z p j k := by
      have hh : 2 * cdDefA A z p j k + cdQuad A z p j k = 0 := by rw [← h3, hE]
      linear_combination (1 / 2) * hh
    rw [zcddDefect A z p j k (hdiff z hz), hD]
    ring
  constructor
  · intro p j k l z hz
    have ha2 : ∀ q : Fin n, ContDiffAt ℝ 2 (coordDatum A p q) z :=
      fun q => coordDatum_contDiffAt hA p q hz 2
    have h := Work.NN.Final.clos2_ddbarStd (coordDatum A p) z ha2 j l k
    exact h
  · intro p j k
    rw [Work.NN.Final.holderNorm_congr_of_isOpen
      (Work.CR.Flat.isOpen_polydisc 0 (fun _ => r)) (fun z hz => hpt p j k z hz) 0 α]
    exact hC r hr1 hr4 A hA a ha0 ha1 hbound p j k

end Work.NN.Newton
