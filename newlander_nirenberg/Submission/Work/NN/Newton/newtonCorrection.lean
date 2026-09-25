import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.NN.Final.Proj
import Submission.Work.NN.Final.clos2_ddbarStd
import Submission.Work.NN.Final.holderNormCongr
import Submission.Work.NN.Newton.newtonCorrDefs
import Submission.Work.NN.Newton.newtonCorrCore
import Submission.Work.NN.Newton.coordDefectData
import Submission.Work.NN.Newton.newtonCorrectionArith
import Submission.Work.NN.Newton.flatOneThin
import Submission.Work.NN.Newton.flatTwoThin
import Submission.Work.NN.Newton.coordDatum_defect_quadratic

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NN/Newton/DESIGN.md first. Your inputs are the sibling lemmas in depends_on (being proved in parallel; build against their statements). Do NOT use Work.NN.Core.dbar_regularity (rests on sorryAx).

# newtonCorrection — guidance

Pure assembly of `flatTwoThin`, `flatOneThin` and `coordDatum_defect_quadratic`.

1. `F^{(l)} := fun m y => Lcoef A (fun y' => y' l) m y`. It is smooth on `P_r` (`A` smooth; see
   `diffAt_Lcoef` in `Final/Defs.lean`).
   * `‖F^{(l)}_m‖_{1,α} ≤ a/2`: it is `(i/2)·` the coefficient of `A` in direction `e_m`, with
     `‖e_m‖ = 1`; use `holderNorm_smul`.
2. `η := ddbar₀ F^{(l)}` is smooth, antisymmetric (`ddbar_antisymm`) and closed. The cyclic sum
   vanishes by `Work.CR.Flat.Polydisc.dbarCoord_comm`. Its norm is `≤ C a²` by
   `coordDatum_defect_quadratic`.
3. `flatTwoThin` at `(r, δ/2)` gives `ψ` on `P_{r(1-δ/2)}` with `‖ψ‖_{1,α} ≤ C(δ/2)^{-N} n² C a²`.
4. `G := F − ψ` is closed on `P_{r(1-δ/2)}` (use `dbarCoord_sub` / `dbarOne_sub`, with
   differentiability from smoothness), and `‖G‖_{1,α} ≤ a/2 + Cδ^{-N}a² ≤ C'δ^{-N}a` (`a ≤ 1`).
5. `flatOneThin` at `(r(1-δ/2), δ')` with `(1-δ/2)(1-δ') = 1-δ`, i.e. `δ' = (δ/2)/(1−δ/2) ∈ [δ/2, δ]`,
   and radius `r(1−δ/2) ∈ [1/2, 4]`. This gives `v_l` with `∂̄_k v_l = F_k − ψ_k` on `P_{r(1-δ)}`.
6. The residual `∂̄_k v_l − Lcoef … = −ψ_k`, bounded by step 3 after restricting the domain
   (`holderNorm_mono_set`).

Keep the radius ranges straight: the thin solvers are stated for `r ∈ [1/2, 4]` and `δ ≤ 1/4`.
-/

namespace Work.NN.Newton

open scoped ContDiff

/-- **The linearised Newton correction.**

For `J = Jstd + A` smooth, almost complex and integrable on the polydisc `P_r` of radius `r`, with
`C^{1,α}`-size `a ≤ 1`, there are smooth corrections `v_l` on `P_{r(1-δ)}` with
`‖v_l‖_{C^{2,α}} ≤ (C/δ^N) a` which solve the linearised equation `∂̄_k v_l = Lcoef A z_l k`
(the coordinate datum `(i/2)(A z e_k)_l`) up to an error of size `(C/δ^N) a²` in `C^{1,α}`.

Construction: `F^{(l)} := Lcoef A z_l`, `ψ := flatTwoThin (∂̄₀ F^{(l)})` on `P_{r(1-δ/2)}`,
`v_l := flatOneThin (F^{(l)} - ψ)` on `P_{r(1-δ)}`; the error is `-ψ`, quadratic by
`coordDatum_defect_quadratic`. -/
theorem newtonCorrection {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ r δ : ℝ, 1 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 8 →
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
        ∃ v : Fin n → Work.NN.Core.Cn n → ℂ,
          (∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))) ∧
          (∀ l, Work.CR.Flat.holderNorm 2 α (v l)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (C / δ ^ N * a)) ∧
          (∀ l k, Work.CR.Flat.holderNorm 1 α
              (fun z => Work.CR.Flat.dbarCoord k (v l) z
                - Work.NN.Core.Lcoef A (fun y => y l) k z)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal (C / δ ^ N * a ^ 2)) := by
  exact newtonCorrection_core hn hα0 hα1 (coordDefectData hn hα0 hα1) (newtonCorrectionArith hn)

end Work.NN.Newton
