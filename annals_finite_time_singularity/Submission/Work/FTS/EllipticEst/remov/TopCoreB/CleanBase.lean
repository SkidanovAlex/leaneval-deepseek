import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.AeMom.Repair.ShiftAeRepair

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TopCoreB/CleanBase`: the reverse expansions, on a poison-free import cone

The declarations `reverse_expansion_2d` / `reverse_expansion_top` of
`Submission.Work.FTS.EllipticEst.remov.PsiSlotBounds` are the pointwise input of the slot
recursions, but their module (and hence everything importing it) sits downstream of
`remov/DthIter_expansion`, whose import cone reaches the `EllHyp`-certificate cluster
(`Cert/*`, `ellHyp_L2Mem_*`, `RPFresh/excess_finite`), which currently does not compile.

The coefficient machinery is available *cleanly* in the fresh namespace `...remov.selfdth` of
`remov/high_chain_sum_self.lean` (`selfdth.DthIter_expansion_local`,
`selfdth.DthCoef_sin_pow_bound`, `selfdth.dthCoef_self`), so the two reverse expansions are
re-produced here verbatim in terms of it.

Also re-exported here: `HkMem_Dz_shift`, which the `A`-half copy
(`TopCoreB/ATopClean.lean`) consumes, taken from the clean provider
`Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-- `D_θ^{m+n} f = D_θ^m (D_θ^n f)`. -/
theorem DthIter_addT (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter (m + n) f = Work.Spaces.DthIter m (Work.Spaces.DthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]

/-- `∂_θ^{m+n} f = ∂_θ^m (∂_θ^n f)`. -/
theorem pthIter_addT (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

theorem sin_two_pos_of_IooT {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

theorem sin_two_nonneg_of_IooT {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) := (sin_two_pos_of_IooT hθ).le

/-- **The reverse expansion of `D_θ^m`** (surjectivity of the `D_θ`-iterate for the plain
`m`-th angular derivative): the plain `m`-th derivative, weighted by `sin(2θ)^m`, is dominated
by the `D_θ`-iterate and the plain derivatives of lower order. -/
theorem revExp2d (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry f) (z, θ)) →
      |Real.sin (2 * θ)| ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ K * (|Work.Spaces.DthIter m f z θ|
          + ∑ r ∈ Finset.range m,
              |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by
  classical
  choose K hKpos hKbd using fun r => selfdth.DthCoef_sin_pow_bound m r
  have hKsum_nonneg : 0 ≤ ∑ r ∈ Finset.range (m + 1), K r :=
    Finset.sum_nonneg fun i _ => (hKpos i).le
  refine ⟨1 + ∑ r ∈ Finset.range (m + 1), K r, by linarith, ?_⟩
  intro f z θ hf
  have hid := selfdth.DthIter_expansion_local m f z θ hf
  have hsplit : (Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m f z θ
      = Work.Spaces.DthIter m f z θ
        - ∑ r ∈ Finset.range m,
            selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ := by
    have hself := congrFun (selfdth.dthCoef_self m) θ
    rw [hid, Finset.sum_range_succ, hself]
    ring
  calc |Real.sin (2 * θ)| ^ m * |Work.Spaces.pthIter m f z θ|
      = |(Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m f z θ| := by rw [abs_mul, abs_pow]
    _ = |Work.Spaces.DthIter m f z θ
          - ∑ r ∈ Finset.range m,
              selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ| := by
        rw [hsplit]
    _ ≤ |Work.Spaces.DthIter m f z θ|
          + |∑ r ∈ Finset.range m,
              selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ| := by
        calc |Work.Spaces.DthIter m f z θ
              - ∑ r ∈ Finset.range m,
                  selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
            = |Work.Spaces.DthIter m f z θ
                + (-(∑ r ∈ Finset.range m,
                  selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ))| := by
              rw [sub_eq_add_neg]
          _ ≤ |Work.Spaces.DthIter m f z θ|
                + |-(∑ r ∈ Finset.range m,
                  selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ)| :=
              abs_add_le _ _
          _ = |Work.Spaces.DthIter m f z θ|
                + |∑ r ∈ Finset.range m,
                  selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ| := by
              rw [abs_neg]
    _ ≤ |Work.Spaces.DthIter m f z θ|
          + ∑ r ∈ Finset.range m,
              K r * (|Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by
        refine add_le_add le_rfl ?_
        calc |∑ r ∈ Finset.range m,
              selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
            ≤ ∑ r ∈ Finset.range m,
                |selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ r ∈ Finset.range m,
                |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [abs_mul]
          _ ≤ ∑ r ∈ Finset.range m,
                K r * (|Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by
              refine Finset.sum_le_sum fun r _ => ?_
              calc |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|
                  ≤ (K r * |Real.sin (2 * θ)| ^ r) * |Work.Spaces.pthIter r f z θ| :=
                    mul_le_mul_of_nonneg_right (hKbd r θ) (abs_nonneg _)
                _ = K r * (|Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by ring
    _ ≤ (1 + ∑ r ∈ Finset.range (m + 1), K r)
          * (|Work.Spaces.DthIter m f z θ|
            + ∑ r ∈ Finset.range m,
                |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r f z θ|) := by
        rw [mul_add]
        refine add_le_add ?_ ?_
        · have h1 : (1 : ℝ) ≤ 1 + ∑ r ∈ Finset.range (m + 1), K r := by linarith
          calc |Work.Spaces.DthIter m f z θ|
              = 1 * |Work.Spaces.DthIter m f z θ| := (one_mul _).symm
            _ ≤ (1 + ∑ r ∈ Finset.range (m + 1), K r)
                  * |Work.Spaces.DthIter m f z θ| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        · rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun r hr => ?_
          have hle : K r ≤ 1 + ∑ i ∈ Finset.range (m + 1), K i := by
            have hmem : r ∈ Finset.range (m + 1) :=
              Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hr))
            have := Finset.single_le_sum (fun i _ => (hKpos i).le) hmem
            linarith
          exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **Pointwise form of the reverse expansion at the top order.**  For `θ ∈ (0, π/2)`,

  `sin(2θ)^{m-2} |∂_θ^m f| ≤ K (|D_θ^{m-2}(∂_θθf)| + Σ_{r<m-2} sin(2θ)^r |∂_θ^{r+2} f|)`. -/
theorem revExpTop (m : ℕ) (hm : 2 ≤ m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      (∀ k : ℕ, ContDiffAt ℝ k (Function.uncurry (Work.Spaces.pthIter 2 f)) (z, θ)) →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (Real.sin (2 * θ)) ^ (m - 2) * |Work.Spaces.pthIter m f z θ|
        ≤ K * (|Work.Spaces.DthIter (m - 2) (Work.Spaces.pthIter 2 f) z θ|
          + ∑ r ∈ Finset.range (m - 2),
              (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter (r + 2) f z θ|) := by
  obtain ⟨K, hKpos, hK⟩ := revExp2d (m - 2)
  refine ⟨K, hKpos, fun f z θ hf hθ => ?_⟩
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_IooT hθ
  have hrev := hK (Work.Spaces.pthIter 2 f) z θ hf
  rw [← abs_pow] at hrev
  rw [abs_of_nonneg (pow_nonneg hs (m - 2))] at hrev
  have hsumrw : (∑ r ∈ Finset.range (m - 2),
        |Real.sin (2 * θ)| ^ r * |Work.Spaces.pthIter r (Work.Spaces.pthIter 2 f) z θ|)
      = ∑ r ∈ Finset.range (m - 2),
          (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter (r + 2) f z θ| := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [abs_of_nonneg hs, pthIter_addT r 2 f]
  rw [hsumrw, ← pthIter_addT (m - 2) 2 f, show m - 2 + 2 = m from by omega] at hrev
  exact hrev

end Work.FTS.EllipticEst.remov.TopCoreB

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false

/-- **Membership form of the `D_z`-shift** (clean provider): if `f` is `C^∞` on the open
quadrant and in `ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`. -/
theorem HkMem_Dz_shift {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) :=
  Work.FTS.EllipticEst.AeMom.Repair.HkMem_Dz_shift hk hf hmem

end Work.FTS.EllipticEst.remov
