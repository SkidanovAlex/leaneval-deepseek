import ChallengeDeps
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.honest_NH_qw_le` — the honest `NH` is at most `(1/32)n₊`

`tildeDataHon` (`Defs.lean`) realises FS's `n₊^H` on the χ-modes as

  `NH = (1/32) • ∑_{k ∈ excited} η_H(k) • a_k†a_k`,   `η_H(k) = 1 − f_u(|k|/(2κ)) ∈ [0,1]`.

The requested lemma compares its quadratic form with the one of `n₊ = Σ_k a_k†a_k`:

  `⟨g, NH g⟩ ≤ (1/32)·⟨g, n₊ g⟩               (g ∈ 𝓕)`,

which is the statement that `n₊^H ≤ n₊` as operators (up to the `1/32`), i.e. the
honest substitution `a_k†a_k ≤ n₊` of every excited mode (`k ≠ 0`, so `a_k†a_k` is a
summand of `n₊`).

## Route

Everything is proved at the `FockData` level, so no instance diamonds arise:

* `qw_sum_finset` — `qw g` is additive and homogeneous in the operator:
  `qw g (Σ_{i∈t} c i • A i) = Σ_{i∈t} c i * qw g (A i)` (induction on the finset,
  using `FockData.qw_add` and `FockData.qw_smul`);
* `qw_nOp_sum_le` — the general inequality
  `qw g ((1/32) • Σ_k η k • nOp k) ≤ (1/32) * qw g (Σ_k nOp k)` for `η k ≤ 1`,
  by summing the pointwise bound `η k * qw g (nOp k) ≤ 1 * qw g (nOp k)`
  (`bp_nOp_nonneg`: `qw g (nOp k) = ‖a_k g‖² ≥ 0`);
* `honest_NH_qw_le` — the requested statement: the honest `NH` is *definitionally*
  of the above shape (`HonestBoxFam`/`tildeDataHon` build it as
  `(1/32) • Σ_k η_H(k) • (creOf m (f k)).comp (annOf m (f k))`, and
  `(boxFockData …).nOp k` is `(creOf m (f k)).comp (annOf m (f k))`), so the
  general lemma applies by definitional unfolding.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

/-- `qw g` is additive and homogeneous in the operator: for any finite family of
operators `A i` with real coefficients `c i`,

  `qw g (Σ_{i ∈ t} c i • A i) = Σ_{i ∈ t} c i * qw g (A i)`.

`qw g X = ⟨X g, g⟩` and `bp` is *linear in its first argument*
(`bp : H →ₗ[ℝ] (H →ₗ[ℝ] ℝ)`), so this is the additivity/homogeneity of `bp` in the
state followed by the same property of `LinearMap.sum_apply`/`smul_apply`. -/
lemma qw_sum_finset {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (g : F.H) {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (c : ι → ℝ) (A : ι → F.H →ₗ[ℝ] F.H) :
    F.qw g (∑ i ∈ t, c i • A i) = ∑ i ∈ t, c i * F.qw g (A i) := by
  induction t using Finset.induction with
  | empty => simp [Work.BoseB7.FockData.qw]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Work.BoseB7.FockData.qw_add,
        Work.BoseB7.FockData.qw_smul, ih]

/-- **The honest `n₊^H` is dominated by `(1/32)n₊` as a quadratic form.**  For any finite
set of modes `s` and weights `η k ≤ 1`,

  `qw g ((1/32) • Σ_{k ∈ s} η k • n_k) ≤ (1/32) * qw g (Σ_{k ∈ s} n_k)`,

with `n_k = a_k†a_k`.  No lower bound on `η` is needed: the only input is
`qw g (n_k) = ‖a_k g‖² ≥ 0` (`Work.BoseB7.bp_nOp_nonneg`). -/
lemma qw_nOp_sum_le {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (s : Finset Mode) (η : Mode → ℝ)
    (hη1 : ∀ k ∈ s, η k ≤ 1) (g : F.H) :
    F.qw g ((1 / 32 : ℝ) • ∑ k ∈ s, η k • F.nOp k)
      ≤ (1 / 32) * F.qw g (∑ k ∈ s, F.nOp k) := by
  have hL : F.qw g ((1 / 32 : ℝ) • ∑ k ∈ s, η k • F.nOp k)
      = (1 / 32) * ∑ k ∈ s, η k * F.qw g (F.nOp k) := by
    rw [Work.BoseB7.FockData.qw_smul, qw_sum_finset F g s η (fun k => F.nOp k)]
  have hR : F.qw g (∑ k ∈ s, F.nOp k) = ∑ k ∈ s, F.qw g (F.nOp k) := by
    have h := qw_sum_finset F g s (fun _ : Mode => (1 : ℝ)) (fun k => F.nOp k)
    simpa using h
  rw [hL, hR]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 32)
  apply Finset.sum_le_sum
  intro k hk
  calc η k * F.qw g (F.nOp k) ≤ 1 * F.qw g (F.nOp k) :=
        mul_le_mul_of_nonneg_right (hη1 k hk) (Work.BoseB7.bp_nOp_nonneg F k g)
    _ = F.qw g (F.nOp k) := one_mul _

/-- **`n₊^H ≤ (1/32)n₊` at the honest box family.**  `tildeDataHon`'s `NH` is
`(1/32) • Σ_{k ∈ excited} η_H(k) • a_k†a_k` with `η_H = 1 − f_u(·/(2κ)) ≤ 1`
(`etaH_le_one`) and `a_k = annOf m (f k)` on the χ-modes, so `qw_nOp_sum_le` applies
by definitional unfolding of `HonestBoxFam`/`tildeDataHon`/`boxFockData`. -/
theorem honest_NH_qw_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) :
    ∀ g : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.H,
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw g
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).T.NH
        ≤ (1 / 32) * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.qw g
            (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
                (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.nOp k) := by
  intro g
  have key := qw_nOp_sum_le (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
    (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N))
    (fun k => Work.BoseBoxFock.etaH fu (((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
        * Real.sqrt (μ * BoseGases.a v))
        (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) (HM μ).N k))
    (fun k _ => Work.BoseBoxFock.etaH_le_one ..) g
  exact key

end Work.BoseBoxFock
