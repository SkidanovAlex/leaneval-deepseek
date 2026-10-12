import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseGateFS.TauRows
import Submission.Work.BoseRowsFS.Hon
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.honest_tauSm_rows` — the `τ̃` rows at the honest model

The `IntKernel.tau_PH` row (`Work.BoseK15.tau_PH_bound`) read at the *honest*
kinetic symbol `Work.BoseBoxFock.tauSm` (the smoothed `τ̃` of
`BOSE_BOXFOCK_LEAD.md` §2.2) rather than at FS's kinked `def:tau`
(`Work.BoseB4.tauFun`).  The honest model's `E.tau` *is* `tauSm`
(`Work.BoseRowsFS.honE_tau`), so this is the form in which the gate consumes the
row: for every honest mode choice `HM`, every `μ > 0` and every cube label `k`,

  `0 ≤ ‖kmom k‖² − τ̃(kmom k)  ∧  ‖kmom k‖² − τ̃(kmom k) ≤ 2‖kmom k‖/(dsℓ)`.

## The proof

`τ̃(x) = (1−ε_T)u²φ(x/u) + ε_T v²φ(x/v)` with `u = (2sℓ)⁻¹`,
`v = (2dsℓ)⁻¹` and `φ = tauProf` the chosen profile, which satisfies

* `φ(r) ≤ (max 0 (r−1))²` and
* `(max 0 (r−2))² ≤ φ(r)`.

**Nonnegativity.**  Multiply the first bound by `u²` (resp. `v²`) and use
`c²φ(r/c) ≤ r²` (`sq_mul_phi_le`): each rescaled summand is at most `x²`, so
`τ̃ x ≤ (1−ε_T)x² + ε_T x² = x²`.

**The linear deficit.**  From the *lower* bound on the profile,
`τ̃ x ≥ (1−ε_T)(max 0 (x−2u))² + ε_T(max 0 (x−2v))²` (the rescaled identity
`c²(max 0 (x/c − 2))² = (max 0 (x−2c))²`, `sq_mul_max_sub`), so

  `x² − τ̃ x ≤ (1−ε_T)(x² − (x−2u)₊²) + ε_T(x² − (x−2v)₊²)`
             `≤ 4x((1−ε_T)u + ε_T v) ≤ 4xv = 2x/(dsℓ)`,

where the last step is `u ≤ v` (i.e. `d ≤ 1`) and `0 ≤ ε_T ≤ 1`.  The honest
parameters give `d = X⁶ = (μa³)^{6/323} ≤ 1`, so `u ≤ v` and the deficit is
`≤ x/(dsℓ)`, twice as small as `TauRows.tauTilde_deficit`'s `4x/(dsℓ)` (which
only uses a `d ≤ 2`-type comparison of the thresholds).  The whole content is
pure arithmetic on the two thresholds and is isolated in `tauSm_rows_core`.
-/

noncomputable section

open scoped Real BigOperators Topology

namespace Work.BoseRowsFS

open Work.BoseB7 Work.BoseBoxFock Work.BoseBoxFix Work.BoseFixR Work.UBB

/-! ## 1. The two profile bounds of `exists_tauProf` -/

/-- The lower bound of the chosen kinetic profile: `(r−2)₊² ≤ τProf r`. -/
lemma tauProf_ge (r : ℝ) : (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
  Work.BoseBoxFock.tauProf_spec.2.2.1 r

/-- The upper bound of the chosen kinetic profile: `τProf r ≤ (r−1)₊²`. -/
lemma tauProf_le (r : ℝ) : Work.BoseBoxFock.tauProf r ≤ (max 0 (r - 1)) ^ 2 :=
  Work.BoseBoxFock.tauProf_spec.2.2.2.1 r

/-! ## 2. The scalar core -/

/-- `x² − (max 0 (x−a))² ≤ 2ax` for `x, a ≥ 0`: in the region `x ≥ a` this is
`a(2x − a) ≤ 2ax`, and in the region `x ≤ a` it is `x² ≤ 2ax`. -/
private lemma sq_sub_max_le' (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    x ^ 2 - (max (x - a) 0) ^ 2 ≤ 2 * a * x := by
  rcases le_or_gt x a with h | h
  · rw [max_eq_right (by linarith : x - a ≤ 0)]
    nlinarith
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ x - a)]
    nlinarith

/-- **The τ̃-rows at the two thresholds.**  For `x ≥ 0`, `0 ≤ e ≤ 1`,
`0 < u ≤ v`,

`0 ≤ x² − ((1−e)u²φ(x/u) + e v²φ(x/v))`
`  ∧ x² − ((1−e)u²φ(x/u) + e v²φ(x/v)) ≤ 4xv`.

With `u = (2sℓ)⁻¹`, `v = (2dsℓ)⁻¹` this is exactly the honest `τ̃`-row, since
`4xv = 2x/(dsℓ)`. -/
lemma tauSm_rows_core (x e u v : ℝ) (hx : 0 ≤ x) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hu : 0 < u) (hv : 0 < v) (huv : u ≤ v) :
    0 ≤ x ^ 2 - ((1 - e) * u ^ 2 * Work.BoseBoxFock.tauProf (x / u)
                  + e * v ^ 2 * Work.BoseBoxFock.tauProf (x / v))
    ∧ x ^ 2 - ((1 - e) * u ^ 2 * Work.BoseBoxFock.tauProf (x / u)
                  + e * v ^ 2 * Work.BoseBoxFock.tauProf (x / v)) ≤ 4 * x * v := by
  have h1e : 0 ≤ 1 - e := by linarith
  -- upper bound on the profile: each rescaled summand is at most `x²`
  have hup_u := Work.BoseGateFS.sq_mul_phi_le Work.BoseBoxFock.tauProf tauProf_le hu hx
  have hup_v := Work.BoseGateFS.sq_mul_phi_le Work.BoseBoxFock.tauProf tauProf_le hv hx
  -- lower bound on the profile: `c²(max 0 (x/c - 2))² = (max 0 (x - 2c))²`
  have hM_u : max (x - 2 * u) 0 ^ 2 ≤ u ^ 2 * Work.BoseBoxFock.tauProf (x / u) := by
    rw [← Work.BoseGateFS.sq_mul_max_sub u x hu]
    exact mul_le_mul_of_nonneg_left (tauProf_ge (x / u)) (sq_nonneg u)
  have hM_v : max (x - 2 * v) 0 ^ 2 ≤ v ^ 2 * Work.BoseBoxFock.tauProf (x / v) := by
    rw [← Work.BoseGateFS.sq_mul_max_sub v x hv]
    exact mul_le_mul_of_nonneg_left (tauProf_ge (x / v)) (sq_nonneg v)
  have hsub_u := sq_sub_max_le' x (2 * u) hx (by linarith)
  have hsub_v := sq_sub_max_le' x (2 * v) hx (by linarith)
  constructor
  · nlinarith [hup_u, hup_v, he0, h1e]
  · have hkey : x ^ 2 - ((1 - e) * u ^ 2 * Work.BoseBoxFock.tauProf (x / u)
          + e * v ^ 2 * Work.BoseBoxFock.tauProf (x / v))
        ≤ x ^ 2 - ((1 - e) * max (x - 2 * u) 0 ^ 2 + e * max (x - 2 * v) 0 ^ 2) := by
      nlinarith [hM_u, hM_v, h1e, he0]
    have hkey2 : x ^ 2 - ((1 - e) * max (x - 2 * u) 0 ^ 2 + e * max (x - 2 * v) 0 ^ 2)
        ≤ 4 * x * v := by
      have hle : (1 - e) * u + e * v ≤ v := by nlinarith [he1, huv]
      nlinarith [hsub_u, hsub_v, hle, he0, h1e]
    linarith

/-! ## 3. The row at the honest model -/

theorem honest_tauSm_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} :
    ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ), 0 < μ →
      Work.BoseB7.FSParamsView (Work.BoseRowsFS.honE v h fc fu HM μ) →
      ∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        0 ≤ ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
            - (Work.BoseRowsFS.honE v h fc fu HM μ).tau k
        ∧ ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖ ^ 2
            - (Work.BoseRowsFS.honE v h fc fu HM μ).tau k
          ≤ 2 * ‖(Work.BoseRowsFS.honF v h fc fu HM μ).kmom k‖
              / ((Work.BoseRowsFS.honE v h fc fu HM μ).d
                * (Work.BoseRowsFS.honE v h fc fu HM μ).s
                * (Work.BoseRowsFS.honE v h fc fu HM μ).ell) := by
  intro HM μ _hμ hview k
  -- the honest parameters: `0 ≤ ε_T ≤ 1`, `0 < d ≤ 1`, `0 < s`, `0 < ℓ`
  have hE0 : 0 ≤ (honE v h fc fu HM μ).eT := by
    rw [hview.eT_eq]; exact Work.BoseBox.fsXp_nonneg hview.t_pos.le
  have hE1 : (honE v h fc fu HM μ).eT ≤ 1 := by
    rw [hview.eT_eq]; exact Work.BoseBox.fsXp_le_one hview.t_pos hview.t_le_one (by norm_num)
  have hd1 : (honE v h fc fu HM μ).d ≤ 1 := by
    rw [hview.d_eq]; exact Work.BoseBox.fsXp_le_one hview.t_pos hview.t_le_one (by norm_num)
  have hdp : 0 < (honE v h fc fu HM μ).d := by
    rw [hview.d_eq]; exact Work.BoseBox.fsXp_pos hview.t_pos
  have hs : 0 < (honE v h fc fu HM μ).s := by
    rw [hview.s_eq]; exact Work.BoseBox.fsXp_pos hview.t_pos
  have hell : 0 < (honE v h fc fu HM μ).ell := Work.BoseB7.ell_pos _ hview
  -- the two thresholds `u = (2sℓ)⁻¹ ≤ v = (2dsℓ)⁻¹` (this is `d ≤ 1`)
  have hu : 0 < (2 * (honE v h fc fu HM μ).s * (honE v h fc fu HM μ).ell)⁻¹ :=
    inv_pos.mpr (by positivity)
  have hv' : 0 < (2 * (honE v h fc fu HM μ).d * (honE v h fc fu HM μ).s
      * (honE v h fc fu HM μ).ell)⁻¹ := inv_pos.mpr (by positivity)
  have huv : (2 * (honE v h fc fu HM μ).s * (honE v h fc fu HM μ).ell)⁻¹
      ≤ (2 * (honE v h fc fu HM μ).d * (honE v h fc fu HM μ).s
          * (honE v h fc fu HM μ).ell)⁻¹ := by
    refine inv_anti₀ (by positivity) ?_
    nlinarith [hd1, mul_pos hs hell]
  -- the scalar core at `x = ‖kmom k‖`
  have hcore := tauSm_rows_core ‖(honF v h fc fu HM μ).kmom k‖ (honE v h fc fu HM μ).eT
      (2 * (honE v h fc fu HM μ).s * (honE v h fc fu HM μ).ell)⁻¹
      (2 * (honE v h fc fu HM μ).d * (honE v h fc fu HM μ).s
        * (honE v h fc fu HM μ).ell)⁻¹
      (norm_nonneg _) hE0 hE1 hu hv' huv
  rw [honE_tau v h fc fu HM μ k]
  refine ⟨?_, ?_⟩
  · simpa only [Work.BoseBoxFock.tauSm] using hcore.1
  · rw [Work.BoseBoxFock.tauSm]
    refine le_trans hcore.2 ?_
    -- `4x·(2dsℓ)⁻¹ = 2x/(dsℓ)`
    have hconv : 4 * ‖(honF v h fc fu HM μ).kmom k‖
        * (2 * (honE v h fc fu HM μ).d * (honE v h fc fu HM μ).s
            * (honE v h fc fu HM μ).ell)⁻¹
        = 2 * ‖(honF v h fc fu HM μ).kmom k‖
          / ((honE v h fc fu HM μ).d * (honE v h fc fu HM μ).s
              * (honE v h fc fu HM μ).ell) := by
      field_simp
      ring
    linarith [hconv.le]

end Work.BoseRowsFS
