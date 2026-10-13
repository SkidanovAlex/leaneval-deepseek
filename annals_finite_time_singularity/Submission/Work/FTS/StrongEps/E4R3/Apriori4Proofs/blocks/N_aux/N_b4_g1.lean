import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

/-! ## The level-`4` pricing of the five `Z`-pieces `k = 0, 2, 4, 6, 8` of `NBlk`

Each of the five pieces is one product of an `α`-small coefficient with a `w`-slot, so a single
application of `mulQo_absorb` (coefficient `HQo α 4`, priced by `C·α²`) resp. `mulW_absorb`
(coefficient `SmoothOpen`/`WlInfMem`, priced by `C·α`) closes it; see
`NOTES_N_b4_pieces.md` for the table.  The constant `K := 2·|C|³ + 1` dominates every
resulting bound (`2C²G` for the `ℚ`-slots and `2C³G` for the `𝒲`-slots, `G = 1 + HkNorm α 5 w`),
and is unconditionally positive (the context already forces `1 ≤ C`, but `K` must be positive
before any context is available). -/

/-- `2C² ≤ 2|C|³ + 1` for `C ≥ 1`. -/
private theorem two_mul_sq_le (C : ℝ) (hCpos : 0 < C) (hCone : 1 ≤ C) :
    2 * C * C ≤ 2 * |C| ^ 3 + 1 := by
  have habs : |C| = C := abs_of_pos hCpos
  rw [habs]
  nlinarith [hCone, sq_nonneg C, mul_nonneg (sq_nonneg C) (by linarith : (0 : ℝ) ≤ C - 1)]

/-- `2C³·A ≤ (2|C|³ + 1)·A` for `A ≥ 0`. -/
private theorem two_mul_cube_mul_le (C : ℝ) (hCpos : 0 < C) {A : ℝ} (hA : 0 ≤ A) :
    2 * C * C * (C * A) ≤ (2 * |C| ^ 3 + 1) * A := by
  have habs : |C| = C := abs_of_pos hCpos
  rw [habs]
  nlinarith [hA]

theorem N_b4_g1 (C C₀ Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Ctx C C₀ Ce Cs α Φs w Φg →
    ∀ k ∈ ({0, 2, 4, 6, 8} : Finset ℕ),
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
  refine ⟨2 * |C| ^ 3 + 1, by positivity, ?_⟩
  intro α hα Φs w Φg ctx k hk
  have hCpos : (0 : ℝ) < C := ctx.hCpos
  have hCone : (1 : ℝ) ≤ C := ctx.hCone
  have hG : (0 : ℝ) ≤ 1 + Work.Spaces.HkNorm α 5 w := zero_le_G
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl
  · -- `k = 0`: `2·(Rop Φ̃_g · w)`
    have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := 2) (s := 2) (by norm_num)
      ctx.hCpos.le zero_le_G ctx.Rqo ctx.wqo ctx.RX ctx.wX
    have hAB : |(2 : ℝ)| * C * C = 2 * C * C := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 0)
        ≤ 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (mul_le_mul_of_nonneg_right (two_mul_sq_le C hCpos hCone) hG)
  · -- `k = 2`: `2·(Rs · φw)`
    have hbF : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
        Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ) ≤ C * α ^ 1 := by
      simpa only [pow_one] using ctx.RsW
    have hQ : (0 : ℝ) ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := mul_nonneg hCpos.le hG
    have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := 2) (s := 1) (by norm_num)
      ctx.hCpos.le hQ ctx.Rssm ctx.RsWm ctx.phiwqo hbF ctx.phiwX
    have hAB : |(2 : ℝ)| * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w))
        = 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 2)
        ≤ 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (two_mul_cube_mul_le C hCpos hG)
  · -- `k = 4`: `-2·(Uc · D_θw)`
    have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := -2) (s := 2) (by norm_num)
      ctx.hCpos.le zero_le_G ctx.Uqo ctx.dthwqo ctx.UX ctx.dthwX
    have hAB : |(-2 : ℝ)| * C * C = 2 * C * C := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 4)
        ≤ 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (mul_le_mul_of_nonneg_right (two_mul_sq_le C hCpos hCone) hG)
  · -- `k = 6`: `-2·(Us · φD_θw)`
    have hbF : Work.Spaces.WlInf α 4 (fun z θ => (z + 1) / z *
        (Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ
          / Work.Construction.s2 θ)) ≤ C * α ^ 1 := by
      simpa only [pow_one] using ctx.UsW
    have hQ : (0 : ℝ) ≤ C * (1 + Work.Spaces.HkNorm α 5 w) := mul_nonneg hCpos.le hG
    have h := mulW_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPW (c := -2) (s := 1) (by norm_num)
      ctx.hCpos.le hQ ctx.Ussm ctx.UsWm ctx.phiDthwqo hbF ctx.phiDthwX
    have hAB : |(-2 : ℝ)| * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w))
        = 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by norm_num
    rw [hAB] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 6)
        ≤ 2 * C * C * (C * (1 + Work.Spaces.HkNorm α 5 w)) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    exact le_trans h2 (two_mul_cube_mul_le C hCpos hG)
  · -- `k = 8`: `-(2α)·(Vc · D_zw)`
    have h := mulQo_absorb ctx.hα0 ctx.hα1 ctx.hCpos ctx.hPQo (c := -(2 * α)) (s := 2)
      (by norm_num) ctx.hCpos.le zero_le_G ctx.Vqo ctx.dzwqo ctx.VX ctx.dzwX
    have hc : |(-(2 * α))| = 2 * α := by
      rw [abs_neg, abs_of_pos (by linarith [ctx.hα0] : (0 : ℝ) < 2 * α)]
    rw [hc] at h
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    have h2 : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 8)
        ≤ 2 * α * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    have hαle : 2 * α ≤ 2 := by linarith [hα.2]
    have hCG : (0 : ℝ) ≤ C * C * (1 + Work.Spaces.HkNorm α 5 w) :=
      mul_nonneg (mul_nonneg hCpos.le hCpos.le) hG
    have hstep : 2 * α * C * C * (1 + Work.Spaces.HkNorm α 5 w)
        ≤ 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by
      calc 2 * α * C * C * (1 + Work.Spaces.HkNorm α 5 w)
          = 2 * α * (C * C * (1 + Work.Spaces.HkNorm α 5 w)) := by ring
        _ ≤ 2 * (C * C * (1 + Work.Spaces.HkNorm α 5 w)) :=
            mul_le_mul_of_nonneg_right hαle hCG
        _ = 2 * C * C * (1 + Work.Spaces.HkNorm α 5 w) := by ring
    exact le_trans (le_trans h2 hstep)
      (mul_le_mul_of_nonneg_right (two_mul_sq_le C hCpos hCone) hG)

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
