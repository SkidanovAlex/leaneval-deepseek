import ChallengeDeps
import Submission.Work.BoseFixR.BlockDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.BoxParamArith` — the parameter arithmetic of the block split

`Work.BoseFixR.BoxWordLower` splits an `n`-particle box state into two blocks and
runs an induction on the particle number: the induction step needs

* the box side arithmetic `μℓ³ = (μa³)^{-166/323}` and the matrix window
  `𝓜 = bigM (paramsAt μ a) a μ = (μa³)^{-327/1292}` (FS `eq:DefM`), and
* the two consequences of the cutoff `k = ⌈8μℓ³⌉`: the small-`n` branch is
  nonempty (`2 ≤ k`) and the two blocks together exhaust the state
  (`k < 9μℓ³`, hence `k/ℓ³ ≤ 9μ`).

All five conjuncts are monomial arithmetic in the diluteness `t = μa³`: with
`ℓ³ = K_ℓ³(μa)^{-3/2}` one has `μℓ³ = t^{-166/323} ≥ 1` and
`μaℓ³ = a·t^{-166/323}`, while `bigM = t^{-327/1292}`; the last conjunct
`𝓜 ≤ μaℓ³` is therefore equivalent to `t^{337/1292} ≤ a`, and it is *this*
that fixes the choice of `ε₀`: the admissible threshold must be at most
`a^{1292/337}`, which is legitimate because `a = a v` is fixed once `v` is.

The helper `bigM_le_mu_a_side_cube` is the only non-elementary step; it converts
the `fsXp`-form `bigM_paramsAt` (`= X^{-327/4}`) into the exponent `-327/1292`
and compares the two `rpow`s.
-/

noncomputable section

set_option linter.unusedVariables false

namespace Work.BoseFixR

open _root_.BoseGases

/-- **The matrix window is below `μaℓ³` once the diluteness is below
`a^{1292/337}`.**  At FS's parameters `bigM (paramsAt μ a) a μ = (μa³)^{-327/1292}`
and `μ a (sideAt μ a)³ = a (μa³)^{-166/323}`, so the inequality is equivalent to
`(μa³)^{337/1292} ≤ a`. -/
lemma bigM_le_mu_a_side_cube {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a)
    (ht : μ * a ^ 3 ≤ a ^ (1292 / 337 : ℝ)) :
    Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ
      ≤ μ * a * Work.BoseBox.sideAt μ a ^ 3 := by
  have htpos : 0 < μ * a ^ 3 := by positivity
  -- `μℓ³ = (μa³)^{-166/323}`: FS's healing-length identity `mu_ell_cube_fsParams`.
  have hL3 : μ * Work.BoseBox.sideAt μ a ^ 3 = (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) := by
    show μ * Work.BoseBox.boxSide (Work.BoseBox.fsParams (μ * a ^ 3)) μ a ^ 3 = _
    exact Work.BoseBox.mu_ell_cube_fsParams hμ ha
  -- `𝓜 = (μa³)^{-327/1292}` (FS `eq:DefM`).
  have hbm : Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ
      = (μ * a ^ 3) ^ (-(327 / 1292 : ℝ)) := by
    rw [Work.BoseBox.bigM_paramsAt hμ ha]
    simp only [Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hgoal : μ * a * Work.BoseBox.sideAt μ a ^ 3
      = a * (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) := by
    rw [← hL3]; ring
  rw [hbm, hgoal]
  -- `(μa³)^{337/1292} ≤ a` from `μa³ ≤ a^{1292/337}`.
  have h1 : (μ * a ^ 3) ^ (337 / 1292 : ℝ) ≤ a := by
    have h2 : (μ * a ^ 3) ^ (337 / 1292 : ℝ)
        ≤ (a ^ (1292 / 337 : ℝ)) ^ (337 / 1292 : ℝ) :=
      Real.rpow_le_rpow htpos.le ht (by norm_num)
    have h3 : (a ^ (1292 / 337 : ℝ)) ^ (337 / 1292 : ℝ) = a := by
      rw [← Real.rpow_mul ha.le,
        show (1292 / 337 : ℝ) * (337 / 1292) = 1 by norm_num, Real.rpow_one]
    linarith
  calc (μ * a ^ 3) ^ (-(327 / 1292 : ℝ))
      = (μ * a ^ 3) ^ ((337 / 1292 : ℝ) + (-(166 / 323))) := by
        rw [show (337 / 1292 : ℝ) + (-(166 / 323)) = -(327 / 1292) by norm_num]
    _ = (μ * a ^ 3) ^ (337 / 1292 : ℝ) * (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) :=
        Real.rpow_add htpos _ _
    _ ≤ a * (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg htpos.le _)

theorem BoxParamArith {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      let L := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      let k := Nat.ceil (8 * μ * L ^ 3)
      1 ≤ μ * L ^ 3 ∧ 2 ≤ k ∧ (k : ℝ) < 9 * μ * L ^ 3 ∧
      (k : ℝ) / L ^ 3 ≤ 9 * μ ∧
      Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v))
          (_root_.BoseGases.a v) μ ≤ μ * (_root_.BoseGases.a v) * L ^ 3 := by
  refine ⟨min 1 ((_root_.BoseGases.a v) ^ (1292 / 337 : ℝ)), ?_, ?_⟩
  · exact lt_min one_pos (Real.rpow_pos_of_pos hav _)
  intro μ hAdm
  obtain ⟨hμ, htε, -⟩ := hAdm
  have htpos : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans htε (min_le_left _ _)
  have hta : μ * (_root_.BoseGases.a v) ^ 3 ≤ (_root_.BoseGases.a v) ^ (1292 / 337 : ℝ) :=
    le_trans htε (min_le_right _ _)
  dsimp only
  have hL3 : μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
      = (μ * (_root_.BoseGases.a v) ^ 3) ^ (-(166 / 323 : ℝ)) := by
    show μ * Work.BoseBox.boxSide (Work.BoseBox.fsParams (μ * (_root_.BoseGases.a v) ^ 3))
        μ (_root_.BoseGases.a v) ^ 3 = _
    exact Work.BoseBox.mu_ell_cube_fsParams hμ hav
  -- `1 ≤ μℓ³`: the diluteness is at most `1`.
  have hx1 : 1 ≤ μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
    rw [hL3]
    simpa using Real.rpow_le_rpow_of_exponent_ge htpos ht1
      (show -(166 / 323 : ℝ) ≤ 0 by norm_num)
  have hLpos : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 :=
    pow_pos (Work.BoseBox.sideAt_pos hμ hav) 3
  -- `2 ≤ ⌈8μℓ³⌉`: `8μℓ³ ≥ 8 ≥ 2`.
  have hceil2 : 2 ≤ Nat.ceil (8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) := by
    have h8 : (2 : ℝ) ≤ 8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
      nlinarith [hx1]
    have := Nat.le_ceil (8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3)
    exact_mod_cast le_trans h8 this
  -- `⌈8μℓ³⌉ < 9μℓ³`: `⌈x⌉ < x + 1 ≤ 9μℓ³` for `μℓ³ ≥ 1`.
  have hceil9 : ((Nat.ceil (8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) : ℝ))
      < 9 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3 := by
    have hlt := Nat.ceil_lt_add_one
      (a := 8 * μ * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3) (by positivity)
    nlinarith [hx1]
  exact ⟨hx1, hceil2, hceil9, by rw [div_le_iff₀ hLpos]; linarith,
    bigM_le_mu_a_side_cube hμ hav hta⟩

end Work.BoseFixR
