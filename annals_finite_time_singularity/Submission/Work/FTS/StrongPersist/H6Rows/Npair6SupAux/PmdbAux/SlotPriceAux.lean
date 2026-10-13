import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux.PmdbAux

/-! ## 2. The pointwise pricing of the coefficient, and the slot dominations -/

/-- **The pointwise pricing of the coefficient at the `𝒲^{6,∞}` level.**  At every `z > 0`
and every interior angle, every slot `D_z^i D_θ^j Aa` with `i + j ≤ 6` is bounded by `KA`.
(This is the `z`-pointwise form of `WlInfMem α 6 Aa` together with `WlInf α 6 Aa ≤ KA`.) -/
def SlotPrice (KA : ℝ) (Aa : ℝ → ℝ → ℝ) : Prop :=
  ∀ i j : ℕ, i + j ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
    |Work.Spaces.mixed i j Aa z θ| ≤ KA

/-- **`𝒲^{6,∞}`-pricing supplies the pointwise slot bounds.** -/
theorem slotPrice_of_WlInf {α KA : ℝ} {Aa : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (h6 : ContDiffOn ℝ 6 (Function.uncurry Aa) Work.FTS.EllipticEst.Q0)
    (hm : Work.Spaces.WlInfMem α 6 Aa) (hb : Work.Spaces.WlInf α 6 Aa ≤ KA) :
    SlotPrice (2000 * KA) Aa := by
  have hW : 0 ≤ Work.Spaces.WlInf α 6 Aa := Work.Spaces.WlInf_nonneg α 6 Aa hm
  intro i j hij z θ hz hθ1 hθ2
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ1, hθ2⟩
  have hsin0 : 0 ≤ Real.sin (2 * θ) :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ2, Real.pi_pos])).le
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · -- the pure `D_z`-slot: `mixed i 0 = DzIter i`
    subst hj0
    simp only [Work.Spaces.mixed_zero_right]
    have h1 := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_le_WlInf6_cd6
      (α := α) (f := Aa) h6 hm (show i ≤ 6 by omega) hz hθ
    have h2 : (1000 : ℝ) * Work.Spaces.WlInf α 6 Aa ≤ 2000 * KA := by linarith
    linarith
  · -- the mixed slot: the angular `𝒲^{6,∞}`-family carries the gain `(α + σ)σ^{α/5} ≤ 2`
    have h1 := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mixed_le_WlInf6_cd6
      (α := α) (f := Aa) hα h6 hm hjpos (show j + i ≤ 6 by omega) hz hθ
    have hσ1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hrpow1 : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 := Real.rpow_le_one hsin0 hσ1 (by linarith)
    have hfac : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
      have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
      have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hsin0 _
      nlinarith
    have h3 : Work.Spaces.WlInf α 6 Aa
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ≤ KA * 2 :=
      mul_le_mul hb hfac (mul_nonneg (by linarith) (Real.rpow_nonneg hsin0 _)) (by linarith)
    linarith

/-- Monotonicity of the canonical weight in its exponent, for `0 ≤ q ≤ q'`. -/
theorem canonW_q_le_gam {α q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ Work.Spaces.gam α) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.TransportS.SlotT2.canonW q z θ
      ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
  rcases eq_or_lt_of_le hq0 with h | h
  · subst h
    unfold Work.FTS.TransportS.SlotT2.canonW
    rw [neg_zero, Real.rpow_zero, mul_one]
    calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.TransportS.one_le_rpow_neg (by linarith [Work.Spaces.gam_sub_one α]) hθ)
            (sq_nonneg _)
  · exact Work.FTS.TransportS.SlotT2.canonW_mono h hq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- Monotonicity of the canonical weight up to `η`. -/
theorem canonW_q_le_eta {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ Work.Spaces.eta) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.TransportS.SlotT2.canonW q z θ
      ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ := by
  rcases eq_or_lt_of_le hq0 with h | h
  · subst h
    unfold Work.FTS.TransportS.SlotT2.canonW
    rw [neg_zero, Real.rpow_zero, mul_one]
    calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left
            (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ) (sq_nonneg _)
  · exact Work.FTS.TransportS.SlotT2.canonW_mono h hq ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- Every leaf weight of the slot `a` is dominated by the `γ`-weight on the open quadrant. -/
theorem leaf_le_canonW_gam {α : ℝ} (hα : 0 < α) {ρ : ℝ → ℝ → ℝ} {a : ℕ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
  rcases hleaf with rfl | rfl | ⟨ha, rfl⟩
  · have hηγ : Work.Spaces.eta ≤ Work.Spaces.gam α := by
      rw [Work.Spaces.gam]
      have := Work.Spaces.eta_lt_one
      linarith
    have h := canonW_q_le_gam (α := α) (q := Work.Spaces.eta) (z := z) (θ := θ)
      Work.Spaces.eta_nonneg hηγ hθ
    simpa only [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.leafEta] using h
  · have hgam0 : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.TransportS.one_le_rpow_neg hgam0 hθ
    calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · rfl

/-- When `a = 0` every leaf weight is dominated by the `η`-weight. -/
theorem leaf_le_canonW_eta {α : ℝ} {ρ : ℝ → ℝ → ℝ} {a : ℕ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (ha : a = 0) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ := by
  rcases hleaf with rfl | rfl | ⟨h1, _⟩
  · rfl
  · have h2 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
    calc (Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * 1 := by ring
      _ ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  · omega

/-- A pure `z`-slot under the `η`-weight is a summand of `HkIntegrand α k`. -/
theorem canonW_eta_zslot_le_Hk {α : ℝ} {g : ℝ → ℝ → ℝ} {k i : ℕ} (hi : i ≤ k) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ * (Work.Spaces.DzIter i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h : Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
      = (Work.FTS.H2.Whz z θ) ^ 2 :=
    Work.FTS.TransportS.SlotT2.canonW_eta_eq z θ hθI
  calc Work.FTS.TransportS.SlotT2.canonW Work.Spaces.eta z θ
        * (Work.Spaces.DzIter i g z θ) ^ 2
      = (Work.FTS.H2.Whz z θ) ^ 2 * (Work.Spaces.DzIter i g z θ) ^ 2 := by rw [h]
    _ = (Work.Spaces.DzIter i g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        rw [Work.FTS.H2.Whz]; ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ := Work.Spaces.sq_le_HkIntegrand_z α k g z θ i hi

/-- A mixed slot with angular order `≥ 1`, under the `γ`-weight, is a summand of
`HkIntegrand α k`. -/
theorem canonW_gam_mslot_le_Hk {α : ℝ} {g : ℝ → ℝ → ℝ} {k j i : ℕ} (hi : 1 ≤ i)
    (hij : i + j ≤ k) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α k g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h := Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθI
  calc Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
        * (Work.Spaces.mixed j i g z θ) ^ 2
      = (Work.Spaces.Wt α z θ) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2 := by rw [h]
    _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
    _ ≤ Work.Spaces.HkIntegrand α k g z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k g z θ i j hi hij

/-- Joint continuity of the canonical weight on the open quadrant. -/
theorem continuousOn_canonW (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.TransportS.SlotT2.canonW q p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
    have h2 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
    have h0 : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)), p.1 ^ 2 ≠ 0 :=
      fun p hp => pow_ne_zero 2 (ne_of_gt hp.1)
    have h3 := ContinuousOn.div₀ (f := fun p : ℝ × ℝ => (1 + p.1) ^ 2)
      (g := fun p : ℝ × ℝ => p.1 ^ 2) (s := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))
      h1 h2 h0
    simpa only [Work.Spaces.w] using h3
  have hs : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  have hspos : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      0 < Real.sin (2 * p.2) :=
    fun p hp => Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2, Real.pi_pos])
  have hs' := ContinuousOn.rpow_const (f := fun p : ℝ × ℝ => Real.sin (2 * p.2)) (p := -q) hs
    (fun p hp => Or.inl (ne_of_gt (hspos p hp)))
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * Real.sin (2 * p.2) ^ (-q))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := (hw.pow 2).mul hs'
  simpa only [Work.FTS.TransportS.SlotT2.canonW] using hmain

/-- The paired `g`-slot, under the leaf weight with exponent `q`, is dominated by the
level-six integrand. -/
theorem canonW_q_Zslot_le_Hk6 {α q : ℝ} {g : ℝ → ℝ → ℝ} {a b : ℕ} (hq0 : 0 ≤ q)
    (hqγ : q ≤ Work.Spaces.gam α) (hqη : a = 0 → q ≤ Work.Spaces.eta)
    (hab : a + b ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    simp only [Work.Spaces.mixed_zero_right]
    refine le_trans (mul_le_mul_of_nonneg_right (canonW_q_le_eta hq0 (hqη rfl) hθ)
      (sq_nonneg _)) ?_
    exact canonW_eta_zslot_le_Hk (show b ≤ 6 by omega) hθ
  · refine le_trans (mul_le_mul_of_nonneg_right (canonW_q_le_gam hq0 hqγ hθ)
      (sq_nonneg _)) ?_
    exact canonW_gam_mslot_le_Hk (i := a) (j := b) (by omega) (by omega) hθ



/-- The paired `g`-slot, under a leaf weight, is dominated by the level-six integrand. -/
theorem leaf_Zslot_le_Hk6 {α : ℝ} (hα : 0 < α) {ρ : ℝ → ℝ → ℝ} {a b : ℕ}
    {g : ℝ → ℝ → ℝ} (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ρ z θ * (Work.Spaces.mixed b a g z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases Nat.eq_zero_or_pos a with ha0 | hapos
  · subst ha0
    simp only [Work.Spaces.mixed_zero_right]
    exact le_trans (mul_le_mul_of_nonneg_right (leaf_le_canonW_eta hleaf rfl hθ) (sq_nonneg _))
      (canonW_eta_zslot_le_Hk (show b ≤ 6 by omega) hθ)
  · exact le_trans
      (mul_le_mul_of_nonneg_right (leaf_le_canonW_gam hα hleaf hθ) (sq_nonneg _))
      (canonW_gam_mslot_le_Hk (α := α) (g := g) (k := 6) (i := a) (j := b)
        (by omega) (by omega) hθ)

/-- The `g`-slot produced by a Leibniz summand with `i + j ≥ 1`, under a leaf weight, is
dominated by the level-six integrand. -/
theorem leaf_Y_le_Hk6 {α : ℝ} (hα : 0 < α) {ρ : ℝ → ℝ → ℝ} {a b : ℕ} {g : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) {i j : ℕ} (hij : 1 ≤ i + j)
    (hi : i ≤ b) (hj : j ≤ a) (hab : a + b ≤ 6) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ρ z θ * (Work.Spaces.mixed (b - i) (a - j + 1) g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  exact le_trans (mul_le_mul_of_nonneg_right (leaf_le_canonW_gam hα hleaf hθ) (sq_nonneg _))
    (canonW_gam_mslot_le_Hk (α := α) (g := g) (k := 6) (i := a - j + 1) (j := b - i)
      (by omega) (by omega) hθ)

end PmdbAux
