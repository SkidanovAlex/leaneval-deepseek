/-
Copyright: work module for the Elgindi finite-time singularity project.

# Level-six core slot lemmas for `Work.FTS.StrongPersist.N6Trans.slotT3Six`

This file collects the elementary, `α`-polynomial facts the per-slot `D_z`-transport bound at
level six (`slotT3Six`) consumes:

* `bell_le_six` — the Bell-number bound `bell n ≤ 1000` for `n ≤ 6` (the coefficient mass of
  the Stirling expansion `D_z^n = ∑_k S(n,k) z^k ∂_z^k`);
* `zpz_le_WlInf6`, `dzIter_le_WlInf6` — `|z^j ∂_z^j f| ≤ |f|_{𝒲^{6,∞}}` and
  `|D_z^b f| ≤ 1000 |f|_{𝒲^{6,∞}}` on the open quadrant (level-six instances of the proved
  level-four lemmas `Work.Spaces.zpz_le_WlInf` / `Work.FTS.OpenPkg.DzIter_le_WlInf_open`);
* `canonW_slot_le_Hk6` — a single canonical slot `canonW q · (D_z^jD_θ^i g)²` is dominated by
  `HkIntegrand α 6 g`, for `q ≤ η` when `i = 0` and `q ≤ γ` always (dispatcher over the
  proved `T1SixAux.canonW_mul_z_le6` / `canonW_mul_mixed_le6`);
* `canonW_zero_slot_le_Hk6` — the degenerate case `q = 0`, i.e. `w²` (only valid at interior
  angles, where the singular slot weights are `≥ 1`);
* `canonW_pair_le6` — the two-factor AM–GM form.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.Basic
import Submission.Work.FTS.TransportS.HardDefs
import Submission.Work.FTS.OpenPkg.DzIter_le_WlInf_open
import Submission.Work.FTS.OpenPkg.Mixed_le_WlInf_open
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.ProductRuleInW
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- `|a b| ≤ (a² + b²)/2`. -/
theorem abs_mul_le_half_sq_add6 (a b : ℝ) : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [abs_mul]
  nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]

/-! ## The Bell-number bound at level six -/

/-- The Bell numbers of the rows `0 ≤ n ≤ 6` are `1, 1, 2, 5, 15, 52, 203`, all below `1000`. -/
theorem bell_le_six (n : ℕ) (hn : n ≤ 6) : Work.Spaces.bell n ≤ 1000 := by
  interval_cases n <;> decide

/-! ## The `𝒲^{6,∞}`-bounds on the radial derivatives -/

/-- `|z^j ∂_z^j f| ≤ |f|_{𝒲^{6,∞}}` for `j ≤ 6`, on the domain. -/
theorem zpz_le_WlInf6 {α : ℝ} {f : ℝ → ℝ → ℝ} (hfm : Work.Spaces.WlInfMem α 6 f)
    {j : ℕ} (hj : j ≤ 6) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    |z ^ j * Work.Spaces.pzIter j f z θ| ≤ Work.Spaces.WlInf α 6 f := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have h := Work.Spaces.pz_sup_bound α 6 f hfm j hj z θ hz hθ
  have hW := Work.Spaces.WlInf_nonneg α 6 f hfm
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz0 j)]
  calc z ^ j * |Work.Spaces.pzIter j f z θ|
      ≤ z ^ j * (Work.Spaces.WlInf α 6 f / (z + 1) ^ j) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hz0 j)
    _ = Work.Spaces.WlInf α 6 f * (z / (z + 1)) ^ j := by rw [div_pow]; ring
    _ ≤ Work.Spaces.WlInf α 6 f * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hW
        exact pow_le_one₀ (div_nonneg hz0 (by linarith)) (by rw [div_le_one hz1]; linarith)
    _ = Work.Spaces.WlInf α 6 f := mul_one _

/-- `|D_z^b f| ≤ 1000 |f|_{𝒲^{6,∞}}` on the open quadrant, for `b ≤ 6`. -/
theorem dzIter_le_WlInf6 {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 6 f)
    {b : ℕ} (hb : b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 1000 * Work.Spaces.WlInf α 6 f := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hz' : z ∈ Set.Ioi (0 : ℝ) := hz
  have hslice : ContDiffOn ℝ Work.Stability.smoothOrder (fun z' => f z' θ) (Set.Ioi 0) :=
    Work.FTS.OpenPkg.smoothOpen_slice_z hf hθ
  have hDz : Work.Spaces.DzIter b f z θ
      = ∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ) :=
    Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hslice b z hz'
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 6 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => zpz_le_WlInf6 hfm (le_trans hk hb) hzI hθI)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 1000 := by
    exact_mod_cast bell_le_six b hb
  have hW : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  calc |Work.Spaces.DzIter b f z θ|
      = |∑ k ∈ Finset.range (b + 1),
          (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ)| := by rw [hDz]
    _ ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 6 f := hsum
    _ ≤ 1000 * Work.Spaces.WlInf α 6 f := mul_le_mul_of_nonneg_right hbell hW

/-! ## The single-slot domination at level six -/

/-- A single canonical slot is dominated by `HkIntegrand α 6 g`. -/
theorem canonW_slot_le_Hk6 {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {j i : ℕ} (hi : i = 0 → q ≤ Work.Spaces.eta)
    (hij : i + j ≤ 6) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  rcases eq_or_ne i 0 with hi0 | hine
  · subst hi0
    simpa only [Work.Spaces.mixed_zero_right] using
      Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_z_le6 α g hq0 (hi rfl) hθ j
        (by omega)
  · exact Work.FTS.StrongPersist.N6Trans.T1SixAux.canonW_mul_mixed_le6 α g hq0 hqγ hθ j i
      (Nat.one_le_iff_ne_zero.mpr hine) hij

/-- The degenerate case `q = 0` of the slot domination: `w²` times a slot square is dominated
by `HkIntegrand α 6 g` at interior angles (where every singular slot weight is `≥ 1`). -/
theorem canonW_zero_slot_le_Hk6 {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {j i : ℕ}
    (hij : i + j ≤ 6) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  rcases eq_or_ne i 0 with hi0 | hine
  · subst hi0
    rw [Work.Spaces.mixed_zero_right]
    have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
    have hstep : (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter j g z θ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hone
        (mul_nonneg (sq_nonneg (Work.Spaces.w z)) (sq_nonneg (Work.Spaces.DzIter j g z θ)))
      calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2
          = 1 * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2) := by ring
        _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2) := h
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter j g z θ) ^ 2 := by ring
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.DzIter j g z θ) ^ 2
        ≤ _ := hstep
      _ = (Work.Spaces.DzIter j g z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [mul_pow, Work.FTS.TransportS.sq_div_rpow hs0 Work.Spaces.eta]
          ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ j (by omega)
  · have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ
    have hstep : (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i g z θ) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hone
        (mul_nonneg (sq_nonneg (Work.Spaces.w z)) (sq_nonneg (Work.Spaces.mixed j i g z θ)))
      calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
          = 1 * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2) := by ring
        _ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * ((Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2) := h
        _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i g z θ) ^ 2 := by ring
    calc (Work.Spaces.w z) ^ 2 * (Work.Spaces.mixed j i g z θ) ^ 2
        ≤ _ := hstep
      _ = (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [mul_pow, Work.Spaces.Wt, Work.Spaces.wTheta,
            Work.FTS.TransportS.sq_mul_rpow_neg_half hs0 (Work.Spaces.gam α)]
          ring
      _ ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 g z θ i j
            (Nat.one_le_iff_ne_zero.mpr hine) hij

/-! ## The two-factor AM–GM form -/

/-- **The two-factor `ℋ⁶` AM–GM estimate.**  For two slots `D_z^jD_θ^ig`, `D_z^bD_θ^ag` whose
weight classes both dominate the canonical exponent `q` (`q ≤ η` whenever the angular index
vanishes, `q ≤ γ` always), the product of the canonical weight with the two absolute values is
dominated by `HkIntegrand α 6 g`. -/
theorem canonW_pair_le6 {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {j i b a : ℕ} (hi : i = 0 → q ≤ Work.Spaces.eta)
    (ha : a = 0 → q ≤ Work.Spaces.eta) (hij : i + j ≤ 6) (hab : a + b ≤ 6)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i g z θ|
        * |Work.Spaces.mixed b a g z θ| ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have hX := canonW_slot_le_Hk6 (α := α) (g := g) hq0 hqγ hi hij hz hθ
  have hY := canonW_slot_le_Hk6 (α := α) (g := g) hq0 hqγ ha hab hz hθ
  have hnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
    Work.FTS.TransportS.SlotT2.canonW_nonneg hθ
  have habs : |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|
      ≤ ((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
    simpa only [abs_mul] using abs_mul_le_half_sq_add6 _ _
  have hkey : Work.FTS.TransportS.SlotT2.canonW q z θ
        * (|Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|)
      ≤ Work.FTS.TransportS.SlotT2.canonW q z θ
        * (((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left habs hnn
  have hsplit : Work.FTS.TransportS.SlotT2.canonW q z θ
        * (((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2)
      = (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) / 2
        + (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
    ring
  calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i g z θ|
        * |Work.Spaces.mixed b a g z θ|
      = Work.FTS.TransportS.SlotT2.canonW q z θ
        * (|Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|) := by ring
    _ ≤ Work.FTS.TransportS.SlotT2.canonW q z θ
        * (((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2) := hkey
    _ = (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) / 2
        + (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2 :=
        hsplit
    _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := by linarith

end Work.FTS.StrongPersist.N6Trans
