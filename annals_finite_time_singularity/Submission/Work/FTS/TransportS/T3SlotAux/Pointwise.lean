/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T3SlotAux/Pointwise`: the pointwise inputs of the per-slot transport bound

This module collects the pointwise estimates needed by the proof of
`Work.FTS.TransportS.T3Slot` (the `t3SlotGuarded` task):

* `qOf α a` — the angular exponent of the *canonical* slot weight `canonW q` of the slot with
  `a` angular derivatives: `η` for the pure `D_z` slot (`a = 0`), `γ` for the mixed slots;
* `IsLeafW.nonneg`, `IsLeafW.le_canonW` — the three leaf weights of `IP4` are nonnegative on
  `Iθ` and dominated by the canonical weight of their slot;
* `dzIter_le_WlInf_open` — `|D_z^b f| ≤ 100 |f|_{𝒲^{4,∞}}` on the open quadrant, for
  `SmoothOpen f` (`b ≤ 4`), by the Stirling expansion `D_z^b = ∑_k S(b,k) z^k ∂_z^k`;
* `canonW_pair_le` — the two-factor `ℋ⁴` AM–GM estimate: the canonical slot weight times two
  `ℋ⁴`-slots (of the *same* weight compatibility class) is dominated by `HkIntegrand α 4 g`.

All declarations are `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.TransportS.T3BadAux.slot_prod_le
import Submission.Work.FTS.H2.OpenPort.coefTh3_mixed_gain
import Submission.Work.FTS.OpenPkg.ScoefOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T3SlotAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The canonical exponent of a slot -/

/-- The angular exponent of the canonical weight of the slot with `a` angular derivatives:
`η` for the pure `D_z` slot (`a = 0`) and `γ` for the mixed slots (`a ≥ 1`). -/
def qOf (α : ℝ) (a : ℕ) : ℝ := if a = 0 then Work.Spaces.eta else Work.Spaces.gam α

theorem qOf_zero (α : ℝ) : qOf α 0 = Work.Spaces.eta := by simp [qOf]

theorem qOf_of_ne {α : ℝ} {a : ℕ} (ha : a ≠ 0) : qOf α a = Work.Spaces.gam α := by
  simp [qOf, ha]

theorem qOf_pos (α : ℝ) (hα : 0 < α) (a : ℕ) : 0 < qOf α a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [qOf_zero]; exact Work.Spaces.eta_pos
  · rw [qOf_of_ne ha]; exact Work.Spaces.gam_pos hα

theorem qOf_le_gam (α : ℝ) (hα : 0 < α) (a : ℕ) : qOf α a ≤ Work.Spaces.gam α := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [qOf_zero, Work.Spaces.gam, Work.Spaces.eta]
    linarith
  · rw [qOf_of_ne ha]

/-! ## The leaf weights -/

/-- Every leaf weight is nonnegative on `Iθ`. -/
theorem IsLeafW.nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ} (h : IsLeafW α a ρ) (z : ℝ) :
    ∀ ⦃θ : ℝ⦄, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ := by
  intro θ hθ
  rcases h with rfl | rfl | ⟨_, rfl⟩
  · exact leafEta_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)
  · exact leafOne_nonneg z θ
  · exact leafGam_nonneg α (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ)

/-- On the open quadrant every leaf weight is dominated by the canonical weight of its slot. -/
theorem IsLeafW.le_canonW {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : IsLeafW α a ρ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (qOf α a) z θ := by
  have hI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h1 : ρ z θ ≤ slotW α a z θ := (IsLeafW_le α hα h).2 z θ hz hθ.1 hθ.2
  rcases eq_or_ne a 0 with ha0 | ha
  · subst ha0
    rw [qOf_zero]
    refine h1.trans (le_of_eq ?_)
    rw [slotW_zero_eq α hθ]
    rfl
  · rw [qOf_of_ne ha]
    refine h1.trans (le_of_eq ?_)
    rw [slotW_of_pos_eq α (Nat.one_le_iff_ne_zero.mpr ha) hθ]
    rfl

/-! ## The `𝒲^{4,∞}`-bounds on the pure `z`-derivatives of the coefficient -/

/-- `|D_z^b f| ≤ 100 |f|_{𝒲^{4,∞}}` on the open quadrant, for `b ≤ 4`, by the Stirling
expansion `D_z^b = ∑_{k≤b} S(b,k) z^k ∂_z^k`. -/
theorem dzIter_le_WlInf_open {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hfm : Work.Spaces.WlInfMem α 4 f)
    {b : ℕ} (hb : b ≤ 4) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Spaces.DzIter b f z θ| ≤ 100 * Work.Spaces.WlInf α 4 f := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open (hsf.curry_z hθ) b z hz]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (Work.Spaces.WlInf α 4 f)
    (fun k => z ^ k * Work.Spaces.pzIter k f z θ)
    (fun k hk => Work.Spaces.zpz_le_WlInf hfm (le_trans hk hb) (le_of_lt hz) hθI)
  have hW : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
  have hb100 : (Work.Spaces.bell b : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le b hb
  calc |∑ k ∈ Finset.range (b + 1),
        (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k f z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * Work.Spaces.WlInf α 4 f := hsum
    _ ≤ 100 * Work.Spaces.WlInf α 4 f := mul_le_mul_of_nonneg_right hb100 hW

/-! ## The two-factor `ℋ⁴` AM–GM estimate -/

/-- A single canonical slot is dominated by `HkIntegrand α 4 g`: the pure `D_z` version. -/
theorem canonW_mul_z_le_Hk {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hq : q ≤ Work.Spaces.eta) {j : ℕ} (hj : j ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.DzIter j g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | h0
  · subst h0
    rw [Work.FTS.TransportS.SlotT2.canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
  · exact Work.FTS.TransportS.SlotT2.canonW_mul_z_le α g hq0 hq h0 hθ j hj

/-- A single canonical slot is dominated by `HkIntegrand α 4 g`: the mixed version. -/
theorem canonW_mul_mixed_le_Hk {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {j i : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with h0 | h0
  · subst h0
    rw [Work.FTS.TransportS.SlotT2.canonW_zero_z, zero_mul]
    exact Work.Spaces.HkIntegrand_nonneg α 4 g 0 θ
  · exact Work.FTS.TransportS.SlotT2.canonW_mul_mixed_le α g hq0 hqγ h0 hθ j i hi hij

/-- A single canonical slot of the correct weight class is dominated by `HkIntegrand α 4 g`. -/
theorem canonW_slot_le_Hk {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {j i : ℕ} (hi : i = 0 → q ≤ Work.Spaces.eta)
    (hij : i + j ≤ 4) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_ne i 0 with rfl | hi'
  · simpa only [Work.Spaces.mixed_zero_right] using
      canonW_mul_z_le_Hk (α := α) (g := g) hq0 (hi rfl) (by omega) hz hθ
  · exact canonW_mul_mixed_le_Hk (α := α) (g := g) hq0 hqγ
      (Nat.one_le_iff_ne_zero.mpr hi') hij hz hθ

/-- **The two-factor `ℋ⁴` AM–GM estimate.**  For two slots `D_z^jD_θ^ig`, `D_z^bD_θ^ag` of
`ℋ⁴` whose weight classes both dominate the canonical weight `canonW q` (i.e. `i = 0` and
`a = 0` force `q ≤ η`), the product of the canonical slot weight with the two absolute values
is dominated by the `ℋ⁴`-integrand. -/
theorem canonW_pair_le {α : ℝ} {g : ℝ → ℝ → ℝ} {q : ℝ} (hq0 : 0 < q)
    (hqγ : q ≤ Work.Spaces.gam α) {j i b a : ℕ} (hi : i = 0 → q ≤ Work.Spaces.eta)
    (ha : a = 0 → q ≤ Work.Spaces.eta) (hij : i + j ≤ 4) (hab : a + b ≤ 4)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i g z θ|
        * |Work.Spaces.mixed b a g z θ|
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hG := canonW_slot_le_Hk (α := α) (g := g) hq0 hqγ hi hij hz hθ
  have hY := canonW_slot_le_Hk (α := α) (g := g) hq0 hqγ ha hab hz hθ
  have hnn : 0 ≤ Work.FTS.TransportS.SlotT2.canonW q z θ :=
    Work.FTS.TransportS.SlotT2.canonW_nonneg hθ
  have habs : |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|
      ≤ ((Work.Spaces.mixed j i g z θ) ^ 2 + (Work.Spaces.mixed b a g z θ) ^ 2) / 2 := by
    rw [← abs_mul]
    exact Work.FTS.TransportS.T3BadAux.abs_mul_le_half_sq_add _ _
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
  have hfin : (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed j i g z θ) ^ 2) / 2
        + (Work.FTS.TransportS.SlotT2.canonW q z θ * (Work.Spaces.mixed b a g z θ) ^ 2) / 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    linarith
  calc Work.FTS.TransportS.SlotT2.canonW q z θ * |Work.Spaces.mixed j i g z θ|
        * |Work.Spaces.mixed b a g z θ|
      = Work.FTS.TransportS.SlotT2.canonW q z θ
        * (|Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b a g z θ|) := by ring
    _ ≤ _ := hkey
    _ = _ := hsplit
    _ ≤ _ := hfin

/-- The canonical slot weight is monotone in its exponent on the open quadrant. -/
theorem canonW_le_of_le {q q' : ℝ} (hqq : q ≤ q') {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.TransportS.SlotT2.canonW q z θ ≤ Work.FTS.TransportS.SlotT2.canonW q' z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rw [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.SlotT2.canonW]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith : -q' ≤ -q)

end Work.FTS.TransportS.T3SlotAux
