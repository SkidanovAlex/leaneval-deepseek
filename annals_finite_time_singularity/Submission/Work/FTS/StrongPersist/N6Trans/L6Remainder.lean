/-
Copyright: work module for the Elgindi finite-time singularity project.

# The Leibniz remainder of the level-six `D_z`-transport slot pairing

For the slot `(a,b)` with `a + b ≤ 6` and the coefficient `f·D_z g`, the pairing
`∫∫ ρ · D_z^bD_θ^a(f·D_zg) · D_z^bD_θ^a g` splits into the *exceptional* term
`∫∫ ρ·f·(D_z(mixed b a g))·(mixed b a g)` (the all-derivatives-on-`g` term, handled by the
radial integration by parts) and the *remainder*, i.e. the Leibniz sum over the indices
`(a₁,b₁) ≠ (0,0)`:

* the summands with `a₁ = 0` carry a pure `D_z`-derivative of `f`, bounded by `|f|_{𝒲^{6,∞}}`
  (`dzIter_le_WlInf6`);
* the summands with `a₁ ≥ 1` carry the weak angular gain `(α+σ)σ^{α/5}` of `mixed_le_WlInf6`;
  on the weight `sin(2θ)^{-γ}` this is split into `α·σ^{α/5}` and `σ^{1+α/5}`, and since
  `γ - α/5 ≥ (η+γ)/2` exactly when `α ≤ 1/30`, the first piece is dominated by the
  two-slot product `(wσ^{-η/2}X)(wσ^{-γ/2}Y)` (bounded by `HkSq α 6 g` via `cs2_mixed_le`)
  while the second is dominated pointwise by `HkIntegrand α 6 g`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6Aux2
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6
import Submission.Work.FTS.TransportS.GoodOpenBase
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.OpenTwins

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
set_option maxHeartbeats 2000000

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg canonW_mono)

/-! ## Two elementary weight identities -/

/-- The split weight: `(w σ^{-q₁/2}X)(w σ^{-q₂/2}Y) = canonW ((q₁+q₂)/2)·|X|·|Y|` on the open
quadrant. -/
theorem wsq_split {z θ q₁ q₂ X Y : ℝ} (hs : 0 < Real.sin (2 * θ)) :
    (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₁ / 2)) * |X|)
        * (Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(q₂ / 2)) * |Y|)
      = canonW ((q₁ + q₂) / 2) z θ * |X| * |Y| := by
  have key : (Real.sin (2 * θ)) ^ (-(q₁ / 2)) * (Real.sin (2 * θ)) ^ (-(q₂ / 2))
      = (Real.sin (2 * θ)) ^ (-((q₁ + q₂) / 2)) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  rw [canonW]
  rw [show (Real.sin (2 * θ)) ^ (-((q₁ + q₂) / 2))
      = (Real.sin (2 * θ)) ^ (-(q₁ / 2)) * (Real.sin (2 * θ)) ^ (-(q₂ / 2)) from key.symm]
  ring

/-- `σ^{-(γ - α/5)} ≤ σ^{-(η+γ)/2}` for `α ≥ 1/30` on the quadrant.  (The comparison fails
for `α < 1/30`: the weight `sin(2θ)^{-(γ-α/5)}` is then intermediate between the pure-`D_z`
slot weight `sin(2θ)^{-η}` and the mixed slot weight `sin(2θ)^{-γ}`, and is dominated by
neither.) -/
theorem rpow_gamma_sub_le {α θ : ℝ} (hα : 0 < α) (hα30 : 1 / 30 ≤ α)
    (hs : 0 < Real.sin (2 * θ)) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - α / 5))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta + Work.Spaces.gam α) / 2) := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : -(Work.Spaces.eta + Work.Spaces.gam α) / 2
      ≤ -(Work.Spaces.gam α - α / 5) := by
    have h : (1 : ℝ) / 200 ≤ 3 * α / 20 := by linarith [hα30]
    have h1 : Work.Spaces.gam α - α / 5 - (Work.Spaces.eta + Work.Spaces.gam α) / 2
        = 1 / 200 - 3 * α / 20 := by
      rw [Work.Spaces.gam, Work.Spaces.eta]; ring
    linarith [h, h1]
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp

/-! ## The pointwise per-summand bounds -/

/-- **A Leibniz summand with `a₁ = 0`.**  The summand carries a pure `D_z`-derivative of `f`,
bounded by `|f|_{𝒲^{6,∞}}`; the two `g`-slots are then paired against the canonical weight
`canonW (qOf α a)` dominating the leaf weight `ρ`. -/
theorem l6_summand_le_zero {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} {a b b1 : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hMf : 0 ≤ Mf) (hWl : 1000 * Work.Spaces.WlInf α 6 f ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hfw : Work.Spaces.WlInfMem α 6 f)
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (hab : a + b ≤ 6)
    (hb1 : 1 ≤ b1) (hb1b : b1 ≤ b) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * |Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b - b1 + 1) a g z θ|
          * |Work.Spaces.mixed b a g z θ| ≤ Mf * Work.Spaces.HkIntegrand α 6 g z θ := by
  intro z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hρle : ρ z θ ≤ canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ :=
    Work.FTS.TransportS.T3SlotAux.IsLeafW.le_canonW hα hleaf hz hθ
  have hDfb : |Work.Spaces.mixed b1 0 f z θ| ≤ Mf := by
    rw [Work.Spaces.mixed_zero_right]
    exact (dzIter_le_WlInf6 hsf hfw (by omega) hz hθ).trans hWl
  have hj1 : a + (b - b1 + 1) ≤ 6 := by omega
  have hpair := canonW_pair_le6 (α := α) (g := g)
    (q := Work.FTS.TransportS.T3SlotAux.qOf α a)
    (Work.FTS.TransportS.T3SlotAux.qOf_pos α hα a)
    (Work.FTS.TransportS.T3SlotAux.qOf_le_gam α hα a)
    (j := b - b1 + 1) (i := a) (b := b) (a := a)
    (fun h => by rw [h]; exact le_of_eq (Work.FTS.TransportS.T3SlotAux.qOf_zero α))
    (fun h => by rw [h]; exact le_of_eq (Work.FTS.TransportS.T3SlotAux.qOf_zero α))
    hj1 hab (le_of_lt hz) hθI
  calc ρ z θ * |Work.Spaces.mixed b1 0 f z θ * Work.Spaces.mixed (b - b1 + 1) a g z θ|
        * |Work.Spaces.mixed b a g z θ|
      = (ρ z θ * |Work.Spaces.mixed b1 0 f z θ|)
        * (|Work.Spaces.mixed (b - b1 + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|) := by
        rw [abs_mul]; ring
    _ ≤ (Mf * canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ)
        * (|Work.Spaces.mixed (b - b1 + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        calc ρ z θ * |Work.Spaces.mixed b1 0 f z θ| ≤ ρ z θ * Mf :=
              mul_le_mul_of_nonneg_left hDfb (Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg
                hleaf z hθI)
          _ = Mf * ρ z θ := by ring
          _ ≤ Mf * canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ :=
              mul_le_mul_of_nonneg_left hρle hMf
    _ = Mf * (canonW (Work.FTS.TransportS.T3SlotAux.qOf α a) z θ
        * |Work.Spaces.mixed (b - b1 + 1) a g z θ| * |Work.Spaces.mixed b a g z θ|) := by ring
    _ ≤ Mf * Work.Spaces.HkIntegrand α 6 g z θ :=
        mul_le_mul_of_nonneg_left hpair hMf

-- ## The blocked piece: the summands with `a₁ ≥ 1` and `a₁ + b₁ ≥ 5`
--
-- The pointwise bound for these summands (`l6_summand_le_pos`) is stated here in
-- `Submission/Work/FTS/StrongPersist/N6Trans/NOTES_slotT3Six_gap.md`; it is provable for
-- `1/30 ≤ α` (via `rpow_gamma_sub_le` and the two-piece split of `(α+σ)σ^{α/5}`), but for
-- `α < 1/30` the weight `sin(2θ)^{-(γ-α/5)}` carried by the pure-`D_z` factor
-- `D_z^{b-b₁+1}g` is intermediate between the pure-`D_z` slot weight `sin(2θ)^{-η}` and the
-- mixed slot weight `sin(2θ)^{-γ}`, and is dominated by neither: every two-slot
-- Cauchy–Schwarz/AM–GM estimate for those summands requires
-- `2(γ - α/5) ≤ η + γ`, i.e. `α ≥ 1/30`.  See the NOTES file for the routes tried.

end Work.FTS.StrongPersist.N6Trans
