import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.N6Trans.HardPair

/-- **The two-mixed-slot `ℋ⁶` pairing with a leaf weight.**  For a slot with at least one
angular derivative (`1 ≤ m`, `m + b ≤ 6`), every leaf weight `ρ` of that slot is dominated, on
the open quadrant (`0 < z`, `0 < θ < π/2`), by the canonical weight `canonW (gam α) = w²σ^{-γ}`;
since the leaf weights of *that* slot are exactly `canonW η`, `canonW 0` and `canonW γ`, and
`canonW q ≤ canonW γ` for every `q ∈ {η, 0, γ}`, the associated two-slot AM–GM estimate
`canonW_pair_le6` applies verbatim.  This is the `a ≥ 1` (mixed) instance, where the two `g`-slots
are priced at the *matched* weight `σ^{-γ}` and no `α`-loss occurs. -/
theorem leafW_pair_mixed_le_Hk (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {m : ℕ}
    (hρ : Work.FTS.TransportS.IsLeafW α m ρ) {j i b : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 6)
    (hm : 1 ≤ m) (hmb : m + b ≤ 6) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ρ z θ * |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b m g z θ|
      ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hρle : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
    have h1 : ρ z θ ≤ Work.FTS.TransportS.slotW α m z θ :=
      (Work.FTS.TransportS.IsLeafW_le α hα hρ).2 z θ hz hθ.1 hθ.2
    have h2 : Work.FTS.TransportS.slotW α m z θ
        = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ := by
      rw [Work.FTS.TransportS.slotW_of_pos' α hm]
      exact (Work.FTS.TransportS.SlotT2.canonW_gam_eq α z θ hθI).symm
    rwa [h2] at h1
  have hpair : Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
      * |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b m g z θ|
      ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := g) (q := Work.Spaces.gam α)
      (Work.Spaces.gam_pos hα) le_rfl (fun h => absurd h (by omega)) (fun h => absurd h (by omega))
      hij hmb (le_of_lt hz) hθI
  have hABnn : 0 ≤ |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b m g z θ| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc ρ z θ * |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b m g z θ|
      = ρ z θ * (|Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b m g z θ|) := by ring
    _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
          * (|Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b m g z θ|) :=
        mul_le_mul_of_nonneg_right hρle hABnn
    _ = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α) z θ
          * |Work.Spaces.mixed j i g z θ| * |Work.Spaces.mixed b m g z θ| := by ring
    _ ≤ Work.Spaces.HkIntegrand α 6 g z θ := hpair

/-- **The `mixedTerm` of the level-six hard pairing (pointwise form).**  At a slot `(a,b)`
(`a + b ≤ 6`) whose first `f`-factor carries an angular derivative (`1 ≤ a₁ < a`), the weight
`ρ` (a leaf weight of the slot `(a,b)`), the `f`-factor and the two `g`-factors `D_z^{b-b₁+1}
D_θ^{a-a₁}g`, `D_z^bD_θ^ag` are dominated pointwise by `|f|_{𝒲^{6,∞}} · HkIntegrand α 6 g`, with
a constant independent of `α`.

`|mixed b₁ a₁ f| ≤ 1000 |f| (α + σ)σ^{α/5} ≤ 2000 |f|` by `mixed_le_WlInf6` (`1 ≤ a₁`,
`a₁ + b₁ ≤ 6`), `ρ ≤ canonW (gam α)` (`IsLeafW_le` and `1 ≤ a`), and the two *mixed* `g`-slots
are absorbed by the matched-weight AM–GM estimate `canonW_pair_le6` (`1 ≤ a - a₁`,
`(a - a₁) + (b - b₁ + 1) ≤ 6`, `1 ≤ a`, `a + b ≤ 6`). -/
theorem mixedTerm_le_six : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 →
    ∀ (f g : ℝ → ℝ → ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 6 g →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      1 ≤ a₁ → a₁ < a → a₁ + b₁ ≤ 6 → b₁ ≤ b →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ
            * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
          * |Work.Spaces.mixed b a g z θ|
        ≤ C * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ := by
  refine ⟨2001, by norm_num, ?_⟩
  intro α hα hα1 f g a b a₁ b₁ ρ hf hfm hg hgm hab hρ ha₁ ha₁a ha₁b₁ hb₁b z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the index bookkeeping
  have ha : 1 ≤ a := by omega
  have haa : 1 ≤ a - a₁ := by omega
  have hsum2 : (a - a₁) + (b - b₁ + 1) ≤ 6 := by omega
  -- the two `g`-slots against the leaf weight
  have hpair : ρ z θ * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
      * |Work.Spaces.mixed b a g z θ| ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
    leafW_pair_mixed_le_Hk α hα hρ haa hsum2 ha hab hz hθ
  have hWnn : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ := by
    have h0 := Work.Spaces.sq_le_HkIntegrand_z α 6 g z θ 0 (by norm_num)
    have hsq : 0 ≤ (Work.Spaces.DzIter 0 g z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := sq_nonneg _
    linarith
  -- `(α + σ)σ^{α/5} ≤ 2` on the open quadrant (σ = sin(2θ) ∈ (0,1])
  have hfac : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
    have hpos : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos, hθ1])
    have hle1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hr : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
      Real.rpow_le_one hpos.le hle1 (by positivity)
    have hr0 : 0 ≤ (Real.sin (2 * θ)) ^ (α / 5) := Real.rpow_nonneg hpos.le _
    have h1 : α + Real.sin (2 * θ) ≤ 2 := by linarith
    simpa using mul_le_mul h1 hr hr0 (by norm_num : (0 : ℝ) ≤ 2)
  -- the `f`-factor: `|D_z^{b₁}D_θ^{a₁} f| ≤ 2000 |f|_{𝒲^{6,∞}}`
  have hfb : |Work.Spaces.mixed b₁ a₁ f z θ| ≤ 2000 * Work.Spaces.WlInf α 6 f := by
    have h := Work.FTS.StrongPersist.N6Trans.L6FBound.mixed_le_WlInf6 hα hf hfm ha₁ ha₁b₁ hz hθ
    have hfacW : Work.Spaces.WlInf α 6 f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        ≤ Work.Spaces.WlInf α 6 f * 2 := mul_le_mul_of_nonneg_left hfac hWnn
    calc |Work.Spaces.mixed b₁ a₁ f z θ|
        ≤ 1000 * (Work.Spaces.WlInf α 6 f
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := h
      _ ≤ 1000 * (Work.Spaces.WlInf α 6 f * 2) := by linarith
      _ = 2000 * Work.Spaces.WlInf α 6 f := by ring
  calc ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ
          * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
        * |Work.Spaces.mixed b a g z θ|
      = |Work.Spaces.mixed b₁ a₁ f z θ| * (ρ z θ
          * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
          * |Work.Spaces.mixed b a g z θ|) := by rw [abs_mul]; ring
    _ ≤ |Work.Spaces.mixed b₁ a₁ f z θ| * Work.Spaces.HkIntegrand α 6 g z θ :=
        mul_le_mul_of_nonneg_left hpair (abs_nonneg _)
    _ ≤ (2000 * Work.Spaces.WlInf α 6 f) * Work.Spaces.HkIntegrand α 6 g z θ :=
        mul_le_mul_of_nonneg_right hfb hHknn
    _ ≤ 2001 * Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ := by
        have hWH : 0 ≤ Work.Spaces.WlInf α 6 f * Work.Spaces.HkIntegrand α 6 g z θ :=
          mul_nonneg hWnn hHknn
        nlinarith

end Work.FTS.StrongPersist.N6Trans.HardPair
