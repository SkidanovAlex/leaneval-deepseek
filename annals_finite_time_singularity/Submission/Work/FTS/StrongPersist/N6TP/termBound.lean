import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.N6Trans.L6Core
import Submission.Work.FTS.StrongPersist.N6Trans.L6Remainder
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.N6TP.termBound`

The *pointwise* per-summand estimate of the level-six `D_z`-transport Leibniz expansion
(the pointwise companion of `Work.FTS.StrongPersist.N6TP.summandBound`).

At a slot `(a,b)` of total order `≤ 6` and a Leibniz index `(a₁,b₁) ≠ (0,0)`, the summand

`ρ · (D_z^{b₁}D_θ^{a₁} f) · (D_z^{b-b₁+1}D_θ^{a-a₁} g) · (D_z^bD_θ^a g)`

of the expansion of `mixed b a (f · D_z g)` is dominated pointwise on the open quadrant by

`(1000 |f|_{𝒲^{6,∞}} + Cf · CoefTh 5 f) · HkIntegrand α 6 g`.

The two regimes:

* `a₁ = 0` (so `b₁ ≥ 1`): the pure radial derivative `D_z^{b₁}f` is bounded by
  `1000 |f|_{𝒲^{6,∞}}` (`dzIter_le_WlInf6`), and the leaf weight `ρ` paired with the two
  `g`-slots is bounded by `HkIntegrand α 6 g` (`l6_summand_le_zero`, which runs the
  two-factor AM–GM estimate `canonW_pair_le6` at the canonical exponent of the slot).
* `1 ≤ a₁`: the caller's hypothesis supplies the *angular* gain
  `|D_z^{b₁}D_θ^{a₁}f| ≤ Cf sin(2θ) · CoefTh 5 f`; the extra factor `sin(2θ)` turns the leaf
  weight into `canonW (α/10)` (`sin_mul_leafW_le_canonW`), and the two *mixed* `g`-slots are
  again absorbed by `canonW_pair_le6` — this time at the exponent `α/10`, which is `≤ η` and
  `≤ γ`, so it is admissible in both slots.
-/

namespace Work.FTS.StrongPersist.N6TP

/-- For `q ≤ γ` the extra factor `sin(2θ)` converts the canonical weight `canonW q` into
`canonW (α/10)` on the open quadrant: `canonW q = w²σ^{-q}` with `σ = sin(2θ)`, so
`σ · canonW q = w²σ^{1-q} ≤ w²σ^{-α/10} = canonW (α/10)` because `0 < σ ≤ 1` and
`-α/10 ≤ 1 - q ⟺ q ≤ 1 + α/10 = γ`. -/
theorem sin_mul_canonW_le (α : ℝ) {q : ℝ} (hq : q ≤ Work.Spaces.gam α)
    {z θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin (2 * θ) * Work.FTS.TransportS.SlotT2.canonW q z θ
      ≤ Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hexp : -(α / 10) ≤ 1 - q := by
    have h2 : Work.Spaces.gam α = 1 + α / 10 := rfl
    linarith [hq, h2]
  have hpow : Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-q)
      = (Real.sin (2 * θ)) ^ (1 - q) := by
    nth_rewrite 1 [← Real.rpow_one (Real.sin (2 * θ))]
    rw [← Real.rpow_add hs 1 (-q)]
    congr 1
  have hle : (Real.sin (2 * θ)) ^ (1 - q) ≤ (Real.sin (2 * θ)) ^ (-(α / 10)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp
  rw [Work.FTS.TransportS.SlotT2.canonW, Work.FTS.TransportS.SlotT2.canonW]
  have hre : Real.sin (2 * θ) * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q))
      = (Work.Spaces.w z) ^ 2 * ((Real.sin (2 * θ)) ^ (1 - q)) := by
    rw [← hpow]; ring
  rw [hre]
  exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- The same for a leaf weight `ρ` of the slot `a`: `sin(2θ)·ρ ≤ canonW (α/10)`, because
`ρ ≤ canonW (qOf α a)` with `qOf α a ≤ γ` (`IsLeafW.le_canonW`). -/
theorem sin_mul_leafW_le_canonW (α : ℝ) (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Real.sin (2 * θ) * ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ := by
  have hρ := Work.FTS.TransportS.T3SlotAux.IsLeafW.le_canonW hα hleaf hz hθ
  have hsin : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  exact (mul_le_mul_of_nonneg_left hρ hsin).trans
    (sin_mul_canonW_le α (Work.FTS.TransportS.T3SlotAux.qOf_le_gam α hα a) hθ)

theorem termBound : ∀ (α Cf : ℝ), 0 < α → α ≤ 1 → 0 ≤ Cf →
    ∀ (f g : ℝ → ℝ → ℝ) (a b a₁ b₁ : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 6 f →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ → a₁ ≤ a → b₁ ≤ b →
      ¬ (a₁ = 0 ∧ b₁ = 0) →
      (∀ a₁ b₁ : ℕ, 1 ≤ a₁ → a₁ + b₁ ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b₁ a₁ f z θ| ≤ Cf * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 5 f) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ
            * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
          * |Work.Spaces.mixed b a g z θ|
        ≤ (1000 * Work.Spaces.WlInf α 6 f + Cf * Work.FTS.VocabO.CoefTh 5 f)
            * Work.Spaces.HkIntegrand α 6 g z θ := by
  intro α Cf hα hα1 hCfnn f g a b a₁ b₁ ρ hf hfm hab hleaf ha₁a hb₁b hne hgain z θ hz hθ0 hθ1
  by_cases ha₁ : a₁ = 0
  · -- the `a₁ = 0` regime: a pure radial derivative of the coefficient
    subst a₁
    have hb₁ : 1 ≤ b₁ := by
      rcases Nat.eq_zero_or_pos b₁ with h | h
      · exact absurd ⟨rfl, h⟩ hne
      · exact h
    have hWnn : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
    have hTnn : 0 ≤ Cf * Work.FTS.VocabO.CoefTh 5 f :=
      mul_nonneg hCfnn (Work.FTS.OpenPkg.CoefTh_nonneg 5 f)
    exact Work.FTS.StrongPersist.N6Trans.l6_summand_le_zero (α := α)
      (Mf := 1000 * Work.Spaces.WlInf α 6 f + Cf * Work.FTS.VocabO.CoefTh 5 f)
      hα (add_nonneg (mul_nonneg (by norm_num) hWnn) hTnn)
      (le_add_of_nonneg_right hTnn) hf hfm hleaf hab hb₁ hb₁b z θ hz hθ0 hθ1
  · -- the `1 ≤ a₁` regime: the angular gain `sin(2θ)` of the coefficient
    have ha₁pos : 1 ≤ a₁ := Nat.one_le_iff_ne_zero.mpr ha₁
    have ha₁b₁ : a₁ + b₁ ≤ 6 := by omega
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hWnn : 0 ≤ Work.Spaces.WlInf α 6 f := Work.Spaces.WlInf_nonneg α 6 f hfm
    have hTnn : 0 ≤ Work.FTS.VocabO.CoefTh 5 f := Work.FTS.OpenPkg.CoefTh_nonneg 5 f
    have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      Work.Spaces.HkIntegrand_nonneg α 6 g z θ
    have hρnn : 0 ≤ ρ z θ := Work.FTS.TransportS.T3SlotAux.IsLeafW.nonneg hleaf z hθI
    have hA : |Work.Spaces.mixed b₁ a₁ f z θ|
        ≤ Cf * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 5 f :=
      hgain a₁ b₁ ha₁pos ha₁b₁ z θ hz hθ0 hθ1
    have hCTnn : 0 ≤ Cf * Work.FTS.VocabO.CoefTh 5 f := mul_nonneg hCfnn hTnn
    have hsinρ : Real.sin (2 * θ) * ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ :=
      sin_mul_leafW_le_canonW α hα hleaf hz hθ
    have hqeta : α / 10 ≤ Work.Spaces.eta := by
      rw [Work.Spaces.eta]; linarith
    have hqgam : α / 10 ≤ Work.Spaces.gam α := by
      rw [Work.Spaces.gam]; linarith
    have hpair : Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ
        * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
        * |Work.Spaces.mixed b a g z θ| ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      Work.FTS.StrongPersist.N6Trans.canonW_pair_le6 (α := α) (g := g) (q := α / 10)
        (by linarith) hqgam (fun _ => hqeta) (fun _ => hqeta)
        (by omega) hab (le_of_lt hz) hθI
    have hBCnn : 0 ≤ |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
        * |Work.Spaces.mixed b a g z θ| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h4 : Real.sin (2 * θ) * ρ z θ * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
        * |Work.Spaces.mixed b a g z θ|
        ≤ Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ
        * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
        * |Work.Spaces.mixed b a g z θ| := by
      have h3 : (Real.sin (2 * θ) * ρ z θ)
            * (|Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
              * |Work.Spaces.mixed b a g z θ|)
          ≤ Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ
            * (|Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
              * |Work.Spaces.mixed b a g z θ|) :=
        mul_le_mul_of_nonneg_right hsinρ hBCnn
      calc Real.sin (2 * θ) * ρ z θ * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
            * |Work.Spaces.mixed b a g z θ|
          = (Real.sin (2 * θ) * ρ z θ)
            * (|Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ
            * (|Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := h3
        _ = Work.FTS.TransportS.SlotT2.canonW (α / 10) z θ
            * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
            * |Work.Spaces.mixed b a g z θ| := by ring
    calc ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ
            * Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
          * |Work.Spaces.mixed b a g z θ|
        = ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ|
            * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
            * |Work.Spaces.mixed b a g z θ| := by rw [abs_mul]; ring
      _ ≤ ρ z θ * (Cf * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 5 f)
            * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
            * |Work.Spaces.mixed b a g z θ| := by
          have h1 : ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ|
              ≤ ρ z θ * (Cf * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 5 f) :=
            mul_le_mul_of_nonneg_left hA hρnn
          have h2 : ρ z θ * |Work.Spaces.mixed b₁ a₁ f z θ|
                * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
              ≤ ρ z θ * (Cf * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 5 f)
                * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
      _ = Cf * Work.FTS.VocabO.CoefTh 5 f
            * (Real.sin (2 * θ) * ρ z θ
              * |Work.Spaces.mixed (b - b₁ + 1) (a - a₁) g z θ|
              * |Work.Spaces.mixed b a g z θ|) := by ring
      _ ≤ Cf * Work.FTS.VocabO.CoefTh 5 f * Work.Spaces.HkIntegrand α 6 g z θ :=
          mul_le_mul_of_nonneg_left (h4.trans hpair) hCTnn
      _ ≤ (1000 * Work.Spaces.WlInf α 6 f + Cf * Work.FTS.VocabO.CoefTh 5 f)
            * Work.Spaces.HkIntegrand α 6 g z θ := by
          have hle : Cf * Work.FTS.VocabO.CoefTh 5 f
              ≤ 1000 * Work.Spaces.WlInf α 6 f + Cf * Work.FTS.VocabO.CoefTh 5 f := by linarith
          exact mul_le_mul_of_nonneg_right hle hHnn

end Work.FTS.StrongPersist.N6TP
