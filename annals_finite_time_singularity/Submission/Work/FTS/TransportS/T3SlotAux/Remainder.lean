/-
Copyright: work module for the Elgindi finite-time singularity project.

# `T3SlotAux/Remainder`: the non-exceptional part of the slot pairing

The slot pairing of the slot `(a,b)` with coefficient `f D_z g` is

`slotPairing ρ a b (f D_z g) g = ∫∫ ρ · D_z^bD_θ^a(f D_z g) · D_z^bD_θ^a g`.

Write `X = D_z^bD_θ^a(f D_z g)` and `Y = D_z^bD_θ^a g`.  The Leibniz expansion of `X` has the
term `f · D_z Y` (`(a1,b1) = (0,0)`), which has to be treated by the radial integration by
parts (`T3SlotAux/flux`), and all the other terms

`c(a1,b1) · (D_z^{b1}D_θ^{a1} f) · (D_z^{b-b1+1}D_θ^{a-a1} g)`,  `(a1,b1) ≠ (0,0)`,

which are bounded pointwise by AM–GM against the `ℋ⁴`-slots of `g`.

All declarations are `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.TransportS.T3SlotAux.Pointwise

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

/-! ## Elementary rearrangement -/

/-- The AM–GM rearrangement used for every Leibniz term: from a bound on the coefficient
factor and a bound on the product of the weight with the two `g`-factors, one gets the bound
on the full product. -/
theorem abs_term_le {ρ F G Y A X : ℝ} (h1 : ρ * |F| ≤ A) (h2 : A * (|G| * |Y|) ≤ X) :
    ρ * |F * G| * |Y| ≤ X := by
  rw [abs_mul]
  calc ρ * (|F| * |G|) * |Y| = (ρ * |F|) * (|G| * |Y|) := by ring
    _ ≤ A * (|G| * |Y|) :=
        mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ ≤ X := h2

/-! ## The σ-gain of the leaf weights -/

theorem eta_le_gam {α : ℝ} (hα : 0 < α) : Work.Spaces.eta ≤ Work.Spaces.gam α := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- `sin(2θ) · sin(2θ)^{-q} = sin(2θ)^{1-q}` on the open quadrant. -/
theorem sin_mul_sin_rpow_neg {θ q : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-q) = (Real.sin (2 * θ)) ^ (1 + -q) := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rw [Real.rpow_add hs, Real.rpow_one]

/-- **The σ-gain of the leaf weights.**  For every leaf weight `ρ` of the slot `a`, the
product `sin(2θ)·ρ` is dominated by the canonical weight `canonW (γ-1)`. -/
theorem IsLeafW.sigma_mul_le_canonW {α : ℝ} (hα : 0 < α) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (h : IsLeafW α a ρ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.sin (2 * θ) * ρ z θ
      ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
  have hkey : ∀ {q : ℝ}, q ≤ Work.Spaces.gam α →
      (Real.sin (2 * θ)) ^ (1 + -q) ≤ (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
    intro q hq
    refine Real.rpow_le_rpow_of_exponent_ge
      (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
      hs1 ?_
    linarith
  have hcanon : (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α))
      = Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := by
    rw [Work.FTS.TransportS.SlotT2.canonW,
      show -(Work.Spaces.gam α - 1) = 1 + -(Work.Spaces.gam α) by ring]
  rcases h with h | h | ⟨_, h⟩
  · subst h
    calc Real.sin (2 * θ) * leafEta z θ
        = (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
          rw [leafEta]; ring
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.eta)) := by
          rw [sin_mul_sin_rpow_neg hθ]
      _ ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left (hkey (eta_le_gam hα)) (sq_nonneg _)
      _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := le_of_eq hcanon
  · subst h
    have hone : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
      have h1 := one_le_rpow_neg (q := Work.Spaces.gam α - 1) (by linarith) hθ
      rwa [show -(Work.Spaces.gam α - 1) = 1 + -(Work.Spaces.gam α) by ring] at h1
    calc Real.sin (2 * θ) * leafOne z θ = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) := by
          rw [leafOne]; ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_left (le_trans hs1 hone) (sq_nonneg _)
      _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := le_of_eq hcanon
  · subst h
    calc Real.sin (2 * θ) * leafGam α z θ
        = (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          rw [leafGam]; ring
      _ = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (1 + -(Work.Spaces.gam α)) := by
          rw [sin_mul_sin_rpow_neg hθ]
      _ ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ := le_of_eq hcanon


/-! ## The pointwise bound on a single Leibniz term -/

/-- **One non-exceptional Leibniz term.**  For `(a1,b1) ≠ (0,0)` the summand
`(D_z^{b1}D_θ^{a1}f)·(D_z^{b-b1+1}D_θ^{a-a1}g)` of the Leibniz expansion of
`D_z^bD_θ^a(f D_z g)` is bounded, against the leaf weight `ρ`, by `Mf · HkIntegrand α 4 g`.

* for `a1 = 0` (hence `b1 ≥ 1`) the coefficient factor is a pure `D_z`-derivative, bounded by
  `Mf`, and the two `g`-factors are `ℋ⁴`-slots of the weight class of the slot `a`;
* for `a1 ≥ 1` the coefficient factor carries the σ-gain of `CoefTh 3`, and the extra factor
  `sin(2θ)` moves the weight to `canonW (γ-1)`, which still dominates the weight classes of the
  two `g`-factors (whose angular indices are `a - a1` and `a`). -/
theorem term_le {α Mf C_f : ℝ} {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hMf : 0 ≤ Mf)
    (hleaf : IsLeafW α a ρ) (hab : a + b ≤ 4) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b)
    (hne : ¬ (a1 = 0 ∧ b1 = 0))
    (hDzb : ∀ b1 : ℕ, 1 ≤ b1 → b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b1 f z θ| ≤ Mf)
    (hFmix : ∀ a1 b1 : ℕ, 1 ≤ a1 → a1 + b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b1 a1 f z θ| ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f)
    (hMfC : C_f * Work.FTS.VocabO.CoefTh 3 f ≤ Mf)
    {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    ρ z θ * |Work.Spaces.mixed b1 a1 f z θ
        * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
      ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hθ : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ1⟩
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hρnn : 0 ≤ ρ z θ := IsLeafW.nonneg hleaf z hθI
  rcases eq_or_ne a1 0 with ha1zero | ha1ne
  · -- the coefficient factor is a pure `D_z`-derivative
    subst ha1zero
    have hb1pos : 1 ≤ b1 := by
      rcases Nat.eq_zero_or_pos b1 with h | h
      · exact absurd ⟨rfl, h⟩ hne
      · exact h
    have hb1le : b1 ≤ 4 := by omega
    have hidx : (a - 0) + (b - b1 + 1) ≤ 4 := by
      have h := Nat.sub_add_cancel hb1
      omega
    have h1 : ρ z θ * |Work.Spaces.mixed b1 0 f z θ| ≤ Mf * ρ z θ := by
      rw [Work.Spaces.mixed_zero_right]
      calc ρ z θ * |Work.Spaces.DzIter b1 f z θ| ≤ ρ z θ * Mf :=
            mul_le_mul_of_nonneg_left (hDzb b1 hb1pos hb1le z θ hz hθ0 hθ1) hρnn
        _ = Mf * ρ z θ := by ring
    have h2 : (Mf * ρ z θ) * (|Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
        * |Work.Spaces.mixed b a g z θ|) ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
      have hle : ρ z θ ≤ Work.FTS.TransportS.SlotT2.canonW (qOf α a) z θ :=
        IsLeafW.le_canonW hα hleaf hz hθ
      have hq0 : 0 < qOf α a := qOf_pos α hα a
      have hqγ : qOf α a ≤ Work.Spaces.gam α := qOf_le_gam α hα a
      have hhi : (a - 0) = 0 → qOf α a ≤ Work.Spaces.eta := by
        intro h
        have ha0 : a = 0 := by omega
        rw [ha0]
        exact le_of_eq (qOf_zero α)
      have hha : a = 0 → qOf α a ≤ Work.Spaces.eta :=
        fun h => by rw [h]; exact le_of_eq (qOf_zero α)
      have hpair := canonW_pair_le (α := α) (g := g) (q := qOf α a) hq0 hqγ
        (j := b - b1 + 1) (i := a - 0) (b := b) (a := a) hhi hha hidx hab hzI hθI
      calc (Mf * ρ z θ) * (|Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|
            * |Work.Spaces.mixed b a g z θ|)
          = Mf * ((ρ z θ * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|)
            * |Work.Spaces.mixed b a g z θ|) := by ring
        _ ≤ Mf * ((Work.FTS.TransportS.SlotT2.canonW (qOf α a) z θ
              * |Work.Spaces.mixed (b - b1 + 1) (a - 0) g z θ|)
            * |Work.Spaces.mixed b a g z θ|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) (abs_nonneg _)) hMf
        _ ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := mul_le_mul_of_nonneg_left hpair hMf
    exact abs_term_le h1 h2
  · -- the coefficient factor carries the σ-gain of `CoefTh 3`
    have ha1pos : 1 ≤ a1 := Nat.one_le_iff_ne_zero.mpr ha1ne
    have hb1le : b1 ≤ 4 := by omega
    have hidx : (a - a1) + (b - b1 + 1) ≤ 4 := by
      have h1 := Nat.sub_add_cancel ha1
      have h2 := Nat.sub_add_cancel hb1
      omega
    have hsnn : 0 ≤ Real.sin (2 * θ) :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ0]) (by linarith [hθ1, Real.pi_pos]))
    have h1 : ρ z θ * |Work.Spaces.mixed b1 a1 f z θ|
        ≤ Mf * (Real.sin (2 * θ) * ρ z θ) := by
      have hF := hFmix a1 b1 ha1pos (by omega) z θ hz hθ0 hθ1
      have hFM : |Work.Spaces.mixed b1 a1 f z θ| ≤ Real.sin (2 * θ) * Mf := by
        calc |Work.Spaces.mixed b1 a1 f z θ|
            ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f := hF
          _ = Real.sin (2 * θ) * (C_f * Work.FTS.VocabO.CoefTh 3 f) := by ring
          _ ≤ Real.sin (2 * θ) * Mf := mul_le_mul_of_nonneg_left hMfC hsnn
      calc ρ z θ * |Work.Spaces.mixed b1 a1 f z θ| ≤ ρ z θ * (Real.sin (2 * θ) * Mf) :=
            mul_le_mul_of_nonneg_left hFM hρnn
        _ = Mf * (Real.sin (2 * θ) * ρ z θ) := by ring
    have h2 : (Mf * (Real.sin (2 * θ) * ρ z θ))
        * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
          * |Work.Spaces.mixed b a g z θ|) ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
      have hsig : Real.sin (2 * θ) * ρ z θ
          ≤ Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ :=
        IsLeafW.sigma_mul_le_canonW hα hleaf hθ
      have hq0 : 0 < Work.Spaces.gam α - 1 := by
        rw [Work.Spaces.gam]; linarith
      have hqγ : Work.Spaces.gam α - 1 ≤ Work.Spaces.gam α := by linarith
      have hqη : Work.Spaces.gam α - 1 ≤ Work.Spaces.eta := by
        rw [Work.Spaces.gam, Work.Spaces.eta]; linarith
      have hpair := canonW_pair_le (α := α) (g := g) (q := Work.Spaces.gam α - 1) hq0 hqγ
        (j := b - b1 + 1) (i := a - a1) (b := b) (a := a)
        (fun _ => hqη) (fun h => absurd h (by omega)) hidx hab hzI hθI
      calc (Mf * (Real.sin (2 * θ) * ρ z θ))
            * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)
          = Mf * ((Real.sin (2 * θ) * ρ z θ)
            * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
              * |Work.Spaces.mixed b a g z θ|)) := by ring
        _ ≤ Mf * ((Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
              * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|)
            * |Work.Spaces.mixed b a g z θ|) := by
            refine mul_le_mul_of_nonneg_left ?_ hMf
            calc Real.sin (2 * θ) * ρ z θ
                  * (|Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|
                    * |Work.Spaces.mixed b a g z θ|)
                = ((Real.sin (2 * θ) * ρ z θ)
                    * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|)
                  * |Work.Spaces.mixed b a g z θ| := by ring
              _ ≤ ((Work.FTS.TransportS.SlotT2.canonW (Work.Spaces.gam α - 1) z θ
                    * |Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ|)
                  * |Work.Spaces.mixed b a g z θ|) :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hsig (abs_nonneg _)) (abs_nonneg _)
        _ ≤ Mf * Work.Spaces.HkIntegrand α 4 g z θ := mul_le_mul_of_nonneg_left hpair hMf
    exact abs_term_le h1 h2

/-! ## The pointwise bound on the whole exceptional-free remainder -/

/-- **The Leibniz expansion and the pointwise bound on the remainder.**  On the open quadrant,

`D_z^bD_θ^a(f D_z g) - f · D_z(D_z^bD_θ^a g)`
  `= ∑_{(a1,b1) ≠ (0,0)} c(a1,b1)·(D_z^{b1}D_θ^{a1}f)·(D_z^{b-b1+1}D_θ^{a-a1}g)`,

and each summand is bounded by `Mf · HkIntegrand α 4 g` (`term_le`), so the whole remainder,
weighted by the leaf weight `ρ` and paired with `D_z^bD_θ^a g`, is bounded by
`6400 Mf HkIntegrand α 4 g`. -/
theorem remainder_pointwise {α Mf C_f : ℝ} {f g : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hMf : 0 ≤ Mf)
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.EllipticEst.SmoothOpen g)
    (hleaf : IsLeafW α a ρ) (hab : a + b ≤ 4)
    (hDzb : ∀ b1 : ℕ, 1 ≤ b1 → b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter b1 f z θ| ≤ Mf)
    (hFmix : ∀ a1 b1 : ℕ, 1 ≤ a1 → a1 + b1 ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b1 a1 f z θ| ≤ C_f * Real.sin (2 * θ) * Work.FTS.VocabO.CoefTh 3 f)
    (hMfC : C_f * Work.FTS.VocabO.CoefTh 3 f ≤ Mf) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |ρ z θ * (Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
          - f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ)
        * Work.Spaces.mixed b a g z θ|
        ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
  intro z θ hz hθ0 hθ1
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hρnn : 0 ≤ ρ z θ := IsLeafW.nonneg hleaf z hθI
  have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hleib := Work.FTS.TransportS.mixed_mul_Dz_open b a f g hsf hsg z θ hz hθ0 hθ1
  set s : Finset (ℕ × ℕ) := Finset.range (a + 1) ×ˢ Finset.range (b + 1) with hs
  set F : ℕ × ℕ → ℝ := fun p => (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ)
      * (Work.Spaces.mixed p.2 p.1 f z θ
        * Work.Spaces.mixed (b - p.2 + 1) (a - p.1) g z θ) with hF
  have hsumprod : (∑ a1 ∈ Finset.range (a + 1), ∑ b1 ∈ Finset.range (b + 1),
      (a.choose a1 : ℝ) * (b.choose b1 : ℝ)
        * (Work.Spaces.mixed b1 a1 f z θ
          * Work.Spaces.mixed (b - b1 + 1) (a - a1) g z θ))
      = ∑ p ∈ s, F p := by
    rw [hs]
    exact (Finset.sum_product (Finset.range (a + 1)) (Finset.range (b + 1)) F).symm
  have h00mem : ((0, 0) : ℕ × ℕ) ∈ s := by
    rw [hs]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hDz : Work.Spaces.mixed (b + 1) a g z θ
      = Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ := rfl
  have h00F : F (0, 0) = f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ := by
    rw [hF]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul,
      Nat.sub_zero, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, hDz]
  have hR : Work.Spaces.mixed b a (fun z θ => f z θ * Work.Spaces.Dz g z θ) z θ
        - f z θ * Work.Spaces.Dz (Work.Spaces.mixed b a g) z θ
      = ∑ p ∈ s.erase (0, 0), F p := by
    rw [hleib, hsumprod, ← h00F]
    exact (Finset.sum_erase_eq_sub (s := s) (f := F) (a := (0,0)) h00mem).symm
  have hterm : ∀ p ∈ s.erase (0, 0),
      |ρ z θ * F p * Work.Spaces.mixed b a g z θ|
        ≤ ((a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (Mf * Work.Spaces.HkIntegrand α 4 g z θ) := by
    intro p hp
    have hp' : p ∈ s := Finset.mem_of_mem_erase hp
    have hpne : p ≠ (0, 0) := Finset.ne_of_mem_erase hp
    rw [hs] at hp'
    have ha1 : p.1 ≤ a :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hp').1)
    have hb1 : p.2 ≤ b :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hp').2)
    have hne : ¬ (p.1 = 0 ∧ p.2 = 0) := by
      rintro ⟨h1, h2⟩
      exact hpne (by ext <;> simp [h1, h2])
    have hcore := term_le (α := α) (Mf := Mf) (C_f := C_f) (f := f) (g := g) (a := a) (b := b)
      (a1 := p.1) (b1 := p.2) (ρ := ρ) hα hα1 hMf hleaf hab ha1 hb1 hne hDzb hFmix hMfC
      hz hθ0 hθ1
    have hc : 0 ≤ (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) := by positivity
    calc |ρ z θ * F p * Work.Spaces.mixed b a g z θ|
        = ((a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (ρ z θ * |Work.Spaces.mixed p.2 p.1 f z θ
              * Work.Spaces.mixed (b - p.2 + 1) (a - p.1) g z θ|
            * |Work.Spaces.mixed b a g z θ|) := by
          rw [hF]
          simp only [abs_mul, abs_of_nonneg hρnn, abs_of_nonneg hc,
            abs_of_nonneg (show (0 : ℝ) ≤ ((a.choose p.1 : ℕ) : ℝ) by positivity),
            abs_of_nonneg (show (0 : ℝ) ≤ ((b.choose p.2 : ℕ) : ℝ) by positivity)]
          ring
      _ ≤ ((a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (Mf * Work.Spaces.HkIntegrand α 4 g z θ) := mul_le_mul_of_nonneg_left hcore hc
  have hcoef : ∀ p : ℕ × ℕ, (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) ≤ 256 := by
    intro p
    have ha4 : a ≤ 4 := by omega
    have hb4 : b ≤ 4 := by omega
    have h1 : (a.choose p.1 : ℝ) ≤ 16 := by
      have h : a.choose p.1 ≤ 2 ^ 4 :=
        le_trans (Nat.choose_le_two_pow a p.1) (Nat.pow_le_pow_right (by norm_num) ha4)
      exact_mod_cast h
    have h2 : (b.choose p.2 : ℝ) ≤ 16 := by
      have h : b.choose p.2 ≤ 2 ^ 4 :=
        le_trans (Nat.choose_le_two_pow b p.2) (Nat.pow_le_pow_right (by norm_num) hb4)
      exact_mod_cast h
    calc (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) ≤ 16 * 16 :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by norm_num)
      _ = 256 := by norm_num
  have hsumc : ∑ p ∈ s.erase (0, 0),
      (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ) ≤ 6400 := by
    have hcard : (s.erase (0, 0)).card ≤ 25 := by
      have h1 : s.card = (a + 1) * (b + 1) := by
        rw [hs, Finset.card_product]
        simp
      have h2 : (s.erase (0, 0)).card ≤ s.card := Finset.card_erase_le
      have ha4 : a ≤ 4 := by omega
      have hb4 : b ≤ 4 := by omega
      have hmul : (a + 1) * (b + 1) ≤ 25 := by
        have h3 : a + 1 ≤ 5 := by omega
        have h4 : b + 1 ≤ 5 := by omega
        exact le_trans (Nat.mul_le_mul h3 h4) (by norm_num)
      omega
    calc ∑ p ∈ s.erase (0, 0), (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ)
        ≤ ∑ _p ∈ s.erase (0, 0), (256 : ℝ) :=
          Finset.sum_le_sum fun p _ => hcoef p
      _ = ((s.erase (0, 0)).card : ℝ) * 256 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 25 * 256 := by
          have : ((s.erase (0, 0)).card : ℝ) ≤ 25 := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this (by norm_num)
      _ = 6400 := by norm_num
  have hmain : |ρ z θ * (∑ p ∈ s.erase (0, 0), F p) * Work.Spaces.mixed b a g z θ|
      ≤ 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by
    have h1 : ρ z θ * (∑ p ∈ s.erase (0, 0), F p) * Work.Spaces.mixed b a g z θ
        = ∑ p ∈ s.erase (0, 0), (ρ z θ * F p * Work.Spaces.mixed b a g z θ) := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [h1]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    calc (∑ p ∈ s.erase (0, 0), (a.choose p.1 : ℝ) * (b.choose p.2 : ℝ))
          * (Mf * Work.Spaces.HkIntegrand α 4 g z θ)
        ≤ 6400 * (Mf * Work.Spaces.HkIntegrand α 4 g z θ) :=
          mul_le_mul_of_nonneg_right hsumc (mul_nonneg hMf hHknn)
      _ = 6400 * Mf * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  rwa [← hR] at hmain

end Work.FTS.TransportS.T3SlotAux
