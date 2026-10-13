/-
Copyright: work module for the Elgindi finite-time singularity project.

# `TransportS/T2Sup/PairBnd`: the pointwise bound of a Leibniz summand

The Leibniz expansion `mixed_mul_Dz_open` of the transport pairing with a slot `(a,b)` reads

  `mixed b a (f · D_z g) = ∑_{a1 ≤ a} ∑_{b1 ≤ b} C(a,a1)C(b,b1) · mixed b1 a1 f · mixed (b+1-b1) (a-a1) g`.

A summand is thus a triple product `f-slot × g-slot × g-slot`, and this module bounds every
summand *except* the single "delicate" one — the pair `(a1,b1) = (0,3)` at the slot
`(a,b) = (1,3)` with the angular exponent `q = γ`, where the `f`-slot `D_z³f` is a *pure*
`D_z`-slot (so no σ-gain is available and the `γ`-priced slot domination does not apply) and
both `g`-slots are of order `≥ 2`, so no Cauchy–Schwarz reduction to `HkIntegrand` works
either.  That one summand is the subject of the delegated `T2Sup.delicateBound`.

The bound produced here is the pointwise majorant

  `canonW q · |f-slot| · |g₁-slot| · |g₂-slot| ≤ (Mf + MK)·HkIntegrand α 4 g
      + Mg·√(HkIntegrand α 4 f)·√(HkIntegrand α 4 g)`

under the three pointwise hypotheses (`Mf` on the pure `D_z`-slots of `f` of order `≤ 2`,
`MK` on the σ-gain of the mixed slots of `f` of order `≤ 2`, `Mg` on the slots of `g` of
order `≤ 2`), which is what the three preceding majorant lemmas
`canonW_mul_abs_le_slotW`, `canonW_mul_abs_le_slotSigma` and `canonW_mul_abs_le_slotG` give.

The case analysis is by the total order `p = a1 + b1` of the `f`-slot:

* `a1 ≥ 1`, `p ≤ 2`: σ-gain case (`canonW_mul_abs_le_slotSigma`);
* `a1 ≥ 1`, `p ≥ 3`: the *middle* `g`-slot `mixed (b+1-b1) (a-a1) g` has order `≤ 2`, hence is
  bounded by `Mg`, and `canonW_mul_abs_le_slotG` applies;
* `a1 = 0`, `b1 ≤ 2`: the `f`-slot is `D_z^{b1} f`, bounded by `Mf`
  (`canonW_mul_abs_le_slotW`);
* `a1 = 0`, `b1 ≥ 3`, `q = η`: as in the second case, with the pure `f`-slot priced at `η`.

All declarations here rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.TransportS.T2Sup.Ptwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2Sup

set_option autoImplicit false

open Work.FTS.TransportS.SlotT2

/-- The slot `mixed b' a g`, whose `θ`-order is exactly `a`, is a canonical slot of `g` at the
exponent `q` determined by `a` (`η` for `a = 0`, `γ` for `a ≥ 1`). -/
theorem slotWo_theta_eq {α q : ℝ} {g : ℝ → ℝ → ℝ} {a b' : ℕ}
    (hα : 0 < α)
    (hq0 : a = 0 → q = Work.Spaces.eta) (hq1 : 0 < a → q = Work.Spaces.gam α)
    (hab : a + b' ≤ 4) :
    SlotWo α q (Work.Spaces.mixed b' a g) g := by
  rcases eq_or_ne a 0 with ha0 | ha0
  · subst ha0
    rw [hq0 rfl]
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using
      slotWo_z (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl g b' (by omega)
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    rw [hq1 (by omega)]
    exact slotWo_mixed (α := α) (q := Work.Spaces.gam α) (Work.Spaces.gam_pos hα) le_rfl
      g b' a ha1 (by omega)

/-- A `g`-slot of order `≤ 4` priced at `η` is a canonical slot. -/
theorem slotWo_eta_of {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {j i : ℕ} (hij : i + j ≤ 4) :
    SlotWo α Work.Spaces.eta (Work.Spaces.mixed j i g) g := by
  rcases Nat.eq_zero_or_pos i with hi0 | hip
  · subst hi0
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using
      slotWo_z (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl g j (by omega)
  · exact slotWo_mixed (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos
      (eta_le_gam hα) g j i hip (by omega)

/-- `η < γ` for `α > 0`. -/
theorem eta_lt_gam_of_pos {α : ℝ} (hα : 0 < α) : Work.Spaces.eta < Work.Spaces.gam α := by
  rw [Work.Spaces.gam]
  have : Work.Spaces.eta = 99 / 100 := rfl
  linarith

/-- `q ∈ {η, γ}` implies `q ≤ 1 + η` (the hypothesis of the σ-gain majorant). -/
theorem q_le_one_add_eta {α q : ℝ} (hα1 : α ≤ 1)
    (hq : q = Work.Spaces.eta ∨ q = Work.Spaces.gam α) :
    q ≤ 1 + Work.Spaces.eta := by
  rcases hq with h | h
  · rw [h]; linarith [Work.Spaces.eta_pos]
  · rw [h, Work.Spaces.gam]
    have : Work.Spaces.eta = 99 / 100 := rfl
    linarith [Work.Spaces.eta_lt_one]

/-- **The pointwise bound of a non-delicate Leibniz summand.** -/
theorem termPair_nd {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg)
    (hab : a + b ≤ 4) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) (hp1 : 1 ≤ a1 + b1)
    (hq0 : a = 0 → q = Work.Spaces.eta) (hq1 : 0 < a → q = Work.Spaces.gam α)
    (hnd : ¬ (a1 = 0 ∧ b1 = 3 ∧ q = Work.Spaces.gam α))
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
          + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
  intro z θ hz hθ hθ2
  have hHIg : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hSQnn : 0 ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
      * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases Nat.eq_zero_or_pos a1 with ha1z | ha1p
  · -- `a1 = 0`: the `f`-slot is the pure `D_z^{b1} f`
    subst ha1z
    simp only [Nat.sub_zero]
    by_cases hb12 : b1 ≤ 2
    · -- the `f`-slot is bounded by `Mf`
      have hbnd := canonW_mul_abs_le_slotW (α := α) (q := q) (KF := Mf)
        (X := Work.Spaces.DzIter b1 f)
        (G := Work.Spaces.mixed (b + 1 - b1) a g)
        (Y := Work.Spaces.mixed b a g)
        (slotWo_theta_eq hα hq0 hq1 (by omega))
        (slotWo_theta_eq hα hq0 hq1 (by omega))
        hMf (fun z θ hz hθ hθ2 => hFsup b1 hb12 z θ hz hθ hθ2) z θ hz hθ hθ2
      have h1 : Mf * Work.Spaces.HkIntegrand α 4 g z θ
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        nlinarith [mul_nonneg hMK hHIg, mul_nonneg hMf hHIg, mul_nonneg hMg hSQnn]
      exact le_trans (by simpa only [Work.Spaces.mixed_zero_right] using hbnd) h1
    · -- `b1 ≥ 3`
      have hb13 : 3 ≤ b1 := by omega
      by_cases hqg : q = Work.Spaces.gam α
      · have ha0' : 0 < a := by
          by_contra h
          have h0 : a = 0 := Nat.le_antisymm (le_of_not_gt h) (Nat.zero_le a)
          have heq : Work.Spaces.gam α = Work.Spaces.eta := hqg ▸ (hq0 h0)
          exact absurd heq (ne_of_gt (eta_lt_gam_of_pos hα))
        exact absurd ⟨rfl, by omega, hqg⟩ hnd
      · have ha0 : a = 0 := by
          by_contra ha
          exact hqg (hq1 (Nat.pos_of_ne_zero ha))
        subst ha0
        have hqeta : q = Work.Spaces.eta := hq0 rfl
        have hmid : (0 : ℕ) + (b + 1 - b1) ≤ 2 := by omega
        have hFsl : SlotWo α q (Work.Spaces.DzIter b1 f) f := by
          rw [hqeta]
          exact slotWo_z (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl
            f b1 (by omega)
        have hYsl : SlotWo α q (Work.Spaces.DzIter b g) g := by
          rw [hqeta]
          exact slotWo_z (α := α) (q := Work.Spaces.eta) Work.Spaces.eta_pos le_rfl
            g b (by omega)
        have hbnd := canonW_mul_abs_le_slotG (α := α) (q := q) (KG := Mg)
          (F := Work.Spaces.DzIter b1 f)
          (Gm := Work.Spaces.DzIter (b + 1 - b1) g)
          (Y := Work.Spaces.DzIter b g)
          hFsl hYsl hMg (fun z θ hz hθ hθ2 => hGsup (b + 1 - b1) 0 hmid z θ hz hθ hθ2)
          z θ hz hθ hθ2
        have h1 : Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
            ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
          have := mul_nonneg (add_nonneg hMf hMK) hHIg
          linarith
        refine le_trans (by
          simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right]
            using hbnd) h1
  · -- `a1 ≥ 1`: the `f`-slot is mixed
    have ha1p1 : 1 ≤ a1 := ha1p
    have ha1pos : 0 < a := by omega
    by_cases hp2 : a1 + b1 ≤ 2
    · -- σ-gain case
      have hbnd := canonW_mul_abs_le_slotSigma (α := α) (q := q) (CK := MK)
        (X := Work.Spaces.mixed b1 a1 f)
        (G := Work.Spaces.mixed (b + 1 - b1) (a - a1) g)
        (Y := Work.Spaces.mixed b a g)
        hα hMK (fun z θ hz hθ hθ2 => hFσ b1 a1 ha1p1 hp2 z θ hz hθ hθ2)
        (q_le_one_add_eta hα1 (Or.inr (hq1 ha1pos)))
        (slotWo_eta_of hα (by omega))
        (slotWo_mixed (α := α) (q := Work.Spaces.gam α) (Work.Spaces.gam_pos hα) le_rfl
          g b a (by omega) (by omega))
        z θ hz hθ hθ2
      have h1 : MK * Work.Spaces.HkIntegrand α 4 g z θ
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        nlinarith [mul_nonneg hMK hHIg, mul_nonneg hMf hHIg, mul_nonneg hMg hSQnn]
      exact le_trans hbnd h1
    · -- `p ≥ 3`: the middle `g`-slot has order `≤ 2`
      have hmid : (a - a1) + (b + 1 - b1) ≤ 2 := by omega
      have hqeq : q = Work.Spaces.gam α := hq1 ha1pos
      have hFsl : SlotWo α q (Work.Spaces.mixed b1 a1 f) f := by
        rw [hqeq]
        exact slotWo_mixed (α := α) (q := Work.Spaces.gam α)
          (Work.Spaces.gam_pos hα) le_rfl f b1 a1 ha1p1 (by omega)
      have hYsl : SlotWo α q (Work.Spaces.mixed b a g) g := by
        rw [hqeq]
        exact slotWo_mixed (α := α) (q := Work.Spaces.gam α)
          (Work.Spaces.gam_pos hα) le_rfl g b a (by omega) (by omega)
      have hbnd := canonW_mul_abs_le_slotG (α := α) (q := q) (KG := Mg)
        (F := Work.Spaces.mixed b1 a1 f)
        (Gm := Work.Spaces.mixed (b + 1 - b1) (a - a1) g)
        (Y := Work.Spaces.mixed b a g)
        hFsl hYsl hMg
        (fun z θ hz hθ hθ2 => hGsup (b + 1 - b1) (a - a1) hmid z θ hz hθ hθ2)
        z θ hz hθ hθ2
      have h1 : Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
            + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        have := mul_nonneg (add_nonneg hMf hMK) hHIg
        linarith
      exact le_trans hbnd h1


/-- A pure `D_z`-slot of order `≤ 4` priced at any `0 ≤ q ≤ η`. -/
theorem slotWo_z_le {α q : ℝ} (hqnn : 0 ≤ q) (hq : q ≤ Work.Spaces.eta)
    (g : ℝ → ℝ → ℝ) (j : ℕ) (hj : j ≤ 4) :
    SlotWo α q (Work.Spaces.DzIter j g) g := by
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    exact slotWo_zero_z g j hj
  · exact slotWo_z (α := α) (q := q) hpos hq g j hj

/-- A mixed slot of order `≤ 4` priced at any `0 ≤ q ≤ γ`. -/
theorem slotWo_mixed_le {α q : ℝ} (hα : 0 < α) (hqnn : 0 ≤ q) (hqγ : q ≤ Work.Spaces.gam α)
    (g : ℝ → ℝ → ℝ) (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    SlotWo α q (Work.Spaces.mixed j i g) g := by
  rcases eq_or_lt_of_le hqnn with h0 | hpos
  · subst h0
    exact slotWo_zero_mixed hα g j i hi hij
  · exact slotWo_mixed (α := α) (q := q) hpos hqγ g j i hi hij

/-- The slot `mixed b' a g` at the exponent `q`, whose `θ`-order is exactly `a`. -/
theorem slotWo_theta_le {α q : ℝ} {g : ℝ → ℝ → ℝ} {a b' : ℕ}
    (hα : 0 < α) (hqnn : 0 ≤ q)
    (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hab : a + b' ≤ 4) :
    SlotWo α q (Work.Spaces.mixed b' a g) g := by
  rcases eq_or_ne a 0 with ha0 | ha0
  · subst ha0
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right] using
      slotWo_z_le (α := α) (q := q) hqnn (hq0 rfl) g b' (by omega)
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    exact slotWo_mixed_le (α := α) (q := q) hα hqnn hqγ g b' a ha1 (by omega)

/-- `q ≤ γ` implies `q ≤ 1 + η`. -/
theorem q_le_one_add_eta' {α q : ℝ} (hα1 : α ≤ 1) (hq : q ≤ Work.Spaces.gam α) :
    q ≤ 1 + Work.Spaces.eta := by
  rw [Work.Spaces.gam] at hq
  have : Work.Spaces.eta = 99 / 100 := rfl
  linarith [Work.Spaces.eta_lt_one]

/-- **The pointwise bound of a non-delicate Leibniz summand, general exponent.** -/
theorem termPair_nd' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {f g : ℝ → ℝ → ℝ} {a b a1 b1 : ℕ} {q Mf MK Mg : ℝ}
    (hMf : 0 ≤ Mf) (hMK : 0 ≤ MK) (hMg : 0 ≤ Mg) (hqnn : 0 ≤ q)
    (hab : a + b ≤ 4) (ha1 : a1 ≤ a) (hb1 : b1 ≤ b) (hp1 : 1 ≤ a1 + b1)
    (hq0 : a = 0 → q ≤ Work.Spaces.eta) (hqγ : q ≤ Work.Spaces.gam α)
    (hqcase : q ≤ Work.Spaces.eta ∨ q = Work.Spaces.gam α)
    (hnd : ¬ (a1 = 0 ∧ b1 = 3 ∧ q = Work.Spaces.gam α))
    (hFsup : ∀ j : ℕ, j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.DzIter j f z θ| ≤ Mf)
    (hFσ : ∀ j i : ℕ, 1 ≤ i → i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i f z θ| ≤ MK * Real.sin (2 * θ))
    (hGsup : ∀ j i : ℕ, i + j ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i g z θ| ≤ Mg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      canonW q z θ * |Work.Spaces.mixed b1 a1 f z θ|
          * |Work.Spaces.mixed (b + 1 - b1) (a - a1) g z θ| * |Work.Spaces.mixed b a g z θ|
        ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
          + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
  intro z θ hz hθ hθ2
  have hHIg : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ := Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hSQnn : 0 ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
      * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases Nat.eq_zero_or_pos a1 with ha1z | ha1p
  · subst ha1z
    simp only [Nat.sub_zero]
    by_cases hb12 : b1 ≤ 2
    · have hbnd := canonW_mul_abs_le_slotW (α := α) (q := q) (KF := Mf)
        (X := Work.Spaces.DzIter b1 f)
        (G := Work.Spaces.mixed (b + 1 - b1) a g)
        (Y := Work.Spaces.mixed b a g)
        (slotWo_theta_le hα hqnn hq0 hqγ (by omega))
        (slotWo_theta_le hα hqnn hq0 hqγ (by omega))
        hMf (fun z θ hz hθ hθ2 => hFsup b1 hb12 z θ hz hθ hθ2) z θ hz hθ hθ2
      have h1 : Mf * Work.Spaces.HkIntegrand α 4 g z θ
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        nlinarith [mul_nonneg hMK hHIg, mul_nonneg hMf hHIg, mul_nonneg hMg hSQnn]
      exact le_trans (by simpa only [Work.Spaces.mixed_zero_right] using hbnd) h1
    · have hb13 : 3 ≤ b1 := by omega
      by_cases hqg : q = Work.Spaces.gam α
      · have ha0' : 0 < a := by
          by_contra h
          have h0 : a = 0 := Nat.le_antisymm (le_of_not_gt h) (Nat.zero_le a)
          exact absurd (hq0 h0) (not_le.mpr (hqg ▸ eta_lt_gam_of_pos hα))
        exact absurd ⟨rfl, by omega, hqg⟩ hnd
      · have hqη : q ≤ Work.Spaces.eta := hqcase.resolve_right hqg
        have hmid : a + (b + 1 - b1) ≤ 2 := by omega
        have hFsl : SlotWo α q (Work.Spaces.DzIter b1 f) f := slotWo_z_le hqnn hqη f b1 (by omega)
        have hYsl : SlotWo α q (Work.Spaces.mixed b a g) g :=
          slotWo_theta_le hα hqnn hq0 hqγ (by omega)
        have hGb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
            |Work.Spaces.mixed (b + 1 - b1) a g z θ| ≤ Mg :=
          fun z θ hz hθ hθ2 => hGsup (b + 1 - b1) a (by omega) z θ hz hθ hθ2
        have hbnd := canonW_mul_abs_le_slotG (α := α) (q := q) (KG := Mg)
          (F := Work.Spaces.DzIter b1 f)
          (Gm := Work.Spaces.mixed (b + 1 - b1) a g)
          (Y := Work.Spaces.mixed b a g)
          hFsl hYsl hMg hGb z θ hz hθ hθ2
        have h1 : Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
            ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
          have := mul_nonneg (add_nonneg hMf hMK) hHIg
          linarith
        exact le_trans hbnd h1
  · have ha1p1 : 1 ≤ a1 := ha1p
    have ha1pos : 0 < a := by omega
    by_cases hp2 : a1 + b1 ≤ 2
    · have hbnd := canonW_mul_abs_le_slotSigma (α := α) (q := q) (CK := MK)
        (X := Work.Spaces.mixed b1 a1 f)
        (G := Work.Spaces.mixed (b + 1 - b1) (a - a1) g)
        (Y := Work.Spaces.mixed b a g)
        hα hMK (fun z θ hz hθ hθ2 => hFσ b1 a1 ha1p1 hp2 z θ hz hθ hθ2)
        (q_le_one_add_eta' hα1 hqγ)
        (slotWo_eta_of hα (by omega))
        (slotWo_mixed_le (α := α) (q := Work.Spaces.gam α) hα
          (le_of_lt (Work.Spaces.gam_pos hα)) le_rfl g b a (by omega) (by omega))
        z θ hz hθ hθ2
      have h1 : MK * Work.Spaces.HkIntegrand α 4 g z θ
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
              + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                  * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        nlinarith [mul_nonneg hMK hHIg, mul_nonneg hMf hHIg, mul_nonneg hMg hSQnn]
      exact le_trans hbnd h1
    · have hmid : (a - a1) + (b + 1 - b1) ≤ 2 := by omega
      have hFsl : SlotWo α q (Work.Spaces.mixed b1 a1 f) f :=
        slotWo_mixed_le (α := α) (q := q) hα hqnn hqγ f b1 a1 ha1p1 (by omega)
      have hYsl : SlotWo α q (Work.Spaces.mixed b a g) g :=
        slotWo_mixed_le (α := α) (q := q) hα hqnn hqγ g b a (by omega) (by omega)
      have hbnd := canonW_mul_abs_le_slotG (α := α) (q := q) (KG := Mg)
        (F := Work.Spaces.mixed b1 a1 f)
        (Gm := Work.Spaces.mixed (b + 1 - b1) (a - a1) g)
        (Y := Work.Spaces.mixed b a g)
        hFsl hYsl hMg
        (fun z θ hz hθ hθ2 => hGsup (b + 1 - b1) (a - a1) hmid z θ hz hθ hθ2)
        z θ hz hθ hθ2
      have h1 : Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
          ≤ (Mf + MK) * Work.Spaces.HkIntegrand α 4 g z θ
            + Mg * (Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
                * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) := by
        have := mul_nonneg (add_nonneg hMf hMK) hHIg
        linarith
      exact le_trans hbnd h1

end Work.FTS.TransportS.T2Sup
