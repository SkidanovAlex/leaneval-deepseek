/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H6Pair6Aux/ip6_dz_self` — the `D_z`-self-pairing bound for the level-six pairing

The target: for small `α` and every honest profile `f` with order-seven honesty,

  `|IP6 1 … 1 α (D_z f) f| ≤ C |f|_{ℋ⁶}²`.

Route (see `H6Pair6Aux/Ip6DzAux.lean` for the auxiliary lemmas):

* `TransportS.ip4_unfold_bound` bounds the five-fold unfolding of the coercive recursion by
  `3^5·10^22` times the *slot sum* `SlotSum α 6 (D_z f) f`;
* each slot term is an elementary pairing `∫_z∫_θ ρ·D_z^bD_θ^a(D_z f)·D_z^bD_θ^a f`, which the
  first-argument shift `slotPairing_dz_left` turns into `∫_z∫_θ (w)²θ_w·(D_zV)·V` with
  `V = D_z^bD_θ^a f`;
* for the top slots `a + b = 6` (where `D_zV` has order seven) the radial integration by parts
  `dzSelf2d`/`dzSelf1d` bounds it by `2∫_z∫_θ (w)²θ_w V²`, and for `a + b ≤ 5` the AM–GM
  inequality `slotAMGM` does the same job;
* `∫_z∫_θ (w)²θ_w V² ≤ HkSq α 6 f` by `intSlotLeHkSq` (the slot weights are summands of
  `HkIntegrand α 6 f`), and the product-measure integrability needed by the IBP is `slotProd`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.Ip6DzAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf1d
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.dzSelf2d
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotProd
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

open Work.FTS.Galerkin (Fn)


/-- The per-slot estimate: each three-term group of the slot sum at level six is bounded by
`4 |f|_{ℋ⁶}²`. -/
theorem slotTerm_le (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h6 : Work.Spaces.HkMem α 6 f)
    (h7 : Work.Spaces.HkMem α 7 f) {a b : ℕ} (hab : a + b ≤ 6) {q : ℝ}
    (hcap : ∀ θ ∈ Set.Ioo 0 (π / 2), (Real.sin (2 * θ)) ^ (-q)
      ≤ (Real.sin (2 * θ)) ^ (-(if a = 0 then Work.Spaces.eta else Work.Spaces.gam α))) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-q)
        * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)|
      ≤ 4 * Work.Spaces.HkSq α 6 f := by
  have hθw_nn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ (Real.sin (2 * θ)) ^ (-q) :=
    fun θ hθ => Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) _
  have hθw_pos : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 < (Real.sin (2 * θ)) ^ (-q) :=
    fun θ hθ => Real.rpow_pos_of_pos (sin_two_pos hθ) _
  have hHkn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hXc : ContinuousOn (Function.uncurry (Work.Spaces.mixed (b + 1) a f))
      Work.FTS.EllipticEst.Q0 := (hsm.mixed (b + 1) a).continuousOn
  have hYc : ContinuousOn (Function.uncurry (Work.Spaces.mixed b a f))
      Work.FTS.EllipticEst.Q0 := (hsm.mixed b a).continuousOn
  have hYs : ∀ θ ∈ Set.Ioo 0 (π / 2),
      ContDiffOn ℝ 1 (fun z => Work.Spaces.mixed b a f z θ) (Set.Ioi 0) :=
    fun θ hθ => SmoothOpen.slice (hsm.mixed b a) hθ 1
  by_cases ha0 : a = 0
  · subst ha0
    simp only [Work.Spaces.mixed_zero_right] at *
    have hcap' : ∀ θ ∈ Set.Ioo 0 (π / 2),
        (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      intro θ hθ
      simpa using hcap θ hθ
    by_cases htop : b = 6
    · subst htop
      have hF : MeasureTheory.Integrable
          (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * (Work.Spaces.DzIter 6 f p.1 p.2) ^ 2
            * (Real.sin (2 * p.2)) ^ (-q))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        have hbig := (slotProd α 6 hsm h6).1 6 le_rfl
        have hc := integrable_prod_of_cap (X := fun z θ => Work.Spaces.DzIter 6 f z θ)
          (by simpa using (hsm.mixed 6 0).continuousOn) (q := q) (q' := Work.Spaces.eta)
          hcap' hbig
        exact hc.congr (Filter.Eventually.of_forall fun p => by ring)
      have hD : MeasureTheory.Integrable
          (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
            * (Work.Spaces.DzIter (6 + 1) f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-q))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        have hbig := (slotProd α 7 hsm h7).1 7 le_rfl
        have hc := integrable_prod_of_cap (X := fun z θ => Work.Spaces.DzIter 7 f z θ)
          (by simpa using (hsm.mixed 7 0).continuousOn) (q := q) (q' := Work.Spaces.eta)
          hcap' hbig
        exact hc.congr (Filter.Eventually.of_forall fun p => by ring)
      have hibp := dzSelf2d (θw := fun θ => (Real.sin (2 * θ)) ^ (-q))
        (V := fun z θ => Work.Spaces.DzIter 6 f z θ)
        (fun Y hY hF' hD' => dzSelf1d hY hF' hD') hθw_nn hθw_pos
        (fun θ hθ => SmoothOpen.slice (hsm.mixed 6 0) hθ 1) hF hD
      have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.DzIter 6 f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f :=
        (intSlotLeHkSq α h6).1 6 le_rfl (fun θ => (Real.sin (2 * θ)) ^ (-q)) hθw_nn hcap'
      have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.DzIter (6 + 1) f z θ * Work.Spaces.DzIter 6 f z θ))
          = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-q)
            * ((z * Work.Spaces.pz (fun z θ => Work.Spaces.DzIter 6 f z θ) z θ)
              * (fun z θ => Work.Spaces.DzIter 6 f z θ) z θ) := rfl
      rw [hgoal]
      linarith [hibp, hval, hHkn]
    · have hb6 : b ≤ 6 := by omega
      have hb1 : b + 1 ≤ 6 := by omega
      have hAesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ =>
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.DzIter (b + 1) f z θ * Work.Spaces.DzIter b f z θ)))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _
          ((continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 q)).mul
            (((hsm.mixed (b + 1) 0).continuousOn).mul ((hsm.mixed b 0).continuousOn)))
      have hamgm := slotAMGM (α := α) (f := f) (q := q) h6 hθw_nn
        (fun z θ hθ => by
          refine le_trans ?_ (sq_le_HkIntegrand_pure6 α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ (b + 1) hb1)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcap' θ ⟨hθ.1, hθ.2⟩) (sq_nonneg _)) (sq_nonneg _))
        (fun z θ hθ => by
          refine le_trans ?_ (sq_le_HkIntegrand_pure6 α ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ b hb6)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcap' θ ⟨hθ.1, hθ.2⟩) (sq_nonneg _)) (sq_nonneg _))
        hAesm
      linarith [hamgm]
  · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
    have hcap' : ∀ θ ∈ Set.Ioo 0 (π / 2),
        (Real.sin (2 * θ)) ^ (-q) ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      intro θ hθ
      simpa [ha0] using hcap θ hθ
    by_cases htop : a + b = 6
    · have hF : MeasureTheory.Integrable
          (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
            * (Work.Spaces.mixed b a f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-q))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        have hbig := (slotProd α 6 hsm h6).2 b a ha1 hab
        have hc := integrable_prod_of_cap (X := fun z θ => Work.Spaces.mixed b a f z θ) hYc
          (q := q) (q' := Work.Spaces.gam α) hcap' hbig
        exact hc.congr (Filter.Eventually.of_forall fun p => by ring)
      have hD : MeasureTheory.Integrable
          (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2
            * (Work.Spaces.mixed (b + 1) a f p.1 p.2) ^ 2 * (Real.sin (2 * p.2)) ^ (-q))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        have hbig := (slotProd α 7 hsm h7).2 (b + 1) a ha1 (by omega)
        have hc := integrable_prod_of_cap (X := fun z θ => Work.Spaces.mixed (b + 1) a f z θ)
          hXc (q := q) (q' := Work.Spaces.gam α) hcap' hbig
        exact hc.congr (Filter.Eventually.of_forall fun p => by ring)
      have hibp := dzSelf2d (θw := fun θ => (Real.sin (2 * θ)) ^ (-q))
        (V := fun z θ => Work.Spaces.mixed b a f z θ)
        (fun Y hY hF' hD' => dzSelf1d hY hF' hD') hθw_nn hθw_pos hYs hF hD
      have hval : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f :=
        (intSlotLeHkSq α h6).2 b a ha1 hab (fun θ => (Real.sin (2 * θ)) ^ (-q)) hθw_nn hcap'
      have hgoal : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ))
          = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-q)
            * ((z * Work.Spaces.pz (fun z θ => Work.Spaces.mixed b a f z θ) z θ)
              * (fun z θ => Work.Spaces.mixed b a f z θ) z θ) := rfl
      rw [hgoal]
      linarith [hibp, hval, hHkn]
    · have hAesm : MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun z θ =>
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-q)
            * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.mixed b a f z θ)))
          ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        Work.Spaces.aesm_of_continuousOn_Qd _
          ((continuousOn_w_sq_Q0.mul (continuousOn_sin_rpow_Q0 q)).mul (hXc.mul hYc))
      have hamgm := slotAMGM (α := α) (f := f) (q := q) h6 hθw_nn
        (fun z θ hθ => by
          refine le_trans ?_ (sq_le_HkIntegrand_mixed6 α hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ (b + 1) a ha1 (by omega))
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcap' θ ⟨hθ.1, hθ.2⟩) (sq_nonneg _)) (sq_nonneg _))
        (fun z θ hθ => by
          refine le_trans ?_ (sq_le_HkIntegrand_mixed6 α hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩ b a ha1 hab)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcap' θ ⟨hθ.1, hθ.2⟩) (sq_nonneg _)) (sq_nonneg _))
        hAesm
      linarith [hamgm]

/-- The three-term group of the slot sum at level six is bounded by `12 |f|_{ℋ⁶}²`. -/
theorem slotGroup_le (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (h6 : Work.Spaces.HkMem α 6 f)
    (h7 : Work.Spaces.HkMem α 7 f) {a b : ℕ} (hab : a + b ≤ 6) :
    |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b
        (Work.Spaces.Dz f) f|
      + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b
        (Work.Spaces.Dz f) f|
      + (if 1 ≤ a then |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b
          (Work.Spaces.Dz f) f| else 0)
      ≤ 12 * Work.Spaces.HkSq α 6 f := by
  have hE : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b
      (Work.Spaces.Dz f) f| ≤ 4 * Work.Spaces.HkSq α 6 f := by
    rw [slotPairing_dz_left (u := f) Work.FTS.TransportS.leafEta a b hsm f]
    have h := slotTerm_le α hα hsm h6 h7 hab (q := Work.Spaces.eta) (by
      intro θ hθ
      by_cases ha : a = 0
      · rw [if_pos ha]
      · rw [if_neg ha]
        exact sin_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    simpa only [leafEta_eq, mul_assoc] using h
  have hO : |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b
      (Work.Spaces.Dz f) f| ≤ 4 * Work.Spaces.HkSq α 6 f := by
    rw [slotPairing_dz_left (u := f) Work.FTS.TransportS.leafOne a b hsm f]
    have h := slotTerm_le α hα hsm h6 h7 hab (q := 0) (by
      intro θ hθ
      by_cases ha : a = 0
      · rw [if_pos ha]
        simpa only [neg_zero, Real.rpow_zero] using one_le_sin_eta hθ
      · rw [if_neg ha]
        simpa only [neg_zero, Real.rpow_zero] using one_le_sin_gam hα hθ)
    simpa only [leafOne_eq, neg_zero, Real.rpow_zero, one_mul, mul_assoc] using h
  have hG : 1 ≤ a → |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α) a b
      (Work.Spaces.Dz f) f| ≤ 4 * Work.Spaces.HkSq α 6 f := by
    intro ha1
    have ha0 : ¬ a = 0 := by omega
    rw [slotPairing_dz_left (u := f) (Work.FTS.TransportS.leafGam α) a b hsm f]
    have h := slotTerm_le α hα hsm h6 h7 hab (q := Work.Spaces.gam α) (by
      intro θ hθ
      rw [if_neg ha0])
    simpa only [leafGam_eq, mul_assoc] using h
  have hHkn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  by_cases ha : 1 ≤ a
  · rw [if_pos ha]
    have hG' := hG ha
    linarith
  · rw [if_neg ha]
    linarith

/-- **The target.** -/
theorem ip6_dz_self : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.VocabO.HQo α 6 f → Work.Spaces.HkMem α 7 f →
      |Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α (Work.Spaces.Dz f) f|
        ≤ C * Work.Spaces.HkSq α 6 f := by
  refine ⟨(3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * 336, 1, by norm_num, by norm_num, ?_⟩
  intro α hα f hf h7
  have hα0 : 0 < α := hα.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hf.1
  have h6 : Work.Spaces.HkMem α 6 f := hf.2
  have hIPn : Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
      = Work.FTS.TransportS.IPn α 5 := rfl
  rw [hIPn]
  have hunf := Work.FTS.TransportS.ip4_unfold_bound 5 α (Work.Spaces.Dz f) f hsm.Dz hsm
  have hslot : Work.FTS.TransportS.SlotSum α 6 (Work.Spaces.Dz f) f
      ≤ 28 * (12 * Work.Spaces.HkSq α 6 f) := by
    rw [Work.FTS.TransportS.SlotSum]
    have hcard : (∑ a ∈ Finset.range (6 + 1),
        ∑ _b ∈ Finset.range (6 + 1 - a), (1 : ℝ)) = 28 := slotSum_six_card
    calc (∑ a ∈ Finset.range (6 + 1), ∑ b ∈ Finset.range (6 + 1 - a),
          (|Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafEta a b
              (Work.Spaces.Dz f) f|
            + |Work.FTS.TransportS.slotPairing Work.FTS.TransportS.leafOne a b
              (Work.Spaces.Dz f) f|
            + (if 1 ≤ a then |Work.FTS.TransportS.slotPairing (Work.FTS.TransportS.leafGam α)
                a b (Work.Spaces.Dz f) f| else 0)))
        ≤ ∑ a ∈ Finset.range (6 + 1), ∑ _b ∈ Finset.range (6 + 1 - a),
            (12 * Work.Spaces.HkSq α 6 f) := by
          refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => ?_
          have ha' : a < 6 + 1 := Finset.mem_range.mp ha
          have hb' : b < 6 + 1 - a := Finset.mem_range.mp hb
          exact slotGroup_le α hα0 hsm h6 h7 (by omega)
      _ = 28 * (12 * Work.Spaces.HkSq α 6 f) := by
          calc (∑ a ∈ Finset.range (6 + 1), ∑ _b ∈ Finset.range (6 + 1 - a),
                (12 * Work.Spaces.HkSq α 6 f))
              = (∑ a ∈ Finset.range (6 + 1),
                  (∑ _b ∈ Finset.range (6 + 1 - a), (1 : ℝ))
                    * (12 * Work.Spaces.HkSq α 6 f)) := by
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Finset.sum_mul]
                simp
            _ = (∑ a ∈ Finset.range (6 + 1), ∑ _b ∈ Finset.range (6 + 1 - a), (1 : ℝ))
                  * (12 * Work.Spaces.HkSq α 6 f) := by rw [Finset.sum_mul]
            _ = 28 * (12 * Work.Spaces.HkSq α 6 f) := by rw [hcard]
  calc |Work.FTS.TransportS.IPn α 5 (Work.Spaces.Dz f) f|
      ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22
          * Work.FTS.TransportS.SlotSum α 6 (Work.Spaces.Dz f) f := hunf
    _ ≤ (3 : ℝ) ^ 5 * (10 : ℝ) ^ 22
          * (28 * (12 * Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left hslot (by positivity)
    _ = ((3 : ℝ) ^ 5 * (10 : ℝ) ^ 22 * 336) * Work.Spaces.HkSq α 6 f := by ring


end Work.FTS.StrongPersist.H6Pair6Aux
