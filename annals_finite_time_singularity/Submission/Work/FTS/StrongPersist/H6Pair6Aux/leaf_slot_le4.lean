import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.intSlotLeHkSq
import Submission.Work.FTS.TransportS.Slots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-!
# The level-four leaf slot bound

This is the level-four counterpart of `leaf_slot_le6`.  For every slot `(a,b)` with
`a + b ≤ 4` and every leaf weight `ρ` of `IP4` (`IsLeafW α a ρ`), the single weighted `L²`
slot integral `∫_z ∫_θ ρ · (D_z^b D_θ^a f)²` is bounded by the full `ℋ⁴`-energy `HkSq α 4 f`.

The proof is the same as the one at level six, only with `intSlotLeHkSq4` (the level-four
instance of the "general `θ`-weight" slot estimate, built here from
`Work.Spaces.sq_le_HkIntegrand_z/mixed` and `Work.Spaces.L2Sq_*_le_HkSq`) in place of the
level-six `intSlotLeHkSq`.
-/

/-- The open interval `Ioo 0 (π/2)` is conull in `Iθ = [0,π/2]`: it differs from `Iθ`
only by the two endpoints, which form a null set. -/
private lemma ae_mem_Ioo_Iθ4 :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (π / 2) := by
  show ∀ᵐ θ ∂(volume.restrict (Set.Icc 0 (π / 2))), θ ∈ Set.Ioo 0 (π / 2)
  rw [← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2))]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hθ)

/-- The square of the mixed weight `Wt α z θ = w z · sin(2θ)^{-γ/2}` is
`w z² · sin(2θ)^{-γ}`. -/
private lemma Wt_sq_eq4 (α z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow]
  rw [show ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ ((2 : ℝ)) from
      (Real.rpow_natCast ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) 2).symm]
  rw [← Real.rpow_mul hs]
  rw [show (-(Work.Spaces.gam α / 2)) * (2 : ℝ) = -(Work.Spaces.gam α) by ring]

/-- The pointwise comparison for a pure `D_z`-slot: if `θw θ ≤ sin(2θ)^{-η}` then the
weighted square `w² θw (D_z^i f)²` is dominated by the `i`-th slot of `HkIntegrand α 4`. -/
private lemma zSlot_pointwise4 (α : ℝ) (f : ℝ → ℝ → ℝ) (i : ℕ) (hi : i ≤ 4)
    (θw : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hle : θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) :
    (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hmain : (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
      ≤ (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Work.Spaces.sq_mul_div_rpow _ _ _ _ (le_of_lt hs) (by norm_num [Work.Spaces.eta])]
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (θw θ * (Work.Spaces.DzIter i f z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              * (Work.Spaces.DzIter i f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.DzIter i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
  exact hmain.trans (Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ i hi)

/-- The pointwise comparison for a mixed slot: if `θw θ ≤ sin(2θ)^{-γ}` then the
weighted square `w² θw (D_z^j D_θ^i f)²` is dominated by the `(i,j)`-slot of
`HkIntegrand α 4`. -/
private lemma mSlot_pointwise4 (α : ℝ) (f : ℝ → ℝ → ℝ) (i j : ℕ) (hi : 1 ≤ i)
    (hij : i + j ≤ 4) (θw : ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hle : θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :
    (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 f z θ := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hmain : (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
      ≤ (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
        = (Work.Spaces.w z) ^ 2
            * (θw θ * (Work.Spaces.mixed j i f z θ) ^ 2) := by ring
      _ ≤ (Work.Spaces.w z) ^ 2
            * ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
              * (Work.Spaces.mixed j i f z θ) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hle (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [mul_pow, Wt_sq_eq4 α z θ hs]
          ring
  exact hmain.trans (Work.Spaces.sq_le_HkIntegrand_mixed α 4 f z θ i j hi hij)

/-- **The level-four "general `θ`-weight" slot estimate.**  For `f ∈ ℋ⁴` and every angular
weight `θw` which is nonnegative on the open quadrant and pointwise dominated there by
`sin(2θ)^{-η}` (the pure `D_z`-slots) resp. by `sin(2θ)^{-γ}` (the slots with an angular
derivative), the weighted slot integral is bounded by `HkSq α 4 f`. -/
private theorem intSlotLeHkSq4 (α : ℝ) {f : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 4 f) :
    (∀ i : ℕ, i ≤ 4 → ∀ θw : ℝ → ℝ,
      (∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f) ∧
    (∀ j i : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ θw : ℝ → ℝ,
      (∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ θw θ) →
      (∀ θ ∈ Set.Ioo 0 (π / 2), θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ Work.Spaces.HkSq α 4 f) := by
  have hIoo := ae_mem_Ioo_Iθ4
  constructor
  · intro i hi θw hnn hle
    have hnn' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ θw θ :=
      hIoo.mono fun θ hθ => hnn θ hθ
    have hle' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      hIoo.mono fun θ hθ => hle θ hθ
    have hinner_nn : ∀ z, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2) :=
      fun z => hnn'.mono fun θ h1 =>
        mul_nonneg (mul_nonneg (sq_nonneg _) h1) (sq_nonneg _)
    have hinner_le : ∀ z, (fun θ =>
          (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter i f z θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Work.Spaces.HkIntegrand α 4 f z θ) :=
      fun z => (hIoo.and hle').mono fun θ hθ => zSlot_pointwise4 α f i hi θw z θ hθ.1 hθ.2
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae (hinner_nn z)) h.2 ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      MeasureTheory.integral_mono_of_nonneg (hinner_nn z) (h.1 z hz) (hinner_le z)
  · intro j i hi hij θw hnn hle
    have hnn' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ θw θ :=
      hIoo.mono fun θ hθ => hnn θ hθ
    have hle' : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
      hIoo.mono fun θ hθ => hle θ hθ
    have hinner_nn : ∀ z, 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ => (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2) :=
      fun z => hnn'.mono fun θ h1 =>
        mul_nonneg (mul_nonneg (sq_nonneg _) h1) (sq_nonneg _)
    have hinner_le : ∀ z, (fun θ =>
          (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2)
        ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ => Work.Spaces.HkIntegrand α 4 f z θ) :=
      fun z => (hIoo.and hle').mono fun θ hθ =>
        mSlot_pointwise4 α f i j hi hij θw z θ hθ.1 hθ.2
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae (hinner_nn z)) h.2 ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz =>
      MeasureTheory.integral_mono_of_nonneg (hinner_nn z) (h.1 z hz) (hinner_le z)

/-- **The leaf weights of `IP4` are dominated by the slot weight of `HkIntegrand α 4`.**

For every slot `(a,b)` of the level-four pairing (`a + b ≤ 4`) and every leaf weight
`IsLeafW α a ρ` (i.e. `ρ = w²σ^{-η}`, `ρ = w²`, or `ρ = w²σ^{-γ}` with `a ≥ 1`), the
single weighted `L²` slot integral `∫_z ∫_θ ρ·(D_z^bD_θ^a f)²` is bounded by `HkSq α 4 f`. -/
theorem leaf_slot_le4 {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hmem : Work.Spaces.HkMem α 4 f) :
    ∀ (a b : ℕ) (ρ : ℝ → ℝ → ℝ), a + b ≤ 4 → Work.FTS.TransportS.IsLeafW α a ρ →
      (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2) ≤ Work.Spaces.HkSq α 4 f := by
  intro a b ρ hab hleaf
  have h6 := intSlotLeHkSq4 α hmem
  have hsin_nn : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hgam_nn : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have heta_nn : 0 ≤ Work.Spaces.eta := Work.Spaces.eta_nonneg
  rcases hleaf with hρ | hρ | ⟨ha1, hρ⟩
  · -- the `η`-leaf weight `w²σ^{-η}`
    subst hρ
    by_cases ha : 1 ≤ a
    · -- a slot with an angular derivative: compare `σ^{-η} ≤ σ^{-γ}`
      have h := h6.2 b a ha hab (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
        (fun θ hθ => Work.FTS.H2.rpow_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafEta] using h
    · -- a `D_z`-only slot: `w²σ^{-η}` is exactly its slot weight
      have ha0 : a = 0 := by omega
      subst a
      have hb : b ≤ 4 := by omega
      have h := h6.1 b hb (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
        (fun θ hθ => le_rfl)
      simpa only [Work.FTS.TransportS.leafEta, Work.Spaces.mixed_zero_right] using h
  · -- the σ-free leaf weight `w²`
    subst hρ
    by_cases ha : 1 ≤ a
    · -- a slot with an angular derivative: `1 ≤ σ^{-γ}`
      have h := h6.2 b a ha hab (fun _ : ℝ => 1) (fun θ hθ => zero_le_one)
        (fun θ hθ => Work.FTS.TransportS.one_le_rpow_neg hgam_nn ⟨hθ.1, hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafOne, mul_one] using h
    · -- a `D_z`-only slot: `1 ≤ σ^{-η}`
      have ha0 : a = 0 := by omega
      subst a
      have hb : b ≤ 4 := by omega
      have h := h6.1 b hb (fun _ : ℝ => 1) (fun θ hθ => zero_le_one)
        (fun θ hθ => Work.FTS.TransportS.one_le_rpow_neg heta_nn ⟨hθ.1, hθ.2⟩)
      simpa only [Work.FTS.TransportS.leafOne, mul_one, Work.Spaces.mixed_zero_right] using h
  · -- the `γ`-leaf weight `w²σ^{-γ}`, which occurs only at slots with `a ≥ 1`
    subst hρ
    have h := h6.2 b a ha1 hab (fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (fun θ hθ => Real.rpow_nonneg (hsin_nn θ hθ) _)
      (fun θ hθ => le_rfl)
    simpa only [Work.FTS.TransportS.leafGam] using h

end Work.FTS.StrongPersist.H6Pair6Aux
