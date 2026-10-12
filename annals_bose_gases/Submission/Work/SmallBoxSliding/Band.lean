import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.SmallBoxSliding.Sliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `I₋ ↔ G` band cost (the `μ ↦ 4μ` region, FS `eq:badset`)

FS restricts the sliding sum to the interior `I₋ = {∀j, |((ℓd)•u)_j| ≤ A − 2μ^{-1/3}}`
(where the chemical potential `μ` is used as it stands, `m(u) = 1`).  On the
remaining band `G ∖ I₋` — where the smallest side of `B(u)` lies between
`μ^{-1/3}` and `2μ^{-1/3}`, so that the chemical-potential lemma is needed —
each box costs at most `Q = Cμa`, and there are at most `vol(bandSet)` of them.
`interior_band_loss` records exactly this: restricting `∫_G` to `∫_{I₋}` costs
`Q·V` when the band volume is at most `V` (`V := 12(1+d)²d^{-3}` in the regime
`μ^{-1/3} ≤ ℓ`, cf. `Sliding.bandSet_measure_le_d3`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-- The band `G ∖ I₋` is contained in `bandSet`, so
`vol(G ∖ I₋) ≤ vol(bandSet)`; in particular the band has finite volume as
soon as `vol(bandSet) ≤ ofReal V`. -/
lemma band_finite_of_volume_le {ℓ d μ V : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hV : 0 ≤ V)
    (hvol : volume (bandSet ℓ d μ) ≤ ENNReal.ofReal V) :
    volume (goodSet ℓ d μ \ interiorSet ℓ d μ) ≠ (⊤ : ℝ≥0∞) := by
  have hsub := diff_goodSet_interiorSet_subset_bandSet (ℓ := ℓ) (d := d) hμ
  have hmono : volume (goodSet ℓ d μ \ interiorSet ℓ d μ) ≤ volume (bandSet ℓ d μ) :=
    measure_mono hsub
  exact ne_of_lt (lt_of_le_of_lt (le_trans hmono hvol) ENNReal.ofReal_lt_top)

/-- **The `I₋`-restriction cost**: if `f` is at least `−Q` on the band `G ∖ I₋`
and the band volume is at most `V`, then restricting the sliding sum from the
good set `G` to the interior `I₋` costs at most `Q·V`:

    ∫_{I₋} f − Q·V ≤ ∫_G f .

FS uses this on `f = eBf` with `Q = Cμa` (the per-box constant error) and
`V = 12(1+d)²d^{-3}` (`Sliding.bandSet_measure_le_d3`). -/
theorem interior_band_loss {ℓ d μ Q V : ℝ} {f : ℝ³ → ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (hvol : volume (bandSet ℓ d μ) ≤ ENNReal.ofReal V)
    (hint : IntegrableOn f (goodSet ℓ d μ))
    (hlow : ∀ u ∈ goodSet ℓ d μ \ interiorSet ℓ d μ, - Q ≤ f u) :
    (∫ u in interiorSet ℓ d μ, f u) - Q * V ≤ ∫ u in goodSet ℓ d μ, f u := by
  have hsub : interiorSet ℓ d μ ⊆ goodSet ℓ d μ := interiorSet_subset_goodSet hμ
  have hImeas : MeasurableSet (interiorSet ℓ d μ) := measurableSet_interiorSet ℓ d μ
  have hDmeas : MeasurableSet (goodSet ℓ d μ \ interiorSet ℓ d μ) :=
    (measurableSet_goodSet ℓ d μ).diff hImeas
  have hsplit : (∫ u in goodSet ℓ d μ, f u)
      = (∫ u in interiorSet ℓ d μ, f u) + (∫ u in goodSet ℓ d μ \ interiorSet ℓ d μ, f u) := by
    have hunion : interiorSet ℓ d μ ∪ (goodSet ℓ d μ \ interiorSet ℓ d μ) = goodSet ℓ d μ := by
      ext u
      constructor
      · rintro (h | h)
        · exact hsub h
        · exact h.1
      · intro h
        by_cases hi : u ∈ interiorSet ℓ d μ
        · exact Or.inl hi
        · exact Or.inr ⟨h, hi⟩
    conv_lhs => rw [← hunion]
    exact MeasureTheory.setIntegral_union (by rw [Set.disjoint_left]; intro x hx hd; exact hd.2 hx) hDmeas
      (hint.mono_set hsub) (hint.mono_set Set.diff_subset)
  -- the band part is ≥ −Q·V
  have hfinB : volume (bandSet ℓ d μ) ≠ (⊤ : ℝ≥0∞) := ne_of_lt (lt_of_le_of_lt hvol ENNReal.ofReal_lt_top)
  have hfin : volume (goodSet ℓ d μ \ interiorSet ℓ d μ) ≠ (⊤ : ℝ≥0∞) :=
    band_finite_of_volume_le hℓ hd hμ hV hvol
  have hsubB := diff_goodSet_interiorSet_subset_bandSet (ℓ := ℓ) (d := d) hμ
  have hvolle : (volume (goodSet ℓ d μ \ interiorSet ℓ d μ)).toReal ≤ V := by
    have h1 : volume (goodSet ℓ d μ \ interiorSet ℓ d μ) ≤ ENNReal.ofReal V :=
      le_trans (measure_mono hsubB) hvol
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    simpa [ENNReal.toReal_ofReal hV] using this
  have hintf : IntegrableOn f (goodSet ℓ d μ \ interiorSet ℓ d μ) := hint.mono_set Set.diff_subset
  have hintc : IntegrableOn (fun _ : ℝ³ => -Q) (goodSet ℓ d μ \ interiorSet ℓ d μ) :=
    MeasureTheory.integrableOn_const hfin
  have hmono : (∫ u in goodSet ℓ d μ \ interiorSet ℓ d μ, (-Q : ℝ))
      ≤ ∫ u in goodSet ℓ d μ \ interiorSet ℓ d μ, f u := by
    refine MeasureTheory.setIntegral_mono_on hintc hintf hDmeas ?_
    intro u hu
    exact hlow u hu
  have hconst : (∫ u in goodSet ℓ d μ \ interiorSet ℓ d μ, (-Q : ℝ))
      = -Q * (volume (goodSet ℓ d μ \ interiorSet ℓ d μ)).toReal := by
    rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def]
    ring
  have hQV : -Q * V ≤ -Q * (volume (goodSet ℓ d μ \ interiorSet ℓ d μ)).toReal := by
    have hvolnn : 0 ≤ (volume (goodSet ℓ d μ \ interiorSet ℓ d μ)).toReal := ENNReal.toReal_nonneg
    nlinarith [hvolle, hQ]
  linarith [hsplit, hmono, hconst, hQV]



/-! ## Item 1 with the interior restriction — both FS error terms -/

/-- **The sliding-sum identity on the interior `I₋`**: item 1 combined with
`interior_band_loss`, i.e. FS `eq:appsliding` restricted to the boxes where
`m(u) = 1`.  Both FS `eq:badset` error terms appear:

    (b/2ℓ²)·cnPlus + ∫_{I₋} eBf − C·B − Q·V ≤ E_ℓ(Φ)

with `C·B` the discarded `χ_{B(u)}²`-mass (`compl_mass_le` + the closed
bad-band law, giving `Cμ²a(μa³)^{M/3}ℓ³`-type) and `Q·V` the `μ ↦ 4μ` band
cost (`Q = Cμa` per box, `V = 12(1+d)²d^{-3}` the box count in the regime
`μ^{-1/3} ≤ ℓ`). -/
theorem sliding_sum_identity_interior {N : ℕ} {ℓ d μ b C B Q V : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} {Φ : X N → ℝ} (eBf : ℝ³ → ℝ)
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hV : 0 ≤ V)
    (hintf : Integrable eBf)
    (hintmass : Integrable (fun u : ℝ³ => chiMass M ℓ d u))
    (hvol : volume (bandSet ℓ d μ) ≤ ENNReal.ofReal V)
    (hslide : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u : ℝ³, eBf u)
        ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hlow : ∀ u : ℝ³, - C * chiMass M ℓ d u ≤ eBf u)
    (hmass : (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) ≤ B)
    (hband : ∀ u ∈ goodSet ℓ d μ \ interiorSet ℓ d μ, - Q ≤ eBf u) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u in interiorSet ℓ d μ, eBf u) - C * B - Q * V
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hmain := sliding_sum_identity (h := h) (M := M) eBf hC hintf hintmass hslide hlow hmass
  have hband' := interior_band_loss (ℓ := ℓ) (d := d) (μ := μ) (Q := Q) (V := V)
    hℓ hd hμ hQ hV hvol (hintf.integrableOn) hband
  linarith


/-! ## The ENNReal-level band volume bound (for `interior_band_loss`'s `hvol`) -/

/-- The band volume bound in the `ENNReal.ofReal` form consumed by
`interior_band_loss`, in the `d^{-3}` shape of FS's `Cμad^{-3}` error term:
in the regime `μ^{-1/3} ≤ ℓ`, `vol(bandSet) ≤ ofReal (12(1+d)²d^{-3})`. -/
theorem bandSet_volume_le_d3 {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hreg : μ ^ (-1 / 3 : ℝ) ≤ ℓ)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    volume (bandSet ℓ d μ) ≤ ENNReal.ofReal (12 * (1 + d) ^ 2 * (d ^ 3)⁻¹) := by
  have h1 := chiSmallBadBand_measure_le (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hμ hAδ
  rw [← bandSet_eq_chiSmallBadBand] at h1
  have hshell := chiSmallB_badband_shell_bound (ℓ := ℓ) (d := d) (μ := μ) hℓ hd hμ hAδ
  have hμp : 0 < μ ^ (-1 / 3 : ℝ) := Real.rpow_pos_of_pos hμ _
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hinv0 : 0 ≤ ((ℓ * d) ^ 3)⁻¹ := by positivity
  have hkey : ((ℓ * d) ^ 3)⁻¹ * ((2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
        (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3)
      ≤ 12 * (1 + d) ^ 2 * (d ^ 3)⁻¹ := by
    have h2 : ((ℓ * d) ^ 3)⁻¹ * ((2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
          (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3)
        ≤ ((ℓ * d) ^ 3)⁻¹ * (12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2) :=
      mul_le_mul_of_nonneg_left hshell hinv0
    have h3 : ((ℓ * d) ^ 3)⁻¹ * (12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2)
        ≤ 12 * (1 + d) ^ 2 * (d ^ 3)⁻¹ := by
      have hident : ((ℓ * d) ^ 3)⁻¹ * (12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2)
          = (μ ^ (-1 / 3 : ℝ) / ℓ) * (12 * (1 + d) ^ 2 * (d ^ 3)⁻¹) := by
        field_simp
      rw [hident]
      have hratio : μ ^ (-1 / 3 : ℝ) / ℓ ≤ 1 := by
        rw [div_le_one hℓ]
        exact hreg
      have hA : 0 ≤ 12 * (1 + d) ^ 2 * (d ^ 3)⁻¹ := by positivity
      nlinarith [hratio, hA]
    linarith [h2, h3]
  calc volume (bandSet ℓ d μ)
      ≤ ENNReal.ofReal (((ℓ * d) ^ 3)⁻¹ * ((2 * ((1 / 2) * ℓ * (1 + d))) ^ 3 -
          (2 * (((1 / 2) * ℓ * (1 + d)) - 2 * μ ^ (-1 / 3 : ℝ))) ^ 3)) := h1
    _ ≤ ENNReal.ofReal (12 * (1 + d) ^ 2 * (d ^ 3)⁻¹) := ENNReal.ofReal_le_ofReal hkey

/-- **Item 1 in the exact FS `eq:appsliding`/`eq:badset` shape**: on the
interior `I₋ = {u : ‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − 2μ^{-1/3}}` with both error terms
instantiated from the closed library —

    (b/2ℓ²)·cnPlus + ∫_{I₋} eBf
      − C·(12(1+d)²(chiSmallDecay M)⁴C₁(μa³)^{M/3}ℓ³)      [χ-mass of the band]
      − Q·(12(1+d)²d^{-3})                                  [per-box cost × box count]
      ≤ kinWord + qLHSword . -/
theorem sliding_sum_identity_interior_concrete {N : ℕ} {ℓ d μ b : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    {a C C₁ Q : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hQ : 0 ≤ Q)
    (hreg : μ ^ (-1 / 3 : ℝ) ≤ ℓ)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ))
    (hEst : (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2
        ≤ C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3)
    {Φ : X N → ℝ} (eBf : ℝ³ → ℝ)
    (hintf : Integrable eBf)
    (hintmass : Integrable (fun u : ℝ³ => chiMass M ℓ d u))
    (hslide : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u : ℝ³, eBf u)
        ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hlow : ∀ u : ℝ³, - C * chiMass M ℓ d u ≤ eBf u)
    (hband : ∀ u ∈ goodSet ℓ d μ \ interiorSet ℓ d μ, - Q ≤ eBf u) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u in interiorSet ℓ d μ, eBf u)
        - C * (12 * (1 + d) ^ 2 * chiSmallBandDecay M d * C₁
            * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3)
        - Q * (12 * (1 + d) ^ 2 * (d ^ 3)⁻¹)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hmass := compl_mass_le hM hℓ hd hμ ha hC₁ hAδ hEst
  have hvol := bandSet_volume_le_d3 hℓ hd hμ hreg hAδ
  have hV : 0 ≤ 12 * (1 + d) ^ 2 * (d ^ 3)⁻¹ := by positivity
  exact sliding_sum_identity_interior (h := h) (M := M) eBf hℓ hd hμ hC hQ hV
    hintf hintmass hvol hslide hlow hmass hband

end Work.SmallBoxSliding
