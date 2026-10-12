import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.SmallBoxSliding.bandSet_measure_le
import Submission.Work.SmallBoxSliding.compl_mass_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Item 1 — the executable sliding-sum identity (FS `eq:BSsliding2` / `eq:appsliding`)

FS `thm:aprioriHLambda`, step 2.  On the good set
`G := {u : ‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}}` (the set of `u` for which every
box `B(u)` has shortest side `λ₁(u) ≥ μ^{-1/3}`, `Geom.goodSet_shortSide`) the
sliding localisation gives

    E_ℓ(Φ) ≥ (b/2ℓ²)·cnPlus(Φ) + ∫_G eBf(u) du − (bad-set loss) ,

where `eBf` is the per-box energy word (`Defs.sboxEBWord` is the canonical
corpus instantiation: the `u`-localised small-box Hamiltonian
`H_{B(u)} = kinWordB + qLHSwordB`).

## What is hypothesis-level (see NOTES.md)

The localisation itself — "the global energy dominates
`(b/2ℓ²)·cnPlus` plus the sum over ALL sliding boxes of the box energies" —
is FS `eq:BSsliding2`, an operator-level IMS-type inequality for the
many-body Hamiltonian.  It enters below as the named hypothesis `hslide`
(together with `hlow`, the per-box lower bound on the discarded boxes, and
`hmass`, the numerical bound on the discarded `χ`-mass).  The per-box bound
itself is the output of the SmallBoxA0 area
(`SmallBoxDLBound.smallbox_dl_energy_bound`); the consumer instantiates
`eBf` from it, so nothing here waits on that area.

## What is proved here

  * `bandSet_mass_integral_le_law` — the CLOSED `chiSmallB_badband_integral_law`
    transported to `bandSet` (definitionally `chiSmallBadBand`);
  * `compl_integral_lower` — the discard step: a function that dominates
    `−C·χ_{B(u)}²`-mass pointwise is bounded below over `Gᶜ` by `−C·B` as soon
    as the discarded mass is at most `B`;
  * `sliding_sum_identity` — the identity;
  * `sliding_sum_identity_two_layer` — the same with the per-box bound
    `eBf ≤ (localised energy word)` as an explicit extra hypothesis;
  * `sliding_sum_identity_concrete` — with the loss instantiated from the law.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-- The `χ_{B(u)}`-mass `I(u) := ∫_x χ_{B(u)}(x)² dx` of the localised box. -/
def chiMass (M : ℕ) (ℓ d : ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2

@[simp] lemma chiMass_def (M : ℕ) (ℓ d : ℝ) (u : ℝ³) :
    chiMass M ℓ d u = ∫ x : ℝ³, (chiSmallB M ℓ d u x) ^ 2 := rfl

lemma chiMass_nonneg (M : ℕ) (ℓ d : ℝ) (u : ℝ³) : 0 ≤ chiMass M ℓ d u :=
  integral_nonneg (fun x => sq_nonneg _)

/-- **The bad-band mass bound (`bandSet` form of the CLOSED law)**: the mass
`∫_x χ_{B(u)}² dx` integrated over the coordinatewise `μ ↦ 4μ` band is at
most `12(1+d)²(chiSmallDecay M)⁴C₁(μa³)^{M/3}ℓ³`.  This is
`ChiSmallBand.chiSmallB_badband_integral_law` transported across
`bandSet ℓ d μ = chiSmallBadBand ℓ d μ` (definitional). -/
theorem bandSet_mass_integral_le_law {M : ℕ} (hM : 1 ≤ M) {ℓ d μ a C₁ : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ) (ha : 0 ≤ a) (hC₁ : 0 ≤ C₁)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ))
    (hEst : (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2
        ≤ C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3) :
    (∫ u in bandSet ℓ d μ, chiMass M ℓ d u)
      ≤ 12 * (1 + d) ^ 2 * chiSmallBandDecay M d * C₁
          * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3 :=
  chiSmallB_badband_integral_law hM hℓ hd hμ ha hAδ hC₁ hEst

/-- **The discard step**: if `f` dominates `−C·χ_{B(u)}²`-mass pointwise and
the discarded mass `∫_{Gᶜ} χ_{B(u)}²` is at most `B`, then `f` is bounded
below over the discarded set `Gᶜ` by `−C·B`. -/
theorem compl_integral_lower {M : ℕ} {ℓ d μ C B : ℝ} {f : ℝ³ → ℝ}
    (hC : 0 ≤ C)
    (hintf : Integrable f)
    (hintmass : Integrable (fun u : ℝ³ => chiMass M ℓ d u))
    (hlow : ∀ u : ℝ³, - C * chiMass M ℓ d u ≤ f u)
    (hmass : (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) ≤ B) :
    - C * B ≤ ∫ u in (goodSet ℓ d μ)ᶜ, f u := by
  have hG : MeasurableSet ((goodSet ℓ d μ)ᶜ) := (measurableSet_goodSet ℓ d μ).compl
  have hintg : IntegrableOn (fun u : ℝ³ => - C * chiMass M ℓ d u) ((goodSet ℓ d μ)ᶜ) :=
    (hintmass.integrableOn).const_mul (-C)
  have hmono : (∫ u in (goodSet ℓ d μ)ᶜ, - C * chiMass M ℓ d u)
      ≤ ∫ u in (goodSet ℓ d μ)ᶜ, f u := by
    refine MeasureTheory.setIntegral_mono_on hintg hintf.integrableOn hG ?_
    intro u _
    exact hlow u
  have hlin : (∫ u in (goodSet ℓ d μ)ᶜ, - C * chiMass M ℓ d u)
      = - C * (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) := by
    rw [MeasureTheory.integral_const_mul]
  have hCm : (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) ≤ B := hmass
  have hle : - C * B ≤ - C * (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) := by
    nlinarith [hCm, hC]
  linarith [hmono, hlin, hle]

/-- **The sliding-sum identity** (FS `eq:BSsliding2` → `eq:appsliding`), with
`eBf` the (free) per-box energy word and the localisation carried as the
hypothesis `hslide`.  On the good set `G`:

    (b/2ℓ²)·cnPlus + ∫_G eBf − C·B ≤ E_ℓ(Φ) ,   E_ℓ = kinWord + qLHSword .

`hslide` is FS's localisation `E_ℓ ≥ (b/2ℓ²)cnPlus + ∫_u eBf`;
`hlow` is the per-box lower bound on the discarded boxes (FS: the `χ_{B(u)}²`-
mass bound), and `hmass ≤ B` is the numerical side of the discarded mass —
discharged by `compl_mass_le` + the CLOSED `chiSmallB_badband_integral_law`
for the `eBf` produced by the SmallBoxA0 per-box bound. -/
theorem sliding_sum_identity {N : ℕ} {ℓ d μ b C B : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} {Φ : X N → ℝ} (eBf : ℝ³ → ℝ)
    (hC : 0 ≤ C)
    (hintf : Integrable eBf)
    (hintmass : Integrable (fun u : ℝ³ => chiMass M ℓ d u))
    (hslide : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u : ℝ³, eBf u)
        ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hlow : ∀ u : ℝ³, - C * chiMass M ℓ d u ≤ eBf u)
    (hmass : (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) ≤ B) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u in goodSet ℓ d μ, eBf u) - C * B
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_goodSet ℓ d μ) hintf
  have hcomp := compl_integral_lower (M := M) hC hintf hintmass hlow hmass
  linarith [hsplit, hcomp]

/-- **The sliding-sum identity, two-layer form**: the per-box bound
`eBf u ≤ w u` (the actual localised small-box energy word `w`, e.g.
`Defs.sboxEBWord`) is an explicit hypothesis, as is the localisation
`hslide` applied to `w`.  The consumer instantiates `eBf` from the SmallBoxA0
per-box bound and `w` from `Defs.sboxEBWord`. -/
theorem sliding_sum_identity_two_layer {N : ℕ} {ℓ d μ b C B : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} {Φ : X N → ℝ} (eBf w : ℝ³ → ℝ)
    (hC : 0 ≤ C)
    (hintf : Integrable eBf) (hintw : Integrable w)
    (hintmass : Integrable (fun u : ℝ³ => chiMass M ℓ d u))
    (hbox : ∀ u : ℝ³, eBf u ≤ w u)
    (hslide : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u : ℝ³, w u)
        ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hlow : ∀ u : ℝ³, - C * chiMass M ℓ d u ≤ w u)
    (hmass : (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) ≤ B) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u in goodSet ℓ d μ, eBf u) - C * B
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hG : MeasurableSet (goodSet ℓ d μ) := measurableSet_goodSet ℓ d μ
  have hle : (∫ u in goodSet ℓ d μ, eBf u) ≤ ∫ u in goodSet ℓ d μ, w u := by
    refine MeasureTheory.setIntegral_mono_on hintf.integrableOn hintw.integrableOn hG ?_
    intro u _
    exact hbox u
  have hmain := sliding_sum_identity (h := h) (M := M) w hC hintw hintmass hslide hlow hmass
  linarith

/-- **The concrete sliding-sum identity**: the discarded-mass loss is
instantiated from the CLOSED bad-band law via `compl_mass_le`.  The two error
terms are

  * `C·(12(1+d)²(chiSmallDecay M)⁴C₁(μa³)^{M/3}ℓ³)` — the `χ_{B(u)}²`-mass of
    the discarded band (the `Cμ²a(μa³)^{M/3}ℓ³` term of FS `eq:badset`);
  * `Q·V` — the slot for the accumulated per-box constant error on the
    discarded boxes (FS's `Cμad^{-3}`; take `Q := Cμa` and
    `V := 12(1+d)²d^{-3}` from `bandSet_measure_le` + the regime
    `μ^{-1/3} ≤ ℓ`). -/
theorem sliding_sum_identity_concrete {N : ℕ} {ℓ d μ b : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    {a C C₁ Q V : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) (hQ : 0 ≤ Q)
    (hV : 0 ≤ V)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ))
    (hEst : (2 * μ ^ (-1 / 3 : ℝ) / ℓ) ^ (2 * M) * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2
        ≤ C₁ * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3)
    {Φ : X N → ℝ} (eBf : ℝ³ → ℝ)
    (hintf : Integrable eBf)
    (hintmass : Integrable (fun u : ℝ³ => chiMass M ℓ d u))
    (hslide : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u : ℝ³, eBf u)
        ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hlow : ∀ u : ℝ³, - C * chiMass M ℓ d u ≤ eBf u) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u in goodSet ℓ d μ, eBf u)
        - C * (12 * (1 + d) ^ 2 * chiSmallBandDecay M d * C₁
            * (μ * a ^ 3) ^ ((M : ℝ) / 3) * ℓ ^ 3)
        - Q * V
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hmass := compl_mass_le hM hℓ hd hμ ha hC₁ hAδ hEst
  have hmain := sliding_sum_identity (h := h) (M := M) eBf hC hintf hintmass hslide hlow hmass
  have hQV : 0 ≤ Q * V := mul_nonneg hQ hV
  linarith

/-- **The band-volume cost in the `d^{-3}` form**: in the regime
`μ^{-1/3} ≤ ℓ` the `u`-measure of the bad band is at most `12(1+d)²d^{-3}`,
which is FS's `#boxes × (per-box cost)` source for the `Cμad^{-3}` error term
(`#boxes = vol(band)` in units of the box spacing). -/
theorem bandSet_measure_le_d3 {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hμ : 0 < μ)
    (hreg : μ ^ (-1 / 3 : ℝ) ≤ ℓ)
    (hAδ : 0 ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)) :
    (MeasureTheory.volume (bandSet ℓ d μ)).toReal ≤ 12 * (1 + d) ^ 2 * (d ^ 3)⁻¹ := by
  have h1 := bandSet_measure_le hℓ hd hμ hAδ
  have hμp : 0 < μ ^ (-1 / 3 : ℝ) := Real.rpow_pos_of_pos hμ _
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hpos : 0 ≤ 12 * (1 + d) ^ 2 := by positivity
  have hkey : ((ℓ * d) ^ 3)⁻¹ * (12 * μ ^ (-1 / 3 : ℝ) * ℓ ^ 2 * (1 + d) ^ 2)
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
  linarith [h1, hkey]


/-! ## The reduction of `hslide` to the telescoping identity + a word comparison

The localisation hypothesis `hslide` of `sliding_sum_identity` is FS
`eq:BSsliding2`, which FS obtain from Bratteli--Solovej [BS, Theorem 3.10]
(an operator-theoretic statement about `H_Λ(μ)` and the box-restricted
`H_{B(u)}`; see NOTES.md §7 for the analysis of why it cannot be derived from
the corpus's word-level u-partition identities).  It does, however, factor as

  (i) the *telescoping identity*
      `∫_u sboxEBWord … u du = kinWordChi + qLHSwordChi`
      (`Words.kinWordB_integral_u` + `Telescope.qLHSwordB_integral_u`) — a
      measure-theoretic identity, and
  (ii) the *word comparison* `(b/2ℓ²)cnPlus + kinWordChi + qLHSwordChi ≤ E_ℓ`,
      a single inequality between explicit corpus words.

The next theorem records this reduction. -/

/-- **`hslide` from a telescoping identity plus one word comparison.**  Given
the identity `∫_u eBf u = w` for the per-box word and the comparison `hcmp`
between the reference word `w` and the global energy word, the literal
hypothesis `hslide` of `Sliding.sliding_sum_identity` follows, hence the
sliding-sum bound. -/
theorem sliding_sum_identity_of_telescope {N : ℕ} {ℓ d μ b C B : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {M : ℕ} {Φ : X N → ℝ} (eBf : ℝ³ → ℝ) (Wr : ℝ)
    (hC : 0 ≤ C)
    (hintf : Integrable eBf)
    (hintmass : Integrable (fun u : ℝ³ => chiMass M ℓ d u))
    (htelescope : (∫ u : ℝ³, eBf u) = Wr)
    (hcmp : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + Wr
        ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hlow : ∀ u : ℝ³, - C * chiMass M ℓ d u ≤ eBf u)
    (hmass : (∫ u in (goodSet ℓ d μ)ᶜ, chiMass M ℓ d u) ≤ B) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u in goodSet ℓ d μ, eBf u) - C * B
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hslide : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u : ℝ³, eBf u)
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    rw [htelescope]
    exact hcmp
  exact sliding_sum_identity (h := h) (M := M) eBf hC hintf hintmass hslide hlow hmass

end Work.SmallBoxSliding
