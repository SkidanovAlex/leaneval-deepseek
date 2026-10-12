import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.ShellMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial null-transfer: a null norm-preimage gives a null set of radii

**Assigned sub-lemma** (used by `Submission.ProfileFormula.canonicalProfile_eq_profile`
and friends):

    null_of_norm_preimage_null {S : Set ℝ}
      (hSvol : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0) :
      (volume : Measure ℝ) (S ∩ Set.Ioi (0 : ℝ)) = 0

The norm-preimage of `S` has zero volume in `ℝ³` ⇒ the *radii* in `S` form a
Lebesgue-null subset of `(0,∞)`.  This is the 3D→1D converse of
`Submission.AERadial.volume_preimage_norm_null_r3` / `volume_preimage_norm_null`
(which go 1D→3D).  It is valid because the Lebesgue measure of `ℝ³` in polar
coordinates is `σ × (r² dr)` on `(sphere 0 1) × (0,∞)` — the sphere factor is
finite and *positive*, and the density `r²` is positive on `(0,∞)`.

## Implementation

The proof is organised as:

1. **3D → `(0,∞)`-measure.**  Hull the (null) preimage set to a measurable null
   `H`, push it through the polar homeomorphism `Φ` (a measure-preserving
   homeomorphism onto `ShellS2 × ShellRpos` w.r.t. `volume.toSphere.prod
   volumeIoiPow 2`), obtaining a measurable null superset of `univ ×ˢ Ŝ`,
   `Ŝ := {r : (0,∞) | r ∈ S}`.  The product-measure of a rectangle is the
   product of the measures (`Measure.prod_prod`, which needs no measurability),
   and the sphere factor is finite and non-zero (`Measure.toSphere_ne_zero`),
   so `(volumeIoiPow 2) Ŝ = 0`.

2. **`(0,∞)`-measure → Lebesgue measure on ℝ.**  `volumeIoiPow 2` is Lebesgue
   measure on `(0,∞)` with density `r ↦ r²`.  On each piece bounded below by a
   positive `a` this density is `≥ a²`, so a `volumeIoiPow 2`-null measurable
   set has zero `Measure.comap Subtype.val volume`-measure (an integral lower
   bound `ofReal a² * ν s ≤ volumeIoiPow 2 s`, then `mul_eq_zero`).  A general
   (possibly non-measurable) `Ŝ` is handled by taking its measurable hull and
   covering by countably many pieces `{r | 1/(n+1) ≤ r}`; null sets are then
   transferred back to ℝ through `MeasurableEmbedding.comap_apply`
   (`ν s = volume (val '' s)`), and the conclusion
   `volume (S ∩ Ioi 0) = 0` follows from `val '' Ŝ = S ∩ Ioi 0` by
   monotonicity of measures.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- For a measurable `s ⊆ {r | a ≤ r}` with `0 ≤ a`, the density of
`volumeIoiPow 2` (namely `r ↦ r²`) is bounded below by the constant `a²`,
so `a² • ν s ≤ volumeIoiPow 2 s`, where `ν` is Lebesgue measure on `(0,∞)`. -/
lemma density_volumeIoiPow_two {a : ℝ} (ha : 0 ≤ a) {s : Set ShellRpos}
    (hsmeas : MeasurableSet s) (hs : ∀ r : ShellRpos, r ∈ s → a ≤ (r : ℝ)) :
    ENNReal.ofReal (a ^ 2) * (Measure.comap (Subtype.val : ShellRpos → ℝ) volume) s ≤
      (Measure.volumeIoiPow 2 : Measure ShellRpos) s := by
  calc
    ENNReal.ofReal (a ^ 2) * (Measure.comap (Subtype.val : ShellRpos → ℝ) volume) s
        = ∫⁻ (x : ShellRpos) in s, ENNReal.ofReal (a ^ 2)
            ∂(Measure.comap (Subtype.val : ShellRpos → ℝ) volume) := by
          rw [setLIntegral_const]
    _ ≤ ∫⁻ (x : ShellRpos) in s, ENNReal.ofReal ((x : ℝ) ^ 2)
            ∂(Measure.comap (Subtype.val : ShellRpos → ℝ) volume) := by
          apply setLIntegral_mono
          · measurability
          · intro x hx
            apply ENNReal.ofReal_le_ofReal
            nlinarith [sq_nonneg ((x : ℝ) - a), hs x hx, ha]
    _ = (Measure.volumeIoiPow 2 : Measure ShellRpos) s := by
          rw [Measure.volumeIoiPow]
          rw [MeasureTheory.withDensity_apply (f := fun x : ShellRpos => ENNReal.ofReal ((x : ℝ) ^ 2)) hsmeas]

/-- Every positive real is bounded below by `1/(n+1)` for some `n`. -/
lemma exists_inv_succ_le {r : ℝ} (hr : 0 < r) : ∃ n : ℕ, (1 : ℝ) / (n + 1) ≤ r := by
  rcases exists_nat_gt (1 / r) with ⟨n, hn⟩
  have hnpos : 0 < (n : ℝ) := lt_trans (one_div_pos.mpr hr) hn
  have hn1 : (1 : ℕ) ≤ n := by
    exact Nat.succ_le_of_lt (by exact_mod_cast hnpos : 0 < n)
  let m : ℕ := n - 1
  have hm1 : m + 1 = n := by
    dsimp [m]
    exact Nat.sub_add_cancel hn1
  have hden : (↑m : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hm1
  refine ⟨m, ?_⟩
  rw [hden]
  have hrne : r ≠ 0 := ne_of_gt hr
  have hstep : (1 / r) * r < (n : ℝ) * r := mul_lt_mul_of_pos_right hn hr
  have h1 : (1 : ℝ) < (n : ℝ) * r := by
    simpa [inv_mul_cancel₀ hrne] using hstep
  exact le_of_lt (by
    calc
      (1 : ℝ) / (n : ℝ) < (1 : ℝ) / (n : ℝ) * ((n : ℝ) * r) := by
        simpa using (mul_lt_mul_of_pos_left h1 (one_div_pos.mpr hnpos))
      _ = r := by field_simp [hnpos.ne'])

/-- If `U ⊆ {r | a ≤ r}` (`a > 0`) is `volumeIoiPow 2`-null, then its image
under the coercion `(0,∞) → ℝ` is Lebesgue-null. -/
lemma volume_null_of_volumeIoiPow_null_below {U : Set ShellRpos} {a : ℝ} (ha : 0 < a)
    (hUa : ∀ r : ShellRpos, r ∈ U → a ≤ (r : ℝ))
    (hρ : (Measure.volumeIoiPow 2 : Measure ShellRpos) U = 0) :
    (volume : Measure ℝ) ((↑) '' U : Set ℝ) = 0 := by
  let W : Set ShellRpos :=
    toMeasurable (Measure.volumeIoiPow 2 : Measure ShellRpos) U ∩ {r : ShellRpos | a ≤ (r : ℝ)}
  have hUmem : U ⊆ W := by
    intro r hr
    exact ⟨subset_toMeasurable _ _ hr, hUa r hr⟩
  have hWmeas : MeasurableSet W := by
    dsimp [W]
    exact (measurableSet_toMeasurable _ _).inter ((measurableSet_Ici).preimage measurable_subtype_coe)
  have hρW : (Measure.volumeIoiPow 2 : Measure ShellRpos) W = 0 := by
    refine measure_mono_null (s := W)
      (t := toMeasurable (Measure.volumeIoiPow 2 : Measure ShellRpos) U) ?_ ?_
    · intro r hr
      exact hr.1
    · rw [measure_toMeasurable]
      exact hρ
  have hνW : (Measure.comap (Subtype.val : ShellRpos → ℝ) volume) W = 0 := by
    have hineq : ENNReal.ofReal (a ^ 2) * (Measure.comap (Subtype.val : ShellRpos → ℝ) volume) W
        ≤ (Measure.volumeIoiPow 2 : Measure ShellRpos) W := by
      apply density_volumeIoiPow_two (a := a) (le_of_lt ha) hWmeas
      intro r hr
      exact hr.2
    have hprod0 : ENNReal.ofReal (a ^ 2) * (Measure.comap (Subtype.val : ShellRpos → ℝ) volume) W = 0 := by
      apply le_antisymm
      · simpa [hρW] using hineq
      · exact bot_le
    have hne : ENNReal.ofReal (a ^ 2) ≠ 0 := by
      intro hz
      have hle : a ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hz
      nlinarith [sq_pos_of_ne_zero ha.ne']
    exact (mul_eq_zero.mp hprod0).resolve_left hne
  have himgsub : ((↑) '' U : Set ℝ) ⊆ ((↑) '' W : Set ℝ) := by
    intro y hy
    rcases hy with ⟨r, hrU, rfl⟩
    exact ⟨r, hUmem hrU, rfl⟩
  have hvolW : (volume : Measure ℝ) ((↑) '' W : Set ℝ) = 0 := by
    rw [← (MeasurableEmbedding.comap_apply (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
      (volume : Measure ℝ) W)]
    exact hνW
  exact measure_mono_null himgsub hvolW

/-- If `U ⊆ (0,∞)` is `volumeIoiPow 2`-null, then its image in ℝ is Lebesgue-null. -/
lemma volume_null_of_volumeIoiPow_null {U : Set ShellRpos}
    (hρ : (Measure.volumeIoiPow 2 : Measure ShellRpos) U = 0) :
    (volume : Measure ℝ) ((↑) '' U : Set ℝ) = 0 := by
  let piece : ℕ → Set ShellRpos := fun n =>
    U ∩ {r : ShellRpos | (1 : ℝ) / (n + 1) ≤ (r : ℝ)}
  have hcover : U ⊆ ⋃ n : ℕ, piece n := by
    intro r hr
    rcases exists_inv_succ_le (r := (r : ℝ)) r.2 with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, ⟨hr, hn⟩⟩
  have hpiece0 : ∀ n : ℕ, (volume : Measure ℝ) ((↑) '' piece n : Set ℝ) = 0 := by
    intro n
    have ha : 0 < (1 : ℝ) / (n + 1) := by positivity
    apply volume_null_of_volumeIoiPow_null_below (a := (1 : ℝ) / (n + 1)) ha
    · intro r hr
      exact hr.2
    · exact measure_mono_null (s := piece n) (t := U) (by intro r hr; exact hr.1) hρ
  have hunion : (volume : Measure ℝ) (⋃ n : ℕ, ((↑) '' piece n : Set ℝ)) = 0 := by
    exact measure_iUnion_null hpiece0
  have himg : ((↑) '' U : Set ℝ) ⊆ ⋃ n : ℕ, ((↑) '' piece n : Set ℝ) := by
    intro y hy
    rcases hy with ⟨r, hrU, rfl⟩
    have hrcover : r ∈ ⋃ n : ℕ, piece n := hcover hrU
    rw [Set.mem_iUnion] at hrcover
    rcases hrcover with ⟨n, hn⟩
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [Set.mem_image]
    refine ⟨r, hn, rfl⟩
  exact measure_mono_null himg hunion

/-- **3D → `(0,∞)`:** if the norm-preimage of `S` is null in `ℝ³`, then the
positive radii in `S` form a null set for the measure `volumeIoiPow 2` on
`(0,∞)` (Lebesgue with density `r²`). -/
lemma volumeIoiPow_null_of_norm_preimage_null {S : Set ℝ}
    (hSvol : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0) :
    (Measure.volumeIoiPow 2 : Measure ShellRpos) {r : ShellRpos | (r : ℝ) ∈ S} = 0 := by
  let Φ : ({0}ᶜ : Set ℝ³) ≃ₜ (ShellS2 × ShellRpos) := homeomorphUnitSphereProd ℝ³
  let σ : Measure ShellS2 := (volume.toSphere : Measure ShellS2)
  let ρ : Measure ShellRpos := (Measure.volumeIoiPow 2 : Measure ShellRpos)
  let P : Set ℝ³ := {x : ℝ³ | ‖x‖ ∈ S}
  let H : Set ℝ³ := toMeasurable (volume : Measure ℝ³) P
  have hHmeas : MeasurableSet H := measurableSet_toMeasurable _ _
  have hHvol : (volume : Measure ℝ³) H = 0 := by
    dsimp [H]
    rw [measure_toMeasurable]
    exact hSvol
  have hPH : P ⊆ H := by
    intro x hx
    exact subset_toMeasurable (volume : Measure ℝ³) P hx
  let B : Set ({0}ᶜ : Set ℝ³) := {x : ({0}ᶜ : Set ℝ³) | (x : ℝ³) ∈ H}
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    exact hHmeas.preimage measurable_subtype_coe
  have hAHmeas : MeasurableSet (Φ '' B) := by
    exact (Homeomorph.measurableEmbedding Φ).measurableSet_image.mpr hBmeas
  have hmp : MeasurePreserving Φ (volume.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³)) (σ.prod ρ) := by
    simpa [Φ, σ, ρ] using
      (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd (μ := (volume : Measure ℝ³)))
  have hAH0 : (σ.prod ρ) (Φ '' B) = 0 := by
    have hmap : (volume.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³)).map Φ = σ.prod ρ := hmp.map_eq
    rw [← hmap]
    rw [Measure.map_apply (Homeomorph.measurable Φ) hAHmeas]
    have hpre : Φ ⁻¹' (Φ '' B) = B := by
      exact Set.preimage_image_eq B (Homeomorph.injective Φ)
    rw [hpre]
    have hcomap : (Measure.comap (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³) (volume : Measure ℝ³)) B
        = (volume : Measure ℝ³) ((Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³) '' B) := by
      exact MeasurableEmbedding.comap_apply
        (MeasurableEmbedding.subtype_coe ((measurableSet_singleton (0 : ℝ³)).compl : MeasurableSet ({0}ᶜ : Set ℝ³)))
        (volume : Measure ℝ³) B
    rw [hcomap]
    refine measure_mono_null (s := (Subtype.val : ({0}ᶜ : Set ℝ³) → ℝ³) '' B) (t := H) ?_ hHvol
    intro y hy
    rcases hy with ⟨b, hb, rfl⟩
    exact hb
  let Sh : Set ShellRpos := {r : ShellRpos | (r : ℝ) ∈ S}
  have hcover : (Set.univ : Set ShellS2) ×ˢ Sh ⊆ Φ '' B := by
    intro z hz
    rcases hz with ⟨hz1, hz2⟩
    let x : ({0}ᶜ : Set ℝ³) := Φ.symm z
    have hxH : (x : ℝ³) ∈ H := by
      have hxP : (x : ℝ³) ∈ P := by
        dsimp [P]
        have hxv : (x : ℝ³) = (z.2 : ℝ) • (z.1 : ℝ³) := by
          dsimp [x]
          rw [homeomorphUnitSphereProd_symm_apply_coe]
        have hnx : ‖(x : ℝ³)‖ = (z.2 : ℝ) := by
          rw [hxv, norm_smul]
          have hz1 : ‖(z.1 : ℝ³)‖ = 1 := by
            simp
          have hz2nn : 0 ≤ (z.2 : ℝ) := le_of_lt z.2.2
          rw [hz1]
          simp [abs_of_nonneg hz2nn]
        simpa [Sh, hnx] using hz2
      exact hPH hxP
    refine ⟨x, ?_, ?_⟩
    · dsimp [B]
      exact hxH
    · dsimp [x]
      exact Homeomorph.apply_symm_apply Φ z
  have hcover0 : (σ.prod ρ) ((Set.univ : Set ShellS2) ×ˢ Sh) = 0 :=
    measure_mono_null hcover hAH0
  have hprod0 : σ Set.univ * ρ Sh = 0 := by
    rw [← Measure.prod_prod (μ := σ) (ν := ρ) Set.univ Sh]
    exact hcover0
  have hσne0 : σ Set.univ ≠ 0 := by
    have hne : σ ≠ 0 := MeasureTheory.Measure.toSphere_ne_zero (volume : Measure ℝ³)
    intro h
    exact hne (Measure.measure_univ_eq_zero.mp h)
  exact (mul_eq_zero.mp hprod0).resolve_left hσne0

/-- **Null-transfer**: if the preimage of `S` under the norm is null in `ℝ³`,
then the positive radii of `S` are Lebesgue-null. -/
theorem null_of_norm_preimage_null {S : Set ℝ}
    (hSvol : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0) :
    (volume : Measure ℝ) (S ∩ Set.Ioi (0 : ℝ)) = 0 := by
  have hρU : (Measure.volumeIoiPow 2 : Measure ShellRpos) {r : ShellRpos | (r : ℝ) ∈ S} = 0 :=
    volumeIoiPow_null_of_norm_preimage_null hSvol
  have hvolImg : (volume : Measure ℝ) ((↑) '' {r : ShellRpos | (r : ℝ) ∈ S} : Set ℝ) = 0 :=
    volume_null_of_volumeIoiPow_null hρU
  have hset : ((↑) '' {r : ShellRpos | (r : ℝ) ∈ S} : Set ℝ) = S ∩ Set.Ioi (0 : ℝ) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨r, hr, rfl⟩
      exact ⟨hr, r.2⟩
    · intro hy
      rcases hy with ⟨hyS, hy0⟩
      refine ⟨⟨y, hy0⟩, hyS, rfl⟩
  rw [← hset]
  exact hvolImg

end Submission.BoseGases
