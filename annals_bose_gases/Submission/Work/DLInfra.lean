import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ChallengeDeps
import Submission.Q0Value
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `dℓ`-infra layer — `u`-indexed small boxes `B(u)` and cutoffs `χ_{B(u)}`

FS `final_v2.tex` §SmallBoxes: for the second localisation one introduces
the family of small boxes

    B(u) = [−ℓ/2, ℓ/2]³ ∩ ( ℓd·u + [−ℓd/2, ℓd/2]³ ) ,   u ∈ ℝ³,

and the localising cutoffs

    χ_{B(u)}(x) = χ(x/ℓ)·χ(x/(ℓd) − u)

(`χ` the corpus cut-off, `L²`-normalised: `CubicChi.chi_L2 : ∫χ² = 1`).
This module lays down the corpus forms: `dlBox` (the set), `chiB` (the
cutoff, in terms of `chiScale`), and the first geometric facts:
(1) the support lemma `chiB_support_mem` (`χ_{B(u)}(x) ≠ 0 ⟹ x ∈ B(u)`),
(2) the per-`x` partition integral
`∫_u χ_{B(u)}(x)² du = (χ(x/ℓ))²` (translation/reflection invariance of the
Lebesgue measure + `chi_L2`), whence the normalisation
`∬ χ_{B(u)}(x)² dx du = ℓ³` (eq:chiBintegral, the corpus form of the
`(g1)`-fact of `SlidingSum.chiB_geometric_estimates`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The `u`-indexed small box `B(u) := acube ℓ ∩ (ℓd·u + acube(ℓd))` (FS:
`B(u) = [−ℓ/2,ℓ/2]³ ∩ (ℓd u + [−ℓd/2,ℓd/2]³)`), i.e. the part of the big
box `acube ℓ` lying in the small box of side `ℓ·d` centred at `(ℓ·d)•u`. -/
def dlBox (ℓ d : ℝ) (u : ℝ³) : Set ℝ³ :=
  acube ℓ ∩ {x : ℝ³ | x - (ℓ * d) • u ∈ acube (ℓ * d)}

/-- Membership in `B(u)` is coordinatewise in both cubes. -/
lemma mem_dlBox_iff (ℓ d : ℝ) (u x : ℝ³) :
    x ∈ dlBox ℓ d u ↔ x ∈ acube ℓ ∧ x - (ℓ * d) • u ∈ acube (ℓ * d) := by
  simp [dlBox]

/-- The localised cutoff `χ_{B(u)}(x) := χ(x/ℓ)·χ(x/(ℓd) − u)` (FS
eq:chiBdefinition), in corpus terms: `χ(x/ℓ) = chiScale ℓ x` and
`χ(x/(ℓd) − u) = chiScale (ℓd) (x − (ℓd)•u)`. -/
noncomputable def chiB (ℓ d : ℝ) (u x : ℝ³) : ℝ :=
  chiScale ℓ x * chiScale (ℓ * d) (x - (ℓ * d) • u)

/-- **First `χ_{B(u)}`-fact**: `χ_{B(u)}` is supported in `B(u)` — if
`χ_{B(u)}(x) ≠ 0` then `x ∈ acube ℓ` (from the `χ(x/ℓ)`-factor) and
`x − (ℓd)•u ∈ acube(ℓd)` (from the `χ(x/(ℓd) − u)`-factor). -/
lemma chiB_support_mem {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u x : ℝ³)
    (hx : chiB ℓ d u x ≠ 0) : x ∈ dlBox ℓ d u := by
  have h1 : chiScale ℓ x ≠ 0 := by
    intro h
    apply hx
    simp [chiB, h]
  have h2 : chiScale (ℓ * d) (x - (ℓ * d) • u) ≠ 0 := by
    intro h
    apply hx
    simp [chiB, h]
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  exact ⟨chiScale_mem_acube hℓ h1, chiScale_mem_acube hld h2⟩

/-- per-x partition integral: ∫_u χ_{B(u)}(x)² du = (χ(x/ℓ))². -/
lemma chiB_partition_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (x : ℝ³) :
    (∫ u : ℝ³, (chiB ℓ d u x) ^ 2) = (chiScale ℓ x) ^ 2 := by
  unfold chiB
  -- pull (χ(x/ℓ))² out (independent of u)
  have hfact : (∫ u : ℝ³, (chiScale ℓ x * chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2)
      = (chiScale ℓ x) ^ 2 * (∫ u : ℝ³, (chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2) := by
    have hpt : (fun u : ℝ³ => (chiScale ℓ x * chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2)
        = fun u : ℝ³ => (chiScale ℓ x) ^ 2 * (chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2 := by
      funext u
      ring
    rw [hpt]
    simpa using (MeasureTheory.integral_const_mul (μ := (volume : Measure ℝ³))
      (r := (chiScale ℓ x) ^ 2) (f := fun u : ℝ³ => (chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2))
  have hinner : (∫ u : ℝ³, (chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2) = 1 := by
    have hld : ℓ * d ≠ 0 := mul_ne_zero (ne_of_gt hℓ) (ne_of_gt hd)
    -- chiScale (ℓd) (x − (ℓd)•u) = chi((ℓd)⁻¹•x − u); set a := (ℓd)⁻¹•x; chi even ⟹ chi(a−u)² = chi(u−a)²
    have hpt2 : (fun u : ℝ³ => (chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2)
        = fun u : ℝ³ => (chi (u - (ℓ * d)⁻¹ • x)) ^ 2 := by
      funext u
      have hsc : chiScale (ℓ * d) (x - (ℓ * d) • u) = chi ((ℓ * d)⁻¹ • x - u) := by
        dsimp [chiScale]
        congr 1
        rw [smul_sub]
        congr 1
        rw [smul_smul, inv_mul_cancel₀ hld, one_smul]
      rw [hsc]
      -- chi(a−u)² = chi(u−a)² since chi is even
      have hsq : (chi ((ℓ * d)⁻¹ • x - u)) ^ 2 = (chi (u - (ℓ * d)⁻¹ • x)) ^ 2 := by
        congr 1
        rw [← chi_even (u - (ℓ * d)⁻¹ • x)]
        congr 1
        abel
      exact hsq
    rw [hpt2]
    -- ∫_u chi(u − a)² du = ∫χ² (translation invariance), a := (ℓd)⁻¹•x
    let a : ℝ³ := (ℓ * d)⁻¹ • x
    have htr : MeasureTheory.MeasurePreserving (fun u : ℝ³ => u - a) volume volume := by
      -- u − a = (−a) + u ; measurePreserving_add_left volume (−a)
      have hmp := MeasureTheory.measurePreserving_add_left (volume : Measure ℝ³) (-a)
      -- hmp : MeasurePreserving (fun x => (-a) + x) volume volume
      simpa [sub_eq_add_neg, add_comm] using hmp
    have himp : (∫ u : ℝ³, (chi (u - a)) ^ 2) = (∫ w : ℝ³, (chi w) ^ 2) := by
      have hφ : AEMeasurable (fun u : ℝ³ => u - a) volume := htr.aemeasurable
      have hfm : AEStronglyMeasurable (fun w : ℝ³ => (chi w) ^ 2) (Measure.map (fun u : ℝ³ => u - a) volume) := by
        exact (chi_contDiff.continuous.pow 2).aestronglyMeasurable
      have hm := MeasureTheory.integral_map (μ := volume) hφ (f := fun w : ℝ³ => (chi w) ^ 2) hfm
      -- hm : ∫ w, (chi w)^2 ∂(map (fun u => u − a) volume) = ∫ u, (chi (u − a))^2 ∂volume
      rw [htr.map_eq] at hm
      exact hm.symm
    calc
      (∫ u : ℝ³, (chi (u - a)) ^ 2) = (∫ w : ℝ³, (chi w) ^ 2) := himp
      _ = 1 := chi_L2
  calc
    (∫ u : ℝ³, (chiB ℓ d u x) ^ 2) = (chiScale ℓ x) ^ 2 * (∫ u : ℝ³, (chiScale (ℓ * d) (x - (ℓ * d) • u)) ^ 2) := by
        simpa [chiB] using hfact
    _ = (chiScale ℓ x) ^ 2 := by rw [hinner]; ring

/-- **The dilation normalisation** `∫_x (χ(x/ℓ))² dx = ℓ³` (FS eq:chiBintegral
content; the (g3)-factor): `∫_x (χ(x/ℓ))² = ℓ³·∫_s χ(s)²` by the corpus
dilation change-of-variable `integral_comp_smul_right` +
`chiScale_apply_smul`, and `∫χ² = 1` (`chi_L2`). -/
lemma chiScale_dilation_sq {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ x : ℝ³, (chiScale ℓ x) ^ 2) = ℓ ^ 3 := by
  have hsc := integral_comp_smul_right (g := fun x : ℝ³ => (chiScale ℓ x) ^ 2) hℓ
  calc
    (∫ x : ℝ³, (chiScale ℓ x) ^ 2) = ℓ ^ 3 * (∫ s : ℝ³, (chiScale ℓ (ℓ • s)) ^ 2) := hsc
    _ = ℓ ^ 3 * (∫ s : ℝ³, (chi s) ^ 2) := by
        congr 1
        have hpt : ∀ s : ℝ³, (chiScale ℓ (ℓ • s)) ^ 2 = (chi s) ^ 2 := by
          intro s
          rw [chiScale_apply_smul (ne_of_gt hℓ)]
        apply integral_congr_ae
        exact ae_of_all _ hpt
    _ = ℓ ^ 3 := by
        rw [chi_L2]
        ring

/-- **The `u`-normalisation (g3)**: `∬ χ_{B(u)}(x)² dx du = ℓ³` — from the
per-`x` partition `chiB_partition_u` and the dilation `chiScale_dilation_sq`. -/
lemma chiB_double_integral_u_sq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) :
    (∫ x : ℝ³, ∫ u : ℝ³, (chiB ℓ d u x) ^ 2) = ℓ ^ 3 := by
  calc
    (∫ x : ℝ³, ∫ u : ℝ³, (chiB ℓ d u x) ^ 2)
        = (∫ x : ℝ³, (chiScale ℓ x) ^ 2) := by
            apply integral_congr_ae
            exact ae_of_all _ (fun x => chiB_partition_u hℓ hd x)
    _ = ℓ ^ 3 := chiScale_dilation_sq hℓ

end BoseGases

end Submission
