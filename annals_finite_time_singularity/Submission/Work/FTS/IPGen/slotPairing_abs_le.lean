/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋ⁴`-Cauchy–Schwarz bound for a single leaf slot

`Work.FTS.TransportS.slotPairing ρ a b f g = ∫_z ∫_θ ρ · D_z^bD_θ^a f · D_z^bD_θ^a g` is the
elementary slot pairing out of which the coercive pairing `IP4` is assembled.  Every leaf
weight `ρ` of `IP4` (`ρ = leafEta = w² sin(2θ)^{-η}`, `ρ = leafOne = w²`, or `ρ = leafGam α =
w² sin(2θ)^{-γ}` at a slot with `a ≥ 1`) is (a.e.) dominated by the slot weight of the
corresponding summand of `HkIntegrand α 4`, so Cauchy–Schwarz in `L²(Iz × Iθ)` gives

  `|slotPairing ρ a b f g| ≤ |f|_{ℋ⁴} · |g|_{ℋ⁴} = Xn α f · Xn α g`,

with the *sharp* constant `1` (this is the per-slot form of `H4Pair_cs` for the leaf weights of
`IP4`, and the `cs` clause of `N4ExtraQ`/`IPLinHQo` for the concrete coercive pairing).

The only subtlety is that at the two endpoints `θ = 0, π/2` the junk values of the `rpow`
weights (`x ^ (-q) = 0` at `x = 0`) prevent the pointwise domination from holding; the two
endpoints are null for `volume.restrict Iθ`, so the estimate is proved a.e. in `θ`.  All the
constants are `1`: nothing is lost beyond the two Cauchy–Schwarz inequalities.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Membership in the *open* angular interval, almost everywhere -/

/-- For `volume.restrict Iθ` the two endpoints `0`, `π/2` are null, so `θ` lies in the open
interval a.e.: `Icc 0 (π/2)` and `Ioo 0 (π/2)` agree a.e. -/
theorem ip_ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have h : volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := volume)).symm
  rw [h]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-! ## The square-root form of Cauchy–Schwarz on a set -/

/-- **Cauchy–Schwarz in square-root form**: for nonnegative integrable `A`, `B` on `s`,

  `∫_s √A · √B ≤ √(∫_s A) · √(∫_s B)`.

(For nonnegative `A` the square root `√A` is square-integrable exactly when `A` is integrable,
so this is `Work.Spaces.cs_integral` applied to `√A`, `√B`.) -/
theorem cs_sqrt_le {s : Set ℝ} {A B : ℝ → ℝ}
    (hA : IntegrableOn A s) (hB : IntegrableOn B s)
    (hAnn : ∀ x, 0 ≤ A x) (hBnn : ∀ x, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) := by
  have hu_meas : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hu_sq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hAnn x)).symm))
  have hv_sq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr (Filter.Eventually.of_forall (fun x => (Real.sq_sqrt (hBnn x)).symm))
  have hu_lp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hu_meas).mpr hu_sq
  have hv_lp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hv_meas).mpr hv_sq
  have hcs := Work.Spaces.cs_integral hu_lp hv_lp
  have e1 : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hAnn x))
  have e2 : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => Real.sq_sqrt (hBnn x))
  rw [e1, e2] at hcs
  calc (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in s, A x) * (∫ x in s, B x)) := Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in s, A x) * Real.sqrt (∫ x in s, B x) :=
        Real.sqrt_mul (integral_nonneg hAnn) _

/-! ## The two-level Cauchy–Schwarz engine for a general nonnegative weight -/

/-- **The `L²`-Cauchy–Schwarz bound for a single slot with a general weight.**

Suppose `ρ ≥ 0` on `Iθ` and that, a.e. in `θ` (equivalently for `θ ∈ (0,π/2)`, the two
endpoints being null), the weight times the square of each slot is dominated by the
`ℋ⁴`-integrand of the corresponding datum:
`ρ z θ · X z θ ² ≤ HkIntegrand α 4 f z θ` and `ρ z θ · Y z θ ² ≤ HkIntegrand α 4 g z θ`.
Then the weighted slot pairing is bounded by the product of the two `ℋ⁴`-norms with constant
`1`:

  `|∫_z ∫_θ ρ · X · Y| ≤ |f|_{ℋ⁴} · |g|_{ℋ⁴}`.

Route: at each `z`, the pointwise domination turns `ρ |X| |Y|` into the product of the two
`L²`-functions `√(HkIntegrand α 4 f z ·)`, `√(HkIntegrand α 4 g z ·)`; the `θ`-Cauchy–Schwarz
(`cs_sqrt_le`) bounds the `θ`-integral of that product by `√(F z) √(G z)`, where `F`, `G` are
the two slice energies; the `z`-Cauchy–Schwarz (`cs_sqrt_le` again, with `F`, `G` integrable by
`HkMem`) then gives `√(HkSq α 4 f) · √(HkSq α 4 g)`. -/
theorem cs_slotInt_abs_le {α : ℝ} {ρ X Y f g : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g)
    (hρnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hdf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 f z θ)
    (hdg : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g z θ with hG
  have hFnn : ∀ z, 0 ≤ F z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hFint : IntegrableOn F Work.Spaces.Iz := by rw [hF]; exact hmf.2
  have hGint : IntegrableOn G Work.Spaces.Iz := by rw [hG]; exact hmg.2
  -- the `z`-majorant `√F · √G` is integrable, `F` and `G` being in `L¹`
  have hprod : IntegrableOn (fun z => Real.sqrt (F z) * Real.sqrt (G z)) Work.Spaces.Iz := by
    have hFm : AEStronglyMeasurable (fun z => Real.sqrt (F z)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hFint.aestronglyMeasurable
    have hGm : AEStronglyMeasurable (fun z => Real.sqrt (G z)) (volume.restrict Work.Spaces.Iz) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable
    have hFsq : Integrable (fun z => Real.sqrt (F z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hFint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hFnn z)).symm))
    have hGsq : Integrable (fun z => Real.sqrt (G z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
      hGint.congr (Eventually.of_forall (fun z => (Real.sq_sqrt (hGnn z)).symm))
    have hFlp : MemLp (fun z => Real.sqrt (F z)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq hFm).mpr hFsq
    have hGlp : MemLp (fun z => Real.sqrt (G z)) 2 (volume.restrict Work.Spaces.Iz) :=
      (memLp_two_iff_integrable_sq hGm).mpr hGsq
    exact memLp_one_iff_integrable.mp (hFlp.mul hGlp)
  -- the angular estimate, for every `z ∈ Iz`
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
    intro z hz
    have hprodθ : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) Work.Spaces.Iθ := by
      have hfm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmf.1 z hz).aestronglyMeasurable
      have hgm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmg.1 z hz).aestronglyMeasurable
      have hfsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmf.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 f z θ)).symm))
      have hgsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmg.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α 4 g z θ)).symm))
      have hflp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hfm).mpr hfsq
      have hglp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hgm).mpr hgsq
      exact memLp_one_iff_integrable.mp (hflp.mul hglp)
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |ρ z θ * X z θ * Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) := by
      filter_upwards [ip_ae_mem_Ioo_Iθ] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hρ0 : 0 ≤ ρ z θ := hρnn z hz θ hθI
      have hsX : Real.sqrt (ρ z θ * (X z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ) :=
        Real.sqrt_le_sqrt (hdf z hz θ hθ)
      have hsY : Real.sqrt (ρ z θ * (Y z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
        Real.sqrt_le_sqrt (hdg z hz θ hθ)
      have hs : Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ) = ρ z θ := by
        rw [← sq, Real.sq_sqrt hρ0]
      calc |ρ z θ * X z θ * Y z θ|
          = ρ z θ * |X z θ| * |Y z θ| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hρ0]
        _ = (Real.sqrt (ρ z θ) * Real.sqrt (ρ z θ)) * |X z θ| * |Y z θ| := by rw [hs]
        _ = Real.sqrt (ρ z θ * (X z θ) ^ 2) * Real.sqrt (ρ z θ * (Y z θ) ^ 2) := by
            rw [Real.sqrt_mul hρ0, Real.sqrt_mul hρ0, Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
            ring
        _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
            mul_le_mul hsX hsY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α 4 f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α 4 g z θ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) hprodθ hpt
      _ ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
          rw [hF, hG]
          exact cs_sqrt_le (hmf.1 z hz) (hmg.1 z hz)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g z θ)
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ ∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hprod
          (ae_restrict_of_forall_mem hIzm hslice)
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        cs_sqrt_le hFint hGint hFnn hGnn
    _ = Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkSq, Work.Spaces.HkSq, hF, hG]

/-! ## Nonnegativity of the leaf weights, and their pointwise slot domination -/

/-- Every leaf weight of `IP4` is nonnegative on `Iz × Iθ`. -/
theorem leaf_nonneg {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ := by
  rcases hρ with rfl | rfl | ⟨_, rfl⟩
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)
  · intro z hz θ hθ
    exact sq_nonneg _
  · intro z hz θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθ) _)

/-- **The pointwise slot domination of a leaf weight.**  For the slot `(a,b)` of `ℋ⁴`
(`a + b ≤ 4`) and any leaf weight `ρ` attached to `a`, the weight times the square of the slot
of `h` is dominated by the `ℋ⁴`-integrand of `h`, at every point with `z ∈ Iz`,
`θ ∈ (0,π/2)`:

  `ρ z θ · (D_z^bD_θ^a h z θ)² ≤ HkIntegrand α 4 h z θ`.

Each leaf weight is the square of one of the block weights `Whz = w σ^{-η/2}` (`leafEta`), `1`
(`leafOne`, which is dominated by `Whz²`, resp. by `Wm²` at the mixed slots) and `Wm = W σ^{-γ/2}`
(`leafGam`, only at slots with `a ≥ 1`), and the blocks of `HkIntegrand α 4` are exactly the
squares of those weights times the slots (`Work.Spaces.sq_le_HkIntegrand_z` and
`Work.Spaces.sq_le_HkIntegrand_mixed`). -/
theorem leaf_dom {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 4)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (h : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσ : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha, rfl⟩
  · -- `ρ = leafEta = Whz²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ 4 := by omega
      have hkey : Work.FTS.TransportS.leafEta z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by
        rw [Work.FTS.TransportS.leafEta, ← Work.FTS.H2.hbi_Whz_sq z θ hσ]
        ring
      rw [hkey]
      exact Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ b hb
    · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h0
      have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
      simp only [Work.FTS.H2.Wm] at hWm
      have hle : Work.FTS.TransportS.leafEta z θ ≤ Work.Spaces.Wt α z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafEta, hWm]
        exact mul_le_mul_of_nonneg_left (Work.FTS.H2.rpow_eta_le_gam hα hθI) (sq_nonneg _)
      calc Work.FTS.TransportS.leafEta z θ * (Work.Spaces.mixed b a h z θ) ^ 2
          ≤ Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ a b h1 (by omega)
  · -- `ρ = leafOne = 1²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ 4 := by omega
      have hle : Work.FTS.TransportS.leafOne z θ ≤ Work.FTS.H2.Whz z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hσ]
        exact le_mul_of_one_le_right (sq_nonneg _)
          (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          ≤ Work.FTS.H2.Whz z θ ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ b hb
    · have h1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr h0
      have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
      simp only [Work.FTS.H2.Wm] at hWm
      have hle : Work.FTS.TransportS.leafOne z θ ≤ Work.Spaces.Wt α z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafOne, hWm]
        exact le_mul_of_one_le_right (sq_nonneg _)
          (Work.FTS.TransportS.one_le_rpow_neg (le_of_lt (Work.Spaces.gam_pos hα)) hθ)
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.mixed b a h z θ) ^ 2
          ≤ Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ a b h1 (by omega)
  · -- `ρ = leafGam α = Wm²`, only at slots with `a ≥ 1`
    have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
    simp only [Work.FTS.H2.Wm] at hWm
    have hle : Work.FTS.TransportS.leafGam α z θ = Work.Spaces.Wt α z θ ^ 2 := by
      rw [Work.FTS.TransportS.leafGam, ← hWm]
    calc Work.FTS.TransportS.leafGam α z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        = Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 := by rw [hle]
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ a b ha (by omega)

/-! ## The requested per-slot bound -/

theorem slotPairing_abs_le {α : ℝ} (hα : 0 < α) {a b : ℕ} (hab : a + b ≤ 4)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ)
    {f g : Work.FTS.Galerkin.Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmf : Work.Spaces.HkMem α 4 f)
    (hmg : Work.Spaces.HkMem α 4 g) :
    |Work.FTS.TransportS.slotPairing ρ a b f g|
      ≤ Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      ρ z θ * Work.Spaces.mixed b a f z θ * Work.Spaces.mixed b a g z θ|
      ≤ Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g :=
    cs_slotInt_abs_le hmf hmg (leaf_nonneg hρ)
      (fun z hz θ hθ => leaf_dom hα hab hρ f hz hθ)
      (fun z hz θ hθ => leaf_dom hα hab hρ g hz hθ)
  rw [Work.FTS.TransportS.slotPairing]
  simpa only [Work.FTS.Nonlin.Xn] using hmain

end Work.FTS.IPGen
