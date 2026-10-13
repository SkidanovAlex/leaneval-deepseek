/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `ℋ^n`-Cauchy–Schwarz bound for a single leaf slot, in every order `n`

`Work.FTS.IPGen.slotPairing_abs_le` proves

  `|slotPairing ρ a b f g| ≤ |f|_{ℋ⁴}·|g|_{ℋ⁴}`   (`a + b ≤ 4`),

with the sharp constant `1`.  The proof never uses anything special about `4`: the `ℋ^k`
norm is a sum of weighted `L²`-norms of the derivatives `D_z^i f` (`i ≤ k`) and `D_z^jD_θ^i f`
(`i ≥ 1`, `i + j ≤ k`), and every leaf weight `ρ` of the slot `a` is pointwise dominated by
the corresponding slot weight of `HkIntegrand α k` as soon as `a + b ≤ k`.  This module
repeats that argument verbatim with `4` replaced by an arbitrary `n : ℕ`, giving the
general-order slot bound

  `|slotPairing ρ a b f g| ≤ |f|_{ℋ^n}·|g|_{ℋ^n}`   (`a + b ≤ n`),

which is what the `ℋ^n`-transfer estimates of the `E4R3` chapter consume.

All declarations here are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.IPGen.slotPairing_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two-level Cauchy–Schwarz engine, in general order -/

/-- **The `L²`-Cauchy–Schwarz bound for a single slot with a general weight and general order.**

This is `Work.FTS.IPGen.cs_slotInt_abs_le` with `4` replaced by `n`: suppose `ρ ≥ 0` on `Iθ`
and that, for `θ ∈ (0,π/2)` (the endpoints being null), the weight times the square of each
slot is dominated by the `ℋ^n`-integrand of the corresponding datum.  Then

  `|∫_z ∫_θ ρ · X · Y| ≤ |f|_{ℋ^n} · |g|_{ℋ^n}`. -/
theorem cs_slotInt_abs_le_gen {α : ℝ} {n : ℕ} {ρ X Y f g : ℝ → ℝ → ℝ}
    (hmf : Work.Spaces.HkMem α n f) (hmg : Work.Spaces.HkMem α n g)
    (hρnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ ρ z θ)
    (hdf : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (X z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n f z θ)
    (hdg : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      ρ z θ * (Y z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n g z θ) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := by
  have hIθm : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hIzm : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  set F : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n f z θ with hF
  set G : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ with hG
  have hFnn : ∀ z, 0 ≤ F z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n f z θ
  have hGnn : ∀ z, 0 ≤ G z := fun z =>
    integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α n g z θ
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
    have hprodθ : IntegrableOn (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
        * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ)) Work.Spaces.Iθ := by
      have hfm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmf.1 z hz).aestronglyMeasurable
      have hgm : AEStronglyMeasurable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n g z θ))
          (volume.restrict Work.Spaces.Iθ) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable (hmg.1 z hz).aestronglyMeasurable
      have hfsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmf.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α n f z θ)).symm))
      have hgsq : Integrable
          (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) ^ 2)
          (volume.restrict Work.Spaces.Iθ) :=
        (hmg.1 z hz).congr (Eventually.of_forall (fun θ =>
          (Real.sq_sqrt (Work.Spaces.HkIntegrand_nonneg α n g z θ)).symm))
      have hflp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hfm).mpr hfsq
      have hglp : MemLp (fun θ => Real.sqrt (Work.Spaces.HkIntegrand α n g z θ)) 2
          (volume.restrict Work.Spaces.Iθ) :=
        (memLp_two_iff_integrable_sq hgm).mpr hgsq
      exact memLp_one_iff_integrable.mp (hflp.mul hglp)
    have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |ρ z θ * X z θ * Y z θ|
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) := by
      filter_upwards [Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ] with θ hθ
      have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have hρ0 : 0 ≤ ρ z θ := hρnn z hz θ hθI
      have hsX : Real.sqrt (ρ z θ * (X z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n f z θ) :=
        Real.sqrt_le_sqrt (hdf z hz θ hθ)
      have hsY : Real.sqrt (ρ z θ * (Y z θ) ^ 2)
          ≤ Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) :=
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
        _ ≤ Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
              * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) :=
            mul_le_mul hsX hsY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
        ≤ ∫ θ in Work.Spaces.Iθ, |ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
      _ ≤ ∫ θ in Work.Spaces.Iθ, Real.sqrt (Work.Spaces.HkIntegrand α n f z θ)
            * Real.sqrt (Work.Spaces.HkIntegrand α n g z θ) :=
          integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) hprodθ hpt
      _ ≤ Real.sqrt (F z) * Real.sqrt (G z) := by
          rw [hF, hG]
          exact Work.FTS.IPGen.cs_sqrt_le (hmf.1 z hz) (hmg.1 z hz)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α n f z θ)
            (fun θ => Work.Spaces.HkIntegrand_nonneg α n g z θ)
  calc |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ|
      ≤ ∫ z in Work.Spaces.Iz,
          |∫ θ in Work.Spaces.Iθ, ρ z θ * X z θ * Y z θ| := abs_integral_le_integral_abs
    _ ≤ ∫ z in Work.Spaces.Iz, Real.sqrt (F z) * Real.sqrt (G z) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hprod
          (ae_restrict_of_forall_mem hIzm hslice)
    _ ≤ Real.sqrt (∫ z in Work.Spaces.Iz, F z) * Real.sqrt (∫ z in Work.Spaces.Iz, G z) :=
        Work.FTS.IPGen.cs_sqrt_le hFint hGint hFnn hGnn
    _ = Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := by
        rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, Work.Spaces.HkSq, Work.Spaces.HkSq, hF, hG]

/-! ## The pointwise slot domination, in general order -/

/-- **The pointwise slot domination of a leaf weight, in general order.**  For the slot `(a,b)`
with `a + b ≤ n` and any leaf weight `ρ` attached to `a`, the weight times the square of the
slot of `h` is dominated by the `ℋ^n`-integrand of `h` at every point with `z ∈ Iz`,
`θ ∈ (0,π/2)`:

  `ρ z θ · (D_z^bD_θ^a h z θ)² ≤ HkIntegrand α n h z θ`.

This is `Work.FTS.IPGen.leaf_dom` with `4` replaced by `n`. -/
theorem leaf_dom_gen {α : ℝ} (hα : 0 < α) {a b n : ℕ} (hab : a + b ≤ n)
    {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) (h : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ρ z θ * (Work.Spaces.mixed b a h z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α n h z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσ : 0 ≤ Real.sin (2 * θ) := Work.FTS.H2.sin_two_nonneg_of_mem_Iθ hθI
  rcases hρ with rfl | rfl | ⟨ha, rfl⟩
  · -- `ρ = leafEta = Whz²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ n := by omega
      have hkey : Work.FTS.TransportS.leafEta z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by
        rw [Work.FTS.TransportS.leafEta, ← Work.FTS.H2.hbi_Whz_sq z θ hσ]
        ring
      rw [hkey]
      exact Work.Spaces.sq_le_HkIntegrand_z α n h z θ b hb
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
        _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α n h z θ a b h1 (by omega)
  · -- `ρ = leafOne = 1²`
    rcases eq_or_ne a 0 with h0 | h0
    · subst h0
      rw [Work.Spaces.mixed_zero_right]
      have hb : b ≤ n := by omega
      have hle : Work.FTS.TransportS.leafOne z θ ≤ Work.FTS.H2.Whz z θ ^ 2 := by
        rw [Work.FTS.TransportS.leafOne, Work.FTS.H2.hbi_Whz_sq z θ hσ]
        exact le_mul_of_one_le_right (sq_nonneg _)
          (Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ)
      calc Work.FTS.TransportS.leafOne z θ * (Work.Spaces.DzIter b h z θ) ^ 2
          ≤ Work.FTS.H2.Whz z θ ^ 2 * (Work.Spaces.DzIter b h z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Work.Spaces.DzIter b h z θ * Work.FTS.H2.Whz z θ) ^ 2 := by ring
        _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
            Work.Spaces.sq_le_HkIntegrand_z α n h z θ b hb
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
        _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
            Work.Spaces.sq_le_HkIntegrand_mixed α n h z θ a b h1 (by omega)
  · -- `ρ = leafGam α = Wm²`, only at slots with `a ≥ 1`
    have hWm := Work.FTS.H2.hbi_Wm_sq α z θ hσ
    simp only [Work.FTS.H2.Wm] at hWm
    have hle : Work.FTS.TransportS.leafGam α z θ = Work.Spaces.Wt α z θ ^ 2 := by
      rw [Work.FTS.TransportS.leafGam, ← hWm]
    calc Work.FTS.TransportS.leafGam α z θ * (Work.Spaces.mixed b a h z θ) ^ 2
        = Work.Spaces.Wt α z θ ^ 2 * (Work.Spaces.mixed b a h z θ) ^ 2 := by rw [hle]
      _ = (Work.Spaces.mixed b a h z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ Work.Spaces.HkIntegrand α n h z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α n h z θ a b ha (by omega)

/-! ## The requested general-order per-slot bound -/

theorem slotPairing_abs_le_gen {α : ℝ} (hα : 0 < α) {a b n : ℕ} (hab : a + b ≤ n) {ρ : ℝ → ℝ → ℝ} (hρ : Work.FTS.TransportS.IsLeafW α a ρ) {f g : Work.FTS.Galerkin.Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmf : Work.Spaces.HkMem α n f) (hmg : Work.Spaces.HkMem α n g) : |Work.FTS.TransportS.slotPairing ρ a b f g| ≤ Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g := by
  have hmain : |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      ρ z θ * Work.Spaces.mixed b a f z θ * Work.Spaces.mixed b a g z θ|
      ≤ Work.Spaces.HkNorm α n f * Work.Spaces.HkNorm α n g :=
    cs_slotInt_abs_le_gen hmf hmg (Work.FTS.IPGen.leaf_nonneg hρ)
      (fun z hz θ hθ => leaf_dom_gen hα hab hρ f hz hθ)
      (fun z hz θ hθ => leaf_dom_gen hα hab hρ g hz hθ)
  rw [Work.FTS.TransportS.slotPairing]
  exact hmain

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
