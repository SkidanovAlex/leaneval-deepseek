import ChallengeDeps
import Submission.ChiWitness
import Submission.RadialEven
import Submission.ScatGChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, brick B8 — the chosen scattering kernel data (packaged)

Instantiation layer: with `h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`
(the `a v ≠ 0` branch of the box bound) and `w₀ := Classical.choose h`, the
scattering numerator

    g₀(x) := v x·(1 − w₀ x),        g₂(x) := g₀(x)·(1 + w₀ x) = v(1−w₀)(1+w₀)

is packaged with everything the kernel calculus (`Submission.KernelIds`,
`Submission.ConvChiBound`, `Submission.LocPotential`,
`Submission.ConvolutionTaylor`) and the eventual box identities need:

  * integrability (`ScatG.scatG_integrable`, `ScatGIntegrals.scat_gomega_integrable`);
  * evenness (`Submission.RadialEven` — radial `v`, `w₀` ⟹ `g₀`, `g₂` even);
  * support (`g₀ x = g₂ x = 0` for `R ≤ ‖x‖`);
  * mass (`∫g₀ = 8π·a v`; `8πa v ≤ ∫g₂ ≤ 16πa v`);
  * nonnegativity a.e. (`g₀ ≥ 0`, `g₂ ≥ 0` a.e.);
  * the **box identities** eq:DefU / eq:w2int instantiated with the global
    witness `chiR0` (`Submission.ChiWitness`):

        (1/2)·ℓ^(-6:ℤ)·∫∫ χ_ℓ(x)χ_ℓ(y)·(g₀(x−y)/C_ℓ(x−y)) dxdy
            = (1/2)·ℓ^(-3:ℤ)·∫g₀ = 4π·(a v)·ℓ^(-3)
        (1/2)·ℓ^(-6:ℤ)·∫∫ χ_ℓ(x)χ_ℓ(y)·(g₂(x−y)/C_ℓ(x−y)) dxdy
            = (1/2)·ℓ^(-3:ℤ)·∫g₂

valid once `0 < ℓ` and `R ≤ ℓ·chiR0` (the dilute regime).
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real Convolution

namespace Submission.BoseGases

set_option autoImplicit false

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `g₀ := v(1−w₀)` with `w₀ := Classical.choose h`. -/
noncomputable def g0 (v : ℝ³ → ℝ) (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (x : ℝ³) : ℝ := v x * (1 - Classical.choose h x)

/-- `g₂ := g₀(1+w₀) = v(1−w₀)(1+w₀)`. -/
noncomputable def g2 (v : ℝ³ → ℝ) (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (x : ℝ³) : ℝ := (v x * (1 - Classical.choose h x)) * (1 + Classical.choose h x)

/-- `w₀ := Classical.choose h` is radial and is a scattering solution. -/
theorem w0_spec {v : ℝ³ → ℝ} (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    IsRadial (Classical.choose h) ∧ IsScatteringSolution (Classical.choose h) v := by
  exact Classical.choose_spec h

/-- `g₀` is integrable. -/
theorem g0_integrable {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    MeasureTheory.Integrable (g0 v h) := by
  have hw₀ : IsScatteringSolution (Classical.choose h) v := (Classical.choose_spec h).2
  change MeasureTheory.Integrable (fun x : ℝ³ => v x * (1 - (Classical.choose h) x))
  exact scatG_integrable hv_supp hw₀

/-- `g₀·w₀` is integrable. -/
theorem g0w0_integrable {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    MeasureTheory.Integrable (fun x : ℝ³ => (g0 v h x) * Classical.choose h x) := by
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  have hGw : MeasureTheory.Integrable
      (fun x : ℝ³ => (v x * (1 - (Classical.choose h) x)) * (Classical.choose h) x) :=
    scat_gomega_integrable hv_nonneg hvrad hv_supp hrad₀ hw₀
  simpa [g0] using hGw

/-- `g₂` is integrable (as the sum `g₀ + g₀w₀`). -/
theorem g2_integrable {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    MeasureTheory.Integrable (g2 v h) := by
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  have hG : MeasureTheory.Integrable (fun x : ℝ³ => v x * (1 - (Classical.choose h) x)) :=
    scatG_integrable hv_supp hw₀
  have hGw : MeasureTheory.Integrable
      (fun x : ℝ³ => (v x * (1 - (Classical.choose h) x)) * (Classical.choose h) x) :=
    scat_gomega_integrable hv_nonneg hvrad hv_supp hrad₀ hw₀
  have hG2 : MeasureTheory.Integrable
      (fun x : ℝ³ => (v x * (1 - (Classical.choose h) x)) * (1 + (Classical.choose h) x)) := by
    have hEq : (fun x : ℝ³ => (v x * (1 - (Classical.choose h) x)) * (1 + (Classical.choose h) x))
        = fun x : ℝ³ => v x * (1 - (Classical.choose h) x)
            + (v x * (1 - (Classical.choose h) x)) * (Classical.choose h) x := by
      funext x
      ring
    rw [hEq]
    exact hG.add hGw
  change MeasureTheory.Integrable
      (fun x : ℝ³ => (v x * (1 - (Classical.choose h) x)) * (1 + (Classical.choose h) x))
  exact hG2

/-- `g₀` is even. -/
theorem g0_even {v : ℝ³ → ℝ} (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ x : ℝ³, g0 v h (-x) = g0 v h x := by
  have hrad₀ : IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  intro x
  exact scat_g_even (w := Classical.choose h) hvrad hrad₀ x

/-- `g₂` is even. -/
theorem g2_even {v : ℝ³ → ℝ} (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ x : ℝ³, g2 v h (-x) = g2 v h x := by
  have hrad₀ : IsRadial (Classical.choose h) := (Classical.choose_spec h).1
  intro x
  have hve : v (-x) = v x := radial_neg hvrad x
  have hwe : (Classical.choose h) (-x) = (Classical.choose h) x := radial_neg hrad₀ x
  simp [g2, hve, hwe]

/-- `g₀` vanishes outside `ball 0 R`. -/
theorem g0_zero_of_norm_ge {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {x : ℝ³} (hx : R ≤ ‖x‖)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    g0 v h x = 0 := by
  simpa [g0] using scat_g_zero_of_norm_ge (w := Classical.choose h) hv_supp hx

/-- `g₂` vanishes outside `ball 0 R`. -/
theorem g2_zero_of_norm_ge {v : ℝ³ → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) {x : ℝ³} (hx : R ≤ ‖x‖)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    g2 v h x = 0 := by
  simpa [g2, g0] using scat_g1pw_zero_of_norm_ge (w := Classical.choose h) hv_supp hx

/-- **Mass of `g₀`**: `∫g₀ = 8π·a v`. -/
theorem g0_integral {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    (∫ x : ℝ³, g0 v h x) = 8 * π * a v := by
  simpa [g0] using chosen_scattering_integral (v := v) h

/-- **Mass bounds of `g₂`**: `8πa v ≤ ∫g₂ ≤ 16πa v`. -/
theorem g2_integral_bounds {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    8 * π * a v ≤ (∫ x : ℝ³, g2 v h x) ∧
      (∫ x : ℝ³, g2 v h x) ≤ 16 * π * a v := by
  simpa [g2, g0] using
    (chosen_g1pomega_integral_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h)

/-- `0 ≤ g₀` a.e. (from `0 ≤ v` and `w₀ ≤ 1` a.e.). -/
theorem g0_nonneg_ae {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ᵐ x : ℝ³, 0 ≤ g0 v h x := by
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  have hg := scattering_g_nonneg (w := Classical.choose h) hR hv_nonneg hvrad hv_supp hrad₀ hw₀
  filter_upwards [hg] with x hx
  simpa [g0] using hx

/-- `0 ≤ g₂` a.e. -/
theorem g2_nonneg_ae {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ᵐ x : ℝ³, 0 ≤ g2 v h x := by
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial (Classical.choose h) := hspec.1
  have hw₀ : IsScatteringSolution (Classical.choose h) v := hspec.2
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hrad₀ hw₀
  have hg0 := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  filter_upwards [hg0, hb.1] with x hx0 hw0
  dsimp [g2]
  exact mul_nonneg (by simpa [g0] using hx0) (by linarith)

/-- Bounds on the scattering length in the chosen branch: `0 ≤ a v ≤ R`;
combine with `a v ≠ 0` for `0 < a v`. -/
theorem av_bounds_weak {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    0 ≤ a v ∧ a v ≤ R := by
  exact chosen_av_bounds_weak hR hv_nonneg hvrad hv_supp h

/-- **eq:DefU in chosen form**: `(1/2)ℓ^(-6:ℤ)∫∫χ_ℓχ_ℓ·(g₀/C_ℓ) =
(1/2)ℓ^(-3:ℤ)·∫g₀ = 4π(a v)ℓ^(-3)`, for `0 < ℓ` and `R ≤ ℓ·chiR0`. -/
theorem kernel_box_g0 {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (1 / 2) * ℓ ^ (-6 : ℤ) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          chiScale ℓ x * chiScale ℓ y * (g0 v h (x - y) / convScale ℓ (x - y))) =
      (1 / 2) * ℓ ^ (-3 : ℤ) * (8 * π * a v) := by
  have hsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g0 v h x = 0 := by
    intro x hx
    exact g0_zero_of_norm_ge hv_supp hx h
  have hmain := eq_DefU_norm (h := g0 v h) (ℓ := ℓ) (R := R) (r₀ := chiR0) hℓ
    (g0_integrable hR hv_supp h) hsupp chiR0_pos hRℓ chiR0_half
  rw [hmain]
  rw [g0_integral hR hv_supp h]

/-- **eq:w2int in chosen form**: with `g₂ = g₀(1+w₀)`,
`(1/2)ℓ^(-6:ℤ)∫∫χ_ℓχ_ℓ·(g₂/C_ℓ) = (1/2)ℓ^(-3:ℤ)·∫g₂`. -/
theorem kernel_box_g2 {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    (1 / 2) * ℓ ^ (-6 : ℤ) *
        (∫ x : ℝ³, ∫ y : ℝ³,
          chiScale ℓ x * chiScale ℓ y * (g2 v h (x - y) / convScale ℓ (x - y))) =
      (1 / 2) * ℓ ^ (-3 : ℤ) * (∫ z : ℝ³, g2 v h z) := by
  have hsupp : ∀ x : ℝ³, R ≤ ‖x‖ → g2 v h x = 0 := by
    intro x hx
    exact g2_zero_of_norm_ge hv_supp hx h
  exact eq_DefU_norm (h := g2 v h) (ℓ := ℓ) (R := R) (r₀ := chiR0) hℓ
    (g2_integrable hR hv_nonneg hvrad hv_supp h) hsupp chiR0_pos hRℓ chiR0_half

end BoseGases

end Submission
