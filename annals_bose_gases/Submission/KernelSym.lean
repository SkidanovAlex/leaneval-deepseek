import ChallengeDeps
import Submission.ScatKernelChosen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — symmetry of the χ-renormalized kernels and ω

The corpus-native potsplit (`Submission.PotWords.potsplit_expect`) requires the
kernels `w(x,y) = w(y,x)` and `ω(x,y) = ω(y,x)` to be symmetric.  For the
chosen-branch kernels `wPair(ℓ,h)(x,y) = χ_ℓ(x)χ_ℓ(y)h(x−y)/C_ℓ(x−y)` this
holds when the numerator `h` is even (`χ`, `C` are even: `KernelIds`); the
numerator potentials `v` (radial), `g₀`, `g₂` are even.  `ω(x,y) := w₀(x−y)`
is symmetric when the scattering solution `w₀` is even (radial).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Curried `wPair`. -/
noncomputable def wPairC (ℓ : ℝ) (h : ℝ³ → ℝ) (x y : ℝ³) : ℝ := wPair ℓ h x y

/-- `ω(x,y) := w₀(x−y)`. -/
noncomputable def omC (w0 : ℝ³ → ℝ) (x y : ℝ³) : ℝ := w0 (x - y)

/-- `convScale` is even. -/
lemma convScale_symm (ℓ : ℝ) (x : ℝ³) : convScale ℓ (-x) = convScale ℓ x := by
  unfold convScale
  rw [show (ℓ⁻¹) • (-x) = -((ℓ⁻¹) • x) by simp [smul_neg]]
  exact conv3chi_even ((ℓ⁻¹) • x)

/-- `wPairC ℓ h` is symmetric when the numerator `h` is even. -/
lemma wPairC_sym {h : ℝ³ → ℝ} (hh : ∀ z : ℝ³, h (-z) = h z) (ℓ : ℝ) :
    ∀ x y : ℝ³, wPairC ℓ h x y = wPairC ℓ h y x := by
  intro x y
  unfold wPairC wPair wScaled
  have hh' : h (y - x) = h (x - y) := by
    rw [show y - x = -(x - y) by abel]
    exact hh (x - y)
  have hC : convScale ℓ (y - x) = convScale ℓ (x - y) := by
    rw [show y - x = -(x - y) by abel]
    exact convScale_symm ℓ (x - y)
  have hchi : chiScale ℓ x * chiScale ℓ y = chiScale ℓ y * chiScale ℓ x := by ring
  rw [hh', hC]
  rw [mul_assoc, mul_assoc]
  ring

/-- `omC w0` is symmetric when `w0` is even. -/
lemma omC_sym {w0 : ℝ³ → ℝ} (hw0 : ∀ z : ℝ³, w0 (-z) = w0 z) :
    ∀ x y : ℝ³, omC w0 x y = omC w0 y x := by
  intro x y
  unfold omC
  rw [show y - x = -(x - y) by abel, hw0]

/-- Symmetry of the chosen-branch kernel `wPair(ℓ,v)` (radial `v`). -/
lemma wPairC_v_sym {v : ℝ³ → ℝ} (hvrad : IsRadial v) (ℓ : ℝ) :
    ∀ x y : ℝ³, wPairC ℓ v x y = wPairC ℓ v y x :=
  wPairC_sym (radial_even hvrad) ℓ

/-- Symmetry of `wPair(ℓ,g₀)`. -/
lemma wPairC_g0_sym {v : ℝ³ → ℝ} (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) :
    ∀ x y : ℝ³, wPairC ℓ (g0 v h) x y = wPairC ℓ (g0 v h) y x := by
  apply wPairC_sym
  intro z
  exact g0_even hvrad h z

/-- Symmetry of `wPair(ℓ,g₂)`. -/
lemma wPairC_g2_sym {v : ℝ³ → ℝ} (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) :
    ∀ x y : ℝ³, wPairC ℓ (g2 v h) x y = wPairC ℓ (g2 v h) y x := by
  apply wPairC_sym
  intro z
  exact g2_even hvrad h z

/-- Symmetry of `ω(x,y) := w₀(x−y)` for the radial chosen solution `w₀`. -/
lemma omC_chosen_sym {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    ∀ x y : ℝ³, omC (Classical.choose h) x y = omC (Classical.choose h) y x := by
  apply omC_sym
  intro z
  exact radial_neg (w0_spec h).1 z

end BoseGases

end Submission
