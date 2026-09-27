import Mathlib
import Submission.Work.Drive.N2.windowDatum

/-!
# The model parameters of the saddle packet (D2 core)

The two model parameters of the saddle window, with the conventions of
`N2Lead/NOTES_LEAD_saddlePacket.md` §0: with `lam0 = ρ_j / 8` the value multiplier of the scaled
Morse coordinate is `lam := lam0²`, and

* `packetEta D η = 3η / (2 λ)` is the *model* half-height `ηs`, so that `λ · ηs = 3η/2`: the anchor
  level `f p - 3η/2` corresponds to `Re (Z ·)² = -ηs`;
* `packetEtaB D η = 2η / λ = 4 ηs / 3` is the half-width of the widened band, so that
  `λ · ηb = 2η`.

These are the constants with which the whole D2 core (`Work.Drive.N2.saddleCertifiedWindowOneComp`)
is stated; they live in their own module so that the lemmas of the core can be stated without
importing the core's target.

They are definitionally the `packetEta`/`packetEtaB` of the core file.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff

/-- **The model parameter of the saddle window**: `ηs` with `lam * ηs = 3 η / 2`, where
`lam = (ρ j / 8)²` is the value multiplier of the scaled Morse coordinate. -/
noncomputable def packetEta {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) (η : ℝ) : ℝ :=
  3 * η / (2 * (D.ρ D.j / 8) ^ 2)

/-- The half-width of the widened band: `2 η / lam`. -/
noncomputable def packetEtaB {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) (η : ℝ) : ℝ :=
  2 * η / (D.ρ D.j / 8) ^ 2

lemma packetEta_pos {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) {η : ℝ} (hη : 0 < η) :
    0 < packetEta D η := by
  rw [packetEta]
  have hρ := D.hρ D.j
  positivity

lemma packetEtaB_pos {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) {η : ℝ} (hη : 0 < η) :
    0 < packetEtaB D η := by
  rw [packetEtaB]
  have hρ := D.hρ D.j
  positivity

/-- `ηb = 4 ηs / 3`: the widened band is `4/3` times the model band. -/
lemma packetEtaB_eq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) (η : ℝ) :
    packetEtaB D η = 4 * packetEta D η / 3 := by
  rw [packetEta, packetEtaB]
  have hρ := D.hρ D.j
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  have h : (D.ρ D.j / 8) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The normalisation law `λ · ηs = 3 η / 2`. -/
lemma packetEta_law {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) (η : ℝ) :
    (D.ρ D.j / 8) ^ 2 * packetEta D η = 3 * η / 2 := by
  rw [packetEta]
  have hρ := D.hρ D.j
  have h : (D.ρ D.j / 8) ^ 2 ≠ 0 := by positivity
  field_simp

/-- The band law `λ · ηb = 2 η`. -/
lemma packetEtaB_law {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    {f : M → ℝ} {p : M} (D : WindowDatum f p) (η : ℝ) :
    (D.ρ D.j / 8) ^ 2 * packetEtaB D η = 2 * η := by
  rw [packetEtaB]
  have hρ := D.hρ D.j
  have h : (D.ρ D.j / 8) ^ 2 ≠ 0 := by positivity
  field_simp

end Work.Drive.N2
