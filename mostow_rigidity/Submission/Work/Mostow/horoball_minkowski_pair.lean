import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.BaryBase

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- **Timelike orthogonal complement is spacelike.**  If `w` is Minkowski-orthogonal to the
hyperboloid point `x = hlift z` (so `⟨x,x⟩ = -1`), then `⟨w,w⟩ ≥ 0`.

In coordinates `w = (w_s, w₀)` the relation `⟨x,w⟩ = 0` reads `⟪z,w_s⟫ = (tpart z)·w₀`, whence
`w₀ = ⟪z,w_s⟫/tpart z` and
`⟨w,w⟩ = ‖w_s‖² - w₀² ≥ ‖w_s‖²(1 - ‖z‖²/(tpart z)²) = ‖w_s‖²/(tpart z)² ≥ 0`. -/
lemma mform_nonneg_of_mform_hlift_eq_zero (z : E n) (w : Fin n ⊕ Fin 1 → ℝ)
    (hw : mform (hlift z) w = 0) : 0 ≤ mform w w := by
  have hT : 0 < tpart z := tpart_pos z
  have hT2 : tpart z ^ 2 = 1 + ‖z‖ ^ 2 := tpart_sq z
  have h1 : mform (hlift z) w = inner ℝ z (hspat w) - tpart z * htime w := by
    rw [mform_eq]; simp
  rw [h1] at hw
  have hw0' : htime w = inner ℝ z (hspat w) / tpart z :=
    (eq_div_iff (ne_of_gt hT)).2 (by linarith)
  rw [mform_eq, real_inner_self_eq_norm_sq, hw0']
  have hsq : inner ℝ z (hspat w) / tpart z * (inner ℝ z (hspat w) / tpart z)
      = (inner ℝ z (hspat w)) ^ 2 / tpart z ^ 2 := by
    rw [← pow_two, div_pow]
  rw [hsq]
  have hcs : (inner ℝ z (hspat w)) ^ 2 ≤ ‖z‖ ^ 2 * ‖hspat w‖ ^ 2 := by
    have h := abs_real_inner_le_norm z (hspat w)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rwa [sq_abs, mul_pow] at h2
  have hkey : (inner ℝ z (hspat w)) ^ 2 ≤ ‖hspat w‖ ^ 2 * tpart z ^ 2 := by
    nlinarith [hcs, hT2, sq_nonneg ‖hspat w‖]
  rw [sub_nonneg, div_le_iff₀ (by positivity : (0:ℝ) < tpart z ^ 2)]
  linarith

-- Route: `tpart z - ⟪z,ξ⟫ = exp (busemann ξ z)` (and likewise for η), so the claim is
-- `exp (β_ξ z + β_η z) ≥ (1 - ⟪ξ,η⟫)/2`.  In Minkowski form: `x = hlift z` (⟨x,x⟩ = -1),
-- `θ = theta ξ`, `θ' = theta η` are null, `A := -⟨x,θ⟩`, `B := -⟨x,θ'⟩`, `⟨θ,θ'⟩ = ⟪ξ,η⟫ - 1`.
-- Put `u := A⁻¹ • θ + B⁻¹ • θ'`; then `⟨x,u⟩ = -2`, so `w := x - 2⁻¹ • u` satisfies `⟨x,w⟩ = 0` and
-- `⟨w,w⟩ = -1 + 2 + ⟨u,u⟩/4 = 1 + ⟨θ,θ'⟩/(2AB)`.  A vector `w` with `⟨x,w⟩ = 0` and `x` timelike has
-- `⟨w,w⟩ ≥ 0` (coordinate proof via `mform_eq`, `hspat_hlift'`, `htime_hlift'`:
-- `0 = ⟨x,w⟩ = ⟪z,w_s⟫ - (tpart z)*w₀` gives `w₀ = ⟪z,w_s⟫/tpart z`, hence
-- `⟨w,w⟩ = ‖w_s‖² - w₀² ≥ ‖w_s‖²(1 - ‖z‖²/(tpart z)²) ≥ 0`).  So `2AB ≥ -⟨θ,θ'⟩ = 1 - ⟪ξ,η⟫`.
-- The toolkit (`mform`, `theta`, `hlift`, `mform_eq`, `mform_hlift_theta'`, `mform_theta_theta'`,
-- `mform_hlift_self`, bilinearity lemmas) is in `Submission.Work.Mostow.poAux` / `StabHoroForm`.
theorem horoball_minkowski_pair (n : ℕ) (ξ η : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n) (z : Submission.Mostow.E n) : (1 - inner ℝ ξ η) / 2 ≤ (Submission.Mostow.tpart z - inner ℝ z ξ) * (Submission.Mostow.tpart z - inner ℝ z η) := by
  set A := tpart z - inner ℝ z ξ with hA
  set B := tpart z - inner ℝ z η with hB
  have hApos : 0 < A := busemann_arg_pos ξ hξ z
  have hBpos : 0 < B := busemann_arg_pos η hη z
  set x := hlift z with hx
  set θ := theta ξ with hθ
  set θ' := theta η with hθ'
  have hmxθ : mform x θ = -A := by
    rw [hx, hθ, hA, mform_hlift_theta']; ring
  have hmxθ' : mform x θ' = -B := by
    rw [hx, hθ', hB, mform_hlift_theta']; ring
  have hθθ : mform θ θ = 0 := by rw [hθ]; exact mform_theta_theta_sph ξ hξ
  have hθ'θ' : mform θ' θ' = 0 := by rw [hθ']; exact mform_theta_theta_sph η hη
  have hθθ' : mform θ θ' = inner ℝ ξ η - 1 := by rw [hθ, hθ', mform_eq]; simp
  have hθ'θ : mform θ' θ = inner ℝ ξ η - 1 := by rw [mform_comm]; exact hθθ'
  set u := A⁻¹ • θ + B⁻¹ • θ' with hu
  have hxu : mform x u = -2 := by
    simp only [hu, mform_add_right, mform_smul_right, hmxθ, hmxθ']
    field_simp
    ring
  have hux : mform u x = -2 := by rw [mform_comm]; exact hxu
  have huu : mform u u = 2 * (A * B)⁻¹ * (inner ℝ ξ η - 1) := by
    simp only [hu, mform_add_left, mform_add_right, mform_smul_left, mform_smul_right, hθθ,
      hθ'θ', hθθ', hθ'θ]
    ring_nf
  have hxself : mform x x = -1 := by rw [hx]; exact mform_hlift_self z
  have hww : mform (x - (1/2:ℝ) • u) (x - (1/2:ℝ) • u) = 1 + mform θ θ' / (2*A*B) := by
    simp only [mform_sub_left, mform_sub_right, mform_smul_left, mform_smul_right, hxself, hxu,
      hux, huu, hθθ']
    field_simp
    ring
  have hnonneg : 0 ≤ mform (x - (1/2:ℝ) • u) (x - (1/2:ℝ) • u) := by
    apply mform_nonneg_of_mform_hlift_eq_zero z
    rw [← hx]
    simp only [mform_sub_right, mform_smul_right, hxu, hxself]
    ring
  rw [hww] at hnonneg
  have h2 : 1 - inner ℝ ξ η ≤ 2 * A * B := by
    rw [hθθ'] at hnonneg
    have hpos2 : 0 < 2 * A * B := by positivity
    have h := (le_div_iff₀ hpos2).mp (by linarith : (-1:ℝ) ≤ (inner ℝ ξ η - 1) / (2 * A * B))
    linarith
  linarith

end

end Work.Mostow
