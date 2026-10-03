import Mathlib
import Submission.Work.Peluse.LadderP.stepPCore

namespace Work.Peluse.LadderP

/-- The non-degeneracy comparison `nondegLeOfCore`: with `η = cη γ^{2 e₅₁}`, the core inequality
`C uᵉ ≤ C₅₁ cη^{e₅₁} γ^{(1+2 e₅₁)e₅₁}` and the non-degeneracy hypothesis
`(M₁L)ᵉ ≤ C (uD)ᵉ L` give `(M₁L)^{e₅₁} ≤ C₅₁ (γηD)^{e₅₁} L`.

The point is that `e₅₁ ≤ e` (a *smaller* exponent on the left) can be handled because
`D ≤ M₁L` lets one trade `D^{e-e₅₁}` for `(M₁L)^{e-e₅₁}`; the prefactor
`A := C₅₁ (γη)^{e₅₁}` is shown to be non-negative for free, since a negative `A` would force
`(M₁L)ᵉ ≤ 0 < (M₁L)ᵉ` from the two hypotheses. -/
theorem nondegLeOfCore (j n M₁ : ℕ) (L D : ℕ) {u γ η C C₅₁ cη : ℝ} {e e₅₁ : ℕ}
    (hM₁ : 1 ≤ M₁) (hC₅₁ : 0 < C₅₁) (he₅₁ : 1 ≤ e₅₁) (he : e₅₁ ≤ e) (hL1 : 1 ≤ L)
    (hη : η = cη * γ ^ (2 * e₅₁))
    (hcore : C * u ^ e ≤ C₅₁ * cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁))
    (hDle : (D : ℝ) ≤ (M₁ : ℝ) * (L : ℝ))
    (hnondeg : ((M₁ : ℝ) * (L : ℝ)) ^ e ≤ C * (u * (D : ℝ)) ^ e * (L : ℝ)) :
    ((M₁ : ℝ) * (L : ℝ)) ^ e₅₁ ≤ C₅₁ * (γ * η * (D : ℝ)) ^ e₅₁ * (L : ℝ) := by
  set S : ℝ := (M₁ : ℝ) * (L : ℝ) with hS
  set A : ℝ := C₅₁ * (γ * η) ^ e₅₁ with hA
  have hS1 : (1 : ℝ) ≤ S := by
    rw [hS]
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hM₁) (by exact_mod_cast hL1)
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS1
  have hDnn : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := by positivity
  have hDpow : (0 : ℝ) ≤ (D : ℝ) ^ e := pow_nonneg hDnn e
  -- the `η`-rewriting: `(γ η)^{e₅₁} = cη^{e₅₁} γ^{(1+2e₅₁)e₅₁}`
  have hγη : (γ * η) ^ e₅₁ = cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁) := by
    calc (γ * η) ^ e₅₁
        = γ ^ e₅₁ * η ^ e₅₁ := by rw [mul_pow]
      _ = γ ^ e₅₁ * (cη * γ ^ (2 * e₅₁)) ^ e₅₁ := by rw [hη]
      _ = γ ^ e₅₁ * (cη ^ e₅₁ * (γ ^ (2 * e₅₁)) ^ e₅₁) := by rw [mul_pow]
      _ = γ ^ e₅₁ * (cη ^ e₅₁ * γ ^ (2 * e₅₁ * e₅₁)) := by rw [← pow_mul]
      _ = cη ^ e₅₁ * (γ ^ e₅₁ * γ ^ (2 * e₅₁ * e₅₁)) := by ring
      _ = cη ^ e₅₁ * γ ^ (e₅₁ + 2 * e₅₁ * e₅₁) := by rw [pow_add]
      _ = cη ^ e₅₁ * γ ^ ((1 + 2 * e₅₁) * e₅₁) := by
            have hexp : e₅₁ + 2 * e₅₁ * e₅₁ = (1 + 2 * e₅₁) * e₅₁ := by ring
            rw [hexp]
  have hcore' : C * u ^ e ≤ A := by
    rw [hA, hγη]
    simpa only [mul_assoc] using hcore
  have hnondeg' : S ^ e ≤ C * u ^ e * (D : ℝ) ^ e * (L : ℝ) := by
    calc S ^ e ≤ C * (u * (D : ℝ)) ^ e * (L : ℝ) := hnondeg
      _ = C * u ^ e * (D : ℝ) ^ e * (L : ℝ) := by rw [mul_pow]; ring
  have hDL : (D : ℝ) ≤ S := hDle
  have hstep1 : C * u ^ e * (D : ℝ) ^ e ≤ A * (D : ℝ) ^ e :=
    mul_le_mul_of_nonneg_right hcore' hDpow
  have hstep2 : C * u ^ e * (D : ℝ) ^ e * (L : ℝ) ≤ A * (D : ℝ) ^ e * (L : ℝ) :=
    mul_le_mul_of_nonneg_right hstep1 hLnn
  -- the prefactor `A` is automatically non-negative
  have hA0 : 0 ≤ A := by
    by_contra hneg
    have hneg' : A < 0 := not_le.mp hneg
    have h3 : A * (D : ℝ) ^ e * (L : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg') hDpow) hLnn
    have h5 : S ^ e ≤ 0 := le_trans hnondeg' (le_trans hstep2 h3)
    have h6 : 0 < S ^ e := pow_pos hSpos e
    linarith
  have heq : e = e₅₁ + (e - e₅₁) := by omega
  have heq2 : e = (e - e₅₁) + e₅₁ := by omega
  have hSpow : S ^ e = S ^ e₅₁ * S ^ (e - e₅₁) := by
    conv_lhs => rw [heq]
    rw [pow_add]
  have hDpowE : (D : ℝ) ^ e = (D : ℝ) ^ (e - e₅₁) * (D : ℝ) ^ e₅₁ := by
    conv_lhs => rw [heq2]
    rw [pow_add]
  -- `D^{e-e₅₁} ≤ S^{e-e₅₁}` is the only place `D ≤ M₁L` is used
  have hDse : (D : ℝ) ^ (e - e₅₁) ≤ S ^ (e - e₅₁) := pow_le_pow_left₀ hDnn hDL (e - e₅₁)
  have hDleS : (D : ℝ) ^ e ≤ S ^ (e - e₅₁) * (D : ℝ) ^ e₅₁ := by
    rw [hDpowE]
    exact mul_le_mul_of_nonneg_right hDse (pow_nonneg hDnn e₅₁)
  have hAD : A * (D : ℝ) ^ e * (L : ℝ) ≤ (A * (D : ℝ) ^ e₅₁ * (L : ℝ)) * S ^ (e - e₅₁) := by
    have h1 : A * (D : ℝ) ^ e ≤ A * (S ^ (e - e₅₁) * (D : ℝ) ^ e₅₁) :=
      mul_le_mul_of_nonneg_left hDleS hA0
    have h2 : A * (D : ℝ) ^ e * (L : ℝ) ≤ A * (S ^ (e - e₅₁) * (D : ℝ) ^ e₅₁) * (L : ℝ) :=
      mul_le_mul_of_nonneg_right h1 hLnn
    calc A * (D : ℝ) ^ e * (L : ℝ)
        ≤ A * (S ^ (e - e₅₁) * (D : ℝ) ^ e₅₁) * (L : ℝ) := h2
      _ = (A * (D : ℝ) ^ e₅₁ * (L : ℝ)) * S ^ (e - e₅₁) := by ring
  have hchain : S ^ e ≤ (A * (D : ℝ) ^ e₅₁ * (L : ℝ)) * S ^ (e - e₅₁) :=
    le_trans hnondeg' (le_trans hstep2 hAD)
  have hSpos' : 0 < S ^ (e - e₅₁) := pow_pos hSpos _
  have hkey : S ^ e₅₁ * S ^ (e - e₅₁) ≤ (A * (D : ℝ) ^ e₅₁ * (L : ℝ)) * S ^ (e - e₅₁) := by
    rw [← hSpow]; exact hchain
  have hres : S ^ e₅₁ ≤ A * (D : ℝ) ^ e₅₁ * (L : ℝ) := le_of_mul_le_mul_right hkey hSpos'
  calc S ^ e₅₁ ≤ A * (D : ℝ) ^ e₅₁ * (L : ℝ) := hres
    _ = C₅₁ * (γ * η * (D : ℝ)) ^ e₅₁ * (L : ℝ) := by rw [hA, mul_pow]; ring

end Work.Peluse.LadderP
