import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.norm_one_sub_exp_two_pi_I_lower
import Submission.Work.Pert.I_mul_half_eta_mem_Qm

/-!
# PERT · `exists_tauC_gate_ge_fixed`: the gate point where `τ_f` is large, with the missing
hypothesis supplied

The statement requested as `Work.Pert.exists_tauC_gate_ge` is **false** as it stands: its
hypotheses do not relate `‖σ‖` to `‖α‖`, and `hnorm` ties `‖σ‖` to `‖1 - exp (2πi α)‖`, which can
be arbitrarily small compared with `‖α‖` when `α` is close to a non-zero integer — compatible with
`MandelDim.InF1 α` and `‖α‖ η ≤ 1/1024`.  Counterexample (found and checked numerically):

`u ≡ 2`, `α = 900 + 300 i`, `ξ₁ = 4·10⁻⁷`, `η = 10⁻⁶`, `σ = (1 - exp (2πi α))/2` (so
`‖σ‖ = (1 - e^{-600π})/2 < 1/2`, `‖u 0‖ = 2 ∈ [1/2,2]`, `‖α‖ η ≈ 9.49·10⁻⁴ ≤ 1/1024`,
`2ξ₁ = 8·10⁻⁷ < η`, `InF1 α` since `300 < 900`).  The conclusion would require a point
`z ∈ Qm ξ₁ α` with `‖1 - exp (-2πi α z)‖ ≤ 4η‖σ‖ ≤ 2·10⁻⁶`.  But `Work.Pert.scale_lattice`
(proved, sorry-free) shows that every `z ∈ Qm ξ₁ α` satisfies `‖z - k/α‖ ≥ ξ₁/2` for all
`k : ℤ`, so `‖1 - exp (-2πi α z)‖ ≥ 2√2·‖α‖·ξ₁/2 ≥ 5.4·10⁻⁴` on the whole gate, and hence
`‖τ_f z‖ ≤ ‖σ‖/5.4·10⁻⁴ ≤ 932 < 1/(4η) = 250000` for every gate point: the claimed point does
not exist.  The same happens for `α` near any non-zero integer (e.g. `α = 1 + 10⁻¹⁰ i`,
`ξ₁ = 10⁻⁸`, `η = 10⁻⁶`, where the gate stays `≳ 4·10⁻⁸` away from the lattice in the relevant
sense while `4η‖σ‖ ≈ 1.3·10⁻¹⁵`).

The obstruction is exactly the smallness of `α` (the intended use has `‖α‖η ≤ 10⁻⁶` with `η ≥ 1`,
see `Work.Pert.small_of_nearOn` and `Work.Pert.Dsub_phi_star`).  Accordingly the two theorems
below prove the requested conclusion under one extra hypothesis each:

* `exists_tauC_gate_ge_of_norm_le`: `‖α‖ ≤ 1/1024` (then `‖1 - exp (2πi α)‖ ≥ π‖α‖` and
  `‖σ‖ = ‖1 - exp (2πi α)‖/‖u 0‖ ≥ π‖α‖/2`);
* `exists_tauC_gate_ge_of_one_le_eta`: `1 ≤ η` (which together with `‖α‖ η ≤ 1/1024` gives
  `‖α‖ ≤ 1/1024`, so it is a corollary of the first).

In both cases the witness is the single explicit point `z = i η/2`, which lies in the lower gate
(`Work.Pert.I_mul_half_eta_mem_Qm`); there `exp (-(2πi α z)) = exp (π η α)`, so
`‖1 - exp (-(2πi α z))‖ ≤ (3/2)·π η ‖α‖` by the quadratic Taylor bound
`Complex.norm_exp_sub_one_sub_id_le` (legitimate because `π η ‖α‖ ≤ π/1024`), while
`4η‖σ‖ ≥ 2π η ‖α‖`.
-/

namespace Work.Pert

open MandelDim Complex

noncomputable section

/-- `x² ≤ x/2` for `0 ≤ x ≤ 1/2` — the numerical core of the Taylor estimate at `z = i η/2`. -/
private lemma sq_le_half_mul {x : ℝ} (h0 : 0 ≤ x) (h : x ≤ 1 / 2) : x ^ 2 ≤ (1 / 2) * x := by
  nlinarith [h, h0]

/-- **Repaired gate estimate** (extra hypothesis: `‖α‖ ≤ 1/1024`): for a perturbation with
normal form data `(σ, α)`, `1 - σu 0 = exp (2πi α)`, `1/2 ≤ ‖u 0‖ ≤ 2`, `InF1 α` and
`2ξ₁ < η`, `π η ‖α‖ ≤ π/1024`, there is a point of the lower gate where `‖τ_f‖ ≥ 1/(4η)` —
namely `z = i η/2`. -/
theorem exists_tauC_gate_ge_of_norm_le {u : ℂ → ℂ} {σ α : ℂ} {ξ₁ η : ℝ}
    (hξ : 0 < ξ₁) (hη : 2 * ξ₁ < η) (hInF1 : MandelDim.InF1 α) (hα0 : α ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu0 : 1 / 2 ≤ ‖u 0‖) (hub2 : ‖u 0‖ ≤ 2) (hαη : ‖α‖ * η ≤ 1 / 1024)
    (hαsmall : ‖α‖ ≤ 1 / 1024) (hσ0 : σ ≠ 0) :
    ∃ z ∈ Work.Pert.Qm ξ₁ α, 1 / (4 * η) ≤ ‖Work.Pert.tauC σ α z‖ := by
  have hηpos : 0 < η := by linarith
  have hαnormpos : 0 < ‖α‖ := norm_pos_iff.mpr hα0
  have hαnormnn : (0 : ℝ) ≤ ‖α‖ := le_of_lt hαnormpos
  refine ⟨Complex.I * (η / 2), I_mul_half_eta_mem_Qm hξ hη hInF1, ?_⟩
  -- `‖1 - exp (2πi α)‖ ≥ π‖α‖` and `‖σ‖ ≥ π‖α‖/2`
  have hE : Real.pi * ‖α‖ ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ :=
    norm_one_sub_exp_two_pi_I_lower hαsmall
  have hsu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
    linear_combination -hnorm
  have hu0pos : 0 < ‖u 0‖ := by linarith
  have hσ : ‖σ‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ / ‖u 0‖ := by
    have h : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * Complex.I * α)‖ := by
      rw [← norm_mul, hsu]
    rw [eq_div_iff (ne_of_gt hu0pos)]
    linarith
  have hσlb : Real.pi * ‖α‖ / 2 ≤ ‖σ‖ := by
    rw [hσ, le_div_iff₀ hu0pos]
    have h1 : Real.pi * ‖α‖ / 2 * ‖u 0‖ ≤ Real.pi * ‖α‖ / 2 * 2 :=
      mul_le_mul_of_nonneg_left hub2 (by positivity)
    linarith
  -- the exponent at `z = i η/2` is `π η α`
  have hx : -(2 * Real.pi * Complex.I * α * (Complex.I * (η / 2))) = Real.pi * η * α := by
    have hII : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
    calc -(2 * ↑Real.pi * I * α * (I * (↑η / 2)))
        = -(2 * ↑Real.pi * α * (I * I) * (↑η / 2)) := by ring
      _ = ↑Real.pi * ↑η * α := by rw [hII]; ring
  have hxnorm : ‖Real.pi * η * α‖ = Real.pi * η * ‖α‖ := by
    rw [norm_mul, norm_mul]
    simp [abs_of_pos Real.pi_pos, abs_of_pos hηpos]
  have hxnn : (0 : ℝ) ≤ Real.pi * η * ‖α‖ := by positivity
  have hxle : ‖Real.pi * η * α‖ ≤ 1 / 2 := by
    rw [hxnorm]
    have h1 : η * ‖α‖ ≤ 1 / 1024 := by linarith [hαη]
    have h2 : Real.pi * (η * ‖α‖) ≤ 512 * (1 / 1024) :=
      mul_le_mul (by nlinarith [Real.pi_lt_four]) h1 (by positivity) (by norm_num)
    nlinarith [h2]
  have hsq : (Real.pi * η * ‖α‖) ^ 2 ≤ (1 / 2) * (Real.pi * η * ‖α‖) :=
    sq_le_half_mul hxnn (by rw [← hxnorm]; exact hxle)
  -- upper bound for the denominator of `τ`
  have hden_ub : ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * (Complex.I * (η / 2))))‖
      ≤ (3 / 2) * (Real.pi * η * ‖α‖) := by
    rw [hx]
    have h2 : ‖Real.pi * η * α‖ ≤ 1 := by linarith [hxle]
    have h3 : ‖Complex.exp (Real.pi * η * α) - 1 - Real.pi * η * α‖ ≤ ‖Real.pi * η * α‖ ^ 2 :=
      Complex.norm_exp_sub_one_sub_id_le h2
    have h4 : ‖Complex.exp (Real.pi * η * α) - 1‖
        ≤ ‖Real.pi * η * α‖ + ‖Real.pi * η * α‖ ^ 2 := by
      have h5 : ‖Complex.exp (Real.pi * η * α) - 1‖
          = ‖(Complex.exp (Real.pi * η * α) - 1 - Real.pi * η * α) + Real.pi * η * α‖ := by
        congr 1
        ring
      rw [h5]
      have h6 := norm_add_le (Complex.exp (Real.pi * η * α) - 1 - Real.pi * η * α)
        (Real.pi * η * α)
      linarith [h6, h3]
    have h7 : ‖1 - Complex.exp (Real.pi * η * α)‖ = ‖Complex.exp (Real.pi * η * α) - 1‖ :=
      norm_sub_rev _ _
    rw [h7]
    have h8 : ‖Real.pi * η * α‖ + ‖Real.pi * η * α‖ ^ 2
        ≤ (3 / 2) * (Real.pi * η * ‖α‖) := by
      have hq : ‖Real.pi * η * α‖ ^ 2 ≤ (1 / 2) * (Real.pi * η * ‖α‖) := by
        rw [hxnorm]; exact hsq
      rw [hxnorm]
      rw [hxnorm] at hq
      linarith [hq]
    linarith [h4, h8]
  -- lower bound for the denominator of `τ` (positivity)
  have hden_lb : Real.pi * η * ‖α‖ / 2
      ≤ ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * (Complex.I * (η / 2))))‖ := by
    rw [hx]
    have h2 : ‖Real.pi * η * α‖ ≤ 1 := by linarith [hxle]
    have h3 : ‖Complex.exp (Real.pi * η * α) - 1 - Real.pi * η * α‖ ≤ ‖Real.pi * η * α‖ ^ 2 :=
      Complex.norm_exp_sub_one_sub_id_le h2
    have h7 : ‖1 - Complex.exp (Real.pi * η * α)‖ = ‖Complex.exp (Real.pi * η * α) - 1‖ :=
      norm_sub_rev _ _
    rw [h7]
    have h9 : Real.pi * η * ‖α‖ - (Real.pi * η * ‖α‖) ^ 2
        ≤ ‖Complex.exp (Real.pi * η * α) - 1‖ := by
      have h10 : ‖Real.pi * η * α‖ ≤ ‖Complex.exp (Real.pi * η * α) - 1‖
          + ‖Complex.exp (Real.pi * η * α) - 1 - Real.pi * η * α‖ := by
        have h11 : ‖Real.pi * η * α‖
            = ‖(Complex.exp (Real.pi * η * α) - 1)
                - (Complex.exp (Real.pi * η * α) - 1 - Real.pi * η * α)‖ := by
          congr 1
          ring
        rw [h11]
        exact norm_sub_le _ _
      rw [hxnorm] at h10
      have h12 : ‖Complex.exp (Real.pi * η * α) - 1 - Real.pi * η * α‖
          ≤ (Real.pi * η * ‖α‖) ^ 2 := by
        rw [← hxnorm]; exact h3
      linarith [h10, h12]
    have h13 : Real.pi * η * ‖α‖ / 2 ≤ Real.pi * η * ‖α‖ - (Real.pi * η * ‖α‖) ^ 2 := by
      linarith [hsq]
    linarith [h9, h13]
  have hdenpos : 0 < ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * (Complex.I * (η / 2))))‖ :=
    lt_of_lt_of_le (by positivity) hden_lb
  have htau : ‖Work.Pert.tauC σ α (Complex.I * (η / 2))‖
      = ‖σ‖ / ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * (Complex.I * (η / 2))))‖ := by
    unfold Work.Pert.tauC
    exact norm_div _ _
  rw [htau, le_div_iff₀ hdenpos]
  have hstep : (1 / (4 * η))
      * ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * (Complex.I * (η / 2))))‖
      ≤ (1 / (4 * η)) * ((3 / 2) * (Real.pi * η * ‖α‖)) :=
    mul_le_mul_of_nonneg_left hden_ub (by positivity)
  have hlast : (1 / (4 * η)) * ((3 / 2) * (Real.pi * η * ‖α‖))
      = (3 / 8) * (Real.pi * ‖α‖) := by
    field_simp
    ring
  calc (1 / (4 * η)) * ‖1 - Complex.exp (-(2 * Real.pi * Complex.I * α * (Complex.I * (η / 2))))‖
      ≤ (1 / (4 * η)) * ((3 / 2) * (Real.pi * η * ‖α‖)) := hstep
    _ = (3 / 8) * (Real.pi * ‖α‖) := hlast
    _ ≤ (1 / 2) * (Real.pi * ‖α‖) := by nlinarith [hαnormnn, Real.pi_pos]
    _ ≤ ‖σ‖ := by linarith [hσlb]

/-- **Repaired gate estimate, `η ≥ 1` form**: the statement requested as
`Work.Pert.exists_tauC_gate_ge`, with the additional hypothesis `1 ≤ η`.  Together with
`‖α‖ η ≤ 1/1024` this gives `‖α‖ ≤ 1/1024`, so this is the `of_norm_le` version above.  This is
the form matching the intended use (`Work.Pert.small_of_nearOn` yields `‖α‖ η ≤ 10⁻⁶` for
`η ≥ η₁` with `η₁` a large constant depending on the germ). -/
theorem exists_tauC_gate_ge_of_one_le_eta {u : ℂ → ℂ} {σ α : ℂ} {ξ₁ η : ℝ}
    (hξ : 0 < ξ₁) (hη : 2 * ξ₁ < η) (hInF1 : MandelDim.InF1 α) (hα0 : α ≠ 0)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu0 : 1 / 2 ≤ ‖u 0‖) (hub2 : ‖u 0‖ ≤ 2) (hαη : ‖α‖ * η ≤ 1 / 1024)
    (hη1 : 1 ≤ η) (hσ0 : σ ≠ 0) :
    ∃ z ∈ Work.Pert.Qm ξ₁ α, 1 / (4 * η) ≤ ‖Work.Pert.tauC σ α z‖ := by
  refine exists_tauC_gate_ge_of_norm_le hξ hη hInF1 hα0 hnorm hu0 hub2 hαη ?_ hσ0
  calc ‖α‖ = ‖α‖ * 1 := by ring
    _ ≤ ‖α‖ * η := mul_le_mul_of_nonneg_left hη1 (norm_nonneg α)
    _ ≤ 1 / 1024 := hαη

end

end Work.Pert
