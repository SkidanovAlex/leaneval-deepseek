import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.H2.T1Q.SmoothTransitionDeriv
import Submission.Work.H2.T1Q.SinRatioBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The cutoff function `χ` of the `T1` estimate

This file constructs the smooth cutoff `χ ζ θ` (with a uniform constant `B`) used to localise
the `θ`-variable away from the two singular ends `θ = 0` and `θ = π/2` of the quadrant, with a
*uniform in `ζ`* bound on `|sin (2θ) · ∂_θ χ ζ θ|`.

The construction is the product `χ ζ θ = φ_ζ θ · ψ_ζ θ` of two rescalings of Mathlib's smooth
step function `Real.smoothTransition`:

* `φ ζ θ = smoothTransition (2/ζ · θ - 1)` rises from `0` at `θ = ζ/2` to `1` at `θ = ζ`;
* `ψ ζ θ = smoothTransition (2/ζ · (π/2 - ζ/2) - 2/ζ · θ)` falls from `1` at `θ = π/2 - ζ`
  to `0` at `θ = π/2 - ζ/2`.

Hence `χ ζ θ = 1` on `[ζ, π/2 - ζ]`, `χ ζ θ = 0` on `[0, ζ/2] ∪ [π/2 - ζ/2, π/2]`, and the
derivative is supported in the two windows `(ζ/2, ζ)` and `(π/2 - ζ, π/2 - ζ/2)`. In either
window `|sin (2θ)| ≤ 2ζ`, so `|∂_θ χ| ≤ 4/ζ · (number of active factors)` and
`|sin (2θ) ∂_θ χ| ≤ 8 M`, with `M` a bound for `|deriv smoothTransition|`.
-/

open scoped Real Topology
open Filter Set

noncomputable section

namespace Work.H2.T1Q

/-- The rising factor: `φ_ζ θ = smoothTransition (2/ζ · θ - 1)`. -/
def phi (ζ : ℝ) : ℝ → ℝ := fun t => Real.smoothTransition (2 / ζ * t - 1)

/-- The falling factor: `ψ_ζ θ = smoothTransition (2/ζ · (π/2 - ζ/2) - 2/ζ · θ)`. -/
def psi (ζ : ℝ) : ℝ → ℝ :=
  fun t => Real.smoothTransition (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * t)

/-- The cutoff `χ ζ = φ_ζ · ψ_ζ`. -/
def chiFun (ζ : ℝ) : ℝ → ℝ := phi ζ * psi ζ

private lemma contDiff_phi (ζ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phi ζ) := by
  unfold phi; fun_prop

private lemma contDiff_psi (ζ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (psi ζ) := by
  unfold psi; fun_prop

theorem Cutoff : ∃ (chi : ℝ → ℝ → ℝ) (B : ℝ), 0 < B ∧
    (∀ ζ : ℝ, ContDiff ℝ (⊤ : ℕ∞) (chi ζ)) ∧
    (∀ ζ θ : ℝ, 0 ≤ chi ζ θ) ∧ (∀ ζ θ : ℝ, chi ζ θ ≤ 1) ∧
    (∀ ζ θ : ℝ, 0 < ζ → ζ ≤ θ → θ ≤ π / 2 - ζ → chi ζ θ = 1) ∧
    (∀ ζ θ : ℝ, 0 < ζ → θ ≤ ζ / 2 → chi ζ θ = 0) ∧
    (∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 ≤ θ → chi ζ θ = 0) ∧
    (∀ ζ θ : ℝ, 0 < ζ → θ < ζ / 2 → deriv (chi ζ) θ = 0) ∧
    (∀ ζ θ : ℝ, 0 < ζ → π / 2 - ζ / 2 < θ → deriv (chi ζ) θ = 0) ∧
    (∀ ζ : ℝ, 0 < ζ → ∀ θ : ℝ, |Real.sin (2 * θ) * deriv (chi ζ) θ| ≤ B) ∧
    (∀ θ : ℝ, 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun ζ : ℝ => chi ζ θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1))
    := by
  obtain ⟨hderiv_nonpos, hderiv_one_le, M, hM0, hMbd⟩ := SmoothTransitionDeriv
  refine ⟨chiFun, max (8 * M) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness in `θ`
    intro ζ
    exact (contDiff_phi ζ).mul (contDiff_psi ζ)
  · -- nonnegativity
    intro ζ θ
    show 0 ≤ phi ζ θ * psi ζ θ
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · -- upper bound `1`
    intro ζ θ
    show phi ζ θ * psi ζ θ ≤ 1
    calc phi ζ θ * psi ζ θ ≤ 1 * psi ζ θ :=
          mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
            (Real.smoothTransition.nonneg _)
      _ = psi ζ θ := one_mul _
      _ ≤ 1 := Real.smoothTransition.le_one _
  · -- `χ = 1` on the middle interval
    intro ζ θ hζ h1 h2
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hA : 1 ≤ 2 / ζ * θ - 1 := by
      have hle : 2 / ζ * ζ ≤ 2 / ζ * θ := mul_le_mul_of_nonneg_left h1 h2ζ.le
      have hval : 2 / ζ * ζ = 2 := div_mul_cancel₀ 2 hζ.ne'
      linarith
    have hB : 1 ≤ 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ := by
      have hle : 2 / ζ * θ ≤ 2 / ζ * (Real.pi / 2 - ζ) :=
        mul_le_mul_of_nonneg_left h2 h2ζ.le
      have hval : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * (Real.pi / 2 - ζ) = 1 := by
        field_simp
        ring
      linarith
    show phi ζ θ * psi ζ θ = 1
    rw [show phi ζ θ = 1 from Real.smoothTransition.one_of_one_le hA,
        show psi ζ θ = 1 from Real.smoothTransition.one_of_one_le hB, mul_one]
  · -- `χ = 0` for `θ ≤ ζ/2`
    intro ζ θ hζ h
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hA : 2 / ζ * θ - 1 ≤ 0 := by
      have hle : 2 / ζ * θ ≤ 2 / ζ * (ζ / 2) := mul_le_mul_of_nonneg_left h h2ζ.le
      have hval : 2 / ζ * (ζ / 2) = 1 := by field_simp
      linarith
    show phi ζ θ * psi ζ θ = 0
    rw [show phi ζ θ = 0 from Real.smoothTransition.zero_of_nonpos hA, zero_mul]
  · -- `χ = 0` for `π/2 - ζ/2 ≤ θ`
    intro ζ θ hζ h
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hB : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ ≤ 0 := by
      have hle : 2 / ζ * (Real.pi / 2 - ζ / 2) ≤ 2 / ζ * θ :=
        mul_le_mul_of_nonneg_left h h2ζ.le
      linarith
    show phi ζ θ * psi ζ θ = 0
    rw [show psi ζ θ = 0 from Real.smoothTransition.zero_of_nonpos hB, mul_zero]
  · -- `deriv χ = 0` for `θ < ζ/2`
    intro ζ θ hζ hθ
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hev : chiFun ζ =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Iio.mem_nhds hθ] with t ht
      have hA : 2 / ζ * t - 1 ≤ 0 := by
        have hle : 2 / ζ * t ≤ 2 / ζ * (ζ / 2) := mul_le_mul_of_nonneg_left ht.le h2ζ.le
        have hval : 2 / ζ * (ζ / 2) = 1 := by field_simp
        linarith
      show phi ζ t * psi ζ t = 0
      rw [show phi ζ t = 0 from Real.smoothTransition.zero_of_nonpos hA, zero_mul]
    rw [hev.deriv_eq]
    exact deriv_const θ 0
  · -- `deriv χ = 0` for `π/2 - ζ/2 < θ`
    intro ζ θ hζ hθ
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hev : chiFun ζ =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hθ] with t ht
      have hB : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * t ≤ 0 := by
        have hle : 2 / ζ * (Real.pi / 2 - ζ / 2) < 2 / ζ * t :=
          mul_lt_mul_of_pos_left ht h2ζ
        linarith
      show phi ζ t * psi ζ t = 0
      rw [show psi ζ t = 0 from Real.smoothTransition.zero_of_nonpos hB, mul_zero]
    rw [hev.deriv_eq]
    exact deriv_const θ 0
  · -- the uniform weighted derivative bound
    intro ζ hζ θ
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ
    have hdphi : deriv (phi ζ) θ = deriv Real.smoothTransition (2 / ζ * θ - 1) * (2 / ζ) := by
      unfold phi
      have h1 : HasDerivAt (fun t : ℝ => 2 / ζ * t - 1) (2 / ζ) θ := by
        simpa using (((hasDerivAt_id θ).const_mul (2 / ζ)).sub_const 1)
      have h2 : DifferentiableAt ℝ Real.smoothTransition (2 / ζ * θ - 1) := by fun_prop
      exact (h2.hasDerivAt.comp θ h1).deriv
    have hdpsi : deriv (psi ζ) θ =
        deriv Real.smoothTransition (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ) * (-(2 / ζ)) := by
      unfold psi
      have h1 : HasDerivAt (fun t : ℝ => 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * t)
          (-(2 / ζ)) θ := by
        have hh := (hasDerivAt_id θ).const_mul (2 / ζ)
        simpa using hh.const_sub (2 / ζ * (Real.pi / 2 - ζ / 2))
      have h2 : DifferentiableAt ℝ Real.smoothTransition
          (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ) := by fun_prop
      exact (h2.hasDerivAt.comp θ h1).deriv
    have hdmul : deriv (chiFun ζ) θ = deriv (phi ζ) θ * psi ζ θ + phi ζ θ * deriv (psi ζ) θ := by
      have d1 : DifferentiableAt ℝ (phi ζ) θ := by unfold phi; fun_prop
      have d2 : DifferentiableAt ℝ (psi ζ) θ := by unfold psi; fun_prop
      unfold chiFun
      exact deriv_mul d1 d2
    have hphi_le : |phi ζ θ| ≤ 1 := by
      unfold phi
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hpsi_le : |psi ζ θ| ≤ 1 := by
      unfold psi
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hb_phi : |Real.sin (2 * θ)| * |deriv (phi ζ) θ| ≤ 4 * M := by
      rw [hdphi, abs_mul, abs_of_pos h2ζ]
      by_cases hA : 0 < 2 / ζ * θ - 1 ∧ 2 / ζ * θ - 1 < 1
      · have hwin : ζ / 2 < θ ∧ θ < ζ := by
          obtain ⟨hA1, hA2⟩ := hA
          have h1 : 1 < 2 / ζ * θ := by linarith
          have h2 : 2 / ζ * θ < 2 := by linarith
          have h3 : ζ < 2 * θ := by
            rw [div_mul_eq_mul_div] at h1
            have := (lt_div_iff₀ hζ).mp h1
            simpa using this
          have h4 : 2 * θ < 2 * ζ := by
            rw [div_mul_eq_mul_div] at h2
            have := (div_lt_iff₀ hζ).mp h2
            simpa using this
          constructor <;> linarith
        have hsin4 : |Real.sin (2 * θ)| * (2 / ζ) ≤ 4 := SinRatioBound hζ (Or.inl hwin)
        calc |Real.sin (2 * θ)| * (|deriv Real.smoothTransition (2 / ζ * θ - 1)| * (2 / ζ))
            ≤ |Real.sin (2 * θ)| * (M * (2 / ζ)) := by
              gcongr
              exact hMbd _
          _ = M * (|Real.sin (2 * θ)| * (2 / ζ)) := by ring
          _ ≤ M * 4 := mul_le_mul_of_nonneg_left hsin4 hM0
          _ = 4 * M := by ring
      · have hz : deriv Real.smoothTransition (2 / ζ * θ - 1) = 0 := by
          rcases not_and_or.mp hA with h | h
          · exact hderiv_nonpos _ (not_lt.mp h)
          · exact hderiv_one_le _ (not_lt.mp h)
        rw [hz, abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (by norm_num) hM0
    have hb_psi : |Real.sin (2 * θ)| * |deriv (psi ζ) θ| ≤ 4 * M := by
      rw [hdpsi, abs_mul, abs_neg, abs_of_pos h2ζ]
      by_cases hB : 0 < 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ ∧
          2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ < 1
      · have hwin : Real.pi / 2 - ζ < θ ∧ θ < Real.pi / 2 - ζ / 2 := by
          obtain ⟨hB1, hB2⟩ := hB
          have h5 : 2 / ζ * θ < 2 / ζ * (Real.pi / 2 - ζ / 2) := by linarith
          have h6 : θ < Real.pi / 2 - ζ / 2 := lt_of_mul_lt_mul_left h5 h2ζ.le
          have h7 : 2 / ζ * (Real.pi / 2 - ζ / 2 - θ) < 1 := by
            have hfac : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ =
                2 / ζ * (Real.pi / 2 - ζ / 2 - θ) := by ring
            linarith
          have h8 : Real.pi / 2 - ζ / 2 - θ < ζ / 2 := by
            have hv : (1 : ℝ) = 2 / ζ * (ζ / 2) := by field_simp
            rw [hv] at h7
            exact lt_of_mul_lt_mul_left h7 h2ζ.le
          constructor <;> linarith
        have hsin4 : |Real.sin (2 * θ)| * (2 / ζ) ≤ 4 := SinRatioBound hζ (Or.inr hwin)
        calc |Real.sin (2 * θ)| *
              (|deriv Real.smoothTransition (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ)| * (2 / ζ))
            ≤ |Real.sin (2 * θ)| * (M * (2 / ζ)) := by
              gcongr
              exact hMbd _
          _ = M * (|Real.sin (2 * θ)| * (2 / ζ)) := by ring
          _ ≤ M * 4 := mul_le_mul_of_nonneg_left hsin4 hM0
          _ = 4 * M := by ring
      · have hz : deriv Real.smoothTransition
            (2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ) = 0 := by
          rcases not_and_or.mp hB with h | h
          · exact hderiv_nonpos _ (not_lt.mp h)
          · exact hderiv_one_le _ (not_lt.mp h)
        rw [hz, abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (by norm_num) hM0
    have hderivchi : |deriv (chiFun ζ) θ| ≤ |deriv (phi ζ) θ| + |deriv (psi ζ) θ| := by
      rw [hdmul]
      calc |deriv (phi ζ) θ * psi ζ θ + phi ζ θ * deriv (psi ζ) θ|
          ≤ |deriv (phi ζ) θ * psi ζ θ| + |phi ζ θ * deriv (psi ζ) θ| := abs_add_le _ _
        _ = |deriv (phi ζ) θ| * |psi ζ θ| + |phi ζ θ| * |deriv (psi ζ) θ| := by
            rw [abs_mul, abs_mul]
        _ ≤ |deriv (phi ζ) θ| * 1 + 1 * |deriv (psi ζ) θ| := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpsi_le (abs_nonneg _)
            · exact mul_le_mul_of_nonneg_right hphi_le (abs_nonneg _)
        _ = |deriv (phi ζ) θ| + |deriv (psi ζ) θ| := by ring
    calc |Real.sin (2 * θ) * deriv (chiFun ζ) θ|
        = |Real.sin (2 * θ)| * |deriv (chiFun ζ) θ| := by rw [abs_mul]
      _ ≤ |Real.sin (2 * θ)| * (|deriv (phi ζ) θ| + |deriv (psi ζ) θ|) :=
            mul_le_mul_of_nonneg_left hderivchi (abs_nonneg _)
      _ = |Real.sin (2 * θ)| * |deriv (phi ζ) θ| + |Real.sin (2 * θ)| * |deriv (psi ζ) θ| := by
            ring
      _ ≤ 4 * M + 4 * M := add_le_add hb_phi hb_psi
      _ = 8 * M := by ring
      _ ≤ max (8 * M) 1 := le_max_left _ _
  · -- the limiting behaviour as `ζ → 0⁺`
    intro θ hθ0 hθπ
    have hc : 0 < min θ (Real.pi / 2 - θ) := lt_min hθ0 (by linarith)
    have hmem : Set.Ioo (0 : ℝ) (min θ (Real.pi / 2 - θ)) ∈ 𝓝[>] (0 : ℝ) := by
      have h1 : Set.Iio (min θ (Real.pi / 2 - θ)) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds hc)
      have h2 : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
      exact Filter.mem_of_superset (inter_mem h1 h2) (fun x hx => ⟨hx.2, hx.1⟩)
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [hmem] with ζ hζ
    obtain ⟨hζ0, hζlt⟩ := hζ
    have h1 : ζ ≤ θ := le_of_lt (lt_of_lt_of_le hζlt (min_le_left _ _))
    have h2 : θ ≤ Real.pi / 2 - ζ := by
      have : ζ ≤ Real.pi / 2 - θ := le_of_lt (lt_of_lt_of_le hζlt (min_le_right _ _))
      linarith
    have h2ζ : (0 : ℝ) < 2 / ζ := div_pos two_pos hζ0
    have hA : 1 ≤ 2 / ζ * θ - 1 := by
      have hle : 2 / ζ * ζ ≤ 2 / ζ * θ := mul_le_mul_of_nonneg_left h1 h2ζ.le
      have hval : 2 / ζ * ζ = 2 := div_mul_cancel₀ 2 hζ0.ne'
      linarith
    have hB : 1 ≤ 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * θ := by
      have hle : 2 / ζ * θ ≤ 2 / ζ * (Real.pi / 2 - ζ) := mul_le_mul_of_nonneg_left h2 h2ζ.le
      have hval : 2 / ζ * (Real.pi / 2 - ζ / 2) - 2 / ζ * (Real.pi / 2 - ζ) = 1 := by
        field_simp
        ring
      linarith
    show (1 : ℝ) = chiFun ζ θ
    show (1 : ℝ) = phi ζ θ * psi ζ θ
    rw [show phi ζ θ = 1 from Real.smoothTransition.one_of_one_le hA,
        show psi ζ θ = 1 from Real.smoothTransition.one_of_one_le hB, mul_one]

end Work.H2.T1Q
