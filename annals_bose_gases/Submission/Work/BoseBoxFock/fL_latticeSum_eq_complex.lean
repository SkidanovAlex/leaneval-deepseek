import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.fL_latticeSum_eq_periodisation_complex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators
open MeasureTheory

/-!
# `Work.BoseBoxFock.fL_latticeSum_eq_complex`

The **complex exponential form** of the periodisation (Poisson summation) identity for the
low-momentum symbol `fc.f(‖·‖/κ)`, in its **finite-lattice** (`Lab N`) form.

For `κ, ℓ > 0`, `N` with `2κℓ/(2π) ≤ N` and every shift `z ∈ ℝ³`,

    Σ_{s ∈ Lab N, s ≠ 0} f(‖k_s‖/κ)·e^{i⟪k_s,z⟫}
      = ℓ³ Σ'_d (2π)⁻³ ∫_p e^{i⟪p, z + ℓ·v_d⟫} f(‖p‖/κ) dp  −  1 ,

where `k_s = kmomLab ℓ N s = (2π/ℓ) • latVec (labVec N s)` is the sampling lattice of the
label cube `Lab N = (ZMod (2N+1))³` and `v_d = latVec d` runs over `ℤ³`.

## Proof architecture

`P1` (`Work.BoseBoxFock.fL_latticeSum_eq_periodisation_complex`, proved in the sibling module)
is the **complex** Poisson/periodisation identity over the *full* lattice `ℤ³`:

    Σ'_m f(‖(2π/ℓ)•latVec m‖/κ)·e^{i⟪(2π/ℓ)•latVec m, w⟫}
      = ℓ³ Σ'_d (2π)⁻³ ∫_p e^{i⟪p, w + ℓ•latVec d⟫} f(‖p‖/κ) dp .

`P2` (`tsum_lat_eq_sum_lab`, proved here) is the **finite-lattice reduction**: since `fc.f`
vanishes for argument `≥ 2` and `2κℓ/(2π) ≤ N`, every nonvanishing term of the series over
`ℤ³` has `‖m‖ < 2κℓ/(2π) ≤ N`, hence all coordinates satisfy `|m i| ≤ N`, i.e. `m` lies in the
centred cube `[-N,N]³ = labVec N '' Lab N`; so the full lattice series *is* the finite sum over
`Lab N` (with no tail).

The stated identity then follows by subtracting the `s = 0` term, which is `fc.f 0 · e^0 = 1`
(`LowCut.one`), exactly accounting for the `− 1` on the right-hand side.
-/

/-- `vec n = 2π • latVec n`. -/
lemma vec_eq_two_pi_smul_latVec_fL (m : Fin 3 → ℤ) :
    Work.BoseB4.vec m = (2 * Real.pi) • latVec m := by
  rw [Work.BoseB4.vec, latVec, ← WithLp.toLp_smul]
  rfl

/-- `kmomLab` is the sampling lattice vector `(2π/ℓ) • latVec` at the centred label. -/
lemma kmomLab_eq_piL (ℓ : ℝ) (N : ℕ) (s : Lab N) :
    kmomLab ℓ N s = (2 * Real.pi / ℓ) • latVec (labVec N s) := by
  rw [kmomLab, vec_eq_two_pi_smul_latVec_fL, smul_smul, inv_mul_eq_div]

/-- The centred representatives of the cube labels are distinct. -/
lemma labVec_injective_fL (N : ℕ) : Function.Injective (labVec N) := by
  intro a b h
  funext i
  exact ZMod.valMinAbs_inj.mp (congrFun h i)

/-- Every `m ∈ ℤ³` with `|m i| ≤ N` is the centred representative of a label of `Lab N`. -/
lemma latVec_surj_fL (N : ℕ) {m : Fin 3 → ℤ} (hm : ∀ i, |m i| ≤ (N : ℤ)) :
    labVec N (fun i => ((m i : ℤ) : ZMod (2 * N + 1))) = m := by
  funext i
  show ((((m i : ℤ) : ZMod (2 * N + 1))).valMinAbs) = m i
  have hne : NeZero (2 * N + 1) := ⟨by omega⟩
  refine (ZMod.valMinAbs_spec _ _).mpr ⟨?_, ?_⟩
  · rfl
  · obtain ⟨h1, h2⟩ := abs_le.mp (hm i)
    simp only [Set.mem_Ioc]
    constructor <;> omega

/-- **The finite-lattice reduction.**  Because `fc.f` is supported in `‖p‖ ≤ 2κ` and
`2κℓ/(2π) ≤ N`, the full `ℤ³`-series is the finite `Lab N`-sum (the terms of the centred cube
`[-N,N]³`; there is no tail). -/
theorem tsum_lat_eq_sum_lab (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (N : ℕ) (hN : 2 * κ * ℓ / (2 * Real.pi) ≤ (N : ℝ)) (z : EuclideanSpace ℝ (Fin 3)) :
    (∑' m : Fin 3 → ℤ,
        ((fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)))
      = ∑ s : Lab N,
          ((fc.f (‖kmomLab ℓ N s‖ / κ) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N s) z : ℂ)) := by
  classical
  have hc : 0 < 2 * Real.pi / ℓ := by positivity
  -- pass to the `(2π/ℓ) • latVec` normalisation on the right-hand side
  have hRHS : (∑ s : Lab N, ((fc.f (‖kmomLab ℓ N s‖ / κ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N s) z : ℂ)))
      = ∑ s : Lab N,
          ((fc.f (‖(2 * Real.pi / ℓ) • latVec (labVec N s)‖ / κ) : ℝ) : ℂ) *
            Complex.exp (Complex.I *
              (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N s)) z : ℂ)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [kmomLab_eq_piL]
  -- every term off the centred cube vanishes, the symbol being supported in `‖p‖ ≤ 2κ`
  have hzero : ∀ m ∉ (Finset.univ.image (labVec N)),
      ((fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)) = 0 := by
    intro m hm
    have hnorm : (N : ℝ) < ‖latVec m‖ := by
      by_contra hle
      rw [not_lt] at hle
      apply hm
      refine Finset.mem_image.mpr ⟨fun i => ((m i : ℤ) : ZMod (2 * N + 1)),
        Finset.mem_univ _, ?_⟩
      refine latVec_surj_fL N fun i => ?_
      have h1 : |(m i : ℝ)| ≤ ‖latVec m‖ := by
        have h := PiLp.norm_apply_le (latVec m) i
        simpa [latVec_apply] using h
      have h2 : |(m i : ℝ)| ≤ (N : ℝ) := le_trans h1 hle
      rw [← Int.cast_abs] at h2
      exact_mod_cast h2
    have hbig : 2 * κ < ‖(2 * Real.pi / ℓ) • latVec m‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc.le]
      have hscal : (2 * Real.pi / ℓ) * (2 * κ * ℓ / (2 * Real.pi)) = 2 * κ := by
        field_simp
      rw [← hscal]
      exact mul_lt_mul_of_pos_left (lt_of_le_of_lt hN hnorm) hc
    have h2 : (2 : ℝ) ≤ ‖(2 * Real.pi / ℓ) • latVec m‖ / κ := by
      rw [le_div_iff₀ hκ]
      linarith
    rw [fc.zero _ h2, Complex.ofReal_zero, zero_mul]
  -- reindex the `Lab N`-sum as the sum over the image of `labVec N`
  have himg : (∑ s : Lab N,
          ((fc.f (‖(2 * Real.pi / ℓ) • latVec (labVec N s)‖ / κ) : ℝ) : ℂ) *
            Complex.exp (Complex.I *
              (inner ℝ ((2 * Real.pi / ℓ) • latVec (labVec N s)) z : ℂ)))
      = ∑ m ∈ (Finset.univ.image (labVec N)),
          ((fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)) :=
    (Finset.sum_image (s := (Finset.univ : Finset (Lab N))) (g := labVec N)
      (f := fun m : Fin 3 → ℤ =>
        ((fc.f (‖(2 * Real.pi / ℓ) • latVec m‖ / κ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)))
      (fun x _ y _ hxy => labVec_injective_fL N hxy)).symm
  rw [hRHS, himg]
  exact tsum_eq_sum hzero

theorem fL_latticeSum_eq_complex {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * κ * ℓ / (2 * Real.pi) ≤ (N : ℝ)) (z : EuclideanSpace ℝ (Fin 3)) :
    (∑ s : Work.BoseBoxFock.Lab N, if s = 0 then 0 else
        ((fc.f (‖Work.BoseBoxFock.kmomLab ℓ N s‖ / κ) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) z : ℂ)))
      = (ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ,
          ((((2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ∫ p : EuclideanSpace ℝ (Fin 3),
              Complex.exp (Complex.I * (inner ℝ p (z + ℓ • Work.BoseBoxFock.latVec d) : ℂ)) *
                ((fc.f (‖p‖ / κ) : ℝ) : ℂ))
        - 1 := by
  classical
  -- P1: the complex Poisson/periodisation identity on the full lattice `ℤ³`
  have hpois := fL_latticeSum_eq_periodisation_complex fc hκ hℓ z
  -- P2: the finite-lattice reduction
  have hlat := tsum_lat_eq_sum_lab fc hκ hℓ N hN z
  rw [hlat] at hpois
  -- the label `0` contributes `f(0) = 1`, accounting for the `− 1`
  set G : Lab N → ℂ := fun s => ((fc.f (‖kmomLab ℓ N s‖ / κ) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N s) z : ℂ)) with hGdef
  have hkmom0 : kmomLab ℓ N (0 : Lab N) = 0 := by
    rw [kmomLab_eq_piL]
    have h0 : labVec N (0 : Lab N) = 0 := by
      funext i; simp [labVec]
    have hz : latVec (0 : Fin 3 → ℤ) = 0 := by
      rw [latVec]; exact PiLp.ext (fun i => by simp)
    rw [h0, hz, smul_zero]
  have hG0 : G 0 = 1 := by
    rw [hGdef]
    beta_reduce
    rw [hkmom0]
    simp [fc.one 0 (by norm_num)]
  have hpt : ∀ s : Lab N, (if s = 0 then (0 : ℂ) else G s) = G s - (if s = 0 then G s else 0) := by
    intro s
    by_cases h : s = 0 <;> simp [h]
  have hsum2 : (∑ s : Lab N, (if s = 0 then G s else 0)) = G 0 := by
    rw [Finset.sum_ite_eq']
    simp
  rw [← hpois]
  calc (∑ s : Lab N, (if s = 0 then (0 : ℂ) else G s))
      = ∑ s : Lab N, (G s - (if s = 0 then G s else 0)) := Finset.sum_congr rfl fun s _ => hpt s
    _ = (∑ s : Lab N, G s) - ∑ s : Lab N, (if s = 0 then G s else 0) :=
        Finset.sum_sub_distrib (s := Finset.univ) (f := G)
          (g := fun s : Lab N => if s = 0 then G s else 0)
    _ = (∑ s : Lab N, G s) - 1 := by rw [hsum2, hG0]

end

end Work.BoseBoxFock
