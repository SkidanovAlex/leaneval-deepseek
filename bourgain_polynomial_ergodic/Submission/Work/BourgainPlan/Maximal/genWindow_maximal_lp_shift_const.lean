import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_defs
import Submission.Work.BourgainPlan.Maximal.polyGeneral_window_lp_leading
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp_leading

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set Finset
open scoped ENNReal BigOperators

set_option maxHeartbeats 4000000

/-! ## A dilation maximal bound uniform in the integer shift

Bourgain's §7.1 maximal estimate `poly_dilation_lp Q` for a polynomial `Q` nonnegative on `[0,∞)`
holds with *one* constant for all integer shifts `Q + C k`: the shift is absorbed by translating
the test function `ψ ↦ ψ (· - k)`, which leaves the `Lᵖ` norm unchanged.  This is the same
mechanism that `poly_dilation_lp_leading` uses for a *single* shift `m`; here we carry the
quantifier over `k` through. -/

/-- The dilation maximal bound `poly_dilation_lp` for a nonnegative polynomial holds with a constant
independent of the integer shift `Q + C k`. -/
private lemma poly_dilation_lp_shift_uniform (Q : Polynomial ℤ)
    (hQ : ∀ x : ℝ, 0 ≤ x → 0 ≤ (Q.map (Int.castRingHom ℝ)).eval x) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ) (ψ : ℝ → ℝ≥0∞), Measurable ψ → (∀ x, ψ x ≠ ⊤) →
      (∫⁻ x, ENNReal.rpow (ψ x) p < ⊤) →
      ∫⁻ x, ENNReal.rpow (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - ((Q + Polynomial.C k).map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) p
        ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.rpow (ψ x) p := by
  obtain ⟨C, hC, hbound⟩ := poly_dilation_lp Q hQ hp
  refine ⟨C, hC, fun k ψ hψ hψfin hH => ?_⟩
  have hψ'shift : Measurable (fun y : ℝ => ψ (y - (k:ℝ))) :=
    hψ.comp (measurable_id.sub measurable_const)
  have hfin' : ∀ y : ℝ, ψ (y - (k:ℝ)) ≠ ⊤ := fun y => hψfin _
  have hRHS : (∫⁻ y, ENNReal.rpow (ψ (y - (k:ℝ))) p) = ∫⁻ y, ENNReal.rpow (ψ y) p := by
    simpa [sub_eq_add_neg] using
      (MeasureTheory.lintegral_add_right_eq_self (μ := MeasureTheory.volume)
        (fun y : ℝ => ENNReal.rpow (ψ y) p) (-(k:ℝ)))
  have hH' : ∫⁻ y, ENNReal.rpow (ψ (y - (k:ℝ))) p < ⊤ := by rw [hRHS]; exact hH
  have hkey := hbound (fun y : ℝ => ψ (y - (k:ℝ))) hψ'shift hfin' hH'
  calc ∫⁻ x, ENNReal.rpow (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - ((Q + Polynomial.C k).map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) p
      = ∫⁻ x, ENNReal.rpow (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ ((x - (Q.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)) - (k:ℝ))) p := by
          refine lintegral_congr fun x => ?_
          congr 1
          refine iSup_congr fun N => ?_
          refine lintegral_congr fun s => ?_
          rw [poly_eval_map_add_C]
          congr 1
          ring
    _ ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.rpow (ψ (x - (k:ℝ))) p := hkey
    _ = ENNReal.ofReal C * ∫⁻ x, ENNReal.rpow (ψ x) p := by rw [hRHS]

/-- `poly_dilation_lp_leading` with a constant uniform in the shift: a polynomial `P` with positive
leading coefficient satisfies the dilation maximal estimate with one constant for every integer
shift `P + C c`. -/
private lemma poly_dilation_lp_shift_const' (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 1 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℤ) (ψ : ℝ → ℝ≥0∞), Measurable ψ → (∀ x, ψ x ≠ ⊤) →
      (∫⁻ x, ENNReal.rpow (ψ x) p < ⊤) →
      ∫⁻ x, ENNReal.rpow (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x - ((P + Polynomial.C c).map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) p
        ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.rpow (ψ x) p := by
  have _hd := hd
  obtain ⟨m₀, hm₀⟩ := poly_leading_shift_nonneg P hP
  have hQ : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((P + Polynomial.C m₀).map (Int.castRingHom ℝ)).eval x := by
    intro x hx
    rw [poly_eval_map_add_C]
    exact hm₀ x hx
  obtain ⟨C, hC, hbound⟩ := poly_dilation_lp_shift_uniform (P + Polynomial.C m₀) hQ hp
  refine ⟨C, hC, fun c ψ hψ hψfin hH => ?_⟩
  have hshift : P + Polynomial.C m₀ + Polynomial.C (c - m₀) = P + Polynomial.C c := by
    rw [add_assoc, ← Polynomial.C_add, show m₀ + (c - m₀) = c by ring]
  have h := hbound (c - m₀) ψ hψ hψfin hH
  rwa [hshift] at h

/-- **Bourgain's window-model `ℓ^p` maximal bound, uniformly in the constant shift `P + C c`.**

This is `Work.BourgainPlan.Maximal.polyGeneral_window_lp_leading` (`genWindow_defs` form) with the
window model `genWindow (P + C c)` replacing the model for `P`: the constant `C` is now uniform in
the shift `c : ℤ`.  Bourgain's Lemma 7.20 has no shift hypothesis, and §7.4 (7.64) needs the bound
for every integer shift of the polynomial; the uniformity in `c` is obtained by consuming the
shift-uniform §7.1 input `poly_dilation_lp_shift_const'` inside `genBlock_slice_lp_leading` (whose
body takes the dilation bound as a parameter and never uses `P` itself). -/
theorem genWindow_maximal_lp_shift_const (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {p : ℝ} (hp : 1 < p) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφs : ∀ β : ℝ, β ∉ Set.Icc (-(1/2)) (1/2) → φ β = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℤ) (q : ℕ) (hq : 0 < q) (D : ℝ) (hD : 0 < D) (hDq : (q:ℝ) ≤ D)
        (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
      MeasureTheory.lintegral MeasureTheory.Measure.count
          (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ =>
            ‖genWindow (P + Polynomial.C c) k q D φ g s m‖ₑ) p)
        ≤ ENNReal.ofReal C * (MeasureTheory.lintegral MeasureTheory.volume
            (fun y : ℝ => ‖FourierTransform.fourierInv φ y‖ₑ))
          * MeasureTheory.lintegral MeasureTheory.Measure.count
              (fun m : ℤ => ENNReal.rpow (‖g m‖ₑ) p) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.Analysis.ExponentialSums.exists_decay_fourierInv
      (Commons.Analysis.ExponentialSums.hasCompactSupport_of_Icc hφs) hφ
  obtain ⟨C₂, hC₂pos, hC₂⟩ :=
    Commons.Analysis.Fourier.lattice_sup_le_integral_sup_band_limited_rpow (p := p) hp
  obtain ⟨C_p, hC_ppos, hC_p_shift⟩ := poly_dilation_lp_shift_const' P hP (by omega) (p := p) hp
  refine ⟨C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1), by positivity, ?_⟩
  intro c q hq D hD hDq g s hs
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp
  haveI : NeZero q := ⟨hq.ne'⟩
  change MeasureTheory.lintegral MeasureTheory.Measure.count
      (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ =>
        ‖genWindow (P + Polynomial.C c) k q D φ g s m‖ₑ) p)
      ≤ _
  have hLHS : MeasureTheory.lintegral MeasureTheory.Measure.count
      (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ =>
        ‖genWindow (P + Polynomial.C c) k q D φ g s m‖ₑ) p)
      = ∑ z : Fin q, ∑' y : ℤ,
          (⨆ k : ℕ, ‖genBlock (P + Polynomial.C c) k q D φ g s ((z:ℕ):ℤ) (y:ℝ)‖ₑ)^p := by
    rw [MeasureTheory.lintegral_count,
      Commons.Analysis.ExponentialSums.Commons.Analysis.ExponentialSums.tsum_int_eq_sum_fin q
        (fun m : ℤ => ENNReal.rpow (iSup fun k : ℕ =>
          ‖genWindow (P + Polynomial.C c) k q D φ g s m‖ₑ) p)]
    simp only [ENNReal.rpow_eq_pow]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    refine tsum_congr (fun y => ?_)
    congr 1
    apply iSup_congr
    intro k
    rw [genWindow_eq_genBlock (P + Polynomial.C c) k q hq D hD hφ.continuous hφs g s
      ((z:ℕ):ℤ) y]
  rw [hLHS]
  calc ∑ z : Fin q, ∑' y : ℤ,
        (⨆ k : ℕ, ‖genBlock (P + Polynomial.C c) k q D φ g s ((z:ℕ):ℤ) (y:ℝ)‖ₑ)^p
      = ∑ z : Fin q, ∫⁻ y : ℤ,
          (⨆ k : ℕ, ‖genBlock (P + Polynomial.C c) k q D φ g s ((z:ℕ):ℤ) (y:ℝ)‖ₑ)^p
            ∂MeasureTheory.Measure.count := by
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [MeasureTheory.lintegral_count]
    _ ≤ ∑ z : Fin q, ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          (∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (((z:ℕ):ℤ)+j)), ‖g j‖ₑ ^ p) :=
        Finset.sum_le_sum (fun z _ =>
          genBlock_slice_lp_leading (P + Polynomial.C c) hp hφ hφs hC₀pos hC₀ hC₂pos hC_ppos hC₂
            (hC_p_shift c) q hq D hD hDq g s ((z:ℕ):ℤ))
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          (∑ z : Fin q, ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (((z:ℕ):ℤ)+j)), ‖g j‖ₑ ^ p) := by
        rw [← Finset.mul_sum]
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          (∑ j ∈ s, ‖g j‖ₑ ^ p) := by
        congr 1
        rw [← Commons.Analysis.ExponentialSums.Commons.Analysis.ExponentialSums.sum_Icc_eq_sum_fin q
          (fun z : ℤ => ∑ j ∈ s.filter (fun j => (q:ℤ) ∣ (z+j)), ‖g j‖ₑ ^ p)]
        exact Commons.Analysis.ExponentialSums.sum_filter_residue_le hq g s
    _ = ENNReal.ofReal (C₂ * C_p * (2 * C₀ * (1 + Real.pi/2)) ^ (p - 1)) *
          (∫⁻ y : ℝ, ‖FourierTransformInv.fourierInv φ y‖ₑ ∂volume) *
          ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂MeasureTheory.Measure.count := by
        congr 1
        rw [MeasureTheory.lintegral_count,
          tsum_eq_sum (s := s) (fun m hm => by rw [hs m hm]; simp [hp0])]

end Work.BourgainPlan.Maximal
