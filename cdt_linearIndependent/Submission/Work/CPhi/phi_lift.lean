import Mathlib
import Submission.CDTPlan.InterfacesK
import Submission.Work.CPhi.phiC_analytic
import Submission.Work.CPhi.exists_differentiableOn_log_ball

/-!
# Area PhiLift — the `x`-side lift of `φ_C`

We prove `Submission.CDTPlan.PhiLift`: there is a holomorphic `Φ` on the unit disc with
`Φ z + Φ (-z) = phiC (z^2) = Φ z * Φ (-z)` for `z` in the disc, and `Φ z = 0 → z = 0`.

Construction (as in the project guidance).  Write `φ = phiC`, and let `V := dslope φ 0` be the
"quotient" `w ↦ φ w / w` extended holomorphically at `0` by `V 0 = φ'(0)` (Mathlib's `dslope`,
differentiable since `φ` is, by `Complex.differentiableOn_dslope`).  Then `φ w = w * V w` on the
disc and `V` is zero-free there.  Since the disc is simply connected, `V` has a holomorphic
logarithm `L` (`Work.CPhi.exists_differentiableOn_log_ball`), so `S := exp (L · / 2)` is a
holomorphic square root of `V`: `S w ^ 2 = V w`.

Then `Φ z := (φ (z^2) + z * S (z^2) * k (ψ (z^2))) / 2`, where `k` is the holomorphic square root
of `h − 4` supplied by `HauptFacts`.  Indeed `(z S (z^2))^2 = z^2 V (z^2) = φ (z^2)`, so
`Φ z * Φ (-z) = (φ (z^2)^2 − z^2 S (z^2)^2 k (ψ (z^2))^2)/4 = (φ^2 − φ (φ − 4))/4 = φ (z^2)`,
and `Φ z + Φ (-z) = φ (z^2)` because `Φ` is the "even part plus odd square root" splitting:
`Φ (-z) = (φ (z^2) − z S (z^2) k (ψ (z^2)))/2`.  Finally `Φ z = 0` forces
`φ (z^2) = Φ z * Φ (-z) = 0`, and `φ` vanishes on the disc only at `0` (because `h` does, and
`ψ` does), whence `z = 0`.
-/

namespace Work.CPhi

open Complex Metric Filter Submission.CDTPlan

open scoped Topology

theorem phi_lift (hM : HauptFacts) (hP : PsiCFacts) : PhiLift := by
  -- ### analytic facts on `φ = h ∘ ψ_C`
  obtain ⟨hφdiff, hφ0, hφderiv, hψle, hφzero, k, hkdiff, hksqψ, _hksq⟩ :=
    phiC_analytic hM hP
  have hderiv_ne : deriv phiC 0 ≠ 0 := by rw [hφderiv]; norm_num
  -- ### `V w = φ w / w` on the disc, holomorphic and zero-free
  have hmem : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hVdiff : DifferentiableOn ℂ (dslope phiC 0) (ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope (f := phiC) (c := 0) (s := ball (0 : ℂ) 1) hmem).mpr hφdiff
  have hVne : ∀ z ∈ ball (0 : ℂ) 1, dslope phiC 0 z ≠ 0 := by
    intro z hz hzero
    rcases eq_or_ne z 0 with rfl | hzne
    · rw [dslope_same] at hzero
      exact hderiv_ne hzero
    · rw [dslope_of_ne phiC hzne, slope_def_field, hφ0, sub_zero, sub_zero] at hzero
      rcases div_eq_zero_iff.mp hzero with h | h
      · exact hzne (hφzero z hz h)
      · exact hzne h
  have hVfact : ∀ z ∈ ball (0 : ℂ) 1, phiC z = z * dslope phiC 0 z := by
    intro z _
    rcases eq_or_ne z 0 with rfl | hzne
    · simp [hφ0]
    · rw [dslope_of_ne phiC hzne, slope_def_field, hφ0, sub_zero, sub_zero, mul_comm,
        div_mul_cancel₀ _ hzne]
  -- ### a holomorphic square root `S` of `V`
  obtain ⟨L, hLdiff, hLexp⟩ :=
    exists_differentiableOn_log_ball (c := 0) (r := 1) (V := dslope phiC 0)
      hVdiff hVne
  have hSsq : ∀ w ∈ ball (0 : ℂ) 1, Complex.exp (L w / 2) ^ 2 = dslope phiC 0 w := by
    intro w hw
    rw [pow_two, ← Complex.exp_add, show L w / 2 + L w / 2 = L w by ring]
    exact hLexp w hw
  -- ### mapping properties
  have hψmaps : Set.MapsTo psiC (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [mem_ball, dist_zero_right]
    have := hψle z hz
    linarith
  have hsqmaps : Set.MapsTo (fun z : ℂ => z ^ 2) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [mem_ball, dist_zero_right, norm_pow] at hz ⊢
    exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  -- ### the holomorphic lift `Φ`
  set Φ : ℂ → ℂ :=
    fun z => (phiC (z ^ 2) + z * Complex.exp (L (z ^ 2) / 2) * k (psiC (z ^ 2))) / 2 with hΦdef
  have hΦdiff : DifferentiableOn ℂ Φ (ball (0 : ℂ) 1) := by
    rw [hΦdef]
    have h1 : DifferentiableOn ℂ (fun z : ℂ => phiC (z ^ 2)) (ball (0 : ℂ) 1) :=
      hφdiff.comp (differentiableOn_pow 2) hsqmaps
    have hkψ : DifferentiableOn ℂ (fun z : ℂ => k (psiC z)) (ball (0 : ℂ) 1) :=
      hkdiff.comp hP.2.1 hψmaps
    have hS : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (L (z ^ 2) / 2)) (ball (0 : ℂ) 1) :=
      ((hLdiff.comp (differentiableOn_pow 2) hsqmaps).div_const 2).cexp
    have hk : DifferentiableOn ℂ (fun z : ℂ => k (psiC (z ^ 2))) (ball (0 : ℂ) 1) :=
      hkψ.comp (differentiableOn_pow 2) hsqmaps
    exact (h1.add ((differentiableOn_id.mul hS).mul hk)).div_const 2
  have hsum : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) := by
    intro z hz
    have hz2 : z ^ 2 ∈ ball (0 : ℂ) 1 := hsqmaps hz
    have hneg : (-z) ^ 2 = z ^ 2 := by ring
    have hq : (-z) * Complex.exp (L (z ^ 2) / 2) * k (psiC (z ^ 2)) =
        -(z * Complex.exp (L (z ^ 2) / 2) * k (psiC (z ^ 2))) := by ring
    simp only [hΦdef, hneg, hq]
    ring
  have hprod : ∀ z ∈ ball (0 : ℂ) 1, Φ z * Φ (-z) = phiC (z ^ 2) := by
    intro z hz
    have hz2 : z ^ 2 ∈ ball (0 : ℂ) 1 := hsqmaps hz
    have hneg : (-z) ^ 2 = z ^ 2 := by ring
    have hq : (-z) * Complex.exp (L (z ^ 2) / 2) * k (psiC (z ^ 2)) =
        -(z * Complex.exp (L (z ^ 2) / 2) * k (psiC (z ^ 2))) := by ring
    have hq2 : (z * Complex.exp (L (z ^ 2) / 2) * k (psiC (z ^ 2))) ^ 2 =
        phiC (z ^ 2) * (phiC (z ^ 2) - 4) := by
      rw [show (z * Complex.exp (L (z ^ 2) / 2) * k (psiC (z ^ 2))) ^ 2 =
          z ^ 2 * dslope phiC 0 (z ^ 2) * k (psiC (z ^ 2)) ^ 2 by rw [← hSsq (z ^ 2) hz2]; ring]
      rw [← hVfact (z ^ 2) hz2, ← hksqψ (z ^ 2) hz2]
    simp only [hΦdef, hneg, hq]
    linear_combination (-1 / 4) * hq2
  have hzero : ∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0 := by
    intro z hz hz0
    have hz2 : z ^ 2 ∈ ball (0 : ℂ) 1 := hsqmaps hz
    have hp : phiC (z ^ 2) = 0 := by
      have := hprod z hz
      rw [hz0, zero_mul] at this
      exact this.symm
    have hz2zero : z ^ 2 = 0 := hφzero (z ^ 2) hz2 hp
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hz2zero
  exact ⟨Φ, hΦdiff, fun z hz => ⟨hsum z hz, hprod z hz⟩, hzero⟩

end Work.CPhi
