import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.CPhi.exists_differentiableOn_log_ball

/-! Guidance from the project lead (the requester):

# Area APhi — generic lift of h∘ψ (`PhiLiftGen`)
Generalise `Work.CPhi.phi_lift` (proved for ψ_C) to any ψ holomorphic on the disc, ψ(0)=0, ψ'(0)≠0,
|ψ|<1, ψ(z)=0 ⇒ z=0 — its proof only uses these facts plus HauptFacts (h(q)=0 ⇔ q=0, h'(0)=−256,
h−4 = k²). Copy and generalise (φ(w) = w·S(w)², Φ(z) = (φ(z²) + z S(z²) k(ψ(z²)))/2).
Contracts: `Submission/CDTPlan/InterfacesA2.lean` (Theorem A template), `InterfacesA.lean` (ψ_A, φ_A,
ANumerics, Zagier integrality), `InterfacesC.lean` (intY, tq, dY), `Interfaces.lean`.
The Theorem-C side has already solved the analogous pieces — REUSE, do not rebuild:
`Submission/Work/CPhi/` (lift of φ_C), `Submission/Work/CPull/` (germs.lean: `germ_of_even`,
`pullbackMero_of_germ`, `germ_intY`, `germ_tq`, pullbackMero_B2/B3/B4, deriv_phiC_zeros_finite),
`Submission/Work/CLift/` (continuation of P along Φ with OdeContinuation),
`Submission/Work/CDcl/` (symmetrised-powers route to the d/dy-closure), `Submission/Work/CDen/`.
Axiom-clean A-side facts: `Submission.Work.Purge.a_side_clean` bundles HA_ode, HB_ode, HC_ode,
GA_odeLHS_eq_zero, Cintegral/Aintegral identities, overconvergesB/C (use it instead of the
native_decide-tainted originals); `Work.ZagBI` re-proved HA_ode cleanly too. Never depend on
`native_decide` (check #print axioms).
-/

namespace Work.APhi

open Complex Metric Filter Submission.CDTPlan

open scoped Topology

/-- **Generic lift of `h ∘ ψ`.**  For any `ψ` holomorphic on the unit disc with `ψ 0 = 0`,
`ψ'(0) ≠ 0`, `‖ψ‖ < 1` and `ψ` zero-free on the disc, the composite `φ = h ∘ ψ` admits a
holomorphic lift `Φ` through `y = x²/(x−1)`: `Φ` and `w ↦ Φ(−w)` are the two roots of
`x² − φ(z²) x + φ(z²)`.  This is `Work.CPhi.phi_lift` with `ψ_C` replaced by an arbitrary
admissible `ψ`; the proof uses only `HauptFacts`. -/
theorem phi_lift_gen (hM : HauptFacts) : PhiLiftGen := by
  obtain ⟨hMdiff, hMderiv, hMzero, k, hkdiff, hksq⟩ := hM
  intro ψ hψdiff hψ0 hψderiv hψle hψzero
  set φ : ℂ → ℂ := fun z => hauptH (ψ z) with hφdef
  -- ### the admissible map `ψ` sends the disc into itself
  have hψmaps : Set.MapsTo ψ (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [mem_ball, dist_zero_right] using hψle z hz
  -- ### analytic facts on `φ = h ∘ ψ`
  have hφdiff : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) := by
    rw [hφdef]; exact hMdiff.comp hψdiff hψmaps
  have hφ0 : φ 0 = 0 := by rw [hφdef]; simp [hauptH, hψ0]
  have hderiv_ne : deriv φ 0 ≠ 0 := by
    have h1 : DifferentiableAt ℂ ψ 0 := hψdiff.differentiableAt (ball_mem_nhds _ zero_lt_one)
    have h2 : DifferentiableAt ℂ hauptH (ψ 0) := by
      rw [hψ0]; exact hMdiff.differentiableAt (ball_mem_nhds _ zero_lt_one)
    rw [hφdef]
    change deriv (hauptH ∘ ψ) 0 ≠ 0
    rw [deriv_comp (x := (0 : ℂ)) h2 h1, hψ0, hMderiv]
    exact mul_ne_zero (by norm_num) hψderiv
  have hφzero : ∀ z ∈ ball (0 : ℂ) 1, φ z = 0 → z = 0 := by
    intro z hz hz0
    simp only [hφdef] at hz0
    exact hψzero z hz (hMzero (ψ z) (hψmaps hz) hz0)
  have hksq' : ∀ z ∈ ball (0 : ℂ) 1, φ z - 4 = k (ψ z) ^ 2 := by
    intro z hz; rw [hφdef]; exact hksq (ψ z) (hψmaps hz)
  -- ### `V w = φ w / w` on the disc, holomorphic and zero-free
  have hmem : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := isOpen_ball.mem_nhds (mem_ball_self one_pos)
  have hVdiff : DifferentiableOn ℂ (dslope φ 0) (ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope (f := φ) (c := 0) (s := ball (0 : ℂ) 1) hmem).mpr hφdiff
  have hVne : ∀ z ∈ ball (0 : ℂ) 1, dslope φ 0 z ≠ 0 := by
    intro z hz hzero
    rcases eq_or_ne z 0 with rfl | hzne
    · rw [dslope_same] at hzero
      exact hderiv_ne hzero
    · rw [dslope_of_ne φ hzne, slope_def_field, hφ0, sub_zero, sub_zero] at hzero
      rcases div_eq_zero_iff.mp hzero with h | h
      · exact hzne (hφzero z hz h)
      · exact hzne h
  have hVfact : ∀ z ∈ ball (0 : ℂ) 1, φ z = z * dslope φ 0 z := by
    intro z _
    rcases eq_or_ne z 0 with rfl | hzne
    · simp [hφ0]
    · rw [dslope_of_ne φ hzne, slope_def_field, hφ0, sub_zero, sub_zero, mul_comm,
        div_mul_cancel₀ _ hzne]
  -- ### a holomorphic square root `S` of `V`
  obtain ⟨L, hLdiff, hLexp⟩ :=
    Work.CPhi.exists_differentiableOn_log_ball (c := 0) (r := 1) (V := dslope φ 0)
      hVdiff hVne
  have hSsq : ∀ w ∈ ball (0 : ℂ) 1, Complex.exp (L w / 2) ^ 2 = dslope φ 0 w := by
    intro w hw
    rw [pow_two, ← Complex.exp_add, show L w / 2 + L w / 2 = L w by ring]
    exact hLexp w hw
  -- ### mapping properties
  have hsqmaps : Set.MapsTo (fun z : ℂ => z ^ 2) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
    intro z hz
    simp only [mem_ball, dist_zero_right, norm_pow] at hz ⊢
    exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  -- ### the holomorphic lift `Φ`
  set Φ : ℂ → ℂ :=
    fun z => (φ (z ^ 2) + z * Complex.exp (L (z ^ 2) / 2) * k (ψ (z ^ 2))) / 2 with hΦdef
  have hΦdiff : DifferentiableOn ℂ Φ (ball (0 : ℂ) 1) := by
    rw [hΦdef]
    have h1 : DifferentiableOn ℂ (fun z : ℂ => φ (z ^ 2)) (ball (0 : ℂ) 1) :=
      hφdiff.comp (differentiableOn_pow 2) hsqmaps
    have hkψ : DifferentiableOn ℂ (fun z : ℂ => k (ψ z)) (ball (0 : ℂ) 1) :=
      hkdiff.comp hψdiff hψmaps
    have hS : DifferentiableOn ℂ (fun z : ℂ => Complex.exp (L (z ^ 2) / 2)) (ball (0 : ℂ) 1) :=
      ((hLdiff.comp (differentiableOn_pow 2) hsqmaps).div_const 2).cexp
    have hk : DifferentiableOn ℂ (fun z : ℂ => k (ψ (z ^ 2))) (ball (0 : ℂ) 1) :=
      hkψ.comp (differentiableOn_pow 2) hsqmaps
    exact (h1.add ((differentiableOn_id.mul hS).mul hk)).div_const 2
  have hsum : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = φ (z ^ 2) := by
    intro z hz
    have hneg : (-z) ^ 2 = z ^ 2 := by ring
    have hq : (-z) * Complex.exp (L (z ^ 2) / 2) * k (ψ (z ^ 2)) =
        -(z * Complex.exp (L (z ^ 2) / 2) * k (ψ (z ^ 2))) := by ring
    simp only [hΦdef, hneg, hq]
    ring
  have hprod : ∀ z ∈ ball (0 : ℂ) 1, Φ z * Φ (-z) = φ (z ^ 2) := by
    intro z hz
    have hz2 : z ^ 2 ∈ ball (0 : ℂ) 1 := hsqmaps hz
    have hneg : (-z) ^ 2 = z ^ 2 := by ring
    have hq : (-z) * Complex.exp (L (z ^ 2) / 2) * k (ψ (z ^ 2)) =
        -(z * Complex.exp (L (z ^ 2) / 2) * k (ψ (z ^ 2))) := by ring
    have hq2 : (z * Complex.exp (L (z ^ 2) / 2) * k (ψ (z ^ 2))) ^ 2 =
        φ (z ^ 2) * (φ (z ^ 2) - 4) := by
      rw [show (z * Complex.exp (L (z ^ 2) / 2) * k (ψ (z ^ 2))) ^ 2 =
          z ^ 2 * dslope φ 0 (z ^ 2) * k (ψ (z ^ 2)) ^ 2 by
            rw [← hSsq (z ^ 2) hz2]; ring]
      rw [← hVfact (z ^ 2) hz2, ← hksq' (z ^ 2) hz2]
    simp only [hΦdef, hneg, hq]
    linear_combination (-1 / 4) * hq2
  have hzero : ∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0 := by
    intro z hz hz0
    have hz2 : z ^ 2 ∈ ball (0 : ℂ) 1 := hsqmaps hz
    have hp : φ (z ^ 2) = 0 := by
      have := hprod z hz
      rw [hz0, zero_mul] at this
      exact this.symm
    have hz2zero : z ^ 2 = 0 := hφzero (z ^ 2) hz2 hp
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hz2zero
  exact ⟨Φ, hΦdiff, fun z hz => ⟨hsum z hz, hprod z hz⟩, hzero⟩

end Work.APhi
