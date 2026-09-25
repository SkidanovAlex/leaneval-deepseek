import Mathlib
import Submission.Work.QuadraticFields.CertificateReal
import Submission.Work.QuadraticFields.multiQuad_finrank
import Submission.Work.QuadraticFields.finrank_adjoin_sq_eq_two
import Submission.Work.QuadraticFields.multiQuad_isGalois
import Submission.Work.QuadraticFields.gsPrimesQ_nonsquare
import Submission.Work.QuadraticFields.gsRoot_generates
import Submission.Work.QuadraticFields.isUnramifiedAtFinitePrimes_multiQuad
import Submission.Work.QuadraticFields.WideNarrow
import Submission.Work.QuadraticFields.gsProd_nonsquare
import Submission.Work.QuadraticFields.gsF_isTotallyReal
import Submission.Work.QuadraticFields.gsM_isTotallyReal
import Submission.Work.QuadraticFields.gs_unramified_at_infinite_places


/-!
# The totally real numerical certificate, in final form

The base field `F = ℚ(√2576450045)` (inside `M`), `2576450045 = 5·13·17·29·37·41·53`, is a real
quadratic field with `ω(2576450045) = 7`, so genus theory gives `rank₂ Cl F ≥ 6`.  The
multiquadratic field `M = ℚ(√5, √13, √17, √29, √37, √41, √53)` is an unramified extension of `F`
of degree `2 ^ 6 = 64`, exhibiting six independent unramified quadratic extensions of `F`.

## Main results

* `gs_certificate`: `M/F` is unramified at all finite primes and `[M : F] = 64`.
* `gsF_discr`: `disc F = 2576450045`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

theorem gsPrimesQ_nonsquare' (T : Finset gsPrimesQ) (hT : T.Nonempty) :
    ∀ r : ℚ, r ^ 2 ≠ ∏ i ∈ T, ((i : gsPrimesQ) : ℚ) := by
  intro r hr
  have hsub : (T.image (fun i : gsPrimesQ => (i : ℚ))) ⊆ gsPrimesQ := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact j.2
  have hne : (T.image (fun i : gsPrimesQ => (i : ℚ))).Nonempty := hT.image _
  have hprod : (∏ i ∈ T, ((i : gsPrimesQ) : ℚ)) =
      ∏ a ∈ T.image (fun i : gsPrimesQ => (i : ℚ)), a :=
    (Finset.prod_image (f := fun a : ℚ => a) (g := fun i : gsPrimesQ => (i : ℚ))
      (s := T) (fun x _ y _ hxy => Subtype.ext hxy)).symm
  exact gsPrimesQ_nonsquare hsub hne r (by rw [← hprod]; exact hr)

theorem gsM_finrank : Module.finrank ℚ gsM = 128 := by
  have h := multiQuad_finrank gsPrimesQ gsPrimesQ_nonsquare'
  rw [gsPrimesQ_card] at h
  norm_num at h
  exact h

theorem gsF_finrank : Module.finrank ℚ ↥gsF = 2 := by
  have hprod : (∏ a ∈ gsPrimes, gsRoot a) ^ 2 = algebraMap ℚ gsM (2576450045 : ℚ) := by
    rw [← Finset.prod_pow]
    rw [Finset.prod_congr rfl (fun a ha => gsRoot_sq a ha)]
    rw [← map_prod]
    congr 1
    exact_mod_cast gsPrimes_prod
  have h := finrank_adjoin_sq_eq_two (M := gsM) (2576450045 : ℚ) (∏ a ∈ gsPrimes, gsRoot a)
    hprod gsProd_nonsquare
  unfold gsF prodSubfield
  exact h

/-- **`M/F` is unramified at all finite primes.** -/
theorem gs_unramified : IsUnramifiedAtFinitePrimes ↥gsF gsM := by
  haveI : IsGalois ℚ gsM := multiQuad_isGalois gsPrimesQ
  exact isUnramifiedAtFinitePrimes_multiQuad (M := gsM) gsPrimes gsRoot gsRoot_sq
    gsRoot_generates (by rw [gsPrimes_card]; norm_num) gsPrimes_isPrimeDiscriminant
    (fun a ha b hb hne => gsPrimes_coprime a b ha hb hne)

/-- **`[M : F] = 64 = 2 ^ 6`.** -/
theorem gs_finrank : Module.finrank ↥gsF gsM = 64 := by
  have h := Module.finrank_mul_finrank ℚ ↥gsF gsM
  rw [gsF_finrank, gsM_finrank] at h
  omega

/-- **The totally real numerical certificate.**  `M = ℚ(√5, √13, √17, √29, √37, √41, √53)` is an
unramified extension (at all finite primes and at the infinite places) of the real quadratic field
`F = ℚ(√2576450045)` of degree `2 ^ 6 = 64`. -/
theorem gs_certificate : IsUnramifiedAtFinitePrimes ↥gsF gsM ∧
    IsUnramifiedAtInfinitePlaces ↥gsF gsM ∧ Module.finrank ↥gsF gsM = 64 :=
  ⟨gs_unramified, gs_unramified_at_infinite_places, gs_finrank⟩

end

end Work.QuadraticFields
