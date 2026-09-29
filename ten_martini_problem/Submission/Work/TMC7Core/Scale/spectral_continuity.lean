import Mathlib
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle

/-!
# Spectral continuity in the frequency for the almost Mathieu operator

For fixed coupling `lam`, the spectrum (as a set of real energies) depends
continuously on the frequency `α`: if `E ∈ amoSpec α₀ lam`, then every frequency
`α` sufficiently close to `α₀` has a spectral point `E'` within `ε` of `E`.

The proof is the "easy" spectral-continuity argument used in
Avila--Jitomirskaya (the frequency `α` may be rational): transfer a finitely
supported approximate eigenvector at `α₀` to a nearby frequency, using that the
difference of the two operators is diagonal multiplication by a finitely
supported sequence.

Auxiliary results (all proved here):
* `exists_approx_eigenvector`: a self-adjoint operator has approximate
  eigenvectors at every point of its spectrum;
* `exists_finsupp_close`: finitely supported vectors are dense in `ℓ²(ℤ)`;
* `fs_approx`: approximate eigenvectors can be chosen finitely supported;
* `norm_le_of_spectrum_avoid`: if the spectrum of a self-adjoint operator avoids
  `(z-d,z+d)` then `d‖x‖ ≤ ‖(A-z)x‖` (resolvent-norm bound);
* `spectrum_close`: a vector with small `‖(A-z)x‖` produces a spectral point
  close to `z`;
* `lp_norm_le_of_supported` and `amo_perturb`: the finite-support perturbation
  bound for the almost Mathieu operator.
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core.Scale

/-! ## 1. Approximate eigenvectors of a self-adjoint operator -/

/-- For a self-adjoint bounded operator `A` on a complex Hilbert space, every
spectral point `z` is an approximate eigenvalue: there are unit vectors `x` with
`‖(A - z) x‖` arbitrarily small. -/
theorem exists_approx_eigenvector {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] (A : X →L[ℂ] X) (hA : IsSelfAdjoint A) (z : ℝ)
    (hz : (z : ℂ) ∈ spectrum ℂ A) {η : ℝ} (hη : 0 < η) :
    ∃ x : X, ‖x‖ = 1 ∧ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ < η := by
  by_contra hcon
  push_neg at hcon
  set B : X →L[ℂ] X := A - algebraMap ℂ (X →L[ℂ] X) z with hB
  have hzsa : IsSelfAdjoint ((z : ℂ)) := by
    rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  have hBsa : IsSelfAdjoint B := by
    rw [hB]; exact hA.sub (IsSelfAdjoint.algebraMap _ hzsa)
  have hbound : ∀ x : X, η * ‖x‖ ≤ ‖B x‖ := by
    intro x
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp
    · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hunit : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul]
        have hnorm : ‖(((‖x‖⁻¹ : ℝ)) : ℂ)‖ = ‖x‖⁻¹ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        rw [hnorm, inv_mul_cancel₀ hxn]
      have hc := hcon (((‖x‖⁻¹ : ℝ) : ℂ) • x) hunit
      rw [map_smul, norm_smul] at hc
      have hnorm : ‖(((‖x‖⁻¹ : ℝ)) : ℂ)‖ = ‖x‖⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      rw [hnorm] at hc
      have hmul := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
      have h2 : ‖x‖⁻¹ * ‖B x‖ * ‖x‖ = ‖B x‖ := by
        rw [mul_assoc, mul_comm (‖B x‖) ‖x‖, ← mul_assoc, inv_mul_cancel₀ hxn, one_mul]
      linarith [hmul, h2]
  have hker : B.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : B x = 0 := by simpa using hx
    have h := hbound x
    rw [hx0, norm_zero] at h
    have : ‖x‖ = 0 := by nlinarith [norm_nonneg x, hη]
    exact norm_eq_zero.mp this
  have hdense : B.range.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff]
    rw [ContinuousLinearMap.IsStarNormal.orthogonal_range hBsa.isStarNormal, hker]
  have hanti : ∃ K, AntilipschitzWith K B :=
    ⟨⟨η⁻¹, le_of_lt (inv_pos.mpr hη)⟩, by
      apply ContinuousLinearMap.antilipschitz_of_bound
      intro x
      change ‖x‖ ≤ η⁻¹ * ‖B x‖
      rw [inv_mul_eq_div, le_div_iff₀ hη]
      linarith [hbound x]⟩
  have hbij : Function.Bijective B :=
    (ContinuousLinearMap.bijective_iff_dense_range_and_antilipschitz B).mpr ⟨hdense, hanti⟩
  have hunit : IsUnit B := ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  have hunit' : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - A) := by
    have h1 : algebraMap ℂ (X →L[ℂ] X) z - A = -B := by rw [hB]; abel
    rw [h1]; exact hunit.neg
  exact (spectrum.mem_iff.mp hz) hunit'

/-! ## 2. Density of finitely supported vectors in `ℓ²(ℤ)` -/

/-- Every element of `ℓ²(ℤ)` is approximated by a finite sum of standard basis
vectors. -/
theorem exists_finsupp_close (x : EllTwo) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℤ, ‖(∑ i ∈ s, lp.single 2 i (x i)) - x‖ < ε := by
  have h := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) x
  rw [HasSum] at h
  have h2 : ∀ᶠ s in Filter.atTop, dist (∑ i ∈ s, lp.single 2 i (x i)) x < ε :=
    Metric.tendsto_nhds.mp h ε hε
  rw [Filter.eventually_atTop] at h2
  obtain ⟨s₀, hs₀⟩ := h2
  exact ⟨s₀, by simpa [dist_eq_norm] using hs₀ s₀ (le_refl s₀)⟩

/-- Finitely supported approximate eigenvectors, in relative form: for a
self-adjoint almost Mathieu operator `H` and a real spectral point `E`, there is a
nonzero vector `u` supported on a finite set `s` with `‖(H - E) u‖ < δ ‖u‖`. -/
theorem fs_approx (H : EllTwo →L[ℂ] EllTwo) (hH : IsSelfAdjoint H) (E : ℝ)
    (hE : (E : ℂ) ∈ spectrum ℂ H) {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : EllTwo, u ≠ 0 ∧ (∃ s : Finset ℤ, ∀ n : ℤ, n ∉ s → u n = 0) ∧
      ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) u‖ < δ * ‖u‖ := by
  obtain ⟨x, hx1, hx2⟩ := exists_approx_eigenvector H hH E hE (η := δ/4) (by linarith)
  set C : ℝ := ‖H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E‖ with hC
  have hCnn : 0 ≤ C := norm_nonneg _
  have hεpos : 0 < min (1/2 : ℝ) (δ / (8 * (C + 1))) := by
    apply lt_min (by norm_num); positivity
  obtain ⟨s, hs⟩ := exists_finsupp_close x hεpos
  set v : EllTwo := ∑ i ∈ s, lp.single 2 i (x i) with hv
  have hvclose : ‖v - x‖ < min (1/2 : ℝ) (δ / (8 * (C + 1))) := by rw [hv]; exact hs
  have hvn : 1/2 ≤ ‖v‖ := by
    have h1 : |‖v‖ - ‖x‖| ≤ ‖v - x‖ := abs_norm_sub_norm_le v x
    rw [hx1] at h1
    have h3 : ‖v - x‖ < 1/2 := lt_of_lt_of_le hvclose (min_le_left _ _)
    rw [abs_le] at h1
    linarith [h1.1, h3]
  refine ⟨v, ?_, ⟨s, ?_⟩, ?_⟩
  · intro hcon; have := hvn; rw [hcon, norm_zero] at this; norm_num at this
  · intro n hn
    rw [hv, lp.coeFn_sum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [lp.single_apply, Pi.single_eq_of_ne]
    intro h; exact hn (h ▸ hi)
  · have hCx2 : C * ‖v - x‖ < δ / 8 := by
      have hvc : ‖v - x‖ < δ / (8 * (C + 1)) := lt_of_lt_of_le hvclose (min_le_right _ _)
      calc C * ‖v - x‖ ≤ (C + 1) * ‖v - x‖ := by gcongr; linarith
        _ < (C + 1) * (δ / (8 * (C + 1))) := by gcongr
        _ = δ / 8 := by field_simp
    have hbound : ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v‖ < 3 * δ / 8 := by
      have hdecomp : (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) v =
          (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (v - x) +
          (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) x := by
        rw [← map_add]; congr 1; abel
      rw [hdecomp]
      have hCx : ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (v - x)‖ ≤ C * ‖v - x‖ := by
        rw [hC]; exact ContinuousLinearMap.le_opNorm _ _
      calc ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (v - x) +
            (H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) x‖
          ≤ ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) (v - x)‖ +
            ‖(H - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) x‖ := norm_add_le _ _
        _ ≤ C * ‖v - x‖ + δ / 4 := by linarith [hCx, hx2.le]
        _ < δ / 8 + δ / 4 := by linarith [hCx2]
        _ = 3 * δ / 8 := by ring
    have hfin : 3 * δ / 8 < δ * ‖v‖ := by
      have h2 : δ * (1/2) ≤ δ * ‖v‖ := mul_le_mul_of_nonneg_left hvn hδ.le
      nlinarith [hδ, h2]
    linarith

/-! ## 3. The resolvent-norm / spectral-distance bound -/

/-- If the spectrum of a self-adjoint operator `A` avoids the interval
`(z-d, z+d)`, then `‖(A - z) x‖ ≥ d ‖x‖` for every `x`. -/
theorem norm_le_of_spectrum_avoid {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    [CompleteSpace X] [Nontrivial X]
    (A : X →L[ℂ] X) (hA : IsSelfAdjoint A) (z : ℝ) {d : ℝ} (hd : 0 < d)
    (hspec : ∀ w ∈ spectrum ℂ A, d ≤ ‖w - (z : ℂ)‖) :
    ∀ x : X, d * ‖x‖ ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ := by
  intro x
  set B : X →L[ℂ] X := A - algebraMap ℂ (X →L[ℂ] X) z with hB
  have hzsa : IsSelfAdjoint ((z : ℂ)) := by rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]
  have hBsa : IsSelfAdjoint B := by rw [hB]; exact hA.sub (IsSelfAdjoint.algebraMap _ hzsa)
  have hzn : (z : ℂ) ∉ spectrum ℂ A := by
    intro hz
    have h1 := hspec (z:ℂ) hz
    have h2 : ‖(z:ℂ) - (z:ℂ)‖ = 0 := by simp
    rw [h2] at h1; linarith
  have hunit : IsUnit B := by
    have h1 : algebraMap ℂ (X →L[ℂ] X) z - A = -B := by rw [hB]; abel
    have h2 : IsUnit (algebraMap ℂ (X →L[ℂ] X) z - A) := spectrum.notMem_iff.mp hzn
    rw [h1] at h2; simpa using h2.neg
  obtain ⟨u, hu⟩ := hunit
  have hunit' : IsUnit B := ⟨u, hu⟩
  have hB'inv : Ring.inverse B = ↑u⁻¹ := by rw [← hu]; exact Ring.inverse_unit u
  have hB'sa : IsSelfAdjoint (Ring.inverse B) := by
    rw [IsSelfAdjoint, ← Ring.inverse_star, hBsa.star_eq]
  have hkey : ‖Ring.inverse B‖ ≤ d⁻¹ := by
    obtain ⟨k, hkmem, hkval⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty
      (𝕜 := ℂ) (spectrum.nonempty (Ring.inverse B))
    have hsr := hB'sa.spectralRadius_eq_nnnorm
    have hkk : ‖k‖₊ = ‖Ring.inverse B‖₊ := ENNReal.coe_inj.mp (by rw [hkval, hsr])
    have hk : ‖k‖ = ‖Ring.inverse B‖ := by
      have hh := congrArg ((↑) : NNReal → ℝ) hkk
      simpa using hh
    rw [← hk]
    have hmem : k⁻¹ ∈ spectrum ℂ B := by
      rw [hB'inv] at hkmem
      rw [← spectrum.map_inv u] at hkmem
      rw [hu] at hkmem
      exact Set.mem_inv.mp hkmem
    rw [hB, ← spectrum.sub_singleton_eq A (z:ℂ)] at hmem
    obtain ⟨w, hwmem, b, hb, hbeq⟩ := hmem
    rw [Set.mem_singleton_iff] at hb
    subst hb
    have hbound : d ≤ ‖k⁻¹‖ := by rw [← hbeq]; exact hspec w hwmem
    rw [← inv_inv k, norm_inv]
    exact (inv_le_inv₀ (by linarith) hd).mpr hbound
  have hxB : (Ring.inverse B) (B x) = x := by
    have hcomp : (Ring.inverse B) * B = 1 := Ring.inverse_mul_cancel B hunit'
    calc (Ring.inverse B) (B x) = ((Ring.inverse B) * B) x := (mul_apply_eq_comp _ _ _).symm
      _ = (1 : X →L[ℂ] X) x := by rw [hcomp]
      _ = x := one_apply_eq_self x
  have hx_le : ‖x‖ ≤ d⁻¹ * ‖B x‖ := by
    calc ‖x‖ = ‖Ring.inverse B (B x)‖ := by rw [hxB]
      _ ≤ ‖Ring.inverse B‖ * ‖B x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ d⁻¹ * ‖B x‖ := mul_le_mul_of_nonneg_right hkey (norm_nonneg _)
  have hstep := mul_le_mul_of_nonneg_left hx_le hd.le
  rw [← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul] at hstep
  exact hstep

/-- A vector `x ≠ 0` with `‖(A - z) x‖ = r ‖x‖` produces a spectral point of a
self-adjoint `A` within `r` of `z`. -/
theorem spectrum_close {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsSelfAdjoint A) (z : ℝ) (x : X) (hx : x ≠ 0) :
    ∃ w ∈ spectrum ℂ A, ‖w - (z : ℂ)‖ ≤ ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ / ‖x‖ := by
  haveI : Nontrivial X := ⟨x, 0, hx⟩
  by_contra hcon
  push_neg at hcon
  set r := ‖(A - algebraMap ℂ (X →L[ℂ] X) z) x‖ / ‖x‖ with hr
  obtain ⟨w₀, hw₀mem, hw₀min⟩ := (spectrum.isCompact A).exists_isMinOn (spectrum.nonempty A)
      (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  have hdpos : 0 < ‖w₀ - (z:ℂ)‖ :=
    lt_of_le_of_lt (div_nonneg (norm_nonneg _) (norm_nonneg _)) (hcon w₀ hw₀mem)
  have hspec : ∀ w ∈ spectrum ℂ A, ‖w₀ - (z:ℂ)‖ ≤ ‖w - (z : ℂ)‖ := fun w hw => hw₀min hw
  have key := norm_le_of_spectrum_avoid A hA z hdpos hspec x
  have hle : ‖w₀ - (z:ℂ)‖ ≤ r := by
    have h1 : ‖w₀ - (z:ℂ)‖ * ‖x‖ ≤ r * ‖x‖ := by
      rw [hr, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx)]
      exact key
    exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hx)
  exact absurd hle (not_le.mpr (hcon w₀ hw₀mem))

/-! ## 4. The finite-support perturbation bound for the AMO -/

/-- Norm bound for a vector supported in a finite set. -/
theorem lp_norm_le_of_supported (w u : EllTwo) (s : Finset ℤ) (hs : ∀ n : ℤ, n ∉ s → w n = 0)
    (M : ℝ) (hM : 0 ≤ M) (hper : ∀ n ∈ s, ‖w n‖ ≤ M * ‖u n‖) :
    ‖w‖ ≤ M * ‖u‖ := by
  have hp : (0:ℝ) < (2:ENNReal).toReal := by norm_num
  have hto : (2:ENNReal).toReal = 2 := by norm_num
  have hwp : ‖w‖ ^ 2 = ∑' n : ℤ, ‖w n‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) hp w
    rw [hto] at h
    simp_rw [Real.rpow_two] at h
    exact h
  have hup : ‖u‖ ^ 2 = ∑' n : ℤ, ‖u n‖ ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) hp u
    rw [hto] at h
    simp_rw [Real.rpow_two] at h
    exact h
  have hle : ∀ n : ℤ, ‖w n‖ ^ 2 ≤ M ^ 2 * ‖u n‖ ^ 2 := by
    intro n
    rcases em (n ∈ s) with hn | hn
    · calc ‖w n‖ ^ 2 ≤ (M * ‖u n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hper n hn) 2
        _ = M ^ 2 * ‖u n‖ ^ 2 := by ring
    · rw [hs n hn, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      positivity
  have hsummable_w : Summable fun n : ℤ => ‖w n‖ ^ 2 := by
    have h := lp.hasSum_norm (p := 2) (E := fun _ : ℤ => ℂ) hp w
    rw [hto] at h
    simp_rw [Real.rpow_two] at h
    exact h.summable
  have hsummable_u : Summable fun n : ℤ => ‖u n‖ ^ 2 := by
    have h := lp.hasSum_norm (p := 2) (E := fun _ : ℤ => ℂ) hp u
    rw [hto] at h
    simp_rw [Real.rpow_two] at h
    exact h.summable
  have hsummable_um : Summable fun n : ℤ => M ^ 2 * ‖u n‖ ^ 2 := hsummable_u.mul_left _
  have hsum_le : ∑' n : ℤ, ‖w n‖ ^ 2 ≤ ∑' n : ℤ, M ^ 2 * ‖u n‖ ^ 2 :=
    Summable.tsum_le_tsum hle hsummable_w hsummable_um
  have key : ‖w‖ ^ 2 ≤ M ^ 2 * ‖u‖ ^ 2 := by
    rw [hwp, hup]
    calc ∑' n : ℤ, ‖w n‖ ^ 2 ≤ ∑' n : ℤ, M ^ 2 * ‖u n‖ ^ 2 := hsum_le
      _ = M ^ 2 * ∑' n : ℤ, ‖u n‖ ^ 2 := tsum_mul_left
  have key2 : ‖w‖ ^ 2 ≤ (M * ‖u‖) ^ 2 := by
    calc ‖w‖ ^ 2 ≤ M ^ 2 * ‖u‖ ^ 2 := key
      _ = (M * ‖u‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp key2

/-- Continuity of the almost Mathieu operator in the frequency, in the weak sense
needed here: on a fixed finitely supported vector the operators at nearby
frequencies are norm-close. -/
theorem amo_perturb (α₀ lam : ℝ) (u : EllTwo) (s : Finset ℤ)
    (hs : ∀ n : ℤ, n ∉ s → u n = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℝ, |α - α₀| < δ →
      ∀ H H' : EllTwo →L[ℂ] EllTwo,
        IsAlmostMathieuOperator α₀ lam 0 H → IsAlmostMathieuOperator α lam 0 H' →
        ‖H' u - H u‖ < ε := by
  intro ε hε
  set M : ℝ := ε / (‖u‖ + 1) with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have hMnn : 0 ≤ M := hMpos.le
  have hGcont : Continuous fun α : ℝ => ∑ n ∈ s, |amoPot α lam 0 n - amoPot α₀ lam 0 n| := by
    unfold amoPot; fun_prop
  have hG0 : (∑ n ∈ s, |amoPot α₀ lam 0 n - amoPot α₀ lam 0 n|) = 0 := by simp
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hGcont.continuousAt M hMpos
  refine ⟨δ, hδpos, fun α hα H H' hH hH' => ?_⟩
  have hGα : (∑ n ∈ s, |amoPot α lam 0 n - amoPot α₀ lam 0 n|) < M := by
    have h1 := hδ (x := α) (by rwa [Real.dist_eq])
    rwa [hG0, Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg (fun n _ => abs_nonneg _))] at h1
  have hc : ∀ n : ℤ, (H' u - H u) n = (((amoPot α lam 0 n - amoPot α₀ lam 0 n : ℝ)) : ℂ) * u n := by
    intro n
    rw [lp.coeFn_sub, Pi.sub_apply, hH' u n, hH u n, amoPot, amoPot]
    push_cast; ring
  have hsupp : ∀ n : ℤ, n ∉ s → (H' u - H u) n = 0 := by
    intro n hn; rw [hc n, hs n hn, mul_zero]
  have hper : ∀ n ∈ s, ‖(H' u - H u) n‖ ≤ M * ‖u n‖ := by
    intro n hn
    rw [hc n, norm_mul]
    have hΔ : ‖(((amoPot α lam 0 n - amoPot α₀ lam 0 n : ℝ)) : ℂ)‖ ≤ M := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_trans (Finset.single_le_sum
        (f := fun i : ℤ => |amoPot α lam 0 i - amoPot α₀ lam 0 i|) (fun i _ => abs_nonneg _) hn) hGα.le
    exact mul_le_mul_of_nonneg_right hΔ (norm_nonneg _)
  have hnorm : ‖H' u - H u‖ ≤ M * ‖u‖ := lp_norm_le_of_supported _ _ s hsupp M hMnn hper
  have hMu : M * ‖u‖ < ε := by
    rw [hM, div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < ‖u‖ + 1)]
    nlinarith [norm_nonneg u, hε]
  linarith [hnorm, hMu]

/-! ## 5. Spectral continuity in the frequency -/

theorem spectral_continuity (h1 : P_OpBasics) (lam α₀ : ℝ) (E : ℝ) (hE : E ∈ amoSpec α₀ lam) : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ α : ℝ, |α - α₀| < δ → ∃ E' : ℝ, |E' - E| < ε ∧ E' ∈ amoSpec α lam := by
  intro ε hε
  obtain ⟨H, hH, hHspec⟩ := hE
  have hHsa : IsSelfAdjoint H := h1.2.1 α₀ lam 0 H hH
  obtain ⟨u, hu_ne, ⟨s, hs⟩, hu_approx⟩ := fs_approx H hHsa E hHspec (δ := ε/2) (by linarith)
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
  obtain ⟨δ, hδpos, hδ⟩ := amo_perturb α₀ lam u s hs (ε/2 * ‖u‖) (by positivity)
  refine ⟨δ, hδpos, fun α hα => ?_⟩
  obtain ⟨H', hH'⟩ := h1.1 α lam 0
  have hH'sa : IsSelfAdjoint H' := h1.2.1 α lam 0 H' hH'
  have hdiff : ‖H' u - H u‖ < ε/2 * ‖u‖ := hδ α hα H H' hH hH'
  have hclose : ‖(H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) u‖ < ε * ‖u‖ := by
    have hd : (H' - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E) u =
        (H' u - H u) + (H u - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E u) := by
      rw [sub_apply]; abel
    have hua : ‖H u - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E u‖ < ε/2 * ‖u‖ := by
      rwa [sub_apply] at hu_approx
    rw [hd]
    calc ‖(H' u - H u) + (H u - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E u)‖
        ≤ ‖H' u - H u‖ + ‖H u - algebraMap ℂ (EllTwo →L[ℂ] EllTwo) E u‖ := norm_add_le _ _
      _ < ε/2 * ‖u‖ + ε/2 * ‖u‖ := by linarith
      _ = ε * ‖u‖ := by ring
  obtain ⟨w, hwmem, hwle⟩ := spectrum_close H' hH'sa E u hu_ne
  have h3 : ‖w - (E:ℂ)‖ < ε := by
    have h := (div_lt_iff₀ hu_pos).mpr hclose
    linarith [hwle]
  have hre : w = (w.re : ℂ) := hH'sa.mem_spectrum_eq_re hwmem
  have h4 : |w.re - E| < ε := by
    have h5 : ‖(w.re : ℂ) - (E : ℂ)‖ < ε := by rw [← hre]; exact h3
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h5
    exact h5
  exact ⟨w.re, h4, H', hH', by rw [← hre]; exact hwmem⟩

end Work.TMC7Core.Scale
