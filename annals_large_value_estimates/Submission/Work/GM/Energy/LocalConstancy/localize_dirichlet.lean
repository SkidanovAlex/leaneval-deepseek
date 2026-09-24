import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.RLocal.Bump
import Submission.Work.GM.Energy.LocalConstancy.LocalizeSetup
import Submission.Work.GM.Energy.LocalConstancy.localize_identity
import Submission.Work.GM.Energy.LocalConstancy.tail_integral_le_of_decay

/-!
# GM Lemma 11.3: locality of a Dirichlet polynomial

This file proves `localize_dirichlet` (GM Lemma 11.3 in the form requested by the Energy area):
for arbitrary coefficients `a n` and any `K ≥ 1`, the value `Σ_{n∈[N,2N]} a n n^{it}` is controlled
by its average over `[t-K,t+K]`, up to `K^{-m}·Σ‖a n‖`.

The proof follows the paper.  Write `n = N·(n/N)`, so `n^{iu} = N^{iu}·(n/N)^{iu}`: since
`‖N^{iu}‖ = 1`, both the value and the integrand may be replaced by the *normalised* polynomial
`G N a u = Σ a n (n/N)^{iu}` (defined in `.../LocalizeSetup.lean`), whose frequencies
`log (n/N) ∈ [0, log 2]` occupy a fixed interval, independent of `N`.

For `G` we have (`localize_identity`) the exact Fourier identity
`G N a t = ∫ ξ, 𝓕ψ(ξ)·G N a (t+ξ) dξ`, where `ψ` is the flat-top bump `RLocal.PsiBump`
(`= 1` on `[0,1]`, supported in `[-1/3,4/3]`, with Fourier decay, integrability and inversion
already established in `.../RLocal/Bump.lean`).  Splitting the `ξ`-integral at `|ξ| = K`, the part
`|ξ| ≤ K` is bounded by `(sup‖𝓕ψ‖)·∫_{t-K}^{t+K}‖G‖` (after the change of variables `u = t+ξ`) and
the tail by `(sup_u ‖G u‖)·∫_{|ξ|>K}‖𝓕ψ‖ ≤ (Σ‖a n‖)·C_m K^{-m}`, using the decay of `𝓕ψ` with
`j = m+1` (`tail_integral_le_of_decay`).  All constants depend only on `m`, hence uniformly on `N`.
-/

namespace Work.GM.Energy.LocalConstancy

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The core estimate for the normalised polynomial -/

theorem localize_dirichlet_core (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ), ∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
      ‖Loc.G N a t‖ ≤ C * (∫ u in t - K..t + K, ‖Loc.G N a u‖)
        + C / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖a n‖) := by
  obtain ⟨M, hMpos, hM⟩ := Loc.PsiBump_fourier_norm_le
  obtain ⟨Cj, hCj0, hCj⟩ := Work.GM.Energy.RLocal.PsiBump_fourier_decay (m + 1)
  have hIntF : Integrable (𝓕 Work.GM.Energy.RLocal.PsiBump) :=
    Work.GM.Energy.RLocal.PsiBump_fourier_integrable
  have hContF : Continuous (𝓕 Work.GM.Energy.RLocal.PsiBump) :=
    Work.GM.Energy.RLocal.continuous_fourier_PsiBump
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  refine ⟨max M (2 * Cj / (m : ℝ)) + 1, by positivity, ?_⟩
  intro N hN a K hK t
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
  have hGcont : Continuous (Loc.G N a) := Loc.G_continuous hN a
  set A : ℝ := ∑ n ∈ Finset.Icc N (2 * N), ‖a n‖ with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; exact Finset.sum_nonneg fun n _ => norm_nonneg _
  have hGle : ∀ u : ℝ, ‖Loc.G N a u‖ ≤ A := fun u => by
    rw [hA]; exact Loc.G_norm_le hN a u
  set Ct : ℝ := 2 * Cj / (m : ℝ) with hCt
  have hCt0 : 0 ≤ Ct := by rw [hCt]; positivity
  -- the tail bound for the Fourier transform of the bump
  have htail : ∫ ξ in {ξ : ℝ | K < |ξ|}, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ‖
      ≤ Ct * K ^ (-(m : ℝ)) := by
    have h1 := tail_integral_le_of_decay hCj0 (by omega : 2 ≤ m + 1) hK fun ξ hξ => hCj ξ hξ
    have he : (((m + 1 : ℕ) : ℝ)) - 1 = (m : ℝ) := by push_cast; ring
    have he2 : 1 - (((m + 1 : ℕ) : ℝ)) = -(m : ℝ) := by push_cast; ring
    rw [he, he2] at h1
    exact h1
  -- integrability of the integrand and its norm
  have hfint : Integrable (fun ξ : ℝ =>
      (𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)) := by
    refine Integrable.mono' (g := fun ξ : ℝ => A * ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ‖)
      (hIntF.norm.const_mul A) ?_ ?_
    · exact (hContF.mul (hGcont.comp (continuous_const.add continuous_id))).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hGle (t + ξ))
        (norm_nonneg ((𝓕 Work.GM.Energy.RLocal.PsiBump) ξ))).trans_eq (mul_comm _ _)
  have hfnint := hfint.norm
  have hstep : ‖Loc.G N a t‖ ≤ ∫ ξ, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖ := by
    rw [localize_identity N hN a t]
    exact norm_integral_le_integral_norm _
  -- good part: over `Icc (-K) K`
  have hgood : ∫ ξ in Set.Icc (-K) K,
      ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖
      ≤ M * (∫ u in t - K..t + K, ‖Loc.G N a u‖) := by
    have hmono : ∫ ξ in Set.Icc (-K) K,
        ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖
        ≤ ∫ ξ in Set.Icc (-K) K, M * ‖Loc.G N a (t + ξ)‖ := by
      refine setIntegral_mono_ae hfnint.integrableOn ?_ (Filter.Eventually.of_forall fun ξ => ?_)
      · exact (continuous_const.mul
          ((hGcont.comp (continuous_const.add continuous_id)).norm)).continuousOn.integrableOn_compact
          isCompact_Icc
      · beta_reduce
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    refine hmono.trans ?_
    rw [integral_const_mul]
    have hcv : ∫ ξ in Set.Icc (-K) K, ‖Loc.G N a (t + ξ)‖
        = ∫ u in t - K..t + K, ‖Loc.G N a u‖ := by
      rw [(MeasureTheory.setIntegral_congr_set
        (MeasureTheory.Ioc_ae_eq_Icc (μ := volume) (a := -K) (b := K))).symm]
      rw [← intervalIntegral.integral_of_le (by linarith : -K ≤ K)]
      have h := intervalIntegral.integral_comp_add_right (a := -K) (b := K)
        (fun u : ℝ => ‖Loc.G N a u‖) t
      rw [show (∫ x in -K..K, ‖Loc.G N a (t + x)‖) = ∫ x in -K..K, ‖Loc.G N a (x + t)‖ from
        intervalIntegral.integral_congr fun x _ => by rw [add_comm]]
      rw [h]
      rw [show -K + t = t - K by ring, show K + t = t + K by ring]
    rw [hcv]
  -- bad part: over the complement of `Icc (-K) K`
  have hbad : ∫ ξ in (Set.Icc (-K) K)ᶜ,
      ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖
      ≤ A * (Ct * K ^ (-(m : ℝ))) := by
    have hmono : ∫ ξ in (Set.Icc (-K) K)ᶜ,
        ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖
        ≤ ∫ ξ in (Set.Icc (-K) K)ᶜ, A * ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ‖ := by
      refine setIntegral_mono_ae hfnint.integrableOn
        (hIntF.norm.const_mul A).integrableOn (Filter.Eventually.of_forall fun ξ => ?_)
      beta_reduce
      rw [norm_mul]
      calc ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ‖ * ‖Loc.G N a (t + ξ)‖
          ≤ ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ‖ * A :=
            mul_le_mul_of_nonneg_left (hGle (t + ξ)) (norm_nonneg _)
        _ = A * ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ‖ := mul_comm _ _
    refine hmono.trans ?_
    rw [integral_const_mul]
    have hset : (Set.Icc (-K) K)ᶜ = {ξ : ℝ | K < |ξ|} := by
      ext ξ
      rw [Set.mem_compl_iff, Set.mem_ofPred_eq]
      have h : (ξ ∈ Set.Icc (-K) K) ↔ |ξ| ≤ K := by
        rw [Set.mem_Icc, abs_le]
      rw [h, not_le]
    rw [hset]
    exact mul_le_mul_of_nonneg_left htail hA0
  -- combine
  have hsplit : ∫ ξ, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖
      = (∫ ξ in Set.Icc (-K) K, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖)
        + (∫ ξ in (Set.Icc (-K) K)ᶜ, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖) :=
    (integral_add_compl (s := Set.Icc (-K) K) measurableSet_Icc hfnint).symm
  have htot : ‖Loc.G N a t‖ ≤ M * (∫ u in t - K..t + K, ‖Loc.G N a u‖)
      + A * (Ct * K ^ (-(m : ℝ))) := by
    calc ‖Loc.G N a t‖
        ≤ ∫ ξ, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖ := hstep
      _ = (∫ ξ in Set.Icc (-K) K, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖)
          + (∫ ξ in (Set.Icc (-K) K)ᶜ, ‖(𝓕 Work.GM.Energy.RLocal.PsiBump) ξ * Loc.G N a (t + ξ)‖) :=
          hsplit
      _ ≤ M * (∫ u in t - K..t + K, ‖Loc.G N a u‖) + A * (Ct * K ^ (-(m : ℝ))) :=
          add_le_add hgood hbad
  set I : ℝ := ∫ u in t - K..t + K, ‖Loc.G N a u‖ with hI
  have hI0 : 0 ≤ I := by
    rw [hI]
    exact intervalIntegral.integral_nonneg (by linarith) fun u _ => norm_nonneg _
  have hMC : M ≤ max M Ct + 1 := by
    have := le_max_left M Ct; linarith
  have hCtC : Ct ≤ max M Ct + 1 := by
    have := le_max_right M Ct; linarith
  have hKm : K ^ (-(m : ℝ)) = (K ^ (m : ℝ))⁻¹ := Real.rpow_neg hK0.le (m : ℝ)
  have hKm0 : 0 ≤ (K ^ (m : ℝ))⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg hK0.le _)
  calc ‖Loc.G N a t‖
      ≤ M * I + A * (Ct * K ^ (-(m : ℝ))) := htot
    _ = M * I + A * Ct * (K ^ (m : ℝ))⁻¹ := by rw [hKm]; ring
    _ ≤ (max M Ct + 1) * I + (max M Ct + 1) / K ^ (m : ℝ) * A := by
        have h1 : M * I ≤ (max M Ct + 1) * I := by nlinarith
        have h2 : A * Ct * (K ^ (m : ℝ))⁻¹ ≤ (max M Ct + 1) / K ^ (m : ℝ) * A := by
          rw [div_eq_mul_inv]
          have h3 : A * Ct ≤ A * (max M Ct + 1) := mul_le_mul_of_nonneg_left hCtC hA0
          have h4 : A * Ct * (K ^ (m : ℝ))⁻¹ ≤ A * (max M Ct + 1) * (K ^ (m : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right h3 hKm0
          calc A * Ct * (K ^ (m : ℝ))⁻¹ ≤ A * (max M Ct + 1) * (K ^ (m : ℝ))⁻¹ := h4
            _ = (max M Ct + 1) * (K ^ (m : ℝ))⁻¹ * A := by ring
        linarith

/-- **GM Lemma 11.3** (locality of a Dirichlet polynomial, general coefficients): for arbitrary
coefficients `a n` (`n ∈ [N,2N]`) and any `K ≥ 1`, the value of `Σ_{n∈[N,2N]} a n n^{it}` at a
point is controlled by the average of the same expression over `[t-K,t+K]`, up to a `K^{-m}`
multiple of the coefficient mass.
(Proof route: the exact identity `Σ_n a n n^{it} = ∫ ψ̂(ξ) Σ_n a n n^{i(t+ξ)} dξ` for a fixed
smooth bump `ψ` with `ψ(log n/2π) = 1` for all `n ∈ [N,2N]` (a translate of a fixed bump, so
that the derivative bounds and the Fourier decay of `ψ̂` are uniform in `N`); then restrict the
`ξ`-integral to `|ξ| ≤ K` using
`Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay` and bound the tail by
`(sup_u ‖Σ_n a n n^{iu}‖) · ∫_{|ξ|>K}|ψ̂| ≤ (Σ_n ‖a n‖) · C_m K^{-m}`.) -/
theorem localize_dirichlet (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (a : ℕ → ℂ), ∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤
          C * (∫ u in t - K..t + K,
                ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (u : ℂ))‖)
          + C / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖a n‖) := by
  obtain ⟨C, hC, hbound⟩ := localize_dirichlet_core m hm
  refine ⟨C, hC, ?_⟩
  intro N hN a K hK t
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN
  have hterm : ∀ n ∈ Finset.Icc N (2 * N), ∀ u : ℝ,
      (n : ℂ) ^ (Complex.I * (u : ℂ))
        = (N : ℂ) ^ (Complex.I * (u : ℂ))
          * (Complex.ofReal ((n : ℝ) / (N : ℝ))) ^ (Complex.I * (u : ℂ)) := by
    intro n hn u
    have hx0 : (0 : ℝ) ≤ (n : ℝ) / (N : ℝ) :=
      div_nonneg (by positivity) (by positivity)
    have h := Complex.mul_cpow_ofReal_nonneg (le_of_lt hNpos) hx0 (Complex.I * (u : ℂ))
    have h2 : ((N : ℝ) : ℂ) * Complex.ofReal ((n : ℝ) / (N : ℝ)) = (n : ℂ) := by
      have h3 : (N : ℝ) * ((n : ℝ) / (N : ℝ)) = (n : ℝ) := by field_simp
      rw [← Complex.ofReal_mul, h3, Complex.ofReal_natCast]
    rw [h2] at h
    simpa only [Complex.ofReal_natCast] using h
  have hF : ∀ u : ℝ,
      (∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (u : ℂ)))
        = (N : ℂ) ^ (Complex.I * (u : ℂ)) * Loc.G N a u := by
    intro u
    rw [Loc.G, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hterm n hn u]
    ring
  have hFnorm : ∀ u : ℝ,
      ‖(∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (u : ℂ)))‖
        = ‖Loc.G N a u‖ := by
    intro u
    rw [hF u, norm_mul]
    rw [show ‖(N : ℂ) ^ (Complex.I * (u : ℂ))‖ = 1 from by
      simpa only [Complex.ofReal_natCast] using Loc.norm_cpow_I_mul_eq_one hNpos u, one_mul]
  have hI : (∫ u in t - K..t + K, ‖Loc.G N a u‖)
      = ∫ u in t - K..t + K,
          ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (u : ℂ))‖ := by
    apply intervalIntegral.integral_congr
    intro u _
    exact (hFnorm u).symm
  calc ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖
      = ‖Loc.G N a t‖ := hFnorm t
    _ ≤ C * (∫ u in t - K..t + K, ‖Loc.G N a u‖)
        + C / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖a n‖) := hbound N hN a K hK t
    _ = C * (∫ u in t - K..t + K,
            ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (Complex.I * (u : ℂ))‖)
        + C / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N (2 * N), ‖a n‖) := by rw [hI]


end Work.GM.Energy.LocalConstancy
