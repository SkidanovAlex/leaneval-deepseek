/-
  # Local invariance of a regular level set under a tangent vector field

  Let `V : ℝᵐ → ℝ^{m-1}` be `C¹` and regular on its zero set (`hgrad`: at every zero of `V` the
  `m-1` component gradients are linearly independent), and let `X` be a `C¹` vector field which is
  tangent to the zero set along the zero set (`htan`).  If `y` is a (local) solution of the ODE
  `y' = X ∘ y` with `V (y t₀) = 0`, then `V` vanishes on `y` near `t₀`.

  The proof (on top of the already proved local parametrisation
  `Work.WilE2.exists_ift_param_self` of the level set) is:

  * a regular zero `z₀` of `V` is the base point of a `C¹` curve `ψ` parametrising the level set,
    with `ℓ (ψ s - z₀) = s` for a linear functional `ℓ` and `ψ 0 = z₀`;
  * along `ψ` the vector field `X` is a multiple of the velocity `ψ'` (the tangency identity
    `X (ψ s) = fderiv ψ s (ℓ (X (ψ s)))`): both vectors lie in the one-dimensional kernel of
    `fderiv V (ψ s)`;
  * the "level-set parameter" `s t = ℓ (y t - z₀)` of the solution therefore satisfies
    `‖X (y t) - fderiv ψ (s t) (ℓ (X (y t)))‖ ≤ C * ‖y t - ψ (s t)‖`, a Grönwall bound for
    `z t = y t - ψ (s t)`; since `z t₀ = 0`, `z` vanishes near `t₀`;
  * hence `y = ψ ∘ s` near `t₀`, so `V (y t) = V (ψ (s t)) = 0` near `t₀`.
-/
import Mathlib
import Submission.Work.WilE2.local_orbit_covers_eps
import Submission.Work.WilE2.exists_ne_zero_mem_ker_fderiv
import Submission.Work.WilE2.eq_zero_of_eventually_hasDerivAt_bound_at

open scoped Topology ContDiff
open Filter
set_option autoImplicit false

namespace Work.WilE2

/-- The vector field `X` is a multiple of the velocity of the parametrisation `ψ` of the level
set (the tangency identity): near `0`, `X (ψ s) = fderiv ℝ ψ s (ℓ (X (ψ s)))`.

This is `Work.WilE2.tangent_of_param_self` without the auxiliary hypothesis that `X` be
non-vanishing on the level set (a hypothesis which that proof never uses). -/
theorem tangent_of_param_local {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ))
    (X : (Fin m → ℝ) → (Fin m → ℝ)) (hV : ContDiff ℝ 1 V)
    (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z))
    (htan : ∀ z, V z = 0 → ∀ i, fderiv ℝ (fun w => V w i) z (X z) = 0)
    (p : Fin m → ℝ) (ℓ : (Fin m → ℝ) →L[ℝ] ℝ) (ψ : ℝ → (Fin m → ℝ))
    (hψdiff : ContDiffAt ℝ 1 ψ 0)
    (hψM : ∀ᶠ s : ℝ in nhds 0, V (ψ s) = 0)
    (hℓψ : ∀ᶠ s : ℝ in nhds 0, ℓ (ψ s - p) = s) :
    ∀ᶠ s : ℝ in nhds 0, X (ψ s) = fderiv ℝ ψ s (ℓ (X (ψ s))) := by
  have hψloc : ∀ᶠ s : ℝ in nhds 0, HasFDerivAt ψ (fderiv ℝ ψ s) s := by
    obtain ⟨u, hu, hucd⟩ := hψdiff.contDiffOn (m := 1) le_rfl (fun h => absurd h (by decide))
    obtain ⟨u', hu'sub, hu'open, h0u'⟩ := mem_nhds_iff.mp hu
    filter_upwards [hu'open.mem_nhds h0u'] with s hs
    exact (((hucd.mono hu'sub).differentiableOn_one).differentiableAt
      (hu'open.mem_nhds hs)).hasFDerivAt
  obtain ⟨δ₁, hδ₁, hδ₁P⟩ := exists_pos_abs_lt_of_eventually hψloc
  obtain ⟨δ₂, hδ₂, hδ₂P⟩ := exists_pos_abs_lt_of_eventually hψM
  obtain ⟨δ₃, hδ₃, hδ₃P⟩ := exists_pos_abs_lt_of_eventually hℓψ
  set δ : ℝ := min δ₁ (min δ₂ δ₃) / 2 with hδdef
  have hminpos : 0 < min δ₁ (min δ₂ δ₃) := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hlt₁ : δ < δ₁ := by rw [hδdef]; linarith [min_le_left δ₁ (min δ₂ δ₃)]
  have hlt₂ : δ < δ₂ := by
    rw [hδdef]; linarith [min_le_right δ₁ (min δ₂ δ₃), min_le_left δ₂ δ₃]
  have hlt₃ : δ < δ₃ := by
    rw [hδdef]; linarith [min_le_right δ₁ (min δ₂ δ₃), min_le_right δ₂ δ₃]
  have hball : ∀ t, |t| < δ → HasFDerivAt ψ (fderiv ℝ ψ t) t :=
    fun t ht => hδ₁P t (lt_trans ht hlt₁)
  have hballV : ∀ t, |t| < δ → V (ψ t) = 0 := fun t ht => hδ₂P t (lt_trans ht hlt₂)
  have hballℓ : ∀ t, |t| < δ → ℓ (ψ t - p) = t := fun t ht => hδ₃P t (lt_trans ht hlt₃)
  filter_upwards [isOpen_Ioo.mem_nhds
    (show (0:ℝ) ∈ Set.Ioo (-δ) δ from ⟨by linarith, hδpos⟩)] with s hs
  have hmem : s ∈ Set.Ioo (-δ) δ := hs
  have hlt : |s| < δ := by rw [abs_lt]; exact ⟨hmem.1, hmem.2⟩
  have hnb : ∀ᶠ t in nhds s, t ∈ Set.Ioo (-δ) δ := isOpen_Ioo.mem_nhds hmem
  have hsd : HasFDerivAt ψ (fderiv ℝ ψ s) s := hball s hlt
  have hVs : ∀ᶠ t in nhds s, V (ψ t) = 0 :=
    hnb.mono (fun t ht => hballV t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩))
  have hℓs : ∀ᶠ t in nhds s, ℓ (ψ t - p) = t :=
    hnb.mono (fun t ht => hballℓ t (by rw [abs_lt]; exact ⟨ht.1, ht.2⟩))
  have hψ's : (fderiv ℝ ψ s) 1 ≠ 0 := by
    have h := fderiv_apply_one_eq_one ℓ hsd hℓs
    intro h0
    rw [h0, map_zero] at h
    exact zero_ne_one h
  have htan_ψ' : (fderiv ℝ V (ψ s)) ((fderiv ℝ ψ s) 1) = 0 :=
    curve_fderiv_eq_zero V hV hsd hVs
  have htanX : (fderiv ℝ V (ψ s)) (X (ψ s)) = 0 := by
    rw [fderiv_eq_pi V hV (ψ s)]
    funext i
    simpa using htan (ψ s) (hballV s hlt) i
  have htop : (fderiv ℝ V (ψ s)).range = ⊤ :=
    fderiv_range_top V hV (ψ s) (hgrad (ψ s) (hballV s hlt))
  obtain ⟨c, hc⟩ := smul_eq_of_range_top (fderiv ℝ V (ψ s)) htop htan_ψ' htanX hψ's
  have hℓ1 : ℓ ((fderiv ℝ ψ s) 1) = 1 := fderiv_apply_one_eq_one ℓ hsd hℓs
  have hℓc : ℓ (X (ψ s)) = c := by
    rw [hc, map_smul, hℓ1, smul_eq_mul, mul_one]
  calc X (ψ s) = c • (fderiv ℝ ψ s) 1 := hc
    _ = ℓ (X (ψ s)) • (fderiv ℝ ψ s) 1 := by rw [hℓc]
    _ = fderiv ℝ ψ s (ℓ (X (ψ s))) := by
        rw [← ContinuousLinearMap.map_smul, smul_eq_mul, mul_one]

theorem local_invariance {m : ℕ} (V : (Fin m → ℝ) → (Fin (m - 1) → ℝ)) (X : (Fin m → ℝ) → (Fin m → ℝ))
    (hV : ContDiff ℝ 1 V) (hX : ContDiff ℝ 1 X)
    (hgrad : ∀ z, V z = 0 → LinearIndependent ℝ (fun i => fderiv ℝ (fun w => V w i) z))
    (htan : ∀ z, V z = 0 → ∀ i : Fin (m - 1), fderiv ℝ (fun w => V w i) z (X z) = 0)
    (y : ℝ → Fin m → ℝ) (t₀ : ℝ) (hy : V (y t₀) = 0)
    (hode : ∀ᶠ t in nhds t₀, HasDerivAt y (X (y t)) t) :
    ∀ᶠ t in nhds t₀, V (y t) = 0 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · -- `m ≤ 1`: the target of `V` is a subsingleton, so `V` vanishes identically
    have h0 : m - 1 = 0 := by omega
    haveI : Subsingleton (Fin (m - 1) → ℝ) := by rw [h0]; infer_instance
    filter_upwards with t
    exact Subsingleton.elim (V (y t)) 0
  · -- main case `m ≥ 2`
    set z₀ : Fin m → ℝ := y t₀ with hz₀def
    have hVz₀ : V z₀ = 0 := hy
    -- a nonzero tangent direction at `z₀`
    obtain ⟨v, hv0, hvker⟩ := exists_ne_zero_mem_ker_fderiv hm V z₀
    -- the parametrisation `ψ` of the level set through `z₀`, with parameter `ℓ`
    obtain ⟨ℓ, ψ, hℓv, hψ0, hψC1, hψev, _⟩ :=
      exists_ift_param_self V hV hgrad z₀ v hVz₀ hv0 hvker
    have hψM : ∀ᶠ s : ℝ in nhds 0, V (ψ s) = 0 := hψev.mono fun s h => h.1
    have hℓψ : ∀ᶠ s : ℝ in nhds 0, ℓ (ψ s - z₀) = s := hψev.mono fun s h => h.2
    have htang₀ : ∀ᶠ s : ℝ in nhds 0, X (ψ s) = fderiv ℝ ψ s (ℓ (X (ψ s))) :=
      tangent_of_param_local V X hV hgrad htan z₀ ℓ ψ hψC1 hψM hℓψ
    -- `ψ` is differentiable near `0`, with bounded differential there
    have hψloc₀ : ∀ᶠ r : ℝ in nhds 0, HasFDerivAt ψ (fderiv ℝ ψ r) r := by
      obtain ⟨u, hu, hucd⟩ := hψC1.contDiffOn (m := 1) le_rfl (fun h => absurd h (by decide))
      obtain ⟨u', hu'sub, hu'open, h0u'⟩ := mem_nhds_iff.mp hu
      filter_upwards [hu'open.mem_nhds h0u'] with r hr
      exact (((hucd.mono hu'sub).differentiableOn_one).differentiableAt
        (hu'open.mem_nhds hr)).hasFDerivAt
    set M : ℝ := ‖fderiv ℝ ψ 0‖ + 1 with hMdef
    have hbdd₀ : ∀ᶠ r : ℝ in nhds 0, ‖fderiv ℝ ψ r‖ ≤ M := by
      have h1 : ∀ᶠ r in nhds (0 : ℝ), dist (fderiv ℝ ψ r) (fderiv ℝ ψ 0) < 1 :=
        (hψC1.continuousAt_fderiv one_ne_zero).eventually
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
      filter_upwards [h1] with r hr
      have h2 : ‖fderiv ℝ ψ r - fderiv ℝ ψ 0‖ < 1 := by rwa [dist_eq_norm] at hr
      have h3 : ‖fderiv ℝ ψ r‖ ≤ ‖fderiv ℝ ψ 0‖ + ‖fderiv ℝ ψ r - fderiv ℝ ψ 0‖ := by
        calc ‖fderiv ℝ ψ r‖ = ‖fderiv ℝ ψ 0 + (fderiv ℝ ψ r - fderiv ℝ ψ 0)‖ := by
              congr 1; abel
          _ ≤ ‖fderiv ℝ ψ 0‖ + ‖fderiv ℝ ψ r - fderiv ℝ ψ 0‖ := norm_add_le _ _
      rw [hMdef]; linarith
    -- the level-set parameter of `y`
    set s : ℝ → ℝ := fun t => ℓ (y t - z₀) with hsdef
    have hs0 : s t₀ = 0 := by simp [hsdef, hz₀def]
    have hsd : ∀ᶠ t : ℝ in nhds t₀, HasDerivAt s (ℓ (X (y t))) t := by
      filter_upwards [hode] with t ht
      have h1 : HasDerivAt (fun u : ℝ => ℓ (y u) - ℓ z₀) (ℓ (X (y t))) t :=
        (hasDerivAt_comp (ContinuousLinearMap.hasFDerivAt ℓ : HasFDerivAt ℓ ℓ (y t))
          ht).sub_const (ℓ z₀)
      simpa [hsdef, map_sub] using h1
    have hsc : ContinuousAt s t₀ := (hsd.self_of_nhds).continuousAt
    have hstend : Tendsto s (nhds t₀) (nhds 0) := by
      have h : Tendsto s (nhds t₀) (nhds (s t₀)) := hsc
      rwa [hs0] at h
    have hytend : Tendsto y (nhds t₀) (nhds z₀) := by
      have h : Tendsto y (nhds t₀) (nhds (y t₀)) := (hode.self_of_nhds).continuousAt
      rwa [← hz₀def] at h
    -- derivative of `z = y - ψ ∘ s`, with a Grönwall bound for it
    have hzderiv : ∀ᶠ t : ℝ in nhds t₀,
        HasDerivAt (fun u : ℝ => y u - ψ (s u))
          (X (y t) - fderiv ℝ ψ (s t) (ℓ (X (y t)))) t := by
      filter_upwards [hode, hstend.eventually hψloc₀, hsd] with t hyt hψt hst
      exact hyt.sub (hasDerivAt_comp hψt hst)
    have hz0 : (fun u : ℝ => y u - ψ (s u)) t₀ = 0 := by simp [hs0, hψ0, hz₀def]
    obtain ⟨K, W, hWmem, hKW⟩ := hX.locallyLipschitz z₀
    set C : ℝ := (K : ℝ) * (1 + M * ‖ℓ‖) with hCdef
    have hyW : ∀ᶠ t : ℝ in nhds t₀, y t ∈ W := hytend.eventually hWmem
    have hψW : ∀ᶠ t : ℝ in nhds t₀, ψ (s t) ∈ W := by
      have h1 : Tendsto (fun t : ℝ => ψ (s t)) (nhds t₀) (nhds (ψ 0)) :=
        Tendsto.comp hψC1.continuousAt hstend
      have h2 : Tendsto (fun t : ℝ => ψ (s t)) (nhds t₀) (nhds z₀) := by
        rwa [hψ0] at h1
      exact h2.eventually hWmem
    have hzbound : ∀ᶠ t : ℝ in nhds t₀,
        ‖X (y t) - fderiv ℝ ψ (s t) (ℓ (X (y t)))‖ ≤ C * ‖y t - ψ (s t)‖ := by
      filter_upwards [hstend.eventually htang₀, hstend.eventually hbdd₀, hyW, hψW]
        with t htan_t hMbdd hytW hψtW
      have hkey : X (y t) - fderiv ℝ ψ (s t) (ℓ (X (y t)))
          = (X (y t) - X (ψ (s t)))
            - fderiv ℝ ψ (s t) (ℓ (X (y t) - X (ψ (s t)))) := by
        simp only [map_sub]
        rw [← htan_t]
        abel
      have hMnn : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
      have h1 : ‖X (y t) - X (ψ (s t))‖ ≤ (K : ℝ) * ‖y t - ψ (s t)‖ := by
        have h := hKW.dist_le_mul (y t) hytW (ψ (s t)) hψtW
        simpa [dist_eq_norm] using h
      have hB : ‖ℓ (X (y t) - X (ψ (s t)))‖ ≤ ‖ℓ‖ * ‖X (y t) - X (ψ (s t))‖ :=
        ContinuousLinearMap.le_opNorm ℓ _
      have hD : ‖fderiv ℝ ψ (s t) (ℓ (X (y t) - X (ψ (s t))))‖
          ≤ M * ‖ℓ (X (y t) - X (ψ (s t)))‖ :=
        le_trans (ContinuousLinearMap.le_opNorm _ _)
          (mul_le_mul_of_nonneg_right hMbdd (norm_nonneg _))
      have hE : M * ‖ℓ (X (y t) - X (ψ (s t)))‖
          ≤ M * (‖ℓ‖ * ‖X (y t) - X (ψ (s t))‖) :=
        mul_le_mul_of_nonneg_left hB hMnn
      have hF : M * (‖ℓ‖ * ‖X (y t) - X (ψ (s t))‖)
          ≤ M * (‖ℓ‖ * ((K : ℝ) * ‖y t - ψ (s t)‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) hMnn
      have hG : ‖(X (y t) - X (ψ (s t)))
            - fderiv ℝ ψ (s t) (ℓ (X (y t) - X (ψ (s t))))‖
          ≤ (K : ℝ) * ‖y t - ψ (s t)‖ + M * (‖ℓ‖ * ((K : ℝ) * ‖y t - ψ (s t)‖)) :=
        calc ‖(X (y t) - X (ψ (s t)))
              - fderiv ℝ ψ (s t) (ℓ (X (y t) - X (ψ (s t))))‖
            ≤ ‖X (y t) - X (ψ (s t))‖
              + ‖fderiv ℝ ψ (s t) (ℓ (X (y t) - X (ψ (s t))))‖ := norm_sub_le _ _
          _ ≤ (K : ℝ) * ‖y t - ψ (s t)‖ + M * (‖ℓ‖ * ((K : ℝ) * ‖y t - ψ (s t)‖)) :=
              add_le_add h1 (le_trans hD (le_trans hE hF))
      rw [hkey]
      calc ‖(X (y t) - X (ψ (s t)))
            - fderiv ℝ ψ (s t) (ℓ (X (y t) - X (ψ (s t))))‖
          ≤ (K : ℝ) * ‖y t - ψ (s t)‖ + M * (‖ℓ‖ * ((K : ℝ) * ‖y t - ψ (s t)‖)) := hG
        _ = C * ‖y t - ψ (s t)‖ := by rw [hCdef]; ring
    have hzfinal : ∀ᶠ t : ℝ in nhds t₀, (fun u : ℝ => y u - ψ (s u)) t = 0 :=
      eq_zero_of_eventually_hasDerivAt_bound_at hz0 hzderiv hzbound
    -- `y` agrees with the parametrisation of the level set near `t₀`
    obtain ⟨δ, hδpos, hδ⟩ := exists_pos_abs_lt_of_eventually hψM
    have hyeq : ∀ᶠ t : ℝ in nhds t₀, y t = ψ (s t) :=
      hzfinal.mono fun t ht => sub_eq_zero.mp ht
    have hsa : ∀ᶠ t : ℝ in nhds t₀, |s t| < δ := by
      have h0lt : |s t₀| < δ := by rw [hs0]; simpa using hδpos
      exact (continuous_abs.continuousAt.comp hsc).eventually (isOpen_Iio.mem_nhds h0lt)
    filter_upwards [hyeq, hsa] with t ht1 ht2
    rw [ht1]
    exact hδ (s t) ht2

end Work.WilE2
