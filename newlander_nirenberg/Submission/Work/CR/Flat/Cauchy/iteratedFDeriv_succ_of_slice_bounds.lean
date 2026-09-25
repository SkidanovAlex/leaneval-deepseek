import Mathlib

namespace Work.CR.Flat.Cauchy

open Set Filter
open scoped Topology

/-- Auxiliary Taylor-type bound: if `g : E → ℂ` is differentiable on a convex set `Ω` and its
derivative is Hölder continuous with exponent `α > 0` and constant `K` there, then the first-order
Taylor remainder is bounded by `K ‖y - z‖ ^ α * ‖y - z‖`. -/
theorem norm_sub_fderiv_le_of_fderiv_holder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℂ} {Ω : Set E} (hΩconv : Convex ℝ Ω)
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hdiff : ∀ y ∈ Ω, DifferentiableAt ℝ g y)
    (hholder : ∀ y ∈ Ω, ∀ z ∈ Ω, ‖fderiv ℝ g y - fderiv ℝ g z‖ ≤ K * ‖y - z‖ ^ α)
    {z y : E} (hz : z ∈ Ω) (hy : y ∈ Ω) :
    ‖g y - g z - fderiv ℝ g z (y - z)‖ ≤ K * ‖y - z‖ ^ α * ‖y - z‖ := by
  set C := K * ‖y - z‖ ^ α * ‖y - z‖ with hCdef
  set φ : ℝ → ℂ := fun t => g (z + t • (y - z)) - t • (fderiv ℝ g z (y - z)) with hφdef
  have hmem : ∀ t ∈ Set.Icc (0:ℝ) 1, z + t • (y - z) ∈ Ω :=
    fun t ht => hΩconv.add_smul_mem hz (by simpa using hy) ht
  have hφ : φ 1 - φ 0 = g y - g z - fderiv ℝ g z (y - z) := by
    have h1 : φ 1 = g y - fderiv ℝ g z (y - z) := by simp [hφdef]
    have h0 : φ 0 = g z := by simp [hφdef]
    rw [h1, h0]; abel
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt φ
      ((fderiv ℝ g (z + t • (y - z))) (y - z) - fderiv ℝ g z (y - z)) (Set.Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ => z + s • (y - z)) (y - z) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - z)).const_add z
    have h2 : HasFDerivAt g (fderiv ℝ g (z + t • (y - z))) (z + t • (y - z)) :=
      (hdiff _ (hmem t ht)).hasFDerivAt
    have h3 := h2.comp_hasDerivAt t h1
    have h4 : HasDerivAt (fun s : ℝ => s • (fderiv ℝ g z (y - z))) (fderiv ℝ g z (y - z)) t := by
      simpa using (hasDerivAt_id t).smul_const (fderiv ℝ g z (y - z))
    have h5 := h3.sub h4
    rw [hφdef]
    exact h5.hasDerivWithinAt
  have hbound' : ∀ t ∈ Set.Ico (0:ℝ) 1,
      ‖(fderiv ℝ g (z + t • (y - z))) (y - z) - fderiv ℝ g z (y - z)‖ ≤ C := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := le_of_lt ht.2
    have hmem_t : z + t • (y - z) ∈ Ω := hmem t ⟨ht0, ht1⟩
    have h1 : ‖fderiv ℝ g (z + t • (y - z)) - fderiv ℝ g z‖ ≤ K * ‖t • (y - z)‖ ^ α := by
      simpa [add_sub_cancel_left] using hholder _ hmem_t z hz
    calc ‖(fderiv ℝ g (z + t • (y - z))) (y - z) - fderiv ℝ g z (y - z)‖
        = ‖((fderiv ℝ g (z + t • (y - z))) - fderiv ℝ g z) (y - z)‖ := by rw [sub_apply]
      _ ≤ ‖(fderiv ℝ g (z + t • (y - z))) - fderiv ℝ g z‖ * ‖y - z‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * ‖t • (y - z)‖ ^ α) * ‖y - z‖ := by gcongr
      _ ≤ (K * ‖y - z‖ ^ α) * ‖y - z‖ := by
            gcongr
            rw [norm_smul, Real.norm_of_nonneg ht0]
            simpa using mul_le_of_le_one_left (norm_nonneg (y - z)) ht1
      _ = C := by rw [hCdef]
  have hres := norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound'
  rwa [hφ] at hres

/-- Auxiliary: if all the "slice" functions `y ↦ Φ y u` of a map `Φ` into continuous multilinear
maps are differentiable at `z`, then the family `u ↦ fderiv (fun y => Φ y u) z` is a multilinear
map. -/
theorem multilinearMap_fderiv_of_apply_differentiable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {k : ℕ} {Φ : E → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ} {z : E}
    (hdiff : ∀ u : Fin k → E, DifferentiableAt ℝ (fun y => Φ y u) z) :
    ∃ L : MultilinearMap ℝ (fun _ : Fin k => E) (E →L[ℝ] ℂ),
      ∀ u, L u = fderiv ℝ (fun y => Φ y u) z := by
  refine ⟨{ toFun := fun u => fderiv ℝ (fun y => Φ y u) z, map_update_add' := ?_, map_update_smul' := ?_ },
    fun u => rfl⟩
  · intro _ u j x y
    have hfun : (fun y' => Φ y' (Function.update u j (x + y)))
        = (fun y' => Φ y' (Function.update u j x)) + (fun y' => Φ y' (Function.update u j y)) := by
      funext y'
      simp only [Pi.add_apply]
      exact ContinuousMultilinearMap.map_update_add (Φ y') u j x y
    rw [hfun]
    exact fderiv_add (hdiff _) (hdiff _)
  · intro _ u j c x
    have hfun : (fun y' => Φ y' (Function.update u j (c • x)))
        = c • (fun y' => Φ y' (Function.update u j x)) := by
      funext y'
      simp only [Pi.smul_apply]
      exact ContinuousMultilinearMap.map_update_smul (Φ y') u j c x
    rw [hfun]
    exact fderiv_const_smul (hdiff _) c

theorem iteratedFDeriv_succ_of_slice_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {F : E → ℂ} {Ω : Set E} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {α K : ℝ} (hα : 0 < α) (hK : 0 ≤ K)
    (hdiff : ∀ u : Fin k → E, ∀ z ∈ Ω,
      DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ k F y u) z)
    (hbound : ∀ u : Fin k → E, ∀ z ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z‖ ≤ K * ∏ i, ‖u i‖)
    (hholder : ∀ u : Fin k → E, ∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z
        - fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z'‖
        ≤ K * (∏ i, ‖u i‖) * ‖z - z'‖ ^ α) :
    (∀ z ∈ Ω, ∀ w : Fin (k + 1) → E,
      ‖iteratedFDeriv ℝ (k + 1) F z w‖ ≤ K * ∏ i, ‖w i‖) ∧
    (∀ z ∈ Ω, ∀ z' ∈ Ω,
      ‖iteratedFDeriv ℝ (k + 1) F z - iteratedFDeriv ℝ (k + 1) F z'‖
        ≤ K * ‖z - z'‖ ^ α) := by
  have hprod_nonneg : ∀ u : Fin k → E, 0 ≤ ∏ i, ‖u i‖ :=
    fun u => Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have key : ∀ z ∈ Ω, ∃ (L : MultilinearMap ℝ (fun _ : Fin k => E) (E →L[ℝ] ℂ))
      (D : E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ)),
      (∀ u, L u = fderiv ℝ (fun y => iteratedFDeriv ℝ k F y u) z) ∧
      (∀ v u, D v u = L u v) ∧
      HasFDerivAt (iteratedFDeriv ℝ k F) D z := by
    intro z hz
    obtain ⟨L, hL⟩ := multilinearMap_fderiv_of_apply_differentiable
      (Φ := iteratedFDeriv ℝ k F) (z := z) (fun u => hdiff u z hz)
    let Lv : E →ₗ[ℝ] MultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
      { toFun := fun v =>
          { toFun := fun u => L u v
            map_update_add' := by
              intro _ u j x y
              simpa only [add_apply] using
                congrArg (fun f : E →L[ℝ] ℂ => f v) (MultilinearMap.map_update_add L u j x y)
            map_update_smul' := by
              intro _ u j c x
              simpa only [smul_apply] using
                congrArg (fun f : E →L[ℝ] ℂ => f v) (MultilinearMap.map_update_smul L u j c x) }
        map_add' := by
          intro v w
          ext u
          exact map_add (L u) v w
        map_smul' := by
          intro c v
          ext u
          exact map_smul (L u) c v }
    have hLv : ∀ v u, Lv v u = L u v := fun v u => rfl
    let D : E →L[ℝ] (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) :=
      MultilinearMap.mkContinuousLinear Lv K (fun v u => by
        rw [hLv]
        calc ‖L u v‖ ≤ ‖L u‖ * ‖v‖ := ContinuousLinearMap.le_opNorm (L u) v
          _ ≤ (K * ∏ i, ‖u i‖) * ‖v‖ := by
                gcongr
                simpa only [hL u] using hbound u z hz
          _ = K * ‖v‖ * ∏ i, ‖u i‖ := by ring)
    have hD : ∀ v u, D v u = L u v := by
      intro v u
      simp only [D, MultilinearMap.mkContinuousLinear, LinearMap.mkContinuous_apply]
      exact hLv v u
    refine ⟨L, D, hL, hD, ?_⟩
    rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hKc : Tendsto (fun y : E => K * ‖y - z‖ ^ α) (𝓝 z) (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : E => K) (𝓝 z) (𝓝 K)).mul
          ((tendsto_norm_sub_self z).rpow_const_nhds_zero hα)
    filter_upwards [(tendsto_order.1 hKc).2 c hc, hΩopen.mem_nhds hz] with y hylt hymem
    have hCnn : 0 ≤ K * ‖y - z‖ ^ α * ‖y - z‖ :=
      mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)) (norm_nonneg _)
    have hbd : ‖iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k F z - D (y - z)‖
        ≤ K * ‖y - z‖ ^ α * ‖y - z‖ := by
      rw [ContinuousMultilinearMap.opNorm_le_iff hCnn]
      intro u
      have hpt : (iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k F z - D (y - z)) u
          = (fun y' => iteratedFDeriv ℝ k F y' u) y - (fun y' => iteratedFDeriv ℝ k F y' u) z
            - fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' u) z (y - z) := by
        simp only [sub_apply, hD, hL]
      rw [hpt]
      have hA' := norm_sub_fderiv_le_of_fderiv_holder (g := fun y' => iteratedFDeriv ℝ k F y' u)
        hΩconv hα (mul_nonneg hK (hprod_nonneg u))
        (fun y' hy' => hdiff u y' hy')
        (fun y' hy' z' hz' => hholder u y' hy' z' hz') hz hymem
      calc ‖(fun y' => iteratedFDeriv ℝ k F y' u) y - (fun y' => iteratedFDeriv ℝ k F y' u) z
              - fderiv ℝ (fun y' => iteratedFDeriv ℝ k F y' u) z (y - z)‖
          ≤ (K * ∏ i, ‖u i‖) * ‖y - z‖ ^ α * ‖y - z‖ := hA'
        _ = (K * ‖y - z‖ ^ α * ‖y - z‖) * ∏ i, ‖u i‖ := by ring
    calc ‖iteratedFDeriv ℝ k F y - iteratedFDeriv ℝ k F z - D (y - z)‖
        ≤ K * ‖y - z‖ ^ α * ‖y - z‖ := hbd
      _ ≤ c * ‖y - z‖ := mul_le_mul_of_nonneg_right (le_of_lt hylt) (norm_nonneg _)
  constructor
  · intro z hz w
    obtain ⟨L, D, hL, hD, hFD⟩ := key z hz
    have hfd : fderiv ℝ (iteratedFDeriv ℝ k F) z = D := hFD.fderiv
    have hval : iteratedFDeriv ℝ (k + 1) F z w = L (Fin.tail w) (w 0) := by
      change (fderiv ℝ (iteratedFDeriv ℝ k F) z (w 0)) (Fin.tail w) = L (Fin.tail w) (w 0)
      rw [hfd, hD]
    rw [hval]
    calc ‖L (Fin.tail w) (w 0)‖ ≤ ‖L (Fin.tail w)‖ * ‖w 0‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * ∏ i, ‖Fin.tail w i‖) * ‖w 0‖ := by
            gcongr
            simpa only [hL] using hbound (Fin.tail w) z hz
      _ = K * ∏ i, ‖w i‖ := by
            rw [Fin.prod_univ_succ]
            simp only [Fin.tail]
            ring
  · intro z hz z' hz'
    obtain ⟨L, D, hL, hD, hFD⟩ := key z hz
    obtain ⟨L', D', hL', hD', hFD'⟩ := key z' hz'
    have hfd : fderiv ℝ (iteratedFDeriv ℝ k F) z = D := hFD.fderiv
    have hfd' : fderiv ℝ (iteratedFDeriv ℝ k F) z' = D' := hFD'.fderiv
    rw [ContinuousMultilinearMap.opNorm_le_iff
      (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))]
    intro w
    have hval : (iteratedFDeriv ℝ (k + 1) F z - iteratedFDeriv ℝ (k + 1) F z') w
        = L (Fin.tail w) (w 0) - L' (Fin.tail w) (w 0) := by
      rw [sub_apply]
      congr 1
      · change (fderiv ℝ (iteratedFDeriv ℝ k F) z (w 0)) (Fin.tail w) = L (Fin.tail w) (w 0)
        rw [hfd, hD]
      · change (fderiv ℝ (iteratedFDeriv ℝ k F) z' (w 0)) (Fin.tail w) = L' (Fin.tail w) (w 0)
        rw [hfd', hD']
    rw [hval]
    calc ‖L (Fin.tail w) (w 0) - L' (Fin.tail w) (w 0)‖
        = ‖(L (Fin.tail w) - L' (Fin.tail w)) (w 0)‖ := by rw [sub_apply]
      _ ≤ ‖L (Fin.tail w) - L' (Fin.tail w)‖ * ‖w 0‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ (K * (∏ i, ‖Fin.tail w i‖) * ‖z - z'‖ ^ α) * ‖w 0‖ := by
            gcongr
            rw [hL, hL']
            exact hholder (Fin.tail w) z hz z' hz'
      _ = K * ‖z - z'‖ ^ α * ∏ i, ‖w i‖ := by
            rw [Fin.prod_univ_succ]
            simp only [Fin.tail]
            ring

end Work.CR.Flat.Cauchy
