import Mathlib
import Submission.Work.CKFinal.Socket.Construction
import Submission.Work.CKFinal.Socket.F2_S2op_good
import Submission.Work.CKFinal.Socket.F2_S2op_triple_U0
import Submission.Work.CKFinal.Socket.F2_S2op_orbit_free_near
set_option maxHeartbeats 4000000

noncomputable section
open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

lemma continuous_S_smul_socket : Continuous (fun τ : UpperHalfPlane => ModularGroup.S • τ) := by
  rw [Topology.IsEmbedding.continuous_iff UpperHalfPlane.isEmbedding_coe]
  simp only [Function.comp_def]
  have h : (fun τ : UpperHalfPlane => ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) =
      fun τ : UpperHalfPlane => -((τ : ℂ))⁻¹ :=
    funext fun τ => Work.Kernels.S_smul_coe τ
  rw [h]
  exact (UpperHalfPlane.continuous_coe.inv₀ (fun τ => UpperHalfPlane.ne_zero τ)).neg

lemma continuousAt_cpow_zpow {α : Type*} [TopologicalSpace α] {f : α → ℂ} {a : α} {k : ℤ}
    (hf : ContinuousAt f a) (h0 : f a ≠ 0) :
    ContinuousAt (fun x => f x ^ k) a := by
  rcases lt_or_ge k 0 with hk | hk
  · have hkpos : 0 < -k := by omega
    set n : ℕ := (-k).toNat with hn
    have hnk : (n : ℤ) = -k := by rw [hn]; exact Int.toNat_of_nonneg hkpos.le
    have hfun : (fun x => f x ^ k) = fun x => ((f x) ^ n)⁻¹ := by
      funext x
      rw [show k = -(n : ℤ) by omega]
      rw [zpow_neg, zpow_natCast]
    rw [hfun]
    exact (hf.pow n).inv₀ (by simp [h0])
  · set n : ℕ := k.toNat with hn
    have hnk : (n : ℤ) = k := by rw [hn]; exact Int.toNat_of_nonneg hk
    have hfun : (fun x => f x ^ k) = fun x => (f x) ^ n := by
      funext x
      rw [show k = (n : ℤ) by omega, zpow_natCast]
    rw [hfun]
    exact hf.pow n

theorem continuousAt_S2op_layerFn (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ)
    (hU0 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (layerFn ℓ d r) Work.CKFinal.U0)
    {τ : UpperHalfPlane} (h0 : ModularGroup.S • τ ∈ Work.CKFinal.U0)
    (h1 : ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.CKFinal.U0)
    (h2 : ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ Work.CKFinal.U0) :
    ContinuousAt (fun σ : UpperHalfPlane =>
      Work.Asymptotics.S2op ((d : ℤ) / 2) (layerFn ℓ d r) σ) τ := by
  have hpoint : ∀ σ : UpperHalfPlane,
      Work.Asymptotics.S2op ((d : ℤ) / 2) (layerFn ℓ d r) σ
        = layerFn ℓ d r (ModularGroup.S • ((2:ℝ) +ᵥ σ))
            * ((((2:ℝ) +ᵥ σ : UpperHalfPlane) : ℂ) ^ (-((d:ℤ)/2)))
          - 2 * (layerFn ℓ d r (ModularGroup.S • ((1:ℝ) +ᵥ σ))
            * ((((1:ℝ) +ᵥ σ : UpperHalfPlane) : ℂ) ^ (-((d:ℤ)/2))))
          + layerFn ℓ d r (ModularGroup.S • σ)
            * (((σ : UpperHalfPlane) : ℂ) ^ (-((d:ℤ)/2))) := by
    intro σ
    rw [Work.Asymptotics.S2op_apply_eq, Work.Kernels.slash_S_apply, Work.Kernels.slash_S_apply,
      Work.Kernels.slash_S_apply]
  have hcoe : ∀ m : ℝ, ContinuousAt (fun σ : UpperHalfPlane => ((((m:ℝ) +ᵥ σ : UpperHalfPlane) : ℂ))) τ :=
    fun m => (UpperHalfPlane.continuous_coe.comp (continuous_vadd_real m)).continuousAt
  have hL : ∀ (m : ℝ), ModularGroup.S • ((m:ℝ) +ᵥ τ) ∈ Work.CKFinal.U0 →
      ContinuousAt (fun σ : UpperHalfPlane => layerFn ℓ d r (ModularGroup.S • ((m:ℝ) +ᵥ σ))) τ := by
    intro m hpt
    have hinner : Continuous (fun σ : UpperHalfPlane => ModularGroup.S • ((m:ℝ) +ᵥ σ)) :=
      continuous_S_smul_socket.comp (continuous_vadd_real m)
    exact ContinuousAt.comp (f := fun σ : UpperHalfPlane => ModularGroup.S • ((m:ℝ) +ᵥ σ))
      (x := τ) (g := layerFn ℓ d r)
      (hU0.continuousOn.continuousAt (isOpen_U0.mem_nhds hpt)) hinner.continuousAt
  have hZ : ∀ m : ℝ, ContinuousAt (fun σ : UpperHalfPlane =>
      ((((m:ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)) ^ (-((d:ℤ)/2))) τ :=
    fun m => continuousAt_cpow_zpow (hcoe m) (UpperHalfPlane.ne_zero _)
  have hL0 : ContinuousAt (fun σ : UpperHalfPlane => layerFn ℓ d r (ModularGroup.S • σ)) τ := by
    have hinner : Continuous (fun σ : UpperHalfPlane => ModularGroup.S • σ) := continuous_S_smul_socket
    exact ContinuousAt.comp (f := fun σ : UpperHalfPlane => ModularGroup.S • σ)
      (x := τ) (g := layerFn ℓ d r)
      (hU0.continuousOn.continuousAt (isOpen_U0.mem_nhds h0)) hinner.continuousAt
  have hZ0 : ContinuousAt (fun σ : UpperHalfPlane =>
      (((σ : UpperHalfPlane) : ℂ)) ^ (-((d:ℤ)/2))) τ :=
    continuousAt_cpow_zpow UpperHalfPlane.continuous_coe.continuousAt (UpperHalfPlane.ne_zero _)
  have hsum := (((hL 2 h2).mul (hZ 2)).sub (((hL 1 h1).mul (hZ 1)).const_mul 2)).add
    (hL0.mul hZ0)
  refine hsum.congr ?_
  filter_upwards with σ
  exact (hpoint σ).symm

lemma clean_of_orbit_free {σ : UpperHalfPlane}
    (h : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, (γ • σ).re ≠ 0) :
    ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun σ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro t ht hj
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hj
  have h2 : (γ⁻¹ • σ : UpperHalfPlane) = Work.Kernels.imagAxis t ht := by
    rw [← hγ, inv_smul_smul]
  have hre : (γ⁻¹ • σ).re = 0 := by rw [h2]; simp [Work.Kernels.imagAxis]
  exact (h γ⁻¹) hre

lemma S2op_congr_three_aux (k : ℤ) {F G : UpperHalfPlane → ℂ} {τ : UpperHalfPlane}
    (h0 : F (ModularGroup.S • τ) = G (ModularGroup.S • τ))
    (h1 : F (ModularGroup.S • ((1:ℝ) +ᵥ τ)) = G (ModularGroup.S • ((1:ℝ) +ᵥ τ)))
    (h2 : F (ModularGroup.S • ((2:ℝ) +ᵥ τ)) = G (ModularGroup.S • ((2:ℝ) +ᵥ τ))) :
    Work.Asymptotics.S2op k F τ = Work.Asymptotics.S2op k G τ := by
  rw [Work.Asymptotics.S2op_apply_eq, Work.Asymptotics.S2op_apply_eq,
    Work.Kernels.slash_S_apply, Work.Kernels.slash_S_apply, Work.Kernels.slash_S_apply,
    Work.Kernels.slash_S_apply, Work.Kernels.slash_S_apply, Work.Kernels.slash_S_apply,
    h2, h1, h0]

theorem F2_S2op_main (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (r : ℝ)
    (hU0 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (Work.CKFinal.Socket.layerFn ℓ d r) Work.CKFinal.U0)
    {τ : UpperHalfPlane} (h1 : ModularGroup.S • τ ∈ Work.CKFinal.Socket.O ℓ d hd)
    (h2 : ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ Work.CKFinal.Socket.O ℓ d hd)
    (h3 : ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ Work.CKFinal.Socket.O ℓ d hd) :
    Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.CKFinal.Socket.F2 ℓ d hd r) τ = 0 := by
  obtain ⟨hu0, hu1, hu2⟩ := F2_S2op_triple_U0 ℓ d hd h1 h2 h3
  have hcongr : Work.Asymptotics.S2op ((d : ℤ) / 2) (Work.CKFinal.Socket.F2 ℓ d hd r) τ
      = Work.Asymptotics.S2op ((d : ℤ) / 2) (layerFn ℓ d r) τ :=
    S2op_congr_three_aux _ (F2_agree_U0 ℓ d hd r hu0) (F2_agree_U0 ℓ d hd r hu1)
      (F2_agree_U0 ℓ d hd r hu2)
  rw [hcongr]
  have hcont := continuousAt_S2op_layerFn ℓ d hd r hU0 hu0 hu1 hu2
  have hseq : ∀ n : ℕ, ∃ σ : UpperHalfPlane, dist σ τ < 1/(n+1) ∧
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, (γ • σ).re ≠ 0 := by
    intro n
    obtain ⟨σ, hd', hf⟩ := F2_S2op_orbit_free_near τ (1/(n+1)) (by positivity)
    exact ⟨σ, hd', hf⟩
  choose σ hσ using hseq
  have htend : Filter.Tendsto σ Filter.atTop (𝓝 τ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (hσ n).1.le) ?_
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlim : Filter.Tendsto (fun n => Work.Asymptotics.S2op ((d : ℤ) / 2) (layerFn ℓ d r) (σ n))
      Filter.atTop (𝓝 (Work.Asymptotics.S2op ((d : ℤ) / 2) (layerFn ℓ d r) τ)) :=
    hcont.tendsto.comp htend
  have hzero : ∀ n, Work.Asymptotics.S2op ((d : ℤ) / 2) (layerFn ℓ d r) (σ n) = 0 :=
    fun n => S2op_paperLayer ℓ d hd r (σ n) (clean_of_orbit_free (hσ n).2)
  refine tendsto_nhds_unique hlim ?_
  rw [show (fun n => Work.Asymptotics.S2op ((d : ℤ) / 2) (layerFn ℓ d r) (σ n)) = fun _ => (0:ℂ)
    from funext hzero]
  exact tendsto_const_nhds

end Socket
end Work.CKFinal
