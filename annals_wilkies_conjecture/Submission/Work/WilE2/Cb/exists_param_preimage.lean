import Mathlib
import Submission.Work.WilE9G.Sard.Basic

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace Work.WilE2.Cb

/-- A vector of `Fin (m+1) → ℝ` vanishing on every coordinate `i.succAbove k` is a multiple of
`Pi.single i 1`. -/
private lemma eq_smul_single_of_succAbove_eq_zero {m : ℕ} (i : Fin (m+1)) (d : Fin (m+1) → ℝ)
    (hd : ∀ k, d (i.succAbove k) = 0) :
    d = d i • (Pi.single i (1:ℝ) : Fin (m+1) → ℝ) := by
  funext j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨k, hk⟩
  · subst h
    simp
  · rw [hk, hd k, Pi.smul_apply, Pi.single_eq_of_ne (Fin.succAbove_ne i k), smul_zero]

/-- **The tangent space of a local level set is the range of the derivative of the
parametrisation.**  Let `F : ℝ^{m+1} → ℝ` be `C²`, `i` a coordinate, `h : ℝ^m → ℝ` differentiable
at `u`, and suppose that `F` vanishes on the graph `u' ↦ Fin.insertNth i (h u') u'` near `u`, the
`i`-th partial derivative of `F` at the base point being nonzero.  Then every vector `v` in the
kernel of `fderiv F` at the base point is the derivative at `u` of the parametrisation. -/
theorem exists_param_preimage {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (i : Fin (m+1)) {h : (Fin m → ℝ) → ℝ} {u : Fin m → ℝ}
    (hhd : DifferentiableAt ℝ h u)
    (hzero : ∀ᶠ u' in nhds u, F (Fin.insertNth i (h u') u') = 0)
    (hne : fderiv ℝ F (Fin.insertNth i (h u) u) (Pi.single i 1) ≠ 0)
    {v : Fin (m+1) → ℝ} (hv : fderiv ℝ F (Fin.insertNth i (h u) u) v = 0) :
    ∃ z : Fin m → ℝ, fderiv ℝ (fun u' : Fin m → ℝ => Fin.insertNth i (h u') u') u z = v := by
  classical
  set Φ : (Fin m → ℝ) → (Fin (m+1) → ℝ) := fun u' => Fin.insertNth i (h u') u' with hΦ
  set L : (Fin m → ℝ) →L[ℝ] (Fin (m+1) → ℝ) :=
    (Work.WilE9G.Sard.insCLM m i).comp
      ((fderiv ℝ h u).prod (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))) with hL
  -- the parametrisation is differentiable at `u` with derivative `L`
  have hpair : HasFDerivAt (fun u' : Fin m → ℝ => (h u', u'))
      ((fderiv ℝ h u).prod (1 : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))) u :=
    hhd.hasFDerivAt.prodMk (hasFDerivAt_id u)
  have hsub : HasFDerivAt
      (fun u' : Fin m → ℝ => (Work.WilE9G.Sard.insCLM m i) (h u', u')) L u :=
    (Work.WilE9G.Sard.insCLM m i).hasFDerivAt.comp u hpair
  have hΦd : HasFDerivAt Φ L u := by
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards with u'
    rw [hΦ, Work.WilE9G.Sard.insCLM_apply]
  -- the coordinates of `L z`
  have hL_apply : ∀ z : Fin m → ℝ, L z = Fin.insertNth i (fderiv ℝ h u z) z := by
    intro z
    rw [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      Work.WilE9G.Sard.insCLM_apply]
    rfl
  have hcoord : ∀ (z : Fin m → ℝ) (k : Fin m), L z (i.succAbove k) = z k := by
    intro z k
    rw [hL_apply z, Fin.insertNth_apply_succAbove]
  -- the differential of `F` vanishes on the image of `L` (chain rule + `F ∘ Φ = 0` near `u`)
  have hFd : HasFDerivAt F (fderiv ℝ F (Fin.insertNth i (h u) u)) (Φ u) :=
    (((hF.contDiffAt (x := Φ u)).of_le (one_le_two : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt_one).hasFDerivAt
  have hz' : (fun u' : Fin m → ℝ => F (Fin.insertNth i (h u') u')) =ᶠ[𝓝 u] (fun _ => (0:ℝ)) :=
    hzero
  have hchain : (fderiv ℝ F (Φ u)).comp L = 0 := by
    have h1 : fderiv ℝ (fun u' : Fin m → ℝ => F (Fin.insertNth i (h u') u')) u
        = (fderiv ℝ F (Φ u)).comp L := (hFd.comp u hΦd).fderiv
    rw [← h1, hz'.fderiv_eq]
    simp
  have hker : ∀ z : Fin m → ℝ, fderiv ℝ F (Fin.insertNth i (h u) u) (L z) = 0 := by
    intro z
    have h := DFunLike.congr_fun hchain z
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] using h
  -- the candidate preimage of `v`
  refine ⟨fun k => v (i.succAbove k), ?_⟩
  rw [hΦd.fderiv]
  set z₀ : Fin m → ℝ := fun k => v (i.succAbove k) with hz₀
  have hd0 : fderiv ℝ F (Fin.insertNth i (h u) u) (v - L z₀) = 0 := by
    rw [map_sub, hker z₀, hv, sub_zero]
  have hdec : v - L z₀ = (v - L z₀) i • (Pi.single i (1:ℝ) : Fin (m+1) → ℝ) :=
    eq_smul_single_of_succAbove_eq_zero i (v - L z₀) (fun k => by
      rw [Pi.sub_apply, hcoord z₀ k, hz₀]
      simp)
  have hdi : (v - L z₀) i = 0 := by
    have h1 : fderiv ℝ F (Fin.insertNth i (h u) u)
        ((v - L z₀) i • (Pi.single i (1:ℝ) : Fin (m+1) → ℝ)) = 0 := by
      rw [← hdec]; exact hd0
    rw [map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right hne
  have hz : v - L z₀ = 0 := by rw [hdec, hdi, zero_smul]
  exact (sub_eq_zero.mp hz).symm

end Work.WilE2.Cb
