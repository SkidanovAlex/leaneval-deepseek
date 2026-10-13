import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.straighteningDefs
import Submission.Work.WilE3.Frame.VcoefC_not_mem_range
import Submission.Work.WilE3.Frame.injective_iota_of_jacValC_ne_zero

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-- The coordinate map `PhiC` is complex differentiable, with derivative `DPhiC`. -/
private lemma hasFDerivAt_PhiC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (z : Fin k → ℂ) : HasFDerivAt (PhiC c h ι) (DPhiC c h ι z) z := by
  have h1 : HasFDerivAt (fun z : Fin k → ℂ => uCoord k ι z)
      (ContinuousLinearMap.pi fun i : U k ι =>
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1) z :=
    (ContinuousLinearMap.pi (fun i : U k ι =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i.1)).hasFDerivAt
  have h2 : HasFDerivAt (fun z : Fin k → ℂ => fun a : Fin j => eaEvalC c (h a) z)
      (ContinuousLinearMap.pi fun a : Fin j =>
        ∑ i : Fin k, (eaEvalC c (eaD c i (h a)) z) •
          ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => ℂ) i) z := by
    rw [hasFDerivAt_pi]
    intro a
    exact (Work.WilE3.API.eaEvalC_fderiv_analytic c (h a) z).2
  exact h1.prodMk h2

/-- Uniqueness of a vector supported on the `ι`-coordinates which is tangent to `{h = 0}`: if
`δ` vanishes off `Set.range ι` and kills every `(∂_i h_a)(z)`, at a point `z` where the `ι`-Jacobian
of `h` is invertible, then `δ = 0`. -/
private lemma eq_zero_of_support_range_and_tangent' {k r j : ℕ} (c : EAChain k r)
    (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (z : Fin k → ℂ)
    (hz : jacValC c h ι z ≠ 0) (δ : Fin k → ℂ)
    (hδ : ∀ i : Fin k, i ∉ Set.range ι → δ i = 0)
    (hT : ∀ a : Fin j, ∑ i, δ i * eaEvalC c (eaD c i (h a)) z = 0) :
    δ = 0 := by
  classical
  have hinj : Function.Injective ι := injective_iota_of_jacValC_ne_zero c h ι z hz
  -- the tangency sums only see the `ι`-coordinates of `δ`
  have hsum : ∀ a : Fin j, (∑ i : Fin k, δ i * eaEvalC c (eaD c i (h a)) z)
      = ∑ b : Fin j, δ (ι b) * eaEvalC c (eaD c (ι b) (h a)) z := by
    intro a
    have hsub : (Finset.univ.filter fun i : Fin k => i ∈ Set.range ι) ⊆ Finset.univ :=
      fun x _ => Finset.mem_univ x
    rw [← Finset.sum_subset hsub (fun x _ hxs => by
      rw [Finset.mem_filter] at hxs
      have hxr : x ∉ Set.range ι := fun hxr => hxs ⟨Finset.mem_univ x, hxr⟩
      rw [hδ x hxr, zero_mul])]
    have hfilter : (Finset.univ.filter fun i : Fin k => i ∈ Set.range ι) =
        Finset.univ.image ι := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
    rw [hfilter, Finset.sum_image]
    intro x _ y _ hxy
    exact hinj hxy
  -- the matrix-vector form of the tangency condition
  have hMv : (jacMatC c h ι z) *ᵥ (fun b : Fin j => δ (ι b)) = 0 := by
    funext a
    rw [Matrix.mulVec_apply_eq_sum]
    have h1 : (∑ j : Fin j, jacMatC c h ι z a j * δ (ι j))
        = ∑ j : Fin j, δ (ι j) * eaEvalC c (eaD c (ι j) (h a)) z := by
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [jacMatC, Matrix.of_apply]
      ring
    rw [h1, ← hsum a]
    exact hT a
  have hdet : (jacMatC c h ι z).det ≠ 0 := by
    rw [← jacValC_eq_det]
    exact hz
  have hx : (fun b : Fin j => δ (ι b)) = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdet hMv
  funext i
  by_cases hi : i ∈ Set.range ι
  · obtain ⟨b, rfl⟩ := hi
    exact congrFun hx b
  · exact hδ i hi

/-- **The tangent of the straightened curve is the frame field.**  Let `Ψ` be the (complex-analytic)
local inverse of the coordinate map `Φ = (ι^c-coordinates, h)` (`exists_param`).  Then the curve
`v ↦ Ψ (v, 0)` — the germ of `{h = 0}` near `x` — has, at every nearby `v`, the tangent vector
carried by the frame field `VcoefC c h ι l` of `Vcoef.lean`: both are tangent to `{h = 0}` (the curve
lies in the fibre `Φ = (u,0)`, hence in `{h = 0}`) and both have `l`-th `ι^c`-coordinate `1`.

This identifies the ordered frame derivatives of `E3_identity` with the ordinary derivatives along
`{h = 0}`. -/
theorem fderiv_curve_eq_VcoefC {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) (x : Fin k → ℝ)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : ∀ᶠ w in 𝓝 (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0),
      Work.WilE3.Frame.PhiC c h ι (Ψ w) = w)
    (hΨ0 : Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0) =
      Work.WilE3.Frame.toC x)
    (hΨan : AnalyticAt ℂ Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x), 0))
    (hd : (Matrix.of fun a b => eaEvalC c (eaD c (ι b) (h a))
      (Work.WilE3.Frame.toC x)).det ≠ 0) :
    ∀ l : Work.WilE3.Frame.U k ι,
      ∀ᶠ v in 𝓝 (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x)),
        fderiv ℂ (fun v' : Work.WilE3.Frame.U k ι → ℂ => Ψ (v', 0)) v (Pi.single l 1) =
          Work.WilE3.Frame.VcoefC c h ι (l : Fin k) (Ψ (v, 0)) := by
  classical
  intro l
  -- rename the base point and the curve
  set u0 : U k ι → ℂ := uCoord k ι (toC x) with hu0
  set z0 : Fin k → ℂ := toC x with hz0
  let F : (U k ι → ℂ) → (Fin k → ℂ) := fun v' => Ψ (v', 0)
  let inc : (U k ι → ℂ) →L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ)) :=
    ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ)
  have hinc_apply : ∀ v' : U k ι → ℂ, inc v' = (v', 0) := fun v' => rfl
  -- the Jacobian is invertible at `z0`
  have hz0j : jacValC c h ι z0 ≠ 0 := by
    rw [jacValC_eq_det]
    exact hd
  -- three open neighbourhoods of the base point
  obtain ⟨N, hN_open, hN_mem, hN_eq⟩ : ∃ N : Set ((U k ι → ℂ) × (Fin j → ℂ)),
      IsOpen N ∧ (u0, 0) ∈ N ∧ ∀ w ∈ N, PhiC c h ι (Ψ w) = w := by
    obtain ⟨s, hs, hse⟩ := Filter.eventually_iff_exists_mem.mp hΨ
    exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
      fun w hw => hse w (interior_subset hw)⟩
  obtain ⟨Na, hNa_open, hNa_mem, hNa_an⟩ : ∃ Na : Set ((U k ι → ℂ) × (Fin j → ℂ)),
      IsOpen Na ∧ (u0, 0) ∈ Na ∧ ∀ w ∈ Na, AnalyticAt ℂ Ψ w := by
    obtain ⟨s, hs, hse⟩ := Filter.eventually_iff_exists_mem.mp hΨan.eventually_analyticAt
    exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
      fun w hw => hse w (interior_subset hw)⟩
  obtain ⟨Nz, hNz_open, hNz_mem, hNz_ne⟩ : ∃ Nz : Set (Fin k → ℂ),
      IsOpen Nz ∧ z0 ∈ Nz ∧ ∀ z ∈ Nz, jacValC c h ι z ≠ 0 := by
    have hcont : ContinuousAt (jacValC c h ι) z0 := by
      have h := (Work.WilE3.API.eaEvalC_fderiv_analytic c (jacDet c h ι) z0).1
      exact h.continuousAt
    obtain ⟨s, hs, hse⟩ := Filter.eventually_iff_exists_mem.mp
      (hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hz0j))
    exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
      fun z hz => hse z (interior_subset hz)⟩
  -- the set of parameters that are in the domain of the straightening
  have hO1_open : IsOpen {v : U k ι → ℂ | (v, 0) ∈ N ∩ Na} := by
    have hc : Continuous fun v : U k ι → ℂ => (v, (0 : Fin j → ℂ)) := by fun_prop
    exact IsOpen.preimage hc (hN_open.inter hNa_open)
  have hO1_mem : u0 ∈ {v : U k ι → ℂ | (v, 0) ∈ N ∩ Na} := ⟨hN_mem, hNa_mem⟩
  have hF_u0 : F u0 = z0 := by
    show Ψ (u0, 0) = z0
    exact hΨ0
  have hF_cont : ContinuousAt F u0 :=
    ContinuousAt.comp (x := u0) (f := ⇑inc) (g := Ψ) hΨan.continuousAt
      inc.continuous.continuousAt
  -- the good set of parameters is a neighbourhood of `u0`
  have hmem : ∀ᶠ v in 𝓝 u0, (v, 0) ∈ N ∩ Na ∧ F v ∈ Nz := by
    refine Filter.Eventually.and ?_ ?_
    · exact hO1_open.eventually_mem hO1_mem
    · exact hF_cont.tendsto.eventually
        (hNz_open.eventually_mem (by rw [hF_u0]; exact hNz_mem))
  refine hmem.mono ?_
  intro v hv
  obtain ⟨hvN, hvZ⟩ := hv
  change fderiv ℂ F v (Pi.single l 1) = VcoefC c h ι (l : Fin k) (F v)
  have hF_v_dz : DifferentiableAt ℂ F v :=
    DifferentiableAt.comp (x := v) ((hNa_an (v, 0) hvN.2).differentiableAt) inc.differentiableAt
  set ξ : Fin k → ℂ := fderiv ℂ F v (Pi.single l 1) with hξ
  -- `PhiC ∘ F` is the inclusion of the `ι`-complement coordinates
  have hEv : (fun v' => PhiC c h ι (F v')) =ᶠ[𝓝 v] (fun v' : U k ι → ℂ => (v', 0)) := by
    filter_upwards [hO1_open.eventually_mem hvN] with v' hv'
    exact hN_eq (v', 0) hv'.1
  have hderiv_comp : fderiv ℂ (fun v' => PhiC c h ι (F v')) v
      = (DPhiC c h ι (F v)).comp (fderiv ℂ F v) := by
    have h1 : HasFDerivAt (fun v' : U k ι → ℂ => PhiC c h ι (F v'))
        ((DPhiC c h ι (F v)).comp (fderiv ℂ F v)) v :=
      HasFDerivAt.comp (x := v) (hasFDerivAt_PhiC c h ι (F v)) hF_v_dz.hasFDerivAt
    exact h1.fderiv
  have hlin : fderiv ℂ (fun v' : U k ι → ℂ => (v', 0)) v = inc := by
    exact (hasFDerivAt_prodMk_left v (0 : Fin j → ℂ)).fderiv
  have hTo : (DPhiC c h ι (F v)).comp (fderiv ℂ F v) = inc := by
    rw [← hderiv_comp, hEv.fderiv_eq, hlin]
  -- the two conditions characterising `VcoefC`
  have hPhi_xi : DPhiC c h ι (F v) ξ = (Pi.single l 1, 0) := by
    have h2 := congrArg (fun T : (U k ι → ℂ) →L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ)) =>
      T (Pi.single l 1)) hTo
    simp only [ContinuousLinearMap.comp_apply, hinc_apply] at h2
    rw [hξ]
    exact h2
  have hUcomp : uCoord k ι ξ = Pi.single l 1 := by
    have h := DPhiC_fst c h ι (F v) ξ
    rw [hPhi_xi] at h
    simpa using h.symm
  have hHcomp : ∀ a : Fin j, ∑ i : Fin k, eaEvalC c (eaD c i (h a)) (F v) * ξ i = 0 := by
    intro a
    have h := DPhiC_snd c h ι (F v) ξ a
    rw [hPhi_xi] at h
    simpa using h.symm
  -- the `ι`-complement coordinates of `ξ` are those of `VcoefC`
  have hUcond : ∀ i : Fin k, i ∉ Set.range ι → ξ i = if i = (l : Fin k) then 1 else 0 := by
    intro i hi
    have h1 : ξ i = (Pi.single l 1 : U k ι → ℂ) ⟨i, hi⟩ := by
      have h2 := congrFun hUcomp ⟨i, hi⟩
      simpa [uCoord] using h2
    rw [h1, Pi.single_apply]
    by_cases hh : (⟨i, hi⟩ : U k ι) = l
    · have hh' : i = (l : Fin k) := congrArg Subtype.val hh
      simp [hh, hh']
    · have hh' : ¬ (i = (l : Fin k)) := fun hh'' => hh (Subtype.ext hh'')
      simp [hh, hh']
  have hH' : ∀ a : Fin j, ∑ i, ξ i * eaEvalC c (eaD c i (h a)) (F v) = 0 := by
    intro a
    rw [← hHcomp a]
    exact Finset.sum_congr rfl fun i _ => mul_comm (ξ i) _
  -- the difference is supported on the `ι`-coordinates
  have hδ : ∀ i : Fin k, i ∉ Set.range ι → (ξ - VcoefC c h ι (l : Fin k) (F v)) i = 0 := by
    intro i hi
    rw [Pi.sub_apply, hUcond i hi,
      VcoefC_not_mem_range c h ι (l : Fin k) (F v) hi, sub_self]
  have hT : ∀ a : Fin j, ∑ i, (ξ - VcoefC c h ι (l : Fin k) (F v)) i *
      eaEvalC c (eaD c i (h a)) (F v) = 0 := by
    intro a
    have hz : jacValC c h ι (F v) ≠ 0 := hNz_ne (F v) hvZ
    have hV := VcoefC_tangent c h ι (l : Fin k) (F v) hz a
    have hsplit : ∀ i : Fin k, (ξ - VcoefC c h ι (l : Fin k) (F v)) i *
        eaEvalC c (eaD c i (h a)) (F v)
        = ξ i * eaEvalC c (eaD c i (h a)) (F v) -
          VcoefC c h ι (l : Fin k) (F v) i * eaEvalC c (eaD c i (h a)) (F v) := by
      intro i
      rw [Pi.sub_apply]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib,
      hH' a, hV, sub_zero]
  have huniq : ξ - VcoefC c h ι (l : Fin k) (F v) = 0 :=
    eq_zero_of_support_range_and_tangent' c h ι (F v) (hNz_ne (F v) hvZ) _ hδ hT
  exact sub_eq_zero.mp huniq

end

end Work.WilE3.Frame
