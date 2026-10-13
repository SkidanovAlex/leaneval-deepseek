import Mathlib
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef
import Submission.Work.WilE3.Frame.curve_analytic
import Submission.Work.WilE3.Frame.VcoefC_not_mem_range
import Submission.Work.WilE3.Frame.injective_iota_of_jacValC_ne_zero
import Submission.Work.WilE3.Frame.curve_tangent_unique
import Submission.Work.WilE3.Frame.straighteningDefs
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §2. The tangent of the straightened curve is the frame field -/

/-- **The tangent of the straightened curve is the frame field** (ambient form).  With `Ψ` an
analytic local inverse of the coordinate map `Φ = (ιᶜ-coordinates, h)` at `x` and `jacValC ≠ 0`
near `toC x`, the curve `u ↦ Ψ (u|_ιᶜ, 0)` has, near `toC x` and in every ambient direction
`l ∉ range ι`, the tangent vector `VcoefC c h ι l`: differentiating `Φ (cur u) = (u|_ιᶜ, 0)` gives
`uCoord ξ = e_{⟨l,_⟩}` and `Σ_i ξ_i (∂_i h_a)(cur u) = 0` for `ξ = fderiv cur u e_l`, and the
difference `ξ - VcoefC c h ι l (cur u)` vanishes by `eq_zero_of_support_and_tangent`. -/
theorem fderiv_cur_eq_VcoefC (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (x : Fin k → ℝ)
    (Ψ : ((U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : ∀ᶠ w in 𝓝 (uCoord k ι (toC x), 0), PhiC c h ι (Ψ w) = w)
    (hΨ0 : Ψ (uCoord k ι (toC x), 0) = toC x)
    (hΨan : AnalyticAt ℂ Ψ (uCoord k ι (toC x), 0))
    (hΔ : ∀ᶠ z in 𝓝 (toC x), jacValC c h ι z ≠ 0) :
    ∀ l : Fin k, l ∉ Set.range ι →
      ∀ᶠ u in 𝓝 (toC x),
        fderiv ℂ (fun u' : Fin k → ℂ => Ψ (uCoord k ι u', 0)) u (Pi.single l 1) =
          VcoefC c h ι l (Ψ (uCoord k ι u, 0)) := by
  classical
  intro l hl
  set z0 : Fin k → ℂ := toC x with hz0
  set u0 : U k ι → ℂ := uCoord k ι z0 with hu0
  let cur : (Fin k → ℂ) → (Fin k → ℂ) := fun u => Ψ (uCoord k ι u, 0)
  -- `jacValC` is nonzero at the base point
  have hz0j : jacValC c h ι z0 ≠ 0 := hΔ.self_of_nhds
  -- three open neighbourhoods of the base point
  obtain ⟨N, hNopen, hNmem, hNeq⟩ : ∃ N : Set ((U k ι → ℂ) × (Fin j → ℂ)),
      IsOpen N ∧ (u0, 0) ∈ N ∧ ∀ w ∈ N, PhiC c h ι (Ψ w) = w := by
    obtain ⟨s, hs, hse⟩ := Filter.eventually_iff_exists_mem.mp hΨ
    exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
      fun w hw => hse w (interior_subset hw)⟩
  obtain ⟨Na, hNaopen, hNamem, hNaan⟩ : ∃ Na : Set ((U k ι → ℂ) × (Fin j → ℂ)),
      IsOpen Na ∧ (u0, 0) ∈ Na ∧ ∀ w ∈ Na, AnalyticAt ℂ Ψ w := by
    obtain ⟨s, hs, hse⟩ := Filter.eventually_iff_exists_mem.mp hΨan.eventually_analyticAt
    exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
      fun w hw => hse w (interior_subset hw)⟩
  obtain ⟨Nz, hNzopen, hNzmem, hNzne⟩ : ∃ Nz : Set (Fin k → ℂ),
      IsOpen Nz ∧ z0 ∈ Nz ∧ ∀ z ∈ Nz, jacValC c h ι z ≠ 0 := by
    have hcont : ContinuousAt (jacValC c h ι) z0 :=
      (Work.WilE3.API.eaEvalC_fderiv_analytic c (jacDet c h ι) z0).1.continuousAt
    obtain ⟨s, hs, hse⟩ := Filter.eventually_iff_exists_mem.mp
      (hcont.preimage_mem_nhds (isOpen_ne.mem_nhds hz0j))
    exact ⟨interior s, isOpen_interior, mem_interior_iff_mem_nhds.mpr hs,
      fun z hz => hse z (interior_subset hz)⟩
  -- the parametrisation and the set of parameters in the domain of the straightening
  have hpair : Continuous fun u : Fin k → ℂ => (uCoord k ι u, (0 : Fin j → ℂ)) :=
    (ContinuousLinearMap.prod (uCoordL k ι)
      (0 : (Fin k → ℂ) →L[ℂ] (Fin j → ℂ))).continuous
  have hO1open : IsOpen {u : Fin k → ℂ | (uCoord k ι u, (0 : Fin j → ℂ)) ∈ N ∩ Na} :=
    IsOpen.preimage hpair (hNopen.inter hNaopen)
  have hO1mem : z0 ∈ {u : Fin k → ℂ | (uCoord k ι u, (0 : Fin j → ℂ)) ∈ N ∩ Na} :=
    ⟨hNmem, hNamem⟩
  have hcurcont : ContinuousAt cur z0 := by
    have h := ContinuousAt.comp (x := z0)
      (f := fun u : Fin k → ℂ => (uCoord k ι u, (0 : Fin j → ℂ))) (g := Ψ)
      hΨan.continuousAt hpair.continuousAt
    simpa only [cur, Function.comp_def] using h
  have hcur_z0 : cur z0 = z0 := by
    show Ψ (uCoord k ι z0, 0) = z0
    exact hΨ0
  have hgood : ∀ᶠ u in 𝓝 z0,
      u ∈ {u : Fin k → ℂ | (uCoord k ι u, (0 : Fin j → ℂ)) ∈ N ∩ Na} ∧ cur u ∈ Nz := by
    refine Filter.Eventually.and (hO1open.eventually_mem hO1mem) ?_
    exact hcurcont.tendsto.eventually
      (hNzopen.eventually_mem (by rw [hcur_z0]; exact hNzmem))
  refine hgood.mono ?_
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  have hgd : HasFDerivAt (fun u' : Fin k → ℂ => (uCoord k ι u', (0 : Fin j → ℂ)))
      ((uCoordL k ι).prod 0) u :=
    (hasFDerivAt_uCoord k ι u).prodMk (hasFDerivAt_const (0 : Fin j → ℂ) u)
  have hcurd : DifferentiableAt ℂ cur u :=
    (hNaan (uCoord k ι u, (0 : Fin j → ℂ)) hu1.2).differentiableAt.comp u hgd.differentiableAt
  -- `PhiC ∘ cur` is the injection of the `ι`-complement coordinates
  have hEv : (fun u' : Fin k → ℂ => PhiC c h ι (cur u')) =ᶠ[𝓝 u]
      (fun u' : Fin k → ℂ => (uCoord k ι u', (0 : Fin j → ℂ))) := by
    filter_upwards [hO1open.eventually_mem hu1] with u' hu'
    exact hNeq (uCoord k ι u', 0) hu'.1
  have hchain : fderiv ℂ (fun u' : Fin k → ℂ => PhiC c h ι (cur u')) u
      = (DPhiC c h ι (cur u)).comp (fderiv ℂ cur u) :=
    (HasFDerivAt.comp (x := u) (hasFDerivAt_PhiC' c h ι (cur u)) hcurd.hasFDerivAt).fderiv
  have hlin : fderiv ℂ (fun u' : Fin k → ℂ => (uCoord k ι u', (0 : Fin j → ℂ))) u
      = (uCoordL k ι).prod 0 := hgd.fderiv
  have hTo : (DPhiC c h ι (cur u)).comp (fderiv ℂ cur u) = (uCoordL k ι).prod 0 := by
    rw [← hchain, hEv.fderiv_eq, hlin]
  set ξ : Fin k → ℂ := fderiv ℂ cur u (Pi.single l 1) with hξdef
  have hPhi : DPhiC c h ι (cur u) ξ = (Pi.single ⟨l, hl⟩ (1 : ℂ), (0 : Fin j → ℂ)) := by
    have h2 := congrArg
      (fun T : (Fin k → ℂ) →L[ℂ] ((U k ι → ℂ) × (Fin j → ℂ)) => T (Pi.single l 1)) hTo
    simp only [ContinuousLinearMap.comp_apply] at h2
    rw [hξdef, h2, ContinuousLinearMap.prod_apply, uCoordL_single k ι hl]
    simp
  have hUcomp : uCoord k ι ξ = Pi.single ⟨l, hl⟩ (1 : ℂ) := by
    have h := DPhiC_fst c h ι (cur u) ξ
    rw [hPhi] at h
    simpa using h.symm
  have hHcomp : ∀ a : Fin j,
      ∑ i : Fin k, eaEvalC c (eaD c i (h a)) (cur u) * ξ i = 0 := by
    intro a
    have h := DPhiC_snd c h ι (cur u) ξ a
    rw [hPhi] at h
    simpa using h.symm
  have hUcond : ∀ i : Fin k, i ∉ Set.range ι → ξ i = if i = l then 1 else 0 := by
    intro i hi
    have h1 : ξ i = (Pi.single ⟨l, hl⟩ (1 : ℂ) : U k ι → ℂ) ⟨i, hi⟩ := by
      have h2 := congrFun hUcomp ⟨i, hi⟩
      simpa [uCoord] using h2
    rw [h1, Pi.single_apply]
    by_cases hh : i = l
    · have hs1 : (⟨i, hi⟩ : U k ι) = ⟨l, hl⟩ := Subtype.ext hh
      have hs2 : (⟨l, hl⟩ : U k ι) = ⟨i, hi⟩ := hs1.symm
      simp [hh, hs1, hs2]
    · have hs1 : ¬ ((⟨i, hi⟩ : U k ι) = ⟨l, hl⟩) := fun hc => hh (congrArg Subtype.val hc)
      have hs2 : ¬ ((⟨l, hl⟩ : U k ι) = ⟨i, hi⟩) := fun hc => hs1 hc.symm
      simp [hh, hs1, hs2]
  have hδ : ∀ i : Fin k, i ∉ Set.range ι → (ξ - VcoefC c h ι l (cur u)) i = 0 := by
    intro i hi
    rw [Pi.sub_apply, hUcond i hi, VcoefC_not_mem_range c h ι l (cur u) hi, sub_self]
  have hT : ∀ a : Fin j,
      ∑ i, (ξ - VcoefC c h ι l (cur u)) i * eaEvalC c (eaD c i (h a)) (cur u) = 0 := by
    intro a
    have hz : jacValC c h ι (cur u) ≠ 0 := hNzne (cur u) hu2
    have hV := VcoefC_tangent c h ι l (cur u) hz a
    have hξt : ∑ i, ξ i * eaEvalC c (eaD c i (h a)) (cur u) = 0 := by
      rw [← hHcomp a]
      exact Finset.sum_congr rfl fun i _ => mul_comm (ξ i) _
    have hsplit : ∀ i : Fin k, (ξ - VcoefC c h ι l (cur u)) i *
        eaEvalC c (eaD c i (h a)) (cur u)
        = ξ i * eaEvalC c (eaD c i (h a)) (cur u) -
          VcoefC c h ι l (cur u) i * eaEvalC c (eaD c i (h a)) (cur u) := by
      intro i
      rw [Pi.sub_apply]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_sub_distrib, hξt, hV, sub_zero]
  have huniq : ξ - VcoefC c h ι l (cur u) = 0 :=
    eq_zero_of_support_and_tangent c h ι (cur u) (hNzne (cur u) hu2) _ hδ hT
  exact sub_eq_zero.mp huniq


end

end Work.WilE3.Frame
