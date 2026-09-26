import Mathlib
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.ae_faceNoBend
import Submission.Work.Drive.Mono.arcHeightAux

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal
open scoped _root_.Topology

noncomputable section

/-!
# The no-bend lemma for the Γ-arcs

Auxiliary lemmas (chain rules, the Cramer solution of the crossing system, and the coordinate
formula for the derivative in `ℝ³`) and then `Work.Drive.Mono.gammaArc_noBend`.
-/

/-! ## Chain rules -/

/-- Chain rule: the derivative of `g ∘ β` for a differentiable `g` on the parameter plane. -/
theorem deriv_comp_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ × ℝ → E} {β : ℝ → ℝ × ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g (β t)) (hβ : DifferentiableAt ℝ β t) :
    deriv (fun u => g (β u)) t = (fderiv ℝ g (β t)) (deriv β t) :=
  (hg.hasFDerivAt.comp_hasDerivAt t hβ.hasDerivAt).deriv

/-- Chain rule for a continuous linear map on `ℝ³`. -/
theorem deriv_clm_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : R3 →L[ℝ] E) (γ : ℝ → R3) (x : ℝ) (h : DifferentiableAt ℝ γ x) :
    deriv (fun t => L (γ t)) x = L (deriv γ x) :=
  ((ContinuousLinearMap.hasFDerivAt L).comp_hasDerivAt x h.hasDerivAt).deriv

/-- **The coordinates of the derivative in `ℝ³`.** -/
theorem deriv_eq_toLp (γ : ℝ → R3) (x : ℝ) (h : DifferentiableAt ℝ γ x) :
    deriv γ x = WithLp.toLp 2 (fun k : Fin 3 => deriv (fun t => γ t k) x) := by
  set P := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ) with hP
  have h1 : deriv (fun t => P (γ t)) x = P (deriv γ x) :=
    ((ContinuousLinearEquiv.hasFDerivAt P).comp_hasDerivAt x h.hasDerivAt).deriv
  have h2 : (fun t => P (γ t)) = fun t k => γ t k := by
    funext t k; rw [PiLp.continuousLinearEquiv_apply]
  rw [h2] at h1
  have h3 : deriv (fun t k => γ t k) x = fun k => deriv (fun t => γ t k) x := by
    refine deriv_pi (fun k => ?_)
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k).differentiableAt.comp x h)
  rw [h3] at h1
  have h4 : (P.symm : (Fin 3 → ℝ) → R3) (fun k => deriv (fun t => γ t k) x) =
      WithLp.toLp 2 (fun k => deriv (fun t => γ t k) x) :=
    PiLp.continuousLinearEquiv_symm_apply 2 ℝ (fun _ : Fin 3 => ℝ) _
  calc deriv γ x = P.symm (P (deriv γ x)) := (ContinuousLinearEquiv.symm_apply_apply P _).symm
    _ = P.symm (fun k => deriv (fun t => γ t k) x) := by rw [h1]
    _ = WithLp.toLp 2 (fun k => deriv (fun t => γ t k) x) := h4

/-- The coordinate functions `y_{σ k} ∘ par` of the parametrisation are differentiable. -/
theorem differentiableAt_par_coord (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (k : Fin 3)
    (q : ℝ × ℝ) : DifferentiableAt ℝ (fun r => (Work.BoxShrink.Pinch.par ψ r) (σ k)) q :=
  ((contDiff_par_coord ψ σ k).differentiable (by decide)).differentiableAt

/-! ## Index bookkeeping -/

/-- Two of the three indices of `Fin 3` already being `i` and `2`, the third one is `j`. -/
theorem eq_of_ne_of_ne {i j k : Fin 3} (hi : i ≠ 2) (hji : j ≠ i) (hj2 : j ≠ 2)
    (hki : k ≠ i) (hk2 : k ≠ 2) : k = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- There is a third index besides `i` and `2`. -/
theorem exists_index_ne_two_ne (i : Fin 3) (hi : i ≠ 2) : ∃ j : Fin 3, j ≠ 2 ∧ j ≠ i := by
  fin_cases i
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact absurd rfl hi

/-! ## The Cramer system -/

theorem faceVertDet_two_ne_zero_of_invertible (ψ : Submission.Diffeo)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) {p : ℝ × ℝ}
    (hinv : (fderiv ℝ (facePairMap ψ σ i) p).IsInvertible) :
    faceVertDet ψ σ i 2 p ≠ 0 := by
  intro hdet
  have hA0 : fderiv ℝ (coordFun ψ σ i) p ≠ 0 :=
    fderiv_coordFun_ne_zero_of_invertible ψ σ i hinv
  obtain ⟨A, hA⟩ := hinv
  have hinj : Function.Injective (fderiv ℝ (facePairMap ψ σ i) p) := by
    rw [← hA]; exact A.injective
  have hdet' : (fderiv ℝ (coordFun ψ σ i) p) ((1 : ℝ), (0 : ℝ)) *
        (fderiv ℝ (coordFun ψ σ 2) p) ((0 : ℝ), (1 : ℝ)) -
      (fderiv ℝ (coordFun ψ σ i) p) ((0 : ℝ), (1 : ℝ)) *
        (fderiv ℝ (coordFun ψ σ 2) p) ((1 : ℝ), (0 : ℝ)) = 0 := hdet
  have hTne : (-(fderiv ℝ (coordFun ψ σ i) p) ((0 : ℝ), (1 : ℝ)),
      (fderiv ℝ (coordFun ψ σ i) p) ((1 : ℝ), (0 : ℝ))) ≠ 0 := by
    intro h0
    apply hA0
    refine ContinuousLinearMap.ext (fun v => ?_)
    rw [linCoord_apply_pair]
    have h1 : (fderiv ℝ (coordFun ψ σ i) p) ((0 : ℝ), (1 : ℝ)) = 0 := by
      have h := congrArg Prod.fst h0; simpa using h
    have h2 : (fderiv ℝ (coordFun ψ σ i) p) ((1 : ℝ), (0 : ℝ)) = 0 := by
      have h := congrArg Prod.snd h0; simpa using h
    rw [h1, h2]; simp
  have hkerT : fderiv ℝ (facePairMap ψ σ i) p
      (-(fderiv ℝ (coordFun ψ σ i) p) ((0 : ℝ), (1 : ℝ)),
        (fderiv ℝ (coordFun ψ σ i) p) ((1 : ℝ), (0 : ℝ))) = 0 := by
    rw [fderiv_facePairMap, ContinuousLinearMap.prod_apply]
    have h1 : (fderiv ℝ (coordFun ψ σ i) p)
        (-(fderiv ℝ (coordFun ψ σ i) p) ((0 : ℝ), (1 : ℝ)),
          (fderiv ℝ (coordFun ψ σ i) p) ((1 : ℝ), (0 : ℝ))) = 0 := by
      rw [linCoord_apply_pair]; ring
    have h2 : (fderiv ℝ (coordFun ψ σ 2) p)
        (-(fderiv ℝ (coordFun ψ σ i) p) ((0 : ℝ), (1 : ℝ)),
          (fderiv ℝ (coordFun ψ σ i) p) ((1 : ℝ), (0 : ℝ))) = 0 := by
      rw [linCoord_apply_pair]; linarith [hdet']
    rw [h1, h2]
    rfl
  exact hTne (hinj (by rw [hkerT, map_zero]))

/-- **Cramer's rule for the crossing system.**  A vector `v` with `A v = 0` and `B v = 1` is the
Hamiltonian field of `A` divided by the determinant. -/
theorem eq_smul_of_det {A B : ℝ × ℝ →L[ℝ] ℝ} {v : ℝ × ℝ}
    (hE : A ((1 : ℝ), (0 : ℝ)) * B ((0 : ℝ), (1 : ℝ)) -
      A ((0 : ℝ), (1 : ℝ)) * B ((1 : ℝ), (0 : ℝ)) ≠ 0)
    (h1 : A v = 0) (h2 : B v = 1) :
    v = (A ((1 : ℝ), (0 : ℝ)) * B ((0 : ℝ), (1 : ℝ)) -
        A ((0 : ℝ), (1 : ℝ)) * B ((1 : ℝ), (0 : ℝ)))⁻¹ •
      (-(A ((0 : ℝ), (1 : ℝ))), A ((1 : ℝ), (0 : ℝ))) := by
  set a : ℝ := A ((1 : ℝ), (0 : ℝ)) with ha
  set b : ℝ := A ((0 : ℝ), (1 : ℝ)) with hb
  set c' : ℝ := B ((1 : ℝ), (0 : ℝ)) with hc'
  set d : ℝ := B ((0 : ℝ), (1 : ℝ)) with hd
  have hΔ : a * d - b * c' ≠ 0 := hE
  have h1' : v.1 * a + v.2 * b = 0 := by
    have h := linCoord_apply_pair A v
    rw [h1] at h
    simpa [ha, hb] using h.symm
  have h2' : v.1 * c' + v.2 * d = 1 := by
    have h := linCoord_apply_pair B v
    rw [h2] at h
    simpa [hc', hd] using h.symm
  have hv1 : v.1 = (a * d - b * c')⁻¹ * (-b) := by
    have k1 := congrArg (fun x : ℝ => x * d) h1'
    have k2 := congrArg (fun x : ℝ => x * b) h2'
    have key : v.1 * (a * d - b * c') = -b := by nlinarith [k1, k2]
    rw [show (a * d - b * c')⁻¹ * (-b) = -b / (a * d - b * c') by ring,
      eq_div_iff hΔ]
    exact key
  have hv2 : v.2 = (a * d - b * c')⁻¹ * a := by
    have k1 := congrArg (fun x : ℝ => x * c') h1'
    have k2 := congrArg (fun x : ℝ => x * a) h2'
    have key : v.2 * (a * d - b * c') = a := by nlinarith [k1, k2]
    rw [show (a * d - b * c')⁻¹ * a = a / (a * d - b * c') by ring,
      eq_div_iff hΔ]
    exact key
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [hv1]; simp
  · rw [hv2]; simp

/-! ## The main lemma -/

/-- **`FaceNoBend` turns a vertical entry of a Γ-arc into a double zero of its horizontal
velocity.**  Let `γ` be a Γ-arc parametrised by height (`(γ t) (σ 2) = c (σ 2) + u + t`) lying in the
face `(γ t) (σ i) = c (σ i) + ε · boxSide i s` (`i ≠ 2`), with `γ = par ψ ∘ β`.  If the pair
`((y (σ i)) ∘ par, (y (σ 2)) ∘ par)` has invertible derivative on the crossing
(`Work.Drive.Mono.FaceCrossReg`) and a vertical-tangent crossing is a *double* zero of the
vertical-tangent determinant (`Work.Drive.Mono.FaceNoBend`), then `deriv γ 0 = e_{σ 2}` forces
`deriv (deriv γ) 0 = 0`: the arc `γ` touches the direction `e_{σ 2}` to second order at `t = 0`.
This is what makes the *vertical* arcs of the merged no-graze witness controllable
(`Submission/Work/Drive/Mono/NOTES_LEAD_gammaWitness.md` §1b and §2 step 5). -/
theorem gammaArc_noBend (ψ : Submission.Diffeo) {s u : ℝ}
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hX : Work.Drive.Mono.FaceCrossReg ψ c σ s u) (hFB : Work.Drive.Mono.FaceNoBend ψ c σ s u)
    {η : ℝ} (hη : 0 < η)
    {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {i : Fin 3} (hi : i ≠ 2)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {β : ℝ → ℝ × ℝ} (hβ : ContDiffOn ℝ 3 β (Set.Icc (-η) η))
    (hγβ : ∀ t ∈ Set.Icc (-η) η, Work.BoxShrink.Pinch.par ψ (β t) = γ t ∧
        (γ t) (σ i) = c (σ i) + ε * Submission.boxSide i * s)
    (hγh : ∀ t ∈ Set.Icc (-η) η, (γ t) (σ 2) = c (σ 2) + u + t) :
    deriv γ 0 = Work.BoxShrink.shiftVσ σ 1 → deriv (deriv γ) 0 = 0 := by
  intro hderiv
  classical
  obtain ⟨j, hj2, hji⟩ := exists_index_ne_two_ne i hi
  have hij : i ≠ j := fun h => hji h.symm
  -- ## neighbourhoods of `0`
  have h0Ioo : (0 : ℝ) ∈ Set.Ioo (-η) η := ⟨by linarith, by linarith⟩
  have h0Icc : (0 : ℝ) ∈ Set.Icc (-η) η := ⟨by linarith, by linarith⟩
  have hIcc_nhds0 : Set.Icc (-η) η ∈ 𝓝 (0 : ℝ) :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds h0Ioo) Set.Ioo_subset_Icc_self
  -- ## the two coordinate identities on the interval
  have hFi : ∀ t ∈ Set.Icc (-η) η, (Work.BoxShrink.Pinch.par ψ (β t)) (σ i) =
      c (σ i) + ε * Submission.boxSide i * s := by
    intro t ht
    rw [(hγβ t ht).1]
    exact (hγβ t ht).2
  have hG2 : ∀ t ∈ Set.Icc (-η) η, (Work.BoxShrink.Pinch.par ψ (β t)) (σ 2) =
      c (σ 2) + u + t := by
    intro t ht
    rw [(hγβ t ht).1]
    exact hγh t ht
  have hG20 : (Work.BoxShrink.Pinch.par ψ (β 0)) (σ 2) = c (σ 2) + u := by
    simpa using hG2 0 h0Icc
  -- ## `γ` agrees with `par ∘ β` near `0` and is differentiable there
  have hγβev : γ =ᶠ[𝓝 (0 : ℝ)] (fun t => Work.BoxShrink.Pinch.par ψ (β t)) :=
    Filter.eventually_of_mem hIcc_nhds0 (fun t ht => ((hγβ t ht).1).symm)
  have hβdiff : ∀ t ∈ Set.Ioo (-η) η, DifferentiableAt ℝ β t := by
    intro t ht
    exact (hβ.contDiffAt (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht)
      Set.Ioo_subset_Icc_self)).differentiableAt (by norm_num)
  have hparβdiff : ∀ t ∈ Set.Ioo (-η) η,
      DifferentiableAt ℝ (fun w => Work.BoxShrink.Pinch.par ψ (β w)) t := by
    intro t ht
    exact ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt.comp t
      (hβdiff t ht)
  have hγdiff : ∀ t ∈ Set.Ioo (-η) η, DifferentiableAt ℝ γ t := by
    intro t ht
    refine (hparβdiff t ht).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) Set.Ioo_subset_Icc_self)
      (fun w hw => ((hγβ w hw).1).symm)
  -- ## the two eventual descriptions of the coordinate functions
  have hFconst : (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ i)) =ᶠ[𝓝 (0 : ℝ)]
      fun _ => c (σ i) + ε * Submission.boxSide i * s :=
    Filter.eventually_of_mem hIcc_nhds0 (fun w hw => hFi w hw)
  have hGaff : (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ 2)) =ᶠ[𝓝 (0 : ℝ)]
      fun w => c (σ 2) + u + w :=
    Filter.eventually_of_mem hIcc_nhds0 (fun w hw => hG2 w hw)
  -- ## Cramer at `0`
  have hEne : faceVertDet ψ σ i 2 (β 0) ≠ 0 :=
    faceVertDet_two_ne_zero_of_invertible ψ σ i
      (hX i hi ε hε (β 0) (hFi 0 h0Icc) hG20)
  have hAv0 : (fderiv ℝ (coordFun ψ σ i) (β 0)) (deriv β 0) = 0 := by
    have h1 := deriv_comp_fderiv (g := coordFun ψ σ i) (β := β) (t := 0)
      (differentiableAt_par_coord ψ σ i (β 0)) (hβdiff 0 h0Ioo)
    rw [← h1]
    exact (Filter.EventuallyEq.deriv_eq hFconst).trans (deriv_const 0 _)
  have hBv0 : (fderiv ℝ (coordFun ψ σ 2) (β 0)) (deriv β 0) = 1 := by
    have h1 := deriv_comp_fderiv (g := coordFun ψ σ 2) (β := β) (t := 0)
      (differentiableAt_par_coord ψ σ 2 (β 0)) (hβdiff 0 h0Ioo)
    rw [← h1]
    have h2 : deriv (fun w : ℝ => c (σ 2) + u + w) 0 = 1 :=
      ((hasDerivAt_id (0 : ℝ)).const_add (c (σ 2) + u)).deriv
    rw [← h2]
    exact Filter.EventuallyEq.deriv_eq hGaff
  have hv0 : deriv β 0 = (faceVertDet ψ σ i 2 (β 0))⁻¹ • faceTangent ψ σ i (β 0) :=
    eq_smul_of_det (A := fderiv ℝ (coordFun ψ σ i) (β 0))
      (B := fderiv ℝ (coordFun ψ σ 2) (β 0)) (v := deriv β 0) hEne hAv0 hBv0
  have hTv : faceTangent ψ σ i (β 0) = faceVertDet ψ σ i 2 (β 0) • deriv β 0 := by
    rw [hv0, smul_smul, mul_inv_cancel₀ hEne, one_smul]
  -- ## the `σ j`-coordinate of the velocity at `0` vanishes
  have hφj0 : deriv (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ j)) 0 = 0 := by
    have hWj : (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ j)) =ᶠ[𝓝 (0 : ℝ)]
        (fun w => γ w (σ j)) := by
      filter_upwards [hγβev.symm] with w hw
      exact congrArg (fun z : R3 => z (σ j)) hw
    have h1 := deriv_clm_comp (coordCLM σ j) γ 0 (hγdiff 0 h0Ioo)
    have h2 : coordCLM σ j (deriv γ 0) = 0 := by
      rw [hderiv]
      show (Work.BoxShrink.shiftVσ σ 1) (σ j) = 0
      rw [Work.BoxShrink.shiftVσ_apply]
      have hne : σ j ≠ σ 2 := fun h => hj2 (σ.injective h)
      simp [hne]
    calc deriv (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ j)) 0
        = deriv (fun w => γ w (σ j)) 0 := Filter.EventuallyEq.deriv_eq hWj
      _ = deriv (fun t => coordCLM σ j (γ t)) 0 := rfl
      _ = coordCLM σ j (deriv γ 0) := h1
      _ = 0 := h2
  -- ## the trace is vertical at the crossing, and the determinant vanishes doubly there
  have hD0 : faceVertDet ψ σ i j (β 0) = 0 := by
    have h1 : faceVertDet ψ σ i j (β 0) =
        (fderiv ℝ (coordFun ψ σ j) (β 0)) (faceTangent ψ σ i (β 0)) :=
      (fderiv_coordFun_faceTangent ψ σ i j (β 0)).symm
    have h2 : (fderiv ℝ (coordFun ψ σ j) (β 0)) (faceTangent ψ σ i (β 0)) =
        faceVertDet ψ σ i 2 (β 0) *
          ((fderiv ℝ (coordFun ψ σ j) (β 0)) (deriv β 0)) := by
      rw [hTv, map_smul, smul_eq_mul]
    have h3 : (fderiv ℝ (coordFun ψ σ j) (β 0)) (deriv β 0) =
        deriv (fun w => coordFun ψ σ j (β w)) 0 :=
      (deriv_comp_fderiv (g := coordFun ψ σ j) (β := β) (t := 0)
        (differentiableAt_par_coord ψ σ j (β 0)) (hβdiff 0 h0Ioo)).symm
    rw [h1, h2, h3]
    show faceVertDet ψ σ i 2 (β 0) *
      deriv (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ j)) 0 = 0
    rw [hφj0, mul_zero]
  have hFB0 : fderiv ℝ (faceVertDet ψ σ i j) (β 0) (faceTangent ψ σ i (β 0)) = 0 :=
    hFB i j hi hj2 hij ε hε (β 0) (hFi 0 h0Icc) hG20 hD0
  have hDv0 : (fderiv ℝ (faceVertDet ψ σ i j) (β 0)) (deriv β 0) = 0 := by
    rw [hv0, map_smul, smul_eq_mul, hFB0, mul_zero]
  -- ## the derivative of the quotient `y (σ j) / y (σ 2)` along the arc
  have hDfun_diff : DifferentiableAt ℝ (faceVertDet ψ σ i j) (β 0) :=
    ((faceVertDet_contDiff_one ψ σ i j).differentiable (by norm_num)).differentiableAt
  have hEfun_diff : DifferentiableAt ℝ (faceVertDet ψ σ i 2) (β 0) :=
    ((faceVertDet_contDiff_one ψ σ i 2).differentiable (by norm_num)).differentiableAt
  have hDc : HasDerivAt (fun w => faceVertDet ψ σ i j (β w))
      ((fderiv ℝ (faceVertDet ψ σ i j) (β 0)) (deriv β 0)) 0 :=
    hDfun_diff.hasFDerivAt.comp_hasDerivAt 0 (hβdiff 0 h0Ioo).hasDerivAt
  have hEc : HasDerivAt (fun w => faceVertDet ψ σ i 2 (β w))
      ((fderiv ℝ (faceVertDet ψ σ i 2) (β 0)) (deriv β 0)) 0 :=
    hEfun_diff.hasFDerivAt.comp_hasDerivAt 0 (hβdiff 0 h0Ioo).hasDerivAt
  have hΨderiv : deriv (fun w => faceVertDet ψ σ i j (β w) / faceVertDet ψ σ i 2 (β w)) 0 = 0 := by
    have hfun : (fun w => faceVertDet ψ σ i j (β w) / faceVertDet ψ σ i 2 (β w)) =
        (fun w => faceVertDet ψ σ i j (β w)) / (fun w => faceVertDet ψ σ i 2 (β w)) := rfl
    rw [hfun, (hDc.div hEc hEne).deriv, hDv0, hD0]
    ring
  have hΨdiff : DifferentiableAt ℝ
      (fun w => faceVertDet ψ σ i j (β w) / faceVertDet ψ σ i 2 (β w)) 0 :=
    hDc.differentiableAt.div hEc.differentiableAt hEne
  -- ## `deriv φ_j` is that quotient
  have hHderiv : (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ j)) w) =ᶠ[𝓝 (0 : ℝ)]
      (fun w => faceVertDet ψ σ i j (β w) / faceVertDet ψ σ i 2 (β w)) := by
    have hcont : ContinuousAt (fun w : ℝ => faceVertDet ψ σ i 2 (β w)) 0 :=
      ContinuousAt.comp ((faceVertDet_contDiff_one ψ σ i 2).continuous.continuousAt)
        (hβdiff 0 h0Ioo).continuousAt
    have hEev : ∀ᶠ w in 𝓝 (0 : ℝ), faceVertDet ψ σ i 2 (β w) ≠ 0 :=
      hcont.eventually_ne hEne
    filter_upwards [isOpen_Ioo.mem_nhds h0Ioo, hEev] with w hw hEw
    have hmemIcc : Set.Icc (-η) η ∈ 𝓝 w :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds hw) Set.Ioo_subset_Icc_self
    have hβw : DifferentiableAt ℝ β w := hβdiff w hw
    have hFw : (fun v => (Work.BoxShrink.Pinch.par ψ (β v)) (σ i)) =ᶠ[𝓝 w]
        fun _ => c (σ i) + ε * Submission.boxSide i * s :=
      Filter.eventually_of_mem hmemIcc (fun v hv => hFi v hv)
    have hGw : (fun v => (Work.BoxShrink.Pinch.par ψ (β v)) (σ 2)) =ᶠ[𝓝 w]
        fun v => c (σ 2) + u + v :=
      Filter.eventually_of_mem hmemIcc (fun v hv => hG2 v hv)
    have hAw : (fderiv ℝ (coordFun ψ σ i) (β w)) (deriv β w) = 0 := by
      have h1 := deriv_comp_fderiv (g := coordFun ψ σ i) (β := β) (t := w)
        (differentiableAt_par_coord ψ σ i (β w)) hβw
      rw [← h1]
      exact (Filter.EventuallyEq.deriv_eq hFw).trans (deriv_const w _)
    have hBw : (fderiv ℝ (coordFun ψ σ 2) (β w)) (deriv β w) = 1 := by
      have h1 := deriv_comp_fderiv (g := coordFun ψ σ 2) (β := β) (t := w)
        (differentiableAt_par_coord ψ σ 2 (β w)) hβw
      rw [← h1]
      have h2 : deriv (fun v : ℝ => c (σ 2) + u + v) w = 1 :=
        ((hasDerivAt_id w).const_add (c (σ 2) + u)).deriv
      rw [← h2]
      exact Filter.EventuallyEq.deriv_eq hGw
    have hcram : deriv β w = (faceVertDet ψ σ i 2 (β w))⁻¹ • faceTangent ψ σ i (β w) :=
      eq_smul_of_det (A := fderiv ℝ (coordFun ψ σ i) (β w))
        (B := fderiv ℝ (coordFun ψ σ 2) (β w)) (v := deriv β w) hEw hAw hBw
    have hcomp : deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ j)) w =
        (fderiv ℝ (coordFun ψ σ j) (β w)) (deriv β w) :=
      deriv_comp_fderiv (g := coordFun ψ σ j) (β := β) (t := w)
        (differentiableAt_par_coord ψ σ j (β w)) hβw
    rw [hcomp, hcram, map_smul, smul_eq_mul, fderiv_coordFun_faceTangent]
    ring
  -- ## the three coordinate facts
  have hfact_i : DifferentiableAt ℝ
        (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ i)) w) 0 ∧
      deriv (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ i)) w) 0 = 0 := by
    have hd0 : deriv (fun _ : ℝ => c (σ i) + ε * Submission.boxSide i * s) = fun _ => (0 : ℝ) := by
      funext w; exact deriv_const w _
    have hd : deriv (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ i)) =ᶠ[𝓝 (0 : ℝ)]
        fun _ => (0 : ℝ) :=
      hFconst.deriv.trans (Filter.EventuallyEq.of_eq hd0)
    exact ⟨(differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hd,
      by rw [Filter.EventuallyEq.deriv_eq hd]; exact deriv_const 0 0⟩
  have hfact_2 : DifferentiableAt ℝ
        (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ 2)) w) 0 ∧
      deriv (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ 2)) w) 0 = 0 := by
    have hd0 : deriv (fun w : ℝ => c (σ 2) + u + w) = fun _ => (1 : ℝ) := by
      funext w
      exact ((hasDerivAt_id w).const_add (c (σ 2) + u)).deriv
    have hd : deriv (fun w => (Work.BoxShrink.Pinch.par ψ (β w)) (σ 2)) =ᶠ[𝓝 (0 : ℝ)]
        fun _ => (1 : ℝ) :=
      hGaff.deriv.trans (Filter.EventuallyEq.of_eq hd0)
    exact ⟨(differentiableAt_const (1 : ℝ)).congr_of_eventuallyEq hd,
      by rw [Filter.EventuallyEq.deriv_eq hd]; exact deriv_const 0 1⟩
  have hfact_j : DifferentiableAt ℝ
        (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ j)) w) 0 ∧
      deriv (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ j)) w) 0 = 0 :=
    ⟨hΨdiff.congr_of_eventuallyEq hHderiv,
      by rw [Filter.EventuallyEq.deriv_eq hHderiv]; exact hΨderiv⟩
  have hparfacts : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ k)) w) 0 ∧
      deriv (fun w => deriv (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ k)) w) 0 = 0 := by
    intro k
    rcases eq_or_ne k i with h | h
    · rw [h]; exact hfact_i
    · rcases eq_or_ne k (2 : Fin 3) with h2 | h2
      · rw [h2]; exact hfact_2
      · rw [eq_of_ne_of_ne hi hji hj2 h h2]; exact hfact_j
  have hcoord : ∀ k : Fin 3,
      DifferentiableAt ℝ (fun w => deriv (fun s => γ s (σ k)) w) 0 ∧
      deriv (fun w => deriv (fun s => γ s (σ k)) w) 0 = 0 := by
    intro k
    have hWγ : (fun s => (Work.BoxShrink.Pinch.par ψ (β s)) (σ k)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => γ s (σ k)) := by
      filter_upwards [hγβev.symm] with s hs
      exact congrArg (fun z : R3 => z (σ k)) hs
    have hd := hWγ.deriv
    refine ⟨(hparfacts k).1.congr_of_eventuallyEq hd.symm, ?_⟩
    rw [← Filter.EventuallyEq.deriv_eq hd]
    exact (hparfacts k).2
  have hDiff_all : ∀ m : Fin 3, DifferentiableAt ℝ (fun w => deriv (fun s => γ s m) w) 0 := by
    intro m
    have h := (hcoord (σ.symm m)).1
    simpa [Equiv.apply_symm_apply] using h
  have hVal_all : ∀ m : Fin 3, deriv (fun w => deriv (fun s => γ s m) w) 0 = 0 := by
    intro m
    have h := (hcoord (σ.symm m)).2
    simpa [Equiv.apply_symm_apply] using h
  -- ## conclude for the vector derivative
  set P := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ) with hP
  have hγderiv_ae : deriv γ =ᶠ[𝓝 (0 : ℝ)]
      (fun w => WithLp.toLp 2 (fun m : Fin 3 => deriv (fun s => γ s m) w)) := by
    filter_upwards [Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0Ioo)
      (fun w hw => hγdiff w hw)] with w hw
    exact deriv_eq_toLp γ w hw
  have hΞeq : (fun w : ℝ => WithLp.toLp 2 (fun m : Fin 3 => deriv (fun s => γ s m) w)) =
      fun w => P.symm (fun m : Fin 3 => deriv (fun s => γ s m) w) := by
    funext w; rw [PiLp.continuousLinearEquiv_symm_apply]
  calc deriv (deriv γ) 0
      = deriv (fun w => WithLp.toLp 2 (fun m : Fin 3 => deriv (fun s => γ s m) w)) 0 :=
        Filter.EventuallyEq.deriv_eq hγderiv_ae
    _ = deriv (fun w => P.symm (fun m : Fin 3 => deriv (fun s => γ s m) w)) 0 := by rw [hΞeq]
    _ = P.symm (deriv (fun w => fun m : Fin 3 => deriv (fun s => γ s m) w) 0) :=
        ((ContinuousLinearEquiv.hasFDerivAt P.symm).comp_hasDerivAt 0
          (differentiableAt_pi.mpr (fun m => hDiff_all m)).hasDerivAt).deriv
    _ = P.symm (fun m : Fin 3 => deriv (fun w => deriv (fun s => γ s m) w) 0) := by
        congr 1
        exact deriv_pi (fun m => hDiff_all m)
    _ = P.symm 0 := by
        congr 1
        funext m
        exact hVal_all m
    _ = 0 := map_zero P.symm

end

end Work.Drive.Mono
