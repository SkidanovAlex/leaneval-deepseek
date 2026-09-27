import Mathlib
import Submission.Work.Drive.mixedFactorTransfer
import Submission.Work.Drive.genFunctionalStable
import Submission.Work.Drive.genAlongTransfer
import Submission.Work.Drive.coreLoop_injective_mod_one
import Submission.Work.Drive.rotSweepEquivariance

/-!
# `(F1)` for the mixed factors of the reference triple

The mixed factor of block `k` of the `hn2` reference triple is the pairing of the *perturbed rotated
configuration chart* `chartPert (τ k) ∘ (rotCapping (u k) ∘ Q)` with the *perturbed reference plane*
`chartPert (τ 2) ∘ linPlaneChart φ lam hlampos`.  This file instantiates the proved
`Work.Drive.odd_coreSideCountPt_reference_mixed` (`Drive/mixedFactorTransfer.lean`) for that data,
with the genericity hypotheses reduced to a **single** hypothesis on the *unperturbed* functional:

> `Work.Drive.GenAlong (linFun φ ∘ (classEquiv (τ 2))⁻¹ ∘ classEquiv (τ k)) V`

(this is `(†)` of `F1_GENERICITY_RESOLUTION.md`), everything else being geometry:

* `Work.Drive.mem_projLine_chartPert_iff` — the dictionary "the class of the perturbed loop lies in
  the perturbed plane" ⟺ "the transported functional vanishes at the lift" (the input of `hinj`);
* `Work.Drive.odd_coreSideCountPt_rotCapping_of_genAlong` — the instantiated `(F1)`.

The point of the reduction is that `(†)` for a *small* perturbation is a consequence of the openness
of `GenAlong` (`Work.Drive.genAlong_open`) and the estimates of the class perturbation
(`Work.Drive.norm_classEquiv_sub_one_le`, `Work.Drive.exists_norm_classEquiv_symm_sub_one_lt`): the
reference functional `linFun φ` is chosen *once*, before the perturbation parameters, by
`Work.Drive.exists_genAlong_family` — see `F1_GENERICITY_RESOLUTION.md`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- The normal functional of a linear plane chart, as a *continuous* linear functional (the
underlying definition `Work.Drive.linFun` is only a linear map). -/
def linFunCLM (φ : Eucl 3 ≃L[ℝ] Eucl 3) : Eucl 3 →L[ℝ] ℝ :=
  (cproj 3) ∘L ((φ.symm : Eucl 3 →L[ℝ] Eucl 3))

@[simp] lemma linFunCLM_apply (φ : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    linFunCLM φ v = linFun φ v := by
  simp [linFunCLM, linFun, cproj]

/-- `GenAlong` depends only on the values of the functional. -/
lemma GenAlong_congr {ℓ ℓ' : Eucl 3 →L[ℝ] ℝ} (h : ∀ v : Eucl 3, ℓ v = ℓ' v) {V : ℝ → Eucl 3} :
    GenAlong ℓ V ↔ GenAlong ℓ' V := by
  have hV0 : ℓ (V 0) = ℓ' (V 0) := h (V 0)
  have hiff : ∀ t : ℝ, (ℓ (V t) = 0) ↔ (ℓ' (V t) = 0) := fun t => by rw [h (V t)]
  have hderiv : (fun s : ℝ => ℓ (V s)) = fun s : ℝ => ℓ' (V s) := funext fun s => h (V s)
  have hset : {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ ℓ (V t) = 0}
      = {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ ℓ' (V t) = 0} := by
    ext t
    simp only [Set.mem_setOf_eq]
    rw [hiff t]
  simp only [GenAlong, hV0, hderiv, hiff, hset]

/-- **The class-membership dictionary of a perturbed chart and a perturbed plane.**  For a lift `V` of
the class loop of `Q` and the perturbed chart `chartPert τ ∘ Q`, the class of the perturbed loop lies
in the plane of the perturbed functional `linFun (φ.trans (classEquiv σ))` exactly at the parameters
where the transported functional vanishes at the transported lift. -/
theorem mem_projLine_chartPert_iff {Q : ℂ → CappingSpace} {V : ℝ → Eucl 3}
    (hVne : ∀ t : ℝ, V t ≠ 0)
    (hVcls : ∀ t ∈ Icc (0 : ℝ) 1,
      Projectivization.mk ℝ (V t) (hVne t) = (cappingSpaceHomeoProj (coreLoop Q t)).2)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ σ : Eucl 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (cappingSpaceHomeoProj (coreLoop (chartPert τ ∘ Q) t)).2
        ∈ projLine (linSub (φ.trans (classEquiv σ)))
      ↔ linFun φ ((classEquiv σ).symm (classEquiv τ (V t))) = 0 := by
  have hkey : linFun (φ.trans (classEquiv σ)) (classEquiv τ (V t))
      = linFun φ ((classEquiv σ).symm (classEquiv τ (V t))) := by
    have h := linFun_trans_classEquiv φ σ ((classEquiv σ).symm (classEquiv τ (V t)))
    simpa using h
  rw [class_coreLoop_chartPert τ Q t, ← hVcls t ht, classMap_mk τ (V t) (hVne t),
    mk_mem_projLine_iff _ (classEquiv_ne_zero (hVne t)), hkey]

/-- **`(F1)` for the mixed factors of the reference triple.**  The pairing of the perturbed rotated
configuration chart with the perturbed reference plane is odd, from

* the level bands of the configuration chart (`c ≤ levelOf (Q z) ≤ β`, `β < lam`) and the smallness
  conditions `c₂ ≤ levelScale τ c`, `levelScale τ β < levelScale σ lam`;
* a *smooth* nonvanishing lift `V` of the class loop of the rotated configuration chart, with the
  essentiality `V 1 = κ • V 0`, `κ < 0`;
* **the single genericity hypothesis** `GenAlong (linFun φ ∘ (classEquiv σ)⁻¹ ∘ classEquiv τ) V`.

The chart injectivity clause of `(F1)` is *derived* here: the loop of the perturbed chart is injective
up to its period (from `Work.Drive.coreLoop_injective_mod_one` for `Q` and the injectivity of
`rotCapping u` and of `chartPert τ`), and neither `0` nor `1` is a meet parameter (from the `hV0`
clause of the genericity and from `V 1 = κ V 0`). -/
theorem odd_coreSideCountPt_rotCapping_of_genAlong {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) (u : UnitAddCircle)
    {c β lam c₂ : ℝ} (hc : 0 < c) (hc₂ : 0 < c₂) (hβpos : 0 < β) (hlampos : 0 < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    {τ σ : Eucl 3}
    (hc₂le : c₂ ≤ ((levelScale τ ⟨c, hc⟩ : Set.Ioi (0 : ℝ)) : ℝ))
    (hβσ : ((levelScale τ ⟨β, hβpos⟩ : Set.Ioi (0 : ℝ)) : ℝ)
        < ((levelScale σ ⟨lam, hlampos⟩ : Set.Ioi (0 : ℝ)) : ℝ))
    (V : ℝ → Eucl 3) (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hVne : ∀ t : ℝ, V t ≠ 0)
    (hVcls : ∀ t ∈ Icc (0 : ℝ) 1, Projectivization.mk ℝ (V t) (hVne t)
      = (cappingSpaceHomeoProj (coreLoop (fun z => rotCapping u (Q z)) t)).2)
    {κ : ℝ} (hκ : κ < 0) (hesse : V 1 = κ • V 0)
    (hgen : GenAlong ((linFunCLM φ) ∘L (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
      ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3))) V) :
    Odd (coreSideCountPt (chartPert τ ∘ fun z => rotCapping u (Q z)) c₂
      (diskPlane (chartPert σ ∘ linPlaneChart φ lam hlampos))) := by
  classical
  -- ## notational setup
  set Q' : ℂ → CappingSpace := fun z => rotCapping u (Q z) with hQ'def
  set ℓ : Eucl 3 →L[ℝ] ℝ := linFunCLM φ with hℓdef
  set B : Eucl 3 →L[ℝ] Eucl 3 :=
    (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3))
    with hBdef
  have hkey : ∀ w : Eucl 3, linFun (φ.trans (classEquiv σ)) (classEquiv τ w) = ℓ (B w) := by
    intro w
    have h := linFun_trans_classEquiv φ σ ((classEquiv σ).symm (classEquiv τ w))
    simp only [ContinuousLinearEquiv.apply_symm_apply] at h
    rw [hBdef, linFunCLM_apply]
    exact h
  have hfun : (fun t : ℝ => linFun (φ.trans (classEquiv σ)) (classEquiv τ (V t)))
      = fun t : ℝ => ℓ (B (V t)) := funext fun t => hkey (V t)
  -- ## the seam clauses
  have hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z := fun z hz => hQ.2.2.1 z hz
  have hQ'seam : ∀ z : ℂ, ‖z‖ = 1 → Q' (-z) = Q' z := by
    intro z hz
    simp only [hQ'def, Function.comp_apply]
    rw [hQseam z hz]
  -- ## the essentiality and the non-vanishing at `0`
  have hV0gen : ℓ (B (V 0)) ≠ 0 := hgen.1
  have hV0 : linFun (φ.trans (classEquiv σ)) (classEquiv τ (V 0)) ≠ 0 := by
    rw [hkey]; exact hV0gen
  -- ## the perturbed loop and its injectivity up to the period
  have hInjQ : ∀ s s' : ℝ, coreLoop Q s = coreLoop Q s' → ∃ k : ℤ, s' = s + k :=
    fun s s' h => coreLoop_injective_mod_one hγ hγne hQ h
  have hInjQ' : ∀ s s' : ℝ, coreLoop Q' s = coreLoop Q' s' → ∃ k : ℤ, s' = s + k := by
    intro s s' h
    have h' : coreLoop Q s = coreLoop Q s' := by
      have h2 : rotCapping u (coreLoop Q s) = rotCapping u (coreLoop Q s') := h
      exact rotCapping_injective u h2
    exact hInjQ s s' h'
  have hInjPert : ∀ s s' : ℝ,
      coreLoop (chartPert τ ∘ Q') s = coreLoop (chartPert τ ∘ Q') s' → ∃ k : ℤ, s' = s + k := by
    intro s s' h
    have h' : coreLoop Q' s = coreLoop Q' s' := chartPert_injective τ h
    exact hInjQ' s s' h'
  -- ## the two endpoint parameters are not meet parameters
  have hloopClosed : coreLoop (chartPert τ ∘ Q') 0 = coreLoop (chartPert τ ∘ Q') 1 :=
    coreLoop_zero_eq_one (Q := chartPert τ ∘ Q') (fun z hz => by
      simp only [Function.comp_apply]
      rw [hQ'seam z hz])
  have hmem0 : (cappingSpaceHomeoProj (coreLoop (chartPert τ ∘ Q') 0)).2
      ∉ projLine (linSub (φ.trans (classEquiv σ))) := by
    rw [mem_projLine_chartPert_iff (Q := Q') hVne hVcls φ τ σ (left_mem_Icc.mpr zero_le_one)]
    simpa [hℓdef, hBdef] using hV0gen
  have hnot1 : (1 : ℝ) ∉ {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      (cappingSpaceHomeoProj (coreLoop (chartPert τ ∘ Q') t)).2
        ∈ projLine (linSub (φ.trans (classEquiv σ)))} := by
    rintro ⟨-, hmem⟩
    exact hmem0 (by rw [hloopClosed]; exact hmem)
  -- ## the chart injectivity clause of `(F1)`
  have hinj : Set.InjOn (coreLoop (chartPert τ ∘ Q'))
      {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        (cappingSpaceHomeoProj (coreLoop (chartPert τ ∘ Q') t)).2
          ∈ projLine (linSub (φ.trans (classEquiv σ)))} := by
    intro s hs s' hs' heq
    have hsne : s ≠ 1 := fun h => hnot1 (h ▸ hs)
    have hs'ne : s' ≠ 1 := fun h => hnot1 (h ▸ hs')
    obtain ⟨k, hk⟩ := hInjPert s s' heq
    have hs1 : s < 1 := lt_of_le_of_ne hs.1.2 hsne
    have hs'1 : s' < 1 := lt_of_le_of_ne hs'.1.2 hs'ne
    have hkz : k = 0 := by
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have : (k : ℝ) ≤ -1 := by
          have : k ≤ -1 := by omega
          exact_mod_cast this
        have : s' ≤ -1 + 1 := by
          rw [hk]; push_cast; linarith [hs.1.1]
        linarith [hs'.1.1]
      · exact hk0
      · have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
        have : 1 + 0 < s' := by rw [hk]; push_cast; linarith [hs.1.1]
        linarith [hs'1]
    rw [hk, hkz]; push_cast; ring
  -- ## the remaining hypotheses of `(F1)`
  have hder : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => linFun (φ.trans (classEquiv σ)) (classEquiv τ (V t)))
        (deriv (fun t : ℝ => linFun (φ.trans (classEquiv σ)) (classEquiv τ (V t))) x) x := by
    intro x _
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ℓ (B (V t))) :=
      (ℓ ∘L B).contDiff.comp hVs
    have hdx : HasDerivAt (fun t : ℝ => ℓ (B (V t)))
        (deriv (fun t : ℝ => ℓ (B (V t))) x) x :=
      (hcd.differentiable (by simp)).differentiableAt.hasDerivAt
    rw [hfun]
    exact hdx
  have hfin : ({t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
      linFun (φ.trans (classEquiv σ)) (classEquiv τ (V t)) = 0}).Finite := by
    have hset : {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧
        linFun (φ.trans (classEquiv σ)) (classEquiv τ (V t)) = 0}
        = {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ ℓ (B (V t)) = 0} := by
      ext t
      simp only [Set.mem_setOf_eq]
      rw [hkey (V t)]
    rw [hset]
    exact hgen.2.1
  have hreg : ∀ t ∈ Icc (0 : ℝ) 1,
      linFun (φ.trans (classEquiv σ)) (classEquiv τ (V t)) = 0 →
      deriv (fun s : ℝ => linFun (φ.trans (classEquiv σ)) (classEquiv τ (V s))) t ≠ 0 := by
    intro t ht hzero
    have hzero' : ℓ (B (V t)) = 0 := by rw [← hkey (V t)]; exact hzero
    rw [show (fun s : ℝ => linFun (φ.trans (classEquiv σ)) (classEquiv τ (V s)))
        = fun s : ℝ => ℓ (B (V s)) from hfun]
    exact hgen.2.2 t ht hzero'
  -- ## the level bounds of the perturbed rotated chart
  have hlevQ' : ∀ z : ℂ, levelOf (Q' z) = levelOf (Q z) := by
    intro z
    simp only [hQ'def, Function.comp_apply]
    exact levelOf_rotCapping u (Q z)
  have hclow' : ∀ z : ℂ, ‖z‖ ≤ 1 → c₂ ≤ levelOf ((chartPert τ ∘ Q') z) := by
    intro z hz
    have hsub : (⟨levelOf (Q' z), levelOf_pos _⟩ : Set.Ioi (0 : ℝ))
        = ⟨levelOf (Q z), levelOf_pos _⟩ := Subtype.ext (hlevQ' z)
    rw [Function.comp_apply, levelOf_chartPert, hsub]
    exact le_trans hc₂le ((levelScale_le_iff τ ⟨c, hc⟩
      ⟨levelOf (Q z), levelOf_pos _⟩).mpr (hclow z hz))
  have hβ' : ∀ z : ℂ, ‖z‖ ≤ 1 →
      levelOf ((chartPert τ ∘ Q') z) ≤ ((levelScale τ ⟨β, hβpos⟩ : Set.Ioi (0 : ℝ)) : ℝ) := by
    intro z hz
    have hsub : (⟨levelOf (Q' z), levelOf_pos _⟩ : Set.Ioi (0 : ℝ))
        = ⟨levelOf (Q z), levelOf_pos _⟩ := Subtype.ext (hlevQ' z)
    rw [Function.comp_apply, levelOf_chartPert, hsub]
    exact (levelScale_le_iff τ ⟨levelOf (Q z), levelOf_pos _⟩ ⟨β, hβpos⟩).mpr (hβ z hz)
  -- ## the instantiation
  exact odd_coreSideCountPt_reference_mixed (Q' := Q') (φ := φ) (τ := τ) (σ := σ)
    (c' := c₂) (β' := ((levelScale τ ⟨β, hβpos⟩ : Set.Ioi (0 : ℝ)) : ℝ)) (lam := lam)
    hc₂ hlampos hclow' hβ' hβσ V hVne hVcls hκ hesse hV0 hder hfin hreg hinj

/-- **The level conditions of `(F1)` hold for all sufficiently small perturbations.**  For a strict gap
`c₂ < c` and a strict gap `β < lam`, the scale conditions

> `c₂ ≤ levelScale τ ⟨c, _⟩`  and  `levelScale τ ⟨β, _⟩ < levelScale σ ⟨lam, _⟩`

hold for all `τ`, `σ` of sufficiently small norm.  (This is the openness of the level bands: the
perturbed chart's band is `levelScale τ [c, β]`, which must stay below the perturbed reference level
`levelScale σ lam`.) -/
theorem exists_levelScale_bounds_ball {c β lam c₂ : ℝ} (hc : 0 < c) (hβpos : 0 < β)
    (hlampos : 0 < lam) (hc₂ : 0 < c₂) (hc₂c : c₂ < c) (hβlam : β < lam) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ σ : Eucl 3, ‖τ‖ < δ → ‖σ‖ < δ →
      c₂ ≤ ((levelScale τ ⟨c, hc⟩ : Set.Ioi (0 : ℝ)) : ℝ) ∧
      ((levelScale τ ⟨β, hβpos⟩ : Set.Ioi (0 : ℝ)) : ℝ)
        < ((levelScale σ ⟨lam, hlampos⟩ : Set.Ioi (0 : ℝ)) : ℝ) := by
  have hlogc₂ : Real.log c₂ < Real.log c := Real.log_lt_log hc₂ hc₂c
  have hlogβ : Real.log β < Real.log lam := Real.log_lt_log hβpos hβlam
  set γ₁ : ℝ := (Real.log c - Real.log c₂) / 2 with hγ₁def
  set γ₂ : ℝ := (Real.log lam - Real.log β) / 2 with hγ₂def
  have hγ₁pos : 0 < γ₁ := by rw [hγ₁def]; linarith
  have hγ₂pos : 0 < γ₂ := by rw [hγ₂def]; linarith
  refine ⟨min γ₁ γ₂, lt_min hγ₁pos hγ₂pos, fun τ σ hτ hσ => ⟨?_, ?_⟩⟩
  · have hτ₁ : ‖τ‖ < γ₁ := lt_of_lt_of_le hτ (min_le_left _ _)
    have hτ0 : -γ₁ < τ 0 := by
      have h := (abs_le.mp (PiLp.norm_apply_le τ 0)).1
      linarith
    rw [levelScale_apply]
    calc c₂ = Real.exp (Real.log c₂) := (Real.exp_log hc₂).symm
      _ ≤ Real.exp (Real.log c - γ₁) := Real.exp_le_exp.mpr (by rw [hγ₁def]; linarith)
      _ ≤ Real.exp (Real.log c + τ 0) := Real.exp_le_exp.mpr (by linarith)
  · have hτ₂ : ‖τ‖ < γ₂ := lt_of_lt_of_le hτ (min_le_right _ _)
    have hσ₂ : ‖σ‖ < γ₂ := lt_of_lt_of_le hσ (min_le_right _ _)
    have hτ0 : τ 0 < γ₂ := lt_of_le_of_lt (abs_le.mp (PiLp.norm_apply_le τ 0)).2 hτ₂
    have hσ0 : -γ₂ < σ 0 := by
      have h := (abs_le.mp (PiLp.norm_apply_le σ 0)).1
      linarith
    rw [levelScale_apply, levelScale_apply, Real.exp_lt_exp]
    have h2 : Real.log β + γ₂ = Real.log lam - γ₂ := by rw [hγ₂def]; ring
    linarith

/-- **The mixed factor `(F1)` for all sufficiently small class perturbations.**  Combining
`Work.Drive.genAlong_classEquiv_transfer` (the genericity survives the class perturbation) with
`Work.Drive.exists_levelScale_bounds_ball` (the level bands stay separated): for a functional `ℓ`
generic along the class lift `V`, there is a radius `δ` such that the pairing of the perturbed rotated
configuration chart with the perturbed reference plane is odd for **every** pair of perturbation
parameters `τ`, `σ` of norm below `δ`.

This is the form consumed by the `hn2` assembly: the reference-triple genericity lemma produces
parameters of arbitrarily small norm, and this lemma turns the corresponding mixed factor into `1`
without any further condition. -/
theorem exists_delta_odd_coreSideCountPt_rotCapping {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (ℓ : Eucl 3 →L[ℝ] ℝ) (φ : Eucl 3 ≃L[ℝ] Eucl 3) (hφ : ∀ v : Eucl 3, linFun φ v = ℓ v)
    (u : UnitAddCircle)
    {c β lam c₂ : ℝ} (hc : 0 < c) (hβpos : 0 < β) (hlampos : 0 < lam) (hc₂ : 0 < c₂)
    (hc₂c : c₂ < c) (hβlam : β < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (V : ℝ → Eucl 3) (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hVne : ∀ t : ℝ, V t ≠ 0)
    (hVcls : ∀ t ∈ Icc (0 : ℝ) 1, Projectivization.mk ℝ (V t) (hVne t)
      = (cappingSpaceHomeoProj (coreLoop (fun z => rotCapping u (Q z)) t)).2)
    {κ : ℝ} (hκ : κ < 0) (hesse : V 1 = κ • V 0)
    (hℓgen : GenAlong ℓ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ σ : Eucl 3, ‖τ‖ < δ → ‖σ‖ < δ →
      Odd (coreSideCountPt (chartPert τ ∘ fun z => rotCapping u (Q z)) c₂
        (diskPlane (chartPert σ ∘ linPlaneChart φ lam hlampos))) := by
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := genAlong_classEquiv_transfer hVs hℓgen
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := exists_levelScale_bounds_ball hc hβpos hlampos hc₂ hc₂c hβlam
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun τ σ hτ hσ => ?_⟩
  have hτ₁ : ‖τ‖ < δ₁ := lt_of_lt_of_le hτ (min_le_left _ _)
  have hσ₁ : ‖σ‖ < δ₁ := lt_of_lt_of_le hσ (min_le_left _ _)
  have hlev := hδ₂ τ σ (lt_of_lt_of_le hτ (min_le_right _ _))
    (lt_of_lt_of_le hσ (min_le_right _ _))
  refine odd_coreSideCountPt_rotCapping_of_genAlong hγ hQ φ u hc hc₂ hβpos hlampos
    hclow hβ hlev.1 hlev.2 V hVs hVne hVcls hκ hesse ?_
  refine (GenAlong_congr (V := V) (ℓ := ℓ ∘L (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
      ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3)))
    (ℓ' := (linFunCLM φ) ∘L (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)) ∘L
      ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3))) ?_).mp (hδ₁ τ σ hτ₁ hσ₁)
  intro v
  simp only [ContinuousLinearMap.comp_apply, linFunCLM_apply]
  exact (hφ (((classEquiv σ).symm : Eucl 3 →L[ℝ] Eucl 3)
    ((classEquiv τ : Eucl 3 →L[ℝ] Eucl 3) v))).symm

end

end Work.Drive


