import Mathlib
import Submission.Work.Drive.chartPertTransfer
import Submission.Work.Drive.refPlaneLevel
import Submission.Work.Drive.chartPert_linPlaneChart
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping
import Submission.Work.Drive.linCapping

/-!
# The two inputs of the *mixed* factors of the reference triple

The mixed factors of the reference triple `(P_u, P_v, R)` of `hn2` are the pairings

> `ε(R; chart P_k) = coreSideCount (Ξ τ k ∘ Q_k) (cblk 2) (diskPlane (Ξ τ₂ ∘ Q_R))`

(see `HN2_MIXED_FACTOR_STATUS.md` §2).  They split into

* **`(F1)`: the `(1,3)`-pairing is odd** — an application of `Work.Drive.odd_coreSideCountPt_reference`
  at the *perturbed* chart `chartPert τ ∘ Q_k` with the transported functional
  `φ'' = φ.trans (classEquiv τ₂)` and the scaled level `levelScale τ₂ ⟨lam, _⟩`.  The data it consumes are
  the lift of the perturbed chart's class loop and the level band of the perturbed chart, both supplied
  here (`class_eq_coreLoop_chartPert`, `isChartData_chartPert`);
* **`(F2)`: the reference block's own factors vanish by levels** — the perturbed reference chart's loop
  lies at the single level `levelScale σ lam`, strictly above the levels of the perturbed configuration
  planes, so the pairing is `0`.  This file proves that vanishing for the *perturbed* data
  (`not_odd_coreSideCount_reference_perturbed`), from the unperturbed level bounds
  (`Work.Drive.le_levelOf_rotPresentation`, `Work.Drive.levelOf_rotPresentation_le`) transported along
  `Work.Drive.levelOf_chartPert`.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Set

noncomputable section

/-! ## 1. The class loop and the level band of a perturbed chart -/

/-- **The class loop of a perturbed chart.**  If `V` lifts the class of the core loop of `Q` on `[0,1]`,
then `classEquiv τ ∘ V` lifts the class of the core loop of `chartPert τ ∘ Q`. -/
theorem class_eq_coreLoop_chartPert {Q : ℂ → CappingSpace} {V : ℝ → Eucl 3}
    (hVne : ∀ t : ℝ, V t ≠ 0)
    (hVcls : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Projectivization.mk ℝ (V t) (hVne t)
        = (cappingSpaceHomeoProj (coreLoop Q t)).2)
    (τ : Eucl 3) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Projectivization.mk ℝ (classEquiv τ (V t)) (classEquiv_ne_zero (hVne t))
        = (cappingSpaceHomeoProj (coreLoop (chartPert τ ∘ Q) t)).2 := by
  intro t ht
  rw [class_coreLoop_chartPert τ Q t, ← hVcls t ht, classMap_mk]

/-- **The loop of a perturbed chart lies at the scaled level.** -/
theorem levelOf_coreLoop_chartPert (Q : ℂ → CappingSpace) (τ : Eucl 3) {lam : ℝ} (hlam : 0 < lam)
    (hQ : ∀ t : ℝ, levelOf (coreLoop Q t) = lam) (t : ℝ) :
    levelOf (coreLoop (chartPert τ ∘ Q) t)
      = ((levelScale τ ⟨lam, hlam⟩ : Set.Ioi (0 : ℝ)) : ℝ) := by
  have h : coreLoop (chartPert τ ∘ Q) t = chartPert τ (coreLoop Q t) := rfl
  rw [h, levelOf_chartPert]
  have hsub : (⟨levelOf (coreLoop Q t), levelOf_pos _⟩ : Set.Ioi (0 : ℝ)) = ⟨lam, hlam⟩ :=
    Subtype.ext (hQ t)
  rw [hsub]

/-- **The levels of a perturbed rotated presentation.** -/
theorem levelOf_chartPert_rotPresentation (Q : ℂ → CappingSpace) (u : UnitAddCircle) (τ : Eucl 3)
    (y : EuclideanSpace ℝ (Fin 2)) :
    levelOf ((chartPert τ ∘ rotPresentation Q u) y)
      = ((levelScale τ ⟨levelOf (rotPresentation Q u y), levelOf_pos _⟩ : Set.Ioi (0 : ℝ)) : ℝ) :=
  levelOf_chartPert τ _

/-! ## 2. `(F2)`: the reference block's own factors vanish for the *perturbed* triple -/

/-- **The reference block's factors vanish, for the perturbed reference triple.**  Let `Q` be a
configuration chart with level band `[c, β]` (`β < lam`, `0 < c`), `φ` a linear equivalence, `τ` the
perturbation of a *configuration* block and `σ` the perturbation of the *reference* block.  Then the
pairing of the loop of the perturbed reference plane `chartPert σ ∘ linPlaneChart φ lam hlampos`
(which lies at the single level `levelScale σ lam`) with the sweep of the perturbed configuration plane
`chartPert τ ∘ rotPresentation Q u` (whose levels are `levelScale τ [c, β]`) is *even*, as soon as the
truncation level `c₂` is below the configuration levels (`c₂ ≤ levelScale τ c`) and the configuration
levels stay strictly below the reference level (`levelScale τ β < levelScale σ lam`). -/
theorem not_odd_coreSideCount_reference_perturbed (Q : ℂ → CappingSpace) (u : UnitAddCircle)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) {β c lam c₂ : ℝ} (hc : 0 < c) (hlampos : 0 < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β)
    (τ σ : Eucl 3) (hc₂ : 0 < c₂) (hβpos : 0 < β)
    (hc₂le : c₂ ≤ ((levelScale τ ⟨c, hc⟩ : Set.Ioi (0 : ℝ)) : ℝ))
    (hβσ : ((levelScale τ ⟨β, hβpos⟩ : Set.Ioi (0 : ℝ)) : ℝ)
      < ((levelScale σ ⟨lam, hlampos⟩ : Set.Ioi (0 : ℝ)) : ℝ)) :
    ¬ Odd (coreSideCount (chartPert σ ∘ linPlaneChart φ lam hlampos) c₂
        (chartPert τ ∘ rotPresentation Q u)) := by
  refine not_odd_coreSideCount_of_level_lt (chartPert σ ∘ linPlaneChart φ lam hlampos) hc₂
    (chartPert τ ∘ rotPresentation Q u) ?_ ?_
  · intro y
    rw [Function.comp_apply, levelOf_chartPert]
    exact le_trans hc₂le ((levelScale_le_iff τ ⟨c, hc⟩
      ⟨levelOf (rotPresentation Q u y), levelOf_pos _⟩).mpr
        (le_levelOf_rotPresentation Q hclow u y))
  · intro t _ y
    rw [Function.comp_apply, levelOf_chartPert,
      levelOf_coreLoop_chartPert (linPlaneChart φ lam hlampos) σ hlampos
        (fun t => levelOf_coreLoop_linPlaneChart φ hlampos t) t]
    exact lt_of_le_of_lt ((levelScale_le_iff τ
      ⟨levelOf (rotPresentation Q u y), levelOf_pos _⟩ ⟨β, hβpos⟩).mpr
        (levelOf_rotPresentation_le Q hβ u y)) hβσ


/-! ## 3. `(F1)` for the *mixed* factors (two different perturbation parameters)

The mixed factor of block `k` of the reference triple is
`coreSideCountPt (Ξ τ k ∘ Q') c' (diskPlane (Ξ σ ∘ linPlaneChart φ lam hlampos))` with the
configuration chart `Q'` rotated, the chart slot perturbed by `τ` and the *plane* slot by `σ`.  This is
an application of the proved `Work.Drive.odd_coreSideCountPt_reference` at the **perturbed chart**
`chartPert τ ∘ Q'` with the **transported functional** `φ.trans (classEquiv σ)` and the scaled level
`levelScale σ ⟨lam, _⟩`; the only bookkeeping is the transport of the plane presentation along
`chartPert_linPlaneChart` (item (i)) and of the lift along `class_eq_coreLoop_chartPert`.  No
perturbation-independence is involved (`HN2_MIXED_FACTOR_STATUS.md` §2). -/

/-- **`(F1)` for the mixed factors of the reference triple.**  The hypotheses are those of
`Work.Drive.odd_coreSideCountPt_reference` at the *perturbed* chart, read through the perturbation: a
lift `V` of the class loop of the (rotated) configuration chart `Q'`, its essentiality, the level band
of the perturbed chart, and the regularity of the transported functional
`linFun (φ.trans (classEquiv σ))` along the transported lift `classEquiv τ ∘ V`. -/
theorem odd_coreSideCountPt_reference_mixed (Q' : ℂ → CappingSpace)
    (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ σ : Eucl 3) {c' β' lam : ℝ} (hc' : 0 < c') (hlampos : 0 < lam)
    (hclow' : ∀ z : ℂ, ‖z‖ ≤ 1 → c' ≤ levelOf ((chartPert τ ∘ Q') z))
    (hβ' : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf ((chartPert τ ∘ Q') z) ≤ β')
    (hβ'lam : β' < ((levelScale σ ⟨lam, hlampos⟩ : Set.Ioi (0 : ℝ)) : ℝ))
    (V : ℝ → Eucl 3) (hVne : ∀ t : ℝ, V t ≠ 0)
    (hVcls : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Projectivization.mk ℝ (V t) (hVne t)
        = (cappingSpaceHomeoProj (coreLoop Q' t)).2)
    {κ : ℝ} (hκ : κ < 0) (hesse : V 1 = κ • V 0)
    (hV0 : Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
      (Work.Drive.classEquiv τ (V 0)) ≠ 0)
    (hder : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t)))
        (deriv (fun t : ℝ => Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
          (Work.Drive.classEquiv τ (V t))) x) x)
    (hfin : ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
      Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t)) = 0}).Finite)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t)) = 0 →
      deriv (fun t : ℝ => Work.Drive.linFun (φ.trans (Work.Drive.classEquiv σ))
        (Work.Drive.classEquiv τ (V t))) t ≠ 0)
    (hinj : Set.InjOn (Work.Drive.coreLoop (chartPert τ ∘ Q'))
      {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧
        (Work.Drive.cappingSpaceHomeoProj
          (Work.Drive.coreLoop (chartPert τ ∘ Q') t)).2
          ∈ Work.Drive.projLine (Work.Drive.linSub (φ.trans (Work.Drive.classEquiv σ)))}) :
    Odd (Work.Drive.coreSideCountPt (chartPert τ ∘ Q') c'
      (Work.Drive.diskPlane (chartPert σ ∘ Work.Drive.linPlaneChart φ lam hlampos))) := by
  have hmain := Work.Drive.odd_coreSideCountPt_reference (Q := chartPert τ ∘ Q')
    (φ := φ.trans (Work.Drive.classEquiv σ)) (hc := hc') (hβlam := hβ'lam)
    (hlampos := (Work.Drive.levelScale σ ⟨lam, hlampos⟩).2) (hclow := hclow') (hβ := hβ')
    (V := fun t => Work.Drive.classEquiv τ (V t))
    (hVne := fun t => Work.Drive.classEquiv_ne_zero (hVne t))
    (hVcls := class_eq_coreLoop_chartPert hVne hVcls τ)
    (hκ := hκ) (hesse := by
      show Work.Drive.classEquiv τ (V 1) = κ • Work.Drive.classEquiv τ (V 0)
      rw [hesse, map_smul])
    (hV0 := hV0) (hder := hder) (hfin := hfin) (hreg := hreg) (hinj := hinj)
  rw [Work.Drive.chartPert_linPlaneChart φ lam hlampos σ]
  exact hmain


/-! ## 4. The lift of the class loop of a *rotated* chart

The configuration chart `Q' = rotCapping u ∘ Q` of the reference triple has its class loop related to
that of `Q` by the projective rotation `projRot`: the *linear* lift of that rotation is
`Work.Drive.diagRotL t` (`Work.Drive.projMap_diagRotL`).  This is the form in which the `hn2` assembly
produces the lift `V` that `Work.Drive.odd_coreSideCountPt_reference_mixed` consumes. -/

/-- `diagRotL t` does not vanish on nonzero vectors. -/
lemma diagRotL_ne_zero' (t : ℝ) {v : Eucl 3} (hv : v ≠ 0) : diagRotL t v ≠ 0 :=
  fun h => hv ((diagRotL t).injective (by rw [h, map_zero]))

/-- **The class loop of a rotated chart, in terms of the lift of the chart.**  For every angle
`u : UnitAddCircle` (written `u = t₀` in the circle) and every nonvanishing lift `Vc` of the class map
of `Q` on the unit circle, the map `t ↦ diagRotL t₀ (Vc (coreLoopArg t))` is a lift of the class loop of
`rotCapping u ∘ Q`. -/
theorem class_eq_coreLoop_rotCapping_comp (Q : ℂ → CappingSpace) (u : UnitAddCircle)
    (Vc : ℂ → Eucl 3) (hVcne : ∀ z : ℂ, ‖z‖ = 1 → Vc z ≠ 0)
    (hVccls : ∀ z : ℂ, ∀ hz : ‖z‖ = 1,
      Projectivization.mk ℝ (Vc z) (hVcne z hz) = (cappingSpaceHomeoProj (Q z)).2) :
    ∃ t₀ : ℝ, ((t₀ : ℝ) : UnitAddCircle) = u ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Projectivization.mk ℝ (diagRotL t₀ (Vc (coreLoopArg t)))
            (diagRotL_ne_zero' t₀ (hVcne _ (coreLoopArg_norm t)))
          = (cappingSpaceHomeoProj (coreLoop (fun z => rotCapping u (Q z)) t)).2 := by
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, ((t₀ : ℝ) : UnitAddCircle) = u := ⟨Quotient.out u, Quotient.out_eq u⟩
  refine ⟨t₀, ht₀, fun t _ => ?_⟩
  have hloop : coreLoop (fun z => rotCapping u (Q z)) t = rotCapping u (coreLoop Q t) := rfl
  rw [hloop, ← ht₀]
  have hpair := cappingSpaceHomeoProj_rotCapping t₀ (coreLoop Q t)
  rw [congrArg Prod.snd hpair, coreLoop_eq]
  rw [← hVccls _ (coreLoopArg_norm t), ← projMap_diagRotL t₀]
  rw [Projectivization.map_mk]
  rfl

end

end Work.Drive
