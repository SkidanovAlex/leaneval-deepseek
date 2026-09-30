import Mathlib
import Submission.Work.CurvModels.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `SecNonposAt` depends only on the germ of the metric field

`Work.Curvature.SecNonposAt G q` is the pointwise non-positivity of the sectional curvature
numerator `G q (modelCurv G q u v v) u ≤ 0`, where `modelCurv` is built from the Christoffel
symbol `koszulChr G` and its derivatives.  Although this is not visible from the definition, every
ingredient is *local* at `q`:

* `dG G q v a c` and `dBmodel G q d a b` are derivatives at `q` of functions of `·` alone;
* `koszulChr G q a b` is determined by the Koszul formula, i.e. by the values of `G` *near* `q`
  (through `dG`) together with the values of `G` *at* `q` (through `IsMetricAt G q`, which
  supplies the positivity/linearity needed by `koszulChr_eq_of_forall`);
* the remaining evaluation `G q (…) u` only involves the value of `G` at `q`.

Consequently, if `G` is a metric near `q` in the sense of `IsMetricNear`, and `G'` agrees with `G`
on a neighbourhood of `q` (`AgreesNear`), then `SecNonposAt` holds for `G'` as soon as it holds
for `G`.  This is the chapter's locality theorem.
-/

noncomputable section

open Filter Topology
open Work.Curvature

namespace Work.CurvModels

/-! ## Congruence of the building blocks -/

/-- **`dG` only depends on the germ**: eventual equality of `G` and `G'` at `q` gives equality of
the derivatives of the metric components. -/
theorem dG_congr {G G' : MetricField} {q : E4} (h : G =ᶠ[𝓝 q] G') (v a c : E4) :
    dG G q v a c = dG G' q v a c := by
  have hev : (fun r : E4 => G r a c) =ᶠ[𝓝 q] (fun r : E4 => G' r a c) :=
    h.mono (fun r hr => congrFun (congrFun hr a) c)
  rw [dG, dG, hev.fderiv_eq]

/-- **The Koszul right hand side only depends on the germ.** -/
theorem koszulRHS_congr {G G' : MetricField} {q : E4} (h : G =ᶠ[𝓝 q] G') (a b c : E4) :
    koszulRHS G q a b c = koszulRHS G' q a b c := by
  unfold koszulRHS
  rw [dG_congr h b a c, dG_congr h a b c, dG_congr h c a b]

/-- **The Christoffel symbol only depends on the germ.**  If `G'` is a metric at `q` (so that the
Koszul solution is unique there), `G` and `G'` agree *at* `q`, and their Koszul right hand sides
agree at `q`, then `koszulChr G q a b = koszulChr G' q a b`.  (Nothing is assumed about `G` besides
the agreement: if the Koszul solution does not exist for `G`, the definition falls back to `0` for
both fields simultaneously, because existence is transported by the agreement.) -/
theorem koszulChr_congr {G G' : MetricField} {q a b : E4}
    (hG' : IsMetricAt G' q)
    (hval : ∀ z c : E4, G q z c = G' q z c)
    (hrhs : ∀ c : E4, koszulRHS G q a b c = koszulRHS G' q a b c) :
    koszulChr G q a b = koszulChr G' q a b := by
  by_cases hP : ∃ z : E4, ∀ c, G q z c = koszulRHS G q a b c
  · have hspec := koszulChr_spec hP
    have hz : ∀ c : E4, G' q (koszulChr G q a b) c = koszulRHS G' q a b c := by
      intro c
      rw [← hval (koszulChr G q a b) c, hspec c, hrhs c]
    exact (koszulChr_eq_of_forall hG'.sub_fst (fun x hx => hG'.pos hx) hz).symm
  · have hP' : ¬ ∃ z : E4, ∀ c, G' q z c = koszulRHS G' q a b c := by
      rintro ⟨z, hz⟩
      exact hP ⟨z, fun c => by rw [hval z c, hrhs c, hz c]⟩
    rw [koszulChr, koszulChr, dite_eq_right hP, dite_eq_right hP']

/-! ## Congruence on an open set -/

/-- The Christoffel symbol is invariant under replacing `G` by an agreeing field `G'` on an open
set, provided `G'` is a metric there. -/
theorem koszulChr_congr_of_mem {G G' : MetricField} {V : Set E4} (hVo : IsOpen V)
    (hag : ∀ r ∈ V, ∀ a b : E4, G r a b = G' r a b)
    (hG' : ∀ r ∈ V, IsMetricAt G' r) {q : E4} (hq : q ∈ V) (a b : E4) :
    koszulChr G q a b = koszulChr G' q a b := by
  have hev : G =ᶠ[𝓝 q] G' := by
    filter_upwards [hVo.mem_nhds hq] with r hr
    exact funext fun x => funext fun y => hag r hr x y
  exact koszulChr_congr (hG' q hq) (fun z c => hag q hq z c) (fun c => koszulRHS_congr hev a b c)

/-- The derivative of the Christoffel symbol is invariant under replacing `G` by an agreeing field
`G'` on an open set. -/
theorem dBmodel_congr_of_mem {G G' : MetricField} {V : Set E4} (hVo : IsOpen V)
    (hag : ∀ r ∈ V, ∀ a b : E4, G r a b = G' r a b)
    (hG' : ∀ r ∈ V, IsMetricAt G' r) {q : E4} (hq : q ∈ V) (d a b : E4) :
    dBmodel G q d a b = dBmodel G' q d a b := by
  have hev : (fun r : E4 => koszulChr G r a b) =ᶠ[𝓝 q] (fun r : E4 => koszulChr G' r a b) := by
    filter_upwards [hVo.mem_nhds hq] with r hr
    exact koszulChr_congr_of_mem hVo hag hG' hr a b
  unfold dBmodel
  rw [hev.fderiv_eq]

/-- **The model curvature is invariant under replacing `G` by an agreeing field `G'` on an open
set**, provided `G'` is a metric there. -/
theorem modelCurv_congr_of_mem {G G' : MetricField} {V : Set E4} (hVo : IsOpen V)
    (hag : ∀ r ∈ V, ∀ a b : E4, G r a b = G' r a b)
    (hG' : ∀ r ∈ V, IsMetricAt G' r) {q : E4} (hq : q ∈ V) (u v w : E4) :
    modelCurv G q u v w = modelCurv G' q u v w := by
  have h1 := dBmodel_congr_of_mem hVo hag hG' hq u w v
  have h2 := dBmodel_congr_of_mem hVo hag hG' hq v w u
  have h3 := koszulChr_congr_of_mem hVo hag hG' hq (koszulChr G q w v) u
  have h4 := koszulChr_congr_of_mem hVo hag hG' hq w v
  have h5 := koszulChr_congr_of_mem hVo hag hG' hq (koszulChr G q w u) v
  have h6 := koszulChr_congr_of_mem hVo hag hG' hq w u
  rw [modelCurv, modelCurv, h1, h2, h3, h4, h5, h6]

/-! ## The locality theorem -/

theorem SecNonposAt_congr {G G' : Work.Curvature.MetricField} {q : Work.Curvature.E4}
    (hG : Work.CurvModels.IsMetricNear G q) (h : Work.CurvModels.AgreesNear G G' q)
    (hsec : Work.Curvature.SecNonposAt G q) : Work.Curvature.SecNonposAt G' q := by
  intro u v
  obtain ⟨U, hUo, hqU, hUag⟩ := h.exists_open
  have hT : ∀ᶠ q' in 𝓝 q, IsMetricAt G q' := hG
  have hqW : q ∈ interior {q' : E4 | IsMetricAt G q'} :=
    mem_interior_iff_mem_nhds.mpr hT
  have hVo : IsOpen (U ∩ interior {q' : E4 | IsMetricAt G q'}) := hUo.inter isOpen_interior
  have hqV : q ∈ U ∩ interior {q' : E4 | IsMetricAt G q'} := ⟨hqU, hqW⟩
  have hag : ∀ r ∈ U ∩ interior {q' : E4 | IsMetricAt G q'},
      ∀ a b : E4, G r a b = G' r a b := fun r hr => hUag r hr.1
  have hG' : ∀ r ∈ U ∩ interior {q' : E4 | IsMetricAt G q'}, IsMetricAt G' r := by
    intro r hr
    have hrT : IsMetricAt G r :=
      interior_subset (s := {q' : E4 | IsMetricAt G q'}) hr.2
    exact hrT.congr_apply (hag r hr)
  have hmc := modelCurv_congr_of_mem hVo hag hG' hqV u v v
  calc G' q (modelCurv G' q u v v) u
      = G' q (modelCurv G q u v v) u := by rw [hmc]
    _ = G q (modelCurv G q u v v) u := (hUag q hqU (modelCurv G q u v v) u).symm
    _ ≤ 0 := hsec u v

end Work.CurvModels
