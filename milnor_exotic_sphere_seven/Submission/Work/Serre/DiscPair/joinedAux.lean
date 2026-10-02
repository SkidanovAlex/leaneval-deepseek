import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.CylMapGen
import Submission.Work.StemsB.Fibrations
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Transport of the fibrewise restriction of the relative class along a path

This file isolates the *formal* part of the transport of the fibre restriction of the relative
class along a path in the base, in the shape used by
`Work.Serre.DiscPair.fibreRestriction_injective_of_joined`.

Setting: `q : C(X, B)` is a Serre fibration, `M := cyl q`, `A := range (cylIncl q)`,
`F_b := (cylRetract q) ⁻¹' {b}` (the fibre of the retraction, a cone on the fibre `q⁻¹{b}`),
`A_b := F_b ∩ A`, and

  `cylFibreRes q b k : H^k(M, A; ℚ) → H^k(F_b, A_b; ℚ)`

is the restriction map.

The two inputs of the transport (both `Prop`s, so that this file stays `sorry`-free) are

* `CylIntervalFibreRestriction` — for a Serre fibration over the *unit interval* the restriction is
  injective (no fibre hypotheses are needed: `cyl p` is homotopy equivalent to the contractible
  interval, and `H_*(P, p⁻¹{t}) = 0` over a contractible base, so the map is really
  `H^r(P) → H^r(p⁻¹{t})`, an isomorphism);
* `CylMapFibreInjectivity` — the fibre comparison map `pathPsiFibre` induced by the pullback square
  along a path is injective on relative cohomology (its two sources are the cone pairs of the same
  fibre).

The main theorem `fibreRestriction_vanishing_iff_of_joined` then says that for a relative class `U`
and the two ends of a path `γ`, the restrictions of `U` to the fibres over `γ 0` and `γ 1` vanish
simultaneously; consequently `cylFibreRes q b` is injective at one point of a path-connected base if
and only if it is injective at any other.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

variable {X B : Type} [TopologicalSpace X] [TopologicalSpace B]

/-- The fibre of the retraction of the mapping cylinder of `f` over the point `t` of the target. -/
def cylFibre (f : C(X, B)) (t : B) : Set (Work.Serre.cyl f) :=
  (Work.Serre.cylRetract f) ⁻¹' {t}

/-- The part of the bottom copy of the mapping cylinder lying over `t`. -/
def cylFibreBot (f : C(X, B)) (t : B) : Set ↥(cylFibre f t) :=
  {x | (x : Work.Serre.cyl f) ∈ Set.range (Work.Serre.cylIncl f)}

/-- The inclusion of the fibre pair into the mapping-cylinder pair. -/
def cylFibreIncl (f : C(X, B)) (t : B) : C(↥(cylFibre f t), Work.Serre.cyl f) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- **The restriction of relative cohomology to the fibre over `t`.** -/
def cylFibreRes (f : C(X, B)) (t : B) (k : ℕ) :
    Work.Thom.RelCoh ℚ k (Work.Serre.cyl f) (Set.range (Work.Serre.cylIncl f)) →ₗ[ℚ]
      Work.Thom.RelCoh ℚ k ↥(cylFibre f t) (cylFibreBot f t) :=
  (Work.Thom.relCohMap (cylFibreIncl f t) (cylFibreBot f t) (Set.range (Work.Serre.cylIncl f))
    (fun _ hx => hx) ℚ k).hom

/-! ## The pullback square of a path -/

variable (q : C(X, B)) (γ : C(unitInterval, B))

/-- **The map `cyl (pullbackSnd q γ) → cyl q` induced by the pullback square of a path.** -/
def pathPsi : C(Work.Serre.cyl (Work.StemsB.pullbackSnd q γ), Work.Serre.cyl q) :=
  Work.StemsB.cylMapGen (Work.StemsB.pullbackSnd q γ) q (Work.StemsB.pullbackFst q γ) γ
    (fun z => z.2.symm)

/-- **The restriction of `pathPsi` to the fibre over `t`**, as a map of fibre pairs. -/
def pathPsiFibre (t : unitInterval) :
    C(↥(cylFibre (Work.StemsB.pullbackSnd q γ) t), ↥(cylFibre q (γ t))) where
  toFun z := ⟨pathPsi q γ z.1, Work.StemsB.cylMapGen_mapsTo_fibre
    (Work.StemsB.pullbackSnd q γ) q (Work.StemsB.pullbackFst q γ) γ (fun z => z.2.symm) z.2⟩
  continuous_toFun := Continuous.subtype_mk
    ((pathPsi q γ).continuous.comp continuous_subtype_val) _

/-- `pathPsiFibre` carries the bottom copy over `t` into the bottom copy over `γ t`. -/
theorem pathPsiFibre_mapsTo_bot (t : unitInterval) :
    Set.MapsTo (pathPsiFibre q γ t) (cylFibreBot (Work.StemsB.pullbackSnd q γ) t)
      (cylFibreBot q (γ t)) :=
  fun _ hz => Work.StemsB.cylMapGen_mapsTo_range (Work.StemsB.pullbackSnd q γ) q
    (Work.StemsB.pullbackFst q γ) γ (fun z => z.2.symm) hz

/-- `pathPsi` carries the bottom copy into the bottom copy. -/
theorem pathPsi_mapsTo_range :
    Set.MapsTo (pathPsi q γ) (Set.range (Work.Serre.cylIncl (Work.StemsB.pullbackSnd q γ)))
      (Set.range (Work.Serre.cylIncl q)) :=
  fun _ hz => Work.StemsB.cylMapGen_mapsTo_range (Work.StemsB.pullbackSnd q γ) q
    (Work.StemsB.pullbackFst q γ) γ (fun z => z.2.symm) hz

/-- **Naturality of the restriction maps along the pullback square**: the fibre inclusion followed
by `pathPsi` is `pathPsiFibre` followed by the fibre inclusion. -/
theorem cylFibreIncl_comp_pathPsiFibre (t : unitInterval) :
    (cylFibreIncl q (γ t)).comp (pathPsiFibre q γ t) =
      (pathPsi q γ).comp (cylFibreIncl (Work.StemsB.pullbackSnd q γ) t) := by
  ext z
  rfl

/-! ## The two inputs -/

/-- **The interval case.**  For a Serre fibration `p : C(P, I)` over the unit interval and any
`t : I`, the restriction `H^{r+1}(cyl p, range (cylIncl p); ℚ) → H^{r+1}(cyl p|_t, A_t; ℚ)` is
injective (`r ≥ 1`).  No fibre hypothesis is needed. -/
def IntervalFibreRestriction : Prop :=
  ∀ {P : Type} [TopologicalSpace P] (p : C(P, unitInterval)),
    Work.StemsB.IsSerreFibration p → ∀ (r : ℕ), 1 ≤ r →
      ∀ t : unitInterval, Function.Injective (cylFibreRes p t (r + 1))

/-- **The fibre-pair comparison along a path.**  The map of mapping cylinders induced by the
pullback square of a path restricts, over any `t`, to a map of pairs which is injective on relative
cohomology. -/
def CylMapFibreInjectivity : Prop :=
  ∀ {B X : Type} [TopologicalSpace B] [TopologicalSpace X] (q : C(X, B))
    (γ : C(unitInterval, B)) (r : ℕ),
    ∀ t : unitInterval, Function.Injective
      (Work.Thom.relCohMap (pathPsiFibre q γ t) (cylFibreBot (Work.StemsB.pullbackSnd q γ) t)
        (cylFibreBot q (γ t)) (pathPsiFibre_mapsTo_bot q γ t) ℚ (r + 1)).hom

/-! ## The transport -/

/-- **Transport of the vanishing of the fibre restriction along a path.**  For a Serre fibration
`q`, a relative class `U ∈ H^{r+1}(cyl q, A; ℚ)` and a path `γ`, the restrictions of `U` to the
fibres over `γ 0` and over `γ 1` vanish simultaneously. -/
theorem fibreRestriction_vanishing_iff_of_joined
    (hint : IntervalFibreRestriction) (hinj : CylMapFibreInjectivity)
    (q : C(X, B)) (hq : Work.StemsB.IsSerreFibration q) (r : ℕ) (hr : 1 ≤ r)
    (γ : C(unitInterval, B))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q))) :
    cylFibreRes q (γ 0) (r + 1) U = 0 ↔ cylFibreRes q (γ 1) (r + 1) U = 0 := by
  classical
  have hpS : Work.StemsB.IsSerreFibration (Work.StemsB.pullbackSnd q γ) :=
    fun k => Work.StemsB.hasHLP_pullback q γ (hq k)
  set W : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl (Work.StemsB.pullbackSnd q γ))
      (Set.range (Work.Serre.cylIncl (Work.StemsB.pullbackSnd q γ))) :=
    (Work.Thom.relCohMap (pathPsi q γ)
      (Set.range (Work.Serre.cylIncl (Work.StemsB.pullbackSnd q γ)))
      (Set.range (Work.Serre.cylIncl q)) (pathPsi_mapsTo_range q γ) ℚ (r + 1)).hom U with hW
  have hfac : ∀ t : unitInterval,
      cylFibreRes (Work.StemsB.pullbackSnd q γ) t (r + 1) W =
        (Work.Thom.relCohMap (pathPsiFibre q γ t)
          (cylFibreBot (Work.StemsB.pullbackSnd q γ) t)
          (cylFibreBot q (γ t)) (pathPsiFibre_mapsTo_bot q γ t) ℚ (r + 1)).hom
          (cylFibreRes q (γ t) (r + 1) U) := by
    intro t
    have hcomp : ((pathPsi q γ).comp (cylFibreIncl (Work.StemsB.pullbackSnd q γ) t))
        = ((cylFibreIncl q (γ t)).comp (pathPsiFibre q γ t)) :=
      cylFibreIncl_comp_pathPsiFibre q γ t
    have h1 := Work.Thom.relCohMap_compA_apply
      (cylFibreBot (Work.StemsB.pullbackSnd q γ) t)
      (Set.range (Work.Serre.cylIncl (Work.StemsB.pullbackSnd q γ)))
      (Set.range (Work.Serre.cylIncl q))
      (cylFibreIncl (Work.StemsB.pullbackSnd q γ) t) (pathPsi q γ)
      (fun _ hx => hx) (pathPsi_mapsTo_range q γ) (fun _ hx => pathPsi_mapsTo_range q γ hx)
      ℚ (r + 1) U
    have h2 := Work.Thom.relCohMap_compA_apply
      (cylFibreBot (Work.StemsB.pullbackSnd q γ) t) (cylFibreBot q (γ t))
      (Set.range (Work.Serre.cylIncl q))
      (pathPsiFibre q γ t) (cylFibreIncl q (γ t)) (pathPsiFibre_mapsTo_bot q γ t)
      (fun _ hx => hx) (fun _ hx => pathPsiFibre_mapsTo_bot q γ t hx) ℚ (r + 1) U
    have h3 : (Work.Thom.relCohMap
          ((pathPsi q γ).comp (cylFibreIncl (Work.StemsB.pullbackSnd q γ) t))
          (cylFibreBot (Work.StemsB.pullbackSnd q γ) t)
          (Set.range (Work.Serre.cylIncl q)) (fun _ hx => pathPsi_mapsTo_range q γ hx)
          ℚ (r + 1)).hom U
        = (Work.Thom.relCohMap
          ((cylFibreIncl q (γ t)).comp (pathPsiFibre q γ t))
          (cylFibreBot (Work.StemsB.pullbackSnd q γ) t)
          (Set.range (Work.Serre.cylIncl q))
          (fun _ hx => pathPsiFibre_mapsTo_bot q γ t hx) ℚ (r + 1)).hom U := by
      rw [Work.Thom.relCohMap_congrA (cylFibreBot (Work.StemsB.pullbackSnd q γ) t)
        (Set.range (Work.Serre.cylIncl q)) hcomp
        (fun _ hx => pathPsi_mapsTo_range q γ hx)
        (fun _ hx => pathPsiFibre_mapsTo_bot q γ t hx) ℚ (r + 1)]
    rw [h3] at h1
    rw [← h2] at h1
    simpa only [cylFibreRes, hW] using h1
  have h0 := hint (Work.StemsB.pullbackSnd q γ) hpS r hr (0 : unitInterval)
  have h1' := hint (Work.StemsB.pullbackSnd q γ) hpS r hr (1 : unitInterval)
  have hzinj0 := hinj (q := q) (γ := γ) (r := r) (0 : unitInterval)
  have hzinj1 := hinj (q := q) (γ := γ) (r := r) (1 : unitInterval)
  constructor
  · intro h
    have hW0 : W = 0 := h0 (by rw [hfac 0, h, map_zero, map_zero])
    have hz1 : (Work.Thom.relCohMap (pathPsiFibre q γ (1 : unitInterval))
        (cylFibreBot (Work.StemsB.pullbackSnd q γ) 1)
        (cylFibreBot q (γ 1)) (pathPsiFibre_mapsTo_bot q γ 1) ℚ (r + 1)).hom
        (cylFibreRes q (γ 1) (r + 1) U) = 0 := by
      rw [← hfac 1, hW0, map_zero]
    exact hzinj1 (by rw [hz1, map_zero])
  · intro h
    have hW0 : W = 0 := h1' (by rw [hfac 1, h, map_zero, map_zero])
    have hz0 : (Work.Thom.relCohMap (pathPsiFibre q γ (0 : unitInterval))
        (cylFibreBot (Work.StemsB.pullbackSnd q γ) 0)
        (cylFibreBot q (γ 0)) (pathPsiFibre_mapsTo_bot q γ 0) ℚ (r + 1)).hom
        (cylFibreRes q (γ 0) (r + 1) U) = 0 := by
      rw [← hfac 0, hW0, map_zero]
    exact hzinj0 (by rw [hz0, map_zero])

end

end Work.Serre.DiscPair
