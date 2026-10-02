import Mathlib
import Submission.Work.ThomBordism.fibreRes_span_iff
import Submission.Work.Thom.ATools
import Submission.Work.ThomBordism.fibreGenerator_bundleComap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

/-!
# Naturality of the fibre restriction of a Thom class

For a map of real bundles `G : Z.TotalSpace → Z'.TotalSpace` covering `f : B → B'` and inducing a
homeomorphism `e` of the fibre of `Z` over `b` with the fibre of `Z'` over `f b` (notation: `he`
says that the two underlying maps agree, `hpe` that they match the punctured fibres), the
restriction of a class `σ ∈ H^n(Z',Z'∖0;ℤ)` to the fibre and the map `G^*` commute:

`fibreRes_Z (G^* σ) = e^* (fibreRes_{Z'} σ)`.

Both sides are the pullback of `σ` along a map of pairs `(Z_b, Z_b∖0) → (Z'_{f b}, Z'_{f b}∖0)`,
and the two maps agree by `he`; the statement is exactly the functoriality of `relCohMap` for this
identity, the two composites being `G ∘ fibreIncl_Z` and `fibreIncl_{Z'} ∘ e`.  The proof below
mirrors `Work.ThomBordism.fibreRes_bundleComap`.
-/

theorem fibreRes_relCohMap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F F' : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {ι ι' : Type}
    (Z : Work.TangentClasses.RealBundle B F ι) (Z' : Work.TangentClasses.RealBundle B' F' ι')
    (f : C(B, B')) (G : C(Z.TotalSpace, Z'.TotalSpace)) (hf : ∀ p, (G p).proj = f p.proj)
    (hgm : ∀ p ∈ Work.Thom.zeroComplement Z, G p ∈ Work.Thom.zeroComplement Z')
    (b : B) (e : ↥(Work.ThomBordism.fibre Z b) ≃ₜ ↥(Work.ThomBordism.fibre Z' (f b)))
    (he : ∀ p, ((e p : ↥(Work.ThomBordism.fibre Z' (f b))) : Z'.TotalSpace) = G (p : Z.TotalSpace))
    (hpe : ∀ p, p ∈ Work.ThomBordism.fibrePunctSub Z b ↔
      e p ∈ Work.ThomBordism.fibrePunctSub Z' (f b))
    (n : ℕ) (σ : Work.Thom.OpenThom Z' n) :
    Work.ThomBordism.fibreRes Z b n
        ((Work.Thom.relCohMap G (Work.Thom.zeroComplement Z)
          (Work.Thom.zeroComplement Z') hgm ℤ n).hom σ)
      = (Work.Thom.relCohMap (e : C(↥(Work.ThomBordism.fibre Z b),
            ↥(Work.ThomBordism.fibre Z' (f b))))
          (Work.ThomBordism.fibrePunctSub Z b) (Work.ThomBordism.fibrePunctSub Z' (f b))
          (fun p hp => (hpe p).mp hp) ℤ n).hom
        (Work.ThomBordism.fibreRes Z' (f b) n σ) := by
  -- the punctured fibres are carried into the corresponding zero complements
  have hep : ∀ x ∈ fibrePunctSub Z b,
      (e : C(↥(fibre Z b), ↥(fibre Z' (f b)))) x ∈ fibrePunctSub Z' (f b) :=
    fun x hx => (hpe x).mp hx
  have hcompG : ∀ x ∈ fibrePunctSub Z b,
      G (fibreIncl Z b x) ∈ Work.Thom.zeroComplement Z' :=
    fun x hx => hgm _ (fibreIncl_mem Z b x hx)
  have hcompE : ∀ x ∈ fibrePunctSub Z b,
      fibreIncl Z' (f b) ((e : C(↥(fibre Z b), ↥(fibre Z' (f b)))) x)
        ∈ Work.Thom.zeroComplement Z' :=
    fun x hx => fibreIncl_mem Z' (f b) _ (hep x hx)
  -- unfold `fibreRes` on both sides
  show (ModuleCat.Hom.hom (Work.Thom.relCohMap (fibreIncl Z b) (fibrePunctSub Z b)
        (Work.Thom.zeroComplement Z) (fibreIncl_mem Z b) ℤ n))
      (ModuleCat.Hom.hom (Work.Thom.relCohMap G (Work.Thom.zeroComplement Z)
        (Work.Thom.zeroComplement Z') hgm ℤ n) σ)
    = (ModuleCat.Hom.hom (Work.Thom.relCohMap
        (e : C(↥(fibre Z b), ↥(fibre Z' (f b))))
        (fibrePunctSub Z b) (fibrePunctSub Z' (f b))
        (fun p hp => (hpe p).mp hp) ℤ n))
      (ModuleCat.Hom.hom (Work.Thom.relCohMap (fibreIncl Z' (f b)) (fibrePunctSub Z' (f b))
        (Work.Thom.zeroComplement Z') (fibreIncl_mem Z' (f b)) ℤ n) σ)
  -- functoriality of `relCohMap` for the two composites `G ∘ fibreIncl_Z` and
  -- `fibreIncl_{Z'} ∘ e`, which are the same map of pairs by `he`
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
      (Work.Thom.relCohMap G (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z')
        hgm ℤ n)
      (Work.Thom.relCohMap (fibreIncl Z b) (fibrePunctSub Z b) (Work.Thom.zeroComplement Z)
        (fibreIncl_mem Z b) ℤ n),
    Work.Thom.relCohMap_compA (fibrePunctSub Z b) (Work.Thom.zeroComplement Z)
      (Work.Thom.zeroComplement Z') (fibreIncl Z b) G (fibreIncl_mem Z b) hgm hcompG ℤ n]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
      (Work.Thom.relCohMap (fibreIncl Z' (f b)) (fibrePunctSub Z' (f b))
        (Work.Thom.zeroComplement Z') (fibreIncl_mem Z' (f b)) ℤ n)
      (Work.Thom.relCohMap (e : C(↥(fibre Z b), ↥(fibre Z' (f b)))) (fibrePunctSub Z b)
        (fibrePunctSub Z' (f b)) (fun p hp => (hpe p).mp hp) ℤ n),
    Work.Thom.relCohMap_compA (fibrePunctSub Z b) (fibrePunctSub Z' (f b))
      (Work.Thom.zeroComplement Z') (e : C(↥(fibre Z b), ↥(fibre Z' (f b))))
      (fibreIncl Z' (f b)) hep (fibreIncl_mem Z' (f b)) hcompE ℤ n]
  -- the two composites agree as maps
  have heq : G.comp (fibreIncl Z b)
      = (fibreIncl Z' (f b)).comp (e : C(↥(fibre Z b), ↥(fibre Z' (f b)))) := by
    apply ContinuousMap.ext
    intro x
    exact (he x).symm
  exact congrArg (fun m => (ModuleCat.Hom.hom m) σ)
    (Work.Thom.relCohMap_congrA (fibrePunctSub Z b) (Work.Thom.zeroComplement Z')
      heq hcompG hcompE ℤ n)

end

end Work.ThomBordism
