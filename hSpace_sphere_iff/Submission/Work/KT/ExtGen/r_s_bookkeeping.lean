import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.AssemblyDefs
import Submission.Work.KT.Fund.Geom
import Submission.Work.KT.Fund.Disc
import Submission.Work.KT.bott_aux
import Submission.Work.KT.k0_basic

/-!
# `Work.KT.ExtGen` — the elementary retraction facts for `Work.KT.fund_product`

With `M = K0 C(X × S2, ℂ)`, `A = K0 C(X, ℂ)`, `s = Fund.s X` (pull-back along `fst`) and
`r = Fund.r X` (restriction to the fibre over the base point `pt = up 0` of `S²`), we have

* `r ∘ s = id` (`r_comp_s`) — because `fst ∘ bp = id`;
* `s` injective (`s_injective`);
* `r` is multiplicative for any pair of `IsK0Mul` products (`r_comp_mul`) — the naturality of the
  `K₀`-product under the algebra homomorphism `pullAlg (bp X)` (`bott_aux.ba_k0_mul_natural`);
* `r = ev0 ∘ pullUp` (`r_eq_ev0_comp_pullUp`, `pt = up 0` is the *centre* of the upper disc), hence
  `ker r = ker (pullUp X)` (`r_zero_imp_pullUp_zero`).

These are exactly the hypotheses `hrs` and `hrmul` of the assembly `EG.fund_product_of_bott`
together with the disc-restriction input of `Work.KT.kappa_span` (GEN); they were stated nowhere
else in the library.
-/

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

/-- `r ∘ s = id`: the restriction to the fibre over the base point is a retraction of the pull-back
along the projection. -/
theorem r_comp_s (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (a : K0 C(X, ℂ)) : Work.KT.Fund.r X (Work.KT.Fund.s X a) = a := by
  have hbp : (ContinuousMap.fst : C(X × S2, X)).comp (Work.KT.Fund.bp X)
      = ContinuousMap.id X := by
    ext x
    rfl
  have h1 : (Work.KT.pullAlg (Work.KT.Fund.bp X)).comp
      (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X))) = AlgHom.id ℂ C(X, ℂ) := by
    rw [← Work.KT.Fund.pullAlg_comp (Work.KT.Fund.bp X)
        (ContinuousMap.fst : C(X × S2, X)), hbp, Work.KT.Fund.pullAlg_id]
  show K0.mapA (Work.KT.pullAlg (Work.KT.Fund.bp X))
      (K0.mapA (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X))) a) = a
  rw [Work.KT.ba_mapA_comp_apply (Work.KT.pullAlg (ContinuousMap.fst : C(X × S2, X)))
      (Work.KT.pullAlg (Work.KT.Fund.bp X)) a, h1, Work.KT.ba_mapA_id_apply]

/-- `Fund.s X` is injective (immediate from `r_comp_s`). -/
theorem s_injective (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] :
    Function.Injective (Work.KT.Fund.s X) := by
  intro a b h
  rw [← r_comp_s X a, ← r_comp_s X b, h]

/-- `r` is multiplicative: for `IsK0Mul` products `μ` on `M` and `μX` on `A`,
`r (μ x y) = μX (r x) (r y)`. -/
theorem r_comp_mul (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (μ : K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ) →+ K0 C(X × S2, ℂ)) (hμ : IsK0Mul μ)
    (μX : K0 C(X, ℂ) →+ K0 C(X, ℂ) →+ K0 C(X, ℂ)) (hμX : IsK0Mul μX)
    (x y : K0 C(X × S2, ℂ)) :
    Work.KT.Fund.r X (μ x y) = μX (Work.KT.Fund.r X x) (Work.KT.Fund.r X y) :=
  Work.KT.ba_k0_mul_natural (C(X × S2, ℂ)) (C(X, ℂ))
    (Work.KT.pullAlg (Work.KT.Fund.bp X)).toRingHom μ μX (fun a b => mul_comm a b) hμ hμX x y

/-! ## `ker r = ker (pullUp X)`

`pt = up 0` is the *centre* of the disc `D⁺` parametrising the upper hemisphere, whence
`r = ev0 ∘ pullUp`; and a class over the disc is the pull-back of its restriction to the centre
(`Fund.sD_ev0`).  So `ker r = ker (pullUp X)`.  Together with
`Work.KT.ExtGen.ker_r_subset_ker_pullDn` (base-point independence of the two hemispheres) this
gives the hypotheses of `Work.KT.kappa_span` (GEN) for classes in `ker r`. -/

/-- The upper hemisphere parametrisation `X × D → X × S²`. -/
def upMap (X : Type) [TopologicalSpace X] : C(X × Ball ℂ, X × S2) :=
  ⟨fun p => (p.1, Work.KT.Fund.up p.2),
    Continuous.prodMk continuous_fst
      (Work.KT.Fund.continuous_up.comp continuous_snd)⟩

lemma pullUp_eq_pullAlg (X : Type) [TopologicalSpace X] :
    Work.KT.Fund.pullUp X = (Work.KT.pullAlg (upMap X)).toRingHom := by
  refine RingHom.ext fun g => ?_
  refine ContinuousMap.ext fun p => ?_
  rfl

lemma bp_eq_upMap_comp (X : Type) [TopologicalSpace X] :
    Work.KT.Fund.bp X = (upMap X).comp (Work.KT.Fund.zeroX X) := by
  refine ContinuousMap.ext fun x => ?_
  refine Prod.ext rfl ?_
  rfl

/-- `r = ev0 ∘ (pullUp X)`: the two ways of restricting to the centre of the upper disc. -/
theorem r_eq_ev0_comp_pullUp' (X : Type) [TopologicalSpace X] :
    Work.KT.Fund.r X = (Work.KT.Fund.ev0 X).comp (K0.map (Work.KT.Fund.pullUp X)) := by
  have h1 : Work.KT.pullAlg (Work.KT.Fund.bp X) =
      (Work.KT.pullAlg (Work.KT.Fund.zeroX X)).comp (Work.KT.pullAlg (upMap X)) := by
    rw [bp_eq_upMap_comp X,
      Work.KT.Fund.pullAlg_comp (Work.KT.Fund.zeroX X) (upMap X)]
  have h2 : K0.mapA (Work.KT.pullAlg (Work.KT.Fund.bp X)) =
      (K0.mapA (Work.KT.pullAlg (Work.KT.Fund.zeroX X))).comp
        (K0.mapA (Work.KT.pullAlg (upMap X))) := by
    rw [h1, Work.KT.ba_mapA_comp]
  have h3 : K0.mapA (Work.KT.pullAlg (upMap X)) = K0.map (Work.KT.Fund.pullUp X) := by
    rw [pullUp_eq_pullAlg X]
  show K0.mapA (Work.KT.pullAlg (Work.KT.Fund.bp X)) = _
  rw [h2, h3]
  rfl

theorem r_zero_imp_pullUp_zero (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (z : K0 C(X × S2, ℂ)) : Work.KT.Fund.r X z = 0 →
      K0.map (Work.KT.Fund.pullUp X) z = 0 := by
  intro hz
  have h1 : Work.KT.Fund.ev0 X (K0.map (Work.KT.Fund.pullUp X) z) = 0 := by
    have h1' : Work.KT.Fund.r X z = 0 := hz
    rw [r_eq_ev0_comp_pullUp' X] at h1'
    simpa only [AddMonoidHom.comp_apply] using h1'
  have h2 : Work.KT.Fund.sD X (0 : K0 C(X, ℂ)) = K0.map (Work.KT.Fund.pullUp X) z := by
    rw [← h1]
    exact Work.KT.Fund.sD_ev0 X (K0.map (Work.KT.Fund.pullUp X) z)
  rw [map_zero] at h2
  exact h2.symm

end

end Work.KT.ExtGen
