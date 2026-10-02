import Mathlib
import Submission.Work.ThomBordism.thomClassFibreDefs
import Submission.Work.Thom.comapAux
import Submission.Work.ThomBordism.fibreGeneratorBundleComap
import Submission.Work.Thom.ATools

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The fibre-generator condition is preserved by pulling a bundle back

If a class `σ ∈ H^n(E,E∖0;ℤ)` of a real bundle `Z` restricts to a generator of the relative
cohomology of every fibre pair `(Z_b, Z_b∖0)`, then its pullback along `f : C(B',B)` has the same
property for the pullback bundle `f^*Z`.

The mathematical content is that the fibre of `f^*Z` at `b'` is *canonically* the fibre of `Z` at
`f b'` — the map `⟨b',v⟩ ↦ ⟨f b',v⟩` is a homeomorphism of pairs, both fibres being identified with
the model fibre by the second coordinate (`fibreComapHomeomorph`).  Consequently the restriction of
the pulled-back class to the fibre over `b'` is the image of the restriction of `σ` to the fibre
over `f b'` under an isomorphism of `ℤ`-modules, which carries generators to generators.
-/

namespace Work.ThomBordism

open Work.TangentClasses

noncomputable section

variable {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}

/-! ## The model-fibre coordinate on a fibre -/

/-- **The model-fibre coordinate `p ↦ p.2` is continuous on the fibre** of a real bundle over `b`:
on the fibre, the trivialisation at `b` is the identity `p ↦ (b, p.2)`. -/
theorem continuous_fibreSnd (Z : RealBundle B F ι) (b : B) :
    Continuous fun q : ↥(fibre Z b) => ((q : Z.TotalSpace).2 : F) := by
  have hmem : ∀ q : ↥(fibre Z b), (q : Z.TotalSpace) ∈ (Z.localTrivAt b).source := by
    intro q
    rw [← VectorBundleCore.localTrivAt_def, VectorBundleCore.mem_localTriv_source]
    rw [show ((q : Z.TotalSpace).1 : B) = b from q.2]
    exact Z.mem_baseSet_at b
  have hcont₁ : Continuous fun q : ↥(fibre Z b) => Z.localTrivAt b (q : Z.TotalSpace) :=
    continuousOn_univ.mp
      ((Z.localTrivAt b).continuousOn.comp continuous_subtype_val.continuousOn
        (by intro q _; exact hmem q))
  refine (hcont₁.snd).congr (fun q => ?_)
  have h := VectorBundleCore.localTrivAt_apply Z (q : Z.TotalSpace)
  rw [show (q : Z.TotalSpace).proj = b from q.2] at h
  exact congrArg Prod.snd h

/-- Two points of the total space of a real bundle (whose fibre is constantly the model fibre) are
equal as soon as their base points and their model-fibre coordinates agree. -/
theorem totalSpace_eq_of {Z : RealBundle B F ι} {p q : Z.TotalSpace}
    (h1 : p.1 = q.1) (h2 : (p.2 : F) = (q.2 : F)) : p = q := by
  obtain ⟨x, v⟩ := p
  obtain ⟨y, w⟩ := q
  subst h1
  exact Bundle.TotalSpace.mk_inj.mpr h2

/-! ## The fibre of a pullback -/

/-- **The canonical homeomorphism between the fibre of a pullback bundle and the fibre of the
bundle**: the map `⟨b',v⟩ ↦ ⟨f b',v⟩`, both fibres being identified with the model fibre `F` by the
second coordinate. -/
def fibreComapHomeomorph (Z : RealBundle B F ι) (f : C(B', B)) (b' : B') :
    ↥(fibre (Work.Thom.bundleComap Z f) b') ≃ₜ ↥(fibre Z (f b')) where
  toFun p := fibreMapComap Z f b' p
  invFun q := ⟨Bundle.TotalSpace.mk b' (show (Work.Thom.bundleComap Z f).Fiber b' from
    ((q : Z.TotalSpace).2 : F)), rfl⟩
  left_inv p := by
    refine Subtype.ext (totalSpace_eq_of ?_ ?_)
    · exact (p.2).symm
    · rfl
  right_inv q := by
    refine Subtype.ext (totalSpace_eq_of ?_ ?_)
    · exact (q.2).symm
    · rfl
  continuous_toFun := (fibreMapComap Z f b').continuous
  continuous_invFun := by
    have hcont : Continuous fun q : ↥(fibre Z (f b')) =>
        (Bundle.TotalSpace.mk b' (show (Work.Thom.bundleComap Z f).Fiber b' from
          ((q : Z.TotalSpace).2 : F)) : (Work.Thom.bundleComap Z f).TotalSpace) :=
      (FiberBundle.continuous_totalSpaceMk (F := F)
        (E := (Work.Thom.bundleComap Z f).Fiber) b').comp (continuous_fibreSnd Z (f b'))
    exact hcont.subtype_mk (fun q => rfl)

@[simp] theorem fibreComapHomeomorph_apply (Z : RealBundle B F ι) (f : C(B', B)) (b' : B')
    (p : ↥(fibre (Work.Thom.bundleComap Z f) b')) :
    ((fibreComapHomeomorph Z f b' p : ↥(fibre Z (f b'))) : Z.TotalSpace)
      = Work.Thom.totalMap Z f (p : (Work.Thom.bundleComap Z f).TotalSpace) := rfl

/-- **The pullback of relative cohomology along `fibreMapComap` is a bijection**: the fibre of the
pullback bundle over `b'` is canonically the fibre of `Z` over `f b'`. -/
theorem fibreMapComap_bijective (Z : RealBundle B F ι) (f : C(B', B)) (b' : B') (n : ℕ) :
    Function.Bijective (Work.Thom.relCohMap (fibreMapComap Z f b')
      (fibrePunctSub (Work.Thom.bundleComap Z f) b')
      (fibrePunctSub Z (f b'))
      (fibreMapComap_mem Z f b') ℤ n).hom := by
  have he : ∀ p : ↥(fibre (Work.Thom.bundleComap Z f) b'),
      p ∈ fibrePunctSub (Work.Thom.bundleComap Z f) b' ↔
        fibreComapHomeomorph Z f b' p ∈ fibrePunctSub Z (f b') := by
    intro p
    constructor
    · intro hp
      exact ⟨(fibreComapHomeomorph Z f b' p).2, by
        show ((fibreComapHomeomorph Z f b' p : ↥(fibre Z (f b'))) : Z.TotalSpace).2 ≠ 0
        rw [fibreComapHomeomorph_apply, Work.Thom.totalMap_apply]
        exact hp.2⟩
    · intro hp
      have h2 : ((fibreComapHomeomorph Z f b' p : ↥(fibre Z (f b'))) : Z.TotalSpace).2 ≠ 0 :=
        hp.2
      rw [fibreComapHomeomorph_apply, Work.Thom.totalMap_apply] at h2
      exact ⟨p.2, h2⟩
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
    (fibrePunctSub (Work.Thom.bundleComap Z f) b') (fibrePunctSub Z (f b'))
    (fibreComapHomeomorph Z f b') he ℤ n
  have hmap : ((fibreComapHomeomorph Z f b' : C(↥(fibre (Work.Thom.bundleComap Z f) b'),
        ↥(fibre Z (f b'))))) = fibreMapComap Z f b' := by
    apply ContinuousMap.ext
    intro p
    rfl
  rwa [Work.Thom.relCohMap_congrA (fibrePunctSub (Work.Thom.bundleComap Z f) b')
      (fibrePunctSub Z (f b')) hmap (fun x hx => (he x).mp hx)
      (fibreMapComap_mem Z f b') ℤ n] at hbij

/-! ## The fibre-generator condition -/

/-- **The restriction of a pulled-back class to a fibre is the pullback of its restriction**: the
square

`H^n(E,E∖0) --(fibreIncl)^*--> H^n(E_{f b'}, E_{f b'}∖0)`
`      |                                    |`
`  (f^*Z pullback)                    (fibreMapComap)^*`
`      v                                    v`
`H^n(f^*E,f^*E∖0) --(fibreIncl)^*--> H^n(f^*E_{b'}, f^*E_{b'}∖0)`

commutes.  (Here `f^*E_{b'}` denotes the fibre of the pullback bundle over `b'`.) -/
theorem fibreRes_bundleComap (Z : RealBundle B F ι) (f : C(B', B)) (b' : B') (n : ℕ)
    (σ : Work.Thom.OpenThom Z n) :
    fibreRes (Work.Thom.bundleComap Z f) b' n
        ((Work.Thom.relCohMap (Work.Thom.totalMap Z f)
          (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
          (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom σ)
      = (Work.Thom.relCohMap (fibreMapComap Z f b')
          (fibrePunctSub (Work.Thom.bundleComap Z f) b') (fibrePunctSub Z (f b'))
          (fibreMapComap_mem Z f b') ℤ n).hom (fibreRes Z (f b') n σ) := by
  set W := Work.Thom.bundleComap Z f with hW
  set A : Set ↥(fibre W b') := fibrePunctSub W b' with hA
  set Bs : Set ↥(fibre Z (f b')) := fibrePunctSub Z (f b') with hBs
  set zW : Set W.TotalSpace := Work.Thom.zeroComplement W with hzW
  set zZ : Set Z.TotalSpace := Work.Thom.zeroComplement Z with hzZ
  show (Work.Thom.relCohMap (fibreIncl W b') A zW (fibreIncl_mem W b') ℤ n).hom
      ((Work.Thom.relCohMap (Work.Thom.totalMap Z f) zW zZ
        (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom σ)
    = (Work.Thom.relCohMap (fibreMapComap Z f b') A Bs (fibreMapComap_mem Z f b') ℤ n).hom
      ((Work.Thom.relCohMap (fibreIncl Z (f b')) Bs zZ (fibreIncl_mem Z (f b')) ℤ n).hom σ)
  -- the composite `totalMap ∘ fibreIncl` carries the punctured fibre into `zeroComplement Z` …
  have hcomp : ∀ x ∈ A, (Work.Thom.totalMap Z f) (fibreIncl W b' x) ∈ zZ :=
    fun x hx => Work.Thom.totalMap_mem_zeroComplement Z f _ (fibreIncl_mem W b' x hx)
  -- … and so does the composite `fibreIncl ∘ fibreMapComap`, which is the same map.
  have hcomp' : ∀ x ∈ A, ((fibreIncl Z (f b')).comp (fibreMapComap Z f b')) x ∈ zZ := by
    intro x hx
    rw [fibreIncl_comp_fibreMapComap Z f b']
    exact hcomp x hx
  -- Functoriality of `relCohMap` for the two composites.
  have hAstep : CategoryTheory.CategoryStruct.comp
        (Work.Thom.relCohMap (Work.Thom.totalMap Z f) zW zZ
          (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n)
        (Work.Thom.relCohMap (fibreIncl W b') A zW (fibreIncl_mem W b') ℤ n)
      = (Work.Thom.relCohMap ((fibreIncl Z (f b')).comp (fibreMapComap Z f b')) A zZ
          hcomp' ℤ n) :=
    (Work.Thom.relCohMap_compA A zW zZ (fibreIncl W b') (Work.Thom.totalMap Z f)
        (fibreIncl_mem W b') (Work.Thom.totalMap_mem_zeroComplement Z f) hcomp ℤ n).trans
      (Work.Thom.relCohMap_congrA A zZ (fibreIncl_comp_fibreMapComap Z f b')
        hcomp hcomp' ℤ n)
  have hBstep : CategoryTheory.CategoryStruct.comp
        (Work.Thom.relCohMap (fibreIncl Z (f b')) Bs zZ (fibreIncl_mem Z (f b')) ℤ n)
        (Work.Thom.relCohMap (fibreMapComap Z f b') A Bs (fibreMapComap_mem Z f b') ℤ n)
      = (Work.Thom.relCohMap ((fibreIncl Z (f b')).comp (fibreMapComap Z f b')) A zZ
          hcomp' ℤ n) :=
    Work.Thom.relCohMap_compA A Bs zZ (fibreMapComap Z f b') (fibreIncl Z (f b'))
      (fibreMapComap_mem Z f b') (fibreIncl_mem Z (f b')) hcomp' ℤ n
  have lhs_eq : (Work.Thom.relCohMap (fibreIncl W b') A zW (fibreIncl_mem W b') ℤ n).hom
        ((Work.Thom.relCohMap (Work.Thom.totalMap Z f) zW zZ
          (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom σ)
      = (Work.Thom.relCohMap ((fibreIncl Z (f b')).comp (fibreMapComap Z f b')) A zZ
          hcomp' ℤ n).hom σ := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
        (Work.Thom.relCohMap (Work.Thom.totalMap Z f) zW zZ
          (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n)
        (Work.Thom.relCohMap (fibreIncl W b') A zW (fibreIncl_mem W b') ℤ n), hAstep]
  have rhs_eq : (Work.Thom.relCohMap (fibreMapComap Z f b') A Bs (fibreMapComap_mem Z f b')
          ℤ n).hom
        ((Work.Thom.relCohMap (fibreIncl Z (f b')) Bs zZ (fibreIncl_mem Z (f b')) ℤ n).hom σ)
      = (Work.Thom.relCohMap ((fibreIncl Z (f b')).comp (fibreMapComap Z f b')) A zZ
          hcomp' ℤ n).hom σ := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp
        (Work.Thom.relCohMap (fibreIncl Z (f b')) Bs zZ (fibreIncl_mem Z (f b')) ℤ n)
        (Work.Thom.relCohMap (fibreMapComap Z f b') A Bs (fibreMapComap_mem Z f b') ℤ n),
      hBstep]
  rw [lhs_eq, rhs_eq]

theorem fibreGenerator_bundleComap {B B' : Type} [TopologicalSpace B] [TopologicalSpace B']
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type} {n : ℕ}
    (Z : Work.TangentClasses.RealBundle B F ι) (f : C(B', B)) (σ : Work.Thom.OpenThom Z n)
    (h : Work.ThomBordism.IsFibreGenerator Z n σ) :
    Work.ThomBordism.IsFibreGenerator (Work.Thom.bundleComap Z f) n
      ((Work.Thom.relCohMap (Work.Thom.totalMap Z f)
        (Work.Thom.zeroComplement (Work.Thom.bundleComap Z f))
        (Work.Thom.zeroComplement Z) (Work.Thom.totalMap_mem_zeroComplement Z f) ℤ n).hom σ) := by
  intro b'
  obtain hbij := fibreMapComap_bijective Z f b' n
  -- the class generating the fibre over `f b'`
  have hgen : Submodule.span ℤ {fibreRes Z (f b') n σ} = ⊤ := h (f b')
  -- its image under the fibre isomorphism generates the fibre over `b'`
  have hkey := fibreRes_bundleComap Z f b' n σ
  have hmap : Submodule.map (Work.Thom.relCohMap (fibreMapComap Z f b')
        (fibrePunctSub (Work.Thom.bundleComap Z f) b') (fibrePunctSub Z (f b'))
        (fibreMapComap_mem Z f b') ℤ n).hom (Submodule.span ℤ {fibreRes Z (f b') n σ})
      = Submodule.span ℤ {((Work.Thom.relCohMap (fibreMapComap Z f b')
        (fibrePunctSub (Work.Thom.bundleComap Z f) b') (fibrePunctSub Z (f b'))
        (fibreMapComap_mem Z f b') ℤ n).hom (fibreRes Z (f b') n σ))} := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [hkey, ← hmap, hgen, Submodule.map_top, LinearMap.range_eq_top.mpr hbij.2]

end

end Work.ThomBordism
