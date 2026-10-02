import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.thomClass_fibreGenerator
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Tubular.thomClass_span_top
import Submission.Work.Thom.step_natural
import Submission.Work.ThomBordism.nonempty_thomClass_normalBundle
import Submission.Work.ThomBordism.exists_fibreHomeomorph_normalBundle
import Submission.Work.ThomBordism.nfRes_fibreRes_naturality

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.ThomBordism

/-- The degree bookkeeping `0 + k = k` for generators. -/
theorem span_cast_singleton_eq_top_of_eq {M : ℕ → Type*} [∀ n, AddCommGroup (M n)]
    [∀ n, Module ℤ (M n)] {a b : ℕ} (h : a = b) (x : M a)
    (hx : Submodule.span ℤ ({(h ▸ x)} : Set (M b)) = ⊤) :
    Submodule.span ℤ ({x} : Set (M a)) = ⊤ := by
  cases h
  simpa using hx

theorem nfRes_span_top_of_generator {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    {U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)}
    (hspan : Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤) :
    Submodule.span ℤ ({Work.ThomBordism.nfRes E x k U} : Set (Work.Thom.RelCoh ℤ k
      ↥(Work.ThomBordism.nfSet E x) (Work.ThomBordism.nfPunct E x))) = ⊤ := by
  classical
  haveI : LocallyPathConnectedSpace V.pt :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 8)) V.pt
  haveI hpath : PathConnectedSpace V.pt := PathConnectedSpace.of_locallyPathConnectedSpace
  -- the integral Thom class of the normal bundle
  obtain ⟨Th⟩ := nonempty_thomClass_normalBundle (V := V) (k := k) hk E ND
  let nu : Work.TangentClasses.RealBundle V.pt (Work.Tubular.Euc k)
      (Work.ThomBordism.PontryaginThom.CoverIdx V k) := Work.Tubular.normalBundle E ND
  let φ : nu.TotalSpace ≃ₜ Work.Tubular.NormalTotal E := Work.Tubular.eucNormalHomeomorph E ND
  have hproj : ∀ p : nu.TotalSpace, Work.Tubular.NormalTotal.proj (φ p) = p.1 := fun p => rfl
  have hlen : ∀ p : nu.TotalSpace,
      Work.Thom.fibreNorm nu p ≠ 0 ↔ Work.Tubular.normalNorm E (φ p) ≠ 0 := by
    intro p
    rw [Work.Tubular.fibreNorm_eq_normalNorm, Work.Tubular.eucNormalHomeomorph_apply]
  -- the Thom class generates the relative cohomology of the Thom pair
  have hspanTh : Submodule.span ℤ ({Th.τ} : Set (Work.Thom.OpenThom nu k)) = ⊤ :=
    span_cast_singleton_eq_top_of_eq (M := fun m => Work.Thom.OpenThom nu m)
      (Nat.zero_add k).symm Th.τ (by simpa using Work.Tubular.thomClass_span_top nu k Th)
  -- compatibility of the homeomorphism with the punctured loci
  have hnorm_symm : ∀ p : Work.Tubular.NormalTotal E,
      Work.Thom.fibreNorm nu (φ.symm p) = Work.Tubular.normalNorm E p := by
    intro p
    rw [Work.Tubular.fibreNorm_eq_normalNorm]
    exact congrArg (Work.Tubular.normalNorm E) (φ.apply_symm_apply p)
  have hiffφs : ∀ p : Work.Tubular.NormalTotal E,
      p ∈ Work.Tubular.normalNonzero E ↔ φ.symm p ∈ Work.Thom.zeroComplement nu := by
    intro p
    rw [Work.Tubular.mem_normalNonzero, Work.Thom.mem_zeroComplement, ← hnorm_symm p,
      Work.Thom.fibreNorm]
    exact norm_ne_zero_iff
  have hmemφs : ∀ p ∈ Work.Tubular.normalNonzero E, φ.symm p ∈ Work.Thom.zeroComplement nu :=
    fun p hp => (hiffφs p).mp hp
  have hmemφ : ∀ p ∈ Work.Thom.zeroComplement nu, φ p ∈ Work.Tubular.normalNonzero E := by
    intro p hp
    have h1 : Work.Thom.fibreNorm nu p ≠ 0 := by
      rw [Work.Thom.fibreNorm]
      exact norm_ne_zero_iff.mpr ((Work.Thom.mem_zeroComplement p).mp hp)
    rw [Work.Tubular.mem_normalNonzero]
    exact (hlen p).mp h1
  -- the generator of the Thom pair coming from the Thom class
  let Lφs := (Work.Thom.relCohMap (φ.symm : C(Work.Tubular.NormalTotal E, nu.TotalSpace))
      (Work.Tubular.normalNonzero E) (Work.Thom.zeroComplement nu) hmemφs ℤ k).hom
  have hbijφs : Function.Bijective Lφs :=
    Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Tubular.normalNonzero E)
      (Work.Thom.zeroComplement nu) φ.symm hiffφs ℤ k
  let V' := Lφs Th.τ
  have hspanV' : Submodule.span ℤ ({V'} : Set _) = ⊤ :=
    Work.Tubular.span_singleton_map_eq_top Lφs hbijφs.2 (x := Th.τ) hspanTh
  -- the pullback of `V'` along `φ` is the Thom class itself
  let Lφ := (Work.Thom.relCohMap (φ : C(nu.TotalSpace, Work.Tubular.NormalTotal E))
      (Work.Thom.zeroComplement nu) (Work.Tubular.normalNonzero E) hmemφ ℤ k).hom
  have hgf1 : ∀ p ∈ Work.Thom.zeroComplement nu, φ.symm (φ p) ∈ Work.Thom.zeroComplement nu :=
    fun p hp => by rw [φ.symm_apply_apply]; exact hp
  have hcompφ : (Work.Thom.relCohMap ((φ.symm : C(Work.Tubular.NormalTotal E, nu.TotalSpace)).comp
        (φ : C(nu.TotalSpace, Work.Tubular.NormalTotal E)))
        (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement nu) hgf1 ℤ k)
      = Work.Thom.relCohMap (ContinuousMap.id nu.TotalSpace) (Work.Thom.zeroComplement nu)
        (Work.Thom.zeroComplement nu) (fun _ hx => hx) ℤ k :=
    Work.Thom.relCohMap_congrA (Work.Thom.zeroComplement nu) (Work.Thom.zeroComplement nu)
      (ContinuousMap.ext fun p => φ.symm_apply_apply p) hgf1 (fun _ hx => hx) ℤ k
  have hφV' : Lφ V' = Th.τ := by
    have h1 := Work.Thom.relCohMap_compA_apply (Work.Thom.zeroComplement nu)
      (Work.Tubular.normalNonzero E) (Work.Thom.zeroComplement nu)
      (φ : C(nu.TotalSpace, Work.Tubular.NormalTotal E))
      (φ.symm : C(Work.Tubular.NormalTotal E, nu.TotalSpace)) hmemφ hmemφs hgf1 ℤ k Th.τ
    rw [hcompφ] at h1
    rw [Work.Thom.relCohMap_idA (Work.Thom.zeroComplement nu) ℤ k, ModuleCat.hom_id] at h1
    simpa using h1
  -- the fibre transport
  obtain ⟨e, he, hpe⟩ := exists_fibreHomeomorph_normalBundle (V := V) (k := k) E ND x
  let Le := (Work.Thom.relCohMap (e : C(↥(Work.ThomBordism.fibre nu x),
      ↥(Work.ThomBordism.nfSet E x))) (Work.ThomBordism.fibrePunctSub nu x)
      (Work.ThomBordism.nfPunct E x) (fun p hp => (hpe p).mp hp) ℤ k).hom
  have hbijE : Function.Bijective Le :=
    Work.Thom.bijective_relCohMap_of_homeomorphA (Work.ThomBordism.fibrePunctSub nu x)
      (Work.ThomBordism.nfPunct E x) e hpe ℤ k
  have hgen : Work.ThomBordism.IsFibreGenerator nu k Th.τ :=
    Work.ThomBordism.thomClass_fibreGenerator nu Th (by simp [Work.Tubular.Euc])
  have hle : Le (Work.ThomBordism.nfRes E x k V')
      = Work.ThomBordism.fibreRes nu x k Th.τ := by
    rw [show Le (Work.ThomBordism.nfRes E x k V')
        = Work.ThomBordism.fibreRes nu x k (Lφ V') from
      nfRes_fibreRes_naturality (V := V) (k := k) (E := E) nu φ hproj hmemφ x e he hpe V', hφV']
  have hspanL : Submodule.span ℤ ({Le (Work.ThomBordism.nfRes E x k V')} : Set _) = ⊤ := by
    rw [hle]
    exact hgen x
  -- the generator transfers back along the bijection `Le`
  have hspanM : Submodule.span ℤ ({Work.ThomBordism.nfRes E x k V'} : Set _) = ⊤ := by
    have hmap : Submodule.map Le
        (Submodule.span ℤ ({(Work.ThomBordism.nfRes E x k V')} : Set _)) = ⊤ := by
      rw [Submodule.map_span, Set.image_singleton]
      exact hspanL
    have hcle : Submodule.comap Le (Submodule.map Le
        (Submodule.span ℤ ({(Work.ThomBordism.nfRes E x k V')} : Set _)))
        ≤ Submodule.span ℤ ({(Work.ThomBordism.nfRes E x k V')} : Set _) := by
      intro y hy
      rw [Submodule.mem_comap, Submodule.mem_map] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      rwa [hbijE.1 hzy] at hz
    rw [hmap, Submodule.comap_top] at hcle
    exact top_le_iff.mp hcle
  -- consequently `nfRes` is surjective, and it carries the generator `U` to a generator
  have hsurj : Function.Surjective (Work.ThomBordism.nfRes E x k) := by
    rw [← LinearMap.range_eq_top]
    have hmap : Submodule.map (Work.ThomBordism.nfRes E x k) ⊤ = ⊤ := by
      nth_rewrite 1 [← hspanV']
      rw [Submodule.map_span, Set.image_singleton]
      exact hspanM
    rw [LinearMap.range_eq_map]
    exact hmap
  exact Work.Tubular.span_singleton_map_eq_top (Work.ThomBordism.nfRes E x k) hsurj
    (x := U) hspan

end Work.ThomBordism
