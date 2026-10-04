import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.sphereCapContractible
import Submission.Work.Cohomology.sphereCapContractibleLt
import Submission.Work.Cohomology.sphereBandHomotopyEquiv
import Submission.Work.Cohomology.epsilonNaturality
import Submission.Work.Cohomology.SphDefs
import Submission.Work.Cohomology.reducedH0OfTwoPoints

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

/-!
# `H_n(S^n) ≅ ℤ`

The `n`-th singular homology (with `ℤ` coefficients) of the unit sphere `S^n ⊆ ℝ^(n+1)` is `ℤ`
for `n ≥ 1`.  The proof is the classical Mayer–Vietoris induction: the sphere `S^(m+1)` is
covered by the two contractible caps `capA m`, `capB m` whose intersection is the equatorial band
`band m`, homotopy equivalent to `S^m`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-! ## 2. Inputs from the geometry of the caps and the band -/

/-- The cap `{x ∈ S^(m+1) : x (last m) > -1/2}` is contractible. -/
lemma contractibleSpace_capA (m : ℕ) : ContractibleSpace ↥(capA m) := by
  haveI h : ContractibleSpace
      {x : EuclideanSpace ℝ (Fin (m+1)) // sphSet (m+1) x ∧ x (Fin.last m) > -(1/2)} :=
    sphereCapContractible m (1/2) (by norm_num) (by norm_num)
  exact Homeomorph.contractibleSpace
    (flatHomeo (q := sphSet (m+1)) (P := fun x => x (Fin.last m) > -(1/2)))

/-- The cap `{x ∈ S^(m+1) : x (last m) < 1/2}` is contractible. -/
lemma contractibleSpace_capB (m : ℕ) : ContractibleSpace ↥(capB m) := by
  haveI h : ContractibleSpace
      {x : EuclideanSpace ℝ (Fin (m+1)) // sphSet (m+1) x ∧ x (Fin.last m) < 1/2} :=
    sphereCapContractibleLt m (1/2) (by norm_num) (by norm_num)
  exact Homeomorph.contractibleSpace
    (flatHomeo (q := sphSet (m+1)) (P := fun x => x (Fin.last m) < 1/2))

/-- The equatorial band of `S^(m+1)` is homotopy equivalent to `S^m`. -/
lemma bandHomotopyEquiv (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(band m) ↥(sphSet m)) := by
  obtain ⟨e⟩ := sphereBandHomotopyEquiv m hm
  exact ⟨(flatHomeo (q := sphSet (m+1))
    (P := fun x => x (Fin.last m) > -(1/2) ∧ x (Fin.last m) < 1/2)).toHomotopyEquiv.trans e⟩

/-- A homotopy equivalence of spaces induces an isomorphism on singular homology. -/
lemma homologyIso_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Nonempty (((singularChains ℤ (TopCat.of X)).homology n)
      ≅ ((singularChains ℤ (TopCat.of Y)).homology n)) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := e.right_inv.some
  haveI := homologyEquiv ℤ (TopCat.of X) (TopCat.of Y) f g h1 h2 n
  exact ⟨CategoryTheory.asIso
    (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of X) (TopCat.of Y) f) n)⟩

/-- Naturality of the degree-`0` augmentation, at the level of the underlying linear maps. -/
lemma eps_comp_homologyMap {X Y : TopCat} (f : X ⟶ Y) :
    (TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ)).hom.comp
        (HomologicalComplex.homologyMap (chainMap ℤ X Y f) 0).hom
      = (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)).hom := by
  rw [← ModuleCat.hom_comp, epsilonNaturality X Y f]

/-- A `ℤ`-linear bijection `F : M ≅ N` that carries the functional `g` to the functional `f`
restricts to an isomorphism of the two kernels. -/
lemma kerIsoOf {M N : ModuleCat ℤ} (f : M ⟶ ModuleCat.of ℤ ℤ) (g : N ⟶ ModuleCat.of ℤ ℤ)
    (F : M ≅ N) (h : F.hom ≫ g = f) :
    Nonempty (kerMod (ModuleCat.Hom.hom f) ≅ kerMod (ModuleCat.Hom.hom g)) := by
  have hF : ∀ x : ↥M, ModuleCat.Hom.hom g (ModuleCat.Hom.hom F.hom x) = ModuleCat.Hom.hom f x := by
    intro x
    have e : ModuleCat.Hom.hom g ∘ₗ ModuleCat.Hom.hom F.hom = ModuleCat.Hom.hom f := by
      rw [← ModuleCat.hom_comp, h]
    have h' : (ModuleCat.Hom.hom g ∘ₗ ModuleCat.Hom.hom F.hom) x = ModuleCat.Hom.hom f x := by
      rw [e]
    simpa only [LinearMap.comp_apply] using h'
  have hinv1 : ∀ x : ↥M, ModuleCat.Hom.hom F.inv (ModuleCat.Hom.hom F.hom x) = x := by
    intro x
    have e : ModuleCat.Hom.hom F.inv ∘ₗ ModuleCat.Hom.hom F.hom = LinearMap.id := by
      rw [← ModuleCat.hom_comp, F.hom_inv_id, ModuleCat.hom_id]
    have h' : (ModuleCat.Hom.hom F.inv ∘ₗ ModuleCat.Hom.hom F.hom) x = x := by
      rw [e]
      rfl
    simpa only [LinearMap.comp_apply] using h'
  have hinv2 : ∀ y : ↥N, ModuleCat.Hom.hom F.hom (ModuleCat.Hom.hom F.inv y) = y := by
    intro y
    have e : ModuleCat.Hom.hom F.hom ∘ₗ ModuleCat.Hom.hom F.inv = LinearMap.id := by
      rw [← ModuleCat.hom_comp, F.inv_hom_id, ModuleCat.hom_id]
    have h' : (ModuleCat.Hom.hom F.hom ∘ₗ ModuleCat.Hom.hom F.inv) y = y := by
      rw [e]
      rfl
    simpa only [LinearMap.comp_apply] using h'
  have e0 : ModuleCat.of ℤ ↥(LinearMap.ker (ModuleCat.Hom.hom f)) ≅
      ModuleCat.of ℤ ↥(LinearMap.ker (ModuleCat.Hom.hom g)) := by
    refine LinearEquiv.toModuleIso (LinearEquiv.ofBijective (f := ?_) ?_)
    · refine { toFun := fun x => ⟨ModuleCat.Hom.hom F.hom x.1, ?_⟩
               map_add' := fun x y => Subtype.ext (map_add (ModuleCat.Hom.hom F.hom) x.1 y.1)
               map_smul' := fun c x => Subtype.ext (by
                 first
                   | (simp; try rfl; done)
                   | exact (ModuleCat.Hom.hom F.hom).map_smulₛₗ c x.1
                   | (rw [Submodule.coe_smul]
                      exact (ModuleCat.Hom.hom F.hom).map_smulₛₗ c x.1)) }
      rw [LinearMap.mem_ker, hF x.1, LinearMap.mem_ker.mp x.2]
    · constructor
      · intro x y hxy
        have h1 : ModuleCat.Hom.hom F.hom x.1 = ModuleCat.Hom.hom F.hom y.1 :=
          congrArg (fun z : ↥(LinearMap.ker (ModuleCat.Hom.hom g)) => z.1) hxy
        exact Subtype.ext (by rw [← hinv1 x.1, ← hinv1 y.1, h1])
      · intro y
        refine ⟨⟨ModuleCat.Hom.hom F.inv y.1, ?_⟩, Subtype.ext (hinv2 y.1)⟩
        rw [LinearMap.mem_ker, ← hF (ModuleCat.Hom.hom F.inv y.1), hinv2 y.1,
          LinearMap.mem_ker.mp y.2]
  exact ⟨moduleCatOfIsoOfEq.symm ≪≫ e0 ≪≫ moduleCatOfIsoOfEq⟩

/-- The kernel of the augmentation is an invariant of homotopy equivalence. -/
lemma ker_eps_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    Nonempty (kerMod (ModuleCat.Hom.hom
        (TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℤ ℤ)))
      ≅ kerMod (ModuleCat.Hom.hom
        (TopCat.singularHomology₀ε (TopCat.of Y) (ModuleCat.of ℤ ℤ)))) := by
  let f : TopCat.of X ⟶ TopCat.of Y := TopCat.ofHom e.toFun
  let g : TopCat.of Y ⟶ TopCat.of X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of X)) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of Y)) := e.right_inv.some
  haveI hiso : IsIso (HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of X) (TopCat.of Y) f) 0) :=
    homologyEquiv ℤ (TopCat.of X) (TopCat.of Y) f g h1 h2 0
  have hmain : (CategoryTheory.asIso (HomologicalComplex.homologyMap
        (chainMap ℤ (TopCat.of X) (TopCat.of Y) f) 0)).hom
        ≫ TopCat.singularHomology₀ε (TopCat.of Y) (ModuleCat.of ℤ ℤ)
      = TopCat.singularHomology₀ε (TopCat.of X) (ModuleCat.of ℤ ℤ) := by
    rw [show (CategoryTheory.asIso (HomologicalComplex.homologyMap
          (chainMap ℤ (TopCat.of X) (TopCat.of Y) f) 0)).hom
        = HomologicalComplex.homologyMap (chainMap ℤ (TopCat.of X) (TopCat.of Y) f) 0 from rfl]
    exact epsilonNaturality (TopCat.of X) (TopCat.of Y) f
  exact kerIsoOf _ _ _ hmain

/-- The two descriptions of the sphere as a set agree. -/
lemma sphereSet_eq (m : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 = sphSet m := by
  ext x
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  rfl

/-! ## 2b. Elementary properties of the caps -/

lemma continuous_lastCoord (m : ℕ) :
    Continuous (fun x : sphTop (m+1) => x.1 (Fin.last m)) := by
  have h1 : Continuous (fun y : EuclideanSpace ℝ (Fin (m+1)) => y (Fin.last m)) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin (m+1) => ℝ) (Fin.last m)
  exact h1.comp continuous_subtype_val

lemma isOpen_capA (m : ℕ) : IsOpen (capA m) :=
  isOpen_lt continuous_const (continuous_lastCoord m)

lemma isOpen_capB (m : ℕ) : IsOpen (capB m) :=
  isOpen_lt (continuous_lastCoord m) continuous_const

lemma capA_union_capB (m : ℕ) : capA m ∪ capB m = Set.univ := by
  ext x
  constructor
  · intro _; trivial
  · intro _
    by_cases h : x.1 (Fin.last m) < 1/2
    · exact Or.inr h
    · refine Or.inl ?_
      show -(1/2) < x.1 (Fin.last m)
      have h' : (1/2 : ℝ) ≤ x.1 (Fin.last m) := not_lt.1 h
      linarith

/-! ## 3. Biproducts of chain complexes -/

/-- The homology level form of the biproduct identity `fst ≫ inl + snd ≫ inr = 𝟙`. -/
lemma homologyMap_total (C D : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ) :
    HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k
        ≫ HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k
      + HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k
        ≫ HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) k
    = 𝟙 ((C ⊞ D).homology k) := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_add, biprod.total, HomologicalComplex.homologyMap_id]

/-- The homology of a biproduct of chain complexes vanishes in degree `k` when both factors do. -/
lemma isZero_homology_biprod (C D : ChainComplex (ModuleCat ℤ) ℕ) (k : ℕ)
    (hC : IsZero (C.homology k)) (hD : IsZero (D.homology k)) :
    IsZero ((C ⊞ D).homology k) := by
  rw [IsZero.iff_id_eq_zero, ← homologyMap_total (C := C) (D := D) k]
  rw [show HomologicalComplex.homologyMap (biprod.fst (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_tgt hC _
      , show HomologicalComplex.homologyMap (biprod.inl (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_src hC _
      , show HomologicalComplex.homologyMap (biprod.snd (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_tgt hD _
      , show HomologicalComplex.homologyMap (biprod.inr (X := C) (Y := D)) k = 0 from
        IsZero.eq_zero_of_src hD _]
  simp

/-- The `k`-th homology of the biproduct of the chain complexes of `↥U` and `↥V`, in the shape in
which it appears in the Mayer–Vietoris sequence, vanishes in positive degrees when `U` and `V`
are contractible. -/
lemma isZero_HBiprod {X : TopCat} (U V : Set X) [ContractibleSpace ↥U] [ContractibleSpace ↥V]
    (k : ℕ) (hk : 1 ≤ k) : IsZero (HBiprod U V k) :=
  isZero_homology_biprod _ _ k (homologyContractible k hk) (homologyContractible k hk)

/-! ## 4. The Mayer–Vietoris connecting map in degrees `≥ 1` is an isomorphism -/

/-- **Mayer–Vietoris induction step.**  For an open cover of `X` by two contractible sets, the
connecting map `H_(k+1)(X) ⟶ H_k(U ∩ V)` is an isomorphism for `k ≥ 1`. -/
theorem mvδX_isIso {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) [ContractibleSpace ↥U] [ContractibleSpace ↥V]
    (k : ℕ) (hk : 1 ≤ k) : IsIso (mvδX U V hU hV hcov k) := by
  haveI h1 : IsZero (HBiprod U V (k + 1)) := isZero_HBiprod U V (k + 1) (by omega)
  haveI h0 : IsZero (HBiprod U V k) := isZero_HBiprod U V k hk
  have hm : Mono (mvδ U V k) := by
    have hf : (ShortComplex.mk (HomologicalComplex.homologyMap (mvRight U V) (k + 1))
        (mvδ U V k) (mv_comp_δ U V k)).f = 0 := IsZero.eq_zero_of_src h1 _
    exact (ShortComplex.exact_iff_mono _ hf).1 (mv_H_exact₃ U V k)
  have he : Epi (mvδ U V k) := by
    have hg : (ShortComplex.mk (mvδ U V k)
        (HomologicalComplex.homologyMap (mvLeft U V) k) (mvδ_comp U V k)).g = 0 :=
      IsZero.eq_zero_of_tgt h0 _
    exact (ShortComplex.exact_iff_epi _ hg).1 (mv_H_exact₁ U V k)
  haveI : IsIso (mvδ U V k) := isIso_of_mono_of_epi _
  show IsIso (CategoryTheory.CategoryStruct.comp (smallIso U V hU hV hcov (k + 1)).inv
    (mvδ U V k))
  infer_instance

/-! ## 5. The base case -/

/-- `mvLeft` is a biproduct lift: its first projection is the map on chains induced by
`U ∩ V ↪ U`. -/
lemma mvLeft_fst {X : TopCat} (U V : Set X) :
    mvLeft U V ≫ biprod.fst (X := singularChains ℤ (TopCat.of ↥U))
        (Y := singularChains ℤ (TopCat.of ↥V))
      = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V) := by
  rw [mvLeft, biprod.lift_fst]
  rfl

/-- `mvLeft` is a biproduct lift: its second projection is the map on chains induced by
`U ∩ V ↪ V`. -/
lemma mvLeft_snd {X : TopCat} (U V : Set X) :
    mvLeft U V ≫ biprod.snd (X := singularChains ℤ (TopCat.of ↥U))
        (Y := singularChains ℤ (TopCat.of ↥V))
      = chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V) := by
  rw [mvLeft, biprod.lift_snd]
  rfl

/-- The kernel of the zeroth Mayer–Vietoris map is the intersection of the kernels of its two
components. -/
lemma ker_mvLeft_zero {X : TopCat} (U V : Set X) :
    LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0))
      = LinearMap.ker (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (mvLeft U V) 0
              ≫ HomologicalComplex.homologyMap
                  (biprod.fst (X := singularChains ℤ (TopCat.of ↥U))
                    (Y := singularChains ℤ (TopCat.of ↥V))) 0))
        ⊓ LinearMap.ker (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (mvLeft U V) 0
              ≫ HomologicalComplex.homologyMap
                  (biprod.snd (X := singularChains ℤ (TopCat.of ↥U))
                    (Y := singularChains ℤ (TopCat.of ↥V))) 0)) := by
  set w := HomologicalComplex.homologyMap (mvLeft U V) 0 with hw
  set p := HomologicalComplex.homologyMap
    (biprod.fst (X := singularChains ℤ (TopCat.of ↥U))
      (Y := singularChains ℤ (TopCat.of ↥V))) 0 with hp
  set q := HomologicalComplex.homologyMap
    (biprod.snd (X := singularChains ℤ (TopCat.of ↥U))
      (Y := singularChains ℤ (TopCat.of ↥V))) 0 with hq
  have htot : p ≫ HomologicalComplex.homologyMap
      (biprod.inl (X := singularChains ℤ (TopCat.of ↥U))
        (Y := singularChains ℤ (TopCat.of ↥V))) 0
      + q ≫ HomologicalComplex.homologyMap
        (biprod.inr (X := singularChains ℤ (TopCat.of ↥U))
          (Y := singularChains ℤ (TopCat.of ↥V))) 0 = 𝟙 _ := homologyMap_total _ _ 0
  refine Submodule.ext fun z => ?_
  simp only [Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · intro hz
    constructor
    · show ModuleCat.Hom.hom (w ≫ p) z = 0
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero]
    · show ModuleCat.Hom.hom (w ≫ q) z = 0
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero]
  · rintro ⟨h1, h2⟩
    have h1' : ModuleCat.Hom.hom p (ModuleCat.Hom.hom w z) = 0 := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h1
    have h2' : ModuleCat.Hom.hom q (ModuleCat.Hom.hom w z) = 0 := by
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2
    have h := congrArg (fun (g : _ ⟶ _) => ModuleCat.Hom.hom g (ModuleCat.Hom.hom w z)) htot
    simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
      ModuleCat.hom_id, LinearMap.id_apply] at h
    rw [← h, h1', h2']
    simp

/-- A linear map with an injective right factor: the kernel of `f` is the kernel of `g ∘ f`. -/
lemma ker_eq_ker_comp_of_injective {M N P : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module ℤ M] [Module ℤ N] [Module ℤ P]
    (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) (hg : Function.Injective g) :
    LinearMap.ker f = LinearMap.ker (g.comp f) := by
  ext z
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  exact ⟨fun h => by rw [h, map_zero], fun h => hg (by rw [h, map_zero])⟩

/-- **Base case, first step.**  For an open cover by two contractible sets, the kernel of the
zeroth Mayer–Vietoris map `H_0(U ∩ V) ⟶ H_0(U) ⊞ H_0(V)` is the kernel of the augmentation of
`U ∩ V`. -/
lemma ker_mvLeft_zero_eq_ker_eps {X : TopCat} (U V : Set X) [ContractibleSpace ↥U]
    [ContractibleSpace ↥V] :
    LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0))
      = LinearMap.ker (ModuleCat.Hom.hom
          (TopCat.singularHomology₀ε (TopCat.of ↥(U ∩ V)) (ModuleCat.of ℤ ℤ))) := by
  have hinjU : Function.Injective (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of ↥U) (ModuleCat.of ℤ ℤ))) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hinjV : Function.Injective (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of ↥V) (ModuleCat.of ℤ ℤ))) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hU := eps_comp_homologyMap (inclUVU U V)
  have hV := eps_comp_homologyMap (inclUVV U V)
  have hpfst : (HomologicalComplex.homologyMap (mvLeft U V) 0
        ≫ HomologicalComplex.homologyMap (biprod.fst
            (X := singularChains ℤ (TopCat.of ↥U))
            (Y := singularChains ℤ (TopCat.of ↥V))) 0)
      = HomologicalComplex.homologyMap
          (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥U) (inclUVU U V)) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, mvLeft_fst]
  have hpsnd : (HomologicalComplex.homologyMap (mvLeft U V) 0
        ≫ HomologicalComplex.homologyMap (biprod.snd
            (X := singularChains ℤ (TopCat.of ↥U))
            (Y := singularChains ℤ (TopCat.of ↥V))) 0)
      = HomologicalComplex.homologyMap
          (chainMap ℤ (TopCat.of ↥(U ∩ V)) (TopCat.of ↥V) (inclUVV U V)) 0 := by
    rw [← HomologicalComplex.homologyMap_comp, mvLeft_snd]
  have h1 : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0
        ≫ HomologicalComplex.homologyMap (biprod.fst
            (X := singularChains ℤ (TopCat.of ↥U))
            (Y := singularChains ℤ (TopCat.of ↥V))) 0))
      = LinearMap.ker (ModuleCat.Hom.hom
          (TopCat.singularHomology₀ε (TopCat.of ↥(U ∩ V)) (ModuleCat.of ℤ ℤ))) := by
    rw [hpfst]
    rw [ker_eq_ker_comp_of_injective _ (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of ↥U) (ModuleCat.of ℤ ℤ))) hinjU, hU]
  have h2 : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0
        ≫ HomologicalComplex.homologyMap (biprod.snd
            (X := singularChains ℤ (TopCat.of ↥U))
            (Y := singularChains ℤ (TopCat.of ↥V))) 0))
      = LinearMap.ker (ModuleCat.Hom.hom
          (TopCat.singularHomology₀ε (TopCat.of ↥(U ∩ V)) (ModuleCat.of ℤ ℤ))) := by
    rw [hpsnd]
    rw [ker_eq_ker_comp_of_injective _ (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε (TopCat.of ↥V) (ModuleCat.of ℤ ℤ))) hinjV, hV]
  rw [ker_mvLeft_zero, h1, h2, inf_idem]

/-! ## 6. The base case and the induction -/

/-- **Base case, first step.**  For an open cover by two contractible sets, the first homology of
`X` is the kernel of the zeroth Mayer–Vietoris map. -/
lemma mvδX_zero_iso {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) [ContractibleSpace ↥U] [ContractibleSpace ↥V] :
    Nonempty ((singularChains ℤ X).homology 1
      ≅ kerMod (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0))) := by
  haveI h1 : IsZero (HBiprod U V 1) := isZero_HBiprod U V 1 le_rfl
  have hinj : Function.Injective (ModuleCat.Hom.hom (mvδ U V 0)) := by
    have hf : (ShortComplex.mk (HomologicalComplex.homologyMap (mvRight U V) 1) (mvδ U V 0)
        (mv_comp_δ U V 0)).f = 0 := IsZero.eq_zero_of_src h1 _
    exact (ModuleCat.mono_iff_injective _).1
      ((ShortComplex.exact_iff_mono _ hf).1 (mv_H_exact₃ U V 0))
  have hrange : (ModuleCat.Hom.hom (mvδ U V 0)).range
      = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0)).ker :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (mv_H_exact₁ U V 0)
  have hcod : ∀ x : ↥(HSmall U V 1), ModuleCat.Hom.hom (mvδ U V 0) x
      ∈ LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0)) := by
    intro x
    rw [← hrange]
    exact ⟨x, rfl⟩
  refine ⟨(smallIso U V hU hV hcov 1).symm ≪≫ LinearEquiv.toModuleIso (LinearEquiv.ofBijective
    (f := LinearMap.codRestrict
      (LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0)))
      (ModuleCat.Hom.hom (mvδ U V 0)) hcod) ?_)⟩
  constructor
  · intro x y hxy
    refine hinj ?_
    have h1 : (ModuleCat.Hom.hom (mvδ U V 0)) x = (ModuleCat.Hom.hom (mvδ U V 0)) y :=
      congrArg (fun z : ↥(LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (mvLeft U V) 0))) => z.1) hxy
    simpa only [LinearMap.codRestrict_apply, Subtype.coe_mk] using h1
  · intro y
    have hy : y.1 ∈ (ModuleCat.Hom.hom (mvδ U V 0)).range := by
      rw [hrange]
      exact LinearMap.mem_ker.mp y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    show (⟨(ModuleCat.Hom.hom (mvδ U V 0)) x, hcod x⟩ : ↥(LinearMap.ker
      (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (mvLeft U V) 0)))) = y
    exact Subtype.ext hx

/-! ## 7. The two point structure of `S⁰` -/

/-- **The unit sphere of `ℝ` is the two point space `{±1}`.** -/
lemma mem_sphSet_one_iff (x : EuclideanSpace ℝ (Fin 1)) :
    x ∈ sphSet 1 ↔ x 0 = 1 ∨ x 0 = -1 := by
  show ‖x‖ = 1 ↔ x 0 = 1 ∨ x 0 = -1
  have h : ‖x‖ = |x 0| := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
      Real.sqrt_sq_eq_abs]
  rw [h]
  exact abs_eq (by norm_num)

lemma sphSet_one_eq :
    (sphSet 1 : Set (EuclideanSpace ℝ (Fin 1)))
      = {x : EuclideanSpace ℝ (Fin 1) | x 0 = 1 ∨ x 0 = -1} :=
  Set.ext fun x => mem_sphSet_one_iff x

/-- The north pole `1 ∈ S⁰`. -/
noncomputable def sphOnePointN : ↥(sphSet 1) :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)), by
    rw [mem_sphSet_one_iff]
    exact Or.inl (by simp)⟩

/-- The south pole `-1 ∈ S⁰`. -/
noncomputable def sphOnePointS : ↥(sphSet 1) :=
  ⟨WithLp.toLp 2 (fun _ : Fin 1 => (-1 : ℝ)), by
    rw [mem_sphSet_one_iff]
    exact Or.inr (by simp)⟩

@[simp] lemma sphOnePointN_coe : (sphOnePointN : EuclideanSpace ℝ (Fin 1)) 0 = 1 := by
  simp [sphOnePointN, PiLp.toLp_apply]

@[simp] lemma sphOnePointS_coe : (sphOnePointS : EuclideanSpace ℝ (Fin 1)) 0 = -1 := by
  simp [sphOnePointS, PiLp.toLp_apply]

lemma sphOnePointS_ne_N : sphOnePointS ≠ sphOnePointN := by
  intro hc
  have h := congrArg (fun y : ↥(sphSet 1) => (y : EuclideanSpace ℝ (Fin 1)) 0) hc
  simp only [sphOnePointN_coe, sphOnePointS_coe] at h
  norm_num at h

/-- Every point of `S⁰` is one of the two poles. -/
lemma sphOne_cases (x : ↥(sphSet 1)) : x = sphOnePointN ∨ x = sphOnePointS := by
  have hx : x.1 0 = 1 ∨ x.1 0 = -1 := (mem_sphSet_one_iff x.1).1 x.2
  rcases hx with h | h
  · left
    apply Subtype.ext
    ext i
    fin_cases i
    simpa using h
  · right
    apply Subtype.ext
    ext i
    fin_cases i
    simpa using h

/-- `S⁰` is a finite set. -/
lemma sphSet_one_finite : (sphSet 1 : Set (EuclideanSpace ℝ (Fin 1))).Finite := by
  have hfin : ({(sphOnePointN : EuclideanSpace ℝ (Fin 1)),
      (sphOnePointS : EuclideanSpace ℝ (Fin 1))} : Set (EuclideanSpace ℝ (Fin 1))).Finite :=
    Set.Finite.insert _ (Set.finite_singleton _)
  refine hfin.subset ?_
  intro x hx
  rcases sphOne_cases ⟨x, hx⟩ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

/-- `S⁰` is a discrete space. -/
lemma discreteTopology_sphSet_one : DiscreteTopology ↥(sphSet 1) := by
  rw [← isDiscrete_iff_discreteTopology]
  exact sphSet_one_finite.isDiscrete

/-- **`S⁰` is the two point space `Bool`.** -/
noncomputable def sphOneEquivBool : ↥(sphSet 1) ≃ Bool where
  toFun x := decide (x = sphOnePointN)
  invFun b := if b then sphOnePointN else sphOnePointS
  left_inv x := by
    rcases sphOne_cases x with h | h
    · subst h; simp
    · subst h; simp [sphOnePointS_ne_N]
  right_inv b := by
    cases b with
    | true => simp
    | false => simp [sphOnePointS_ne_N]

/-- **Base case**: `H_1(S^2) ≅ ℤ`. -/
lemma sphereHomology_one :
    Nonempty ((singularChains ℤ (sphTop 2)).homology 1 ≅ ModuleCat.of ℤ ℤ) := by
  haveI hA : ContractibleSpace ↥(capA 1) := contractibleSpace_capA 1
  haveI hB : ContractibleSpace ↥(capB 1) := contractibleSpace_capB 1
  haveI hD : DiscreteTopology ↥(sphSet 1) := discreteTopology_sphSet_one
  have hker : LinearMap.ker (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (mvLeft (capA 1) (capB 1)) 0))
      = LinearMap.ker (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
          (TopCat.of ↥((capA 1) ∩ (capB 1))) (ModuleCat.of ℤ ℤ))) :=
    ker_mvLeft_zero_eq_ker_eps (capA 1) (capB 1)
  obtain ⟨e1⟩ := mvδX_zero_iso (capA 1) (capB 1) (isOpen_capA 1) (isOpen_capB 1)
    (capA_union_capB 1)
  have e2 : kerMod (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (mvLeft (capA 1) (capB 1)) 0))
      ≅ kerMod (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
          (TopCat.of ↥((capA 1) ∩ (capB 1))) (ModuleCat.of ℤ ℤ))) :=
    LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ hker)
  obtain ⟨e3⟩ := ker_eps_homotopyEquiv (bandHomotopyEquiv 1 le_rfl).some
  obtain ⟨e4⟩ := reducedH0OfTwoPoints ↥(sphSet 1) sphOneEquivBool
  exact ⟨e1 ≪≫ e2 ≪≫ e3 ≪≫ e4⟩

/-- **The main computation**: the `n`-th singular homology of `S^(n+1)` is `ℤ`, for `n ≥ 1`. -/
theorem sphereHomology_aux (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((singularChains ℤ (sphTop (n+1))).homology n ≅ ModuleCat.of ℤ ℤ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_lt_of_le hn with h1 | h2
    · subst h1
      exact sphereHomology_one
    · haveI hA : ContractibleSpace ↥(capA n) := contractibleSpace_capA n
      haveI hB : ContractibleSpace ↥(capB n) := contractibleSpace_capB n
      have hk : 1 ≤ n - 1 := by omega
      haveI hiso : IsIso (mvδX (capA n) (capB n) (isOpen_capA n) (isOpen_capB n)
          (capA_union_capB n) (n - 1)) :=
        mvδX_isIso (capA n) (capB n) (isOpen_capA n) (isOpen_capB n) (capA_union_capB n)
          (n - 1) hk
      have e1 : ((singularChains ℤ (sphTop (n+1))).homology ((n - 1) + 1))
          ≅ (singularChains ℤ (TopCat.of ↥(capA n ∩ capB n))).homology (n - 1) :=
        CategoryTheory.asIso (mvδX (capA n) (capB n) (isOpen_capA n) (isOpen_capB n)
          (capA_union_capB n) (n - 1))
      rw [Nat.sub_add_cancel hn] at e1
      obtain ⟨e2⟩ := homologyIso_of_homotopyEquiv (bandHomotopyEquiv n (by omega)).some (n - 1)
      obtain ⟨e3⟩ := ih (n - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel hn] at e3
      exact ⟨e1 ≪≫ e2 ≪≫ e3⟩

/-- **`H_n(S^n) ≅ ℤ`** for `n ≥ 1`. -/
theorem sphereHomologyTop (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology n ≅
        ModuleCat.of ℤ ℤ) := by
  obtain ⟨e'⟩ := sphereHomology_aux n hn
  obtain ⟨e''⟩ := homologyIso_of_homotopyEquiv
    (Homeomorph.setCongr (sphereSet_eq (n + 1))).toHomotopyEquiv n
  exact ⟨e'' ≪≫ e'⟩

end

end Work.Cohomology
