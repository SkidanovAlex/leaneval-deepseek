import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Submission.Work.CohomologicalShrinking.Shrinking
import Submission.Work.SSGRoute.augmentation_eq_sum
import Submission.Work.SSGRoute.exists_finite_stable_submodule_family
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.Tate.Equivs
import Submission.Work.Tate.coind_augmentation_eq_ker_norm
import Submission.Work.Tate.coind_norm_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option warn.classDefReducibility false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute

open scoped TensorProduct

/-! ## Instances on a `G`-stable submodule -/

noncomputable def stableSubDistribMulAction {G : Type} [Group G] {R : Type} [Semiring R] {M : Type}
    [AddCommMonoid M] [Module R M] [DistribMulAction G M] (W : Submodule R M)
    (h : ∀ (γ : G) (w : M), w ∈ W → γ • w ∈ W) : DistribMulAction G ↥W where
  smul γ w := ⟨γ • (w : M), h γ w w.2⟩
  one_smul w := Subtype.ext (one_smul G (w : M))
  mul_smul γ δ w := Subtype.ext (mul_smul γ δ (w : M))
  smul_zero γ := Subtype.ext (smul_zero γ)
  smul_add γ x y := Subtype.ext (smul_add γ (x : M) (y : M))

theorem stableSubSMulCommClass {G : Type} [Group G] {R : Type} [Semiring R] {M : Type}
    [AddCommMonoid M] [Module R M] [DistribMulAction G M] [SMulCommClass G R M] (W : Submodule R M)
    (h : ∀ (γ : G) (w : M), w ∈ W → γ • w ∈ W) :
    @SMulCommClass G R ↥W (stableSubDistribMulAction (G := G) W h).toSMul _ := by
  letI : SMul G ↥W := (stableSubDistribMulAction (G := G) W h).toSMul
  refine ⟨fun γ r w => ?_⟩
  exact Subtype.ext (smul_comm γ r (w : M))

theorem hm2_rTensor_subtype_injective {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    [Module (ZMod p) M] {T : Type} [AddCommGroup T] [Module (ZMod p) T]
    (W : Submodule (ZMod p) M) : Function.Injective (W.subtype.rTensor T) := by
  haveI : Module.Flat (ZMod p) T := Module.Flat.of_free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := T) W.subtype W.subtype_injective

/-! ## Evaluation lemmas at the level of `coindUp` -/

/-- Value of a `mapKer` element on the twisted modules, as a function. -/
theorem mapKer_coe_apply {G : Type} [Group G] [Fintype G] {M₁ M₂ : Type} [AddCommGroup M₁]
    [AddCommGroup M₂] [DistribMulAction G M₁] [DistribMulAction G M₂]
    (f : ↥(Work.Tate.coindUp G M₁) →+ ↥(Work.Tate.coindUp G M₂))
    (hf : ∀ (γ : G) (a : ↥(Work.Tate.coindUp G M₁)), f (γ • a) = γ • f a)
    (a : ↥(Work.Tate.norm G ↥(Work.Tate.coindUp G M₁)).ker) (s : G) :
    ((↑(Work.Tate.mapKer G ↥(Work.Tate.coindUp G M₁) ↥(Work.Tate.coindUp G M₂) f hf a) :
        ↥(Work.Tate.coindUp G M₂)) : G → M₂) s
      = (f (↑a : ↥(Work.Tate.coindUp G M₁)) : G → M₂) s := by
  rw [Work.Tate.mapKer_apply]

/-- Value of a sum of augmentation generators in a `coindUp`. -/
theorem coe_augSum_apply {G : Type} [Group G] [Fintype G] {M : Type} [AddCommGroup M]
    [DistribMulAction G M] {ι : Type} [Fintype ι]
    (γ : ι → G) (z : ι → ↥(Work.Tate.coindUp G M)) (s : G) :
    ((∑ i, (γ i • z i - z i) : ↥(Work.Tate.coindUp G M)) : G → M) s
      = ∑ i, ((z i : G → M) (s * γ i) - (z i : G → M) s) := by
  simp only [AddSubgroup.val_finsetSum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by
    simp only [AddSubgroupClass.coe_sub, Work.Tate.coe_smul_coindUp, Pi.sub_apply,
      Submission.coind_smul_apply])

/-- **Reduction of the target of `Hm2Map` to a finite coefficient module.**

Let `G` be a finite group, `p` a prime, `E` a finite `𝔽_p[G]`-module, `T` any `𝔽_p[G]`-module,
`E₂` any `𝔽_p[G]`-module and `f : E → E₂` a `G`-equivariant `𝔽_p`-linear map.  If a class
`x ∈ Ĥ⁻²(G, E ⊗ T)` dies under `Hm2Map (f ⊗ id)`, then it dies already under `Hm2Map (g ⊗ id)`
for a factorization `f = j ∘ g` of `f` through a *finite* `𝔽_p[G]`-module `W`.

Mathematically: `Ĥ⁻²(G, M) = ker(N)/I_G·M`, so the vanishing of the class of an explicit function
`u : G → E₂⊗T` is witnessed by a finite sum `∑ (γ • z_γ - z_γ)` with `z_γ : G → E₂⊗T`; since `G`
is finite all these functions have finitely many values, which span a finite `G`-stable submodule of
`E₂⊗T`; a finite submodule of `E₂⊗T` is contained in `W₀ ⊗ T` for some finite `G`-stable
`W₀ ⊆ E₂`, and one may enlarge `W₀` so that it contains `f(E)`.  (Enlarging `W` is essential; the
naive statement `I_G Ē₂ ∩ Ē_W = I_G Ē_W` is false for non-split submodules.) -/

theorem hm2Map_finite_factor (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction G E]
    [SMulCommClass G (ZMod p) E] [Finite E]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction G E₂]
    [SMulCommClass G (ZMod p) E₂]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T]
    (f : E →ₗ[ZMod p] E₂) (hf : ∀ (γ : G) (e : E), f (γ • e) = γ • f e)
    (x : Work.Tate.Hm2 G (E ⊗[ZMod p] T))
    (hx : Work.Tate.Hm2Map (f.rTensor T).toAddMonoidHom
        (fun γ z => Work.CohomologicalShrinking.rTensor_equiv p f hf γ z) x = 0) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod p) W) (_ : DistribMulAction G W)
      (_ : SMulCommClass G (ZMod p) W) (_ : Finite W)
      (j : W →ₗ[ZMod p] E₂) (_ : ∀ (γ : G) (w : W), j (γ • w) = γ • j w) (_ : Function.Injective j)
      (g : E →ₗ[ZMod p] W) (hg : ∀ (γ : G) (e : E), g (γ • e) = γ • g e)
      (_ : ∀ e, j (g e) = f e),
      Work.Tate.Hm2Map (g.rTensor T).toAddMonoidHom
        (fun γ z => Work.CohomologicalShrinking.rTensor_equiv p g hg γ z) x = 0 := by
  classical
  have hfe : ∀ (γ : G) (z : E ⊗[ZMod p] T),
      (f.rTensor T).toAddMonoidHom (γ • z) = γ • (f.rTensor T).toAddMonoidHom z :=
    fun γ z => Work.CohomologicalShrinking.rTensor_equiv p f hf γ z
  obtain ⟨a, ha⟩ := Work.Tate.Hm1π_surjective (G := G)
    (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T))) x
  have hx' : Work.Tate.Hm1π (G := G) (A := ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)))
      (Work.Tate.mapKer (G := G)
        (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
        (B := ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)))
        (Work.Tate.coindUpMap (f.rTensor T).toAddMonoidHom hfe)
        (Work.Tate.coindUpMap_equiv (f.rTensor T).toAddMonoidHom hfe) a) = 0 := by
    rw [← Work.Tate.Hm1Map_Hm1π]
    have h := hx
    simp only [Work.Tate.Hm2Map] at h
    rw [ha]
    exact h
  have hu : ((Work.Tate.mapKer (G := G)
        (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
        (B := ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)))
        (Work.Tate.coindUpMap (f.rTensor T).toAddMonoidHom hfe)
        (Work.Tate.coindUpMap_equiv (f.rTensor T).toAddMonoidHom hfe) a :
        ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T))))
      ∈ Work.Tate.augmentation G ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)) :=
    (Work.Tate.Hm1π_eq_zero_iff (G := G) (A := ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)))
      (Work.Tate.mapKer (G := G)
        (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
        (B := ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)))
        (Work.Tate.coindUpMap (f.rTensor T).toAddMonoidHom hfe)
        (Work.Tate.coindUpMap_equiv (f.rTensor T).toAddMonoidHom hfe) a)).mp hx'
  obtain ⟨ι, hι, γ, z, hz⟩ := augmentation_eq_sum (p := p) (G := G)
    (A := ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T))) hu
  letI : Fintype ι := hι
  obtain ⟨W, hSW, hWstab, hWfin, m', hm'⟩ :=
    exists_finite_stable_submodule_family (p := p) (G := G) (M := E₂) (T := T)
      (S := Set.range f) (Set.finite_range f)
      (fun q : ι × G => ((z q.1 : G → E₂ ⊗[ZMod p] T) q.2))
  letI : DistribMulAction G ↥W := stableSubDistribMulAction W hWstab
  letI : SMulCommClass G (ZMod p) ↥W := stableSubSMulCommClass W hWstab
  let yf : ι → G → ↥W ⊗[ZMod p] T := fun i s => m' (i, s)
  have hlift : ∀ (i : ι) (s : G), (W.subtype.rTensor T) (yf i s) = ((z i : G → E₂ ⊗[ZMod p] T) s) :=
    fun i s => hm' (i, s)
  have hyf_mem : ∀ i, yf i ∈ Work.Tate.coindUp G (↥W ⊗[ZMod p] T) := by
    intro i
    rw [Work.Tate.mem_coindUp_iff]
    apply hm2_rTensor_subtype_injective (p := p) (T := T) W
    change (W.subtype.rTensor T).toAddMonoidHom (∑ s : G, s⁻¹ • yf i s)
      = (W.subtype.rTensor T).toAddMonoidHom 0
    rw [Work.Tate.map_sum_univ, map_zero]
    refine Eq.trans (Finset.sum_congr rfl (fun s _ => ?_)) (Work.Tate.mem_coindUp_iff.mp (z i).2)
    show (W.subtype.rTensor T) (s⁻¹ • yf i s) = s⁻¹ • ((z i : G → E₂ ⊗[ZMod p] T) s)
    rw [Work.CohomologicalShrinking.rTensor_equiv p W.subtype (fun γ w => rfl) s⁻¹ (yf i s),
      hlift i s]
  let yy : ι → ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)) := fun i => ⟨yf i, hyf_mem i⟩
  have hv : (∑ i, (γ i • yy i - yy i))
      ∈ Work.Tate.augmentation G ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)) := by
    refine AddSubgroup.sum_mem _ (fun i _ => ?_)
    exact Work.Tate.smul_sub_self_mem_augmentation (γ i) (yy i)
  let g : E →ₗ[ZMod p] ↥W := f.codRestrict W (fun e => hSW ⟨e, rfl⟩)
  have hcomp2 : W.subtype ∘ₗ g = f :=
    LinearMap.subtype_comp_codRestrict f W (fun e => hSW ⟨e, rfl⟩)
  have hg : ∀ (γ : G) (e : E), g (γ • e) = γ • g e := by
    intro γ e
    apply Subtype.ext
    show f (γ • e) = γ • ((g e : ↥W) : E₂)
    rw [hf γ e]
    rfl
  have hge : ∀ (γ : G) (z : E ⊗[ZMod p] T),
      (g.rTensor T).toAddMonoidHom (γ • z) = γ • (g.rTensor T).toAddMonoidHom z :=
    fun γ z => Work.CohomologicalShrinking.rTensor_equiv p g hg γ z
  have hz_eval : ∀ s : G,
      ((Work.Tate.mapKer (G := G)
          (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
          (B := ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)))
          (Work.Tate.coindUpMap (f.rTensor T).toAddMonoidHom hfe)
          (Work.Tate.coindUpMap_equiv (f.rTensor T).toAddMonoidHom hfe) a :
          ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T))) : G → E₂ ⊗[ZMod p] T) s
        = ∑ i, ((z i : G → E₂ ⊗[ZMod p] T) (s * γ i) - (z i : G → E₂ ⊗[ZMod p] T) s) := by
    intro s
    have h1 := congrArg (fun w : ↥(Work.Tate.coindUp G (E₂ ⊗[ZMod p] T)) =>
      (w : G → E₂ ⊗[ZMod p] T) s) hz
    rw [h1, coe_augSum_apply γ z s]
  have hkey : ((Work.Tate.mapKer (G := G)
        (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
        (B := ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)))
        (Work.Tate.coindUpMap (g.rTensor T).toAddMonoidHom hge)
        (Work.Tate.coindUpMap_equiv (g.rTensor T).toAddMonoidHom hge) a :
        ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T))))
      = ∑ i, (γ i • yy i - yy i) := by
    apply Subtype.ext
    funext s
    apply hm2_rTensor_subtype_injective (p := p) (T := T) W
    have hA : (W.subtype.rTensor T)
        (((Work.Tate.mapKer (G := G)
          (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
          (B := ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)))
          (Work.Tate.coindUpMap (g.rTensor T).toAddMonoidHom hge)
          (Work.Tate.coindUpMap_equiv (g.rTensor T).toAddMonoidHom hge) a :
          ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T))) : G → ↥W ⊗[ZMod p] T) s)
        = ∑ i, ((z i : G → E₂ ⊗[ZMod p] T) (s * γ i) - (z i : G → E₂ ⊗[ZMod p] T) s) := by
      rw [mapKer_coe_apply (f := Work.Tate.coindUpMap (g.rTensor T).toAddMonoidHom hge)
        (hf := Work.Tate.coindUpMap_equiv (g.rTensor T).toAddMonoidHom hge)
        (a := a) (s := s), Work.Tate.coindUpMap_apply]
      change (W.subtype.rTensor T) ((g.rTensor T) (((a : ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T))) :
          G → E ⊗[ZMod p] T) s))
        = ∑ i, ((z i : G → E₂ ⊗[ZMod p] T) (s * γ i) - (z i : G → E₂ ⊗[ZMod p] T) s)
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hcomp2]
      exact hz_eval s
    have hB : (W.subtype.rTensor T)
        (((∑ i, (γ i • yy i - yy i) : ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T))) :
          G → ↥W ⊗[ZMod p] T) s)
        = ∑ i, ((z i : G → E₂ ⊗[ZMod p] T) (s * γ i) - (z i : G → E₂ ⊗[ZMod p] T) s) := by
      rw [coe_augSum_apply]
      change (W.subtype.rTensor T).toAddMonoidHom
          (∑ i, ((yy i : G → ↥W ⊗[ZMod p] T) (s * γ i) - (yy i : G → ↥W ⊗[ZMod p] T) s))
        = ∑ i, ((z i : G → E₂ ⊗[ZMod p] T) (s * γ i) - (z i : G → E₂ ⊗[ZMod p] T) s)
      rw [Work.Tate.map_sum_univ]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_sub]
      rw [show (W.subtype.rTensor T).toAddMonoidHom ((yy i : G → ↥W ⊗[ZMod p] T) (s * γ i))
          = ((z i : G → E₂ ⊗[ZMod p] T) (s * γ i)) from hlift i (s * γ i)]
      rw [show (W.subtype.rTensor T).toAddMonoidHom ((yy i : G → ↥W ⊗[ZMod p] T) s)
          = ((z i : G → E₂ ⊗[ZMod p] T) s) from hlift i s]
    rw [hA, hB]
  have hgoal : ((Work.Tate.mapKer (G := G)
        (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
        (B := ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)))
        (Work.Tate.coindUpMap (g.rTensor T).toAddMonoidHom hge)
        (Work.Tate.coindUpMap_equiv (g.rTensor T).toAddMonoidHom hge) a :
        ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T))))
      ∈ Work.Tate.augmentation G ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)) := by
    rw [hkey]
    exact hv
  refine ⟨↥W, inferInstance, inferInstance, stableSubDistribMulAction W hWstab,
    stableSubSMulCommClass W hWstab, hWfin, W.subtype, (fun γ w => rfl), W.subtype_injective,
    g, hg, (fun e => rfl), ?_⟩
  rw [← ha]
  simp only [Work.Tate.Hm2Map]
  rw [Work.Tate.Hm1Map_Hm1π]
  exact (Work.Tate.Hm1π_eq_zero_iff (G := G) (A := ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)))
    (Work.Tate.mapKer (G := G)
      (A := ↥(Work.Tate.coindUp G (E ⊗[ZMod p] T)))
      (B := ↥(Work.Tate.coindUp G (↥W ⊗[ZMod p] T)))
      (Work.Tate.coindUpMap (g.rTensor T).toAddMonoidHom hge)
      (Work.Tate.coindUpMap_equiv (g.rTensor T).toAddMonoidHom hge) a)).mpr hgoal

end Work.SSGRoute
