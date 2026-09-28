import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.pd_mvdelta_apply
import Submission.Work.Cohomology.pd_hatcher_decomp

/-!
# The boundary of a small cycle which is a boundary

Let `X` be a topological space, `U V ⊆ X` an open cover and `m : ℕ`.  Suppose `z ∈ C_{m+1}(X)` is
a boundary and decomposes as `z = zU + zV` with `zU` supported in `U` and `zV` supported in `V`.
Then `∂zU` is a boundary of a chain supported in `U ∩ V`.

This is the chain-level incarnation of the fact that the connecting homomorphism of the
Mayer–Vietoris sequence of the cover `{U, V}` kills the boundaries: the small chain
`ζ = i_U(zU) + i_V(zV)` is a cycle whose image under `smallToSing` is `z = ∂β`, so by the
injectivity half of the small-simplices theorem (`exists_d_eq_of_smallToSing_eq`) `ζ` itself is a
boundary *in the small chain complex*; comparing this boundary with the explicit lift
`(zU, -zV)` of `ζ` in `C_*(U) ⊞ C_*(V)` and using exactness of the Mayer–Vietoris sequence in the
middle produces a chain `c` in `C_{m+1}(U ∩ V)` with `∂c = ∂zU`.

## Main result

* `mv_boundary_d_of_small_cycle` — the statement above.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat} {U V : Set X}

/-- Naturality of a chain map, evaluated on an element. -/
private lemma hom_comm_apply {K L : ChainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L)
    (p q : ℕ) (x : K.X p) : L.d p q ((φ.f p) x) = (φ.f q) (K.d p q x) := by
  have h := congrArg (fun (g : K.X p ⟶ L.X q) => (ModuleCat.Hom.hom g) x)
    (HomologicalComplex.Hom.comm φ p q)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- Elementwise form of the first projection of a biproduct of chain complexes, on the first
inclusion. -/
private lemma biprod_fst_inl_apply' {K L : ChainComplex (ModuleCat ℤ) ℕ} (i : ℕ) (a : K.X i) :
    (biprod.fst : K ⊞ L ⟶ K).f i ((biprod.inl : K ⟶ K ⊞ L).f i a) = a := by
  have h := congrArg (fun (g : K.X i ⟶ K.X i) => (ModuleCat.Hom.hom g) a)
    (HomologicalComplex.biprod_inl_fst_f K L i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    using h

/-- Elementwise form of the first projection of a biproduct of chain complexes, on the second
inclusion. -/
private lemma biprod_fst_inr_apply' {K L : ChainComplex (ModuleCat ℤ) ℕ} (i : ℕ) (b : L.X i) :
    (biprod.fst : K ⊞ L ⟶ K).f i ((biprod.inr : L ⟶ K ⊞ L).f i b) = 0 := by
  have h := congrArg (fun (g : L.X i ⟶ K.X i) => (ModuleCat.Hom.hom g) b)
    (HomologicalComplex.biprod_inr_fst_f K L i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    using h

/-- The chain map `C_*(U) ⟶ C^{U,V}_*(X)` followed by the inclusion of the small chains is the
inclusion `inclChains X U`, evaluated on an element. -/
private lemma smallToSing_smallOfU_apply (U V : Set X) (n : ℕ)
    (x : (singularChains ℤ (TopCat.of U)).X n) :
    (smallToSing U V).f n ((smallOfU U V).f n x) = (inclChains X U).f n x := by
  have hcomp : (smallOfU U V).f n ≫ (smallToSing U V).f n = (inclChains X U).f n := by
    rw [← HomologicalComplex.comp_f, smallOfU_comp_smallToSing]
  have h := congrArg (fun (φ : (singularChains ℤ (TopCat.of U)).X n ⟶ (singularChains ℤ X).X n) =>
      (ModuleCat.Hom.hom φ) x) hcomp
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The analogue of `smallToSing_smallOfU_apply` for `V`. -/
private lemma smallToSing_smallOfV_apply (U V : Set X) (n : ℕ)
    (x : (singularChains ℤ (TopCat.of V)).X n) :
    (smallToSing U V).f n ((smallOfV U V).f n x) = (inclChains X V).f n x := by
  have hcomp : (smallOfV U V).f n ≫ (smallToSing U V).f n = (inclChains X V).f n := by
    rw [← HomologicalComplex.comp_f, smallOfV_comp_smallToSing]
  have h := congrArg (fun (φ : (singularChains ℤ (TopCat.of V)).X n ⟶ (singularChains ℤ X).X n) =>
      (ModuleCat.Hom.hom φ) x) hcomp
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h

/-- The inclusion `C_*(A) ⟶ C_*(X)` factors through `C_*(B) ⟶ C_*(X)` when `A ⊆ B`,
evaluated on an element. -/
private lemma inclChainsSub_factor (A B : Set X) (h : A ⊆ B) (n : ℕ)
    (x : (singularChains ℤ (TopCat.of A)).X n) :
    (inclChains X A).f n x = (inclChains X B).f n ((inclChainsSub X A B h).f n x) := by
  have hcontra : (inclChainsSub X A B h).f n ≫ (inclChains X B).f n = (inclChains X A).f n := by
    rw [← HomologicalComplex.comp_f, inclChainsSub_comp]
  have h' := congrArg (fun (g : (singularChains ℤ (TopCat.of A)).X n ⟶ (singularChains ℤ X).X n) =>
      (ModuleCat.Hom.hom g) x) hcontra
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h'.symm

/-- Degreewise surjectivity of the second Mayer–Vietoris map, from degreewise short exactness. -/
private lemma mvRight_surj (U V : Set X) (n : ℕ) :
    Function.Surjective (ModuleCat.Hom.hom ((mvRight U V).f n)) := by
  have hS : ((mvShort U V).map (HomologicalComplex.eval (ModuleCat ℤ)
      (ComplexShape.down ℕ) n)).ShortExact := mv_degreewise U V n
  haveI : Epi ((mvRight U V).f n) := hS.epi_g
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- Degreewise exactness of the Mayer–Vietoris sequence in the middle: an element of
`C_*(U) ⊞ C_*(V)` killed by `mvRight` lies in the image of `mvLeft`. -/
private lemma mvLeft_exact (U V : Set X) (n : ℕ)
    (x : (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).X n)
    (hx : (mvRight U V).f n x = 0) :
    ∃ y, (mvLeft U V).f n y = x := by
  have hS : ((mvShort U V).map (HomologicalComplex.eval (ModuleCat ℤ)
      (ComplexShape.down ℕ) n)).ShortExact := mv_degreewise U V n
  have hex : ((mvShort U V).map (HomologicalComplex.eval (ModuleCat ℤ)
      (ComplexShape.down ℕ) n)).Exact := hS.exact
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  rw [show (ModuleCat.Hom.hom ((mvShort U V).map (HomologicalComplex.eval (ModuleCat ℤ)
        (ComplexShape.down ℕ) n)).f) = ModuleCat.Hom.hom ((mvLeft U V).f n) from rfl] at hex
  rw [show (ModuleCat.Hom.hom ((mvShort U V).map (HomologicalComplex.eval (ModuleCat ℤ)
        (ComplexShape.down ℕ) n)).g) = ModuleCat.Hom.hom ((mvRight U V).f n) from rfl] at hex
  have hxker : x ∈ LinearMap.ker (ModuleCat.Hom.hom ((mvRight U V).f n)) := by
    rw [LinearMap.mem_ker]; exact hx
  have hxrange : x ∈ LinearMap.range (ModuleCat.Hom.hom ((mvLeft U V).f n)) := hex.symm ▸ hxker
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hxrange
  exact ⟨y, hy⟩

theorem mv_boundary_d_of_small_cycle {X : TopCat} {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) {m : ℕ} (z zU zV : (Work.Cohomology.singularChains ℤ X).X (m + 1)) (hzU : zU ∈ LinearMap.range (((Work.Cohomology.inclChains X U).f (m + 1)).hom)) (hzV : zV ∈ LinearMap.range (((Work.Cohomology.inclChains X V).f (m + 1)).hom)) (hz : zU + zV = z) (hbd : ∃ β : (Work.Cohomology.singularChains ℤ X).X (m + 2), (Work.Cohomology.singularChains ℤ X).d (m + 2) (m + 1) β = z) : ∃ c ∈ LinearMap.range (((Work.Cohomology.inclChains X (U ∩ V)).f (m + 1)).hom), (Work.Cohomology.singularChains ℤ X).d (m + 1) m c = (Work.Cohomology.singularChains ℤ X).d (m + 1) m zU := by
  classical
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hzU
  obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hzV
  obtain ⟨β, hβ⟩ := hbd
  set ζ : (smallChains U V).X (m + 1) :=
    (smallOfU U V).f (m + 1) a + (smallOfV U V).f (m + 1) b with hζdef
  have hζ : (smallToSing U V).f (m + 1) ζ = z := by
    rw [hζdef, map_add, smallToSing_smallOfU_apply, smallToSing_smallOfV_apply]
    rw [show (inclChains X U).f (m+1) a = zU from ha,
        show (inclChains X V).f (m+1) b = zV from hb]
    exact hz
  have hdd : (singularChains ℤ X).d (m + 1) m
      ((singularChains ℤ X).d (m + 2) (m + 1) β) = 0 := by
    have h := congrArg (fun (g : (singularChains ℤ X).X (m + 2) ⟶ (singularChains ℤ X).X m) =>
      (ModuleCat.Hom.hom g) β)
      (HomologicalComplex.d_comp_d (singularChains ℤ X) (m + 2) (m + 1) m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hζcycle : (smallChains U V).d (m + 1) m ζ = 0 := by
    apply smallToSing_f_injective U V m
    rw [map_zero, ← hom_comm_apply (smallToSing U V) (m + 1) m, hζ, ← hβ]
    exact hdd
  obtain ⟨γ, hγ⟩ := exists_d_eq_of_smallToSing_eq U V hU hV hcov (m + 1) hζcycle (a := β)
    (by rw [hζ, hβ])
  obtain ⟨z₂, hz₂⟩ := mvRight_surj (X := X) U V (m + 2) γ
  let z₂' : (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).X (m + 1) :=
    (biprod.inl : singularChains ℤ (TopCat.of U) ⟶ singularChains ℤ (TopCat.of U) ⊞
      singularChains ℤ (TopCat.of V)).f (m + 1) a
      + (biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f (m + 1) (-b)
  have hz₂'mvR : (mvRight U V).f (m + 1) z₂' = ζ := by
    show (mvRight U V).f (m+1) ((biprod.inl : singularChains ℤ (TopCat.of U) ⟶
        singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f (m + 1) a
      + (biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f (m + 1) (-b)) = ζ
    rw [map_add, mvRight_inl_eval, mvRight_inr_eval, hζdef]
    simp only [map_neg, neg_neg]
    rfl
  have hz₂'fst : (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
      singularChains ℤ (TopCat.of U)).f (m+1) z₂' = a := by
    show (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f (m+1) ((biprod.inl : singularChains ℤ (TopCat.of U) ⟶
        singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f (m + 1) a
      + (biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f (m + 1) (-b)) = a
    rw [map_add, biprod_fst_inl_apply', biprod_fst_inr_apply', add_zero]
  have h2 : (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).d (m + 1) m
      ((singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).d (m + 2)
        (m + 1) z₂) = 0 := by
    have h := congrArg (fun (g : (singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).X (m + 2) ⟶
        (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).X m) =>
      (ModuleCat.Hom.hom g) z₂)
      (HomologicalComplex.d_comp_d (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V))
        (m + 2) (m + 1) m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hker : (mvRight U V).f (m + 1)
      ((singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).d (m + 2)
        (m + 1) z₂ - z₂') = 0 := by
    rw [map_sub, ← hom_comm_apply (mvRight U V) (m+2) (m+1), hz₂, hγ, hz₂'mvR, sub_self]
  obtain ⟨w, hw⟩ := mvLeft_exact (X := X) U V (m + 1) _ hker
  have h1 : (mvLeft U V).f m ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m w)
      = - (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).d (m + 1) m z₂' := by
    rw [← hom_comm_apply (mvLeft U V) (m+1) m, hw, map_sub, h2, zero_sub]
  have hkey : (inclChainsSub X (U ∩ V) U (fun x hx => hx.1)).f m
      ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m w)
      = -((singularChains ℤ (TopCat.of U)).d (m + 1) m a) := by
    have hL : (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f m
        ((mvLeft U V).f m ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m w))
        = (inclChainsSub X (U ∩ V) U (fun x hx => hx.1)).f m
          ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m w) := by
      rw [mvLeft_eval_fst]; rfl
    have hR : (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f m
        (- (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).d (m + 1) m z₂')
        = -((singularChains ℤ (TopCat.of U)).d (m + 1) m a) := by
      rw [map_neg, ← hom_comm_apply (biprod.fst : singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U)) (m+1) m, hz₂'fst]
    calc (inclChainsSub X (U ∩ V) U (fun x hx => hx.1)).f m
          ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m w)
        = (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of U)).f m
            ((mvLeft U V).f m ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m w)) := hL.symm
      _ = (biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of U)).f m
            (- (singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).d (m + 1) m z₂') :=
          by rw [h1]
      _ = -((singularChains ℤ (TopCat.of U)).d (m + 1) m a) := hR
  have hkey' : (inclChainsSub X (U ∩ V) U (fun x hx => hx.1)).f m
      ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m (-w))
      = (singularChains ℤ (TopCat.of U)).d (m + 1) m a := by
    rw [map_neg, map_neg, hkey, neg_neg]
  refine ⟨(inclChains X (U ∩ V)).f (m + 1) (-w), ⟨-w, rfl⟩, ?_⟩
  calc (singularChains ℤ X).d (m + 1) m ((inclChains X (U ∩ V)).f (m + 1) (-w))
      = (inclChains X (U ∩ V)).f m ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m (-w)) :=
        hom_comm_apply (inclChains X (U ∩ V)) (m+1) m (-w)
    _ = (inclChains X U).f m ((inclChainsSub X (U ∩ V) U (fun x hx => hx.1)).f m
          ((singularChains ℤ (TopCat.of ↥(U ∩ V))).d (m + 1) m (-w))) :=
        inclChainsSub_factor (U ∩ V) U (fun x hx => hx.1) m _
    _ = (inclChains X U).f m ((singularChains ℤ (TopCat.of U)).d (m + 1) m a) := by rw [hkey']
    _ = (singularChains ℤ X).d (m + 1) m ((inclChains X U).f (m + 1) a) :=
        (hom_comm_apply (inclChains X U) (m+1) m a).symm
    _ = (singularChains ℤ X).d (m + 1) m zU := by
        rw [show (inclChains X U).f (m+1) a = zU from ha]

end

end Work.Cohomology
