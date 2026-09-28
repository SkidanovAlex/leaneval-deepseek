import Mathlib
import Submission.Work.Cohomology.Singular

/-!
# Vanishing of the singular cohomology of a totally disconnected space

If `X` is totally disconnected, every singular `n`-simplex of `X` with `n ≥ 1` is constant
(the standard simplex is connected), so the singular chain complex of `X` is the "alternating
constant" complex `R[X] ←0- R[X] ←𝟙- R[X] ←0- ⋯`.  Mathlib already provides the isomorphism
`AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace`, and we use it to
show that the differentials `d (m+1) m` of the singular chain complex are isomorphisms for odd
`m`.  Transposing, the differentials `dualDifferential R X m` of the singular cochain complex are
isomorphisms for odd `m`; since these differentials alternate with the zero maps, the cohomology
vanishes in positive degrees.

The conclusion is the lemma `Work.Cohomology.totallyDisconnected`: for every `n`,
`Hⁿ⁺¹(X; R) = 0` is a zero object.
-/

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-! ### Generalities on cochain complexes -/

/-- In an abelian category, if the second differential of a short complex is an isomorphism, then
its homology is a zero object: the cycles vanish. -/
lemma isZero_homology_of_isIso_g {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h : IsIso S.g) : IsZero S.homology :=
  IsZero.of_epi S.homologyπ (IsZero.of_iso (isZero_kernel_of_mono S.g) S.cyclesIsoKernel)

/-- In an abelian category, if the first differential of a short complex is an isomorphism, then
its homology is a zero object: the image of the first differential is everything. -/
lemma isZero_homology_of_isIso_f {C : Type*} [Category C] [Abelian C] (S : ShortComplex C)
    (h : IsIso S.f) : IsZero S.homology :=
  IsZero.of_mono S.homologyι (IsZero.of_iso (isZero_cokernel_of_epi S.f) S.opcyclesIsoCokernel)

/-- Isomorphic homological complexes have isomorphic differentials: a differential of one of them
is an isomorphism if and only if the corresponding differential of the other one is. -/
lemma isIso_d_of_iso {C : Type*} [Category C] [HasZeroMorphisms C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (e : K ≅ L) {i j : ι} (h : IsIso (L.d i j)) :
    IsIso (K.d i j) := by
  have hc : e.hom.f j ≫ e.inv.f j = 𝟙 (K.X j) := by
    have h1 := congrArg (fun (φ : K ⟶ K) => φ.f j) e.hom_inv_id
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using h1
  have key : K.d i j = e.hom.f i ≫ L.d i j ≫ e.inv.f j := by
    calc K.d i j = K.d i j ≫ 𝟙 (K.X j) := by rw [Category.comp_id]
      _ = K.d i j ≫ (e.hom.f j ≫ e.inv.f j) := by rw [hc]
      _ = (K.d i j ≫ e.hom.f j) ≫ e.inv.f j := by rw [Category.assoc]
      _ = (e.hom.f i ≫ L.d i j) ≫ e.inv.f j := by rw [← e.hom.comm i j]
      _ = e.hom.f i ≫ L.d i j ≫ e.inv.f j := by rw [Category.assoc]
  rw [key]
  infer_instance

/-! ### The differentials of the alternating constant complex -/

/-- The differentials of the alternating constant complex `M ←0- M ←𝟙- M ←0- ⋯` in odd degree
are identities. -/
lemma alternatingConst_d_eq_one (R : Type) [CommRing R] {M : ModuleCat R} (m : ℕ) (hm : Odd m) :
    (ChainComplex.alternatingConst.obj M).d (m+1) m = 𝟙 M := by
  dsimp only [ChainComplex.alternatingConst]
  rw [HomologicalComplex.alternatingConst_d]
  simp [ComplexShape.down_Rel, hm]

/-- The transpose of an isomorphism of modules is an isomorphism. -/
lemma isIso_ofHom_dualMap {R : Type} [CommRing R] {M N : ModuleCat R} (f : M ⟶ N)
    (hf : IsIso f) : IsIso (ModuleCat.ofHom (f.hom.dualMap)) := by
  haveI : IsIso f := hf
  rw [ConcreteCategory.isIso_iff_bijective]
  have hbij : Function.Bijective f.hom := ConcreteCategory.bijective_of_isIso f
  exact (LinearEquiv.ofBijective f.hom hbij).dualMap.bijective

/-! ### The dual differential in odd degree is an isomorphism -/

/-- For a totally disconnected space `X`, the differentials `d (m+1) m` of the singular chain
complex are isomorphisms in odd degrees: the singular chain complex is the alternating constant
complex `R[X] ←0- R[X] ←𝟙- R[X] ←0- ⋯`. -/
lemma dualDifferential_isIso_of_odd (R : Type) [CommRing R] (X : TopCat)
    [TotallyDisconnectedSpace X] (m : ℕ) (hm : Odd m) :
    IsIso (dualDifferential R X m) := by
  -- The singular chain complex of `X` is the alternating constant complex on `∐ X, R`.
  have h1 : IsIso (((ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ ModuleCat.of R R)).d (m+1) m)) := by
    rw [alternatingConst_d_eq_one R (m := m) (hm := hm)]
    infer_instance
  have h2 : IsIso ((singularChains R X).d (m+1) m) :=
    isIso_d_of_iso (AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat R) (ModuleCat.of R R) X) h1
  -- the cochain differential is the transpose of the chain differential
  have hd : dualDifferential R X m
      = ModuleCat.ofHom (((singularChains R X).d (m+1) m).hom.dualMap) := by
    apply ModuleCat.hom_ext
    simp only [dualDifferential, ModuleCat.hom_ofHom]
    rfl
  rw [hd]
  exact isIso_ofHom_dualMap (f := ((singularChains R X).d (m+1) m)) h2

/-! ### The main theorem -/

theorem totallyDisconnected (R : Type) [CommRing R] (X : TopCat) [TotallyDisconnectedSpace X]
    (n : ℕ) : CategoryTheory.Limits.IsZero (Work.Cohomology.singularCohomology R (n + 1) X) := by
  -- In each degree, one of the two differentials around `Hⁿ⁺¹` is an isomorphism.
  rcases Nat.even_or_odd (n + 1) with h | h
  · -- `n + 1` is even, hence `n` is odd: the first differential of the short complex is an iso.
    have hn : Odd n := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h)
    have hf : IsIso ((singularCochainComplex R X).sc (n+1)).f := by
      show IsIso ((singularCochainComplex R X).d ((ComplexShape.up ℕ).prev (n+1)) (n+1))
      rw [CochainComplex.prev_nat_succ]
      rw [show (singularCochainComplex R X).d n (n+1)
          = dualDifferential R X n from by
        simp [singularCochainComplex, CochainComplex.of, CochainComplex.of.d]]
      exact dualDifferential_isIso_of_odd R X n hn
    exact isZero_homology_of_isIso_f _ hf
  · -- `n + 1` is odd: the second differential of the short complex is an isomorphism.
    have hg : IsIso ((singularCochainComplex R X).sc (n+1)).g := by
      show IsIso ((singularCochainComplex R X).d (n+1) ((ComplexShape.up ℕ).next (n+1)))
      rw [CochainComplex.next]
      rw [show (singularCochainComplex R X).d (n+1) ((n+1)+1)
          = dualDifferential R X (n+1) from by
        simp [singularCochainComplex, CochainComplex.of, CochainComplex.of.d]]
      exact dualDifferential_isIso_of_odd R X (n+1) h
    exact isZero_homology_of_isIso_g _ hg

end

end Work.Cohomology
