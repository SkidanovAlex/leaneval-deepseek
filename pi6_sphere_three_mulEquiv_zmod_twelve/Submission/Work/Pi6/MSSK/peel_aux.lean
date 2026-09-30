import Mathlib
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.SSSR.serreE1StepAux
import Submission.Work.Pi6.MSSK.exists_bdry_lift_of_pieceAlong_cycle

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Work.Pi6.MSSK

namespace Peel

attribute [local implicit_reducible] Work.SSSR.pullAlong
attribute [local implicit_reducible] Work.SSSR.pieceHorn
attribute [local implicit_reducible] Work.SSSR.pieceLastFace
attribute [local implicit_reducible] Work.SSSR.bdryAlong
attribute [local implicit_reducible] Work.SSSR.pieceAlong
attribute [local implicit_reducible] Work.SSSR.pieceBdryHornC
attribute [local implicit_reducible] Work.SSSR.pieceHornC
attribute [local implicit_reducible] Work.SSSR.lastFaceChain

noncomputable section

variable {R : Type} [CommRing R] [Nontrivial R]

/-! ## General chain-complex bookkeeping -/

/-- The element-level description of the composition of two chain maps. -/
lemma comp_f_apply {R : Type} [CommRing R] {K L M : ChainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) (ψ : L ⟶ M) (n : ℕ) (x : K.X n) :
    (ModuleCat.Hom.hom (ψ.f n)) ((ModuleCat.Hom.hom (φ.f n)) x)
      = (ModuleCat.Hom.hom ((φ ≫ ψ).f n)) x := by
  rw [HomologicalComplex.comp_f]
  rfl

/-- The element-level description of the commutation of a chain map with the differentials. -/
lemma chainMap_comm_apply {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) (i j : ℕ) (x : K.X i) :
    (ModuleCat.Hom.hom (L.d i j)) ((ModuleCat.Hom.hom (φ.f i)) x)
      = (ModuleCat.Hom.hom (φ.f j)) ((ModuleCat.Hom.hom (K.d i j)) x) := by
  have h := HomologicalComplex.Hom.comm φ i j
  have h2 := congrArg (fun (g : K.X i ⟶ L.X j) => (ModuleCat.Hom.hom g) x) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The element-level description of the inverse of an isomorphism of chain complexes. -/
lemma iso_inv_hom_apply {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (e : K ≅ L) (n : ℕ) (x : K.X n) :
    (ModuleCat.Hom.hom (e.inv.f n)) ((ModuleCat.Hom.hom (e.hom.f n)) x) = x := by
  have h := congrArg (fun (g : K ⟶ K) => (ModuleCat.Hom.hom (g.f n)) x) (Iso.hom_inv_id e)
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h

/-- Transport of an element along an equality of degrees, composed twice in opposite
directions, is the identity. -/
lemma castElem_cancel {R : Type} [CommRing R] [Nontrivial R] {K : ChainComplex (ModuleCat R) ℕ}
    {i j : ℕ} (h : i = j) (x : K.X i) :
    Work.SSSR.castElem K h.symm (Work.SSSR.castElem K h x) = x := by
  subst h
  simp [Work.SSSR.castElem]

/-- Transport of an element along an equality of degrees, composed twice in the other
order, is the identity. -/
lemma castElem_cancel' {R : Type} [CommRing R] [Nontrivial R] {K : ChainComplex (ModuleCat R) ℕ}
    {i j : ℕ} (h : i = j) (x : K.X j) :
    Work.SSSR.castElem K h (Work.SSSR.castElem K h.symm x) = x := by
  subst h
  simp [Work.SSSR.castElem]

/-- **The differential of a transported cycle vanishes.**  If `x : K.X i` is a cycle, then so is
its transport along any equality of degrees `i = j`. -/
lemma castElem_d_eq_zero {R : Type} [CommRing R] [Nontrivial R] {K : ChainComplex (ModuleCat R) ℕ}
    {i j : ℕ} (h : i = j) (x : K.X i)
    (hx : (ModuleCat.Hom.hom (K.d i (i-1))) x = 0) :
    (ModuleCat.Hom.hom (K.d j (j-1))) (Work.SSSR.castElem K h x) = 0 := by
  subst h
  convert hx using 2
  simp [Work.SSSR.castElem]

/-- **The degreewise surjectivity of a cokernel projection** of a morphism of chain complexes. -/
lemma cokernel_π_f_surjective {R : Type} [CommRing R]
    {K L : ChainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (n : ℕ) (z : (cokernel φ).X n) :
    ∃ x : L.X n, (ModuleCat.Hom.hom ((cokernel.π φ).f n)) x = z := by
  haveI : PreservesColimit (parallelPair φ 0)
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f φ n
  set e := CategoryTheory.Limits.PreservesCokernel.iso
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) φ with he
  have hπ : (cokernel.π φ).f n ≫ e.hom = cokernel.π (φ.f n) := by
    have h := CategoryTheory.Limits.PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n) φ
    simpa only [HomologicalComplex.eval_map, he] using h
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (cokernel.π (φ.f n))).mp inferInstance
    ((ModuleCat.Hom.hom e.hom) z)
  refine ⟨x, ?_⟩
  have h1 : (ModuleCat.Hom.hom e.hom) ((ModuleCat.Hom.hom ((cokernel.π φ).f n)) x)
      = (ModuleCat.Hom.hom (cokernel.π (φ.f n))) x :=
    congrArg (fun g => (ModuleCat.Hom.hom g) x) hπ
  have h2 : (ModuleCat.Hom.hom (cokernel.π (φ.f n))) x = (ModuleCat.Hom.hom e.hom) z := hx
  exact (ModuleCat.mono_iff_injective e.hom).mp inferInstance (h1.trans h2)

/-- **A cycle of the cokernel of a morphism of chain complexes lifts**, with the degrees
`K` and `K-1` kept as they appear in the target statement (this is
`Work.Pi6.MSSK.exists_lift_of_cokernel_cycle` with the successor index made explicit). -/
lemma exists_lift_of_cokernel_cycle_K (R : Type) [CommRing R]
    {A X : ChainComplex (ModuleCat R) ℕ} (i : A ⟶ X) (K : ℕ) (c : X.X K)
    (hc : (ModuleCat.Hom.hom ((cokernel i).d K (K-1)))
      ((ModuleCat.Hom.hom ((cokernel.π i).f K)) c) = 0) :
    ∃ y : A.X (K-1), (ModuleCat.Hom.hom (i.f (K-1))) y
      = (ModuleCat.Hom.hom (X.d K (K-1))) c := by
  have hcomm := HomologicalComplex.Hom.comm (cokernel.π i) K (K-1)
  have h1 : (ModuleCat.Hom.hom ((cokernel.π i).f (K-1)))
      ((ModuleCat.Hom.hom (X.d K (K-1))) c) = 0 := by
    have hh := congrArg (fun (g : X.X K ⟶ (cokernel i).X (K-1)) =>
      (ModuleCat.Hom.hom g) c) hcomm
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    rw [hc] at hh
    exact hh.symm
  haveI : PreservesColimit (parallelPair i 0)
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) (K-1)) :=
    HomologicalComplex.eval_preservesColimit_of_hasCokernel_f i (K-1)
  have h2 : (ModuleCat.Hom.hom (cokernel.π (i.f (K-1))))
      ((ModuleCat.Hom.hom (X.d K (K-1))) c) = 0 := by
    have hiso := CategoryTheory.Limits.PreservesCokernel.π_iso_hom
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) (K-1)) i
    have hh := congrArg (fun (g : (HomologicalComplex.eval (ModuleCat R)
        (ComplexShape.down ℕ) (K-1)).obj X ⟶
        cokernel ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) (K-1)).map i)) =>
      (ModuleCat.Hom.hom g) ((ModuleCat.Hom.hom (X.d K (K-1))) c)) hiso
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
    simp only [HomologicalComplex.eval_map] at hh
    rw [h1, map_zero] at hh
    exact hh.symm
  obtain ⟨y, hy⟩ := Work.Pi6.MSSK.exists_eq_of_cokernel_π_eq_zero R (i.f (K-1)) h2
  exact ⟨y, hy⟩

/-- **The inclusion `C(∂T_σ) ⟶ C(T_σ)` is injective in every degree** (it is
`Work.SSSR.sChainMap` of the inclusion of a subcomplex, hence the coproduct inclusion attached to
an injective map of index sets). -/
lemma TIncl_f_injective {R : Type} [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (f : X ⟶ Y)
    {s : ℕ} (σ : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) ⟶ Y) (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom ((Work.SSSR.TIncl (R := R) f σ).f n)) := by
  have hmono : Mono ((Work.SSSR.TIncl (R := R) f σ).f n) := by
    change Mono ((Work.SSSR.sChainMap R (Work.SSSR.bdryAlong f σ).ι).f n)
    rw [Work.SSSR.sChainMap_f R (Work.SSSR.bdryAlong f σ).ι n]
    exact Work.SSSR.mono_sigma_map'_of_injective R _
      (Work.SSSR.injective_app_of_mono _ inferInstance n)
  exact (ModuleCat.mono_iff_injective _).mp hmono

/-- **The projection formula of `snakeF`, elementwise**: the cokernel projection
`C(T_σ) ⟶ C(T_σ)/C(Λ)` of `TIncl x` equals `snakeF` applied to the class of `x` in
`C(∂T_σ)/C(Λ)`. -/
lemma snakeF_apply {R : Type} [CommRing R] [Nontrivial R] {X Y : SSet.{0}} (f : X ⟶ Y) (P n : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Y)
    (x : (Work.SSSR.sCC R (Work.SSSR.bdryAlong f σ)).X n) :
    ((cokernel.π (Work.SSSR.bdryIncl f σ ≫ Work.SSSR.TIncl (R := R) f σ)).f n)
        (((Work.SSSR.TIncl (R := R) f σ).f n) x)
      = ((Work.SSSR.StepAux.snakeF (R := R) f P σ).f n)
        (((cokernel.π (Work.SSSR.bdryIncl f σ)).f n) x) := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
  rw [Work.SSSR.StepAux.snakeF_π]

/-- **The inverse of `pieceBdryHornIsoIso`, elementwise**: the class in `C(∂T_σ)/C(Λ)` of the
last-face chain of a chain `x` of `T_{d_last σ}` is the image under the isomorphism of the class of
`x` in the σ-piece of the last face. -/
lemma pieceBdryHornIsoIso_inv_apply {R : Type} [CommRing R] [Nontrivial R] {X Y : SSet.{0}}
    (f : X ⟶ Y) (P n : ℕ)
    (σ : (SSet.stdSimplex.obj (SimplexCategory.mk (P+1)) : SSet.{0}) ⟶ Y)
    (x : (Work.SSSR.sCC R (Work.SSSR.pullAlong f
      (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ))).X n) :
    ((cokernel.π (Work.SSSR.bdryIncl f σ)).f n)
        (((Work.SSSR.lastFaceChain (R := R) f P σ).f n) x)
      = ((Work.SSSR.pieceBdryHornIsoIso (R := R) f P σ).inv.f n)
        (((cokernel.π (Work.SSSR.TIncl (R := R) f
          (SSet.stdSimplex.δ (n := P) (Fin.last (P+1)) ≫ σ))).f n) x) := by
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply]
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
  rw [Work.SSSR.pieceBdryHornIsoIso_inv]

/-- `(-1) ^ k` is an involution on any module. -/
lemma negOnePow_smul_smul {R : Type} [CommRing R] {M : ModuleCat R} (k : ℕ) (x : M) :
    ((-1 : ℤ)^k) • (((-1 : ℤ)^k) • x) = x := by
  have hε : ((-1 : ℤ)^k) * ((-1 : ℤ)^k) = 1 := by
    have h2 : ((-1 : ℤ)^k)^2 = (-1 : ℤ)^(2*k) := by rw [← pow_mul, Nat.mul_comm]
    rw [← pow_two, h2, Even.neg_one_pow (even_two_mul k)]
  rw [← mul_zsmul, hε, one_smul]

end

end Peel

end Work.Pi6.MSSK
