import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSEQP.EqpCechSetup
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero
import Submission.Work.DSEQP.eqp_cech_affine_loc
import Submission.Work.DSEQP.eqp_cech_clear_denoms
import Submission.Work.DSEQP.eqp_cech_kernel
import Submission.Work.DSEQP.eqp_cech_homology_finite
import Submission.Work.DSEQP.eqp_cech_cocycle_generators

/-!
# Higher Čech cohomology is killed by a power of `g`

`Work.DSEQP.eqp_cech_torsion_proved`: if a finite affine cover `U` of a scheme `X` separated over
`Spec A` becomes trivial after inverting `g` (that is, `f ⁻¹ᵁ D(g) ⊆ U j` for some `j`), then the
`(q+1)`-st Čech cohomology of `U` is annihilated by a power of `g`.

The proof decomposes as follows (all the pieces below are proved in the named modules).

* `Work.DSEQP.Xg`, `cechLoc`, `locCech` (`EqpCechSetup`): the open `X_g = f ⁻¹ᵁ D(g)`, the Čech
  complex of the presheaf `W ↦ Γ(X, W ⊓ X_g)`, and the comparison chain map
  `locCech : Č(U, 𝒪_X) ⟶ Č(U, W ↦ Γ(X, W ⊓ X_g))`.
* `Work.DSEQP.locCech_exact` (`EqpCechSetup`): since `X_g ≤ U j`, the localized Čech complex is
  acyclic in positive degrees — `Work.DSF1.Cech.UnitCase` applied to the presheaf of `(Qo …)`.
* `Work.DSEQP.eqp_cech_affine_loc`: over an affine open `W`, restriction `Γ(X,W) → Γ(X, W ⊓ X_g)`
  is the localization at `g` (clearing denominators and kernel).
* `Work.DSEQP.eqp_cech_clear_denoms`, `Work.DSEQP.eqp_cech_kernel`: the same two statements for the
  comparison chain map `locCech`, obtained componentwise from the affine statement (the simplex
  opens are affine because `X` is separated).
* `Work.DSEQP.eqp_cech_homology_finite`: `H^{q+1}` of the Čech complex is a finitely generated
  `A`-module, because it is quasi-isomorphic to the bounded-above finite free model `P`.
* `Work.DSEQP.eqp_cech_cocycle_generators`: finitely many cocycles generate all cocycles modulo
  coboundaries.

Combining them: for a cocycle `w` in degree `q+1`, `locCech w` is a coboundary of the localized
complex; clearing denominators and using the kernel statement shows that some power of `g` times
`w` is a coboundary of `Č(U, 𝒪_X)`. The exponents are made uniform by the finite generation of
`H^{q+1}`, which supplies finitely many generating cocycles.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits Opposite

namespace Work.DSEQP

open DSMap DSMap.Mix DSMap.Mix2
open scoped Simplicial BigOperators

universe a

/-- Every simplex open of the Čech nerve of a family of affine opens of a scheme separated over
`Spec A` is affine. -/
theorem isAffineOpen_Eobj (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] {ι : Type a} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (n : ℕ)
    (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n))).I) :
    IsAffineOpen (Work.DSF1.Cech.Eobj U n x) := by
  haveI : IsAffineHom (pullback.diagonal (terminal.from X)) :=
    isAffineHom_diagonal_of_isSeparated (X := X) (f := f) (inferInstance : IsSeparated f)
  rw [show Work.DSF1.Cech.Eobj U n x = ∏ᶜ (U ∘ x) from rfl, Work.DSF1.Cech.piObj_eq_iInf]
  exact IsAffineOpen.iInf (fun b => hU (x b))

/-- The componentwise hypotheses needed by `eqp_cech_clear_denoms` and `eqp_cech_kernel`, obtained
from `eqp_cech_affine_loc` at the affine simplex opens. -/
theorem hcomp_aux (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] {ι : Type a} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (g : A) :
    ∀ (n : ℕ) (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n))).I),
      ((∀ z : (presheafLoc A X f g).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)),
        ∃ (k : ℕ) (t : (cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
          ((cechPresheaf A X f).map
            (CategoryTheory.homOfLE
              (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ Xg A X f g ≤
                Work.DSF1.Cech.Eobj U n x)).op).hom t = g ^ k • z) ∧
       (∀ t : (cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)),
          ((cechPresheaf A X f).map
            (CategoryTheory.homOfLE
              (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ Xg A X f g ≤
                Work.DSF1.Cech.Eobj U n x)).op).hom t = 0 → ∃ k : ℕ, g ^ k • t = 0)) :=
  fun n x =>
    eqp_cech_affine_loc A X f (Work.DSF1.Cech.Eobj U n x) (isAffineOpen_Eobj A X f U hU n x) g

/-- For every cocycle in degree `q+1` of the Čech complex, some power of `g` turns it into a
coboundary. -/
theorem cech_kill (A : Type a) [CommRing A] (X : Scheme.{a}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] {ι : Type a} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (g : A) (j : ι) (hgood : Xg A X f g ≤ U j) (q : ℕ)
    (w : (DSMap.cech A X f U).X (q + 1))
    (hw : ((DSMap.cech A X f U).d (q + 1) (q + 2)).hom w = 0) :
    ∃ N : ℕ, g ^ N • w ∈ LinearMap.range (((DSMap.cech A X f U).d q (q + 1)).hom) := by
  have hcomp := hcomp_aux A X f U hU g
  have hsurj := fun n x => (hcomp n x).1
  have hker := fun n x => (hcomp n x).2
  have hcc : ((locCech A X f U g).f (q + 1) ≫
      (cechLoc A X f U g).d (q + 1) (q + 2)).hom w = 0 := by
    rw [HomologicalComplex.Hom.comm, ModuleCat.comp_apply, hw, map_zero]
  have hcc' : ((cechLoc A X f U g).d (q + 1) (q + 2)).hom
      ((locCech A X f U g).f (q + 1) w) = 0 := by
    rwa [ModuleCat.comp_apply] at hcc
  obtain ⟨t, ht⟩ := locCech_exact (A := A) (X := X) (f := f) (U := U) (g := g) (j := j) hgood q
    ((locCech A X f U g).f (q + 1) w) hcc'
  obtain ⟨k, s, hs⟩ := eqp_cech_clear_denoms A X f U g hsurj q t
  have hnat : (locCech A X f U g).f (q + 1) (((DSMap.cech A X f U).d q (q + 1)).hom s)
      = ((cechLoc A X f U g).d q (q + 1)).hom ((locCech A X f U g).f q s) := by
    have hchain := HomologicalComplex.Hom.comm (locCech A X f U g) q (q + 1)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← hchain]
  have h0 : (locCech A X f U g).f (q + 1)
      (g ^ k • w - ((DSMap.cech A X f U).d q (q + 1)).hom s) = 0 := by
    rw [map_sub, map_smul, hnat, hs, map_smul, ht, sub_self]
  obtain ⟨m, hm⟩ := eqp_cech_kernel A X f U g hker (q + 1)
    (g ^ k • w - ((DSMap.cech A X f U).d q (q + 1)).hom s) h0
  refine ⟨m + k, ?_⟩
  have h1 : g ^ m • (g ^ k • w) = g ^ m • (((DSMap.cech A X f U).d q (q + 1)).hom s) := by
    have h2 := hm
    simp only [smul_sub, sub_eq_zero] at h2
    exact h2
  have hm' : g ^ m • (g ^ k • w) = ((DSMap.cech A X f U).d q (q + 1)).hom (g ^ m • s) := by
    rw [h1, map_smul]
  refine LinearMap.mem_range.mpr ⟨g ^ m • s, ?_⟩
  rw [← hm', pow_add, mul_smul]

/-- Finiteness of the higher Čech cohomology, from a bounded-above finite free model. -/
theorem cech_homology_finite_aux (A : Type a) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{a}) (f : X ⟶ Spec (.of A)) {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : DSMap.Mix2.IsFinFreeModelU A X f U P ε) (q : ℕ) :
    Module.Finite A ((DSMap.cech A X f U).homology (q + 1)) := by
  obtain ⟨hP1, -, φ, hφ, -⟩ := hP
  have hfinZ : Module.Finite A
      (((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat).homology ((q + 1 : ℕ) : ℤ)) :=
    eqp_cech_homology_finite A ((DSMap.cech A X f U).extend ComplexShape.embeddingUpNat)
      P hP1 φ hφ _
  have e := HomologicalComplex.extendHomologyIso (DSMap.cech A X f U)
    ComplexShape.embeddingUpNat (j := q + 1) (j' := ((q + 1 : ℕ) : ℤ)) rfl
  haveI := hfinZ
  exact Module.Finite.of_surjective e.hom.hom (fun y => ⟨e.inv.hom y, by simp⟩)

theorem eqp_cech_torsion_proved (A : Type a) [CommRing A] [IsNoetherianRing A] (X : Scheme.{a})
    (f : X ⟶ Spec (.of A)) [IsSeparated f] {ι : Type a} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (g : A) (j : ι)
    (hgood : f ⁻¹ᵁ (PrimeSpectrum.basicOpen g : (Spec (.of A)).Opens) ≤ U j)
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    (hP : IsFinFreeModelU A X f U P ε) (q : ℕ) :
    ∃ N : ℕ, ∀ z : (cech A X f U).X (q + 1), ((cech A X f U).d (q + 1) (q + 2)).hom z = 0 →
      ∃ y : (cech A X f U).X q, ((cech A X f U).d q (q + 1)).hom y = g ^ N • z := by
  have hgood' : Xg A X f g ≤ U j := hgood
  have hfin := cech_homology_finite_aux A X f U P ε hP q
  obtain ⟨r, z, hz, hgen⟩ := eqp_cech_cocycle_generators (DSMap.cech A X f U) q hfin
  have hkill : ∀ i : Fin r, ∃ N : ℕ,
      g ^ N • z i ∈ LinearMap.range (((DSMap.cech A X f U).d q (q + 1)).hom) :=
    fun i => cech_kill A X f U hU g j hgood' q (z i) (hz i)
  choose N hN using hkill
  refine ⟨∑ i, N i, fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := hgen w hw
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp ha
  choose v hv using fun i => LinearMap.mem_range.mp (hN i)
  refine ⟨g ^ (∑ i, N i) • u + ∑ i, a i • (g ^ ((∑ j, N j) - N i) • v i), ?_⟩
  have hle : ∀ i : Fin r, N i ≤ ∑ j, N j := fun i =>
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hdi : ∀ i : Fin r, ((DSMap.cech A X f U).d q (q + 1)).hom
      (g ^ ((∑ j, N j) - N i) • v i) = g ^ (∑ j, N j) • z i := by
    intro i
    rw [map_smul, hv i, smul_smul, ← pow_add, Nat.sub_add_cancel (hle i)]
  have hS : ∑ i : Fin r, ((DSMap.cech A X f U).d q (q + 1)).hom
        (a i • (g ^ ((∑ j, N j) - N i) • v i))
      = ∑ i : Fin r, a i • (g ^ (∑ j, N j) • z i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hdi i]
  have hT : ∑ i : Fin r, g ^ (∑ j, N j) • (a i • z i)
      = ∑ i : Fin r, a i • (g ^ (∑ j, N j) • z i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, smul_smul, mul_comm]
  rw [map_add, map_smul, map_sum, hS, hu, smul_sub, Finset.smul_sum, hT, sub_add_cancel]

end Work.DSEQP
