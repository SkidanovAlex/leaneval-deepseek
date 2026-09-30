import Mathlib
import Submission.Work.Pi6.MSS.E1Aux
import Submission.Work.Pi6.MSS.e1CohDualDefs
import Submission.Work.Pi6.MSS.e1CohDual.evBijective
import Submission.Work.Pi6.MSS.e1CohDual.evNat
import Submission.Work.SSSR.d1_eqToHom_conj
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cohomological `E_1` row is the dual of the chain level `E_1` row

For a continuous map `p : E → B` and a field `𝕜`, the row complex `E1Row 𝕜 (serreCF 𝕜 E B p) q` of
the cohomological Serre spectral sequence of `p` is isomorphic, as a cochain complex, to the
`𝕜`-dual of the chain level `E_1` row `E1Complex 𝕜 ξ q` for `ξ.F = serF 𝕜 (Sing p)`.

The comparison is the evaluation map `Work.Pi6.MSS.e1cEvFrom` of `e1CohDualDefs.lean` (the
identification of the graded piece `F^s C/F^{s+1} C` with the `𝕜`-dual of `C(A_{s+1})/C(A_s)`); it is
bijective (`e1CohDual.evBijective`) and a cochain map (`e1CohDual.evNat`).  See
`Submission/Work/Pi6/MSS/NOTES_e1CohDual.md` for the status of the assembly.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomologicalComplex
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

variable (𝕜 : Type) [Field 𝕜]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Glue for the dual complex and the `E_1` complex -/

/-- The dual of an isomorphism of chain complexes is an isomorphism of the dual cochain complexes
(contravariantly). -/
def e1cDualIso {C D : ChainComplex (ModuleCat 𝕜) ℕ} (e : C ≅ D) :
    Work.Cohomology.dualComplex 𝕜 C ≅ Work.Cohomology.dualComplex 𝕜 D where
  hom := Work.Cohomology.dualComplexMap 𝕜 D C e.inv
  inv := Work.Cohomology.dualComplexMap 𝕜 C D e.hom
  hom_inv_id := by
    rw [← Work.Cohomology.dualComplexMap_comp 𝕜 e.hom e.inv, Iso.hom_inv_id,
      Work.Cohomology.dualComplexMap_id 𝕜 C]
  inv_hom_id := by
    rw [← Work.Cohomology.dualComplexMap_comp 𝕜 e.inv e.hom, Iso.inv_hom_id,
      Work.Cohomology.dualComplexMap_id 𝕜 D]

/-- Two filtrations with the same underlying functor have isomorphic `E_1` complexes. -/
noncomputable def e1cE1Congr {C : ChainComplex (ModuleCat 𝕜) ℕ}
    (ξ ξ' : Work.SSSR.Filtration 𝕜 C) (h : ξ.F = ξ'.F) (t : ℕ) :
    Work.SSSR.E1Complex 𝕜 ξ t ≅ Work.SSSR.E1Complex 𝕜 ξ' t :=
  HomologicalComplex.Hom.isoOfComponents
    (fun s => eqToIso (congrArg (fun F => (Work.SSSR.grF F s).homology (s+t)) h))
    (fun i j hij => by
      obtain rfl : i = j + 1 := hij.symm
      simp only [Work.SSSR.E1Complex, ChainComplex.of_d]
      exact Work.SSSR.d1_eqToHom_conj ξ ξ' h j t)

/-! ## Transport of cohomological degrees -/

/-- The transport of an element of `Z_1^s` to the target degree is evaluated by the transported
functional. -/
theorem e1cEvPZcast (p : C(E, B)) (s : ℕ) {a b : ℕ} (h : a = b)
    (y : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s a)) :
    (e1cEv 𝕜 p s a y).comp (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) h.symm)
      = e1cEv 𝕜 p s b (e1cPZcast 𝕜 p s h y) := by
  cases h
  have h1 : e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) (rfl : a = a) = LinearMap.id := by
    simp only [e1cHomCast, congrArg, eqToHom_refl, ModuleCat.hom_id]
  have h2 : e1cPZcast 𝕜 p s (rfl : a = a) y = y := by
    apply Subtype.ext
    simp only [e1cPZcast, LinearMap.codRestrict_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, CohFilt.xcast_rfl, LinearMap.id_apply]
  simp only [h1, h2, LinearMap.comp_id]

/-- The two transports along inverse equalities are inverse to each other. -/
theorem e1cHomCast_comp {K : ChainComplex (ModuleCat 𝕜) ℕ} {a b : ℕ} (h : a = b) :
    (e1cHomCast 𝕜 (K := K) h).comp (e1cHomCast 𝕜 (K := K) h.symm) = LinearMap.id := by
  cases h
  simp only [e1cHomCast, congrArg, eqToHom_refl, ModuleCat.hom_id, LinearMap.comp_id]

/-- Composition of the degree transports. -/
theorem e1cHomCast_trans {K : ChainComplex (ModuleCat 𝕜) ℕ} {a b c : ℕ} (h : a = b) (h' : b = c) :
    (e1cHomCast 𝕜 (K := K) h').comp (e1cHomCast 𝕜 (K := K) h)
      = e1cHomCast 𝕜 (K := K) (h.trans h') := by
  cases h
  cases h'
  simp only [e1cHomCast, congrArg, eqToHom_refl, ModuleCat.hom_id, LinearMap.comp_id]

/-- The transport of the homology along an equality of degrees, as a linear equivalence. -/
noncomputable def e1cHomCastEquiv {K : ChainComplex (ModuleCat 𝕜) ℕ} {a b : ℕ} (h : a = b) :
    K.homology a ≃ₗ[𝕜] K.homology b where
  toLinearMap := e1cHomCast 𝕜 (K := K) h
  invFun := e1cHomCast 𝕜 (K := K) h.symm
  left_inv x := by
    show e1cHomCast 𝕜 (K := K) h.symm (e1cHomCast 𝕜 (K := K) h x) = x
    exact LinearMap.congr_fun (e1cHomCast_comp 𝕜 (K := K) h.symm) x
  right_inv x := by
    show e1cHomCast 𝕜 (K := K) h (e1cHomCast 𝕜 (K := K) h.symm x) = x
    exact LinearMap.congr_fun (e1cHomCast_comp 𝕜 (K := K) h) x

/-- The naturality of the comparison map (the statement of `e1CohDual.evNat`). -/
theorem e1cEvShift_nat (p : C(E, B)) (s q : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s (s+q)))
    (z : (e1cKg 𝕜 p (s+1)).cycles ((s+1)+q)) :
    e1cEv 𝕜 p s (s+q) x
        (Work.SSSR.d1 (e1cFilt 𝕜 p) s q
          (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z))
      = e1cEv 𝕜 p (s+1) (s+q+1)
          (pZmap 𝕜 (serreCF 𝕜 E B p) 1 s (s+q) x)
          (e1cHomCast 𝕜 (K := e1cKg 𝕜 p (s+1)) (show (s+1)+q = s+q+1 by omega)
            (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z)) :=
  Work.Pi6.MSS.e1CohDual.evNat 𝕜 E B p s q x z

/-- The transport of the functional along an equality of degrees. -/
theorem e1cEv_congr (p : C(E, B)) (s : ℕ) {a b : ℕ} (h : a = b)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s a)) :
    e1cEv 𝕜 p s a x
      = (e1cEv 𝕜 p s b (e1cPZcast 𝕜 p s h x)).comp
          (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) h) := by
  calc e1cEv 𝕜 p s a x
      = (e1cEv 𝕜 p s a x).comp LinearMap.id := (LinearMap.comp_id _).symm
    _ = (e1cEv 𝕜 p s a x).comp ((e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) h.symm).comp
          (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) h)) := by
          rw [e1cHomCast_comp 𝕜 (K := e1cKg 𝕜 p s) h.symm, LinearMap.comp_id]
    _ = ((e1cEv 𝕜 p s a x).comp (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) h.symm)).comp
          (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) h) := (LinearMap.comp_assoc _ _ _).symm
    _ = (e1cEv 𝕜 p s b (e1cPZcast 𝕜 p s h x)).comp
          (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) h) := by
          rw [e1cEvPZcast 𝕜 p s h x]

/-- The comparison map is bijective in every degree. -/
theorem e1cEvShift_bijective (p : C(E, B)) (s q : ℕ) :
    Function.Bijective (e1cEvShift 𝕜 p s q) := by
  have h1 : Function.Bijective (e1cEvFrom 𝕜 p s (q+s)) :=
    Work.Pi6.MSS.e1CohDual.evBijective 𝕜 E B p s (q+s)
  have h2 : Function.Bijective
      (LinearMap.dualMap (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) (Nat.add_comm s q))) :=
    (LinearEquiv.dualMap (e1cHomCastEquiv 𝕜 (K := e1cKg 𝕜 p s) (Nat.add_comm s q))).bijective
  have h4 : e1cEvShift 𝕜 p s q = (LinearMap.dualMap (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s)
      (Nat.add_comm s q))).comp (e1cEvFrom 𝕜 p s (q+s)) := rfl
  rw [h4]
  exact h2.comp h1

attribute [local implicit_reducible] Work.Pi6.MSS.E1Row Work.SSSR.E1Complex Work.SSSR.E1
  Work.Pi6.MSS.e1cFilt Work.Pi6.MSS.pEraw
  Work.Cohomology.dualComplex Work.Cohomology.dualDiff

/-! ## The comparison map as a cochain map

The comparison map `e1cEvShift 𝕜 p s q` (the `𝕜`-dual of the evaluation of `Z_1^s` on the homology
of the graded piece) is bijective in every degree (`e1cEvShift_bijective`) and satisfies the
cochain-map condition, i.e. it is compatible with the differentials `pD 𝕜 W 1` of `E1Row` and
`dualDiff`/`d1` of `dualComplex (E1Complex 𝕜 (e1cFilt 𝕜 p) q)`.

That cochain-map condition is the statement below (`e1cEvShift_nat_q`, obtained from `e1cEvShift_nat`
by transporting the cochain with `e1cEv_congr`, the `pZmap` with `e1cPZmapPZcast` and the homology
element with `e1cHomCast_trans`; all transports are `eqToHom`'s along `Nat.add_comm`-type equalities,
hence transparent up to `Subsingleton.elim`).  Packaging it with `e1cEvShift_bijective` through
`HomologicalComplex.Hom.isoOfComponents`, and transporting the filtration with
`e1cE1Congr`/`e1cDualIso`, gives `e1CohDual`
(`Submission/Work/Pi6/MSS/NOTES_e1CohDual.md` records the two remaining proof obligations). -/

/-- **Naturality of the comparison map** in the degree conventions of `E1Row` and `E1Complex`. -/
theorem e1cEvShift_nat_q (p : C(E, B)) (s q : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)))
    (z : (e1cKg 𝕜 p (s+1)).cycles ((s+1)+q)) :
    e1cEvShift 𝕜 p s q
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)).subtype) x)
        (Work.SSSR.d1 (e1cFilt 𝕜 p) s q
          (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z))
      = e1cEvShift 𝕜 p (s+1) q
          (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 1 (s+1) (q+(s+1))).comap
            (pZ 𝕜 (serreCF 𝕜 E B p) 1 (s+1) (q+(s+1))).subtype)
            (pZmap 𝕜 (serreCF 𝕜 E B p) 1 s (q+s) x))
          (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z) := by
  rw [e1cEvShift_apply, e1cEvFrom_apply, e1cEvShift_apply, e1cEvFrom_apply]
  have hq : q + s = s + q := by omega
  have hq2 : q + (s+1) = s + q + 1 := by omega
  -- Step 1: the left hand side, in the `s + q` convention.
  have step1 : e1cEv 𝕜 p s (q+s) x
        (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) (Nat.add_comm s q)
          (Work.SSSR.d1 (e1cFilt 𝕜 p) s q
            (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z)))
      = e1cEv 𝕜 p s (s+q) (e1cPZcast 𝕜 p s hq x)
          (Work.SSSR.d1 (e1cFilt 𝕜 p) s q
            (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z)) := by
    rw [e1cEv_congr 𝕜 p s hq x, LinearMap.comp_apply]
    congr 1
    have hcomp : (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) hq).comp
        (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) (Nat.add_comm s q)) = LinearMap.id := by
      rw [show Nat.add_comm s q = hq.symm from Subsingleton.elim _ _]
      exact e1cHomCast_comp 𝕜 (K := e1cKg 𝕜 p s) hq
    rw [← LinearMap.comp_apply (f := e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) hq), hcomp,
      LinearMap.id_apply]
  rw [step1]
  -- Step 2: the naturality, in the `s + q` convention.
  rw [e1cEvShift_nat 𝕜 p s q (e1cPZcast 𝕜 p s hq x) z]
  -- Step 3: the right hand side, back in the `q + (s+1)` convention.
  rw [e1cEv_congr 𝕜 p (s+1) hq2 (pZmap 𝕜 (serreCF 𝕜 E B p) 1 s (q+s) x),
    LinearMap.comp_apply]
  have hpz2 : e1cPZcast 𝕜 p (s+1) hq2 (pZmap 𝕜 (serreCF 𝕜 E B p) 1 s (q+s) x)
      = pZmap 𝕜 (serreCF 𝕜 E B p) 1 s (s+q) (e1cPZcast 𝕜 p s hq x) := by
    rw [show hq2 = (show (q+s)+1 = (s+q)+1 by omega) from Subsingleton.elim _ _]
    exact (e1cPZmapPZcast 𝕜 p s hq x).symm
  rw [hpz2]
  -- Step 4: the two homology elements agree.
  congr 1
  have hcast : (e1cHomCast 𝕜 (K := e1cKg 𝕜 p (s+1)) hq2).comp
      (e1cHomCast 𝕜 (K := e1cKg 𝕜 p (s+1)) (Nat.add_comm (s+1) q))
      = e1cHomCast 𝕜 (K := e1cKg 𝕜 p (s+1))
          (show (s+1)+q = s+q+1 by omega) := by
    rw [e1cHomCast_trans]
  rw [← LinearMap.comp_apply (f := e1cHomCast 𝕜 (K := e1cKg 𝕜 p (s+1)) hq2), hcast]

/-- The differential of the `E_1` complex is `d¹`. -/
theorem e1cE1Complex_d {C : ChainComplex (ModuleCat 𝕜) ℕ} (ξ : Work.SSSR.Filtration 𝕜 C)
    (q i : ℕ) : (Work.SSSR.E1Complex 𝕜 ξ q).d (i+1) i = Work.SSSR.d1 ξ i q := by
  simp only [Work.SSSR.E1Complex, ChainComplex.of_d]

/-- **Naturality of the comparison map**, in the form in which it occurs in the cochain-map
condition: the target argument is `d` of the class rather than the transported `pZmap`. -/
theorem e1cEvShift_nat_q_pD (p : C(E, B)) (s q : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)))
    (z : (e1cKg 𝕜 p (s+1)).cycles ((s+1)+q)) :
    e1cEvShift 𝕜 p s q
        (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)).subtype) x)
        (Work.SSSR.d1 (e1cFilt 𝕜 p) s q
          (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z))
      = e1cEvShift 𝕜 p (s+1) q
          ((pD 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)).hom
            (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)).comap
              (pZ 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)).subtype) x))
          (((e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z) := by
  rw [Work.Pi6.MSS.pd_pD_apply]
  exact e1cEvShift_nat_q 𝕜 p s q x z

/-! ## Assembly -/

/-- The comparison map `e1cEvShift 𝕜 p s q`, as a cochain map from the cohomological `E_1` row to
the dual of the chain level `E_1` row. -/
noncomputable def e1cPhi (p : C(E, B)) (q : ℕ) :
    E1Row 𝕜 (serreCF 𝕜 E B p) q ⟶
      Work.Cohomology.dualComplex 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) :=
  CochainComplex.ofHom (fun s => ModuleCat.ofHom (e1cEvShift 𝕜 p s q))
    (fun i => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      apply LinearMap.ext
      intro z
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
        ((pDen 𝕜 (serreCF 𝕜 E B p) 1 i (q+i)).comap
          (pZ 𝕜 (serreCF 𝕜 E B p) 1 i (q+i)).subtype) y
      obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective
        ((e1cKg 𝕜 p (i+1)).homologyπ ((i+1)+q))).1 inferInstance z
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        Work.Pi6.MSS.E1Row_d, Work.Cohomology.dualComplex, CochainComplex.of_d]
      rw [Work.Cohomology.dualDiff_apply', LinearMap.comp_apply,
        e1cE1Complex_d 𝕜 (e1cFilt 𝕜 p) q i]
      exact e1cEvShift_nat_q_pD 𝕜 p i q x z')

/-- The components of `e1cPhi`. -/
theorem e1cPhi_f (p : C(E, B)) (q s : ℕ) :
    (e1cPhi 𝕜 p q).f s = ModuleCat.ofHom (e1cEvShift 𝕜 p s q) := rfl

/-- Each component of the comparison map is an isomorphism. -/
theorem e1cEvShift_isIso (p : C(E, B)) (s q : ℕ) :
    IsIso ((ModuleCat.ofHom (e1cEvShift 𝕜 p s q)) :
      (E1Row 𝕜 (serreCF 𝕜 E B p) q).X s ⟶
      (Work.Cohomology.dualComplex 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q)).X s) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact e1cEvShift_bijective 𝕜 p s q

/-- **The comparison map is an isomorphism of complexes.** -/
noncomputable def e1cPhiIso (p : C(E, B)) (q : ℕ) :
    E1Row 𝕜 (serreCF 𝕜 E B p) q ≅
      Work.Cohomology.dualComplex 𝕜 (Work.SSSR.E1Complex 𝕜 (e1cFilt 𝕜 p) q) := by
  haveI : ∀ s, IsIso ((e1cPhi 𝕜 p q).f s) := fun s => by
    rw [e1cPhi_f 𝕜 p q s]
    exact e1cEvShift_isIso 𝕜 p s q
  haveI : IsIso (e1cPhi 𝕜 p q) := HomologicalComplex.Hom.isIso_of_components (e1cPhi 𝕜 p q)
  exact asIso (e1cPhi 𝕜 p q)

/-- **The `E_1` row of the cohomological Serre spectral sequence is the dual of the chain level
`E_1` row.** -/
theorem e1CohDual (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (q : ℕ)
    (ξ : Work.SSSR.Filtration 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of E)))
    (hξ : ξ.F = Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)) :
    Nonempty (Work.Pi6.MSS.E1Row 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) q ≅
      Work.Cohomology.dualComplex 𝕜 (Work.SSSR.E1Complex 𝕜 ξ q)) :=
  ⟨e1cPhiIso 𝕜 p q ≪≫ e1cDualIso 𝕜 (e1cE1Congr 𝕜 ξ (e1cFilt 𝕜 p)
    (hξ.trans (e1cFilt_F 𝕜 p).symm) q).symm⟩

end

end Work.Pi6.MSS
