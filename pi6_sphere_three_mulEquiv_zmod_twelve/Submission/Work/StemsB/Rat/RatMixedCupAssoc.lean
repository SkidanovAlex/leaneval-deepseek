import Mathlib
import Submission.Work.StemsB.Rat.CollarDefs

namespace Work.StemsB.Rat

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

noncomputable section

/-! ## Generic (arbitrary coefficient ring) transport tools

The three transport lemmas of `Submission/Work/Thom/localThomMap_cup_zero.lean`
(`Work.Thom.cocycle_transport_K`, `Work.Thom.relComplex_XIsoOfEq_coe`, `Work.Thom.relClassOf_cast`)
are stated there for `ℤ`; the proofs, however, only use the ring-generic structure.  We restate them
here for an arbitrary commutative coefficient ring, which is what the `ℚ`-coefficient associativity
needs.  Likewise `Work.Cohomology.mixedCup_apply` is stated for `ℤ`; its generic form is the
`Classical.choose_spec` of the pairing `Work.Cohomology.mixedRelCupH`. -/

/-- The cocycle condition is transported along an equality of degrees (general coefficient ring). -/
lemma cocycle_transport_K_gen {R : Type} [CommRing R] {K : CochainComplex (ModuleCat R) ℕ}
    {k j : ℕ} (h : k = j) (u : K.X k) (hu : ModuleCat.Hom.hom (K.d k (k+1)) u = 0) :
    ModuleCat.Hom.hom (K.d j (j+1)) ((K.XIsoOfEq h).hom u) = 0 := by
  have e1 := HomologicalComplex.XIsoOfEq_hom_comp_d K h (j+1)
  have e1' := congrArg (fun (g : K.X k ⟶ K.X (j+1)) => ModuleCat.Hom.hom g u) e1
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1'
  have e2 := HomologicalComplex.d_comp_XIsoOfEq_hom K (congrArg (fun t => t + 1) h) k
  have e2' := congrArg (fun (g : K.X k ⟶ K.X (j+1)) => ModuleCat.Hom.hom g u) e2
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e2'
  rw [e1', ← e2', hu, map_zero]

/-- The transport `XIsoOfEq` of the relative complex is the transport of the underlying cochain
(general coefficient ring). -/
lemma relComplex_XIsoOfEq_coe_gen {R : Type} [CommRing R] {Y : TopCat} {B : Set Y} {k j : ℕ}
    (h : k = j) (y : (Work.Cohomology.relComplex R Y B).X k) :
    ((((Work.Cohomology.relComplex R Y B).XIsoOfEq h).hom y)).1 =
      (h ▸ (y.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj Y) k) :
        Work.Cohomology.Cochain R (TopCat.toSSet.obj Y) j) := by
  subst h; simp

lemma eqRec_homologyπ_cocycleOfK_gen {R : Type} [CommRing R]
    {K : CochainComplex (ModuleCat R) ℕ} {a b : ℕ} (h : a = b)
    (y : K.X a) (hy : (K.d a (a+1)).hom y = 0)
    (hy' : (K.d b (b+1)).hom ((K.XIsoOfEq h).hom y) = 0) :
    (h ▸ (K.homologyπ a (Work.Cohomology.cocycleOfK K y hy)) : K.homology b) =
      K.homologyπ b (Work.Cohomology.cocycleOfK K ((K.XIsoOfEq h).hom y) hy') := by
  cases h; simp

/-- The relative class of a cocycle commutes with the transport along an equality of degrees
(general coefficient ring). -/
lemma relClassOf_cast_gen {R : Type} [CommRing R] {Y : TopCat} {A : Set Y} {k j : ℕ} (h : k = j)
    (u : Work.Cohomology.relKern R Y A k) (hu : Work.Cohomology.relDiffLM R Y A k u = 0)
    (hu' : Work.Cohomology.relDiffLM R Y A j
      (((Work.Cohomology.relComplex R Y A).XIsoOfEq h).hom u) = 0) :
    (h ▸ Work.Cohomology.relClassOf R Y A u hu : (Work.Cohomology.relComplex R Y A).homology j)
      = Work.Cohomology.relClassOf R Y A
          (((Work.Cohomology.relComplex R Y A).XIsoOfEq h).hom u) hu' := by
  rw [show Work.Cohomology.relClassOf R Y A u hu = (Work.Cohomology.relComplex R Y A).homologyπ k
      (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex R Y A) u
        (show ((Work.Cohomology.relComplex R Y A).d k (k+1)).hom u = 0 by
          rw [Work.Cohomology.relComplex_d]; exact hu)) from rfl,
    show Work.Cohomology.relClassOf R Y A
        (((Work.Cohomology.relComplex R Y A).XIsoOfEq h).hom u) hu'
      = (Work.Cohomology.relComplex R Y A).homologyπ j
        (Work.Cohomology.cocycleOfK (Work.Cohomology.relComplex R Y A)
          (((Work.Cohomology.relComplex R Y A).XIsoOfEq h).hom u)
          (show ((Work.Cohomology.relComplex R Y A).d j (j+1)).hom
              (((Work.Cohomology.relComplex R Y A).XIsoOfEq h).hom u) = 0 by
            rw [Work.Cohomology.relComplex_d]; exact hu')) from rfl]
  exact eqRec_homologyπ_cocycleOfK_gen (K := Work.Cohomology.relComplex R Y A) h u _ _

/-- **The computation rule for the generic mixed cup product**: on the classes of an absolute
cocycle `a` and a relative cocycle `b` it is the class of the Alexander–Whitney product `a ⌣ b`. -/
theorem mixedCupC_apply_gen (R : Type) [CommRing R] {X : Type} [TopologicalSpace X]
    (A : Set X) (m n : ℕ)
    (a : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of X)) m)
    (b : Work.Cohomology.relKern R (TopCat.of X) A n)
    (ha : Work.Cohomology.cochainDiff R (TopCat.toSSet.obj (TopCat.of X)) a = 0)
    (hb : Work.Cohomology.relDiffLM R (TopCat.of X) A n b = 0) :
    ∃ (hmem : Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X)) a
          (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of X)) n) ∈
        Work.Cohomology.relKern R (TopCat.of X) A (m + n)),
      ∃ (h : Work.Cohomology.relDiffLM R (TopCat.of X) A (m + n)
            ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X)) a
              (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of X)) n), hmem⟩ = 0),
        Work.Thom.mixedCupC R A m n
            (Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj (TopCat.of X)) a ha)
            (Work.Cohomology.relClassOf R (TopCat.of X) A b hb) =
          Work.Cohomology.relClassOf R (TopCat.of X) A
            ⟨Work.Cohomology.cup R (TopCat.toSSet.obj (TopCat.of X)) a
              (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj (TopCat.of X)) n), hmem⟩ h :=
  (Classical.choose_spec (Work.Cohomology.mixedRelCupH R (TopCat.of X) A)) m n a b ha hb

/-! **Associativity of the rational mixed cup product with a degree-zero factor**:
`(a ⌣ c) ⌣ z = a ⌣ (c ⌣ z)` for `c ∈ H^0`.  The two sides live in the degrees `(m+0)+k = m+k`
and `m+(0+k)`, compared by the cast `Nat.add_assoc m 0 k`.  This is the `ℚ`-coefficient analogue of
`Work.StemsB.mixedCupC_assoc_zero` in `Submission/Work/StemsB/collarSqMixed.lean` (whose proof
should be copied; note that the rational file `Submission/Work/StemsB/Rat/CollarSqMixed.lean`
contains a *broken* attempt at the same statement, so do not import it, to avoid a name clash).
The only new ingredients are the `ℚ` analogues of `Work.Cohomology.mixedCup` /
`Work.Cohomology.mixedCup_apply` of `Submission/Work/Cohomology/sph3DiscMixedDefs.lean` (namely
`(Classical.choose (mixedRelCupH (R := ℚ) X A)) m n` together with
`Classical.choose_spec (mixedRelCupH (R := ℚ) X A)` -- the pairing `mixedRelCupH` is available for
an arbitrary coefficient ring) and of the three transport lemmas
`Work.Thom.cocycle_transport_K`, `Work.Thom.relComplex_XIsoOfEq_coe`,
`Work.Thom.relClassOf_cast` of `Submission/Work/Thom/localThomMap_cup_zero.lean`, which are stated
there only for `ℤ`; `relComplex` itself is ring-generic.  Everything else
(`Work.Cohomology.cupAssoc`, `cupH'_apply'`, `exists_cohomologyClassOf`, `exists_relClassOf`,
`cochainDiff_cup_of_cocycles`, `relClassOf_congr`, `relComplex_d_apply`) is available for a general
coefficient ring. -/
theorem RatMixedCupAssoc {X : Type} [TopologicalSpace X] (A : Set X) (m k : ℕ)
    (a : Work.Thom.Coh ℚ m X) (c : Work.Thom.Coh ℚ 0 X) (z : Work.Thom.RelCoh ℚ k X A) :
    (Work.Thom.mixedCupC ℚ A m (0 + k)) a ((Work.Thom.mixedCupC ℚ A 0 k) c z)
      = (Nat.add_assoc m 0 k) ▸
          ((Work.Thom.mixedCupC ℚ A m k)
            ((Work.Cohomology.cupH' ℚ (TopCat.toSSet.obj (TopCat.of X)) m 0) a c) z) := by
  obtain ⟨α, hα, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) m a
  obtain ⟨β, hβ, rfl⟩ := Work.Cohomology.exists_cohomologyClassOf ℚ
    (TopCat.toSSet.obj (TopCat.of X)) 0 c
  obtain ⟨ζ, hζ, rfl⟩ := Work.Cohomology.exists_relClassOf ℚ (TopCat.of X) A k z
  -- the left-hand side
  obtain ⟨hmem1, hcoc1, h1⟩ :=
    mixedCupC_apply_gen (R := ℚ) A 0 k β ζ hβ hζ
  rw [h1]
  obtain ⟨hmem2, hcoc2, h2⟩ :=
    mixedCupC_apply_gen (R := ℚ) A m (0 + k) α
      ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X)) β ζ.1, hmem1⟩ hα hcoc1
  rw [h2]
  -- the right-hand side, under the cast
  rw [Work.Cohomology.cupH'_apply' ℚ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ]
  obtain ⟨hmem3, hcoc3, h3⟩ :=
    mixedCupC_apply_gen (R := ℚ) A m k
      (Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ
      (Work.Cohomology.cochainDiff_cup_of_cocycles ℚ (TopCat.toSSet.obj (TopCat.of X)) α β hα hβ)
      hζ
  rw [h3]
  -- push the cast inside
  let u3 : Work.Cohomology.relKern ℚ (TopCat.of X) A (m + k) :=
    ⟨Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X))
        (Work.Cohomology.cup ℚ (TopCat.toSSet.obj (TopCat.of X)) α β) ζ.1, hmem3⟩
  have hu3 : Work.Cohomology.relDiffLM ℚ (TopCat.of X) A (m + k) u3 = 0 := hcoc3
  have hu3' : Work.Cohomology.relDiffLM ℚ (TopCat.of X) A (m + (0 + k))
      (((Work.Cohomology.relComplex ℚ (TopCat.of X) A).XIsoOfEq
        (Nat.add_assoc m 0 k)).hom u3) = 0 := by
    rw [← Work.Cohomology.relComplex_d_apply]
    exact cocycle_transport_K_gen (K := Work.Cohomology.relComplex ℚ (TopCat.of X) A)
      (Nat.add_assoc m 0 k) u3 (by rw [Work.Cohomology.relComplex_d_apply]; exact hu3)
  rw [relClassOf_cast_gen (Y := TopCat.of X) (A := A) (Nat.add_assoc m 0 k) u3 hu3 hu3']
  -- the cochain identity
  refine Work.Cohomology.relClassOf_congr ℚ (TopCat.of X) A hcoc2 _ (Subtype.ext ?_)
  rw [relComplex_XIsoOfEq_coe_gen (Y := TopCat.of X) (B := A) (Nat.add_assoc m 0 k)]
  simpa only [Subtype.coe_mk, Subtype.coe_eta] using
    (Work.Cohomology.cupAssoc ℚ (TopCat.toSSet.obj (TopCat.of X)) α β ζ.1).symm

end

end Work.StemsB.Rat
