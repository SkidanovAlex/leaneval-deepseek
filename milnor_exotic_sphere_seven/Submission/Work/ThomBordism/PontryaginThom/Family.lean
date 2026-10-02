import Submission.Work.ThomBordism.PontryaginThom.Hurewicz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The family/one-manifold dictionary for the Pontryagin–Thom data

Three bookkeeping lemmas relating the single-manifold data `PTRep` to the family data
`PTFamilyRep`:

* `PTFamilyRep` is invariant under a bijection of the index type (`ptFamilyRepReindex`): the index
  type only enters through the finite sums of the Pontryagin numbers;
* the `Fin 1`-family rep of `V` is exactly a single rep of `V` (`ptRepOfFamilyRep`,
  `ptFamilyRepOfRep`), the normal-bundle data being forgotten/restored by hand.

These are used in `Bordism.lean` to derive the single-manifold transversality input from the family
one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Work.ThomBordism.PontryaginThom

noncomputable section

open Work.Cohomology

/-- **Reindexing a family rep**: the index type of `PTFamilyRep` enters only through the two finite
sums, so a bijection of index types (with the corresponding family) gives the same data. -/
noncomputable def ptFamilyRepReindex {k : ℕ} {D : ThomTarget k} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') {F : ι → Man8} {G : ι' → Man8} (h : ∀ i, G (e i) = F i)
    (r : PTFamilyRep ι F k D) : PTFamilyRep ι' G k D where
  collapse := r.collapse
  hurewicz_p1sq := by
    rw [r.hurewicz_p1sq,
      Fintype.sum_equiv e (fun i => (F i).p1Sq) (fun j => (G j).p1Sq)
        (fun i => congrArg Man8.p1Sq (h i).symm)]
  hurewicz_p2 := by
    rw [r.hurewicz_p2,
      Fintype.sum_equiv e (fun i => (F i).p1Sq - (F i).p2Num)
        (fun j => (G j).p1Sq - (G j).p2Num)
        (fun i => congrArg (fun W : Man8 => W.p1Sq - W.p2Num) (h i).symm)]

/-- **A `Fin 1`-family rep of `V` is a single rep of `V`**, once the normal-bundle data of the
embedding is supplied (a family rep carries none, since the pairings of a family are sums of
numbers and are insensitive to it). -/
noncomputable def ptRepOfFamilyRep {k : ℕ} {D : ThomTarget k} {V : Man8} (n : NormalBundlData V)
    (r : PTFamilyRep (Fin 1) (fun _ => V) k D) : PTRep V k D where
  normal := n
  collapse := r.collapse
  hurewicz_p1sq := by
    rw [r.hurewicz_p1sq, n.normalP1Sq_eq]
    simp
  hurewicz_p2 := by
    rw [r.hurewicz_p2, n.normalP2_eq]
    simp

/-- **The `Fin 1`-family rep of `V` built from a single rep of `V`** (with the same class `α`). -/
noncomputable def ptFamilyRepOfRep {k : ℕ} {D : ThomTarget k} {V : Man8} (r : PTRep V k D) :
    PTFamilyRep (Fin 1) (fun _ => V) k D where
  collapse := r.collapse
  hurewicz_p1sq := by
    rw [r.hurewicz_p1sq, r.normal.normalP1Sq_eq]
    simp
  hurewicz_p2 := by
    rw [r.hurewicz_p2, r.normal.normalP2_eq]
    simp

end

end Work.ThomBordism.PontryaginThom
