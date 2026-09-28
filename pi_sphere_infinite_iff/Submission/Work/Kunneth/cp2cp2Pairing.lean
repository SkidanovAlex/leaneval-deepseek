import Mathlib
import Submission.Work.Kunneth.cp2cp2Fund
import Submission.Work.Kunneth.pullbackHCup
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Projective.cp2SelfIntersection_pm_one_uncond

/-!
# The middle intersection form of `ℂP² × ℂP²`

This file computes the `3 × 3` matrix of intersection numbers of the three middle classes
`a², ab, b²` of `ℂP² × ℂP²` (`a = π₁^*h`, `b = π₂^*h`, `h` the hyperplane class of `ℂP²`).

With the fundamental class `c = [ℂP²] × [ℂP²]` (`Work.Kunneth.cpFund`), the matrix of the pairings
`⟨x ⌣ y, c⟩` on the ordered triple `(a², ab, b²)` is

```
    [ 0  0  1 ]
    [ 0  1  0 ]
    [ 1  0  0 ]
```

— a permutation matrix, in particular unimodular.  The off-diagonal vanishing is degree
bookkeeping in the factors (`H⁶(ℂP²) = H⁸(ℂP²) = 0`), and the diagonal entries are
`⟨a² ⌣ b², c⟩ = ⟨ab ⌣ ab, c⟩ = ⟨h², [ℂP²]⟩² = 1`: the middle self-intersection of `ℂP²` is
`±1` (`Work.Projective.cp2SelfIntersection_pm_one_uncond`), so its square is `1`.

## Main results

* `Work.Kunneth.cpa2_cpb2_pairing` — `⟨a² ⌣ b², c⟩ = 1`;
* `Work.Kunneth.cpab_cpab_pairing` — `⟨ab ⌣ ab, c⟩ = 1`;
* `Work.Kunneth.cpa2_cpa2_pairing`, `cpa2_cpab_pairing`, `cpab_cpa2_pairing`,
  `cpab_cpb2_pairing`, `cpb2_cpab_pairing`, `cpb2_cpb2_pairing` — the vanishing entries;
* `Work.Kunneth.cup_assoc_222`, `cup_assoc_224`, `cup_assoc_422`, `cup_comm_22`, `cup_comm_44`
  — the cast-free forms of associativity and graded commutativity of the cup product in the
  degrees used here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-! ## Notation -/

/-- The hyperplane class `h ∈ H²(ℂP²;ℤ)`. -/
abbrev cpH := Work.Projective.cp2H

/-- `h ⌣ h ∈ H⁴(ℂP²;ℤ)`. -/
abbrev cpHsq := cupH' ℤ cpX 2 2 cpH cpH

/-- `a = π₁^* h ∈ H²(ℂP² × ℂP²;ℤ)`. -/
abbrev cpa := pullbackH cpZ cpX cpFst 2 cpH

/-- `b = π₂^* h ∈ H²(ℂP² × ℂP²;ℤ)`. -/
abbrev cpb := pullbackH cpZ cpX cpSnd 2 cpH

/-- `a² = a ⌣ a ∈ H⁴(ℂP² × ℂP²;ℤ)`. -/
abbrev cpa2 := cupH' ℤ cpZ 2 2 cpa cpa

/-- `ab = a ⌣ b ∈ H⁴(ℂP² × ℂP²;ℤ)`. -/
abbrev cpab := cupH' ℤ cpZ 2 2 cpa cpb

/-- `b² = b ⌣ b ∈ H⁴(ℂP² × ℂP²;ℤ)`. -/
abbrev cpb2 := cupH' ℤ cpZ 2 2 cpb cpb

/-! ## The cohomology of `ℂP²` vanishes in degrees `6` and `8` -/

/-- `H⁶(ℂP²;ℤ) = 0`. -/
instance subsingleton_cpH_six : Subsingleton ↥((SSetCochainComplex ℤ cpX).homology 6) := by
  obtain ⟨e⟩ := (Work.Projective.cpn_cohomology 2 6 :
    Nonempty ((SSetCochainComplex ℤ cpX).homology 6 ≅ Work.Projective.cpnModel 2 6))
  have h : Subsingleton ↥(Work.Projective.cpnModel 2 6) := by
    rw [Work.Projective.cpnModel, if_neg (by decide)]
    infer_instance
  haveI := h
  exact ⟨fun a b => e.toLinearEquiv.injective (Subsingleton.elim _ _)⟩

/-- `H⁸(ℂP²;ℤ) = 0`. -/
instance subsingleton_cpH_eight : Subsingleton ↥((SSetCochainComplex ℤ cpX).homology 8) := by
  obtain ⟨e⟩ := (Work.Projective.cpn_cohomology 2 8 :
    Nonempty ((SSetCochainComplex ℤ cpX).homology 8 ≅ Work.Projective.cpnModel 2 8))
  have h : Subsingleton ↥(Work.Projective.cpnModel 2 8) := by
    rw [Work.Projective.cpnModel, if_neg (by decide)]
    infer_instance
  haveI := h
  exact ⟨fun a b => e.toLinearEquiv.injective (Subsingleton.elim _ _)⟩

/-- **`h² ⌣ h = 0`**, because `H⁶(ℂP²;ℤ) = 0`. -/
theorem cpHsq_mul_cpH : cupH' ℤ cpX 4 2 cpHsq cpH = 0 := by
  haveI : Subsingleton ↥((SSetCochainComplex ℤ cpX).homology (4 + 2)) := subsingleton_cpH_six
  exact Subsingleton.elim _ 0

/-- **`h ⌣ h² = 0`**, because `H⁶(ℂP²;ℤ) = 0`. -/
theorem cpH_mul_cpHsq : cupH' ℤ cpX 2 4 cpH cpHsq = 0 := by
  haveI : Subsingleton ↥((SSetCochainComplex ℤ cpX).homology (2 + 4)) := subsingleton_cpH_six
  exact Subsingleton.elim _ 0

/-- **`h² ⌣ h² = 0`**, because `H⁸(ℂP²;ℤ) = 0`. -/
theorem cpHsq_mul_cpHsq : cupH' ℤ cpX 4 4 cpHsq cpHsq = 0 := by
  haveI : Subsingleton ↥((SSetCochainComplex ℤ cpX).homology (4 + 4)) := subsingleton_cpH_eight
  exact Subsingleton.elim _ 0

/-! ## Cast-free associativity and graded commutativity

`Work.Cohomology.cupH'_assoc` and `Work.Cohomology.gradedComm` are stated with a transport along
`Nat.add_assoc`/`Nat.add_comm`; at the numeric degrees used below those transports are
*definitionally* the identity, so the following are the usable cast-free forms.
-/

/-- Associativity of the cup product at degrees `(2,2,2)`, cast-free. -/
lemma cup_assoc_222 (x y z : ↥((SSetCochainComplex ℤ cpZ).homology 2)) :
    cupH' ℤ cpZ 4 2 (cupH' ℤ cpZ 2 2 x y) z
      = cupH' ℤ cpZ 2 4 x (cupH' ℤ cpZ 2 2 y z) := by
  have h := cupH'_assoc ℤ cpZ 2 2 2 x y z
  rw [Subsingleton.elim (Nat.add_assoc 2 2 2) (rfl : (2 + 2) + 2 = 2 + (2 + 2))] at h
  exact h

/-- Associativity of the cup product at degrees `(2,2,4)`, cast-free. -/
lemma cup_assoc_224 (x y : ↥((SSetCochainComplex ℤ cpZ).homology 2))
    (z : ↥((SSetCochainComplex ℤ cpZ).homology 4)) :
    cupH' ℤ cpZ 4 4 (cupH' ℤ cpZ 2 2 x y) z
      = cupH' ℤ cpZ 2 6 x (cupH' ℤ cpZ 2 4 y z) := by
  have h := cupH'_assoc ℤ cpZ 2 2 4 x y z
  rw [Subsingleton.elim (Nat.add_assoc 2 2 4) (rfl : (2 + 2) + 4 = 2 + (2 + 4))] at h
  exact h

/-- Associativity of the cup product at degrees `(4,2,2)`, cast-free. -/
lemma cup_assoc_422 (x : ↥((SSetCochainComplex ℤ cpZ).homology 4))
    (y z : ↥((SSetCochainComplex ℤ cpZ).homology 2)) :
    cupH' ℤ cpZ 6 2 (cupH' ℤ cpZ 4 2 x y) z
      = cupH' ℤ cpZ 4 4 x (cupH' ℤ cpZ 2 2 y z) := by
  have h := cupH'_assoc ℤ cpZ 4 2 2 x y z
  rw [Subsingleton.elim (Nat.add_assoc 4 2 2) (rfl : (4 + 2) + 2 = 4 + (2 + 2))] at h
  exact h

/-- The canonical `ℤ`-action of an additive commutative group (`ZSMul.toSMul`) agrees with the one
carried by a `Module ℤ` structure on it (all such structures are propositionally equal). -/
private lemma zsmulToSMul_eq (H : Type*) [AddCommGroup H] [Module ℤ H] :
    (ZSMul.toSMul : SMul ℤ H) = (inferInstance : Module ℤ H).toDistribSMul.toSMul := by
  have h : (inferInstance : Module ℤ H) = AddCommGroup.toIntModule H := Subsingleton.elim _ _
  rw [h]
  rfl

attribute [local instance 100] ZSMul.toSMul in
/-- Graded commutativity in degree `2`, cast-free. -/
lemma cup_comm_22 (x y : ↥((SSetCochainComplex ℤ cpZ).homology 2)) :
    cupH' ℤ cpZ 2 2 x y = cupH' ℤ cpZ 2 2 y x := by
  have h := gradedComm ℤ cpZ 2 2 x y
  rw [Subsingleton.elim (Nat.add_comm 2 2) (rfl : 2 + 2 = 2 + 2)] at h
  have h' : ((cupH' ℤ cpZ 2 2) x y) = (-1 : ℤ) ^ (2 * 2) • ((cupH' ℤ cpZ 2 2) y x) := h
  have h1 : (1 : ℤ) • ((cupH' ℤ cpZ 2 2) y x) = ((cupH' ℤ cpZ 2 2) y x) := by
    rw [← zsmulToSMul_eq ↥((SSetCochainComplex ℤ cpZ).homology (2 + 2))]
    exact one_zsmul _
  rw [h', show ((-1 : ℤ) ^ (2 * 2)) = 1 from by norm_num, h1]

attribute [local instance 100] ZSMul.toSMul in
/-- Graded commutativity in degree `4`, cast-free. -/
lemma cup_comm_44 (x y : ↥((SSetCochainComplex ℤ cpZ).homology 4)) :
    cupH' ℤ cpZ 4 4 x y = cupH' ℤ cpZ 4 4 y x := by
  have h := gradedComm ℤ cpZ 4 4 x y
  rw [Subsingleton.elim (Nat.add_comm 4 4) (rfl : 4 + 4 = 4 + 4)] at h
  have h' : ((cupH' ℤ cpZ 4 4) x y) = (-1 : ℤ) ^ (4 * 4) • ((cupH' ℤ cpZ 4 4) y x) := h
  have h1 : (1 : ℤ) • ((cupH' ℤ cpZ 4 4) y x) = ((cupH' ℤ cpZ 4 4) y x) := by
    rw [← zsmulToSMul_eq ↥((SSetCochainComplex ℤ cpZ).homology (4 + 4))]
    exact one_zsmul _
  rw [h', show ((-1 : ℤ) ^ (4 * 4)) = 1 from by norm_num, h1]

/-! ## The products expressed through the factors -/

/-- `a²` is the pullback of `h ⌣ h`. -/
lemma cpa2_eq : cpa2 = pullbackH cpZ cpX cpFst 4 cpHsq :=
  (pullbackH_cupH cpZ cpX cpFst 2 2 cpH cpH).symm

/-- `b²` is the pullback of `h ⌣ h`. -/
lemma cpb2_eq : cpb2 = pullbackH cpZ cpX cpSnd 4 cpHsq :=
  (pullbackH_cupH cpZ cpX cpSnd 2 2 cpH cpH).symm

/-- `ab` is the cross product `h × h`. -/
lemma cpab_eq : cpab = crossH cpX cpX 2 2 cpH cpH := rfl

/-- `a² ⌣ b²` is the cross product `h² × h²`. -/
lemma cpa2_mul_cpb2 : cupH' ℤ cpZ 4 4 cpa2 cpb2 = crossH cpX cpX 4 4 cpHsq cpHsq := by
  rw [cpa2_eq, cpb2_eq]
  rfl

/-- **Middle four interchange**: `(x ⌣ y) ⌣ (x ⌣ y) = (x ⌣ x) ⌣ (y ⌣ y)` for degree-`2`
classes.  This is what identifies `ab ⌣ ab` with `a² ⌣ b²`. -/
lemma cup_interchange_22 (x y : ↥((SSetCochainComplex ℤ cpZ).homology 2)) :
    cupH' ℤ cpZ 4 4 (cupH' ℤ cpZ 2 2 x y) (cupH' ℤ cpZ 2 2 x y)
      = cupH' ℤ cpZ 4 4 (cupH' ℤ cpZ 2 2 x x) (cupH' ℤ cpZ 2 2 y y) := by
  calc cupH' ℤ cpZ 4 4 (cupH' ℤ cpZ 2 2 x y) (cupH' ℤ cpZ 2 2 x y)
      = cupH' ℤ cpZ 2 6 x (cupH' ℤ cpZ 2 4 y (cupH' ℤ cpZ 2 2 x y)) :=
        cup_assoc_224 x y (cupH' ℤ cpZ 2 2 x y)
    _ = cupH' ℤ cpZ 2 6 x (cupH' ℤ cpZ 4 2 (cupH' ℤ cpZ 2 2 y x) y) := by
        rw [← cup_assoc_222 y x y]
    _ = cupH' ℤ cpZ 2 6 x (cupH' ℤ cpZ 4 2 (cupH' ℤ cpZ 2 2 x y) y) := by
        rw [cup_comm_22 y x]
    _ = cupH' ℤ cpZ 2 6 x (cupH' ℤ cpZ 2 4 x (cupH' ℤ cpZ 2 2 y y)) := by
        rw [cup_assoc_222 x y y]
    _ = cupH' ℤ cpZ 4 4 (cupH' ℤ cpZ 2 2 x x) (cupH' ℤ cpZ 2 2 y y) := by
        rw [← cup_assoc_224 x x (cupH' ℤ cpZ 2 2 y y)]

/-! ## The vanishing entries -/

/-- **`a² ⌣ a² = 0`.** -/
lemma cpa2_cpa2_zero : cupH' ℤ cpZ 4 4 cpa2 cpa2 = 0 := by
  have h1 : cupH' ℤ cpZ 4 4 cpa2 cpa2
      = pullbackH cpZ cpX cpFst (4 + 4) (cupH' ℤ cpX 4 4 cpHsq cpHsq) := by
    rw [cpa2_eq]
    exact (pullbackH_cupH cpZ cpX cpFst 4 4 cpHsq cpHsq).symm
  have h2 : pullbackH cpZ cpX cpFst (4 + 4) (cupH' ℤ cpX 4 4 cpHsq cpHsq) = 0 :=
    (congrArg (pullbackH cpZ cpX cpFst (4 + 4)) cpHsq_mul_cpHsq).trans (map_zero _)
  exact h1.trans h2

/-- **`a² ⌣ ab = 0`.** -/
lemma cpa2_cpab_zero : cupH' ℤ cpZ 4 4 cpa2 cpab = 0 := by
  have h1 : cupH' ℤ cpZ 4 4 cpa2 cpab
      = cupH' ℤ cpZ 4 4 (pullbackH cpZ cpX cpFst 4 cpHsq) (crossH cpX cpX 2 2 cpH cpH) := by
    rw [cpa2_eq, cpab_eq]
  have h2 : cupH' ℤ cpZ 4 4 (pullbackH cpZ cpX cpFst 4 cpHsq) (crossH cpX cpX 2 2 cpH cpH)
      = cupH' ℤ cpZ 6 2
          (cupH' ℤ cpZ 4 2 (pullbackH cpZ cpX cpFst 4 cpHsq) cpa) cpb :=
    (cup_assoc_422 (pullbackH cpZ cpX cpFst 4 cpHsq) cpa cpb).symm
  have h3 : cupH' ℤ cpZ 4 2 (pullbackH cpZ cpX cpFst 4 cpHsq) cpa = 0 :=
    ((pullbackH_cupH cpZ cpX cpFst 4 2 cpHsq cpH).symm).trans
      ((congrArg (pullbackH cpZ cpX cpFst (4 + 2)) cpHsq_mul_cpH).trans (map_zero _))
  have h4 : cupH' ℤ cpZ 6 2
      (cupH' ℤ cpZ 4 2 (pullbackH cpZ cpX cpFst 4 cpHsq) cpa) cpb = 0 := by
    rw [h3]
    exact (congrArg (fun f => f cpb) (map_zero (cupH' ℤ cpZ 6 2))).trans rfl
  exact h1.trans (h2.trans h4)

/-- **`ab ⌣ a² = 0`.** -/
lemma cpab_cpa2_zero : cupH' ℤ cpZ 4 4 cpab cpa2 = 0 := by
  rw [cup_comm_44 cpab cpa2]
  exact cpa2_cpab_zero

/-- **`ab ⌣ b² = 0`.** -/
lemma cpab_cpb2_zero : cupH' ℤ cpZ 4 4 cpab cpb2 = 0 := by
  have h1 : cupH' ℤ cpZ 4 4 cpab cpb2
      = cupH' ℤ cpZ 4 4 (crossH cpX cpX 2 2 cpH cpH) (pullbackH cpZ cpX cpSnd 4 cpHsq) := by
    rw [cpab_eq, cpb2_eq]
  have h2 : cupH' ℤ cpZ 4 4 (crossH cpX cpX 2 2 cpH cpH) (pullbackH cpZ cpX cpSnd 4 cpHsq)
      = cupH' ℤ cpZ 2 6 cpa
          (cupH' ℤ cpZ 2 4 cpb (pullbackH cpZ cpX cpSnd 4 cpHsq)) :=
    cup_assoc_224 cpa cpb (pullbackH cpZ cpX cpSnd 4 cpHsq)
  have h3 : cupH' ℤ cpZ 2 4 cpb (pullbackH cpZ cpX cpSnd 4 cpHsq) = 0 :=
    ((pullbackH_cupH cpZ cpX cpSnd 2 4 cpH cpHsq).symm).trans
      ((congrArg (pullbackH cpZ cpX cpSnd (2 + 4)) cpH_mul_cpHsq).trans (map_zero _))
  have h4 : cupH' ℤ cpZ 2 6 cpa
      (cupH' ℤ cpZ 2 4 cpb (pullbackH cpZ cpX cpSnd 4 cpHsq)) = 0 := by
    rw [h3]
    exact map_zero (cupH' ℤ cpZ 2 6 cpa)
  exact h1.trans (h2.trans h4)

/-- **`b² ⌣ ab = 0`.** -/
lemma cpb2_cpab_zero : cupH' ℤ cpZ 4 4 cpb2 cpab = 0 := by
  rw [cup_comm_44 cpb2 cpab]
  exact cpab_cpb2_zero

/-- **`b² ⌣ b² = 0`.** -/
lemma cpb2_cpb2_zero : cupH' ℤ cpZ 4 4 cpb2 cpb2 = 0 := by
  have h1 : cupH' ℤ cpZ 4 4 cpb2 cpb2
      = pullbackH cpZ cpX cpSnd (4 + 4) (cupH' ℤ cpX 4 4 cpHsq cpHsq) := by
    rw [cpb2_eq]
    exact (pullbackH_cupH cpZ cpX cpSnd 4 4 cpHsq cpHsq).symm
  have h2 : pullbackH cpZ cpX cpSnd (4 + 4) (cupH' ℤ cpX 4 4 cpHsq cpHsq) = 0 :=
    (congrArg (pullbackH cpZ cpX cpSnd (4 + 4)) cpHsq_mul_cpHsq).trans (map_zero _)
  exact h1.trans h2

/-! ## The Kronecker pairing of the zero class -/

/-- The Kronecker pairing of the zero class with the fundamental class vanishes. -/
lemma kronH_zero : kronH ℤ cpZ 8 0 cpFund = 0 := by
  rw [map_zero]
  rfl

/-! ## The pairing with the fundamental class -/

/-- **`⟨h², [ℂP²]⟩ = ±1`.** -/
theorem cpHsq_pairing_pm_one :
    kronH ℤ cpX 4 cpHsq cpFund0 = 1 ∨ kronH ℤ cpX 4 cpHsq cpFund0 = -1 :=
  Work.Projective.cp2SelfIntersection_pm_one_uncond

/-- **`⟨a² ⌣ b², c⟩ = 1`**, a diagonal entry of the middle intersection form. -/
theorem cpa2_cpb2_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpa2 cpb2) cpFund = 1 := by
  rw [cpa2_mul_cpb2]
  rw [cpFund_pairing cpHsq cpHsq]
  rcases cpHsq_pairing_pm_one with h | h <;> rw [h] <;> norm_num

/-- **`⟨ab ⌣ ab, c⟩ = 1`**, the central diagonal entry of the middle intersection form. -/
theorem cpab_cpab_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpab cpab) cpFund = 1 := by
  have h : cupH' ℤ cpZ 4 4 cpab cpab = cupH' ℤ cpZ 4 4 cpa2 cpb2 :=
    cup_interchange_22 cpa cpb
  rw [h]
  exact cpa2_cpb2_pairing

/-- **`⟨a² ⌣ a², c⟩ = 0`.** -/
theorem cpa2_cpa2_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpa2 cpa2) cpFund = 0 := by
  rw [cpa2_cpa2_zero, kronH_zero]

/-- **`⟨a² ⌣ ab, c⟩ = 0`.** -/
theorem cpa2_cpab_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpa2 cpab) cpFund = 0 := by
  rw [cpa2_cpab_zero, kronH_zero]

/-- **`⟨ab ⌣ a², c⟩ = 0`.** -/
theorem cpab_cpa2_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpab cpa2) cpFund = 0 := by
  rw [cpab_cpa2_zero, kronH_zero]

/-- **`⟨ab ⌣ b², c⟩ = 0`.** -/
theorem cpab_cpb2_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpab cpb2) cpFund = 0 := by
  rw [cpab_cpb2_zero, kronH_zero]

/-- **`⟨b² ⌣ ab, c⟩ = 0`.** -/
theorem cpb2_cpab_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpb2 cpab) cpFund = 0 := by
  rw [cpb2_cpab_zero, kronH_zero]

/-- **`⟨b² ⌣ b², c⟩ = 0`.** -/
theorem cpb2_cpb2_pairing : kronH ℤ cpZ 8 (cupH' ℤ cpZ 4 4 cpb2 cpb2) cpFund = 0 := by
  rw [cpb2_cpb2_zero, kronH_zero]

end

end Work.Kunneth
