import Mathlib
import Submission.Work.WingbergRoute.CupProduct
import Submission.Work.WingbergRoute.cup_leibniz
import Submission.Work.WingbergRoute.cup_isLocallyConstant
import Submission.Work.WingbergRoute.cup_wellDefined
import Submission.Work.ShafarevichKoch.Cohomology3

/-!
# `Work.WingbergRoute.CupProductCohomology` -- the cup product of continuous cohomology

`Submission/Work/ConCohomology/` builds the continuous cohomology `H¹`, `H²(Γ,M)` and
`Submission/Work/ShafarevichKoch/Cohomology3` adds `H³`; **neither has a cup product**, and neither
has Mathlib.  `Submission/Work/WingbergRoute/CupProduct` supplies the *cochain-level* formulas
(`cup11Fun`, `cup21Fun`, `cup12Fun`, ...) and `cup_leibniz` / `cup_isLocallyConstant` /
`cup_wellDefined` the three facts they satisfy (the Leibniz rule, local constancy of all the
cochain-level products, and the descent conditions).  This module assembles them into the two
pairings

```
Work.WingbergRoute.cupH1 : H¹(G,A) →+ H¹(G,B) →+ H²(G,C)
Work.WingbergRoute.cupH2 : H²(G,A) →+ H¹(G,B) →+ H³(G,C)
```

for a `G`-equivariant additive pairing `f : A →+ B →+ C`, together with their `𝔽₂` specialisations
(`cupH1_zmodTwo`, `cupH2_zmodTwo`) used by the Kummer/norm-residue pairing, and the characterising
formulas on classes of cocycles (`cupH1_mk_mk`, `cupH2_mk_mk`).

The proof is the standard one: the Leibniz rule makes the product of two cocycles a cocycle
(`cupZ11`, `cupZ21`), and the two descent identities make the product of a cocycle with a coboundary
a coboundary, so the product descends to cohomology (`cupZ1H1`, `cupZ2H1`, `cupH1`, `cupH2`).

## Why this belongs to the Wingberg route

Wingberg's duality, and more generally the `S = ∅` case of the Shafarevich--Salle--Koch relation
bound, is a statement about the *norm-residue pairing*

```
H¹(G_∅, 𝔽₂) × H¹(G_∅, 𝔽₂) → H²(G_∅, 𝔽₂),      H²(G_∅, 𝔽₂) × H¹(G_∅, 𝔽₂) → H³(G_∅, 𝔽₂)
```

together with the local duality theorems; the cup product is the missing arrow on this side.
`Submission/Work/ShafarevichKoch/README.md` §24.2 records the absence of a cup product as the
missing piece of the relation count.

## Main declarations

* `Work.WingbergRoute.cup11Co`, `cup21Co` (bundled cochains) and the pointwise helpers;
* `Work.WingbergRoute.mem_Z2_of_d2Fun_eq_zero`, `mem_Z3_of_d3Fun_eq_zero`,
  `H2_mk_eq_zero_of_forall_eq_d1`, `H3_mk_eq_zero_of_forall_eq_d2` (the coboundary criteria);
* `Work.WingbergRoute.cupZ11 : Z¹ →+ Z¹ →+ Z²`, `cupZ21 : Z² →+ Z¹ →+ Z³` (on cocycles);
* `Work.WingbergRoute.cupZ1H1 : Z¹ →+ (H¹ →+ H²)`, `cupZ2H1 : Z² →+ (H¹ →+ H³)`;
* ★ `Work.WingbergRoute.cupH1`, ★ `Work.WingbergRoute.cupH2` (the pairings);
* `Work.WingbergRoute.cupH1_mk_mk`, `cupH2_mk_mk` (`[simp]`, the values on cocycle classes);
* `Work.WingbergRoute.zmodTwoMul`, `isEquivariantBilin_zmodTwoMul`, `cupH1_zmodTwo`,
  `cupH2_zmodTwo` (the `𝔽₂` specialisations).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open scoped Classical

noncomputable section

namespace Work.WingbergRoute

open Work.ConCohomology Work.ShafarevichKoch

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type*} [AddCommGroup A] [DistribMulAction G A] [IsDiscreteGModule G A]
variable {B : Type*} [AddCommGroup B] [DistribMulAction G B] [IsDiscreteGModule G B]
variable {C : Type*} [AddCommGroup C] [DistribMulAction G C] [IsDiscreteGModule G C]

/-! ### Elementary helpers -/

/-- The class map `Z² → H²` as an additive homomorphism. -/
def H2class : Z2 G C →+ H2 G C := QuotientAddGroup.mk' (B2' G C)

/-- The class map `Z³ → H³` as an additive homomorphism. -/
def H3class : Z3 G C →+ H3 G C := QuotientAddGroup.mk' (B3' G C)

lemma H2class_apply (z : Z2 G C) : H2class (G := G) z = H2.mk z := rfl

lemma H3class_apply (z : Z3 G C) : H3class (G := G) z = H3.mk z := rfl

@[simp] lemma H2_mk_add (z w : Z2 G C) : H2.mk (z + w) = H2.mk z + H2.mk w := by
  rw [← H2class_apply (G := G) (z + w), ← H2class_apply (G := G) z,
    ← H2class_apply (G := G) w]
  exact map_add (H2class (G := G)) z w

@[simp] lemma H2_mk_zero' : H2.mk (0 : Z2 G C) = 0 := H2.mk_zero

@[simp] lemma H3_mk_zero : H3.mk (0 : Z3 G C) = 0 := by
  rw [← H3class_apply (G := G) (0 : Z3 G C)]
  exact map_zero (H3class (G := G))

@[simp] lemma H3_mk_add (z w : Z3 G C) : H3.mk (z + w) = H3.mk z + H3.mk w := by
  rw [← H3class_apply (G := G) (z + w), ← H3class_apply (G := G) z,
    ← H3class_apply (G := G) w]
  exact map_add (H3class (G := G)) z w

/-! ### Bundled cochains and pointwise helpers -/

/-- The cup product of two `1`-cochains, bundled as a `2`-cochain. -/
def cup11Co (f : A →+ B →+ C) (a : Cochain1 G A) (b : Cochain1 G B) : Cochain2 G C :=
  ⟨cup11Fun f (a : G → A) (b : G → B), (cup_isLocallyConstant (G := G) f).2.1 a b⟩

/-- The cup product of a `2`-cochain with a `1`-cochain, bundled as a `3`-cochain. -/
def cup21Co (f : A →+ B →+ C) (α : Cochain2 G A) (b : Cochain1 G B) : Cochain3 G C :=
  ⟨cup21Fun f (α : G × G → A) (b : G → B), (cup_isLocallyConstant (G := G) f).2.2.1 α b⟩

@[simp] lemma cup11Co_coe (f : A →+ B →+ C) (a : Cochain1 G A) (b : Cochain1 G B) :
    (cup11Co f a b : G × G → C) = cup11Fun f (a : G → A) (b : G → B) := rfl

@[simp] lemma cup21Co_coe (f : A →+ B →+ C) (α : Cochain2 G A) (b : Cochain1 G B) :
    (cup21Co f α b : G × G × G → C) = cup21Fun f (α : G × G → A) (b : G → B) := rfl

/-- A `2`-cochain whose differential vanishes is a `2`-cocycle. -/
lemma mem_Z2_of_d2Fun_eq_zero (z : Cochain2 G C) (h : d2Fun (M := C) (z : G × G → C) = 0) :
    z ∈ Z2 G C := by
  rw [mem_Z2, isCocycle2_iff_d2Fun]
  exact h

/-- A `3`-cochain whose differential vanishes is a `3`-cocycle. -/
lemma mem_Z3_of_d3Fun_eq_zero (z : Cochain3 G C) (h : d3Fun (M := C) (z : G × G × G → C) = 0) :
    z ∈ Z3 G C := by
  rw [mem_Z3]
  ext p
  exact congrFun h p

lemma mem_B2_of_forall_eq_d1 (z : Cochain2 G C) (κ : Cochain1 G C)
    (h : ∀ p : G × G, (z : G × G → C) p = d1Fun (M := C) (κ : G → C) p) : z ∈ B2 G C := by
  refine ⟨κ, ?_⟩
  ext p
  exact (h p).symm

lemma mem_B3_of_forall_eq_d2 (z : Cochain3 G C) (κ : Cochain2 G C)
    (h : ∀ p : G × G × G, (z : G × G × G → C) p = d2Fun (M := C) (κ : G × G → C) p) :
    z ∈ B3 G C := by
  refine ⟨κ, ?_⟩
  ext p
  exact (h p).symm

lemma H2_mk_eq_zero_of_forall_eq_d1 (z : Z2 G C) (κ : Cochain1 G C)
    (h : ∀ p : G × G, (z : G × G → C) p = d1Fun (M := C) (κ : G → C) p) : H2.mk z = 0 := by
  rw [H2.mk_eq_zero_iff, mem_B2']
  exact mem_B2_of_forall_eq_d1 _ _ h

lemma H2_mk_eq_zero_of_forall_eq_neg_d1 (z : Z2 G C) (κ : Cochain1 G C)
    (h : ∀ p : G × G, (z : G × G → C) p = -d1Fun (M := C) (κ : G → C) p) : H2.mk z = 0 := by
  rw [H2.mk_eq_zero_iff, mem_B2']
  refine ⟨-κ, ?_⟩
  ext p
  rw [map_neg]
  show (-(d1Hom G C κ : Cochain2 G C) : G × G → C) p = (z : G × G → C) p
  rw [h p]
  rfl

lemma H3_mk_eq_zero_of_forall_eq_d2 (z : Z3 G C) (κ : Cochain2 G C)
    (h : ∀ p : G × G × G, (z : G × G × G → C) p = d2Fun (M := C) (κ : G × G → C) p) :
    H3.mk z = 0 := by
  have h0 : (0 : H3 G C) = H3.mk (0 : Z3 G C) := rfl
  rw [h0, H3.mk_eq_mk_iff, mem_B3']
  have hz : ((z - 0 : Z3 G C) : Cochain3 G C) = (z : Cochain3 G C) := by rw [sub_zero]
  rw [hz]
  exact mem_B3_of_forall_eq_d2 _ _ h

/-! ### The cup product on cocycles -/

/-- The cup product on cocycles: `Z¹ × Z¹ → Z²`. -/
def cupZ11 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    Z1 G A →+ Z1 G B →+ Z2 G C where
  toFun a :=
    { toFun := fun b =>
        ⟨cup11Co f (a : Cochain1 G A) (b : Cochain1 G B), by
          refine mem_Z2_of_d2Fun_eq_zero _ ?_
          rw [cup11Co_coe]
          rw [(cup_leibniz (G := G) f hf).1 (a : G → A) (b : G → B)]
          have ha : d1Fun (M := A) (a : G → A) = 0 :=
            (isCocycle1_iff_d1Fun (M := A) (a : G → A)).mp (mem_Z1.mp a.2)
          have hb : d1Fun (M := B) (b : G → B) = 0 :=
            (isCocycle1_iff_d1Fun (M := B) (b : G → B)).mp (mem_Z1.mp b.2)
          rw [ha, hb]
          ext p
          obtain ⟨σ, τ, ρ⟩ := p
          simp [cup21Fun, cup12Fun]
        ⟩
      map_zero' := by
        apply Subtype.ext
        ext p
        obtain ⟨σ, τ⟩ := p
        show f (((a : Cochain1 G A) : G → A) σ) (σ • (((0 : Z1 G B) : Cochain1 G B) : G → B) τ) = 0
        simp
      map_add' := by
        intro b b'
        apply Subtype.ext
        ext p
        obtain ⟨σ, τ⟩ := p
        show f (((a : Cochain1 G A) : G → A) σ) (σ • (((b + b' : Z1 G B) : Cochain1 G B) : G → B) τ) =
          f (((a : Cochain1 G A) : G → A) σ) (σ • ((b : Cochain1 G B) : G → B) τ) +
            f (((a : Cochain1 G A) : G → A) σ) (σ • ((b' : Cochain1 G B) : G → B) τ)
        simp only [AddSubgroup.coe_add, LocallyConstant.add_apply, smul_add, map_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    apply Subtype.ext
    ext p
    obtain ⟨σ, τ⟩ := p
    show f ((((0 : Z1 G A) : Cochain1 G A) : G → A) σ) (σ • ((b : Cochain1 G B) : G → B) τ) = 0
    simp
  map_add' := by
    intro a a'
    apply AddMonoidHom.ext
    intro b
    apply Subtype.ext
    ext p
    obtain ⟨σ, τ⟩ := p
    show f ((((a + a' : Z1 G A) : Cochain1 G A) : G → A) σ)
        (σ • ((b : Cochain1 G B) : G → B) τ) =
      f (((a : Cochain1 G A) : G → A) σ) (σ • ((b : Cochain1 G B) : G → B) τ) +
        f (((a' : Cochain1 G A) : G → A) σ) (σ • ((b : Cochain1 G B) : G → B) τ)
    simp only [AddSubgroup.coe_add, LocallyConstant.add_apply, AddMonoidHom.add_apply, map_add]

/-- The cup product on cocycles: `Z² × Z¹ → Z³`. -/
def cupZ21 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    Z2 G A →+ Z1 G B →+ Z3 G C where
  toFun z :=
    { toFun := fun b =>
        ⟨cup21Co f (z : Cochain2 G A) (b : Cochain1 G B), by
          refine mem_Z3_of_d3Fun_eq_zero _ ?_
          rw [cup21Co_coe]
          exact (cup_wellDefined (G := G) f hf).2.2.1 z b
        ⟩
      map_zero' := by
        apply Subtype.ext
        ext p
        obtain ⟨σ, τ, ρ⟩ := p
        show f (((z : Cochain2 G A) : G × G → A) (σ, τ))
            (((σ * τ) • (((0 : Z1 G B) : Cochain1 G B) : G → B) ρ)) = 0
        simp
      map_add' := by
        intro b b'
        apply Subtype.ext
        ext p
        obtain ⟨σ, τ, ρ⟩ := p
        show f (((z : Cochain2 G A) : G × G → A) (σ, τ))
            (((σ * τ) • (((b + b' : Z1 G B) : Cochain1 G B) : G → B) ρ)) =
          f (((z : Cochain2 G A) : G × G → A) (σ, τ))
            (((σ * τ) • ((b : Cochain1 G B) : G → B) ρ)) +
            f (((z : Cochain2 G A) : G × G → A) (σ, τ))
              (((σ * τ) • ((b' : Cochain1 G B) : G → B) ρ))
        simp only [AddSubgroup.coe_add, LocallyConstant.add_apply, smul_add, map_add] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro b
    apply Subtype.ext
    ext p
    obtain ⟨σ, τ, ρ⟩ := p
    show f ((((0 : Z2 G A) : Cochain2 G A) : G × G → A) (σ, τ))
        (((σ * τ) • ((b : Cochain1 G B) : G → B) ρ)) = 0
    simp
  map_add' := by
    intro z z'
    apply AddMonoidHom.ext
    intro b
    apply Subtype.ext
    ext p
    obtain ⟨σ, τ, ρ⟩ := p
    show f ((((z + z' : Z2 G A) : Cochain2 G A) : G × G → A) (σ, τ))
        (((σ * τ) • ((b : Cochain1 G B) : G → B) ρ)) =
      f (((z : Cochain2 G A) : G × G → A) (σ, τ))
          (((σ * τ) • ((b : Cochain1 G B) : G → B) ρ)) +
        f (((z' : Cochain2 G A) : G × G → A) (σ, τ))
          (((σ * τ) • ((b : Cochain1 G B) : G → B) ρ))
    simp only [AddSubgroup.coe_add, LocallyConstant.add_apply, AddMonoidHom.add_apply, map_add]

/-! ### The cup product on cohomology -/

/-- The cup product `Z¹ × Z¹ → H²`, by passing to classes in the second variable. -/
def cupZ11H (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) (a : Z1 G A) :
    Z1 G B →+ H2 G C :=
  (H2class (G := G)).comp (cupZ11 f hf a)

/-- The cup product `Z² × Z¹ → H³`, by passing to classes in the second variable. -/
def cupZ21H (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) (z : Z2 G A) :
    Z1 G B →+ H3 G C :=
  (H3class (G := G)).comp (cupZ21 f hf z)

@[simp] lemma cupZ11H_apply (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (a : Z1 G A) (b : Z1 G B) : cupZ11H f hf a b = H2.mk (cupZ11 f hf a b) := rfl

@[simp] lemma cupZ21H_apply (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (z : Z2 G A) (b : Z1 G B) : cupZ21H f hf z b = H3.mk (cupZ21 f hf z b) := rfl

/-- The second-variable descent for `cupZ11H`: `B¹(G,B)` acts trivially. -/
lemma cupZ11H_ker (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) (a : Z1 G A) :
    B1' G B ≤ (cupZ11H f hf a).ker := by
  intro b hb
  rw [mem_B1'] at hb
  obtain ⟨b₀, hb₀⟩ := hb
  show cupZ11H f hf a b = 0
  rw [cupZ11H_apply]
  obtain ⟨κ, hκ⟩ := (cup_wellDefined (G := G) f hf).2.1 a b₀
  refine H2_mk_eq_zero_of_forall_eq_neg_d1 _ κ ?_
  intro p
  have hbc : ((b : Z1 G B) : Cochain1 G B) = d0Hom G B b₀ := hb₀.symm
  show cup11Fun f (((a : Z1 G A) : Cochain1 G A)) (((b : Z1 G B) : Cochain1 G B)) p =
    -d1Fun (M := C) (κ : G → C) p
  rw [hbc]
  exact congrFun hκ p

/-- The second-variable descent for `cupZ21H`: `B¹(G,B)` acts trivially. -/
lemma cupZ21H_ker (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) (z : Z2 G A) :
    B1' G B ≤ (cupZ21H f hf z).ker := by
  intro b hb
  rw [mem_B1'] at hb
  obtain ⟨b₀, hb₀⟩ := hb
  show cupZ21H f hf z b = 0
  rw [cupZ21H_apply]
  obtain ⟨κ, hκ⟩ := (cup_wellDefined (G := G) f hf).2.2.2.2 z b₀
  refine H3_mk_eq_zero_of_forall_eq_d2 _ κ ?_
  intro p
  have hbc : ((b : Z1 G B) : Cochain1 G B) = d0Hom G B b₀ := hb₀.symm
  show cup21Fun f (((z : Z2 G A) : Cochain2 G A)) (((b : Z1 G B) : Cochain1 G B)) p =
    d2Fun (M := C) (κ : G × G → C) p
  rw [hbc]
  exact congrFun hκ p

/-- The cup product, descended in the second variable: `Z¹ → (H¹ → H²)`. -/
def cupZ1H1 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    Z1 G A →+ (H1 G B →+ H2 G C) where
  toFun a := QuotientAddGroup.lift (B1' G B) (cupZ11H f hf a) (cupZ11H_ker (G := G) f hf a)
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    refine QuotientAddGroup.induction_on x (fun b => ?_)
    have h0 : cupZ11 f hf (0 : Z1 G A) = 0 := map_zero _
    simp only [QuotientAddGroup.lift_mk, AddMonoidHom.zero_apply, cupZ11H_apply, h0, H2_mk_zero']
  map_add' := by
    intro a a'
    apply AddMonoidHom.ext
    intro x
    refine QuotientAddGroup.induction_on x (fun b => ?_)
    have h0 : cupZ11 f hf (a + a') = cupZ11 f hf a + cupZ11 f hf a' := map_add _ a a'
    simp only [QuotientAddGroup.lift_mk, AddMonoidHom.add_apply, cupZ11H_apply, h0, H2_mk_add]

/-- The cup product, descended in the second variable: `Z² → (H¹ → H³)`. -/
def cupZ2H1 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    Z2 G A →+ (H1 G B →+ H3 G C) where
  toFun z := QuotientAddGroup.lift (B1' G B) (cupZ21H f hf z) (cupZ21H_ker (G := G) f hf z)
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    refine QuotientAddGroup.induction_on x (fun b => ?_)
    have h0 : cupZ21 f hf (0 : Z2 G A) = 0 := map_zero _
    simp only [QuotientAddGroup.lift_mk, AddMonoidHom.zero_apply, cupZ21H_apply, h0, H3_mk_zero]
  map_add' := by
    intro z z'
    apply AddMonoidHom.ext
    intro x
    refine QuotientAddGroup.induction_on x (fun b => ?_)
    have h0 : cupZ21 f hf (z + z') = cupZ21 f hf z + cupZ21 f hf z' := map_add _ z z'
    simp only [QuotientAddGroup.lift_mk, AddMonoidHom.add_apply, cupZ21H_apply, h0, H3_mk_add]

/-- The first-variable descent for `cupZ1H1`: `B¹(G,A)` acts trivially. -/
lemma cupZ1H1_ker (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    B1' G A ≤ (cupZ1H1 (G := G) f hf).ker := by
  intro a ha
  rw [mem_B1'] at ha
  obtain ⟨a₀, ha₀⟩ := ha
  show cupZ1H1 f hf a = 0
  apply AddMonoidHom.ext
  intro x
  refine QuotientAddGroup.induction_on x (fun b => ?_)
  simp only [QuotientAddGroup.lift_mk, AddMonoidHom.zero_apply, cupZ11H_apply]
  -- (the remaining goal is the vanishing of the cup product of a coboundary)
  obtain ⟨κ, hκ⟩ := (cup_wellDefined (G := G) f hf).1 a₀ b
  refine H2_mk_eq_zero_of_forall_eq_d1 _ κ ?_
  intro p
  have hac : ((a : Z1 G A) : Cochain1 G A) = d0Hom G A a₀ := ha₀.symm
  show cup11Fun f (((a : Z1 G A) : Cochain1 G A)) (((b : Z1 G B) : Cochain1 G B)) p =
    d1Fun (M := C) (κ : G → C) p
  rw [hac]
  exact congrFun hκ p

/-- The first-variable descent for `cupZ2H1`: `B²(G,A)` acts trivially. -/
lemma cupZ2H1_ker (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    B2' G A ≤ (cupZ2H1 (G := G) f hf).ker := by
  intro z hz
  rw [mem_B2'] at hz
  obtain ⟨γ, hγ⟩ := hz
  show cupZ2H1 f hf z = 0
  apply AddMonoidHom.ext
  intro x
  refine QuotientAddGroup.induction_on x (fun b => ?_)
  simp only [QuotientAddGroup.lift_mk, AddMonoidHom.zero_apply, cupZ21H_apply]
  obtain ⟨κ, hκ⟩ := (cup_wellDefined (G := G) f hf).2.2.2.1 γ b
  refine H3_mk_eq_zero_of_forall_eq_d2 _ κ ?_
  intro p
  have hzc : ((z : Z2 G A) : Cochain2 G A) = d1Hom G A γ := hγ.symm
  show cup21Fun f (((z : Z2 G A) : Cochain2 G A)) (((b : Z1 G B) : Cochain1 G B)) p =
    d2Fun (M := C) (κ : G × G → C) p
  rw [hzc]
  exact congrFun hκ p

/-- **The cup product `H¹(G,A) × H¹(G,B) → H²(G,C)`.** -/
noncomputable def cupH1 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    H1 G A →+ H1 G B →+ H2 G C :=
  QuotientAddGroup.lift (B1' G A) (cupZ1H1 f hf) (cupZ1H1_ker (G := G) f hf)

/-- **The cup product `H²(G,A) × H¹(G,B) → H³(G,C)`.** -/
noncomputable def cupH2 (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) :
    H2 G A →+ H1 G B →+ H3 G C :=
  QuotientAddGroup.lift (B2' G A) (cupZ2H1 f hf) (cupZ2H1_ker (G := G) f hf)

/-- The cup product on cocycle classes, in the second variable. -/
lemma cupZ1H1_mk (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) (a : Z1 G A)
    (b : Z1 G B) : cupZ1H1 f hf a (H1.mk b) = H2.mk (cupZ11 f hf a b) := by
  show (QuotientAddGroup.lift (B1' G B) (cupZ11H f hf a) (cupZ11H_ker (G := G) f hf a))
    (QuotientAddGroup.mk b) = H2.mk (cupZ11 f hf a b)
  rw [QuotientAddGroup.lift_mk, cupZ11H_apply]

/-- The cup product on cocycle classes, in the second variable. -/
lemma cupZ2H1_mk (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f) (z : Z2 G A)
    (b : Z1 G B) : cupZ2H1 f hf z (H1.mk b) = H3.mk (cupZ21 f hf z b) := by
  show (QuotientAddGroup.lift (B1' G B) (cupZ21H f hf z) (cupZ21H_ker (G := G) f hf z))
    (QuotientAddGroup.mk b) = H3.mk (cupZ21 f hf z b)
  rw [QuotientAddGroup.lift_mk, cupZ21H_apply]

@[simp] lemma cupH1_mk_mk (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (a : Z1 G A) (b : Z1 G B) :
    cupH1 f hf (H1.mk a) (H1.mk b) = H2.mk (cupZ11 f hf a b) := by
  show (QuotientAddGroup.lift (B1' G A) (cupZ1H1 f hf) (cupZ1H1_ker (G := G) f hf))
    (QuotientAddGroup.mk a) (QuotientAddGroup.mk b) = H2.mk (cupZ11 f hf a b)
  rw [QuotientAddGroup.lift_mk]
  exact cupZ1H1_mk f hf a b

@[simp] lemma cupH2_mk_mk (f : A →+ B →+ C) (hf : IsEquivariantBilin (G := G) f)
    (z : Z2 G A) (b : Z1 G B) :
    cupH2 f hf (H2.mk z) (H1.mk b) = H3.mk (cupZ21 f hf z b) := by
  show (QuotientAddGroup.lift (B2' G A) (cupZ2H1 f hf) (cupZ2H1_ker (G := G) f hf))
    (QuotientAddGroup.mk z) (QuotientAddGroup.mk b) = H3.mk (cupZ21 f hf z b)
  rw [QuotientAddGroup.lift_mk]
  exact cupZ2H1_mk f hf z b


/-! ## The `𝔽₂` cup products -/

section ZModTwo

variable [DistribMulAction G (ZMod 2)] [IsDiscreteGModule G (ZMod 2)]

/-- Multiplication, as an additive pairing `𝔽₂ × 𝔽₂ → 𝔽₂`. -/
def zmodTwoMul : ZMod 2 →+ ZMod 2 →+ ZMod 2 where
  toFun a :=
    { toFun := fun b => a * b
      map_zero' := by simp
      map_add' := by intro b b'; simp [mul_add] }
  map_zero' := by
    ext b
    simp
  map_add' := by
    intro a a'
    ext b
    simp [add_mul]

/-- Multiplication is equivariant for a trivial `G`-action on `𝔽₂`. -/
theorem isEquivariantBilin_zmodTwoMul (htriv : ∀ (σ : G) (x : ZMod 2), σ • x = x) :
    IsEquivariantBilin (G := G) zmodTwoMul := by
  intro σ a b
  show zmodTwoMul (σ • a) (σ • b) = σ • zmodTwoMul a b
  rw [htriv σ a, htriv σ b]
  exact (htriv σ (zmodTwoMul a b)).symm

/-- **The `𝔽₂` cup product `H¹ × H¹ → H²`.** -/
noncomputable def cupH1_zmodTwo (htriv : ∀ (σ : G) (x : ZMod 2), σ • x = x) :
    H1 G (ZMod 2) →+ H1 G (ZMod 2) →+ H2 G (ZMod 2) :=
  cupH1 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv)

/-- **The `𝔽₂` cup product `H² × H¹ → H³`** -- the norm-residue/Kummer leg of Wingberg duality. -/
noncomputable def cupH2_zmodTwo (htriv : ∀ (σ : G) (x : ZMod 2), σ • x = x) :
    H2 G (ZMod 2) →+ H1 G (ZMod 2) →+ H3 G (ZMod 2) :=
  cupH2 zmodTwoMul (isEquivariantBilin_zmodTwoMul htriv)

end ZModTwo

end Work.WingbergRoute
