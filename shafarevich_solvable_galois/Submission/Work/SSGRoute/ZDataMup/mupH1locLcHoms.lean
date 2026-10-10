import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Work.SSGRoute.ZDataMup.LT_levelK_kummerClassMap
import Submission.Work.SSGRoute.ZDataMup.mupLocalVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The characters of the locally constant `1`-cocycles of the level-`K` local group

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` finite Galois and
`A` a finite place of `Ω` over `k`.  Write

  `H = decomp k A ⊓ K.fixingSubgroup ≤ G_k`,  `D = ↥(decomp (k := ↥K) A)`

for the level-`K` local subgroup of `G_k` and the level-`K` local decomposition group, joined by
the group isomorphism `decompEquiv_fok : H ≃* D`.

The two objects compared here are

* `H1loc p k Ω K (ZMod p) H`, the locally constant `1`-cohomology of `H` with coefficients in the
  additive group `ZMod p` (a quotient of the locally constant `1`-cocycles by the coboundaries);
* `↥(lcHoms p D)`, the locally constant characters `D →* Multiplicative (ZMod p)`.

**The point of the statement** is that the coefficient module, though an arbitrary
`Gal(K/k)`-module, is acted on *trivially by `H`*: `H ≤ K.fixingSubgroup = ker (res k K)`, so
`res k K g = 1` for `g ∈ H`, and the cocycle condition on `H`,
`a (g * h) = a g + res k K g • a h`, collapses to plain additivity `a (g * h) = a g + a h`,
*independently of the chosen `DistribMulAction (K ≃ₐ[k] K) (ZMod p)` instance*.  Consequently
`H¹_loc(H, ZMod p) ≅ Hom_cont(H, ZMod p) ≅ Hom_cont(D, ZMod p)`: restricting a locally constant
cocycle to `H` determines its class (`toClass_eq_iff_forall_eq`, whose proof uses that the
coboundaries on `H` vanish), and the restriction is exactly a locally constant character of `H`
transported to `D` along `decompEquiv_fok` (a homeomorphism).

The file establishes this identification as a *bijection* `mupH1locChar` which is additive
(additive source group → multiplicative target group), sends `0` to `1`, and satisfies the
computation rule `mupH1locChar (toClass a) (decompEquiv_fok g) = a g` on `H` (the form consumed by
the local Tate/Kummer wiring of the `μ_p` level).  No arithmetic input beyond the triviality of
the action on `H` is used: in particular neither `IsFinPlace k A` nor the finiteness of the
local field enters.

The two ingredients are

* `exists_lcHoms_of_mem`: a locally constant `1`-cocycle on `H` produces a locally constant
  character of `D` (this is `exists_lcHoms_of_cocycle_aux` of `LT_levelK_kummerClassMap` with its
  hypothesis weakened from `K.fixingSubgroup` to `H`);
* `exists_cocycle_of_lcHoms`: conversely every locally constant character of `D` comes from the
  locally constant cocycle `lcHomsExtend` (`LT_levelK_kummerClassMap`).
-/

namespace Work.SSGRoute.ZDataMup

open Classical
open scoped Pointwise

noncomputable section

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
  {A : ValuationSubring Ω}

/-! ## Restriction of local cocycles to a smaller subgroup -/

/-- A locally constant `1`-cocycle on `H'` restricts to a locally constant `1`-cocycle on any
subgroup `H ≤ H'`. -/
lemma mem_lcCocycles_of_le {H H' : Subgroup (Ω ≃ₐ[k] Ω)} (hle : H ≤ H')
    {f : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hf : f ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H') :
    f ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) H := by
  refine ⟨fun g hg h hh => hf.1 g (hle hg) h (hle hh), ?_⟩
  obtain ⟨U, hUo, hU⟩ := hf.2
  exact ⟨U, hUo, fun g hg u hu huH => hU g (hle hg) u hu (hle huH)⟩

/-- The additive reading of `Multiplicative.ofAdd`. -/
private lemma mup_toAdd_ofAdd (x : ZMod p) : (Multiplicative.ofAdd x).toAdd = x := rfl

/-! ## From cocycles to characters -/

/-- **The character of a locally constant `1`-cocycle on `H = decomp k A ⊓ K.fixingSubgroup`.**

On `H` the action of `G_k` on the coefficients factors through `res k K`, which is trivial; hence
`a` is additive on `H` and `g ↦ ofAdd (a g)` is a monoid homomorphism `H →* Multiplicative (ZMod p)`,
locally constant because `a` is.  Transporting it along the homeomorphism `decompEquiv_fok` gives
the required locally constant character of `↥(decomp (k := ↥K) A)`. -/
theorem exists_lcHoms_of_mem (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    ∃ χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)),
      ∀ g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
          Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω)) := by
  classical
  have hHle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
  -- on `H` the cocycle condition is additivity
  have hadd : ∀ g h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      a (((g * h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) : Ω ≃ₐ[k] Ω)) =
        a (g : Ω ≃ₐ[k] Ω) + a (h : Ω ≃ₐ[k] Ω) := by
    intro g h
    have h1 := ha.1 (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2
    rw [res_eq_one_of_le_fixingSubgroup hHle g.2, one_smul] at h1
    exact h1
  have hone : a (1 : Ω ≃ₐ[k] Ω) = 0 := by
    have h1 : a (1 : Ω ≃ₐ[k] Ω) = a (1 : Ω ≃ₐ[k] Ω) + a (1 : Ω ≃ₐ[k] Ω) := by
      have h := hadd 1 1
      simpa using h
    have h2 : a (1 : Ω ≃ₐ[k] Ω) + a (1 : Ω ≃ₐ[k] Ω) = a (1 : Ω ≃ₐ[k] Ω) + 0 := by
      rw [add_zero]
      exact h1.symm
    exact add_left_cancel h2
  have hloc0 : _root_.IsLocallyConstant
      (fun g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) => a (g : Ω ≃ₐ[k] Ω)) :=
    isLocallyConstant_restrict_of_isLocConstOn ha.2
  -- the additive character of `↥H`
  let ψ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →* Multiplicative (ZMod p) :=
    { toFun := fun g => Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω))
      map_one' := by
        show Multiplicative.ofAdd (a (1 : Ω ≃ₐ[k] Ω)) = 1
        rw [hone]
        rfl
      map_mul' := by
        intro g h
        show Multiplicative.ofAdd
            (a (((g * h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) : Ω ≃ₐ[k] Ω))) =
          Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω)) *
            Multiplicative.ofAdd (a (h : Ω ≃ₐ[k] Ω))
        rw [hadd, ofAdd_add] }
  have hψloc : _root_.IsLocallyConstant ψ := hloc0.comp Multiplicative.ofAdd
  -- transport along the homeomorphism `H ≃* decomp ↥K A`
  have hsymm : Continuous ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm :
      ↥(SSGRoute.decomp (k := ↥K) A) →
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
    (Work.SSGRoute.decompEquiv_fok k Ω K A).toEquiv.continuous_symm_iff.2
      (Work.SSGRoute.isHomeomorph_decompEquiv_fok k Ω K A).isOpenMap
  refine ⟨⟨ψ.comp (Work.SSGRoute.decompEquiv_fok k Ω K A).symm.toMonoidHom,
    hψloc.comp_continuous hsymm⟩, fun g => ?_⟩
  show ψ ((Work.SSGRoute.decompEquiv_fok k Ω K A).symm
    (Work.SSGRoute.decompEquiv_fok k Ω K A g)) = Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω))
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- **The character attached to a locally constant `1`-cocycle on `H`**, chosen once and for all
(`exists_lcHoms_of_mem`). -/
noncomputable def mupCocycleChar (A : ValuationSubring Ω)
    (a : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup))) :
    ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  Classical.choose (exists_lcHoms_of_mem (p := p) (k := k) (Ω := Ω) (K := K) A a.1 a.2)

/-- The computation rule of `mupCocycleChar`. -/
lemma mupCocycleChar_spec (A : ValuationSubring Ω)
    (a : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)))
    (g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    (mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A a).1
        (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
      Multiplicative.ofAdd (a.1 (g : Ω ≃ₐ[k] Ω)) :=
  Classical.choose_spec (exists_lcHoms_of_mem (p := p) (k := k) (Ω := Ω) (K := K) A a.1 a.2) g

/-- The character of the zero cocycle is trivial. -/
lemma mupCocycleChar_zero (A : ValuationSubring Ω) :
    mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A 0 = 1 := by
  refine Subtype.ext (MonoidHom.ext fun y => ?_)
  obtain ⟨g, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective y
  rw [mupCocycleChar_spec]
  rfl

/-- **The character of a sum of cocycles is the product of the characters.** -/
lemma mupCocycleChar_add (A : ValuationSubring Ω)
    (a a' : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup))) :
    mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A (a + a') =
      mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A a *
        mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A a' := by
  refine Subtype.ext (MonoidHom.ext fun y => ?_)
  obtain ⟨g, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective y
  rw [Subgroup.coe_mul, MonoidHom.mul_apply, mupCocycleChar_spec, mupCocycleChar_spec,
    mupCocycleChar_spec]
  show Multiplicative.ofAdd ((a + a').1 (g : Ω ≃ₐ[k] Ω)) =
    Multiplicative.ofAdd (a.1 (g : Ω ≃ₐ[k] Ω)) * Multiplicative.ofAdd (a'.1 (g : Ω ≃ₐ[k] Ω))
  rw [show (a + a').1 (g : Ω ≃ₐ[k] Ω) = a.1 (g : Ω ≃ₐ[k] Ω) + a'.1 (g : Ω ≃ₐ[k] Ω) from rfl,
    ofAdd_add]

/-- **Two cocycles with the same class have the same character**: the character only depends on the
values of the cocycle on `H`, and `toClass` identifies cocycles agreeing on `H`. -/
lemma mupCocycleChar_congr (A : ValuationSubring Ω)
    {a a' : ↥(Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup))}
    (h : Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a.1 =
      Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a'.1) :
    mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A a =
      mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A a' := by
  have hagree := (toClass_eq_iff_forall_eq (p := p) (k := k) (Ω := Ω) (K := K) inf_le_right
    a.2 a'.2).mp h
  refine Subtype.ext (MonoidHom.ext fun y => ?_)
  obtain ⟨g, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective y
  rw [mupCocycleChar_spec, mupCocycleChar_spec]
  rw [hagree g g.2]

/-- **The character of the cocycle `lcHomsExtend A hcompat χ` is `χ` itself.** -/
lemma mupCocycleChar_extend (A : ValuationSubring Ω)
    [DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p)]
    (hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A
        ⟨lcHomsExtend (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ,
          lcHomsExtend_mem (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ⟩ = χ := by
  refine Subtype.ext (MonoidHom.ext fun y => ?_)
  obtain ⟨g, rfl⟩ := (Work.SSGRoute.decompEquiv_fok k Ω K A).surjective y
  have h1 : (mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A
        ⟨lcHomsExtend (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ,
          lcHomsExtend_mem (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ⟩).1
        (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
      Multiplicative.ofAdd
        ((χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd) := by
    rw [mupCocycleChar_spec]
    exact congrArg Multiplicative.ofAdd
      (lcHomsExtend_apply_of_mem (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ g.2)
  rw [h1, ofAdd_toAdd]

/-- **Existence of a cocycle with prescribed character** (the converse of
`exists_lcHoms_of_mem`, via the extension `lcHomsExtend`). -/
lemma exists_cocycle_of_lcHoms (A : ValuationSubring Ω)
    (χ : ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A))) :
    ∃ a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      ∀ g : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
        χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A g) =
          Multiplicative.ofAdd (a (g : Ω ≃ₐ[k] Ω)) := by
  letI : DistribMulAction ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p) :=
    Work.SSGRoute.subgroupDistribMulAction k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
  have hcompat : ∀ (h : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := fun _ _ => rfl
  refine ⟨lcHomsExtend (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ,
    lcHomsExtend_mem (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ, fun g => ?_⟩
  rw [lcHomsExtend_apply_of_mem (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ g.2,
    ofAdd_toAdd]

/-! ## The identification `H¹_loc(H, 𝔽_p) ≃ D^∨` -/

/-- A chosen locally constant `1`-cocycle representing a class in the local `H¹` (this is a
choice: `toClass` is surjective onto `H1loc` by construction). -/
noncomputable def mupRepFun (A : ValuationSubring Ω)
    (y : Work.SSGRoute.H1loc p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) : (Ω ≃ₐ[k] Ω) → ZMod p :=
  Classical.choose (Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
    (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y)

/-- The chosen representative is a locally constant `1`-cocycle. -/
lemma mupRepFun_mem (A : ValuationSubring Ω)
    (y : Work.SSGRoute.H1loc p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    mupRepFun (p := p) (k := k) (Ω := Ω) (K := K) A y ∈
      Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
  (Classical.choose_spec (Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
    (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y)).1

/-- The class of the chosen representative is the given class. -/
lemma mupRepFun_spec (A : ValuationSubring Ω)
    (y : Work.SSGRoute.H1loc p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (mupRepFun (p := p) (k := k) (Ω := Ω) (K := K) A y) = y :=
  (Classical.choose_spec (Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
    (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y)).2

/-- **The identification `H¹_loc(H, 𝔽_p) → D^∨`**: the character of a representative cocycle.
It is well defined because two representatives differ by a coboundary, which vanishes on `H`. -/
noncomputable def mupH1locChar (A : ValuationSubring Ω) :
    Work.SSGRoute.H1loc p k Ω K (ZMod p) (SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
      ↥(Work.SSGRoute.lcHoms p ↥(SSGRoute.decomp (k := ↥K) A)) :=
  fun y => mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A
    ⟨mupRepFun (p := p) (k := k) (Ω := Ω) (K := K) A y,
      mupRepFun_mem (p := p) (k := k) (Ω := Ω) (K := K) A y⟩

/-- The computation rule of `mupH1locChar` on the class of a cocycle. -/
lemma mupH1locChar_toClass (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :
    mupH1locChar (p := p) (k := k) (Ω := Ω) (K := K) A
        (Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) =
      mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A ⟨a, ha⟩ :=
  mupCocycleChar_congr (p := p) (k := k) (Ω := Ω) (K := K) A
    (mupRepFun_spec (p := p) (k := k) (Ω := Ω) (K := K) A
      (Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a))

/-- `mupH1locChar` sends the cocycle class of a locally constant cocycle *on `K.fixingSubgroup`*
(hence a fortiori on `H`) to the character computed from its values on `H`. -/
lemma mupH1locChar_toClass_fixing (A : ValuationSubring Ω) (a : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup) :
    mupH1locChar (p := p) (k := k) (Ω := Ω) (K := K) A
        (Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a) =
      mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A
        ⟨a, mem_lcCocycles_of_le inf_le_right ha⟩ :=
  mupCocycleChar_congr (p := p) (k := k) (Ω := Ω) (K := K) A
    (mupRepFun_spec (p := p) (k := k) (Ω := Ω) (K := K) A
      (Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a))

theorem mupH1locLcHoms (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A) :
    ∃ Φ : Work.SSGRoute.H1loc p k Ω K (ZMod p)
          (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
        ↥(Work.SSGRoute.lcHoms p ↥(_root_.SSGRoute.decomp (k := ↥K) A)),
      Function.Bijective Φ ∧
      (∀ x y, Φ (x + y) = Φ x * Φ y) ∧ Φ 0 = 1 ∧
      (∀ (a : (Ω ≃ₐ[k] Ω) → ZMod p),
        a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p) K.fixingSubgroup →
        ∀ g : ↥(_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup),
          ((Φ (Work.SSGRoute.toClass p k Ω K (ZMod p)
              (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)).1
            (Work.SSGRoute.decompEquiv_fok k Ω K A g)).toAdd = a ↑g) := by
  classical
  refine ⟨mupH1locChar (p := p) (k := k) (Ω := Ω) (K := K) A, ?_, ?_, ?_, ?_⟩
  · -- bijectivity
    refine ⟨?_, ?_⟩
    · -- injectivity
      intro y y' hyy
      have hχ : mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A
            ⟨mupRepFun (p := p) (k := k) (Ω := Ω) (K := K) A y,
              mupRepFun_mem (p := p) (k := k) (Ω := Ω) (K := K) A y⟩ =
          mupCocycleChar (p := p) (k := k) (Ω := Ω) (K := K) A
            ⟨mupRepFun (p := p) (k := k) (Ω := Ω) (K := K) A y',
              mupRepFun_mem (p := p) (k := k) (Ω := Ω) (K := K) A y'⟩ := hyy
      rw [← mupRepFun_spec (p := p) (k := k) (Ω := Ω) (K := K) A y,
        ← mupRepFun_spec (p := p) (k := k) (Ω := Ω) (K := K) A y']
      refine (toClass_eq_iff_forall_eq (p := p) (k := k) (Ω := Ω) (K := K) inf_le_right
        (mupRepFun_mem (p := p) (k := k) (Ω := Ω) (K := K) A y)
        (mupRepFun_mem (p := p) (k := k) (Ω := Ω) (K := K) A y')).mpr ?_
      intro g hg
      have h1 := mupCocycleChar_spec (p := p) (k := k) (Ω := Ω) (K := K) A
        ⟨mupRepFun (p := p) (k := k) (Ω := Ω) (K := K) A y,
          mupRepFun_mem (p := p) (k := k) (Ω := Ω) (K := K) A y⟩ ⟨g, hg⟩
      have h2 := mupCocycleChar_spec (p := p) (k := k) (Ω := Ω) (K := K) A
        ⟨mupRepFun (p := p) (k := k) (Ω := Ω) (K := K) A y',
          mupRepFun_mem (p := p) (k := k) (Ω := Ω) (K := K) A y'⟩ ⟨g, hg⟩
      have hval := congrArg (fun χ : ↥(Work.SSGRoute.lcHoms p
          ↥(_root_.SSGRoute.decomp (k := ↥K) A)) =>
        (χ.1 (Work.SSGRoute.decompEquiv_fok k Ω K A ⟨g, hg⟩)).toAdd) hχ
      rw [h1, h2, mup_toAdd_ofAdd, mup_toAdd_ofAdd] at hval
      exact hval
    · -- surjectivity
      intro χ
      letI : DistribMulAction ↥(_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) (ZMod p) :=
        Work.SSGRoute.subgroupDistribMulAction k Ω K (ZMod p)
          (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      have hcompat : ∀ (h : ↥(_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup)) (m : ZMod p),
          h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := fun _ _ => rfl
      refine ⟨Work.SSGRoute.toClass p k Ω K (ZMod p)
          (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup)
          (lcHomsExtend (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ), ?_⟩
      rw [mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A _
        (lcHomsExtend_mem (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ)]
      exact mupCocycleChar_extend (p := p) (k := k) (Ω := Ω) (K := K) A hcompat χ
  · -- additivity
    intro x y
    obtain ⟨a, ha, rfl⟩ := Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
      (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) x
    obtain ⟨b, hb, rfl⟩ := Work.SSGRoute.toClass_surjective p k Ω K (ZMod p)
      (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) y
    have hsum : Work.SSGRoute.toClass p k Ω K (ZMod p)
          (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) a +
        Work.SSGRoute.toClass p k Ω K (ZMod p)
          (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) b =
        Work.SSGRoute.toClass p k Ω K (ZMod p)
          (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) (a + b) :=
      (Work.SSGRoute.toClass_add p k Ω K (ZMod p)
        (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) ha hb).symm
    rw [hsum, mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A (a + b)
        (add_mem ha hb),
      mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A a ha,
      mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A b hb]
    exact mupCocycleChar_add (p := p) (k := k) (Ω := Ω) (K := K) A ⟨a, ha⟩ ⟨b, hb⟩
  · -- `Φ 0 = 1`
    have h0 : Work.SSGRoute.toClass p k Ω K (ZMod p)
        (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) (0 : (Ω ≃ₐ[k] Ω) → ZMod p) = 0 :=
      (Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p)
        (_root_.SSGRoute.decomp k A ⊓ K.fixingSubgroup) (Submodule.zero_mem _)).mpr
        (Submodule.zero_mem _)
    rw [← h0]
    rw [mupH1locChar_toClass (p := p) (k := k) (Ω := Ω) (K := K) A 0 (Submodule.zero_mem _)]
    exact mupCocycleChar_zero (p := p) (k := k) (Ω := Ω) (K := K) A
  · -- the computation rule on cocycles over `K.fixingSubgroup`
    intro a ha g
    rw [mupH1locChar_toClass_fixing (p := p) (k := k) (Ω := Ω) (K := K) A a ha]
    rw [mupCocycleChar_spec, mup_toAdd_ofAdd]

end

end Work.SSGRoute.ZDataMup
