import Mathlib
import Submission.NK.NUV2.LCLeaves
import Submission.NK.LocalDecomposition.All
import Submission.NK.HassePrinciple.All
import Submission.NK.BrauerTwist.All
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup

/-!
# Route B: vocabulary for the non-circular proof of Neukirch's containment

This module fixes the vocabulary in which the non-circular route (Route B) to
`NK.NUV2.DecompContainment` is stated.  The objects are

* `NK.BrauerHasse.H2Profinite p V` — the profinite cohomology `H²(V, Z/p)` of a closed
  subgroup `V ≤ Gal(K'/K)`, defined as the colimit of the level cohomologies
  (`Submission/Work/BrauerHasse/Profinite.lean`);
* its localisation `NK.BrauerHasse.H2Profinite.loc p V x A` at a place `A` of `K'` over a finite
  prime of `K`, which is the restriction to the decomposition group `V ⊓ D_A`
  (`NK.LocalDecomposition.loc_eq_res`).

The route applies Albert–Brauer–Hasse–Noether only at **open** levels `V ≤ Gal(K'/K)` (fixed
fields of number fields), where it is the classical theorem `Br(F)[p] ↪ ∏_v Br(F_v)[p]`; the
coefficients are the *trivial* `Z/p` because every subgroup occurring fixes a primitive `p`-th
root of unity, so that the cyclotomic twist `μ_p` is trivial on its levels.

## Main definitions

* `rootFix ζ` — the fixing subgroup in `Gal(K'/K)` of a root `ζ ∈ K'`;
* `IsMuOpen ζ V` — `V` is open and fixes `ζ`;
* `InOrbit V A A'` — `A'` is a `V`-conjugate of `A`;
* `IsLive p V A` — `A` is `V`-live, i.e. `H²(V ⊓ D_A, Z/p) ≠ 0`;
* `res` — the restriction `H²(U, Z/p) → H²(V, Z/p)` for `V ≤ U`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The fixing subgroup of a root `ζ ∈ K'`** in `Gal(K'/K)`. -/
noncomputable def rootFix (ζ : K') : Subgroup Gal(K'/K) :=
  IntermediateField.fixingSubgroup (IntermediateField.adjoin K ({ζ} : Set K'))

/-- `V` is a `μ_p`-open subgroup: open in `Gal(K'/K)` and fixing the primitive `p`-th root
`ζ ∈ K'`.  These are the levels at which Albert–Brauer–Hasse–Noether is applied. -/
def IsMuOpen (ζ : K') (V : Subgroup Gal(K'/K)) : Prop :=
  IsOpen (V : Set Gal(K'/K)) ∧ V ≤ rootFix (K := K) ζ

/-- `A'` is a `V`-conjugate of the place `A`. -/
def InOrbit (V : Subgroup Gal(K'/K)) (A A' : ValuationSubring K') : Prop :=
  ∃ v ∈ V, v • A = A'

/-- **`A` is `V`-live**: the local cohomology `H²(V ⊓ D_A, Z/p)` of the decomposition group at `A`
is non-trivial, exhibited by a non-zero class. -/
def IsLive (p : ℕ) (V : Subgroup Gal(K'/K)) (A : ValuationSubring K') : Prop :=
  ∃ x : NK.BrauerHasse.H2Profinite p (V ⊓ NK.BrauerHasse.stabSubgroup A), x ≠ 0

/-- Liveness gives non-triviality. -/
theorem IsLive.nontrivial {p : ℕ} {V : Subgroup Gal(K'/K)} {A : ValuationSubring K'}
    (h : IsLive p V A) :
    Nontrivial (NK.BrauerHasse.H2Profinite p (V ⊓ NK.BrauerHasse.stabSubgroup A)) :=
  let ⟨x, hx⟩ := h; ⟨x, 0, hx⟩

/-- The restriction map `H²(U, Z/p) → H²(V, Z/p)` for an inclusion `V ≤ U` of closed subgroups;
this is `NK.LocalDecomposition.H2Profinite.res` and it *is* the localisation at a place when
`V = U ⊓ D_A` (`NK.LocalDecomposition.loc_eq_res`). -/
noncomputable def res (p : ℕ) {V U : Subgroup Gal(K'/K)} (h : V ≤ U) :
    NK.BrauerHasse.H2Profinite p U → NK.BrauerHasse.H2Profinite p V :=
  NK.LocalDecomposition.H2Profinite.res p h

@[simp]
theorem res_ofLevel (p : ℕ) {V U : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') (a : NK.BrauerHasse.LevelH2 p U L) :
    res (K := K) (K' := K') p h (NK.BrauerHasse.H2Profinite.ofLevel L a) =
      NK.BrauerHasse.H2Profinite.ofLevel L
        ((NK.BrauerHasse.H2.map (NK.BrauerHasse.levelInclHom h L)) a) :=
  NK.LocalDecomposition.H2Profinite.res_ofLevel p h L a


/-- **The cardinality squeeze of Route B.**  If `H²(V, Z/p)` has exactly `p` elements and two of its
classes have local components `(≠ 0, 0)` and `(0, ≠ 0)` at the places `A₁, A₂`, then this data is
inconsistent: both classes are non-zero, so (the group having order `p`, hence being cyclic of order
`p`) the second is a non-zero scalar multiple of the first, and the localisation is `ZMod p`-linear,
so the component of the second at `A₁` is a non-zero multiple of the non-zero component of the first.

This is the counting step that closes Claim U: it shows that two live places must be `V`-conjugate
(otherwise the Hasse surjectivity at an open level produces exactly such a pair of classes). -/
theorem squeeze_H2Profinite (p : ℕ) (hp : p.Prime) {V : Subgroup Gal(K'/K)}
    (hcard : Nat.card (NK.BrauerHasse.H2Profinite p V) = p)
    (A₁ A₂ : NK.BrauerHasse.OverFinitePrime K K')
    (y₁ y₂ : NK.BrauerHasse.H2Profinite p V)
    (hy₁ : NK.BrauerHasse.H2Profinite.loc p V y₁ A₁ ≠ 0)
    (hy₂' : NK.BrauerHasse.H2Profinite.loc p V y₂ A₁ = 0)
    (hy₁' : NK.BrauerHasse.H2Profinite.loc p V y₁ A₂ = 0)
    (hy₂ : NK.BrauerHasse.H2Profinite.loc p V y₂ A₂ ≠ 0) : False := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- rewrite the local components at `A₁` as restrictions (the local type is definitionally a
  -- `H2Profinite`, but only there is the `ZMod p`-module structure an instance)
  have hD₁ : V ⊓ NK.BrauerHasse.stabSubgroup A₁.1 ≤ V := inf_le_left
  have hres_zero : NK.LocalDecomposition.H2Profinite.res p hD₁
      (0 : NK.BrauerHasse.H2Profinite p V) = 0 := by
    show NK.LocalDecomposition.H2Profinite.res p hD₁
      (NK.BrauerHasse.H2Profinite.ofLevel (⊥ : FiniteGaloisIntermediateField K K')
        (0 : NK.BrauerHasse.LevelH2 p V ⊥)) = 0
    rw [NK.LocalDecomposition.H2Profinite.res_ofLevel, map_zero]
    exact NK.BrauerHasse.ofLevel_zero ⊥
  have hres₁ : NK.LocalDecomposition.H2Profinite.res p hD₁ y₁ ≠ 0 := by
    rw [← NK.LocalDecomposition.loc_eq_res p V A₁ y₁]; exact hy₁
  have hres₂ : NK.LocalDecomposition.H2Profinite.res p hD₁ y₂ = 0 := by
    rw [← NK.LocalDecomposition.loc_eq_res p V A₁ y₂]; exact hy₂'
  -- both classes are non-zero
  have hy₁0 : y₁ ≠ 0 := fun h0 => hres₁ (by rw [h0, hres_zero])
  have hy₂0 : y₂ ≠ 0 := fun h0 => hy₂ (by rw [h0, NK.BrauerHasse.H2Profinite.loc_zero])
  -- the additive order of `y₁` is `p`
  have hdvd : addOrderOf y₁ ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    (NK.BrauerHasse.H2Profinite.nsmul_p_eq_zero p V y₁)
  have hord : addOrderOf y₁ = p := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hy₁0
    · exact h
  -- hence `y₁` generates the whole group, and `y₂` is a multiple of `y₁`
  haveI : Finite ↥(AddSubgroup.zmultiples y₁) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hord]; exact hp.ne_zero)
  have htop : AddSubgroup.zmultiples y₁ = ⊤ :=
    AddSubgroup.eq_top_of_card_eq _ (by rw [Nat.card_zmultiples, hord, hcard])
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (by rw [htop]; exact AddSubgroup.mem_top y₂)
  have hlamy : (n : ZMod p) • y₁ = y₂ := by
    rw [← hn, Int.cast_smul_eq_zsmul (ZMod p) n y₁]
  have hlamne : (n : ZMod p) ≠ 0 := fun h0 => hy₂0 (by rw [← hlamy, h0, zero_smul])
  -- the restriction is compatible with the `ZMod p`-action
  have hlin : ∀ μ : ZMod p, NK.LocalDecomposition.H2Profinite.res p hD₁ (μ • y₁) =
      μ • NK.LocalDecomposition.H2Profinite.res p hD₁ y₁ := by
    intro μ
    rw [← ZMod.natCast_zmod_val μ, Nat.cast_smul_eq_nsmul (ZMod p) μ.val y₁]
    have hns : ∀ k : ℕ, NK.LocalDecomposition.H2Profinite.res p hD₁ (k • y₁) =
        k • NK.LocalDecomposition.H2Profinite.res p hD₁ y₁ := by
      intro k
      induction k with
      | zero => rw [zero_nsmul, zero_nsmul, hres_zero]
      | succ k ih => rw [succ_nsmul, NK.BrauerHasse.H2Profinite.res_add, ih, ← succ_nsmul]
    rw [hns μ.val, Nat.cast_smul_eq_nsmul (ZMod p) μ.val
      (NK.LocalDecomposition.H2Profinite.res p hD₁ y₁)]
  -- the component of `y₂` at `A₁` is a non-zero multiple of the non-zero component of `y₁`
  have hzero : (n : ZMod p) • NK.LocalDecomposition.H2Profinite.res p hD₁ y₁ = 0 := by
    rw [← hlin, hlamy, hres₂]
  rcases smul_eq_zero.mp hzero with h | h
  · exact hlamne h
  · exact hres₁ h

end NK.NUV2.LC.RouteB
