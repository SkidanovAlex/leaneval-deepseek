/-
Copyright (c) 2025. All rights reserved.

# Proper solutions from a Grunwald–Wang datum

This file proves the *logical* content of Proposition 11 of

* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*,
  arXiv:math/9809211,

namely: **if the prescribed local behaviour can be realized globally, then the resulting solution
is proper.**

Let `S` be the abstract setting of an embedding problem with abelian kernel
(`Work.Properness.Setup`), so that `1 → A → E → Q → 1` with `A = ker π` abelian and
`ρ : H ↠ Q` the map to be lifted.  Fix

* a lift `ψ₀` (a plain solution, `π ∘ ψ₀ = ρ`),
* subgroups `T i ≤ H_K` of `H_K = ker ρ` (in the arithmetic situation the decomposition groups of
  primes splitting completely in the field cut out by `ρ`) and
* homomorphisms `φ i : T i →* A` prescribing the local behaviour on `T i`,

and suppose that a global `1`-cocycle `x ∈ Z¹(H, A)` realizing (over `ψ₀`) the prescribed
differences exists:

`x(t) = φ i t · (ψ₀ t)⁻¹`  for all `t ∈ T i`.

This is exactly `Setup.GrunwaldWangDatum ψ₀ T hT φ`, the conclusion of the Grunwald–Wang step.
Then the *global* lift `ψ = x · ψ₀` (`Work.Properness.exists_lift_of_mulFun`) satisfies
`ψ t = φ i t` for all `t ∈ T i`, so `ψ(T i)` is the range of `φ i`.

Consequently, if the local images generate the whole kernel, `⨆ i, (φ i).range = ⊤`, then
`ψ(H_K) = A` and `ψ` is surjective
(`Work.Properness.isProper_iff_map_HK_eq_A`, `Work.Properness.isProper_of_iSup_map_eq`): the
embedding problem has a **proper** solution in the sense of the paper ("eigentliche Lösung"),
i.e. `Setup.HasProperLift`.

## Main declarations

* `Work.Properness.liftOfDatum_apply_eq` — the lift `x · ψ₀` of a Grunwald–Wang datum takes the
  prescribed value `φ i t` on `T i`;
* `Work.Properness.map_T_liftOfDatum` — likewise `(T i).map ψ = (φ i).range` (inside `A`);
* `Work.Properness.exists_properLift_of_datum` — the requested theorem.
-/
import Mathlib
import Submission.Work.Properness.Defs
import Submission.Work.Properness.exists_lift_mulFun
import Submission.Work.Properness.isProper_of_iSup_map_eq
import Submission.Work.Properness.isProper_iff_map_HK_eq_A
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

-- The requested statement binds `{u v w : Universe}`.  `Universe` is not a Lean 4 keyword, so it is
-- an implicitly bound variable and the statement only elaborates with `autoImplicit` enabled; this
-- is exactly what the sibling file `Submission/Work/Properness/isProper_of_iSup_map_eq.lean` does,
-- and it is why the dummy binders `u v w` (which do not occur in the statement) are present.
set_option autoImplicit true
set_option linter.unusedVariables false

namespace Work.Properness

/-- **The lift of a Grunwald–Wang datum takes the prescribed local values.**

Let `ψ₀` be a lift, let `x ∈ Z¹(H, A)` be a cocycle whose values on `T i ≤ H_K` are the prescribed
differences `φ i - ψ₀|_{T i}`, and let `ψ = x · ψ₀` be the lift attached to `x` and `ψ₀`
(`Work.Properness.exists_lift_of_mulFun`).  Then for every `t ∈ T i`,

`ψ t = φ i t`.

Indeed, in `E`,

`ψ t = x(t) · ψ₀ t = φ i t · (ψ₀ t)⁻¹ · ψ₀ t = φ i t`. -/
theorem liftOfDatum_apply_eq {S : Setup} {ι : Type*} {ψ₀ : S.Lift}
    {T : ι → Subgroup S.H} (hT : ∀ i, T i ≤ S.HK) {φ : ∀ i, T i →* S.A}
    {x : GroupCohomology.Z1 S.H (Additive S.A)}
    (hx : ∀ (i : ι) (t : T i),
      (x.1 (t : S.H)).toMul = φ i t * (S.liftValue ψ₀ ⟨(t : S.H), hT i t.2⟩)⁻¹)
    {ψ : S.Lift} (hψ : ∀ h : S.H, ψ.1 h = S.mulFun x.1 ψ₀.1 h)
    (i : ι) (t : T i) : ψ.1 (t : S.H) = ((φ i t : S.A) : S.E) := by
  rw [hψ (t : S.H)]
  show (((x.1 (t : S.H)).toMul : S.A) : S.E) * ψ₀.1 (t : S.H) = ((φ i t : S.A) : S.E)
  rw [hx i t]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.coe_liftValue]
  group

/-- **The images of the `T i` under the lift of a Grunwald–Wang datum.**

With the notation of `Work.Properness.liftOfDatum_apply_eq`, the lift `ψ = x · ψ₀` maps `T i`
onto the range of `φ i` (viewed as a subgroup of `A = ker π`, hence of `E`):

`(T i).map ψ = (φ i).range`.

This is the local information that feeds into the properness criterion: it turns the hypothesis
`⨆ i, (φ i).range = ⊤` on the prescribed local maps into the hypothesis `⨆ i, (T i).map ψ = A` of
`Work.Properness.isProper_of_iSup_map_eq`. -/
theorem map_T_liftOfDatum {S : Setup} {ι : Type*} {ψ₀ : S.Lift}
    {T : ι → Subgroup S.H} (hT : ∀ i, T i ≤ S.HK) {φ : ∀ i, T i →* S.A}
    {x : GroupCohomology.Z1 S.H (Additive S.A)}
    (hx : ∀ (i : ι) (t : T i),
      (x.1 (t : S.H)).toMul = φ i t * (S.liftValue ψ₀ ⟨(t : S.H), hT i t.2⟩)⁻¹)
    {ψ : S.Lift} (hψ : ∀ h : S.H, ψ.1 h = S.mulFun x.1 ψ₀.1 h)
    (i : ι) : (T i).map ψ.1 = (φ i).range.map (S.A).subtype := by
  ext e
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, hte⟩
    refine ⟨φ i ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, ?_⟩
    show ((φ i ⟨t, ht⟩ : S.A) : S.E) = e
    rw [← hte, liftOfDatum_apply_eq hT hx hψ i ⟨t, ht⟩]
  · rintro ⟨a, ⟨t, ht⟩, hae⟩
    refine ⟨t, t.2, ?_⟩
    rw [liftOfDatum_apply_eq hT hx hψ i t, ht]
    exact hae

/-- **A Grunwald–Wang datum with generating local images yields a proper solution.**

This is the requested statement.  From the datum one gets the lift `ψ = x · ψ₀` of
`Work.Properness.exists_lift_of_mulFun`, whose images of the `T i` are the ranges of the `φ i`
(`Work.Properness.map_T_liftOfDatum`).  The hypothesis `⨆ i, (φ i).range = ⊤` therefore gives

`A = (⊤ : Subgroup A).map A.subtype = (⨆ i, (φ i).range).map A.subtype
   = ⨆ i, (T i).map ψ ≤ H_K.map ψ`,

while `H_K.map ψ ≤ A` always holds (`Setup.map_HK_le_A`).  Hence `H_K.map ψ = A` and
`ψ` is surjective by `Work.Properness.isProper_iff_map_HK_eq_A`, i.e. `Setup.HasProperLift`
holds. -/
theorem exists_properLift_of_datum {u v w : Universe} {S : Work.Properness.Setup.{u, v, w}} {ι : Type*} [Fintype ι] (ψ₀ : S.Lift) (T : ι → Subgroup S.H) (hT : ∀ i, T i ≤ S.HK) (φ : ∀ i, T i →* S.A) (hdat : S.GrunwaldWangDatum ψ₀ T hT φ) (hgen : (⨆ i, (φ i).range) = ⊤) : S.HasProperLift := by
  obtain ⟨x, hx⟩ := hdat
  obtain ⟨ψ, hψ⟩ := Work.Properness.exists_lift_of_mulFun ψ₀ x
  refine ⟨ψ, ?_⟩
  rw [Work.Properness.isProper_iff_map_HK_eq_A_aux ψ]
  refine le_antisymm (S.map_HK_le_A ψ) ?_
  have hA : S.A = (⊤ : Subgroup S.A).map (S.A).subtype := by
    rw [← MonoidHom.range_eq_map]
    exact (Subgroup.range_subtype (S.A)).symm
  calc S.A = (⊤ : Subgroup S.A).map (S.A).subtype := hA
    _ = ((⨆ i, (φ i).range)).map (S.A).subtype := by rw [hgen]
    _ = ⨆ i, ((φ i).range).map (S.A).subtype :=
        Subgroup.map_iSup (S.A).subtype (fun i => (φ i).range)
    _ = ⨆ i, (T i).map ψ.1 :=
        iSup_congr (fun i => (map_T_liftOfDatum hT hx hψ i).symm)
    _ ≤ S.HK.map ψ.1 := iSup_le (fun i => Subgroup.map_mono (hT i))

end Work.Properness
