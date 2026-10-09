import Submission.NK.LocalCFT.Units.Invariants
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The multiplicative structure of a `p`-adic field, and its invariant consequences

This module owns the *shape* of the unit group of a `p`-adic field, the first half of deliverable 4.
For `κ` a `p`-adic field, local field theory gives

  `κˣ ≅ ℤ × μ(κ) × U¹`,   `U¹ = 1 + 𝔪 ≅ ℤ_p^{[κ : ℚ_p]}`   (`p` odd; there is a small `p = 2`
  variant),

hence for the profinite completion

  `κˣ^{∧} ≅ Ẑ × μ(κ) × ℤ_p^{[κ : ℚ_p]}`,

with the following two group-theoretic traces:

* the `p`-Frattini rank is `1 + [κ:ℚ_p] + ε`, where `ε = 1` exactly when `ζ_p ∈ κ`
  (this is the *power-class count* `|κˣ/(κˣ)^p| = p^{1+[κ:ℚ_p]+ε}`; equivalently, the number of
  index-`p` subgroups of `κˣ^{∧}` is `(p^{1+[κ:ℚ_p]+ε}-1)/(p-1)`);
* the `p`-torsion of the abelianisation is `μ_p(κ)`, non-trivial exactly when `ζ_p ∈ κ`.

`NK.LocalCFT.UnitsStructure p κ` records exactly these two traces (not the isomorphism of groups,
which would require a model for `Ẑ × μ × ℤ_p^d`); it is the input that the transfers of
`NK.LocalCFT.Units.Invariants` consume.
`NK.LocalCFT.Units.Invariants` transfers them along `NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion`,
and the theorem `NK.LocalCFT.hasFrattiniRank_AbGal_of_unitsStructure` below is the resulting
statement about `G_κ^{ab}` in terms of `UnitsStructure` alone.

**Discharge.**  Classically the shape is proved by the `p`-adic logarithm
(`U¹ ≅ 𝔪 ≅ ℤ_p^{[κ:ℚ_p]}`) together with the structure of the residue field; in this workspace the
`frattini` field is *derived* by the sibling area `Submission/Work/LocalInputs/` from its single
arithmetic input `NK.LocalInputs.LocalFieldInputs.principal_units_card`
(Serre, *Local Fields*, Ch. II §5), and for `κ = ℚ_p` the commons proves the count outright.  The
`p = 2` case needs `μ_4 ⊆ κ` handled separately.  See `README.md` §5.

## Main definitions

* `NK.LocalCFT.UnitsStructure p κ` — the shape of `κˣ^{∧}`, in its two invariant traces;
* `NK.LocalCFT.hasFrattiniRank_AbGal_of_unitsStructure`,
  `NK.LocalCFT.hasPTorsionAbelianization_iff_AbGal_of_unitsStructure` — the consequences for
  `G_κ^{ab}`.
-/

open scoped Classical

namespace NK.LocalCFT

universe u v

/-- **The multiplicative structure of a `p`-adic field, as seen by its invariants.**
`d = [κ : ℚ_p]` is the absolute degree and `ε ∈ {0,1}` records whether `ζ_p ∈ κ`; the two fields say
that the profinite completion `κˣ^{∧}` has `p`-Frattini rank `1 + d + ε` and that its `p`-torsion is
non-trivial exactly for `ε = 1`.  See the module docstring for how this is discharged. -/
structure UnitsStructure (p : ℕ) (κ : Type u) [Field κ] where
  /-- `p` is prime. -/
  hp : p.Prime
  /-- the absolute degree `[κ : ℚ_p]`. -/
  d : ℕ
  /-- `ε = 1` iff `ζ_p ∈ κ`. -/
  ε : ℕ
  /-- `ε ∈ {0,1}`. -/
  hε : ε ≤ 1
  /-- the `p`-Frattini rank of `κˣ^{∧}` is `1 + [κ:ℚ_p] + ε`. -/
  hasFrattiniRank : NK.LocalAnabelian.HasFrattiniRank p (1 + d + ε)
    (NK.LocalReciprocity.completionUnits κ)
  /-- the `p`-torsion of `κˣ^{∧}` is non-trivial exactly when `ε = 1`. -/
  hasPTorsion_iff : (ε = 1) ↔
    NK.LocalAnabelian.HasPTorsionAbelianization p (NK.LocalReciprocity.completionUnits κ)

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
variable {p : ℕ}

/-- **The `p`-rank of `G_F^{ab}` from the shape of `Fˣ`.**  This is the composite of
`NK.LocalCFT.hasFrattiniRank_AbGal_of_datum` with the structure of the unit group, i.e. the
statement that `G_κ^{ab}` has `p`-Frattini rank `1 + [κ:ℚ_p] + ε`. -/
theorem hasFrattiniRank_AbGal_of_unitsStructure (D : ArtinReciprocity F F')
    (h : UnitsStructure p F) :
    NK.LocalAnabelian.HasFrattiniRank p (1 + h.d + h.ε) (AbGal F F') :=
  hasFrattiniRank_AbGal_of_datum D h.hasFrattiniRank

/-- **The `p`-torsion of `G_F^{ab}` from the shape of `Fˣ`**: it is non-trivial exactly when
`ζ_p ∈ F`, i.e. exactly when `ε = 1`. -/
theorem hasPTorsionAbelianization_iff_AbGal_of_unitsStructure (D : ArtinReciprocity F F')
    (h : UnitsStructure p F) :
    (h.ε = 1) ↔ NK.LocalAnabelian.HasPTorsionAbelianization p (AbGal F F') := by
  exact h.hasPTorsion_iff.trans (NK.LocalAnabelian.hasPTorsionAbelianization_congr_iff
    (Classical.choice (NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D)) p)

end NK.LocalCFT
