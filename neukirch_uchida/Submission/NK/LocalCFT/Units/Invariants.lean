import Submission.NK.LocalCFT.Basic
import Submission.NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion
import Submission.NK.LocalCFT.Units.not_hasUnboundedTowerRank_of_commutative
import Submission.NK.LocalReciprocity.Invariants

/-!
# The units of a `p`-adic field, and the invariants of `G_κ^{ab}`

The local input of the proof of Neukirch–Uchida is that the residue characteristic of a `p`-adic
field `κ` and the absolute degree `[κ : ℚ_p]` are group-theoretic invariants of `G_κ`.  The
sibling area `Submission/Work/LocalReciprocity/Invariants.lean` transfers the
`NK.LocalAnabelian` invariants (`HasFrattiniRank`, `HasUnboundedTowerRank`,
`HasPTorsionAbelianization`, `ResidueCharDetectedBy`) along an isomorphism
`κˣ^{∧} ≃* G_κ^{ab}`; what has to be supplied is the arithmetic of the unit group `κˣ`.

## The structure of `κˣ`

For a `p`-adic field `κ` with residue field of cardinality `q`,

  `κˣ ≅ ℤ × μ_{q-1}(κ) × U¹`,   `U¹ = 1 + 𝔪 ≅ ℤ_p^{[κ : ℚ_p]}`        (`p` odd; there is a small
  `p = 2` variant),

so that the profinite completion is `κˣ^{∧} ≅ Ẑ × μ_{q-1}(κ) × ℤ_p^{[κ:ℚ_p]}`.  Consequently

* `HasFrattiniRank p (1 + [κ:ℚ_p] + ε) (κˣ^{∧})` where `ε ∈ {0,1}` is `1` exactly when `ζ_p ∈ κ`
  (this is the "power-class count" `|κˣ/(κˣ)^p| = p^{1+[κ:ℚ_p]+ε}`; in this workspace it is proved
  by the sibling area `Submission/Work/LocalInputs/` as
  `NK.LocalInputs.hasFrattiniRank_completionUnits_adicCompletion`, from its single named input
  `NK.LocalInputs.LocalFieldInputs.principal_units_card`);
* `HasPTorsionAbelianization p (κˣ^{∧})` iff `ζ_p ∈ κ` (the `p`-torsion of `κˣ^{∧}` is `μ_p(κ)`);
* **and `κˣ^{∧}` has *bounded* `ℓ`-tower rank for every prime `ℓ`** — see below.

## The tower-rank invariant cannot see the residue characteristic on `G_κ^{ab}`

The invariant `NK.LocalAnabelian.HasUnboundedTowerRank ℓ` detects the residue characteristic of
`κ` on the *full* group `G_κ` (Ivanov, arXiv:1309.3046, Lemma 3.12: the justification is that the
maximal pro-`p` quotient of `G_κ` is a Demushkin group of rank `≥ 2`, whose open subgroups have
arbitrarily large `p`-rank, whereas for `ℓ ≠ p` the wild inertia is pro-`p`).

It *cannot* do so on the abelianisation `G_κ^{ab}`: that group is commutative, and for a commutative
group `G` and any finite-index subgroup `V ≤ G` the number of index-`ℓ` subgroups of `V` is bounded
by that of `G` (a subgroup of a `d`-generated abelian group is `d`-generated), so

  `NK.LocalCFT.Units.not_hasUnboundedTowerRank_of_commutative`:
  `¬ HasUnboundedTowerRank ℓ G` for every commutative `G` and every `ℓ`.

Consequently the hypothesis `hFull` (respectively `hOther`) of the transfer theorems in
`NK.LocalReciprocity.Invariants` is *unsatisfiable* for `F` a `p`-adic field — its unit group is
commutative — and the theorem `NK.LocalReciprocity.residueCharDetectedBy_of_datum` has a false
hypothesis.  The theorems below record this in the form used downstream:
`NK.LocalCFT.not_residueCharDetectedBy_AbGal_of_datum` says that
`ResidueCharDetectedBy p (G_κ^{ab})` is *false*, so the residue characteristic must be read off from
the full group `G_κ` (as the sibling area `Submission/Work/LocalInputs/` does, from
`HasUnboundedTowerRank` of `Gal(K'/κ)` itself), not from `G_κ^{ab}`.

## Main results

* `NK.LocalCFT.hasFrattiniRank_AbGal_of_datum` — the `p`-rank of `G_κ^{ab}` is that of `κˣ^{∧}`
  (the *positive* transfer, with the arithmetic of `κˣ` as the input);
* `NK.LocalCFT.hasPTorsionAbelianization_AbGal_of_datum` — the `p`-torsion of `G_κ^{ab}` is that
  of `κˣ^{∧}` (i.e. `μ_p(κ)`);
* `NK.LocalCFT.not_hasUnboundedTowerRank_AbGal_of_datum` and
  `NK.LocalCFT.not_residueCharDetectedBy_AbGal_of_datum` — the *negative* results.
-/

open scoped Classical

namespace NK.LocalCFT

universe u v

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The `p`-rank of `G_F^{ab}` is the `p`-rank of the profinite completion of `Fˣ`.**  This is the
*positive* transfer: the input is the arithmetic of the unit group `Fˣ` (for `F` a `p`-adic field
this is the power-class count `|Fˣ/(Fˣ)^p| = p^{1+[F:ℚ_p]+ε}`, discharged in
`Submission/Work/LocalInputs/`). -/
theorem hasFrattiniRank_AbGal_of_datum (D : ArtinReciprocity F F') {p r : ℕ}
    (h : NK.LocalAnabelian.HasFrattiniRank p r (NK.LocalReciprocity.completionUnits F)) :
    NK.LocalAnabelian.HasFrattiniRank p r (AbGal F F') :=
  NK.LocalReciprocity.hasFrattiniRank_maxAbelian_of_completion
    (Classical.choice (NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D)) h

/-- **The `p`-torsion of `G_F^{ab}` is the `p`-torsion of `Fˣ^{∧}`** (for a `p`-adic field: the
`p`-torsion of `κˣ^{∧}` is `μ_p(κ)`, non-trivial exactly when `ζ_p ∈ κ`). -/
theorem hasPTorsionAbelianization_AbGal_of_datum (D : ArtinReciprocity F F') {p : ℕ}
    (h : NK.LocalAnabelian.HasPTorsionAbelianization p (NK.LocalReciprocity.completionUnits F)) :
    NK.LocalAnabelian.HasPTorsionAbelianization p (AbGal F F') :=
  NK.LocalAnabelian.hasPTorsionAbelianization_congr
    (Classical.choice (NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D)) h

/-- **The tower-rank invariant vanishes on a commutative group.**  For a commutative group the
number of index-`ℓ` subgroups of a finite-index subgroup is bounded by that of the ambient group, so
the tower ranks are bounded. -/
theorem not_hasUnboundedTowerRank_AbGal_of_completion (Φ : NK.LocalReciprocity.completionUnits F ≃* AbGal F F')
    (ℓ : ℕ) (hcomm : ∀ x y : NK.LocalReciprocity.completionUnits F, x * y = y * x) :
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (AbGal F F') :=
  fun h => NK.LocalCFT.Units.not_hasUnboundedTowerRank_of_commutative _
    ℓ hcomm ((NK.LocalAnabelian.hasUnboundedTowerRank_congr_iff Φ ℓ).mpr h)

/-- **The tower-rank invariant vanishes on `G_F^{ab}`**, given the reciprocity isomorphism
`Fˣ^{∧} ≃* G_F^{ab}` and commutativity of `Fˣ^{∧}`. -/
theorem not_hasUnboundedTowerRank_AbGal_of_datum (D : ArtinReciprocity F F') (ℓ : ℕ)
    (hcomm : ∀ x y : NK.LocalReciprocity.completionUnits F, x * y = y * x) :
    ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (AbGal F F') :=
  not_hasUnboundedTowerRank_AbGal_of_completion
    (Classical.choice (NK.LocalCFT.Completion.exists_mulEquiv_unitsCompletion D)) ℓ hcomm

/-- **The residue characteristic cannot be detected on `G_F^{ab}`.**  Since the tower-rank invariant
vanishes on the commutative group `G_F^{ab}` (for all `ℓ`), `ResidueCharDetectedBy p (G_F^{ab})` is
false for every prime `p`. -/
theorem not_residueCharDetectedBy_AbGal_of_datum (D : ArtinReciprocity F F') {p : ℕ}
    (hp : p.Prime) (hcomm : ∀ x y : NK.LocalReciprocity.completionUnits F, x * y = y * x) :
    ¬ NK.LocalAnabelian.ResidueCharDetectedBy p (AbGal F F') :=
  fun h => not_hasUnboundedTowerRank_AbGal_of_datum D p hcomm ((h p hp).mpr rfl)

end NK.LocalCFT
