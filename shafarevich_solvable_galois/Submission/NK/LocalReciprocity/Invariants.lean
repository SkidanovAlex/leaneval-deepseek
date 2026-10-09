import Submission.NK.LocalReciprocity.Prelude
import Submission.NK.LocalReciprocity.Reciprocity
import Submission.NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Group-theoretic invariants of `G_κ^{ab}` read off from local reciprocity

The local input to the proof of Neukirch–Uchida is that the *residue characteristic* of a `p`-adic
field `κ` is a group-theoretic invariant of `G_κ = Gal(κ̄/κ)` (Ivanov, arXiv:1309.3046, Lemma 3.12;
Shimizu, arXiv:2009.10431, Lemma 2.1), and that the `p`-adic rank of `G_κ^{ab}` determines
`[κ : ℚ_p]` (together with whether `ζ_p ∈ κ`).

The module `Submission.NK.LocalAnabelian.Basic` defines the relevant invariants of an abstract
group: `numIndexSubgroups`, `HasFrattiniRank p r G` (the `p`-rank of the maximal elementary
abelian quotient of `G`), `HasUnboundedTowerRank ℓ G` (unbounded `ℓ`-Frattini rank over the open
subgroups `V` with `G/V` a pro-`ℓ` group) and `ResidueCharDetectedBy p G`.

The *transfer* of these invariants along the reciprocity isomorphism
`κˣ^{∧} ≃* G_κ^{ab}` is pure group theory and is proved here
(`hasFrattiniRank_maxAbelian_of_completion`, `hasUnboundedTowerRank_maxAbelian_of_completion`,
`residueCharDetectedBy_of_completion`).  The remaining input is then purely arithmetic: the
structure of the profinite completion of the unit group `κˣ ≅ ℤ × μ(κ) × (1+𝔪)`, namely

* `1 + 𝔪 ≅ ℤ_p ^ [κ : ℚ_p]` (via the `p`-adic logarithm), so that `κˣ^{∧}` has
  `ℤ_p`-rank `1 + [κ : ℚ_p]` together with one extra `ℤ/p` "generator" coming from the `p`-torsion
  `μ_p(κ)`, which is non-trivial exactly when `ζ_p ∈ κ`;
* every finite quotient of `1 + 𝔪` is a `p`-group, so that the `ℓ`-rank of `κˣ` is *bounded* for
  `ℓ ≠ p`, while for `ℓ = p` the subgroups `1 + 𝔪^{p^k}` have `p`-Frattini rank tending to
  infinity.

These two arithmetic inputs are the hypotheses `hFull` and `hOther` of the theorems below; they
are *not* proved here (this needs the theory of the principal units of a `p`-adic field).
-/

open scoped Classical
open CategoryTheory

namespace NK.LocalReciprocity

universe u v

noncomputable section

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- The underlying group of the profinite completion of `Fˣ`. -/
abbrev completionUnits (F : Type u) [Field F] : Type u :=
  ((ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Fˣ)).toProfinite.toTop)

/-- **Transfer of the `p`-rank.**  If the reciprocity isomorphism `Fˣ^{∧} ≃* G_F^{ab}` holds and
the completion of `Fˣ` has `p`-Frattini rank `r`, then so does the abelianised absolute Galois
group `G_F^{ab} = Gal(F^{ab}/F)`. -/
theorem hasFrattiniRank_maxAbelian_of_completion
    (Φ : completionUnits F ≃* ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')))
    {p r : ℕ} (h : NK.LocalAnabelian.HasFrattiniRank p r (completionUnits F)) :
    NK.LocalAnabelian.HasFrattiniRank p r
      ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')) :=
  NK.LocalAnabelian.hasFrattiniRank_congr Φ h

/-- **Transfer of the unbounded-tower-rank predicate.** -/
theorem hasUnboundedTowerRank_maxAbelian_of_completion
    (Φ : completionUnits F ≃* ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')))
    {ℓ : ℕ} (h : NK.LocalAnabelian.HasUnboundedTowerRank ℓ (completionUnits F)) :
    NK.LocalAnabelian.HasUnboundedTowerRank ℓ
      ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')) :=
  NK.LocalAnabelian.hasUnboundedTowerRank_congr Φ h

/-- **Residue characteristic detection.**  If the reciprocity isomorphism
`Fˣ^{∧} ≃* G_F^{ab}` holds, if the `ℓ`-tower rank of `Fˣ^{∧}` is unbounded exactly for
`ℓ = p`, then `p` is the unique prime detected by the tower-rank invariant of `G_F^{ab}`.

The two arithmetic hypotheses are the standard facts about the units of a `p`-adic field recalled
in the module docstring (`hOther` is boundedness of the `ℓ`-rank for `ℓ ≠ p`, `hFull` is
unboundedness for `ℓ = p`). -/
theorem residueCharDetectedBy_of_completion
    (Φ : completionUnits F ≃* ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')))
    {p : ℕ} (hp : p.Prime)
    (hFull : NK.LocalAnabelian.HasUnboundedTowerRank p (completionUnits F))
    (hOther : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (completionUnits F)) :
    NK.LocalAnabelian.ResidueCharDetectedBy p
      ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')) := by
  intro ℓ hℓ
  constructor
  · intro h
    by_contra hne
    exact hOther ℓ hℓ hne
      (NK.LocalAnabelian.hasUnboundedTowerRank_congr Φ.symm h)
  · rintro rfl
    exact hasUnboundedTowerRank_maxAbelian_of_completion Φ hFull

/-- **The `p`-adic rank of `G_F^{ab}`.**  If the units of `F` have the structure
`Fˣ^{∧} ≅ Ẑ × μ × ℤ_p^d` with `ε ∈ {0,1}` extra `ℤ/p`-generator (i.e. `d = [F : ℚ_p]` and
`ε = 1` iff `ζ_p ∈ F`), and the reciprocity isomorphism holds, then the `p`-rank of `G_F^{ab}` —
expressed by the number of index-`p` subgroups — is that of `(ℤ/p)^{1+d+ε}`.  This is
`HasFrattiniRank p (1 + d + ε)`; the arithmetic hypothesis `h` encodes the structure of the unit
group and the count of index-`p` subgroups of `Ẑ × μ × ℤ_p^d`. -/
theorem hasFrattiniRank_maxAbelian_of_unitsStructure
    (Φ : completionUnits F ≃* ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')))
    {p d ε : ℕ} (hp : p.Prime) (hε : ε ≤ 1)
    (h : NK.LocalAnabelian.HasFrattiniRank p (1 + d + ε) (completionUnits F)) :
    NK.LocalAnabelian.HasFrattiniRank p (1 + d + ε)
      ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')) :=
  hasFrattiniRank_maxAbelian_of_completion Φ h

section Datum

/-- The reciprocity datum supplies the infinite-level isomorphism
(`NK.LocalReciprocity.exists_mulEquiv_completion_maxAbelian`), hence the transfers above: the
`p`-rank of `G_F^{ab}` is the `p`-rank of the profinite completion of `Fˣ`. -/
theorem hasFrattiniRank_maxAbelian_of_datum (D : LocalReciprocityDatum F F') {p r : ℕ}
    (h : NK.LocalAnabelian.HasFrattiniRank p r (completionUnits F)) :
    NK.LocalAnabelian.HasFrattiniRank p r
      ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')) :=
  hasFrattiniRank_maxAbelian_of_completion
    (Classical.choice (exists_mulEquiv_completion_maxAbelian D)) h

/-- **Residue characteristic detection from the reciprocity datum**: if the `ℓ`-tower rank of the
profinite completion of `Fˣ` is unbounded exactly for `ℓ = p`, then `p` is the unique prime
detected by the tower-rank invariant of `G_F^{ab}`. -/
theorem residueCharDetectedBy_of_datum (D : LocalReciprocityDatum F F') {p : ℕ} (hp : p.Prime)
    (hFull : NK.LocalAnabelian.HasUnboundedTowerRank p (completionUnits F))
    (hOther : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      ¬ NK.LocalAnabelian.HasUnboundedTowerRank ℓ (completionUnits F)) :
    NK.LocalAnabelian.ResidueCharDetectedBy p
      ((maxAbelianSubext F F') ≃ₐ[F] (maxAbelianSubext F F')) :=
  residueCharDetectedBy_of_completion
    (Classical.choice (exists_mulEquiv_completion_maxAbelian D)) hp hFull hOther

end Datum

end

end NK.LocalReciprocity
