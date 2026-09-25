import Mathlib
import Submission.NK.LocalAnabelian.ResidueField.Defs
import Submission.NK.LocalAnabelian.ResidueField.isGalois_unramifiedClosure

/-!
# Vocabulary for the tame local Kronecker–Weber theorem over `ℚ_[p]`

This file fixes the field-theoretic vocabulary used by the proof of
`NK.Chebotarev.LocalKWTame`: the ambient separable closure `Ω` of `ℚ_[p]`, the maximal
unramified extension `K = ℚ_pᵘʳ ⊆ Ω` (realised as
`NK.LocalAnabelian.unramifiedClosure`), and the two fields that the tame local
Kronecker–Weber theorem compares: the compositum `K ⊔ ℚ_[p]⟮ζ_p⟯` (which contains every tame
abelian extension of `ℚ_[p]`) and the unramified levels `ℚ_[p]⟮ζ_{p^N-1}⟯`.

The classical reference is Milne, *Class Field Theory*, Corollary I.4.12 and the lemma in the
"tame case" of Koenigsmann–Stock, arXiv:2206.05801.
-/

open scoped Classical
open IntermediateField

namespace NK.Chebotarev.LocalKW

/-- The ambient **separable closure of `ℚ_[p]`** in which every local field of the proof is
realised as an intermediate field. -/
abbrev Omega (p : ℕ) [Fact p.Prime] : Type := SeparableClosure ℚ_[p]

/-- **The maximal unramified extension `K = ℚ_pᵘʳ` of `ℚ_[p]`**, realised inside `Ω` as the
compositum of the cyclotomic extensions `ℚ_[p]⟮ζ⟯` over all roots of unity `ζ` of order prime
to `p`. -/
noncomputable abbrev unram (p : ℕ) [Fact p.Prime] : IntermediateField ℚ_[p] (Omega p) :=
  NK.LocalAnabelian.unramifiedClosure (κ := ℚ_[p]) (K' := Omega p) p

/-- A chosen **uniformiser seed**: the rational prime `p`, seen inside `Ω`. -/
noncomputable abbrev primeSeed (p : ℕ) [Fact p.Prime] : Omega p :=
  algebraMap ℚ_[p] (Omega p) (p : ℚ_[p])

end NK.Chebotarev.LocalKW
