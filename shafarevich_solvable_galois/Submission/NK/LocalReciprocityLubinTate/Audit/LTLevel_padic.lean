import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.TorsionCardinality
import Submission.NK.LocalReciprocityLubinTate.LubinTate.finrank_adjoin_root_LTpolyEis
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isGalois_LTLevel
import Submission.NK.LocalReciprocityLubinTate.Audit.exists_irreducible_padic
import Submission.NK.LocalReciprocityLubinTate.Audit.residueCard_padic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Audit: the division-point theory instantiated at `ℚ_[2]` and `ℚ_[3]`

The specification demands that the statements of the chapter be *instantiated* at `F = ℚ_p` with
`p = 2` and `p = 3`, with `q = p` as well as a case with `q = p²`, and that satisfiability,
non-vacuity and universes be checked.

The Stage-4 theorems of the chapter (`#Λ_n = q^n`, `[F(π_n) : F] = (q-1)q^n`, the level `K_n` being
Galois) are general in `q ≥ 2` and in `π ∈ 𝒪[F]` irreducible, so their instantiations are immediate
consequences; this file records them, together with the *non-vacuity witness* — an irreducible
uniformiser of `𝒪[ℚ_[p]]` really does exist (`Audit.exists_irreducible_padic`, whose `(π : ℚ_[p])` is
the rational prime `p`) — so that none of the instantiations is vacuous.

## Instantiated statements

* `q = p`, `p = 2`: `ncard_LTdivisionSet_padic_two : #Λ_n = 2^n`;
* `q = p`, `p = 3`: `ncard_LTdivisionSet_padic_three : #Λ_n = 3^n`;
* `q = p²` with `p = 2` (i.e. `q = 4`, over `ℚ_[2]`): `ncard_LTdivisionSet_padic_two_q_four : #Λ_n = 4^n`;
* the degrees `[F(π_n):F] = (q-1)q^n` at `(p,q) = (2,2)`, `(3,3)`, `(2,4)`:
  `finrank_adjoin_root_LTpolyEis_padic_two`, `..._three`, `..._two_q_four`;
* the Galois property of the level `K_n` at `ℚ_[2]`: `isGalois_LTLevel_padic_two`;
* the satisfiability witnesses `exists_irreducible_padic_two`,
  `exists_ncard_LTdivisionSet_padic_two`, `exists_ncard_LTdivisionSet_padic_three`.

The conventions used are those of §5.3 of the README: `Audit.PadicInstance` supplies the instance
`IsNonarchimedeanLocalField ℚ_[p]` and `Audit.residueCard_padic` gives `residueCard ℚ_[p] = p`.
-/

namespace NK.LocalReciprocityLubinTate.Audit

universe u

/-- **`q = p = 2`**: the `π^n`-division points of the Lubin–Tate group over `ℚ_[2]` number `2^n`. -/
theorem ncard_LTdivisionSet_padic_two
    (π : ↥(ValuativeRel.valuation ℚ_[2]).integer) (hπ : Irreducible π) (n : ℕ) :
    (LTdivisionSet ℚ_[2] (π : ℚ_[2]) 2 n).ncard = 2 ^ n := by
  have h := ncard_LTdivisionSet_residueCard ℚ_[2] π hπ n
  rw [residueCard_padic 2] at h
  exact h

/-- **`q = p = 3`**: the `π^n`-division points of the Lubin–Tate group over `ℚ_[3]` number `3^n`. -/
theorem ncard_LTdivisionSet_padic_three
    (π : ↥(ValuativeRel.valuation ℚ_[3]).integer) (hπ : Irreducible π) (n : ℕ) :
    (LTdivisionSet ℚ_[3] (π : ℚ_[3]) 3 n).ncard = 3 ^ n := by
  have h := ncard_LTdivisionSet_residueCard ℚ_[3] π hπ n
  rw [residueCard_padic 3] at h
  exact h

/-- **`q = p² = 4`** (over `ℚ_[2]`): the `π^n`-division points number `4^n`.  `q = 4` is the
residue cardinality of the unramified quadratic extension of `ℚ_[2]`; the theorem is general in
`q ≥ 2`, and this instantiation checks the `q = p²` convention. -/
theorem ncard_LTdivisionSet_padic_two_q_four
    (π : ↥(ValuativeRel.valuation ℚ_[2]).integer) (hπ : Irreducible π) (n : ℕ) :
    (LTdivisionSet ℚ_[2] (π : ℚ_[2]) 4 n).ncard = 4 ^ n :=
  ncard_LTdivisionSet ℚ_[2] π hπ 4 n (by norm_num)

/-- **`(p,q) = (2,2)`**: a root of the Eisenstein factor `f^{[n]}` generates an extension of degree
`(q-1)q^n = 2^n` over `ℚ_[2]`. -/
theorem finrank_adjoin_root_LTpolyEis_padic_two
    (π : ↥(ValuativeRel.valuation ℚ_[2]).integer) (hπ : Irreducible π) (n : ℕ)
    {x : AlgebraicClosure ℚ_[2]} (hx : (Polynomial.aeval x) (LTpolyEis (π : ℚ_[2]) 2 n) = 0) :
    Module.finrank ℚ_[2]
      ↥(IntermediateField.adjoin ℚ_[2] ({x} : Set (AlgebraicClosure ℚ_[2]))) = 2 ^ n := by
  have h := LubinTate.finrank_adjoin_root_LTpolyEis ℚ_[2] π hπ 2 n (by norm_num) hx
  rw [show ((2 : ℕ) - 1) * 2 ^ n = 2 ^ n from by rw [show (2 : ℕ) - 1 = 1 from rfl, one_mul]] at h
  exact h

/-- **`(p,q) = (3,3)`**: a root of `f^{[n]}` generates an extension of degree `2·3^n` over `ℚ_[3]`. -/
theorem finrank_adjoin_root_LTpolyEis_padic_three
    (π : ↥(ValuativeRel.valuation ℚ_[3]).integer) (hπ : Irreducible π) (n : ℕ)
    {x : AlgebraicClosure ℚ_[3]} (hx : (Polynomial.aeval x) (LTpolyEis (π : ℚ_[3]) 3 n) = 0) :
    Module.finrank ℚ_[3]
      ↥(IntermediateField.adjoin ℚ_[3] ({x} : Set (AlgebraicClosure ℚ_[3]))) = 2 * 3 ^ n := by
  have h := LubinTate.finrank_adjoin_root_LTpolyEis ℚ_[3] π hπ 3 n (by norm_num) hx
  rw [show ((3 : ℕ) - 1) * 3 ^ n = 2 * 3 ^ n from by
    rw [show (3 : ℕ) - 1 = 2 from rfl]] at h
  exact h

/-- **`(p,q) = (2,4)`**, the `q = p²` case: a root of `f^{[n]}` generates an extension of degree
`(q-1)q^n = 3·4^n` over `ℚ_[2]`. -/
theorem finrank_adjoin_root_LTpolyEis_padic_two_q_four
    (π : ↥(ValuativeRel.valuation ℚ_[2]).integer) (hπ : Irreducible π) (n : ℕ)
    {x : AlgebraicClosure ℚ_[2]} (hx : (Polynomial.aeval x) (LTpolyEis (π : ℚ_[2]) 4 n) = 0) :
    Module.finrank ℚ_[2]
      ↥(IntermediateField.adjoin ℚ_[2] ({x} : Set (AlgebraicClosure ℚ_[2]))) = 3 * 4 ^ n := by
  have h := LubinTate.finrank_adjoin_root_LTpolyEis ℚ_[2] π hπ 4 n (by norm_num) hx
  rw [show ((4 : ℕ) - 1) * 4 ^ n = 3 * 4 ^ n from by
    rw [show (4 : ℕ) - 1 = 3 from rfl]] at h
  exact h

/-- The Lubin–Tate level `K_n = ℚ_[2](Λ_n)` is Galois over `ℚ_[2]`. -/
theorem isGalois_LTLevel_padic_two (π : ℚ_[2]) (n : ℕ) :
    IsGalois ℚ_[2] ↥(LTLevel ℚ_[2] π 2 n) :=
  LubinTate.isGalois_LTLevel ℚ_[2] π 2 n (by norm_num)

/-! ## Satisfiability: the instantiated statements are not vacuous -/

/-- There *is* an irreducible uniformiser of `𝒪[ℚ_[2]]` (namely `2`), so the statements above are
not vacuous. -/
theorem exists_irreducible_padic_two :
    ∃ π : ↥(ValuativeRel.valuation ℚ_[2]).integer, Irreducible π ∧ (π : ℚ_[2]) = 2 :=
  exists_irreducible_padic 2

/-- There *is* an irreducible uniformiser of `𝒪[ℚ_[3]]` (namely `3`), so the `p = 3` statements are
not vacuous. -/
theorem exists_irreducible_padic_three :
    ∃ π : ↥(ValuativeRel.valuation ℚ_[3]).integer, Irreducible π ∧ (π : ℚ_[3]) = 3 :=
  exists_irreducible_padic 3

/-- **Satisfiability of `#Λ_n = 2^n`**: it is realised by the Lubin–Tate group of the uniformiser
`2` over `ℚ_[2]`. -/
theorem exists_ncard_LTdivisionSet_padic_two (n : ℕ) :
    ∃ π : ↥(ValuativeRel.valuation ℚ_[2]).integer, Irreducible π ∧
      (LTdivisionSet ℚ_[2] (π : ℚ_[2]) 2 n).ncard = 2 ^ n := by
  obtain ⟨π, hπ, -⟩ := exists_irreducible_padic 2
  exact ⟨π, hπ, ncard_LTdivisionSet_padic_two π hπ n⟩

/-- **Satisfiability of `#Λ_n = 3^n`**. -/
theorem exists_ncard_LTdivisionSet_padic_three (n : ℕ) :
    ∃ π : ↥(ValuativeRel.valuation ℚ_[3]).integer, Irreducible π ∧
      (LTdivisionSet ℚ_[3] (π : ℚ_[3]) 3 n).ncard = 3 ^ n := by
  obtain ⟨π, hπ, -⟩ := exists_irreducible_padic 3
  exact ⟨π, hπ, ncard_LTdivisionSet_padic_three π hπ n⟩

end NK.LocalReciprocityLubinTate.Audit
