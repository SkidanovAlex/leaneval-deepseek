import Mathlib
import Submission.Work.TameArithmetic.All
import Submission.Work.RelatorRank.Defs

/-!
# `Work.TameSalle` -- the idèlic Salle/Koch reduction

**Namespace** `Work.TameSalle`; module `Submission.Work.TameSalle.Defs`.

This chapter isolates the **classical relation bound of Salle--Shafarevich--Koch** for the
maximal pro-`2` extension of `ℚ` unramified outside `S = primesS = {17,41,73,89,97}` and at the
infinite places -- the single remaining input of the benchmark
`Submission.exists_totallyReal_discr_le` (Martinet's asymptotically good totally real towers) --
and proves everything that can be proved around it: the reduction to the statement the benchmark
consumes (`Work.TameArithmetic.TameRelationBound`), the group-theoretic transition between the
literature's *pro-`2`* presentation normalisation and the workspace's *abstract* one, and the
arithmetic of the numbers `5` and `6` appearing in it.

## The classical theorem (the wall)

Salle, *Sur les sous-groupes de Sylow des groupes de Galois...*, Théorème 4.1 (refined for
`p = 2`); Mizusawa, *On the relation rank of pro-`p` Galois groups*, arXiv:1707.00113,
Thm. `thm:relrk` / Prop. `prop:genrk`; Koch, *Galois theory of `p`-extensions*, Ch. 11 Thm. 11.3;
Shafarevich 1963; Hajir--Maire--Ramakrishna, arXiv:2103.09508 §1.  For a number field `k`, a prime
`p` and a finite set `S` of places with `p ∉ S`, writing `G_S(k)` for the maximal pro-`p`
extension of `k` unramified outside `S` and

```
B_S = {a ∈ kˣ : (a) = I^p for a fractional ideal I, and a ∈ (k_vˣ)^p for all v ∈ S}
```

(so `B_S` is a subgroup of `kˣ` containing `(kˣ)^p`), one has the two formulas of Mizusawa's
Prop. `prop:genrk` and Thm. `thm:relrk` (Salle's Théorèmes 3.3 and 4.1, with the author's
refinement for `p = 2`):

```
d(G̃_S(k)) = |S| + |P| + dim_{F_p} B̃_S/(kˣ)^p − dim_{F_p} E_k/E_k^p ,
dim_{F_p} Sha²(G̃_S(k)) ≤ dim_{F_p} B̃_S/(kˣ)^p ,
r(G̃_S(k)) = dim_{F_p} H²(G̃_S(k), F_p) ≤ dim Sha² + |S| − (1−δ_{S,∅})·θ + |P| ,
```

where `E_k = O_kˣ`, `G̃_S(k) = Gal((k^cyc)_S/k)`, `Sha²` is the kernel of the localisation of `H²`,
`P` is the set of places above `p` (and the real ones) at which ramification is allowed, `θ = 1` if
`ζ_p ∈ k` and `0` otherwise, and `B̃_S ⊆ B_S` is the cyclotomic subgroup (`B̃_S = B_S` for `p = 2`,
`k = ℚ` as long as `S` contains neither `∞` nor a prime `q ≡ 3 (mod 4)`).

Combining the two inequalities `dim Sha² ≤ dim B̃_S/(kˣ)^p` and the relation bound gives the
combined form used below.  Specialised to `k = ℚ`, `p = 2`, `S = primesS` -- where `P = ∅`, `θ = 1`
(because `ζ₂ = −1 ∈ ℚ`), `|S| = 5`, `dim_{F₂} E_ℚ/E_ℚ² = 1`, and
`B̃_S = B_S` with `dim_{F₂} B_S/ℚ^{×2} = 1` -- this reads

```
d(Γ) = 5 + 1 − 1 = 5 ,        r(Γ) ≤ d(Γ) + dim_{F₂} B_S/ℚ^{×2} = 6 ,
                               equivalently   r(Γ) − d(Γ) ≤ dim_{F₂} B_S/ℚ^{×2} = 1 ,
```

which is exactly the `Prop` isolated here (`SalleTameRelationBound`); numerically
`4·6 = 24 ≤ 25 = 5·5`, so the finite `2`-group Golod--Shafarevich inequality applies.  The *sharper*
`p = 2` forms of the classical theorem -- the local-term count with the `−(1−δ_{S,∅})θ` correction,
i.e. the Euler-characteristic bound `χ₂(G̃_S(ℚ)) = 1 − d + r ≤ 1` (Mizusawa's Corollary to
Thm. `thm:relrk`, the normalisation of Theorem 3.2 of arXiv:2605.28781) -- also discharge the wall
and are recorded in `Reduction.salleSharp_of_eulerChar_one`; the wall itself is deliberately stated
in the weaker, sufficient form `r(Γ) ≤ d(Γ) + dim_{F₂} B_S/ℚ^{×2} = 6` prescribed by the subproject
brief.  See `README.md` §1 and §4 for the full discussion and references.

The two numerical computations `dim_{F_2} B_S/ℚ^{×2} = 1` (`Work.TameArithmetic.VS_mod_squares_two`:
over `ℚ` every element of `B_S` is `±` a square, while `-1` is not a square) and
`dim_{F_2} ℤˣ/(ℤˣ)² = 1` are *proved in this workspace*; the existence of a presentation with the
resulting relation count is the classical input, isolated here as the single unproved `Prop`
`Work.TameSalle.SalleTameRelationBound` and documented in `README.md`.

## The dictionary used to state it

The literature states the relation count cohomologically, `r(Γ) = dim_{F_2} H²(Γ, F_2)`
(Koch Ch. 11 Thm. 11.3); the workspace's `Work.TameArithmetic.TamePro2Presentation` states it as a
presentation of `Γ = Gal(K/ℚ)` on **five dense generators** by **at most six words** in the
*abstract* free group `FreeGroup (Fin 5)`.  The transition between the two normalisations is the
group-theoretic hygiene proved in `Submission/Work/TameSalle/Bridge.lean`; the numerical
normalisation `r ≤ d + dim_{F_2} B_S/ℚ^{×2}` (with the generator number `d` left free, as in
Salle's inequality) is `SalleTameRelationBound` below.

## Contents

* `Gal` -- the Galois group `Γ = Gal(K/ℚ)`;
* `sqSubgroup`, `BS` (`= B_S = V_S`), `BSModSquares` (`= B_S/ℚ^{×2}`), `twoRank`, `bSRank`
  (`= dim_{F_2} B_S/ℚ^{×2}`), `unitTwoRank` (`= dim_{F_2} ℤˣ/(ℤˣ)²`), `salleGeneratorRank`
  (`= |S| + dim B_S/ℚ^{×2} − dim ℤˣ/(ℤˣ)² = 5`), `salleRelationRank` (`= 5 + 1 = 6`);
* `SalleTameRelationBound` -- **the wall**, Salle's inequality in the literature's normalisation;
* `SalleTameSharpBound` -- the same statement with the generator number specialised to `d(Γ) = 5`
  (`Reduction.lean` proves the two equivalent, and both equivalent to the target).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField

namespace Work.TameSalle

noncomputable section

/-! ## Vocabulary -/

/-- **The Galois group `Γ = Gal(K/ℚ)`** of a Galois extension `K/ℚ`. -/
abbrev Gal (K : Type) [Field K] [Algebra ℚ K] : Type := K ≃ₐ[ℚ] K

/-- **Dense generation** of a topological group by a family: the topological closure of the
abstract subgroup generated by the family is everything.  This is `Work.RelatorRank.DenseGenerating`
(the same statement, written in the form in which the workspace's
`Work.TameArithmetic.TamePro2Presentation` consumes it); in the profinite setting it is strictly
weaker than generation (`1 ∈ ℤ₂` generates `ℤ₂` densely but only generates `ℤ`). -/
abbrev DenseGenerating {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {ι : Type*} (gen : ι → Γ) : Prop :=
  (Subgroup.closure (Set.range gen)).topologicalClosure = ⊤

/-- **The subgroup of squares** of a group, `G² = ⟨{x * x : x ∈ G}⟩`. -/
abbrev sqSubgroup (G : Type*) [Group G] : Subgroup G :=
  Subgroup.closure (Set.range (fun x : G => x * x))

/-- **Koch's group `B_S`** (called `V_S` in the Shafarevich--Koch literature): the group of
`x ∈ ℚˣ` whose principal fractional ideal `(x)` is a square and which are squares in `ℚ_q` for
every `q ∈ S`.  This is `Work.TameArithmetic.VS` (`Submission/Work/TameArithmetic/VSDefs.lean`),
whose `𝔽₂`-rank modulo squares is the "extra relator" term of Salle's inequality. -/
abbrev BS : Subgroup ℚˣ := Work.TameArithmetic.VS

/-- **`B_S/(ℚˣ)²`**, the quotient whose `𝔽₂`-dimension is the `V_S` term of the Shafarevich--Koch
relation count. -/
abbrev BSModSquares : Type := ↥BS ⧸ (BS ⊓ sqSubgroup ℚˣ).subgroupOf BS

/-- The `𝔽₂`-dimension of an elementary abelian `2`-group, taken as the binary logarithm of its
cardinality (so that `dim (ℤ/2)^e = e` and `dim (B_S/(ℚˣ)²) = log₂ #(B_S/(ℚˣ)²)`). -/
def twoRank (A : Type*) [Group A] : ℕ := Nat.log 2 (Nat.card A)

/-- **`dim_{𝔽₂} B_S/ℚ^{×2}`** -- the `B_S` term of Salle's inequality, computed in this workspace
to be `1` (`bSRank_eq_one`, from `Work.TameArithmetic.VS_mod_squares_two`). -/
def bSRank : ℕ := twoRank BSModSquares

/-- **`dim_{𝔽₂} ℤˣ/(ℤˣ)²`** -- the unit term `E_ℚ/E_ℚ²` of Salle's generator-rank formula,
computed in this workspace to be `1` (`unitTwoRank_eq_one`). -/
def unitTwoRank : ℕ := twoRank (ℤˣ ⧸ sqSubgroup ℤˣ)

/-- **Salle's generator term for `k = ℚ`, `p = 2`**:

  `d(Γ) = |S| + dim_{𝔽₂} B_S/ℚ^{×2} − dim_{𝔽₂} ℤˣ/(ℤˣ)² = 5 + 1 − 1 = 5`

(`salleGeneratorRank_eq_five`). -/
def salleGeneratorRank : ℕ := Work.TameArithmetic.primesS.card + bSRank - unitTwoRank

/-- **Salle's relation term**: `d(Γ) + dim_{𝔽₂} B_S/ℚ^{×2} = 5 + 1 = 6`
(`salleRelationRank_eq_six`), the bound `r(Γ) ≤ 6` of the classical theorem. -/
def salleRelationRank : ℕ := salleGeneratorRank + bSRank

/-- **Euler characteristic of a presentation** on `d` generators with `r` relators:
`χ = 1 − d + r`.  For a pro-`p` group `Γ = G_S(ℚ)` the classical (Salle/Mizusawa) computation
expresses the relation count as the *second partial Euler--Poincaré characteristic*
`χ₂ = 1 − d(Γ) + r(Γ)`; Mizusawa's Corollary to Thm. `thm:relrk` gives `χ₂(G̃_S(ℚ)) ≤ 1`, which is
the normalisation in which Theorem 3.2 of arXiv:2605.28781 states its arithmetic input
(see `SalleTameEulerCharBound` and `README.md` §1.2, §4.6). -/
def eulerChar (d r : ℕ) : ℤ := 1 - (d : ℤ) + (r : ℤ)

/-! ## The wall -/

/-- **Salle's relation bound (Théorème 4.1, `p = 2`, `k = ℚ`, `S = primesS`) -- the classical input
of the benchmark.**

There is a maximal pro-`2` extension `K` of `ℚ` unramified outside `S = primesS` and at the
infinite places (`Work.TameArithmetic.IsMaximalTamePro2 K`, which exists by
`Work.TameArithmetic.exists_maximalTamePro2` with no class field theory), a number `d` of
topological generators of `Γ = Gal(K/ℚ)`, and a set of relators, such that

* `d ≤ |S| + dim_{𝔽₂} B_S/ℚ^{×2} − dim_{𝔽₂} ℤˣ/(ℤˣ)² = 5` (`d ≤ salleGeneratorRank`);
* `rel.card ≤ d + dim_{𝔽₂} B_S/ℚ^{×2}` (`rel.card ≤ d + bSRank`), i.e. `r(Γ) − d(Γ) ≤ 1`;
* the relators present `Γ` on the dense generating family (`ker (FreeGroup.lift gen) =
  normalClosure rel`, `DenseGenerating gen`).

Both arithmetic quantities in the statement are *proved* in this workspace:

* `bSRank = 1`: over `ℚ` every element of `B_S` is `±` a square of a rational
  (`Work.TameArithmetic.VS_eq_pm_squares`), and `-1` is not a square
  (`Work.TameArithmetic.neg_one_not_square`), so `B_S/ℚ^{×2} ≅ ℤ/2`;
* `unitTwoRank = 1` and `salleGeneratorRank = 5`.

The *mathematical* content of the proposition -- the existence of the presentation with
`rel.card ≤ d + 1 ≤ 6` relations -- is the classical theorem quoted in the module docstring
(Salle 1978, Théorème 4.1; Shafarevich 1963; Koch Ch. 11 Thm. 11.3; Mizusawa arXiv:1707.00113;
Neukirch--Schmidt--Wingberg Ch. X §7 Cor. 10.7.7).  `README.md` records the precise chain of
classical theorems that would discharge it and which of its steps are proved here. -/
def SalleTameRelationBound : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
    Work.TameArithmetic.IsMaximalTamePro2 K ∧
      ∃ (d : ℕ) (gen : Fin d → Gal K) (rel : Finset (FreeGroup (Fin d))),
        d ≤ salleGeneratorRank ∧ rel.card ≤ d + bSRank ∧ DenseGenerating gen ∧
        MonoidHom.ker (FreeGroup.lift gen) =
          Subgroup.normalClosure (rel : Set (FreeGroup (Fin d)))

/-- **Salle's relation bound in the sharp normalisation `d(Γ) = 5`, `r(Γ) ≤ 6`**: the same
statement with the generator number specialised to the value `salleGeneratorRank = 5` of Salle's
generator formula.  `Reduction.lean` proves `SalleTameSharpBound ↔ SalleTameRelationBound` (the
non-trivial direction is the padding of a `d`-generator presentation to a five-generator one, which
is exactly the counting `(d + 1) + (5 - d) = 6`). -/
def SalleTameSharpBound : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
    Work.TameArithmetic.IsMaximalTamePro2 K ∧
      ∃ (gen : Fin 5 → Gal K) (rel : Finset (FreeGroup (Fin 5))),
        DenseGenerating gen ∧ rel.card ≤ salleRelationRank ∧
        MonoidHom.ker (FreeGroup.lift gen) =
          Subgroup.normalClosure (rel : Set (FreeGroup (Fin 5)))

/-- **The source paper's Euler-characteristic form of the classical input** (Mizusawa's Corollary
to Thm. `thm:relrk`, i.e. Salle's Corollaire 4.3, for `p = 2`): there is a maximal tame pro-`2`
extension `K` of `ℚ` whose Galois group `Γ` admits a presentation on `d ≤ 5` generators with `r`
relators satisfying the Euler-characteristic identity `χ = 1 − d + r = 1` (equivalently `r = d = 5`),
i.e. the sharp relation count `r(Γ) = d(Γ) = 5`.

This is *sharper* than `SalleTameRelationBound` (which only asks `r(Γ) ≤ d(Γ) + bSRank = 6`), and
`Reduction.salle_of_eulerCharBound` proves that it implies the wall, so a caller may place the
classical input on either statement.  It is the form in which Theorem 3.2 of arXiv:2605.28781 uses
the theorem (`χ = 1`), and the form of Salle's Corollaire 4.3 refined by Mizusawa: for
`k = ℚ`, `p = 2`, `χ₂(G̃_S(ℚ)) = 1 − d + r ≤ 1 + dim_{F₂}E_ℚ/E_ℚ² − 1 = 1`. -/
def SalleTameEulerCharBound : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : IsGalois ℚ K),
    Work.TameArithmetic.IsMaximalTamePro2 K ∧
      ∃ (d r : ℕ) (gen : Fin d → Gal K) (rel : Finset (FreeGroup (Fin d))),
        d ≤ salleGeneratorRank ∧ eulerChar d r = 1 ∧ rel.card ≤ r ∧ DenseGenerating gen ∧
        MonoidHom.ker (FreeGroup.lift gen) =
          Subgroup.normalClosure (rel : Set (FreeGroup (Fin d)))

end

end Work.TameSalle
