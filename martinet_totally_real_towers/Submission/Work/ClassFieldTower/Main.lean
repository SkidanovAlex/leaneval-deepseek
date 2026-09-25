import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.Tower
import Submission.Work.ClassFieldTower.infinite_of_hasMinimalPresentation
import Submission.Work.ClassFieldTower.two_pow_classGroupTwoRank
import Submission.Work.ClassFieldTower.unitTwoRank_eq_one_of_imaginaryQuadratic
import Submission.Work.ClassFieldTower.exists_unramifiedLevel_of_infinite
import Submission.Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five

/-!
# `Submission.Work.ClassFieldTower.Main`

**WARNING.**  The definitions `GeneratorRankInput`, `DeficiencyBoundInput`,
`ClassFieldTowerInvariants`, `GolodShafarevichCertificate` and `ShafarevichKochInput` in this
file build the arithmetic input on `HasMinimalPresentation (galoisGroup M) d r`, i.e. on an
ABSTRACT finite presentation of `G_∅ = Gal(F_∅/F)`.  This is **UNSATISFIABLE** whenever `F_∅/F`
is infinite (a finitely presented group is countable, an infinite profinite group is not); see
`Submission/Work/ClassFieldTower/Vacuity.lean` for the machine-checked refutation
(`golodShafarevichCertificate_and_infinite_unsatisfiable`, `not_infiniteHilbertTwoClassFieldTower`).
The SOUND replacement is `Submission/Work/ClassFieldTower/ProTwo.lean`
(`ProTwoPresentationData`, `ProTwoTowerInput`, `InfiniteProTwoExtension`).  The uninstantiated
definitions are kept only for the record; do not use them as an arithmetic input.
-/

/-!
# `Work.ClassFieldTower.Main` -- Golod--Shafarevich and the infinite Hilbert `2`-class tower

This is the assembly module of the class-field-tower chapter.  It turns the two classical
arithmetic invariants of the maximal unramified pro-`2` group `G_∅ = Gal(F_∅/F)` of an
imaginary quadratic field `F`

* `d(G_∅) = rank₂ Cl(F)`  (`classGroupTwoRank F`),
* `r - d ≤ d₂(O_F^×) = 1`  (the Shafarevich--Koch deficiency bound, `ShafarevichKochBound`)

into **infinitude of `G_∅`**, hence into an infinite Hilbert `2`-class field tower with constant
root discriminant.

## Main results

* `four_mul_le_sq_of_le_add_one` -- the numerical step: `r ≤ d + 1` and `5 ≤ d` give `4r ≤ d²`;
* `infinite_galoisGroup_of_classGroupTwoRank_ge_five` -- **the crux**: the two arithmetic
  invariants plus `rank₂ Cl(F) ≥ 5` give `Infinite G_∅`;
* `infinite_galoisGroup_of_certificate` -- the same from a `GolodShafarevichCertificate`;
* `infinite_galoisGroup_of_imaginaryQuadratic_classGroupTwoRank_ge_five` -- the imaginary
  quadratic specialization (`r ≤ d + 1`, `d = rank₂ Cl(F)`, `d ≥ 5`);
* `card_classGroup_twoQuotient_ge_of_classGroupTwoRank_ge` -- the numerical certificate in the
  form "the `2`-part `Cl(F)/Cl(F)²` has order at least `2^5 = 32`";
* `exists_unramifiedLevel_rootDiscr_of_certificate` -- the tower consequence: for every `N`
  there is a finite unramified Galois level `L/F` with `[L : F] ≥ N` and
  `rootDiscr L = rootDiscr F`;
* `infiniteHilbertTwoClassFieldTower_of_shafarevichKochInput` -- the named wall of the chapter.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-! ## 1. The numerical step -/

/-- If `r ≤ d + 1` and `5 ≤ d` then `4 * r ≤ d * d`.  (This is the whole numerical content of
the Golod--Shafarevich criterion in the unramified quadratic case: `r - d ≤ 1` and
`d = rank₂ Cl(F) ≥ 5`.) -/
theorem four_mul_le_sq_of_le_add_one {d r : ℕ} (hr : r ≤ d + 1) (hd : 5 ≤ d) :
    4 * r ≤ d * d := by
  have h1 : (4 * r : ℤ) ≤ 4 * ((d : ℤ) + 1) := by
    have : (r : ℤ) ≤ (d : ℤ) + 1 := by exact_mod_cast hr
    linarith
  have h2 : 4 * ((d : ℤ) + 1) ≤ (d : ℤ) * d := by
    have hpos : (5 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    nlinarith [sq_nonneg ((d : ℤ) - 2)]
  have : (4 * r : ℤ) ≤ (d : ℤ) * d := le_trans h1 h2
  exact_mod_cast this

/-- **The numerical certificate in quotient form.**  If `rank₂ Cl(F) ≥ 5` then the
`2`-part `Cl(F)/Cl(F)²` has order at least `2 ^ 5 = 32`. -/
theorem card_classGroup_twoQuotient_ge_of_classGroupTwoRank_ge {F : Type*} [Field F]
    [NumberField F] (h : 5 ≤ classGroupTwoRank F) :
    2 ^ 5 ≤ Nat.card (ClassGroup (𝓞 F) ⧸
      Subgroup.closure (Set.range (fun x : ClassGroup (𝓞 F) => x ^ 2))) := by
  rw [← two_pow_classGroupTwoRank F]
  exact Nat.pow_le_pow_right (by norm_num) h

/-! ## 2. The crux: the two arithmetic invariants give infinitude -/

/-- **THE GOLOD--SHAFAREVICH CRUX, in class-group-rank form.**

Let `F` be a number field, `M = F_∅` its maximal unramified pro-`2` extension and
`G_∅ = Gal(F_∅/F)`.  Suppose

* `hpres`: `G_∅` has a minimal presentation with `d = classGroupTwoRank F` generators and `r`
  relators (class field theory: `d(G_∅) = rank₂ Cl(F)`; minimality is part of the hypothesis);
* `hdef`: `r ≤ d + unitTwoRank F` (the Shafarevich--Koch deficiency bound);
* `hunit`: `unitTwoRank F ≤ 1` (true for imaginary quadratic `F`, where `d₂(O_F^×) = 1`);
* `hrank`: `5 ≤ d = rank₂ Cl(F)`.

Then `G_∅` is infinite. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_classGroupTwoRank_ge_five {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {r : ℕ} (hunit : unitTwoRank F ≤ 1)
    (hdef : r ≤ classGroupTwoRank F + unitTwoRank F)
    (hpres : HasMinimalPresentation (galoisGroup M) (classGroupTwoRank F) r)
    (hrank : 5 ≤ classGroupTwoRank F) : Infinite (galoisGroup M) := by
  have hr : r ≤ classGroupTwoRank F + 1 := by omega
  have hineq : 4 * r ≤ classGroupTwoRank F * classGroupTwoRank F :=
    four_mul_le_sq_of_le_add_one hr hrank
  have hpos : 0 < classGroupTwoRank F := by omega
  exact infinite_of_hasMinimalPresentation
    (fun hfin => MaximalUnramifiedProP.isPGroup_galoisGroup_of_finite M hfin) hpos hpres hineq

/-- **Compatibility form of the criterion.**  The same conclusion from the stronger hypothesis
that *all* finite quotients of `G` are `p`-groups (the shape of
`Submission.GroupTheory.infinite_of_presentation_of_golodShafarevich`).  Note that for
`G = G_∅` this stronger hypothesis is *not* available: a pro-`p` group can have normal
subgroups of finite index whose quotient is not a `p`-group (e.g. `ℤ_2 / 3ℤ_2 ≅ ℤ/3`), which
is why the criterion used everywhere in this chapter only asks `Finite G → IsPGroup p G`. -/
theorem infinite_of_all_finiteQuotients_pGroup {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    {d r : ℕ} (hpos : 0 < d) (hpres : HasMinimalPresentation G d r)
    (hpg : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup p (G ⧸ N))
    (hineq : 4 * r ≤ d * d) : Infinite G :=
  infinite_of_hasMinimalPresentation
    (fun hfin => by
      haveI := hfin
      exact (hpg ⊥ (show Finite (G ⧸ (⊥ : Subgroup G)) from inferInstance)).of_equiv
        (QuotientGroup.quotientBot (G := G)))
    hpos hpres hineq


/-- **THE GOLOD--SHAFAREVICH CRUX, in certificate form.** -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_certificate {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ} (h : GolodShafarevichCertificate F M d r) :
    Infinite (galoisGroup M) := by
  have hr : r ≤ d + 1 := by
    have h1 : r ≤ d + unitTwoRank F := h.deficiency
    have h2 : unitTwoRank F ≤ 1 := h.unit_bound
    omega
  have hineq : 4 * r ≤ d * d := four_mul_le_sq_of_le_add_one hr h.rank_ge
  have hpos : 0 < d := by
    have := h.rank_ge
    omega
  exact infinite_of_hasMinimalPresentation
    (fun hfin => MaximalUnramifiedProP.isPGroup_galoisGroup_of_finite M hfin) hpos
    h.presentation hineq

/-- **THE GOLOD--SHAFAREVICH CRUX for an imaginary quadratic field.**

For an imaginary quadratic `F` (totally complex of degree `2`) the deficiency bound reads
`r ≤ d + 1` with `d = rank₂ Cl(F)`, and `r ≤ d + 1`, `d ≥ 5` give `4r ≤ d²`.  Hence the two
classical arithmetic invariants of `G_∅` -- a minimal presentation with `d = rank₂ Cl(F)`
generators and `r` relators, and the relation bound `r ≤ d + 1` -- suffice for `G_∅` to be
infinite. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_imaginaryQuadratic_classGroupTwoRank_ge_five {F : Type}
    [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    (h2 : Module.finrank ℚ F = 2) (M : MaximalUnramifiedProP.{0} F 2) {r : ℕ}
    (hpres : HasMinimalPresentation (galoisGroup M) (classGroupTwoRank F) r)
    (hdef : r ≤ classGroupTwoRank F + 1)
    (hrank : 5 ≤ classGroupTwoRank F) : Infinite (galoisGroup M) := by
  have hunit : unitTwoRank F = 1 := unitTwoRank_eq_one_of_imaginaryQuadratic F h2
  refine infinite_galoisGroup_of_classGroupTwoRank_ge_five M ?_ ?_ hpres hrank
  · omega
  · omega

/-- **The numerical certificate form.**  If `G_∅` admits a minimal presentation with `d ≥ 5`
generators and `r` relators satisfying `4r ≤ d²`, then `G_∅` is infinite.  This is the
"essential consumable form" of the assignment: it needs NO identification of `d` with
`rank₂ Cl(F)`. -/
theorem infinite_galoisGroup_of_minimalPresentation {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ} (hpos : 0 < d)
    (hpres : HasMinimalPresentation (galoisGroup M) d r) (hineq : 4 * r ≤ d * d) :
    Infinite (galoisGroup M) :=
  infinite_of_hasMinimalPresentation
    (fun hfin => MaximalUnramifiedProP.isPGroup_galoisGroup_of_finite M hfin) hpos hpres hineq

/-! ## 2b. The two arithmetic invariants of `G_∅`, isolated -/

/-- **CLASS FIELD THEORY INPUT (1): `d(G_∅) = rank₂ Cl(F)`.**

`G_∅` has a minimal presentation whose generator number is exactly `classGroupTwoRank F`, the
`2`-rank of the class group.  Equivalently, the maximal elementary abelian `2`-quotient
`G_∅/Φ(G_∅)` has `F₂`-dimension `rank₂ Cl(F)`: the unramified abelian extensions of `F` of
exponent `2` are the quadratic ones, classified by `Cl(F)/Cl(F)²`. -/
def GeneratorRankInput (F : Type*) [Field F] [NumberField F] (M : MaximalUnramifiedProP F 2) :
    Prop :=
  ∃ r : ℕ, HasMinimalPresentation (galoisGroup M) (classGroupTwoRank F) r

/-- **SHAFAREVICH--KOCH DEFICIENCY BOUND INPUT (2).**

Some minimal presentation of `G_∅` by `d = rank₂ Cl(F)` generators has `r` relators with
`r ≤ d + d₂(O_F^×)`; equivalently the deficiency `df = r - d` satisfies `df ≤ d₂(O_F^×)`
(`Work.ClassFieldTower.shafarevichKochBound_iff_deficiency`). -/
def DeficiencyBoundInput (F : Type*) [Field F] [NumberField F] (M : MaximalUnramifiedProP F 2) :
    Prop :=
  ∃ r : ℕ, ShafarevichKochBound F (classGroupTwoRank F) r ∧
    HasMinimalPresentation (galoisGroup M) (classGroupTwoRank F) r

/-- **The two arithmetic invariants of `G_∅` for a single relator count `r`.** -/
def ClassFieldTowerInvariants (F : Type*) [Field F] [NumberField F]
    (M : MaximalUnramifiedProP F 2) (r : ℕ) : Prop :=
  HasMinimalPresentation (galoisGroup M) (classGroupTwoRank F) r ∧
    ShafarevichKochBound F (classGroupTwoRank F) r

/-- **THE CRUX, with the arithmetic hypotheses isolated.**  If the two classical invariants of
`G_∅` hold at some relator count `r` (`d = rank₂ Cl(F)`; `r - d ≤ d₂(O_F^×)`), the unit invariant
is `≤ 1` (imaginary quadratic) and `rank₂ Cl(F) ≥ 5`, then `G_∅` is infinite. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_invariants {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {r : ℕ} (h : ClassFieldTowerInvariants F M r)
    (hunit : unitTwoRank F ≤ 1) (hrank : 5 ≤ classGroupTwoRank F) :
    Infinite (galoisGroup M) :=
  infinite_galoisGroup_of_classGroupTwoRank_ge_five M hunit h.2 h.1 hrank

/-- **The Golod--Shafarevich crux in the "`5 ≤ d`" form.**  The arithmetic side only has to
supply a minimal presentation of `G_∅` with `d` generators, `r ≤ d + 1` relators, and the
numerical certificate `5 ≤ d`.  (`5 ≤ d` can in turn be certified without class field theory
by a surjection `G_∅ ↠ (𝔽₂)^5`, i.e. by five independent unramified quadratic extensions of
`F`: `Work.ClassFieldTower.five_le_of_surjective_zmodTwo_five`.) -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_presentation_of_five_le {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ}
    (hpres : HasMinimalPresentation (galoisGroup M) d r) (hdef : r ≤ d + 1) (h5 : 5 ≤ d) :
    Infinite (galoisGroup M) := by
  have hineq : 4 * r ≤ d * d := four_mul_le_sq_of_le_add_one hdef h5
  have hpos : 0 < d := by omega
  exact infinite_galoisGroup_of_minimalPresentation M hpos hpres hineq

/-- **THE CFT-FREE NUMERICAL CERTIFICATE.**  The generator bound `d ≥ 5` can be supplied
without class field theory by a surjection `G_∅ ↠ (𝔽₂)^5` -- i.e. by five independent unramified
quadratic extensions of `F` (Galois theory + the universal property of `F_∅`).  Together with a
minimal presentation with `r ≤ d + 1` relators this gives `Infinite G_∅`. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_presentation_and_surjection {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ}
    (hpres : HasMinimalPresentation (galoisGroup M) d r) (hdef : r ≤ d + 1)
    (φ : galoisGroup M →* (Fin 5 → Multiplicative (ZMod 2)))
    (hφ : Function.Surjective φ) : Infinite (galoisGroup M) :=
  infinite_galoisGroup_of_presentation_of_five_le M hpres hdef
    (five_le_of_surjective_zmodTwo_five hpres φ hφ)

/-- **Five independent unramified quadratic extensions of `F`**, expressed as a surjection of
`G_∅` onto `(𝔽₂)^5`.  This is the CFT-free form of the numerical certificate
`rank₂ Cl(F) ≥ 5`: by Galois theory and the universal property of `F_∅`, five independent
unramified quadratic extensions `L₁,…,L₅/F` compose to an unramified exponent-`2` extension of
degree `2^5`, whose Galois group is a quotient of `G_∅`. -/
def HasFiveIndependentUnramifiedQuadratics {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) : Prop :=
  ∃ φ : galoisGroup M →* (Fin 5 → Multiplicative (ZMod 2)), Function.Surjective φ

/-- **THE CFT-FREE CRUX.**  A minimal presentation of `G_∅` with `r ≤ d + 1` relators, together
with five independent unramified quadratic extensions of `F`, gives `Infinite G_∅`. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_presentation_and_fiveQuadratics {F : Type} [Field F]
    [NumberField F] (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ}
    (hpres : HasMinimalPresentation (galoisGroup M) d r) (hdef : r ≤ d + 1)
    (h5 : HasFiveIndependentUnramifiedQuadratics M) : Infinite (galoisGroup M) := by
  obtain ⟨φ, hφ⟩ := h5
  exact infinite_galoisGroup_of_presentation_and_surjection M hpres hdef φ hφ

/-! ## 3. The tower consequence -/

/-- **The tower consequence of the certificate.**  For every `N` there is a finite unramified
Galois extension `L/F` with `[L : F] ≥ N` and constant root discriminant
`rootDiscr L = rootDiscr F`. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem exists_unramifiedLevel_rootDiscr_of_certificate {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ} (h : GolodShafarevichCertificate F M d r)
    (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra F L)
      (_ : FiniteDimensional F L) (_ : IsGalois F L),
      N ≤ Module.finrank F L ∧ differentIdeal (𝓞 F) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr F :=
  exists_unramifiedLevel_of_infinite M (infinite_galoisGroup_of_certificate M h) N

/-! ## 4. The arithmetic input, and the wall of the chapter -/

/-- **The Shafarevich--Koch input for an imaginary quadratic field.**  There is an imaginary
quadratic field `F` whose maximal unramified pro-`2` extension carries a
`GolodShafarevichCertificate`: a minimal presentation of `G_∅` with `d = rank₂ Cl(F)`
generators and `r` relators, `r - d ≤ d₂(O_F^×)`, and `rank₂ Cl(F) ≥ 5`.

This is the single arithmetic input of the chapter -- the classical Golod--Shafarevich theorem
for imaginary quadratic fields with many ramified primes (Golod--Shafarevich 1964).  Its
content is: (i) the class-field-theoretic identification `d(G_∅) = rank₂ Cl(F)`; (ii) the
Shafarevich--Koch deficiency bound; (iii) the numerical genus-theory certificate
`rank₂ Cl(F) ≥ 5`, supplied for a concrete field by `Submission.Work.QuadraticFields`. -/
def ShafarevichKochInput (F : Type) [Field F] [NumberField F] : Prop :=
  ∃ (M : MaximalUnramifiedProP.{0} F 2) (d r : ℕ), GolodShafarevichCertificate F M d r

/-- **THE WALL OF THE CHAPTER, with the numerical input made explicit.**  If some imaginary
quadratic field `F` with `rank₂ Cl(F) ≥ 5` carries the Shafarevich--Koch presentation data of
`G_∅`, then `F` has an infinite Hilbert `2`-class field tower. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infiniteHilbertTwoClassFieldTower_of_exists_classGroupTwoRank_ge_five
    (h : ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyComplex F)
        (_ : Module.finrank ℚ F = 2) (hrank : 5 ≤ classGroupTwoRank F),
        ShafarevichKochInput F) :
    InfiniteHilbertTwoClassFieldTower := by
  classical
  obtain ⟨F, iF, iNF, hTC, h2, hrank, hinput⟩ := h
  letI : Field F := iF
  letI : NumberField F := iNF
  letI : NumberField.IsTotallyComplex F := hTC
  obtain ⟨M, d, r, hcert⟩ := hinput
  exact ⟨F, iF, iNF, M, d, r, hcert, infinite_galoisGroup_of_certificate M hcert⟩

end Work.ClassFieldTower
