/-
Copyright (c) 2025. All rights reserved.

# Grünwald in degree `2`, in `H¹` language

`Work.QuadraticLocalGlobal.grunwald_degree_two` (Grünwald's theorem in degree `2`, the prime-`2`
case of Grünwald–Wang) is the arithmetic input of the embedding-problem proof.  In this chapter it
appears as

* `Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective` — the **unconditional** statement that
  the localisation map on square classes `ℚˣ/(ℚˣ)² → ∏ᵢ ℚ_{q_i}ˣ/(ℚ_{q_i}ˣ)²` is surjective for
  finitely many **distinct** primes (the injectivity hypothesis is what excludes repeated primes,
  for which the statement is false);
* `Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective_pi` — the same for the coefficient
  module `μ₂^r` (`A = 𝔽₂^r`), again with the `Function.Injective` correction;
* `Work.AbsoluteKummer.grunwald_h1_surjective` below — the same statement with `H¹(G_ℚ, μ₂)` (resp.
  `∏ᵢ H¹(G_{ℚ_{q_i}}, μ₂)`) as source (resp. target), *conditional* on the local Kummer
  identifications `LocalKummerTwo`.

## The dictionary

The global Kummer isomorphism `kummerEquivRatTwo : ℚˣ/(ℚˣ)² ≃* H¹(G_ℚ, μ₂)`
(`Submission/Work/AbsoluteKummer/Rat.lean`) is unconditional.  The *local* identification
`ℚ_pˣ/(ℚ_pˣ)² ≃* H¹(G_{ℚ_p}, μ₂)` is what would turn the surjectivity of the localisation map on
square classes into a statement about the restriction maps `H¹(G_ℚ, μ₂) → H¹(G_{ℚ_p}, μ₂)`; it is
recorded here as the named hypothesis `LocalKummerTwo`.  The map used below is the composite

`H¹(G_ℚ, μ₂) ≅ ℚˣ/(ℚˣ)² → ∏ᵢ ℚ_{q_i}ˣ/(ℚ_{q_i}ˣ)² ≅ ∏ᵢ H¹(G_{ℚ_{q_i}}, μ₂)`,

which is the natural restriction map once both sides are identified by Kummer theory.  (A genuine
restriction map `H¹(G_ℚ, μ₂) → H¹(G_{ℚ_p}, μ₂)` needs the choice of a decomposition group, i.e. of
an embedding of `ℚ̄` into `ℚ̄_p`; the Kummer identifications make that choice unnecessary.)
-/
import Submission.Work.AbsoluteKummer.SqClass
import Submission.Work.AbsoluteKummer.KummerBijective
import Submission.Work.AbsoluteKummer.Coefficients
import Submission.Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective
import Submission.Work.AbsoluteKummer.Grunwald.Pi
import Submission.Work.AbsoluteKummer.Rat
import Submission.Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer

noncomputable section

/-- The local Kummer identification at `p`, in degree `2`: the named hypothesis that the group
`ℚ_pˣ/(ℚ_pˣ)²` of local square classes is the first continuous cohomology of `G_{ℚ_p}` with
coefficients `μ₂`. -/
abbrev LocalKummerTwo (p : ℕ) [Fact p.Prime] : Prop :=
  Nonempty (((ℚ_[p])ˣ ⧸ Work.Kummer.nthPowerSubgroup 2 (ℚ_[p])ˣ) ≃*
    Multiplicative (H1 (Field.absoluteGaloisGroup ℚ_[p])
      (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ_[p])))))

/-- The local Kummer identification, as an actual multiplicative equivalence, extracted from the
named hypothesis. -/
noncomputable def localKummerTwoEquiv (p : ℕ) [Fact p.Prime] (h : LocalKummerTwo p) :
    (((ℚ_[p])ˣ ⧸ Work.Kummer.nthPowerSubgroup 2 (ℚ_[p])ˣ) ≃*
      Multiplicative (H1 (Field.absoluteGaloisGroup ℚ_[p])
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ_[p]))))) :=
  Classical.choice h

/-! ## The local Kummer identification is unconditional

`LocalKummerTwo p` is *not* an extra hypothesis: it is the `n = 2` case of the Kummer isomorphism
`Work.AbsoluteKummer.kummerEquiv` over the local field `ℚ_p`.  The only obstruction to writing it
down was that Mathlib's `IsAlgClosure` instance for `AlgebraicClosure` is invisible to type class
search for the spelling `AlgebraicClosure ℚ_[p]` (exactly as for `ℚ`, repaired in
`Submission/Work/AbsoluteGalois/Basic.lean`); registering it here (once and for all, for `ℚ_p`)
makes `IsGalois ℚ_[p] (AlgebraicClosure ℚ_[p])` available and the Kummer isomorphism applies
verbatim. -/
instance instIsAlgClosureAlgebraicClosurePadic (p : ℕ) [Fact p.Prime] :
    IsAlgClosure ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
  AlgebraicClosure.instIsAlgClosure ℚ_[p]

/-- `-1` is a primitive second root of unity in `ℚ_p`. -/
theorem isPrimitiveRoot_neg_one_padic (p : ℕ) [Fact p.Prime] :
    IsPrimitiveRoot (-1 : ℚ_[p]) 2 :=
  IsPrimitiveRoot.neg_one (R := ℚ_[p]) 0 (by norm_num)

/-- **The local Kummer identification, unconditionally**: the group `ℚ_pˣ/(ℚ_pˣ)²` of local square
classes is the first continuous cohomology of `G_{ℚ_p}` with coefficients `μ₂`.  This is the
`n = 2` case of `Work.AbsoluteKummer.kummerEquiv`. -/
theorem localKummerTwo (p : ℕ) [Fact p.Prime] : LocalKummerTwo p :=
  ⟨kummerEquiv (k := ℚ_[p]) (n := 2) (ζ := (-1 : ℚ_[p])) (isPrimitiveRoot_neg_one_padic p)⟩

/-- The local Kummer identification, as the *concrete* isomorphism given by Kummer theory over
`ℚ_p` (rather than a `Classical.choice` out of `LocalKummerTwo`). -/
noncomputable def localKummerTwoEquivOfKummer (p : ℕ) [Fact p.Prime] :
    (((ℚ_[p])ˣ ⧸ Work.Kummer.nthPowerSubgroup 2 (ℚ_[p])ˣ) ≃*
      Multiplicative (H1 (Field.absoluteGaloisGroup ℚ_[p])
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ_[p]))))) :=
  kummerEquiv (k := ℚ_[p]) (n := 2) (ζ := (-1 : ℚ_[p])) (isPrimitiveRoot_neg_one_padic p)

/-- **Grünwald's theorem in degree `2`, in `H¹` language.**  For finitely many distinct primes
`q i` and prescribed local cohomology classes in `H¹(G_{ℚ_{q i}}, μ₂)`, there is a global class in
`H¹(G_ℚ, μ₂)` with the prescribed local behaviour.  The arithmetic content is
`Work.AbsoluteKummer.Grunwald.sqClassLocalize_surjective` (i.e.
`Work.QuadraticLocalGlobal.grunwald_degree_two`); the local and global Kummer identifications used
are the unconditional `Work.AbsoluteKummer.localKummerTwo` and
`Work.AbsoluteKummer.kummerEquivRatTwo`. -/
theorem grunwald_h1_surjective {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime]
    (hq : Function.Injective q) :
    Function.Surjective (fun x : H1 (Field.absoluteGaloisGroup ℚ)
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))) =>
      fun i => (localKummerTwoEquivOfKummer (q i)) (sqClassLocalize (q i)
        (kummerEquivRatTwo.symm (Multiplicative.ofAdd x)))) := by
  intro y
  have hsq : Function.Surjective (fun x : SqClass ℚ =>
      fun i => sqClassLocalize (q i) x) := Grunwald.sqClassLocalize_surjective q hq
  obtain ⟨x, hx⟩ := hsq (fun i => (localKummerTwoEquivOfKummer (q i)).symm (y i))
  refine ⟨Multiplicative.toAdd (kummerEquivRatTwo x), ?_⟩
  funext i
  dsimp only
  have h1 : kummerEquivRatTwo.symm (Multiplicative.ofAdd
      (Multiplicative.toAdd (kummerEquivRatTwo x))) = x := by
    rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [h1]
  have hxi : sqClassLocalize (q i) x =
      (localKummerTwoEquivOfKummer (q i)).symm (y i) :=
    congrFun hx i
  rw [hxi]
  exact MulEquiv.apply_symm_apply _ _

/-- **The local–global map in `H¹` language.**  Under the global and local Kummer
identifications, it is the map `ℚˣ/(ℚˣ)² → ∏ᵢ ℚ_{q i}ˣ/(ℚ_{q i}ˣ)²` induced by the localisations
`ℚ → ℚ_{q i}`: the element `x ∈ H¹(G_ℚ, μ₂)` is sent to the family of local classes of a rational
number representing `x`.  Surjectivity of this map, for finitely many **distinct** primes, is
Grünwald's theorem in degree `2` (`Work.AbsoluteKummer.grunwaldLocalMap_surjective`). -/
noncomputable def grunwaldLocalMap {ι : Type*} [Fintype ι] (q : ι → ℕ) [∀ i, Fact (q i).Prime] :
    H1 (Field.absoluteGaloisGroup ℚ) (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))) →
      (∀ i, H1 (Field.absoluteGaloisGroup ℚ_[q i])
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ_[q i])))) :=
  fun x i => localKummerTwoEquivOfKummer (q i)
    (sqClassLocalize (q i) (kummerEquivRatTwo.symm (Multiplicative.ofAdd x)))

/-- **Grünwald's theorem in degree `2` in `H¹` language**: for finitely many *distinct* primes the
local–global map `Work.AbsoluteKummer.grunwaldLocalMap` is surjective. -/
theorem grunwaldLocalMap_surjective {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (hq : Function.Injective q) :
    Function.Surjective (grunwaldLocalMap q) :=
  grunwald_h1_surjective q hq

/-- The (additive) identification `H¹(G_ℚ, μ₂^r) ≃+ (H¹(G_ℚ, μ₂))^r`
(`Work.AbsoluteKummer.H1Pi.nonempty_h1_pi_equiv`), packaged for the `𝔽₂^r`-statement. -/
noncomputable def h1PiEquiv (r : ℕ) :
    H1 (Field.absoluteGaloisGroup ℚ)
        (∀ _ : Fin r, Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))) ≃+
      (∀ _ : Fin r, H1 (Field.absoluteGaloisGroup ℚ)
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ)))) :=
  Classical.choice (H1Pi.nonempty_h1_pi_equiv (G := Field.absoluteGaloisGroup ℚ)
    (fun _ : Fin r => Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))))

/-- **Grünwald's theorem in degree `2` for `A = 𝔽₂^r` (`μ₂^r`), in `H¹` language.**  For finitely
many distinct primes `q i` and prescribed local cohomology classes in
`(H¹(G_{ℚ_{q i}}, μ₂))^r`, there is a global class in `H¹(G_ℚ, μ₂^r)` with the prescribed local
behaviour.  As in `sqClassLocalize_surjective_pi`, the `Function.Injective q` hypothesis is the
distinctness correction: for repeated primes with independent data the statement is false. -/
theorem grunwald_h1_surjective_pi {r : ℕ} {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (hq : Function.Injective q) :
    Function.Surjective (fun x : H1 (Field.absoluteGaloisGroup ℚ)
        (∀ _ : Fin r, Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))) =>
      fun i : ι => fun j : Fin r => (localKummerTwoEquivOfKummer (q i))
        (sqClassLocalize (q i) (kummerEquivRatTwo.symm (Multiplicative.ofAdd (h1PiEquiv r x j))))) := by
  intro y
  have hsurj : ∀ j : Fin r, ∃ xj : H1 (Field.absoluteGaloisGroup ℚ)
      (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))),
      (fun i : ι => (localKummerTwoEquivOfKummer (q i))
        (sqClassLocalize (q i) (kummerEquivRatTwo.symm (Multiplicative.ofAdd xj)))) =
        (fun i : ι => y i j) :=
    fun j => grunwald_h1_surjective q hq (fun i => y i j)
  choose xj hxj using hsurj
  refine ⟨(h1PiEquiv r).symm (fun j => xj j), ?_⟩
  funext i j
  dsimp only
  rw [show h1PiEquiv r ((h1PiEquiv r).symm (fun j => xj j)) j = xj j from
    congrFun (AddEquiv.apply_symm_apply (h1PiEquiv r) (fun j => xj j)) j]
  exact congrFun (hxj j) i


/-- **The local–global map in `H¹` language for the coefficient module `A = μ₂^r = 𝔽₂^r`.** -/
noncomputable def grunwaldLocalMapPi {r : ℕ} {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] :
    H1 (Field.absoluteGaloisGroup ℚ)
        (∀ _ : Fin r, Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))) →
      (∀ i : ι, ∀ _ : Fin r, H1 (Field.absoluteGaloisGroup ℚ_[q i])
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ_[q i])))) :=
  fun x i j => localKummerTwoEquivOfKummer (q i)
    (sqClassLocalize (q i) (kummerEquivRatTwo.symm
      (Multiplicative.ofAdd (h1PiEquiv r x j))))

/-- **Grünwald's theorem in degree `2` for `A = μ₂^r`, in `H¹` language**: for finitely many
*distinct* primes the local–global map `Work.AbsoluteKummer.grunwaldLocalMapPi` is surjective.  The
`Function.Injective q` hypothesis is the distinctness correction (the statement fails for repeated
primes with independent local data). -/
theorem grunwaldLocalMapPi_surjective {r : ℕ} {ι : Type*} [Fintype ι] (q : ι → ℕ)
    [∀ i, Fact (q i).Prime] (hq : Function.Injective q) :
    Function.Surjective (grunwaldLocalMapPi (r := r) q) :=
  grunwald_h1_surjective_pi q hq

end

end Work.AbsoluteKummer
