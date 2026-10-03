import Mathlib
import Submission.Work.ORLyndon.LyndonIndependenceDefs
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.OROneRel.Basic
import Submission.Work.ORLyndon.lyndon_independence
import Submission.Work.ORLyndon.lyndon_ker_theta_of_independence
import Submission.Work.ORLyndon.lyndon_ker_theta_le
import Submission.Work.ORLyndon.mem_span_of_coset_sums
import Submission.Work.ORLyndon.foxD_pow
import Submission.Work.ORLyndon.Magnus
import Submission.Work.OROneRel.kms_torsion_at
import Submission.Work.OROneRel.not_isProperPower_of
import Submission.Work.OROneRel.theta_apply_rewrite
import Submission.Work.OROneRel.magRewRel_pow

/-!
# The Cohen--Lyndon input, and what it follows from

**See `Submission/Work/ORLyndon/NOTES_lyndon_independence_of_pow.md` for the current route
analysis: the proved reductions, the three candidate routes with references, the structural
findings (the `σ_t`-grading `K[G] = K[ker σ_t][τ^{±1}; conj]`), the dead ends, and a tempting
shortcut that is *false*.**

Requested statement (`Work.ORLyndon.lyndon_independence_of_pow`, kept verbatim below): for
`r = u ^ l` with `1 ≤ l` and `u` not a proper power, the vectors `g • (∂r/∂x)_x` attached to group
elements `g` in pairwise distinct `⟨presentRho r u⟩`-cosets are `K`-linearly independent.

## Status of this statement

This is the **module form of the Cohen--Lyndon / Lyndon identity theorem**: a true classical
theorem (Lyndon 1950; Cohen--Lyndon 1963; simpler proofs by Karrass--Solitar 1972 and Burns 1974),
and it is *exactly* the input that the rest of this chapter assumes.  By the two lemmas already in
the workspace,

* `Work.ORLyndon.lyndon_independence_of_ker_theta` (`lyndon_independence.lean`), and
* `Work.ORLyndon.lyndon_ker_theta_of_independence` (`lyndon_ker_theta_of_independence.lean`),

`LyndonIndependence K r u` is **equivalent** to `ker θ ≤ K[G](w - 1)`, `w = presentRho r u`, i.e. to
the `ker_theta` component of the hypothesis structure `Work.ORLyndon.LyndonIdentity` on which the
whole `ORLyndon` chapter is built.  The chapter `README.md` records this statement as "the one
classical input that is *not* a consequence of the four theorems bundled in
`Work.OROneRel.OneRelatorCombinatorics`" and asks that it be given "a formal owner"; the recorded
review of this very request says the same ("closing this `sorry` means formalizing Cohen--Lyndon —
enormous, and the existing reductions cannot do it").

This file records the reduction structure, all of it proved:

* `Work.ORLyndon.relatorVec_eq_rootVec_smul` — the Fox derivative of a power is the norm element of
  the root times the Fox vector of the root, `(∂u^l/∂x)_x = (1 + w + ⋯ + w^{l-1}) • (∂u/∂x)_x`; this
  is what makes the statement for `r = u ^ l` a statement about the root `u`;
* `Work.ORLyndon.lyndonIndependence_iff_ker_theta_le` — the equivalence with `ker θ ≤ K[G](w - 1)`,
  hence with `LyndonIdentity`;
* `Work.ORLyndon.orderOf_presentRho` — `orderOf (presentRho r u) = l`; this is the order half of the
  Karrass--Magnus--Solitar torsion theorem, stated as a theorem of the workspace
  (`Work.OROneRel.kms_torsion_at`) through the root-tracked Magnus step
  (`Submission/Work/OROneRel/magnus_step_root.lean`).  Caveat for the project's bookkeeping: that
  file still contains `sorry`s (its own header explains that the root-tracked Magnus step is exactly
  what the Freiheitssatz method cannot give without the Masters/Linton cyclic-cover construction),
  so this lemma — and the reduction below that uses it — rests on that unproved step;
* `Work.ORLyndon.coeff_mul_normElem` — the coefficient of `g` in `a * N` is the sum of the
  coefficients of `a` over the right coset `g⟨w⟩` (this is where the order statement is used);
* `Work.ORLyndon.lyndonIndependence_of_rootVec_dvd` and
  `Work.ORLyndon.lyndonIndependence_of_rootVec_annihilator` — **the reductions**: the statement
  follows from `ann_{K[G]}(∂u/∂x) = 0` for the Fox vector of the *root*, equivalently from the
  component-wise hypothesis that some `(∂u/∂x)_x` is a right non-zero-divisor of `K[G]`.  The latter
  is the "β acts injectively" statement of the project's own route (`ROUTE_LEAD.md`, discussion of
  JL Lemma 5.1), needed there with the division closure `S` in place of the division ring `D`.

That last input is *strictly stronger* than the requested statement (it implies it via the reduction
above), so it cannot replace the statement inside the workspace: as the review of this request says,
there is no *weaker* input in the library from which the requested statement follows.  Note also
that the classical route to the statement does **not** go through it: Lyndon's identity theorem is
purely combinatorial (Lyndon 1950; Cohen--Lyndon 1963 proved it "via the usual Magnus hierarchy but
with a stronger inductive hypothesis").  Closing the statement therefore means formalizing
Cohen--Lyndon: the Magnus hierarchy together with the relation modules of its HNN steps — a chapter
the route design does not contain, and the reason the `ORLyndon` chapter keeps `LyndonIdentity`
(equivalently, this statement) as an explicit assumed input.

## The classical induction, and where it stands

The workspace has the one-relator combinatorics with the root tracked
(`Work.OROneRel.kms_torsion_at`, `Work.OROneRel.magnus_step_root`), so the classical induction on
`relatorNorm` is now in reach in shape:

* **base case** `relatorNorm u ≤ 1`, i.e. `u = FreeGroup.of a` (the case `u = 1` is excluded by
  `¬ IsProperPower u`): **proved in this file**, as `Work.ORLyndon.lyndonIndependence_of_letterPow`,
  with the component computation `Work.ORLyndon.relatorVec_letterPow`.  Axiom check:
  `relatorVec_letterPow` rests only on `propext, Classical.choice, Quot.sound`; the base case itself
  additionally uses the workspace's KMS chain (`orderOf_presentRho`), which as noted above still
  rests on `sorry`s in `Submission/Work/OROneRel/magnus_step_root.lean`;
* **induction step** (the crux, still missing): `HasMagnusStep` exhibits `⟨α | u ^ l⟩` as an HNN
  extension of `⟨β | v ^ l⟩` with `relatorNorm v < relatorNorm u` and with the class of `u`
  conjugate to the class of `v` in the base.  The step has to transport the independence statement
  across this HNN extension, i.e. compute the relation module of an HNN step (Mayer--Vietoris) and
  the image of the Fox vector under it.  Developing the *statement* of that step — whose hypotheses
  must record the presentation-level compatibility, not merely the group isomorphism — is the next
  task, and only after that can it be delegated.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

variable {X : Type*} [DecidableEq X] {K : Type*} [Field K]

/-- The Fox vector `(∂u/∂x)_x` of the **root** `u`, pushed into `K[G]` along the presentation
`F(X) →* ⟨X | r⟩` (`relatorVec K r` is the case `u = r`). -/
noncomputable def rootVec (K : Type*) [Field K] {X : Type*} [DecidableEq X]
    (r u : FreeGroup X) : X →₀ MonoidAlgebra K (OneRelatorGroup r) :=
  (foxFD (K := K) u).mapRange (presentAlg K r) (map_zero _)

@[simp] theorem rootVec_apply (r u : FreeGroup X) (x : X) :
    rootVec K r u x = presentAlg K r (foxD (K := K) x u) := by
  rw [rootVec, Finsupp.mapRange_apply, foxFD_apply]

/-- `presentAlg` carries the powers of `u` to the powers of `presentRho r u`. -/
theorem presentAlg_of_pow (r u : FreeGroup X) (j : ℕ) :
    presentAlg K r ((MonoidAlgebra.of K (FreeGroup X)) (u ^ j)) =
      ((MonoidAlgebra.of K (OneRelatorGroup r)) (presentRho r u)) ^ j := by
  rw [presentAlg_of, map_pow, map_pow]

/-- **The Fox derivative of a power.**  For `r = u ^ l` the Fox vector of the relator is the norm
element `1 + w + ⋯ + w ^ (l - 1)` (`w = presentRho r u`) times the Fox vector of the root:
`(∂r/∂x)_x = (1 + w + ⋯ + w ^ (l-1)) • (∂u/∂x)_x ∈ K[G]^X`. -/
theorem relatorVec_eq_rootVec_smul (r u : FreeGroup X) (l : ℕ) (hpow : r = u ^ l) :
    relatorVec K r = (normElem K l (presentRho r u)) • rootVec K r u := by
  subst hpow
  apply Finsupp.ext
  intro x
  rw [Finsupp.smul_apply, relatorVec_apply, rootVec_apply, smul_eq_mul, normElem, foxD_pow, map_mul,
    map_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by
    rw [← map_pow]
    exact presentAlg_of_pow (X := X) (K := K) (u ^ l) u j

/-- **The statement is exactly the annihilator half of Lyndon's identity theorem.**  For `r = u ^ l`
with `1 ≤ l`, the Cohen--Lyndon independence in module form is equivalent to
`ker θ ⊆ K[G](w - 1)`, `w = presentRho r u`, i.e. to the `ker_theta` component of
`Work.ORLyndon.LyndonIdentity`. -/
theorem lyndonIndependence_iff_ker_theta_le (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) :
    LyndonIndependence K r u ↔
      LinearMap.ker (lyndonTheta K r) ≤
        Ideal.span {((MonoidAlgebra.of K (OneRelatorGroup r)) (presentRho r u)) - 1} :=
  ⟨lyndon_ker_theta_of_independence r u l hpos hpow,
    fun hker => lyndon_independence_of_ker_theta r u l hpos hpow hker⟩

/-- The powers `w ^ k`, `k < l`, are distinct as soon as `w` has order exactly `l`. -/
theorem pow_inj_of_orderOf_eq {G : Type*} [Group G] {w : G} {l : ℕ} (hord : orderOf w = l)
    {k k' : ℕ} (hk : k < l) (hk' : k' < l) (h : w ^ k = w ^ k') : k = k' := by
  have hmod : k ≡ k' [MOD orderOf w] := pow_eq_pow_iff_modEq.mp h
  rw [hord] at hmod
  exact Nat.ModEq.eq_of_lt_of_lt hmod hk hk'

/-- Reindexing: for `f l = f 0`, the exponents `l - k` (`k < l`) may be replaced by `k`
(used with `f k = a.coeff (g * w ^ k)` and `w ^ l = 1`). -/
theorem sum_range_sub_eq_sum_range {R : Type*} [AddCommGroup R] (f : ℕ → R) {l : ℕ}
    (heq : f l = f 0) :
    (∑ k ∈ Finset.range l, f (l - k)) = ∑ k ∈ Finset.range l, f k := by
  have h1 : (∑ k ∈ Finset.range l, f (l - k)) = ∑ j ∈ Finset.range l, f (j + 1) := by
    have h := Finset.sum_range_reflect (fun j => f (j + 1)) l
    rw [← h]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < l := Finset.mem_range.mp hj
    congr 1
    omega
  have key : (∑ j ∈ Finset.range l, f (j + 1)) + f 0 = (∑ j ∈ Finset.range l, f j) + f l := by
    rw [← Finset.sum_range_succ' f l, ← Finset.sum_range_succ f l]
  rw [h1]
  have hcancel : (∑ j ∈ Finset.range l, f (j + 1)) + f 0 = (∑ j ∈ Finset.range l, f j) + f 0 := by
    rw [key, heq]
  exact add_right_cancel hcancel

/-- **The coefficient identity for the norm element.**  The coefficient of `g` in `a * N`,
`N = 1 + w + ⋯ + w ^ (l - 1)` with `w = presentRho r u`, is the sum of the coefficients of `a` over
the right `⟨w⟩`-coset `g⟨w⟩ = {g * w ^ k : k < l}`: the powers in `N` enter the convolution as the
inverse powers `(w ^ k)⁻¹ = w ^ (l - k)`, which — because `w` has order exactly `l` — enumerate the
same coset without repetition. -/
theorem coeff_mul_normElem (r u : FreeGroup X) (l : ℕ) (_hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hord : orderOf (presentRho r u) = l) (a : MonoidAlgebra K (OneRelatorGroup r))
    (g : OneRelatorGroup r) :
    (a * normElem K l (presentRho r u)).coeff g = (uCoset r u l g).sum (fun h => a.coeff h) := by
  classical
  set w : OneRelatorGroup r := presentRho r u with hw
  have hwpow : w ^ l = 1 := by
    rw [hw, ← map_pow, ← hpow, presentRho_relator]
  -- the convolution sum, in inverse powers of `w`
  have hconv : (a * normElem K l w).coeff g
      = ∑ k ∈ Finset.range l, a.coeff (g * (w ^ k)⁻¹) := by
    rw [normElem, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← map_pow, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply, mul_one]
  -- `(w ^ k)⁻¹ = w ^ (l - k)`
  have hinv : ∀ k ∈ Finset.range l, (w ^ k)⁻¹ = w ^ (l - k) := by
    intro k hk
    have hk' : k ≤ l := le_of_lt (Finset.mem_range.mp hk)
    exact ((eq_inv_iff_mul_eq_one (a := w ^ (l - k)) (b := w ^ k)).mpr (by
      rw [← pow_add, Nat.sub_add_cancel hk', hwpow])).symm
  have hstep2 : (∑ k ∈ Finset.range l, a.coeff (g * (w ^ k)⁻¹))
      = ∑ k ∈ Finset.range l, a.coeff (g * w ^ (l - k)) :=
    Finset.sum_congr rfl fun k hk => by rw [hinv k hk]
  have hstep3 : (∑ k ∈ Finset.range l, a.coeff (g * w ^ (l - k)))
      = ∑ k ∈ Finset.range l, a.coeff (g * w ^ k) :=
    sum_range_sub_eq_sum_range (fun k => a.coeff (g * w ^ k)) (by rw [hwpow, pow_zero])
  -- the range sum is the coset sum
  have hinj : Set.InjOn (fun k : Fin l => g * w ^ (k : ℕ)) ↑(Finset.univ : Finset (Fin l)) := by
    intro k _ k' _ h
    exact Fin.ext (pow_inj_of_orderOf_eq hord k.2 k'.2 (mul_left_cancel h))
  have hcoset : (uCoset r u l g).sum (fun h => a.coeff h)
      = ∑ k : Fin l, a.coeff (g * w ^ (k : ℕ)) := by
    rw [uCoset]
    exact Finset.sum_image (f := fun h => a.coeff h) (s := Finset.univ) hinj
  have hrange : (∑ k : Fin l, a.coeff (g * w ^ (k : ℕ)))
      = ∑ k ∈ Finset.range l, a.coeff (g * w ^ k) := by
    rw [Finset.sum_fin_eq_sum_range]
    exact Finset.sum_congr rfl fun i hi => by rw [dif_pos (Finset.mem_range.mp hi)]
  exact hconv.trans (hstep2.trans (hstep3.trans (hrange.symm.trans hcoset.symm)))

/-- **The order of the root.**  `orderOf (presentRho r u) = l` for `r = u ^ l`, `1 ≤ l`, `u` not a
proper power: the order half of the Karrass--Magnus--Solitar torsion theorem, which is *proved*
unconditionally in the workspace (`Work.OROneRel.kms_torsion_at`, via the Magnus hierarchy of
`Submission/Work/OROneRel/magnus_step_root.lean`). -/
theorem orderOf_presentRho (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) : orderOf (presentRho r u) = l :=
  (Work.OROneRel.kms_torsion_at r u l hpos hpow hpp).1

/-- **The reduction.**  The requested statement follows from: the Fox derivative of the *root* with
respect to some letter is a right non-zero-divisor of `K[G]`.

For `a` in the kernel of `θ`, the power rule `relatorVec_eq_rootVec_smul` gives
`(a * N) • rootVec = 0`, hence `a * N = 0` by the injectivity input; since `w` has order exactly
`l` (KMS, `orderOf_presentRho`), `a * N = 0` says that all coset sums of `a` vanish, and
`a ∈ K[G](w - 1)` follows from `Work.ORLyndon.mem_span_of_coset_sums`, giving `LyndonIndependence`
by `Work.ORLyndon.lyndon_independence_of_ker_theta`. -/
theorem lyndonIndependence_of_rootVec_dvd (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u) (x : X)
    (hdiv : ∀ b : MonoidAlgebra K (OneRelatorGroup r), b * rootVec K r u x = 0 → b = 0) :
    LyndonIndependence K r u := by
  classical
  have hord : orderOf (presentRho r u) = l := orderOf_presentRho r u l hpos hpow hpp
  refine lyndon_independence_of_ker_theta r u l hpos hpow ?_
  intro a ha
  have hker : a • relatorVec K r = 0 := by
    rw [← lyndonTheta_apply]
    exact LinearMap.mem_ker.mp ha
  have haN : a * normElem K l (presentRho r u) = 0 := by
    have h0 : (a * normElem K l (presentRho r u)) • rootVec K r u = 0 := by
      rw [mul_smul, ← relatorVec_eq_rootVec_smul r u l hpow]
      exact hker
    have h1 := congrArg (fun v : X →₀ MonoidAlgebra K (OneRelatorGroup r) => v x) h0
    simpa only [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul] using hdiv _ h1
  refine mem_span_of_coset_sums r u l hpos hpow a ?_
  intro g
  rw [← coeff_mul_normElem r u l hpos hpow hord a g, haN]
  exact Finsupp.zero_apply

/-- **The reduction, in its weakest form.**  It is enough that the Fox vector of the *root* `u`
have trivial annihilator in `K[G]`: for `a` in the kernel of `θ`, the power rule gives
`(a * N) • rootVec = 0`, so `a * N = 0`, and then `a ∈ K[G](w - 1)`.  (The component-wise version
`lyndonIndependence_of_rootVec_dvd` above, with a right non-zero-divisor, implies this hypothesis
and is the form in which the project's own route needs it.) -/
theorem lyndonIndependence_of_rootVec_annihilator (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hann : ∀ b : MonoidAlgebra K (OneRelatorGroup r), b • rootVec K r u = 0 → b = 0) :
    LyndonIndependence K r u := by
  classical
  refine lyndon_independence_of_ker_theta r u l hpos hpow ?_
  intro a ha
  have hker : a • relatorVec K r = 0 := by
    rw [← lyndonTheta_apply]
    exact LinearMap.mem_ker.mp ha
  have haN : a * normElem K l (presentRho r u) = 0 := by
    have h0 : (a * normElem K l (presentRho r u)) • rootVec K r u = 0 := by
      rw [mul_smul, ← relatorVec_eq_rootVec_smul r u l hpow]
      exact hker
    exact hann _ h0
  refine mem_span_of_coset_sums r u l hpos hpow a ?_
  intro g
  rw [← coeff_mul_normElem r u l hpos hpow (orderOf_presentRho r u l hpos hpow hpp) a g, haN]
  exact Finsupp.zero_apply

/-- **The reduction, when the root's Fox vector has a unit component.**  If one component
`(∂u/∂x)_x` of the Fox vector of the *root* is a unit of `K[G]` — for instance when the letter `x`
occurs exactly once in `u`, so that `(∂u/∂x)_x` is (up to sign) a single group element, as happens
at the bottom of the Magnus hierarchy — then the requested statement holds. -/
theorem lyndonIndependence_of_rootVec_isUnit (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hpp : ¬ Work.OROneRel.IsProperPower u) (x : X)
    (hunit : IsUnit (rootVec K r u x)) : LyndonIndependence K r u := by
  classical
  obtain ⟨w, hw⟩ := hunit
  refine lyndonIndependence_of_rootVec_dvd r u l hpos hpow hpp x fun b hb => ?_
  calc b = (b * (w : MonoidAlgebra K (OneRelatorGroup r))) * (↑w⁻¹ : MonoidAlgebra K _) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = (b * rootVec K r u x) * (↑w⁻¹ : MonoidAlgebra K _) := by rw [hw]
    _ = 0 := by rw [hb, zero_mul]

/-- The Fox vector of a power of a single generator: the norm element of `ā` in the `a`-component
and `0` in every other component. -/
theorem relatorVec_letterPow {α : Type*} [DecidableEq α] (a : α) (l : ℕ) (x : α) :
    relatorVec K ((FreeGroup.of a) ^ l) x =
      if x = a then normElem K l (presentRho ((FreeGroup.of a) ^ l) (FreeGroup.of a)) else 0 := by
  rw [relatorVec_apply, foxD_pow, foxD_of]
  by_cases hax : a = x
  · rw [if_pos hax, if_pos hax.symm, mul_one, map_sum, normElem]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← map_pow]
      exact presentAlg_of_pow (X := α) (K := K) ((FreeGroup.of a) ^ l) (FreeGroup.of a) k
  · rw [if_neg hax, mul_zero, map_zero, if_neg (fun h : x = a => hax h.symm)]

/-- **The base case of the classical induction.**  For a relator that is a power of a single
generator, `u = FreeGroup.of a`, the Fox vector of `u ^ l` is the norm element `N = 1 + ā + ⋯ +
ā ^ (l-1)` in the `a`-component and vanishes in every other component.  Hence a linear relation
`∑ j, c j • (of (g j) • relatorVec K ((of a) ^ l)) = 0` says, in the `a`-component,
`∑ j, c j • (of (g j) * N) = 0`.  The support of `of g * N` is the coset `g⟨ā⟩`, so for `g j`,
`g i` in distinct `⟨ā⟩`-cosets the coefficient of `g i` in the `j`-th summand is `0` for `j ≠ i`,
while for `j = i` only the term `ā ^ 0` contributes, so that coefficient is `1` — here one uses that
`ā ^ k ≠ 1` for `0 < k < l`, which follows from `orderOf_presentRho` (KMS) since `ā` has order
exactly `l`.  Reading off the coefficient of `g i` gives `c i = 0`. -/
theorem lyndonIndependence_of_letterPow {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (a : α) (l : ℕ) (hpos : 1 ≤ l) :
    LyndonIndependence K ((FreeGroup.of a) ^ l) (FreeGroup.of a) := by
  classical
  intro ι _ g c hcos hsum i
  set w : OneRelatorGroup ((FreeGroup.of a) ^ l) :=
    presentRho ((FreeGroup.of a) ^ l) (FreeGroup.of a) with hw
  have hpp : ¬ Work.OROneRel.IsProperPower (FreeGroup.of a) :=
    Work.OROneRel.not_isProperPower_of a
  have hord : orderOf w = l := by
    rw [hw]
    exact orderOf_presentRho ((FreeGroup.of a) ^ l) (FreeGroup.of a) l hpos rfl hpp
  have hvec : ∀ x : α, relatorVec K ((FreeGroup.of a) ^ l) x
      = if x = a then normElem K l w else 0 := by
    intro x
    rw [relatorVec_letterPow, hw]
  -- (2) the `a`-component of the relation
  have hcomp : ∑ j, c j • ((MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l)) (g j))
      * normElem K l w) = 0 := by
    have h0 := congrArg
      (fun v : α →₀ MonoidAlgebra K (OneRelatorGroup ((FreeGroup.of a) ^ l)) => v a) hsum
    rw [Finsupp.finsetSum_apply, Finsupp.zero_apply] at h0
    have h1 : ∀ j, ((c j • ((MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l)) (g j))
        • relatorVec K ((FreeGroup.of a) ^ l))) a)
        = c j • ((MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l)) (g j))
          * normElem K l w) := by
      intro j
      rw [Finsupp.smul_apply, Finsupp.smul_apply, hvec a, if_pos rfl]
      exact congrArg (fun z => c j • z) (by rw [smul_eq_mul])
    rw [Finset.sum_congr rfl fun j _ => h1 j] at h0
    exact h0
  -- (3) the coefficient of `g i` in the `j`-th summand
  have hmul_coeff : ∀ p q y : OneRelatorGroup ((FreeGroup.of a) ^ l),
      ((MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l)) p)
        * (MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l)) q)).coeff y
        = if p * q = y then 1 else 0 := by
    intro p q y
    rw [← map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single]
    by_cases h : p * q = y
    · rw [if_pos h, ← h, Finsupp.single_eq_same]
    · rw [if_neg h, Finsupp.single_eq_of_ne (Ne.symm h)]
  have hN : normElem K l w = ∑ k ∈ Finset.range l,
      MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l)) (w ^ k) := by
    rw [normElem]
    exact Finset.sum_congr rfl fun k _ =>
      (map_pow (MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l))) w k).symm
  have hcoeff : ∀ j : ι,
      ((MonoidAlgebra.of K (OneRelatorGroup ((FreeGroup.of a) ^ l)) (g j))
        * normElem K l w).coeff (g i) = if j = i then 1 else 0 := by
    intro j
    rw [hN, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    by_cases hji : j = i
    · rw [hji]
      rw [if_pos rfl]
      rw [Finset.sum_eq_single 0]
      · rw [hmul_coeff, if_pos (by rw [pow_zero, mul_one])]
      · intro k hk hk0
        rw [hmul_coeff, if_neg]
        intro hcon
        have hklt : k < l := Finset.mem_range.mp hk
        have hwk : w ^ k = 1 := by
          have h := congrArg (fun z => (g i)⁻¹ * z) hcon
          simpa [mul_assoc] using h
        have hle : l ≤ k := Nat.le_of_dvd (by omega) (by
          rw [← hord]
          exact orderOf_dvd_iff_pow_eq_one.mpr hwk)
        omega
      · intro h0
        exact absurd (Finset.mem_range.mpr (by omega : 0 < l)) h0
    · rw [if_neg hji]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hmul_coeff, if_neg]
      intro hcon
      exact hcos i j (Ne.symm hji) (k : ℤ) (by rw [zpow_natCast]; exact hcon.symm)
  -- (4) read off `c i`
  have h0 := congrArg
    (fun z : MonoidAlgebra K (OneRelatorGroup ((FreeGroup.of a) ^ l)) => z.coeff (g i)) hcomp
  rw [MonoidAlgebra.coeff_zero, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h0
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [MonoidAlgebra.coeff_smul_apply, hcoeff j, smul_eq_mul])] at h0
  rw [Finset.sum_eq_single i] at h0
  · simpa using h0
  · intro j _ hji
    rw [if_neg hji, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **The telescoping identity** behind the HNN step's `hzeta` hypothesis: a root whose exponent
sum in `t` vanishes (`sigma t u = 1` in the multiplicative notation of `Work.OROneRel.sigma`, i.e.
exponent sum `0`) is the ζ-expansion of its Magnus rewriting.  Immediate from
`Work.OROneRel.theta_apply_rewrite_mk_eq_zeta`. -/
theorem eq_zeta_magRewRel {α : Type*} [DecidableEq α] (t : α) (u : FreeGroup α)
    (hsigma : Work.OROneRel.sigma t u = 1) :
    u = Work.OROneRel.zeta t (Work.OROneRel.magRewRel t u) := by
  have hL : Work.OROneRel.sigmaList t u.toWord = 0 :=
    Work.OROneRel.theta_apply_rewrite_sigmaList_eq_zero (t := t) (L := u.toWord)
      (by rw [FreeGroup.mk_toWord]; exact hsigma)
  have h := Work.OROneRel.theta_apply_rewrite_mk_eq_zeta (t := t) (L := u.toWord) hL
  rw [FreeGroup.mk_toWord] at h
  rwa [Work.OROneRel.magRewRel_eq_mk_rewrite]

/-! ## The endgame: reductions that do not use the Karrass--Magnus--Solitar chain

The reductions `lyndonIndependence_of_rootVec_dvd` and `lyndonIndependence_of_rootVec_isUnit` above
are the component-wise form of the route through `ann(rootVec) = 0`, but they consume the *exact
order* of the root (`orderOf_presentRho`, hence the Karrass--Magnus--Solitar torsion theorem, which
currently rests on `sorry`s in `Submission/Work/OROneRel/magnus_step_root.lean`).

The three lemmas below give the same reductions in a form whose *proof* uses only the definitional
norm element `∑_{k < l} w ^ k`: no torsion theorem is consumed, so they are `sorryAx`-free.  They
are the interface for the induction of the Cohen--Lyndon theorem (see the notes file).

* `ann_rootVec_of_component` -- injectivity of the whole root Fox vector follows from the
  component-wise statement for a single letter;
* `lyndon_independence_of_rootVec_inj` -- the requested statement follows from the injectivity of
  multiplication by the root Fox vector, together with the order input `orderOf w = l` (the order
  input is *unavoidable*: the two statements are false without it). -/

/-- **Component-wise injectivity.**  If one component `(∂u/∂x)_x` of the root Fox vector is right
regular, then the whole vector has trivial annihilator. -/
theorem ann_rootVec_of_component (r u : FreeGroup X) (x : X)
    (h : ∀ b : MonoidAlgebra K (OneRelatorGroup r), b * rootVec K r u x = 0 → b = 0) :
    ∀ b : MonoidAlgebra K (OneRelatorGroup r), b • rootVec K r u = 0 → b = 0 := by
  intro b hb
  refine h b ?_
  have h1 := congrArg (fun v : X →₀ MonoidAlgebra K (OneRelatorGroup r) => v x) hb
  simpa only [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul] using h1

/-- **The endgame in terms of the injectivity of the root Fox vector.**  Let `r = u ^ l`, `1 ≤ l`,
and suppose that the class `w = presentRho r u` of the root has order exactly `l` (the
Karrass--Magnus--Solitar order statement).  If multiplication by the Fox vector `(∂u/∂x)_x` of the
*root* is injective on `K[G]`, then the Cohen--Lyndon independence holds.

Proof: for `a = ∑_i c i · of (g i)` with the `g i` in pairwise distinct `⟨w⟩`-cosets, the hypothesis
`a • relatorVec = 0` of the statement is, by the power rule `relatorVec_eq_rootVec_smul`, the
equation `(a * N) • rootVec = 0` for the norm element `N = ∑_{k<l} w ^ k`, so `a * N = 0` by
injectivity.  Reading off the coefficient of `g i` in `a * N` gives `c i`: for `j ≠ i` the elements
`g j * w ^ k` (`k < l`) stay outside the coset of `g i`; for `j = i`, only `k = 0` contributes
because `w` has order exactly `l`. -/
theorem lyndon_independence_of_rootVec_inj (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hord : orderOf (presentRho r u) = l)
    (hinj : ∀ b : MonoidAlgebra K (OneRelatorGroup r), b • rootVec K r u = 0 → b = 0) :
    LyndonIndependence K r u := by
  intro ι _ g c hcos hsum i
  classical
  set w : OneRelatorGroup r := presentRho r u with hw
  set a : MonoidAlgebra K (OneRelatorGroup r) :=
    ∑ j, c j • (MonoidAlgebra.of K (OneRelatorGroup r)) (g j) with ha
  -- Step 1: the linear combination `a` annihilates the Fox vector of the relator
  have hsum' : a • relatorVec K r = 0 := by
    rw [ha, Finset.sum_smul]
    rw [Finset.sum_congr rfl fun j _ => smul_assoc (c j) _ _]
    exact hsum
  -- Step 2: `a * N = 0` by injectivity and the power rule
  have haN : a * normElem K l w = 0 := by
    refine hinj _ ?_
    rw [mul_smul, ← relatorVec_eq_rootVec_smul r u l hpow]
    exact hsum'
  -- Step 3: the coefficient of `g i` in `a * N`
  have hN : normElem K l w =
      ∑ k ∈ Finset.range l, MonoidAlgebra.of K (OneRelatorGroup r) (w ^ k) := by
    rw [normElem]
    exact Finset.sum_congr rfl fun k _ => (map_pow _ w k).symm
  have hpow_ne : ∀ k : ℕ, k < l → k ≠ 0 → w ^ k ≠ 1 := by
    intro k hk hk0 h
    have hdvd : l ∣ k := by
      rw [← hord]
      exact orderOf_dvd_iff_pow_eq_one.mpr h
    exact hk0 (Nat.eq_zero_of_dvd_of_lt hdvd hk)
  have hcoeff : ∀ j : ι,
      (((MonoidAlgebra.of K (OneRelatorGroup r) (g j)) * normElem K l w).coeff (g i))
        = if j = i then (1 : K) else 0 := by
    intro j
    rw [hN, Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    have hstep : ∀ k ∈ Finset.range l,
        ((MonoidAlgebra.of K (OneRelatorGroup r) (g j) *
          MonoidAlgebra.of K (OneRelatorGroup r) (w ^ k)).coeff (g i))
          = if k = 0 ∧ j = i then (1 : K) else 0 := by
      intro k hk
      rw [← map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases hk0 : k = 0
      · subst hk0
        by_cases hji : j = i
        · rw [if_pos (by rw [pow_zero, mul_one, hji]), if_pos ⟨rfl, hji⟩]
        · rw [if_neg (fun hcon => hcos i j (Ne.symm hji) 0 (by simpa using hcon.symm)),
            if_neg (fun h : 0 = 0 ∧ j = i => hji h.2)]
      · have hne : g j * w ^ k ≠ g i := by
          intro hcon
          by_cases hji : j = i
          · have h2 : g i * w ^ k = g i * 1 := by rw [hji] at hcon; rw [mul_one]; exact hcon
            exact hpow_ne k (Finset.mem_range.mp hk) hk0 (mul_left_cancel h2)
          · exact hcos i j (Ne.symm hji) (k : ℤ) (by rw [zpow_natCast]; exact hcon.symm)
        rw [if_neg hne, if_neg (fun h : k = 0 ∧ j = i => hk0 h.1)]
    rw [Finset.sum_congr rfl hstep]
    by_cases hji : j = i
    · rw [if_pos hji, Finset.sum_eq_single 0]
      · rw [if_pos ⟨rfl, hji⟩]
      · intro k hk hk0
        rw [if_neg (fun h : k = 0 ∧ j = i => hk0 h.1)]
      · intro h0
        exact absurd (Finset.mem_range.mpr (by omega)) h0
    · rw [if_neg hji, Finset.sum_eq_zero]
      intro k hk
      rw [if_neg (fun h : k = 0 ∧ j = i => hji h.2)]
  have hterm : ∀ j : ι,
      (((c j • (MonoidAlgebra.of K (OneRelatorGroup r)) (g j)) *
        normElem K l w).coeff (g i)) = if j = i then c j else 0 := by
    intro j
    rw [smul_mul_assoc, MonoidAlgebra.coeff_smul_apply, smul_eq_mul, hcoeff j]
    by_cases hji : j = i
    · rw [if_pos hji, if_pos hji, mul_one]
    · rw [if_neg hji, if_neg hji, mul_zero]
  have hcoeff_i : (a * normElem K l w).coeff (g i) = c i := by
    rw [ha, Finset.sum_mul, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [if_neg hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [← hcoeff_i, haN]
  simp

/-- **The reduction, in the component-wise form, without the torsion chain.**  It is enough that one
component `(∂u/∂x)_x` of the Fox vector of the *root* be right regular, together with the order
input `orderOf w = l`.  (The statement `lyndonIndependence_of_rootVec_dvd` above draws the
conclusion from the same hypothesis, but through `orderOf_presentRho`; this version avoids that
dependency, which is what the final proof needs.) -/
theorem lyndon_independence_of_rootVec_regular (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hord : orderOf (presentRho r u) = l) (x : X)
    (hdiv : ∀ b : MonoidAlgebra K (OneRelatorGroup r), b * rootVec K r u x = 0 → b = 0) :
    LyndonIndependence K r u :=
  lyndon_independence_of_rootVec_inj r u l hpos hpow hord
    (ann_rootVec_of_component r u x hdiv)

/-- **The reduction when a component of the root Fox vector is a unit** (for instance when the
letter `x` occurs exactly once in `u`), in the `sorryAx`-free form. -/
theorem lyndon_independence_of_rootVec_isUnit' (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l)
    (hpow : r = u ^ l) (hord : orderOf (presentRho r u) = l) (x : X)
    (hunit : IsUnit (rootVec K r u x)) : LyndonIndependence K r u := by
  obtain ⟨v, hv⟩ := hunit
  refine lyndon_independence_of_rootVec_regular r u l hpos hpow hord x fun b hb => ?_
  calc b = (b * (v : MonoidAlgebra K (OneRelatorGroup r))) *
        (↑v⁻¹ : MonoidAlgebra K (OneRelatorGroup r)) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
    _ = (b * rootVec K r u x) * (↑v⁻¹ : MonoidAlgebra K (OneRelatorGroup r)) := by rw [hv]
    _ = 0 := by rw [hb, zero_mul]

/-- **Injectivity of the root Fox vector in the terminal case.**  If `u = FreeGroup.of a` is a
single generator then the `a`-component of the root Fox vector is `1`, so multiplication by the root
vector is injective. -/
theorem ann_rootVec_letter (α : Type*) [DecidableEq α] (a : α) (l : ℕ) :
    ∀ b : MonoidAlgebra K (OneRelatorGroup ((FreeGroup.of a) ^ l)),
      b • rootVec K ((FreeGroup.of a) ^ l) (FreeGroup.of a) = 0 → b = 0 := by
  intro b hb
  have h1 := congrArg (fun v : α →₀ MonoidAlgebra K (OneRelatorGroup ((FreeGroup.of a) ^ l)) =>
    v a) hb
  rw [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul, rootVec_apply,
    Work.ORLyndon.foxD_of, if_pos rfl, map_one, mul_one] at h1
  exact h1

/-- **The base case of the induction (terminal relators), `sorryAx`-free.**  For `u` a single
generator, the requested statement holds for every `l ≥ 1`. -/
theorem lyndonIndependence_of_letterPow' {α : Type*} [DecidableEq α] {K : Type*} [Field K]
    (a : α) (l : ℕ) (hpos : 1 ≤ l) (hord : orderOf (presentRho ((FreeGroup.of a) ^ l)
      (FreeGroup.of a)) = l) :
    LyndonIndependence K ((FreeGroup.of a) ^ l) (FreeGroup.of a) :=
  lyndon_independence_of_rootVec_inj ((FreeGroup.of a) ^ l) (FreeGroup.of a) l hpos rfl hord
    (ann_rootVec_letter α a l)

/-! ## The `σ_t`-level grading: vocabulary for the Magnus step of the induction

Suppose the exponent sum `σ_t` in a letter `t` vanishes on the root `u`, so that it vanishes on the
relator `r = u ^ l` as well.  Then `σ_t` descends to the one-relator group `G = ⟨α | r⟩`, giving a
surjection `levelOf : G →* Multiplicative ℤ` whose kernel is the Magnus base `B = ker (levelOf)`;
because `levelOf` sends the class of `t` to `1`, the extension splits and `G = B ⋊ ⟨t̄⟩`, so that
`K[G] = ⊕_{k ∈ ℤ} K[B] · t̄ ^ k` is a twisted Laurent polynomial ring over `K[B]` graded by the
level.

The leading-term argument of the Magnus step compares the *top level* of the two sides of an
equation `b · (∂u/∂x) = 0`: the multiplication is compatible with the level in the sense that the
level of a product of monomials is the sum of the levels, so the top level part of a product is the
product of the top level parts.  The vocabulary for that is `levelOf` and `levelPart` below. -/

section Level

variable {α : Type*} [DecidableEq α]

/-- `σ_t` is the `FreeGroup.lift` of its values on the generators. -/
theorem lift_sigma_eq (t : α) :
    FreeGroup.lift (fun s : α => Work.OROneRel.sigma t (FreeGroup.of s)) =
      Work.OROneRel.sigma t := by
  refine MonoidHom.ext fun w => ?_
  exact (FreeGroup.lift_unique (g := Work.OROneRel.sigma t)
    (f := fun s : α => Work.OROneRel.sigma t (FreeGroup.of s)) (fun _ => rfl)
      (x := w)).symm

/-- **The level map of the `σ_t`-decomposition.**  If the exponent sum `σ_t` vanishes on the root
`u` (so that it vanishes on the relator `r = u ^ l`), it descends to the one-relator group
`G = ⟨α | r⟩`.  This is the homomorphism whose kernel is the Magnus base of the decomposition
`G = ker(σ_t) ⋊ ⟨t̄⟩`. -/
noncomputable def levelOf (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) : OneRelatorGroup r →* Multiplicative ℤ :=
  PresentedGroup.toGroup (rels := ({r} : Set (FreeGroup α)))
    (f := fun s : α => Work.OROneRel.sigma t (FreeGroup.of s))
    (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [lift_sigma_eq t, hpow, map_pow, hσ, one_pow])

@[simp] theorem levelOf_of (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (s : α) :
    levelOf t r u l hpow hσ (PresentedGroup.of s) = Work.OROneRel.sigma t (FreeGroup.of s) :=
  PresentedGroup.toGroup.of _

/-- The level of the class of a word of the free group is its `t`-exponent sum. -/
theorem levelOf_presentRho (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (w : FreeGroup α) :
    levelOf t r u l hpow hσ (presentRho r w) = Work.OROneRel.sigma t w := by
  have h : levelOf t r u l hpow hσ (presentRho r w) =
      FreeGroup.lift (fun s : α => Work.OROneRel.sigma t (FreeGroup.of s)) w := rfl
  rw [h, lift_sigma_eq t]

variable {K : Type*} [Field K]

/-- **The `k`-th level part** of an element of the group algebra of `G = ⟨α | r⟩`: the sum of the
terms whose group element has level exactly `k`. -/
noncomputable def levelPart (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ)
    (a : MonoidAlgebra K (OneRelatorGroup r)) : MonoidAlgebra K (OneRelatorGroup r) :=
  ⟨Finsupp.filter (fun g => levelOf t r u l hpow hσ g = Multiplicative.ofAdd k) a.coeff⟩

/-- Evaluation of the `k`-th level part: it keeps exactly the terms whose group element has level
`k`. -/
theorem levelPart_coeff (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ) (a : MonoidAlgebra K (OneRelatorGroup r))
    (g : OneRelatorGroup r) :
    (levelPart t r u l hpow hσ k a).coeff g =
      if levelOf t r u l hpow hσ g = Multiplicative.ofAdd k then a.coeff g else 0 := rfl

/-- Terms of level different from `k` do not contribute to the `k`-th level part. -/
theorem levelPart_coeff_eq_zero (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ) (a : MonoidAlgebra K (OneRelatorGroup r))
    {g : OneRelatorGroup r} (h : levelOf t r u l hpow hσ g ≠ Multiplicative.ofAdd k) :
    (levelPart t r u l hpow hσ k a).coeff g = 0 := by
  rw [levelPart_coeff]
  exact if_neg h

/-- Every group element in the support of the `k`-th level part has level exactly `k`. -/
theorem levelPart_mem_support (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ) (a : MonoidAlgebra K (OneRelatorGroup r))
    {g : OneRelatorGroup r} (hg : g ∈ (levelPart t r u l hpow hσ k a).coeff.support) :
    levelOf t r u l hpow hσ g = Multiplicative.ofAdd k := by
  by_contra h
  exact Finsupp.mem_support_iff.mp hg (levelPart_coeff_eq_zero t r u l hpow hσ k a h)

/-- The level parts are additive. -/
theorem levelPart_add (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ) (a b : MonoidAlgebra K (OneRelatorGroup r)) :
    levelPart t r u l hpow hσ k (a + b) =
      levelPart t r u l hpow hσ k a + levelPart t r u l hpow hσ k b := by
  have h := Finsupp.filter_add (p := fun g : OneRelatorGroup r =>
      levelOf t r u l hpow hσ g = Multiplicative.ofAdd k) (v := a.coeff) (v' := b.coeff)
  exact congrArg (fun z : (OneRelatorGroup r →₀ K) =>
    (⟨z⟩ : MonoidAlgebra K (OneRelatorGroup r))) h

/-- The `k`-th level part of `0` vanishes. -/
theorem levelPart_zero (t : α) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hσ : Work.OROneRel.sigma t u = 1) (k : ℤ) :
    levelPart t r u l hpow hσ k (0 : MonoidAlgebra K (OneRelatorGroup r)) = 0 := by
  have h := Finsupp.filter_zero (p := fun g : OneRelatorGroup r =>
      levelOf t r u l hpow hσ g = Multiplicative.ofAdd k) (M := K)
  exact congrArg (fun z : (OneRelatorGroup r →₀ K) =>
    (⟨z⟩ : MonoidAlgebra K (OneRelatorGroup r))) h

end Level

end Work.ORLyndon
