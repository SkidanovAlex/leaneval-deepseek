import Mathlib
import Submission.Work.ORLyndon.annChain
import Submission.Work.ORLyndon.annAtDefs
import Submission.Work.ORLyndon.annAt_of_epsZero_strong
import Submission.Work.ORLyndon.occDefs
import Submission.Work.ORLyndon.mul_one_sub_of_infinite_order
import Submission.Work.ORLyndon.annAtOfSubgroup
import Submission.Work.ORLyndon.annAt_of_support_le_magnusSubgroup
import Submission.Work.ORLyndon.relatorLetters_pow_clean
import Submission.Work.ORLyndon.nielsenTransfer
import Submission.Work.ORLyndon.annAt_of_jacobian_zero
import Submission.Work.ORLyndon.annAt_of_geometric
import Submission.Work.ORLyndon.rootVec_geom_factorisation
import Submission.Work.ORLyndon.clean_lift_bijective
import Submission.Work.ORLyndon.homogeneous_annihilator
import Submission.Work.ORLyndon.shear_lift_bijective
import Submission.Work.ORLyndon.lsig_sum_wordEps
import Submission.Work.ORLyndon.exists_killing_weight_occTerm_max
import Submission.Work.ORLyndon.exists_int_weight_dominated
import Submission.Work.ORLyndon.twoOccBase
import Submission.Work.ORLyndon.orderOf_presentRho_twoOcc
import Submission.Work.ORLyndon.rootVec_eq_of_twoOcc
import Submission.Work.ORLyndon.exists_twoOcc_decomp
import Submission.Work.ORLyndon.exposedVertex_separating_weight
import Submission.Work.ORLyndon.annAt_letterPow_mul_letterPow
import Submission.Work.ORLyndon.rootVec_occurrences
import Submission.Work.ORLyndon.signedSum_regular
import Submission.Work.ORLyndon.signedSum_regular_of_subgroup
import Submission.Work.ORLyndon.geomSum_regular
import Submission.Work.ORLyndon.isUnit_rootVec_of_letterOnce
import Submission.Work.ORLyndon.lyndonIndependence_eps_zero
import Submission.Work.ORLyndon.orderOf_presentRho_eps_ne_zero
import Submission.Work.ORLyndon.exists_mul_normElem_of_mul_of_eq
import Submission.Work.OROneRel.le_relatorNorm_pow
import Submission.Work.OROneRel.isCyclicallyReducedRelator_of_terminal
import Submission.Work.OROneRel.letterPow
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.letters_closure_iff
import Submission.Work.ORLyndon.isCyclicallyReducedRelator_rootW
import Submission.Work.ORLyndon.transvectionLeftProps
import Submission.Work.ORLyndon.nonTLetters_transvectionLeft_le_clean
import Submission.Work.ORLyndon.twoSidedShear
import Submission.Work.ORLyndon.shearProps
import Submission.Work.ORLyndon.nonTLetters_shear_le
import Submission.Work.ORLyndon.lyndonIdentity_of_pow
-- NOTE (session 6): the modules `Submission.Work.OROneRel.mmStepData_of_expsum_zero`,
-- `magnus_step_root` and `MagnusGenDefs` are *not* needed here and are deliberately not imported:
-- `magnus_step_root` declares `Work.OROneRel.mk_flatten_replicate`, which `weinbaum_at`'s dependency
-- `exists_common_power` declares as well, so the two cones cannot be imported into one module.  See
-- the "import clash" section of `NOTES_epsNeZeroDescent_level.md`.

/-!
# The residual `EpsNeZeroDescent`: reduction and provable fragments

`Work.ORLyndon.EpsNeZeroDescent K` (`annChain.lean`) is the Case-2 half of the Cohen--Lyndon descent
of this directory: `u` is cyclically reduced, is not a proper power, has `2 ≤ relatorNorm u`, **no**
letter of vanishing exponent sum, and the statement asks, for every nonempty `S ⊆ relatorLetters u`,
for a `MagnusDescent K u l S` together with `orderOf (presentRho (u ^ l) u) = l`.

## Proved here (sorry-free)

* `annAt_of_letterOnce`: the fragment of the residual in which the root has a letter occurring exactly
  once.  There the `x`-component of the root Fox vector is a **unit**
  (`Work.ORLyndon.isUnit_rootVec_of_letterOnce`), so `annAt K (u ^ l) u (relatorLetters u)` holds by
  `Work.ORLyndon.annAt_of_unit`, and hence -- by monotonicity -- at every nonempty set of letters.
* the **leading-level transfer** for an *arbitrary* level homomorphism `φ : G →* Multiplicative ℤ`,
  independent of the one-relator setting: `levelPartOf` (the `k`-th level part),
  `levelPartOf_mul_top` (the top level part of a product is the product of the top level parts),
  `exists_levelPartOf_max_ne_zero` (a non-zero element has a non-zero top level part), and

  `Work.ORLyndon.regular_of_topPart_isUnit`:

  > if every level occurring in the support of `a : K[G]` is `≤ M` and the `M`-th level part of `a`
  > is a **unit**, then `b * a = 0` forces `b = 0`.

  This is a *new* (and much more elementary) sufficient condition for the componentwise regularity
  `Work.ORLyndon.annAt K (u ^ l) u {x}` of the root Fox vector: no Magnus rewriting, no HNN step, no
  Freiheitssatz and no base group enters.  It applies whenever some weight `c : α → ℤ` with
  `cohom c u = 1` makes the terms of `∂u / ∂x` separate at their top `cohom c`-level; see the
  discussion below.

## The reduction of the existential half of the residual

`MagnusDescent K u l S` is *not* about finding a short root.  The **terminal witness**
`v := FreeGroup.of x₀` for any `x₀ ∈ S` already qualifies: `relatorNorm v = 1 < 2 ≤ relatorNorm u`,
`v` is not a proper power, cyclically reduced, and `S' := {x₀} ⊆ relatorLetters v` is nonempty.  Its
base antecedent `annAt K (v ^ l) v {x₀}` is *provable* (the Fox component of a single letter is `1`,
a unit), so `MagnusDescent K u l S` **follows from** `annAt K (u ^ l) u S`; and since `annAt` is
monotone in the letter set, the existential half of the residual is discharged as soon as
`annAt K (u ^ l) u (relatorLetters u)` is known for every Case-2 root `u`:

  `(∀ u l, [hypotheses of EpsNeZeroDescent] → annAt K (u ^ l) u (relatorLetters u))`
    ⟹  the `MagnusDescent` half of `EpsNeZeroDescent`.

Conversely, applying the descent datum of *any* witness `(β, v, r', S')` whose antecedent is provable
(from the strong induction of `Work.ORLyndon.descent_bundle`) yields `annAt K (u ^ l) u S` as well, so
the existential half of the residual carries *no* content beyond the annihilator statement at the
root.

## The remaining gap (documented, not hidden)

The annihilator statement `annAt K (u ^ l) u (relatorLetters u)` for *balanced* roots -- every letter
occurring at least twice -- is the open input, and is exactly node N2's Case 2.  The routes that are
*dead* are recorded with their reasons:

* the `σ_t = 0` transfer `Work.ORLyndon.annAt_of_epsZero_strong` needs a letter of vanishing exponent
  sum, which such a root does not have;
* the Nielsen/divisibility route into `Work.OROneRel.magnusStepCase2_of_weight` is blocked by a *cost
  floor* for balanced rank-two roots (`u = a ^ 4 * b ^ 7`: any `ψ ∈ Aut F {a,b}` making one
  coordinate of the exponent vector divisible by the gcd of the others has at least `15` occurrences
  of the *other* letter, while the Magnus rewriting would need at most `10` to be shorter);
* the Masters--Linton `ℤ`-cover/domain step produces the strictly shorter root
  (`Work.OROneRel.coedge_root_norm_lt`, `Work.OROneRel.coedge_root_class`,
  `Work.OROneRel.coedge_injective` are all proved), but the transport of `annAt` from the cover base
  needs the *general-gauge* chain rule and the splitting `B ≅ ⟨β | v ^ l⟩`.

**What the leading-level transfer does give.**  By `regular_of_topPart_isUnit` the statement
`annAt K (u ^ l) u {x}` follows from: there is a weight `c : α → ℤ` with `cohom c u = 1` whose level
`levelOfC` separates the terms of `∂u / ∂x`, with a **single** term at the top level (then the top
level part is a single monomial, hence a unit).  For `u = a ^ p * b ^ q` the weight `c = (q, -p)`
does this for *both* letters, and more generally a weight separates the terms whenever their
exponent vectors are not all congruent modulo `ℚ · eps(u)`; the case in which they *are* (the
"exceptional case") is the residual, e.g. for
`u = a b c a b c b⁻¹c⁻¹ a⁻¹ b c b⁻¹c⁻¹` at the letter `a`.

The order half of the residual is supplied *without* the Karrass--Magnus--Solitar chain by
`Work.ORLyndon.orderOf_presentRho_eps_ne_zero` (a character into `ZMod (l * |d|)`).

**The subgroup route (session 11).**  `Work.ORLyndon.annAt_of_support_subgroup_noZeroDivisors`
(`Submission/Work/ORLyndon/annAtOfSubgroup.lean`) gives a second, strictly stronger route: if the
support of `rootVec K r u x` lies in a subgroup `N ≤ ⟨α | r⟩` with `NoZeroDivisors (K[N])`, and the
component is non-zero, then `annAt K r u {x}`.  The point is that `K[G]` is free over `K[N]`, so
right multiplication by an element of `K[N]` acts componentwise.  The intended input is a *free*
`N` (then `K[N]` is a domain because free groups are orderable) -- e.g. a Magnus subgroup at a letter
`y`, which is free by the Freiheitssatz (`Work.OROneRel.freiheitssatz_at`), for which the support
condition is `(rootVec K r u x).coeff.support ⊆ magnusSubgroup r y`.

**The `l ≥ 2` obstruction (session 11, sharp).**  Do *not* try to reduce `l ≥ 2` to `l = 1` by
pushing `K[⟨α | u ^ l⟩]` forward to `K[⟨α | u⟩]`: the push-forward carries `rootVec` to `rootVec`
(so it shows `Ann(rootVec_{u^l}) ⊆ ker π`) but only `relatorVec_{u^l} ↦ l · relatorVec_u` (so the
`ker θ` form needs `(l : K) ≠ 0`), and both are *strictly weaker* than what is needed: the extra
statement `Ann(rootVec_{u^l}) ∩ ker π = 0` is literally `annAt` at `l`.  See §17.2 of
`NOTES_epsNeZeroDescent_level.md` for the computations and for the equivalent formulations
(`Ann(β) ⊆ Ann_ right(s)`, `annAt ⟺ Ann(β) ∩ Fix = 0`, `Fix = Ann_ right(s)`).

**THE TRANSVECTION ROUTE (session 17) — read `NOTES_epsNeZeroDescent_level.md` §21 first.**  Every
route above tries to *separate* the occurrence terms of `∂u/∂x`, which §8.1/§10.2/§16.4b/§18.4/§20.3
prove impossible in the residual.  The transvection route instead *shortens the root*:

* `annAt_of_jacobian_zero_set` — the set form of the componentwise Nielsen transfer: for a bijective
  `ψ` with Jacobian vanishing off the diagonal at every `x ∈ E`, `annAt K ((ψu)^l) (ψu) E` implies
  `annAt K (u^l) u E`;
* `annAt_of_epsZeroImage` — its composite with the *exponent-sum-zero Magnus step*
  `annAt_of_epsZero_strong`, which is available as soon as `eps t (ψu) = 0`;
* `magnusDescent_of_epsZeroImage` — the resulting `MagnusDescent`, whose witness root
  `rootW t (ψu) l` is shorter than `u` whenever the number of non-`t` letters of `ψu` is below
  `relatorNorm u` (`Work.OROneRel.relatorNorm_rootW_le_nonTLetters`).

The natural choice is a **single elementary transvection** `ψ = Work.ORLyndon.transvectionLeft t y m`
(`y ↦ t^(-m) * y`, a leaf definition in `transvectionLeft.lean`; `transvectionLeftProps` supplies
bijectivity, cleanliness off `t`, and `eps t (ψ w) = eps t w - m * eps y w`).  With
`m := eps t u / eps y u`, the image has `eps t (ψu) = 0` — so the route applies whenever
`eps y u ∣ eps t u` for letters `y ≠ t` of `u`, i.e. exactly the divisibility condition of node N2's
weighted Magnus step.  The census (§21.3) shows that in the residual this **always** works: for all
336 residual instances of length ≤ 8 over ≤ 3 letters there are `t, y` making `ψu` cyclically
reduced, keeping `t` as a letter, and with `nonTLetters t (ψu) < relatorNorm u`.  The single
remaining obligation is thus the purely combinatorial statement `residualTransvectionData` of §21.4 —
**no characters, polytopes, Fox chain rules or division rings are involved**. -/

set_option autoImplicit false
set_option linter.unusedVariables false

universe u v

namespace Work.ORLyndon

open MonoidAlgebra

variable {α : Type u} [DecidableEq α] {K : Type v} [Field K]

/-! ## The leading-level transfer for an arbitrary level homomorphism

Everything in this section is stated for an *arbitrary* group `G` and an arbitrary homomorphism
`φ : G →* Multiplicative ℤ` ("the level"), and is independent of the one-relator setting.  Let
`a, b : K[G]` and suppose that every group element occurring in `a` has level `≤ M` and every one
occurring in `b` has level `≤ N`.  Since `φ` is a homomorphism, the terms of `a * b` of level exactly
`N + M` are exactly the products of a level-`N` term of `a` and a level-`M` term of `b`:

`levelPartOf φ N a * levelPartOf φ M b = levelPartOf φ (N+M) (a * b)`   (`levelPartOf_mul_top`).

Consequently, if the **top level part** of `a` is a *unit* of `K[G]`, then `a` is a right
non-zero-divisor: for `b ≠ 0` with `b * a = 0` the top level part `levelPartOf φ N b` of `b` (`N` the
maximum level in its support) is non-zero, while its product with the top level part of `a` is the
top level part of `b * a = 0`, hence vanishes -- contradicting the unit-ness
(`regular_of_topPart_isUnit`). -/

section LevelGeneral

variable {G : Type u} [Group G]

/-- The `k`-th level part of an element of `K[G]`, for an arbitrary level homomorphism
`φ : G →* Multiplicative ℤ`: the sum of the terms whose group element has level exactly `k`. -/
noncomputable def levelPartOf (φ : G →* Multiplicative ℤ) (k : ℤ) (a : MonoidAlgebra K G) :
    MonoidAlgebra K G :=
  ⟨Finsupp.filter (fun g => φ g = Multiplicative.ofAdd k) a.coeff⟩

theorem levelPartOf_coeff (φ : G →* Multiplicative ℤ) (k : ℤ) (a : MonoidAlgebra K G) (g : G) :
    (levelPartOf φ k a).coeff g =
      if φ g = Multiplicative.ofAdd k then a.coeff g else 0 := rfl

theorem levelPartOf_coeff_eq_zero (φ : G →* Multiplicative ℤ) (k : ℤ) (a : MonoidAlgebra K G)
    {g : G} (h : φ g ≠ Multiplicative.ofAdd k) : (levelPartOf φ k a).coeff g = 0 := by
  rw [levelPartOf_coeff]; exact if_neg h

theorem levelPartOf_mem_support {φ : G →* Multiplicative ℤ} {k : ℤ} {a : MonoidAlgebra K G}
    {g : G} (hg : g ∈ (levelPartOf φ k a).coeff.support) : φ g = Multiplicative.ofAdd k := by
  by_contra h
  exact Finsupp.mem_support_iff.mp hg (levelPartOf_coeff_eq_zero φ k a h)

theorem levelPartOf_zero (φ : G →* Multiplicative ℤ) (k : ℤ) :
    levelPartOf φ k (0 : MonoidAlgebra K G) = 0 :=
  congrArg (fun z : G →₀ K => (⟨z⟩ : MonoidAlgebra K G))
    (Finsupp.filter_zero (p := fun g => φ g = Multiplicative.ofAdd k) (M := K))

/-- The definition of `levelPartOf` in the `ofCoeff` vocabulary, in which the product formula is
proved. -/
private theorem levelPartOf_eq_ofCoeff (φ : G →* Multiplicative ℤ) (k : ℤ)
    (a : MonoidAlgebra K G) :
    levelPartOf φ k a = MonoidAlgebra.ofCoeff
      (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd k) a.coeff) := rfl

/-- **The top level part of a product.**  If every group element in the support of `a` has level
`≤ N` and every one in the support of `b` has level `≤ M`, then the `N`-th level part of `a` times
the `M`-th level part of `b` is the `(N + M)`-th level part of `a * b`. -/
theorem levelPartOf_mul_top (φ : G →* Multiplicative ℤ) {N M : ℤ} {a b : MonoidAlgebra K G}
    (ha : ∀ g ∈ a.coeff.support, (φ g).toAdd ≤ N)
    (hb : ∀ g ∈ b.coeff.support, (φ g).toAdd ≤ M) :
    levelPartOf φ N a * levelPartOf φ M b = levelPartOf φ (N + M) (a * b) := by
  classical
  rw [levelPartOf_eq_ofCoeff, levelPartOf_eq_ofCoeff, levelPartOf_eq_ofCoeff]
  set Ac : G →₀ K := Finsupp.filter (fun g => φ g = Multiplicative.ofAdd N) a.coeff with hAcdef
  set Bc : G →₀ K := Finsupp.filter (fun g => φ g = Multiplicative.ofAdd M) b.coeff with hBcdef
  have hAc : ∀ h, Ac h = if φ h = Multiplicative.ofAdd N then a.coeff h else 0 := by
    intro h; rw [hAcdef, Finsupp.filter_apply]
  have hBc : ∀ h, Bc h = if φ h = Multiplicative.ofAdd M then b.coeff h else 0 := by
    intro h; rw [hBcdef, Finsupp.filter_apply]
  have hsupp : Ac.support ⊆ a.coeff.support := by
    intro h hh
    have hne : Ac h ≠ 0 := Finsupp.mem_support_iff.mp hh
    rw [hAc] at hne
    by_cases hp : φ h = Multiplicative.ofAdd N
    · exact Finsupp.mem_support_iff.mpr (by rwa [if_pos hp] at hne)
    · rw [if_neg hp] at hne; exact absurd rfl hne
  have hlev : ∀ h ∈ Ac.support, φ h = Multiplicative.ofAdd N := by
    intro h hh
    have hne : Ac h ≠ 0 := Finsupp.mem_support_iff.mp hh
    rw [hAc] at hne
    by_cases hp : φ h = Multiplicative.ofAdd N
    · exact hp
    · rw [if_neg hp] at hne; exact absurd rfl hne
  refine MonoidAlgebra.ext (Finsupp.ext (fun g₀ => ?_))
  have hLsum : (MonoidAlgebra.ofCoeff Ac * MonoidAlgebra.ofCoeff Bc).coeff g₀
      = ∑ h ∈ Ac.support, Ac h * Bc (h⁻¹ * g₀) := by
    rw [MonoidAlgebra.coeff_mul_apply_left, MonoidAlgebra.coeff_ofCoeff,
      MonoidAlgebra.coeff_ofCoeff]
    exact Finsupp.sum_of_support_subset Ac (le_refl _) _ (fun i _ => by simp)
  have hRsum : (a * b).coeff g₀ = ∑ h ∈ a.coeff.support, a.coeff h * b.coeff (h⁻¹ * g₀) := by
    rw [MonoidAlgebra.coeff_mul_apply_left]
    exact Finsupp.sum_of_support_subset a.coeff (le_refl _) _ (fun i _ => by simp)
  show (MonoidAlgebra.ofCoeff Ac * MonoidAlgebra.ofCoeff Bc).coeff g₀ =
    (Finsupp.filter (fun g => φ g = Multiplicative.ofAdd (N + M)) (a * b).coeff) g₀
  rw [Finsupp.filter_apply, hLsum, hRsum]
  by_cases hp : φ g₀ = Multiplicative.ofAdd (N + M)
  · rw [if_pos hp]
    have hpadd : (φ g₀).toAdd = N + M := by rw [hp, toAdd_ofAdd]
    have key : ∀ h ∈ Ac.support,
        Ac h * Bc (h⁻¹ * g₀) = a.coeff h * b.coeff (h⁻¹ * g₀) := by
      intro h hh
      have hφh : φ h = Multiplicative.ofAdd N := hlev h hh
      have h1 : Ac h = a.coeff h := by rw [hAc, if_pos hφh]
      have hφz : φ (h⁻¹ * g₀) = Multiplicative.ofAdd M := by
        rw [map_mul, map_inv, hφh, hp, ← ofAdd_neg, ← ofAdd_add,
          show -N + (N + M) = M from by ring]
      have h2 : Bc (h⁻¹ * g₀) = b.coeff (h⁻¹ * g₀) := by rw [hBc, if_pos hφz]
      rw [h1, h2]
    have zero : ∀ x ∈ a.coeff.support, x ∉ Ac.support →
        a.coeff x * b.coeff (x⁻¹ * g₀) = 0 := by
      intro x hx hxAc
      have hxa : a.coeff x ≠ 0 := Finsupp.mem_support_iff.mp hx
      have hle : (φ x).toAdd ≤ N := ha x hx
      have hneN : (φ x).toAdd ≠ N := by
        intro hc
        apply hxAc
        refine Finsupp.mem_support_iff.mpr ?_
        rw [hAc, if_pos (by rw [← ofAdd_toAdd (φ x), hc])]
        exact hxa
      have hlt : (φ x).toAdd < N := lt_of_le_of_ne hle hneN
      have hb0 : b.coeff (x⁻¹ * g₀) = 0 := by
        by_contra hne
        have hmem : x⁻¹ * g₀ ∈ b.coeff.support := Finsupp.mem_support_iff.mpr hne
        have hb' := hb _ hmem
        have hz : (φ (x⁻¹ * g₀)).toAdd = -(φ x).toAdd + (φ g₀).toAdd := by
          rw [map_mul, map_inv, toAdd_mul, toAdd_inv]
        rw [hz, hpadd] at hb'
        linarith
      rw [hb0, mul_zero]
    rw [Finset.sum_congr rfl key, Finset.sum_subset hsupp zero]
  · rw [if_neg hp]
    refine Finset.sum_eq_zero (fun h hh => ?_)
    have hφh : φ h = Multiplicative.ofAdd N := hlev h hh
    have hz : Bc (h⁻¹ * g₀) = 0 := by
      by_contra hne
      have h1 : φ (h⁻¹ * g₀) = Multiplicative.ofAdd M := by
        by_contra hc
        rw [hBc, if_neg hc] at hne
        exact hne rfl
      refine hp ?_
      calc φ g₀ = φ (h * (h⁻¹ * g₀)) := by rw [mul_inv_cancel_left]
        _ = φ h * φ (h⁻¹ * g₀) := map_mul _ _ _
        _ = Multiplicative.ofAdd N * Multiplicative.ofAdd M := by rw [hφh, h1]
        _ = Multiplicative.ofAdd (N + M) := (ofAdd_add N M).symm
    rw [hz, mul_zero]

/-- **A non-zero element has a non-zero top level part.**  If `b ≠ 0`, the levels occurring in its
support have a maximum `N`, every level of its support is `≤ N`, and the `N`-th level part of `b` is
non-zero. -/
theorem exists_levelPartOf_max_ne_zero (φ : G →* Multiplicative ℤ) {b : MonoidAlgebra K G}
    (hb : b ≠ 0) :
    ∃ N : ℤ, levelPartOf φ N b ≠ 0 ∧
      ∀ g ∈ b.coeff.support, (φ g).toAdd ≤ N := by
  classical
  have hne : b.coeff.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hb (MonoidAlgebra.ext (by rw [Finsupp.support_eq_empty.mp h, MonoidAlgebra.coeff_zero]))
  obtain ⟨g₀, hg₀, hmax⟩ := Finset.exists_max_image b.coeff.support
    (fun g => (φ g).toAdd) hne
  refine ⟨(φ g₀).toAdd, ?_, fun g hg => hmax g hg⟩
  intro hzero
  have hcoeff : b.coeff g₀ = 0 := by
    have h1 := levelPartOf_coeff (K := K) φ ((φ g₀).toAdd) b g₀
    rw [hzero] at h1
    simpa [ofAdd_toAdd] using h1.symm
  exact (Finsupp.mem_support_iff.mp hg₀) hcoeff

/-- **The leading-level transfer.**  Let `a : K[G]` have all its levels `≤ M` and suppose that the
`M`-th level part of `a` is a **right non-zero-divisor**.  Then `a` itself is a right
non-zero-divisor: `b * a = 0` forces `b = 0`.

Proof: let `N` be the maximum level occurring in `b ≠ 0`.  By `levelPartOf_mul_top` the `N`-th level
part of `b` times the `M`-th level part of `a` is the `(N + M)`-th level part of `b * a = 0`, hence
vanishes; the regularity of the top level part of `a` then forces the `N`-th level part of `b` to
vanish, contradicting `exists_levelPartOf_max_ne_zero`. -/
theorem regular_of_topPart_regular (φ : G →* Multiplicative ℤ) {M : ℤ} {a : MonoidAlgebra K G}
    (ha : ∀ g ∈ a.coeff.support, (φ g).toAdd ≤ M)
    (hreg : ∀ x : MonoidAlgebra K G, x * levelPartOf φ M a = 0 → x = 0) :
    ∀ b : MonoidAlgebra K G, b * a = 0 → b = 0 := by
  classical
  intro b hb
  by_contra hb0
  obtain ⟨N, hNne, hNmax⟩ := exists_levelPartOf_max_ne_zero (K := K) φ hb0
  have htop := levelPartOf_mul_top (K := K) φ hNmax ha
  rw [hb, levelPartOf_zero] at htop
  exact hNne (hreg _ htop)

/-- **The leading-level transfer, unit form.**  Let `a : K[G]` have all its levels `≤ M` and a
**unit** as its `M`-th level part.  Then `a` is a right non-zero-divisor. -/
theorem regular_of_topPart_isUnit (φ : G →* Multiplicative ℤ) {M : ℤ} {a : MonoidAlgebra K G}
    (ha : ∀ g ∈ a.coeff.support, (φ g).toAdd ≤ M)
    (hunit : IsUnit (levelPartOf φ M a)) :
    ∀ b : MonoidAlgebra K G, b * a = 0 → b = 0 :=
  regular_of_topPart_regular φ ha (annAt_regular_of_unit hunit)

/-- **The leading-level transfer, single-monomial form.**  If the `M`-th level part of `a : K[G]` is a
non-zero scalar multiple of a *single* group element, then -- all levels of `a` being `≤ M` -- `a` is
a right non-zero-divisor.  This is the form in which the transfer is applied to the root Fox vector:
the top level part of `(∂u / ∂x)_x` is a single monomial exactly when the level homomorphism
separates the Fox terms with a unique maximum. -/
theorem regular_of_topPart_eq_smul (φ : G →* Multiplicative ℤ) {M : ℤ} {a : MonoidAlgebra K G}
    {g : G} {c : K} (hc : c ≠ 0)
    (ha : ∀ h ∈ a.coeff.support, (φ h).toAdd ≤ M)
    (htop : levelPartOf φ M a = c • MonoidAlgebra.of K G g) :
    ∀ b : MonoidAlgebra K G, b * a = 0 → b = 0 := by
  refine regular_of_topPart_regular φ ha fun x hx => ?_
  rw [htop] at hx
  have h1 : c • (x * MonoidAlgebra.of K G g) = 0 := by
    rw [← hx, Algebra.mul_smul_comm]
  rcases (smul_eq_zero.mp h1) with hc0 | hxg
  · exact absurd hc0 hc
  · calc x = x * MonoidAlgebra.of K G g * MonoidAlgebra.of K G g⁻¹ := by
          rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = 0 := by rw [hxg, zero_mul]

end LevelGeneral

/-- **The residual of the level method in its sharpest form.**  For *any* level homomorphism
`φ : ⟨α | r⟩ →* Multiplicative ℤ` and any bound `M` on the levels of the support of the root
component `rootVec K r u x`, the component is a right non-zero-divisor as soon as its `M`-th **level
part** is one:

`annAt K r u {x}`.

This is the exact shape of the residual of the whole level route
(`NOTES_epsNeZeroDescent_level.md` §13): the level part in question is the sum of the occurrence
terms of `∂u/∂x` that lie in the top congruence class modulo `ℚ · eps u` (for a generic weight), and
the statement to prove in the residual cases is precisely its regularity.  All the earlier
`annAt`-criteria of this file are special cases: `annAt_of_occTerm_lsig_max` is the case in which
that level part is a single monomial. -/
theorem annAt_of_topPart_regular {r u : FreeGroup α} {x : α}
    (φ : OneRelatorGroup r →* Multiplicative ℤ) (M : ℤ)
    (hle : ∀ g ∈ (rootVec K r u x).coeff.support, Multiplicative.toAdd (φ g) ≤ M)
    (hreg : ∀ b : MonoidAlgebra K (OneRelatorGroup r),
      b * levelPartOf φ M (rootVec K r u x) = 0 → b = 0) :
    annAt K r u {x} :=
  fun b hb => regular_of_topPart_regular (K := K) φ hle hreg b (hb x (Set.mem_singleton x))

/-- **The residual in the case in which some letter occurs exactly once.**  If `x ∈ relatorLetters u`
occurs exactly once (one occurrence of `(x, b)` and none of `(x, !b)`), then the `x`-component of the
root Fox vector is a unit, so `annAt` holds at the full letter set of the root. -/
theorem annAt_of_letterOnce {r u : FreeGroup α} {x : α} (hx : x ∈ Work.OROneRel.relatorLetters u)
    (b : Bool) (h1 : (FreeGroup.toWord u).count (x, b) = 1)
    (h0 : (FreeGroup.toWord u).count (x, !b) = 0) :
    annAt K r u (Work.OROneRel.relatorLetters u) :=
  annAt_of_unit hx (isUnit_rootVec_of_letterOnce r u x b ⟨h1, h0⟩)

/-- `cohom c` is the `FreeGroup.lift` of its values on the generators. -/
theorem lift_cohom (c : α → ℤ) :
    FreeGroup.lift (fun s : α => Work.OROneRel.cohom c (FreeGroup.of s)) =
      Work.OROneRel.cohom c := by
  refine MonoidHom.ext fun w => ?_
  exact (FreeGroup.lift_unique (g := Work.OROneRel.cohom c)
    (f := fun s : α => Work.OROneRel.cohom c (FreeGroup.of s)) (fun _ => rfl) (x := w)).symm

/-- **The general-weight level homomorphism.**  For a weight `c : α → ℤ` killing the root `u`
(i.e. `cohom c u = 1`, so that `cohom c (u ^ l) = 1` as well), the weights descend to the one-relator
group `⟨α | u ^ l⟩`.  Its level parts are the `levelPartOf`-decomposition of the leading-level
transfer above. -/
noncomputable def levelOfC (c : α → ℤ) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hc : Work.OROneRel.cohom c u = 1) : OneRelatorGroup r →* Multiplicative ℤ :=
  PresentedGroup.toGroup (rels := ({r} : Set (FreeGroup α)))
    (f := fun s : α => Work.OROneRel.cohom c (FreeGroup.of s))
    (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      rw [lift_cohom c, hpow, map_pow, hc, one_pow])

/-- The level of the class of a word is its `c`-weight. -/
theorem levelOfC_presentRho (c : α → ℤ) (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hc : Work.OROneRel.cohom c u = 1) (w : FreeGroup α) :
    levelOfC c r u l hpow hc (presentRho r w) = Work.OROneRel.cohom c w := by
  have h : levelOfC c r u l hpow hc (presentRho r w) =
      FreeGroup.lift (fun s : α => Work.OROneRel.cohom c (FreeGroup.of s)) w := rfl
  rw [h, lift_cohom c]

/-! ## The application: `annAt` from a monomial top level part -/

/-- **`annAt` from a single-monomial top level part of the root Fox vector.**  Let `c : α → ℤ` be a
weight with `cohom c u = 1`, so that the level homomorphism
`levelOfC c (u ^ l) u l rfl hc : ⟨α | u ^ l⟩ →* Multiplicative ℤ` is defined.  If every group
element occurring in `rootVec K (u ^ l) u x` has level `≤ M` and the `M`-th level part of
`rootVec K (u ^ l) u x` is a non-zero scalar multiple of a single group element, then the
`x`-component of the root Fox vector is a right non-zero-divisor, i.e. `annAt K (u ^ l) u {x}`. -/
theorem annAt_of_levelTop_single {c : α → ℤ} {u : FreeGroup α} {l : ℕ}
    (hc : Work.OROneRel.cohom c u = 1) {x : α} {M : ℤ} {c₀ : K}
    {g : OneRelatorGroup (u ^ l)} (hc₀ : c₀ ≠ 0)
    (hbound : ∀ h ∈ (rootVec K (u ^ l) u x).coeff.support,
      (levelOfC c (u ^ l) u l rfl hc h).toAdd ≤ M)
    (htop : levelPartOf (levelOfC c (u ^ l) u l rfl hc) M (rootVec K (u ^ l) u x) =
      c₀ • MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g) :
    annAt K (u ^ l) u {x} := by
  intro b hb
  exact regular_of_topPart_eq_smul (levelOfC c (u ^ l) u l rfl hc) hc₀ hbound htop b
    (hb x (by simp))

/-! ## The regularity toolkit

The three operations on right non-zero-divisors which the level method and the factorisation
arguments of the residual need: products, multiplication by units, and the two elementary
"geometric" facts `1 - h` (regular when `h` has infinite order) and `1 + h`. -/

section Toolkit

variable {R : Type*}

/-- A product of right non-zero-divisors is a right non-zero-divisor. -/
theorem regular_mul [SemigroupWithZero R] {a b : R}
    (ha : ∀ c : R, c * a = 0 → c = 0) (hb : ∀ c : R, c * b = 0 → c = 0) :
    ∀ c : R, c * (a * b) = 0 → c = 0 := by
  intro c h
  exact ha c (hb (c * a) (by rw [mul_assoc]; exact h))

/-- A unit is a right non-zero-divisor, so a unit times a right non-zero-divisor is a right
non-zero-divisor. -/
theorem regular_of_unit_mul [Ring R] {u a : R} (hu : IsUnit u)
    (ha : ∀ c : R, c * a = 0 → c = 0) : ∀ c : R, c * (u * a) = 0 → c = 0 := by
  intro c h
  exact annAt_regular_of_unit hu c (ha (c * u) (by rw [mul_assoc]; exact h))

end Toolkit

section LevelMethod

variable {G : Type*} [Group G]

/-- **The level method for a component of the root Fox vector.**  If the `x`-component of the root
Fox vector is presented as a finite sum of group elements whose levels under a level homomorphism
`φ : ⟨α | r⟩ →* Multiplicative ℤ` have a *unique* maximum, then that component is a right
non-zero-divisor, i.e. `annAt K r u {x}`.

This is the form in which the leading-level transfer is applied: the sum is the enumeration of the
occurrences of `x^{±1}` in the defining word of `u`, and `φ` is the character induced by a weight
killing `u`. -/
theorem annAt_of_sum_uniqueMax {r u : FreeGroup α} {x : α}
    (φ : OneRelatorGroup r →* Multiplicative ℤ) {ι : Type*} (s : Finset ι)
    (g : ι → OneRelatorGroup r) (i₀ : ι) (hi₀ : i₀ ∈ s)
    (hle : ∀ i ∈ s, Multiplicative.toAdd (φ (g i)) ≤ Multiplicative.toAdd (φ (g i₀)))
    (huniq : ∀ i ∈ s, Multiplicative.toAdd (φ (g i)) = Multiplicative.toAdd (φ (g i₀)) → i = i₀)
    (hsum : rootVec K r u x = ∑ i ∈ s, MonoidAlgebra.of K (OneRelatorGroup r) (g i)) :
    annAt K r u {x} := by
  intro b hb
  refine regular_of_sum_of_uniqueMax (K := K) φ s g i₀ hi₀ hle huniq b ?_
  rw [← hsum]
  exact hb x (Set.mem_singleton x)

/-- **`annAt` from a factorisation of the root component into right non-zero-divisors.** -/
theorem annAt_of_factorisation {r u : FreeGroup α} {x : α}
    {A B : MonoidAlgebra K (OneRelatorGroup r)}
    (hA : ∀ c : MonoidAlgebra K (OneRelatorGroup r), c * A = 0 → c = 0)
    (hB : ∀ c : MonoidAlgebra K (OneRelatorGroup r), c * B = 0 → c = 0)
    (hfac : rootVec K r u x = A * B) : annAt K r u {x} :=
  fun b hb => regular_mul hA hB b (by rw [← hfac]; exact hb x (Set.mem_singleton x))

/-- **The Fourier/Fox reading of the level method.**  A single monomial `of g` is a right
non-zero-divisor, so if the `x`-component is *equal* to a single monomial, `annAt` holds. -/
theorem annAt_of_eq_single {r u : FreeGroup α} {x : α} {g : OneRelatorGroup r}
    (h : rootVec K r u x = MonoidAlgebra.of K (OneRelatorGroup r) g) : annAt K r u {x} := by
  intro b hb
  have h2 : b * MonoidAlgebra.of K (OneRelatorGroup r) g = 0 := by
    rw [← h]; exact hb x (Set.mem_singleton x)
  have h3 : (b * MonoidAlgebra.of K (OneRelatorGroup r) g)
      * (MonoidAlgebra.of K (OneRelatorGroup r) g⁻¹) = 0 := by rw [h2, zero_mul]
  rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h3

end LevelMethod

/-! ## The occurrence family of the Fox expansion

For a word `L` and a letter `x`, the Fox derivative `∂L/∂x` is the signed sum of the *occurrence
terms* `occTerm x L i` (the prefix ending just before an occurrence of `x`, respectively just after
an occurrence of `x⁻¹`), with coefficients `occEps x L i ∈ {1, -1}` at the occurrences of `x^{±1}`
and `0` elsewhere (`foxWord_occurrences`, `rootVec_occurrences`).  This is the family to which the
level method (`annAt_of_sum_uniqueMax`, `signedSum_regular`) is applied.

The definitions themselves (`occPref`, `occTerm`, `occSign`, `occEps` and their API) live in the
leaf module `Submission.Work.ORLyndon.occDefs`, which imports nothing of this file. -/

section Occurrences

/-- **The occurrence decomposition of the root Fox vector**: the `x`-component of `(∂u/∂x)_x` pushed
into `K[⟨α | r⟩]` is the signed sum of the occurrence terms of the defining word of `u`. -/
theorem rootVec_eq_sum_occEps {r u : FreeGroup α} (x : α) :
    rootVec K r u x =
      ∑ i : Fin (Work.OROneRel.wordOf u).length,
        occEps K x (Work.OROneRel.wordOf u) i •
          MonoidAlgebra.of K (OneRelatorGroup r)
            (presentRho r (occTerm x (Work.OROneRel.wordOf u) i)) := by
  rw [rootVec_occurrences]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [occEps, occTerm]
  by_cases h1 : (Work.OROneRel.wordOf u).get i = (x, true)
  · simp only [h1, if_true, one_smul, Nat.add_zero]
  · have hne : ((x, false) : α × Bool) ≠ (x, true) := by simp
    by_cases h2 : (Work.OROneRel.wordOf u).get i = (x, false)
    · simp only [h2, if_true, if_false, neg_one_smul, hne]
    · simp only [h1, h2, if_false, zero_smul]

/-- **The level method in occurrence form.**  If the occurrence terms `occTerm x (wordOf u) i` of
the Fox expansion of `∂u/∂x`, with their signs `occEps`, have a *unique* maximum level under a level
homomorphism `φ : ⟨α | r⟩ →* Multiplicative ℤ`, then the `x`-component of the root Fox vector is a
right non-zero-divisor, i.e. `annAt K r u {x}`.

This is the theorem the whole level route rests on: it is char-free, and it applies to every root
whose Fox occurrence terms are separated by a character of `⟨α | r⟩`. -/
theorem annAt_of_occTerm_uniqueMax {r u : FreeGroup α} {x : α}
    (φ : OneRelatorGroup r →* Multiplicative ℤ) (i₀ : Fin (Work.OROneRel.wordOf u).length)
    (hε : occEps K x (Work.OROneRel.wordOf u) i₀ ≠ 0)
    (hle : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      occEps K x (Work.OROneRel.wordOf u) i ≠ 0 →
      Multiplicative.toAdd (φ (presentRho r (occTerm x (Work.OROneRel.wordOf u) i))) ≤
        Multiplicative.toAdd (φ (presentRho r (occTerm x (Work.OROneRel.wordOf u) i₀))))
    (huniq : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      occEps K x (Work.OROneRel.wordOf u) i ≠ 0 →
      Multiplicative.toAdd (φ (presentRho r (occTerm x (Work.OROneRel.wordOf u) i))) =
        Multiplicative.toAdd (φ (presentRho r (occTerm x (Work.OROneRel.wordOf u) i₀))) → i = i₀) :
    annAt K r u {x} := by
  classical
  intro b hb
  have hb0 : b * rootVec K r u x = 0 := hb x (Set.mem_singleton x)
  rw [rootVec_eq_sum_occEps (K := K) (r := r) (u := u) x] at hb0
  set s : Finset (Fin (Work.OROneRel.wordOf u).length) :=
    Finset.univ.filter (fun i => occEps K x (Work.OROneRel.wordOf u) i ≠ 0) with hs
  have hsplit : (∑ i : Fin (Work.OROneRel.wordOf u).length,
        occEps K x (Work.OROneRel.wordOf u) i •
          MonoidAlgebra.of K (OneRelatorGroup r)
            (presentRho r (occTerm x (Work.OROneRel.wordOf u) i))) =
      ∑ i ∈ s, occEps K x (Work.OROneRel.wordOf u) i •
          MonoidAlgebra.of K (OneRelatorGroup r)
            (presentRho r (occTerm x (Work.OROneRel.wordOf u) i)) := by
    rw [hs, ← Finset.sum_subset (show (Finset.univ.filter
        (fun i : Fin (Work.OROneRel.wordOf u).length =>
          occEps K x (Work.OROneRel.wordOf u) i ≠ 0)) ⊆ Finset.univ
      from fun i _ => Finset.mem_univ i)]
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    rw [hi, zero_smul]
  rw [hsplit] at hb0
  refine signedSum_regular (K := K) φ s
    (fun i => presentRho r (occTerm x (Work.OROneRel.wordOf u) i))
    (fun i => occEps K x (Work.OROneRel.wordOf u) i) i₀ ?_ hε ?_ ?_ b hb0
  · rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hε⟩
  · intro i hi
    rw [hs] at hi
    exact hle i (Finset.mem_filter.mp hi).2
  · intro i hi
    rw [hs] at hi
    exact huniq i (Finset.mem_filter.mp hi).2

/-- **The level of an occurrence term.**  For a weight `c` killing `u`, the level in
`⟨α | u ^ l⟩` of the occurrence term `occTerm x (wordOf u) i` of the Fox expansion of `∂u/∂x` is the
signed sum of the weights of the letters of the corresponding prefix (`Work.OROneRel.lsig`).  This
is the formula by which the hypotheses of `annAt_of_occTerm_uniqueMax` are checked in practice: the
levels of the occurrence terms are the values of the linear functionals `c ↦ lsig c (prefix i)`. -/
theorem levelOfC_occTerm (c : α → ℤ) {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l)
    (hc : Work.OROneRel.cohom c u = 1) (x : α) (i : Fin (Work.OROneRel.wordOf u).length) :
    levelOfC c r u l hpow hc (presentRho r (occTerm x (Work.OROneRel.wordOf u) i)) =
      Multiplicative.ofAdd (Work.OROneRel.lsig c ((Work.OROneRel.wordOf u).take
        (i.1 + if (Work.OROneRel.wordOf u).get i = (x, true) then 0 else 1))) := by
  rw [levelOfC_presentRho, occTerm, Work.OROneRel.cohom_mk]

/-- **The level method with the weight made explicit.**  For a weight `c : α → ℤ` killing `u`, if
the occurrence terms of the Fox expansion of `∂u/∂x` (`occTerm`, with the signs `occEps`) have a
unique *maximum* of the values `Work.OROneRel.lsig c (prefix)` — the `c`-weights of the
corresponding prefixes, computed by `levelOfC_occTerm` — then the `x`-component of the root Fox
vector is a right non-zero-divisor.

This is the working interface of the level route: it removes the level homomorphism `φ` from the
hypotheses and replaces it by the explicit linear functional `lsig c` of the weight. -/
theorem annAt_of_occTerm_lsig_max (c : α → ℤ) {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l)
    (hc : Work.OROneRel.cohom c u = 1) {x : α} (i₀ : Fin (Work.OROneRel.wordOf u).length)
    (hε : occEps K x (Work.OROneRel.wordOf u) i₀ ≠ 0)
    (hmax : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      occEps K x (Work.OROneRel.wordOf u) i ≠ 0 →
      Work.OROneRel.lsig c ((Work.OROneRel.wordOf u).take
          (i.1 + if (Work.OROneRel.wordOf u).get i = (x, true) then 0 else 1)) ≤
        Work.OROneRel.lsig c ((Work.OROneRel.wordOf u).take
          (i₀.1 + if (Work.OROneRel.wordOf u).get i₀ = (x, true) then 0 else 1)))
    (huniq : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      occEps K x (Work.OROneRel.wordOf u) i ≠ 0 →
      Work.OROneRel.lsig c ((Work.OROneRel.wordOf u).take
          (i.1 + if (Work.OROneRel.wordOf u).get i = (x, true) then 0 else 1)) =
        Work.OROneRel.lsig c ((Work.OROneRel.wordOf u).take
          (i₀.1 + if (Work.OROneRel.wordOf u).get i₀ = (x, true) then 0 else 1)) → i = i₀) :
    annAt K r u {x} :=
  annAt_of_occTerm_uniqueMax (levelOfC c r u l hpow hc) i₀ hε
    (fun i hi => by
      rw [levelOfC_occTerm c hpow hc x i, levelOfC_occTerm c hpow hc x i₀,
        toAdd_ofAdd, toAdd_ofAdd]
      exact hmax i hi)
    (fun i hi h => huniq i hi (by
      rw [levelOfC_occTerm c hpow hc x i, levelOfC_occTerm c hpow hc x i₀,
        toAdd_ofAdd, toAdd_ofAdd] at h
      exact h))

end Occurrences

/-! ## `1 - h` and `1 + h` for a group element `h`

`mul_one_sub_of_infinite_order` gives the positive direction: `1 - h` is a right non-zero-divisor
when `h` has infinite order.  The converse is the *zero divisor* that makes the factorisation
arguments of the exceptional case necessary: for a non-trivial element of finite order the norm
element annihilates `1 - h` (resp. `1 + h`) on the right, so the component can *only* be regular
when the "ratio" of two paired Fox terms has infinite order. -/

section Order

/-- The norm element of a group element of order `n ≥ 1` is non-zero: its coefficient at the
identity is `1` (the only power `g ^ j` with `j < n` that can be trivial is `j = 0`). -/
theorem normElem_ne_zero_of_orderOf_eq {G : Type*} [Group G] {K : Type*} [Field K] {g : G}
    {n : ℕ} (hn : 1 ≤ n) (horder : orderOf g = n) : normElem K n g ≠ 0 := by
  classical
  intro h
  have hcoe : (normElem K n g).coeff (1 : G) = 1 := by
    have h1 : ∀ j : ℕ, (((MonoidAlgebra.of K G) g) ^ j).coeff (1 : G) =
        if g ^ j = 1 then (1 : K) else 0 := by
      intro j
      rw [← map_pow, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
        eq_comm]
    have hsum : (∑ j ∈ Finset.range n, (if g ^ j = 1 then (1 : K) else 0)) =
        (if g ^ 0 = 1 then (1 : K) else 0) := by
      refine Finset.sum_eq_single 0 ?_ ?_
      · intro j hj hne
        rw [if_neg (fun hgj => hne (Nat.eq_zero_of_dvd_of_lt
          (by rw [← horder]; exact orderOf_dvd_iff_pow_eq_one.mpr hgj)
          (Finset.mem_range.mp hj)))]
      · intro h0
        exact absurd (Finset.mem_range.mpr hn) h0
    rw [normElem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      Finset.sum_congr rfl (fun j _ => h1 j), hsum]
    simp
  rw [h] at hcoe
  simp only [MonoidAlgebra.coeff_zero] at hcoe
  exact absurd hcoe.symm (one_ne_zero (α := K))

end Order

/-! ## The Fox identity for the root, and `annAt` from Lyndon's identity theorem

The lemmas of this section are new.  They establish the *Fox fundamental identity for the root*
`Σ_x (∂u/∂x)(x - 1) = ū - 1` and use it, together with Lyndon's identity theorem
(`Work.ORLyndon.LyndonIdentity`), to prove the componentwise regularity of the root Fox vector
`∂u/∂x` — the crux of the residual `EpsNeZeroDescent`:

`Work.ORLyndon.annAt K (u ^ l) u (relatorLetters u)`
  ⟸ `Work.ORLyndon.LyndonIdentity K α (u ^ l) u l` and `(l : K) ≠ 0`.

See the module notes for the precise residual: the implication above is for the *full* letter set of
the root; the residual `EpsNeZeroDescent` asks for `annAt` at every *nonempty subset* `S` of the
letters, which is a strictly stronger statement (equivalently, `MagnusDescent K u l S` with the
trivial witness `v = of x₀` is *equivalent* to `annAt K (u ^ l) u S`, so the residual is exactly the
Magnus step and not merely the full-letter-set statement). -/

section RootAnnihilator

/-- A symbol not occurring in the root has vanishing `x`-component in the root Fox vector. -/
theorem rootVec_eq_zero_of_notMem (r u : FreeGroup α) {x : α}
    (hx : x ∉ Work.OROneRel.relatorLetters u) : rootVec K r u x = 0 := by
  rw [rootVec_apply, foxD_eq_zero_of_notMem_relatorLetters x u hx, map_zero]

/-- **The Fox fundamental identity for the root**: `δ((∂u/∂x)_x) = ū - 1`, i.e.
`Σ_x (∂u/∂x)(x̄ - 1) = ū - 1` in `K[G]`. -/
theorem lyndonDelta_rootVec (r u : FreeGroup α) :
    lyndonDelta K r (rootVec K r u) =
      (MonoidAlgebra.of K (OneRelatorGroup r)) (presentRho r u) - 1 := by
  rw [lyndonDelta_apply]
  show ((foxFD (K := K) u).mapRange (presentAlg K r) (map_zero _)).sum
      (fun x d => d * ((presentAlg K r)
        ((MonoidAlgebra.of K (FreeGroup α)) (FreeGroup.of x)) - 1)) = _
  rw [Work.ORLyndon.Fox.fundamental_identity_map (K := K) (presentAlg K r) u, presentAlg_of]

/-- The norm element is annihilated on the left by `of w - 1` whenever `w ^ l = 1`. -/
theorem sub_one_mul_normElem_eq_zero {G : Type*} [Group G] {K : Type*} [Field K] (w : G) {l : ℕ}
    (hwl : w ^ l = 1) : ((MonoidAlgebra.of K G w - 1) * normElem K l w) = 0 := by
  rw [normElem, mul_geom_sum, ← map_pow, ← map_one (MonoidAlgebra.of K G), hwl, sub_self]

/-- **From Lyndon's identity theorem**: every element of `ker θ` (i.e. annihilating the Fox vector
of the relator) is killed on the right by the norm element `1 + w + ⋯ + w ^ (l-1)`. -/
theorem ker_theta_mul_normElem_of_lyndonIdentity {X : Type u} [DecidableEq X] {K : Type v}
    [Field K] {r u : FreeGroup X} {l : ℕ} (h : LyndonIdentity K X r u l) :
    ∀ a : MonoidAlgebra K (OneRelatorGroup r),
      lyndonTheta K r a = 0 → a * normElem K l (presentRho r u) = 0 := by
  intro a ha
  have haz : a ∈ Ideal.span
      {((MonoidAlgebra.of K (OneRelatorGroup r)) (presentRho r u)) - 1} := by
    rw [← h.ker_theta]
    exact ha
  have hwl : (presentRho r u) ^ l = 1 := by
    rw [← map_pow, h.hpow, presentRho_relator]
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.mp haz
  rw [mul_assoc, sub_one_mul_normElem_eq_zero (presentRho r u) hwl, mul_zero]

/-- **The main transfer.**  Let `r = u ^ l`, and suppose that every element of `ker θ` is killed on
the right by the norm element of the class of `u` (`hwt`) and that every `b` with `b * of ū = b` is a
right multiple of the norm element (`hN`).  Then the `x`-components of the root Fox vector are
jointly right regular.  The proof is the Fox identity for the root: `b * (of ū - 1) = 0` forces
`b = c * N`, and `c * N = b` together with the vanishing of `b` on the root Fox vector puts `c` in
`ker θ`, whence `c * N = 0` and `b = 0`. -/
theorem annAt_letters_of_normElemDecomp (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hwt : ∀ a : MonoidAlgebra K (OneRelatorGroup r),
      lyndonTheta K r a = 0 → a * normElem K l (presentRho r u) = 0)
    (hN : ∀ b : MonoidAlgebra K (OneRelatorGroup r),
      b * MonoidAlgebra.of K (OneRelatorGroup r) (presentRho r u) = b →
      ∃ c, b = c * normElem K l (presentRho r u)) :
    annAt K r u (Work.OROneRel.relatorLetters u) := by
  classical
  intro b hb
  set w : OneRelatorGroup r := presentRho r u with hwdef
  have hz : b • rootVec K r u = 0 := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul]
    by_cases hx : x ∈ Work.OROneRel.relatorLetters u
    · exact hb x hx
    · rw [rootVec_eq_zero_of_notMem r u hx, mul_zero]
  have hfox : b * ((MonoidAlgebra.of K (OneRelatorGroup r)) w - 1) = 0 := by
    have h1 : lyndonDelta K r (b • rootVec K r u) =
        b * ((MonoidAlgebra.of K (OneRelatorGroup r)) w - 1) := by
      rw [map_smul, lyndonDelta_rootVec]
      rfl
    rw [← h1, hz, map_zero]
  have hbw : b * MonoidAlgebra.of K (OneRelatorGroup r) w = b := by
    have h2 : b * ((MonoidAlgebra.of K (OneRelatorGroup r)) w - 1) =
        b * MonoidAlgebra.of K (OneRelatorGroup r) w - b := by
      rw [mul_sub, mul_one]
    rw [h2] at hfox
    exact sub_eq_zero.mp hfox
  obtain ⟨c, hc⟩ := hN b hbw
  have hc_ker : lyndonTheta K r c = 0 := by
    rw [lyndonTheta_apply]
    apply Finsupp.ext
    intro x
    rw [Finsupp.smul_apply, Finsupp.zero_apply, smul_eq_mul]
    by_cases hx : x ∈ Work.OROneRel.relatorLetters u
    · have h3 : c * relatorVec K r x = c * normElem K l w * rootVec K r u x := by
        rw [relatorVec_eq_rootVec_smul r u l hpow, Finsupp.smul_apply, smul_eq_mul, mul_assoc]
      rw [h3, ← hc]
      exact hb x hx
    · have hzero : relatorVec K r x = 0 := by
        rw [relatorVec_eq_rootVec_smul r u l hpow, Finsupp.smul_apply, smul_eq_mul,
          rootVec_eq_zero_of_notMem r u hx, mul_zero]
      rw [hzero, mul_zero]
  have hfin := hwt c hc_ker
  rw [hc, hfin]

/-- **The `hN` hypothesis of `annAt_letters_of_normElemDecomp` when `(l : K) ≠ 0`**: from
`b * of w = b` one gets `b * N = (l : K) • b`, so `b = (((l : K))⁻¹ • b) * N`. -/
theorem exists_mul_normElem_of_l_ne_zero {G : Type*} [Group G] {K : Type*} [Field K] (w : G)
    {l : ℕ} (hwl : w ^ l = 1) (hl : (l : K) ≠ 0) {b : MonoidAlgebra K G}
    (hb : b * MonoidAlgebra.of K G w = b) :
    ∃ c : MonoidAlgebra K G, b = c * normElem K l w := by
  refine ⟨((l : K))⁻¹ • b, ?_⟩
  have hbk : ∀ k : ℕ, b * (MonoidAlgebra.of K G w) ^ k = b := by
    intro k
    induction k with
    | zero => rw [pow_zero, mul_one]
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hb]
  have hbN : b * normElem K l w = (l : K) • b := by
    rw [normElem, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun k _ => hbk k), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    exact (Algebra.smul_def (l : K) b).symm
  rw [smul_mul_assoc, hbN, smul_smul, inv_mul_cancel₀ hl, one_smul]

/-- **`annAt` at the letters of the root, from Lyndon's identity theorem** (for `(l : K) ≠ 0`). -/
theorem annAt_letters_of_lyndonIdentity (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hl : (l : K) ≠ 0) (h : LyndonIdentity K α r u l) :
    annAt K r u (Work.OROneRel.relatorLetters u) := by
  have hwl : (presentRho r u) ^ l = 1 := by rw [← map_pow, hpow, presentRho_relator]
  exact annAt_letters_of_normElemDecomp r u l hpow
    (ker_theta_mul_normElem_of_lyndonIdentity h)
    (fun b hb => exists_mul_normElem_of_l_ne_zero (presentRho r u) hwl hl hb)

/-- **`annAt` at the letters of the root, from Lyndon's identity theorem, in every
characteristic.**  Together with `Work.ORLyndon.annAt_letters_of_normElemDecomp` this removes the
hypothesis `(l : K) ≠ 0` of `annAt_letters_of_lyndonIdentity`, using the char-free decomposition of
the right annihilator of `of w - 1` (`Work.ORLyndon.exists_mul_normElem_of_mul_of_eq`, the coset
descent: `b * of w = b` forces `b` to be a right multiple of the norm element of `w`) together with
the order statement `orderOf (ū) = l` of `Work.ORLyndon.orderOf_presentRho_eps_ne_zero`. -/
theorem annAt_letters_of_lyndonIdentity_uncond (r u : FreeGroup α) (l : ℕ) (hpow : r = u ^ l)
    (hl : 1 ≤ l) (hne : (Work.OROneRel.relatorLetters u).Nonempty)
    (hbad : ∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u ≠ 0)
    (h : LyndonIdentity K α r u l) :
    annAt K r u (Work.OROneRel.relatorLetters u) := by
  classical
  have hord : orderOf (presentRho r u) = l := by
    subst hpow
    exact orderOf_presentRho_eps_ne_zero u l hl hne hbad
  refine annAt_letters_of_normElemDecomp r u l hpow
    (ker_theta_mul_normElem_of_lyndonIdentity h) ?_
  intro b hb
  obtain ⟨c, hc⟩ := exists_mul_normElem_of_mul_of_eq (K := K) (w := presentRho r u) hb
  exact ⟨c, by rw [hord] at hc; exact hc⟩

/-- **The trivial-witness Magnus descent**: `annAt` at a set of letters implies `MagnusDescent` at
that set, with witness the single letter `v = of x₀` (`x₀ ∈ S`), whose own annihilator statement is
trivial (its Fox component is a unit). -/
theorem magnusDescent_of_annAt {u : FreeGroup α} {l : ℕ}
    (hn : 2 ≤ Work.OROneRel.relatorNorm u) {S : Set α} (hSne : S.Nonempty)
    (hann : annAt K (u ^ l) u S) : MagnusDescent K u l S := by
  obtain ⟨x₀, hx₀⟩ := hSne
  have hpp : ¬ Work.OROneRel.IsProperPower (FreeGroup.of x₀) := by
    rintro ⟨v, k, hk, hvk⟩
    have h1 : k ≤ Work.OROneRel.relatorNorm (v ^ k) := by
      by_cases hv : v = 1
      · rw [hv, one_pow] at hvk
        exact absurd (Work.OROneRel.letterPow_true x₀ ▸ hvk)
          (Work.OROneRel.letterPow_ne_one x₀ true)
      · exact Work.OROneRel.le_relatorNorm_pow v k hv
    rw [← hvk, ← Work.OROneRel.letterPow_true x₀, Work.OROneRel.relatorNorm_letterPow] at h1
    omega
  have hcyc : Work.OROneRel.IsCyclicallyReducedRelator (FreeGroup.of x₀) := by
    have := Work.OROneRel.isCyclicallyReducedRelator_of_pow_ofNat (x := x₀) 1
    rwa [pow_one] at this
  refine ⟨α, FreeGroup.of x₀, (FreeGroup.of x₀) ^ l, {x₀}, hpp, rfl, hcyc, ?_,
    ⟨x₀, rfl⟩, ?_, ?_⟩
  · rw [← Work.OROneRel.letterPow_true x₀, Work.OROneRel.relatorNorm_letterPow]; omega
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy, ← Work.OROneRel.letterPow_true x₀, Work.OROneRel.relatorLetters_letterPow]
    exact Set.mem_singleton x₀
  · intro _
    exact hann

end RootAnnihilator

section OrderZeroDivisor

/-- **The zero divisor behind the exceptional case.**  If `h` has order `n ≥ 1`, then the norm
element `N = 1 + h + ⋯ + h ^ (n-1)` satisfies `(1 - h) * N = 0`: the element `1 - h` is *not* a
right non-zero-divisor as soon as `N ≠ 0`, i.e. as soon as `h ≠ 1`. -/
theorem one_sub_mul_normElem_eq_zero_of_orderOf {G : Type*} [Group G] {K : Type*} [Field K]
    {g : G} {n : ℕ} (hn : 1 ≤ n) (horder : orderOf g = n) :
    (1 - MonoidAlgebra.of K G g) * normElem K n g = 0 := by
  have hgn : g ^ n = 1 := by rw [← horder]; exact pow_orderOf_eq_one g
  have h1 : (MonoidAlgebra.of K G g - 1) * normElem K n g = 0 :=
    sub_one_mul_normElem_eq_zero (K := K) g hgn
  have h2 : (1 - MonoidAlgebra.of K G g) = -(MonoidAlgebra.of K G g - 1) := by rw [neg_sub]
  rw [h2, neg_mul, h1, neg_zero]

end OrderZeroDivisor

/-! ## The exceptional case: the elementary order tools

In the exceptional case of the level method the top level part of the component factors as
`A · (1 ± h)` with `A` a unit, and `annAt` at `x` follows from `A` being regular and `1 ± h` being
regular.  By `Work.ORLyndon.mul_one_sub_of_infinite_order` and
`Work.ORLyndon.one_sub_mul_normElem_eq_zero_of_orderOf` (together with
`normElem_ne_zero_of_orderOf_eq`) the factor `1 - h` is regular **iff** `h` has infinite order, and
the same holds for `1 + h`; so the exceptional case reduces to the *order* of the pairing ratio `h`.

The order of an explicit group element is certified by mapping to a torsion-free group: this is the
elementary criterion `Work.ORLyndon.orderOf_eq_zero_of_maps_ne_one` below, which is the form in
which the infinite order of the pairing ratios is expected to be proved (the obstruction is that in
the exceptional case every homomorphism to `ℤ` kills the ratio, so the target group must be a
non-abelian torsion-free quotient). -/

section ExceptionalTools

/-- `1 + c` is a right non-zero-divisor in `K[G]` whenever `c` has infinite order.  The proof is the
one of `Work.ORLyndon.mul_one_sub_of_infinite_order`: `b * (1 + c) = 0` forces `b = -b * c`, so every
coefficient function is constant in absolute value along the infinite orbit `x, x c, x c ^ 2, …`,
and a finitely supported function with infinitely many non-zero values vanishes. -/
theorem mul_one_add_of_infinite_order {G : Type*} [Group G] {K : Type*} [Field K] {c : G}
    (hc : orderOf c = 0) :
    ∀ b : MonoidAlgebra K G, b * (1 + MonoidAlgebra.of K G c) = 0 → b = 0 := by
  have hpow_inj := pow_injective_of_orderOf_eq_zero hc
  intro b hb
  have hbc : b = -(b * MonoidAlgebra.of K G c) := by
    have hsub : b * (1 + MonoidAlgebra.of K G c) = b + b * MonoidAlgebra.of K G c := by
      rw [mul_add, mul_one]
    rw [hsub, add_eq_zero_iff_eq_neg] at hb
    exact hb
  have hcoeff : ∀ x : G, b.coeff (x * c) = - b.coeff x := by
    intro x
    have hsplit : (b * (1 + MonoidAlgebra.of K G c)).coeff (x * c)
        = b.coeff (x * c) + (b * MonoidAlgebra.of K G c).coeff (x * c) := by
      rw [mul_add, mul_one]
      simp
    have hprod : (b * MonoidAlgebra.of K G c).coeff (x * c) = b.coeff x := by
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply]
      simp
    have hzero : (b * (1 + MonoidAlgebra.of K G c)).coeff (x * c) = 0 := by
      rw [hb]; rfl
    rw [hsplit, hprod] at hzero
    exact (add_eq_zero_iff_eq_neg.mp hzero)
  by_contra hb0
  have hne : b.coeff ≠ 0 := by
    intro h
    exact hb0 (MonoidAlgebra.coeff_injective (by rw [h, MonoidAlgebra.coeff_zero]))
  obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hfmem : ∀ n : ℕ, x * c ^ n ∈ b.coeff.support := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        have hstep : x * c ^ (n + 1) = (x * c ^ n) * c := by rw [pow_succ, ← mul_assoc]
        rw [hstep, Finsupp.mem_support_iff] at *
        rw [hcoeff]
        exact neg_ne_zero.mpr ih
  have hfinj : Function.Injective (fun n : ℕ => x * c ^ n) :=
    fun _ _ h => hpow_inj (mul_left_cancel h)
  have hrange : Set.range (fun n : ℕ => x * c ^ n) ⊆ (b.coeff.support : Set G) :=
    fun _ ⟨n, hn⟩ => hn ▸ hfmem n
  have hinf : (Set.range (fun n : ℕ => x * c ^ n)).Infinite :=
    Set.infinite_range_of_injective hfinj
  exact (Finset.finite_toSet b.coeff.support).not_infinite (hinf.mono hrange)

/-- **Infinite order certified by a torsion-free quotient.**  If `φ : G →* H` with `H` torsion-free
and `φ h ≠ 1`, then `h` has infinite order.  (Contrapositive: if a power of `h` is `1` then a power
of `φ h` is `1`, so `φ h` has finite order in the torsion-free group `H`.) -/
theorem orderOf_eq_zero_of_maps_ne_one {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hH : ∀ y : H, IsOfFinOrder y → y = 1) {g : G} (hg : φ g ≠ 1) : orderOf g = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn hgn
  exact hg (hH (φ g)
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [← map_pow, hgn, map_one]⟩))

/-- **`annAt` from a `1 - h` factorisation.**  If the `x`-component of the root Fox vector is a unit
times `1 - h` with `h` of infinite order, then it is a right non-zero-divisor.  This is the shape in
which the exceptional case of the level method is expected to be concluded. -/
theorem annAt_of_eq_unit_mul_one_sub {r u : FreeGroup α} {x : α}
    {h : OneRelatorGroup r} {A : MonoidAlgebra K (OneRelatorGroup r)} (hA : IsUnit A)
    (hfac : rootVec K r u x = A * (1 - MonoidAlgebra.of K (OneRelatorGroup r) h))
    (hord : orderOf h = 0) : annAt K r u {x} :=
  annAt_of_component (Set.mem_singleton x) fun b hb =>
    regular_of_unit_mul hA (mul_one_sub_of_infinite_order hord) b (by rw [← hfac]; exact hb)

/-- **`annAt` from a `1 + h` factorisation** (the shape arising when the two paired occurrence terms
carry the *same* sign). -/
theorem annAt_of_eq_unit_mul_one_add {r u : FreeGroup α} {x : α}
    {h : OneRelatorGroup r} {A : MonoidAlgebra K (OneRelatorGroup r)} (hA : IsUnit A)
    (hfac : rootVec K r u x = A * (1 + MonoidAlgebra.of K (OneRelatorGroup r) h))
    (hord : orderOf h = 0) : annAt K r u {x} :=
  annAt_of_component (Set.mem_singleton x) fun b hb =>
    regular_of_unit_mul hA (mul_one_add_of_infinite_order hord) b (by rw [← hfac]; exact hb)

end ExceptionalTools

/-! ## The domain route to the residual

For `l = 1` the group `⟨α | u⟩` (with `u` not a proper power) is torsion-free, and the classical
route to the componentwise regularity of the root Fox vector is then to know that the group algebra
`K[⟨α | u⟩]` has no zero divisors (which holds, for instance, when the group is orderable, by the
leading-monomial argument).  `annAt_of_ne_zero_of_noZeroDivisors` is the resulting reduction: the
component is regular as soon as it is non-zero, and `Work.ORLyndon.augmentation_rootVec` (a sibling
module) computes its augmentation as `eps · u`, so a letter of non-vanishing exponent sum has a
non-zero component.  The assembly is in `Submission/Work/ORLyndon/domainRoute.lean`
(`Work.ORLyndon.annAt_of_noZeroDivisors`). -/

/-- **`annAt` from the absence of zero divisors.**  If `K[⟨α | r⟩]` has no zero divisors, then any
non-zero component of the root Fox vector is right regular (and hence `annAt` holds at any set of
letters containing that letter). -/
theorem annAt_of_ne_zero_of_noZeroDivisors {r u : FreeGroup α} {x : α}
    (h : NoZeroDivisors (MonoidAlgebra K (OneRelatorGroup r)))
    (hne : rootVec K r u x ≠ 0) : annAt K r u {x} :=
  fun b hb => by
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
      (show b * rootVec K r u x = 0 from hb x (Set.mem_singleton x)) with h0 | h0
    · exact h0
    · exact absurd h0 hne

/-- **The residual of `EpsNeZeroDescent`, precisely.**  `EpsNeZeroDescent K` follows from the
statement that the `x`-component of the root Fox vector is *individually* right regular for every
letter `x` of every Case-2 root:

`∀ v l x, [hypotheses of `EpsNeZeroDescent`] → x ∈ relatorLetters v → annAt K (v ^ l) v {x}`

(the set-indexed `annAt` at a singleton).  Indeed, `annAt` at a singleton gives `annAt` at every
nonempty set `S` of letters containing `x` (`annAt_of_component`, using any `x ∈ S`), and then the
trivial witness `v = of x` turns `annAt` into a `MagnusDescent`; the order half is
`orderOf_presentRho_eps_ne_zero`.

This isolates the residual: by `magnusDescent_of_annAt` the *trivial witness* makes
`MagnusDescent K u l S` equivalent to `annAt K (u ^ l) u S`, so the residual is exactly the
componentwise regularity `annAt K (u ^ l) u {x}` — equivalently the Magnus step of the descent —
and *not* the (strictly weaker) statement `annAt K (u ^ l) u (relatorLetters u)` at the full letter
set, which is what `annAt_letters_of_lyndonIdentity` provides. -/
theorem epsNeZeroDescent_of_singleton_annAt
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v, annAt K (v ^ l) v {x}) :
    EpsNeZeroDescent.{u, v} K := by
  intro A _ u l hl hpp hcyc hn hbad S hSne hSsub
  have hu1 : u ≠ 1 := Work.OROneRel.ne_one_of_not_isProperPower hpp
  have hne : (Work.OROneRel.relatorLetters u).Nonempty :=
    relatorLetters_nonempty_of_ne_one hu1
  have hord : orderOf (presentRho (u ^ l) u) = l :=
    orderOf_presentRho_eps_ne_zero u l hl hne hbad
  obtain ⟨x, hx⟩ := hSne
  have hxs : x ∈ Work.OROneRel.relatorLetters u := hSsub hx
  have hcomp : ∀ b : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      b * rootVec K (u ^ l) u x = 0 → b = 0 :=
    fun b hb => h u l hl hpp hcyc hn hbad x hxs b fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hb
  exact ⟨magnusDescent_of_annAt hn ⟨x, hx⟩ (annAt_of_component hx hcomp), hord⟩

/-! ## The level criterion: the non-exceptional case of the residual

The residual `annAt K (u ^ l) u {x}` (the singleton form, `epsNeZeroDescent_of_singleton_annAt`) is
proved here for every `(u, x)` whose occurrence terms are *separated by a weight*.  The pieces are

* `Work.ORLyndon.exists_killing_weight_occTerm_max` (sibling module): if no two distinct occurrences
  of `x^{±1}` in the reduced word of `u` have prefixes whose exponent vectors differ by a rational
  multiple of `eps · u`, then some weight `c` with `cohom c u = 1` has a *unique strict maximiser*
  among the levels `lsig c (occPref …)` of the occurrence prefixes;
* `annAt_of_occTerm_lsig_max` (above): such a weight makes the top level part of the component a
  single monomial, hence a unit, so the component is a right non-zero-divisor.

The hypothesis fails exactly in the "exceptional case" of the level route, where all the occurrence
terms have the same level for *every* weight (a homomorphism `G →* ℤ` must kill `u`, because `ℤ` is
torsion-free); there the level method is provably silent and the component has to be analysed by the
order of the "pairing ratios" of the prefixes (see `NOTES_epsNeZeroDescent_level.md` §7.3 and the
tools of the `ExceptionalTools` section above). -/

/-- **The level criterion.**  Let `c`-weights separate the *occurrence terms* of the `x`-component of
the root Fox vector of `u`: suppose that no two distinct occurrences of `x^{±1}` in the reduced word
of `u` have prefixes whose exponent vectors differ by a *rational* multiple of the exponent vector
`eps · u` of `u`.  Then `(∂u/∂x)` is a right non-zero-divisor in `K[⟨α | u ^ l⟩]`:
`annAt K (u ^ l) u {x}`. -/
theorem annAt_of_occTerm_sep {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l) {x : α}
    (hex : ∃ i : Fin (Work.OROneRel.wordOf u).length,
      occSign x (Work.OROneRel.wordOf u) i ≠ 0)
    (hsep : ∀ i j : Fin (Work.OROneRel.wordOf u).length,
      occSign x (Work.OROneRel.wordOf u) i ≠ 0 →
      occSign x (Work.OROneRel.wordOf u) j ≠ 0 → i ≠ j →
      ¬ ∃ lam : ℚ, ∀ y : α,
        (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) i) : ℚ)
          = (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) j) : ℚ)
            + lam * (Work.OROneRel.eps y u : ℚ)) :
    annAt K r u {x} := by
  obtain ⟨c, hc, i₀, hi₀, hmax⟩ := exists_killing_weight_occTerm_max u x hex hsep
  refine annAt_of_occTerm_lsig_max (K := K) c hpow hc i₀ ?_ ?_ ?_
  · exact occEps_ne_zero_of_occSign_ne_zero x _ i₀ hi₀
  · intro i hi
    by_cases hii : i = i₀
    · subst hii; exact le_rfl
    · exact le_of_lt (hmax i (occSign_ne_zero_of_occEps_ne_zero x _ i hi) hii)
  · intro i hi heq
    by_cases hii : i = i₀
    · exact hii
    · exact absurd heq (ne_of_lt (hmax i (occSign_ne_zero_of_occEps_ne_zero x _ i hi) hii))

/-! ## The corrected level criterion (C′): a *dominating rational functional*

`annAt_of_occTerm_sep` needs the occurrence terms to be **pairwise** non-congruent modulo `ℚ·eps u`.
That is far stronger than necessary: the level method only needs a *unique strict maximiser*, so it
suffices that **some** occurrence term is congruent to no other one and lies on the convex hull of
the classes — equivalently, that some *rational* functional `φ` killing `eps u` strictly dominates
all the other occurrence terms (`NOTES_epsNeZeroDescent_level.md` §10.2).  The lemma below is that
criterion in analytic form: it is the working interface for every application of the level route,
because `exists_int_weight_dominated` (sibling module) turns the rational `φ` into the integer
weight `c` which `annAt_of_occTerm_lsig_max` consumes. -/
theorem annAt_of_occTerm_dominated {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l) {x : α}
    (s : Finset α) (hs : ∀ p ∈ Work.OROneRel.wordOf u, p.1 ∈ s)
    (i₀ : Fin (Work.OROneRel.wordOf u).length)
    (hi₀ : occSign x (Work.OROneRel.wordOf u) i₀ ≠ 0)
    (φ : α → ℚ)
    (hφ : (∑ y ∈ s, φ y * (Work.OROneRel.eps y u : ℚ)) = 0)
    (hmax : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      occSign x (Work.OROneRel.wordOf u) i ≠ 0 → i ≠ i₀ →
      (∑ y ∈ s, φ y *
        (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) i) : ℚ)) <
      (∑ y ∈ s, φ y *
        (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) i₀) : ℚ))) :
    annAt K r u {x} := by
  classical
  have hsub : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      ∀ p ∈ occPref x (Work.OROneRel.wordOf u) i, p.1 ∈ s := fun i p hp =>
    hs p (List.Sublist.subset (List.take_sublist _ (Work.OROneRel.wordOf u)) hp)
  -- The rational dominating functional in the form consumed by `exists_int_weight_dominated`.
  have hdom : ∃ φ' : α → ℚ, (∑ y ∈ s, φ' y * (Work.OROneRel.eps y u : ℚ)) = 0 ∧
      ∀ j : {i : Fin (Work.OROneRel.wordOf u).length //
          occSign x (Work.OROneRel.wordOf u) i ≠ 0},
        j ≠ ⟨i₀, hi₀⟩ →
        (∑ y ∈ s, φ' y * (Work.OROneRel.wordEps y
            (occPref x (Work.OROneRel.wordOf u) j.1) : ℚ)) <
        (∑ y ∈ s, φ' y * (Work.OROneRel.wordEps y
            (occPref x (Work.OROneRel.wordOf u) i₀) : ℚ)) := by
    refine ⟨φ, hφ, fun j hj => hmax j.1 j.2 fun h => hj (Subtype.ext h)⟩
  obtain ⟨c, hc0, hcle, hcuniq⟩ :=
    exists_int_weight_dominated s (fun y => (Work.OROneRel.eps y u : ℚ))
      (fun j : {i : Fin (Work.OROneRel.wordOf u).length //
          occSign x (Work.OROneRel.wordOf u) i ≠ 0} => fun y =>
        (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) j.1) : ℚ))
      ⟨i₀, hi₀⟩ hdom
  -- The `lsig`-weight of an occurrence prefix, as a rational functional.
  have hlsig : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      (Work.OROneRel.lsig c (occPref x (Work.OROneRel.wordOf u) i) : ℚ)
        = ∑ y ∈ s, (c y : ℚ) *
            (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) i) : ℚ) := by
    intro i
    rw [lsig_sum_wordEps c (occPref x (Work.OROneRel.wordOf u) i) s (hsub i)]
    push_cast
    rfl
  -- `c` kills `u`.
  have hcohom : Work.OROneRel.cohom c u = 1 := by
    have hlsigL : Work.OROneRel.lsig c (Work.OROneRel.wordOf u) = 0 := by
      have hcast : ((Work.OROneRel.lsig c (Work.OROneRel.wordOf u) : ℤ) : ℚ) = 0 := by
        rw [lsig_sum_wordEps c (Work.OROneRel.wordOf u) s hs]
        push_cast
        have hW : ∀ y : α, Work.OROneRel.wordEps y (Work.OROneRel.wordOf u)
            = Work.OROneRel.eps y u := fun y => rfl
        simp only [hW]
        exact hc0
      exact_mod_cast hcast
    have h1 : Work.OROneRel.cohom c u
        = Multiplicative.ofAdd (Work.OROneRel.lsig c (Work.OROneRel.wordOf u)) := by
      conv_lhs => rw [← Work.OROneRel.mk_wordOf u]
      rw [Work.OROneRel.cohom_mk c (Work.OROneRel.wordOf u)]
    rw [h1, hlsigL]
    rfl
  refine annAt_of_occTerm_lsig_max (K := K) c hpow hcohom i₀
    (occEps_ne_zero_of_occSign_ne_zero x _ i₀ hi₀) ?_ ?_
  · intro i hi
    have hi' : occSign x (Work.OROneRel.wordOf u) i ≠ 0 :=
      occSign_ne_zero_of_occEps_ne_zero x (Work.OROneRel.wordOf u) i hi
    have h1 : (Work.OROneRel.lsig c (occPref x (Work.OROneRel.wordOf u) i) : ℚ) ≤
        (Work.OROneRel.lsig c (occPref x (Work.OROneRel.wordOf u) i₀) : ℚ) := by
      rw [hlsig i, hlsig i₀]
      exact hcle ⟨i, hi'⟩
    exact_mod_cast h1
  · intro i hi heq
    have hi' : occSign x (Work.OROneRel.wordOf u) i ≠ 0 :=
      occSign_ne_zero_of_occEps_ne_zero x (Work.OROneRel.wordOf u) i hi
    by_cases hii : i = i₀
    · exact hii
    · have hEq : (∑ y ∈ s, (c y : ℚ) *
          (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) i) : ℚ)) =
          (∑ y ∈ s, (c y : ℚ) *
            (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) i₀) : ℚ)) := by
        rw [← hlsig i, ← hlsig i₀]
        exact_mod_cast heq
      exact absurd (congrArg Subtype.val (hcuniq ⟨i, hi'⟩ hEq)) hii

/-- **The residual of `EpsNeZeroDescent`, in the *corrected* level form (C′).**  Suppose that for
every Case-2 root `u` and every letter `x` of `u` there is a *rational* weight `φ` killing
`eps · u` and an occurrence `i₀` which `φ` makes the unique strict maximiser among the occurrence
prefixes.  Then `Work.ORLyndon.EpsNeZeroDescent K` holds.

The difference from `epsNeZeroDescent_of_occTerm_sep` is that the hypothesis here is
*existential in `φ` and in `i₀`*: the exponent vectors of the occurrence terms need only be
separated by the *value* of `φ`, not by their congruence classes modulo `ℚ · eps u`.  By
`NOTES_epsNeZeroDescent_level.md` §10.2 that is exactly the condition that the class of `i₀` is an
exposed vertex of the convex hull of the classes of the occurrence terms — so the residual of this
criterion is "every extremal class of occurrence terms carries at least two occurrences", which by
§10.3 contains the two-term congruence case `vec(gap) = ±eps u / 2` and its higher analogues. -/
theorem epsNeZeroDescent_of_occTerm_dominated
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        ∃ (s : Finset A) (_ : ∀ p ∈ Work.OROneRel.wordOf v, p.1 ∈ s)
          (i₀ : Fin (Work.OROneRel.wordOf v).length) (φ : A → ℚ),
          occSign x (Work.OROneRel.wordOf v) i₀ ≠ 0 ∧
          (∑ y ∈ s, φ y * (Work.OROneRel.eps y v : ℚ)) = 0 ∧
          (∀ i : Fin (Work.OROneRel.wordOf v).length,
            occSign x (Work.OROneRel.wordOf v) i ≠ 0 → i ≠ i₀ →
            (∑ y ∈ s, φ y * (Work.OROneRel.wordEps y
                (occPref x (Work.OROneRel.wordOf v) i) : ℚ)) <
            (∑ y ∈ s, φ y * (Work.OROneRel.wordEps y
                (occPref x (Work.OROneRel.wordOf v) i₀) : ℚ)))) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt ?_
  intro A _ v l hl hpp hcyc hn hbad x hx
  obtain ⟨s, hs, i₀, φ, hi₀, hφ, hmax⟩ := h v l hl hpp hcyc hn hbad x hx
  exact annAt_of_occTerm_dominated (K := K) (l := l) rfl s hs i₀ hi₀ φ hφ hmax

/-! ## The two-occurrence case of the root Fox vector

The two-term analysis of §9.3 of the notes shows that when a letter `x` occurs **exactly twice** in
the reduced word of `u` (necessarily with the same sign, by `eps x u ≠ 0`), the component
`rootVec K r u x` factors as `(unit) · (1 ± of (ratio))` with `ratio = x · A` (resp. `A · x⁻¹`), and
`annAt` at `x` is *equivalent* to `orderOf ratio = 0` in `⟨α | u ^ l⟩`.

The notes left that order statement open ("the Freiheitssatz certificate provably cannot apply to
the ratio").  It is nevertheless **provable**, by the following elementary trick, which is new here:

* in the one-relator group `Q = ⟨α | u⟩`, the single relation `P · xb · A · xb · B = 1` gives
  `xb · A · xb = P⁻¹ B⁻¹`, hence `(xb · A)² = P⁻¹ B⁻¹ A` — and the right-hand side is a word in the
  *other* generator letters;
* `P⁻¹B⁻¹A = 1` in the free group would give `A = BP` and hence `u = (P · xb · B)²`, a proper power;
* so the ratio's **square** is a nontrivial element of the free Magnus subgroup `F(α ∖ {x})`, which
  by the Freiheitssatz (`orderOf_presentedGroupMap_misses_eq_zero`) has infinite order in `Q`;
* since `⟨α | u ^ l⟩ ↠ ⟨α | u⟩`, the ratio has infinite order in `⟨α | u ^ l⟩` as well.

This section contains the vocabulary and the two component lemmas (the order statement and the
factorisation of the component); the assembly `annAt_of_twoOcc` is below.  The vocabulary
(`magIncl`, `xbOf`, `twoOccPref`, `twoOccRatio`) and the Freiheitssatz order certificate live in the
leaf module `Submission.Work.ORLyndon.twoOccBase`, which this file imports. -/

/-- **The corrected level criterion (C′) from an exposed vertex.**  This is the *geometric* form of
`annAt_of_occTerm_dominated`: it asks, instead of a rational weight `φ`, only that the occurrence
term `i₀` is a vertex of the convex hull of the occurrence-term classes modulo `ℚ · eps u` — i.e.
that `p i₀` is not a convex combination of the other occurrence vectors modulo `ℚ · eps u`.  The
rational weight `φ` is then produced by `Work.ORLyndon.exposedVertex_separating_weight`.

The hypothesis is exactly the condition of `NOTES_epsNeZeroDescent_level.md` §10.2–§10.4; the
residual of the criterion is therefore *"every vertex of the convex hull of the occurrence-term
classes carries at least two occurrences"*, which is the shape of the roots listed in §11.3. -/
theorem annAt_of_occTerm_exposed {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l) {x : α}
    (s : Finset α) (hs : ∀ p ∈ Work.OROneRel.wordOf u, p.1 ∈ s)
    (i₀ : Fin (Work.OROneRel.wordOf u).length)
    (hi₀ : occSign x (Work.OROneRel.wordOf u) i₀ ≠ 0)
    (hexp : ¬ ∃ (lam : {i : Fin (Work.OROneRel.wordOf u).length //
          occSign x (Work.OROneRel.wordOf u) i ≠ 0} → ℚ) (mu : ℚ),
      (∀ j, 0 ≤ lam j) ∧ lam ⟨i₀, hi₀⟩ = 0 ∧ (∑ j, lam j = 1) ∧
        ∀ y ∈ s, (Work.OROneRel.wordEps y
            (occPref x (Work.OROneRel.wordOf u) i₀) : ℚ)
          = (∑ j, lam j * (Work.OROneRel.wordEps y
              (occPref x (Work.OROneRel.wordOf u) j.1) : ℚ))
            + mu * (Work.OROneRel.eps y u : ℚ)) :
    annAt K r u {x} := by
  obtain ⟨φ, hφ, hstrict⟩ := exposedVertex_separating_weight s
    (fun y => (Work.OROneRel.eps y u : ℚ))
    (fun j : {i : Fin (Work.OROneRel.wordOf u).length //
        occSign x (Work.OROneRel.wordOf u) i ≠ 0} => fun y =>
      (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf u) j.1) : ℚ))
    ⟨i₀, hi₀⟩ hexp
  refine annAt_of_occTerm_dominated (K := K) hpow s hs i₀ hi₀ φ hφ ?_
  intro i hi hii
  exact hstrict ⟨i, hi⟩ (fun h => hii (congrArg Subtype.val h))

/-- **The residual of `EpsNeZeroDescent`, in the level form.**  If the separation hypothesis of
`annAt_of_occTerm_sep` holds for every Case-2 root `u` and every letter `x` of `u`, then
`Work.ORLyndon.EpsNeZeroDescent K` holds.

The exceptional case, in which the hypothesis fails, is exactly the case in which *every* weight
killing `u` gives all the occurrence terms of `∂u/∂x` the same level; no level function can then
separate them, and the level method is provably silent. -/
theorem epsNeZeroDescent_of_occTerm_sep
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        (∃ i : Fin (Work.OROneRel.wordOf v).length,
          occSign x (Work.OROneRel.wordOf v) i ≠ 0) ∧
        (∀ i j : Fin (Work.OROneRel.wordOf v).length,
          occSign x (Work.OROneRel.wordOf v) i ≠ 0 →
          occSign x (Work.OROneRel.wordOf v) j ≠ 0 → i ≠ j →
          ¬ ∃ lam : ℚ, ∀ y : A,
            (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf v) i) : ℚ)
              = (Work.OROneRel.wordEps y (occPref x (Work.OROneRel.wordOf v) j) : ℚ)
                + lam * (Work.OROneRel.eps y v : ℚ))) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt ?_
  intro A _ v l hl hpp hcyc hn hbad x hx
  obtain ⟨hex, hsep⟩ := h v l hl hpp hcyc hn hbad x hx
  exact annAt_of_occTerm_sep (K := K) (l := l) rfl hex hsep

/-! ## The two-term criterion

The level method (`annAt_of_occTerm_sep`) disposes of every `(u, x)` whose occurrence terms are
separated by a weight.  When it is silent, the terms fall into *pairs* with equal level, and the
component is a signed sum of monomials `s • of g` with the pairs sharing a factor
`(1 ± of (g⁻¹h))`.  The simplest such situation is the one in which the component has **exactly two
monomial terms**: then the component is `s • of g + t • of h`, and (because the coefficients are
`±1`) it factors as `(s • of g) * (1 ± of (g⁻¹ h))`, so `annAt` at `x` reduces to the *order* of the
explicit ratio `g⁻¹ h ∈ ⟨α | r⟩`.

The two lemmas below record this reduction.  The residual of the whole statement is therefore the
statement that these ratios have infinite order (see
`NOTES_epsNeZeroDescent_level.md`, §8–§9, for the analysis of that statement and the precise
situations in which it is currently out of reach). -/

section TwoTermCriterion

/-- **Two-term criterion, same signs.**  If the `x`-component of the root Fox vector is the sum of
two monomials with the *same* coefficient `s ∈ {1, -1}`, then it is a right non-zero-divisor as soon
as the ratio `g⁻¹ * h` has infinite order in `⟨α | r⟩`. -/
theorem annAt_of_two_monomials_of_eq_sign {r u : FreeGroup α} {x : α} {s : K}
    (hs : s = 1 ∨ s = -1) {g h : OneRelatorGroup r}
    (hfac : rootVec K r u x = s • MonoidAlgebra.of K (OneRelatorGroup r) g
      + s • MonoidAlgebra.of K (OneRelatorGroup r) h)
    (hord : orderOf (g⁻¹ * h) = 0) : annAt K r u {x} := by
  have hunit : IsUnit (s • MonoidAlgebra.of K (OneRelatorGroup r) g) := by
    have hof : IsUnit (MonoidAlgebra.of K (OneRelatorGroup r) g) :=
      ⟨⟨MonoidAlgebra.of K (OneRelatorGroup r) g,
        MonoidAlgebra.of K (OneRelatorGroup r) g⁻¹,
        by rw [← map_mul, mul_inv_cancel, map_one],
        by rw [← map_mul, inv_mul_cancel, map_one]⟩, rfl⟩
    rcases hs with rfl | rfl
    · simpa using hof
    · simpa using hof.neg
  have hfact : rootVec K r u x
      = (s • MonoidAlgebra.of K (OneRelatorGroup r) g)
        * (1 + MonoidAlgebra.of K (OneRelatorGroup r) (g⁻¹ * h)) := by
    rw [hfac, mul_add, mul_one, smul_mul_assoc, ← map_mul]
    congr 2
    group
  exact annAt_of_eq_unit_mul_one_add (K := K) (h := g⁻¹ * h) hunit hfact hord

/-- **Two-term criterion, opposite signs.**  The companion of `annAt_of_two_monomials_of_eq_sign` for
a component whose two monomial coefficients are opposite (`s` and `-s` with `s ∈ {1, -1}`): then the
component factors as `(s • of g) * (1 - of (g⁻¹ * h))`. -/
theorem annAt_of_two_monomials_of_opposite_sign {r u : FreeGroup α} {x : α} {s : K}
    (hs : s = 1 ∨ s = -1) {g h : OneRelatorGroup r}
    (hfac : rootVec K r u x = s • MonoidAlgebra.of K (OneRelatorGroup r) g
      + (-s) • MonoidAlgebra.of K (OneRelatorGroup r) h)
    (hord : orderOf (g⁻¹ * h) = 0) : annAt K r u {x} := by
  have hunit : IsUnit (s • MonoidAlgebra.of K (OneRelatorGroup r) g) := by
    have hof : IsUnit (MonoidAlgebra.of K (OneRelatorGroup r) g) :=
      ⟨⟨MonoidAlgebra.of K (OneRelatorGroup r) g,
        MonoidAlgebra.of K (OneRelatorGroup r) g⁻¹,
        by rw [← map_mul, mul_inv_cancel, map_one],
        by rw [← map_mul, inv_mul_cancel, map_one]⟩, rfl⟩
    rcases hs with rfl | rfl
    · simpa using hof
    · simpa using hof.neg
  have hfact : rootVec K r u x
      = (s • MonoidAlgebra.of K (OneRelatorGroup r) g)
        * (1 - MonoidAlgebra.of K (OneRelatorGroup r) (g⁻¹ * h)) := by
    have hof : MonoidAlgebra.of K (OneRelatorGroup r) g
        * MonoidAlgebra.of K (OneRelatorGroup r) (g⁻¹ * h)
        = MonoidAlgebra.of K (OneRelatorGroup r) h := by
      rw [← map_mul, show g * (g⁻¹ * h) = h by group]
    rw [hfac, mul_sub, mul_one, smul_mul_assoc, hof, neg_smul, sub_eq_add_neg]
  exact annAt_of_eq_unit_mul_one_sub (K := K) (h := g⁻¹ * h) hunit hfact hord

end TwoTermCriterion

/-! ## The order certificate through a level (weight)

Dually to the Freiheitssatz certificate: a homomorphism to the *torsion-free* group
`Multiplicative ℤ` sending the ratio non-trivially certifies its infinite order
(`orderOf_eq_zero_of_maps_ne_one`).  The level maps of this file (`levelOfC c r u l hpow hc`, for a
weight `c` with `cohom c u = 1`) are exactly the homomorphisms `⟨α | u ^ l⟩ →* Multiplicative ℤ`, so
the certificate reads: *if some weight killing `u` gives the ratio a non-zero level, the ratio has
infinite order*. -/

section LevelCertificate

/-- `Multiplicative ℤ` is torsion-free, in the form consumed by `orderOf_eq_zero_of_maps_ne_one`.
(`Multiplicative ℤ` is `IsMulTorsionFree` by instance, being the multiplicative copy of the
additively torsion-free `ℤ`.) -/
theorem isOfFinOrder_multiplicative_int_eq_one (y : Multiplicative ℤ) (hy : IsOfFinOrder y) :
    y = 1 := by
  obtain ⟨n, hn, hyn⟩ := isOfFinOrder_iff_pow_eq_one.mp hy
  have h2 : y ^ n = 1 ^ n := by rw [hyn, one_pow]
  exact IsMulTorsionFree.pow_left_injective (M := Multiplicative ℤ) (n := n) hn.ne' h2

/-- **The level certificate.**  If a weight `c` with `cohom c u = 1` gives the element `q` a
non-trivial level in `⟨α | u ^ l⟩`, then `q` has infinite order. -/
theorem orderOf_eq_zero_of_level_ne_one {r u : FreeGroup α} {l : ℕ} (hpow : r = u ^ l)
    {c : α → ℤ} (hc : Work.OROneRel.cohom c u = 1) {q : OneRelatorGroup r}
    (hq : levelOfC c r u l hpow hc q ≠ 1) : orderOf q = 0 :=
  orderOf_eq_zero_of_maps_ne_one (levelOfC c r u l hpow hc)
    isOfFinOrder_multiplicative_int_eq_one hq

end LevelCertificate

/-- **The two-occurrence case of the singleton `annAt`.**  Suppose a letter `x` occurs exactly twice
in the reduced word of the root `u`, both times as the same signed letter `xb = x^{±1}` — say

`u = P · xb · A · xb · B`   with `P, A, B ∈ F(α ∖ {x})`

(the shape in which `Work.ORLyndon.twoOccRoot`, this file's assembly, is applied).  Then the
`x`-component of the root Fox vector is a right non-zero-divisor in `K[⟨α | u ^ l⟩]`:

`annAt K (u ^ l) u {x}`.

The proof combines the two component lemmas `Work.ORLyndon.rootVec_eq_of_twoOcc` (the component is
`(unit)·(1 + of (ratio))`) and `Work.ORLyndon.orderOf_presentRho_twoOcc` (the ratio has infinite
order) with the two-term criterion `annAt_of_two_monomials_of_eq_sign`. -/
theorem annAt_of_twoOcc {K : Type v} [Field K] {u : FreeGroup α} {x : α} {b : Bool} {l : ℕ}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hx : x ∈ Work.OROneRel.relatorLetters u)
    {P A B : FreeGroup {z : α // z ≠ x}}
    (hu : u = magIncl x P * xbOf x b * magIncl x A * xbOf x b * magIncl x B) :
    annAt K (u ^ l) u {x} := by
  set g : OneRelatorGroup (u ^ l) := presentRho (u ^ l) (twoOccPref x b P) with hg
  set h : OneRelatorGroup (u ^ l)
    := presentRho (u ^ l) (twoOccPref x b P) * presentRho (u ^ l) (twoOccRatio x b A) with hh
  have hgh : g⁻¹ * h = presentRho (u ^ l) (twoOccRatio x b A) := by
    rw [hg, hh]
    group
  have hord : orderOf (g⁻¹ * h) = 0 := by
    rw [hgh]
    exact orderOf_presentRho_twoOcc (x := x) (b := b) (l := l) hcyc hpp hx hu
  have hkey : MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g *
      (1 + MonoidAlgebra.of K (OneRelatorGroup (u ^ l))
        (presentRho (u ^ l) (twoOccRatio x b A)))
      = MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) g
        + MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) h := by
    rw [mul_add, mul_one, hh, hg]
    congr 1
    rw [← map_mul]
  have hfac : rootVec K (u ^ l) u x = (if b then (1 : K) else -1) • MonoidAlgebra.of K
        (OneRelatorGroup (u ^ l)) g
      + (if b then (1 : K) else -1) • MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) h := by
    rw [rootVec_eq_of_twoOcc (r := u ^ l) (x := x) (b := b) hu, ← hg, hkey, smul_add]
  refine annAt_of_two_monomials_of_eq_sign (K := K) (r := u ^ l) (u := u) (x := x)
    (s := (if b then (1 : K) else -1)) (g := g) (h := h) ?_ hfac hord
  by_cases hb : b <;> simp [hb]

/-- **The two-occurrence case in terms of the occurrence count.**  If the reduced word of `u`
contains exactly two occurrences of `x^{±1}` and the exponent sum of `x` in `u` is non-zero (so
that both occurrences carry the same sign), then `annAt K (u ^ l) u {x}` — for every `l` and every
field.

This is the form in which the two-occurrence theorem is applied in practice: the decomposition
`u = P · xᵇ · A · xᵇ · B` is produced internally by `Work.ORLyndon.exists_twoOcc_decomp`. -/
theorem annAt_of_twoOcc_of_count {K : Type v} [Field K] {u : FreeGroup α} {x : α} {l : ℕ}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hpp : ¬ Work.OROneRel.IsProperPower u)
    (hx : x ∈ Work.OROneRel.relatorLetters u)
    (h2 : (Work.OROneRel.wordOf u).count (x, true)
      + (Work.OROneRel.wordOf u).count (x, false) = 2)
    (heps : Work.OROneRel.eps x u ≠ 0) :
    annAt K (u ^ l) u {x} := by
  obtain ⟨b, P, A, B, huv⟩ := exists_twoOcc_decomp (u := u) (x := x) hx h2 heps
  exact annAt_of_twoOcc (K := K) (l := l) hcyc hpp hx huv

/-- `Work.OROneRel.wordOf` and `FreeGroup.toWord` are the same reduced word: the choice of
`DecidableEq` instance is irrelevant (`Decidable _` is a subsingleton). -/
theorem wordOf_eq_toWord {α : Type u} [DecidableEq α] (v : FreeGroup α) :
    Work.OROneRel.wordOf v = FreeGroup.toWord v := by
  have h : (Classical.decEq α : DecidableEq α) = ‹DecidableEq α› := Subsingleton.elim _ _
  show @FreeGroup.toWord α (Classical.decEq α) v = @FreeGroup.toWord α ‹DecidableEq α› v
  rw [h]

/-- **The residual of `EpsNeZeroDescent` after the one- and two-occurrence cases.**

For a Case-2 root `u` and a letter `x` of `u`:

* if `x` occurs **once** in the reduced word of `u`, the `x`-component of the root Fox vector is a
  unit, so `annAt K (u ^ l) u {x}` holds (`isUnit_rootVec_of_letterOnce`);
* if `x` occurs **twice**, then (since `eps x u ≠ 0` forces the two occurrences to carry the same
  sign) `u` has the shape `P · xb · A · xb · B` with `P, A, B` in the other generators
  (`Work.ORLyndon.exists_twoOcc_decomp`), and `annAt K (u ^ l) u {x}` holds by
  `annAt_of_twoOcc`.

Consequently, `EpsNeZeroDescent K` follows from the statements for the letters occurring **at least
three times**.  Those remaining letters are handled by the level criterion
(`annAt_of_occTerm_dominated`, `annAt_of_occTerm_sep`) whenever some weight has a unique strict
maximiser on the occurrence terms; what is left after both is the class of roots in which *every*
congruence class of occurrence terms carries at least two occurrences (see
`NOTES_epsNeZeroDescent_level.md` §11). -/
theorem epsNeZeroDescent_of_three_plus
    (h3 : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        3 ≤ (Work.OROneRel.wordOf v).count (x, true)
          + (Work.OROneRel.wordOf v).count (x, false) → annAt K (v ^ l) v {x}) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt ?_
  intro A _ v l hl hpp hcyc hn hbad x hx
  have hpos : 0 < (Work.OROneRel.wordOf v).count (x, true)
      + (Work.OROneRel.wordOf v).count (x, false) := by
    obtain ⟨b, hb⟩ := hx
    have hb' : (x, b) ∈ Work.OROneRel.wordOf v := by
      simpa only [Work.OROneRel.wordOf] using hb
    have hlt := List.count_pos_iff.mpr hb'
    cases b <;> omega
  rcases Nat.lt_or_ge ((Work.OROneRel.wordOf v).count (x, true)
      + (Work.OROneRel.wordOf v).count (x, false)) 3 with hlt3 | hge3
  · -- at most two occurrences: one or two
    have hcases :
        ((Work.OROneRel.wordOf v).count (x, true) = 1 ∧
          (Work.OROneRel.wordOf v).count (x, false) = 0) ∨
        ((Work.OROneRel.wordOf v).count (x, true) = 0 ∧
          (Work.OROneRel.wordOf v).count (x, false) = 1) ∨
        ((Work.OROneRel.wordOf v).count (x, true)
          + (Work.OROneRel.wordOf v).count (x, false) = 2) := by omega
    rcases hcases with ⟨h1, h0⟩ | ⟨h1, h0⟩ | h2
    · -- exactly one occurrence, as `x`
      refine annAt_of_unit (Set.mem_singleton x)
        (isUnit_rootVec_of_letterOnce (v ^ l) v x true ⟨?_, ?_⟩)
      · have h := h1; rw [wordOf_eq_toWord v] at h; exact h
      · have h := h0; rw [wordOf_eq_toWord v] at h; exact h
    · -- exactly one occurrence, as `x⁻¹`
      refine annAt_of_unit (Set.mem_singleton x)
        (isUnit_rootVec_of_letterOnce (v ^ l) v x false ⟨?_, ?_⟩)
      · have h := h0; rw [wordOf_eq_toWord v] at h; exact h
      · have h := h1; rw [wordOf_eq_toWord v] at h; exact h
    · -- exactly two occurrences
      obtain ⟨b, P, A, B, huv⟩ := exists_twoOcc_decomp (u := v) (x := x) hx h2 (hbad x hx)
      exact annAt_of_twoOcc (K := K) (l := l) hcyc hpp hx huv
  · exact h3 v l hl hpp hcyc hn hbad x hx hge3

/-- **The Magnus-subgroup case of the residual.**  `EpsNeZeroDescent K` follows from the statement
that, for every Case-2 root `v`, every `l ≥ 1` and every letter `x` of `v`, there is a letter `y` of
`v` whose Magnus subgroup contains the whole support of `rootVec K (v ^ l) v x` (equivalently: all the
occurrence terms of `∂v/∂x` avoid `y`), together with `rootVec K (v ^ l) v x ≠ 0`.

The Magnus subgroup at `y` is *free* by the Freiheitssatz (`Work.OROneRel.freiheitssatz_at`, which is
proved unconditionally) and free groups have domain group algebras
(`Work.ORLyndon.monoidAlgebra_freeGroup_isDomain`), so the component is a right non-zero-divisor by
`Work.ORLyndon.annAt_of_support_le_magnusSubgroup`.  This is strictly stronger than the level
criterion `annAt_of_occTerm_dominated`: the latter needs a weight `c` with `cohom c u = 1` and
`eps y u = 1`, whereas here no weight is involved at all. -/
theorem epsNeZeroDescent_of_magnus_support
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v, ∃ y ∈ Work.OROneRel.relatorLetters v,
        ↑(rootVec K (v ^ l) v x).coeff.support ⊆
          (Work.OROneRel.magnusSubgroup (v ^ l) y : Set (OneRelatorGroup (v ^ l))) ∧
        rootVec K (v ^ l) v x ≠ 0) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt (K := K) fun {A} _ v l hl hpp hcyc hn hbad x hx => ?_
  obtain ⟨y, hy, hsupp, hne⟩ := h v l hl hpp hcyc hn hbad x hx
  exact annAt_of_support_le_magnusSubgroup (K := K)
    (Work.OROneRel.isCyclicallyReducedRelator_pow hcyc l)
    (by rw [Work.ORLyndon.relatorLetters_pow v hl]; exact hy) hsupp hne

/-- **The full-letter-set (`Vann`) form of the residual, from Nielsen transforms.**

`Work.ORLyndon.Vann K (u ^ l) u` is the triviality of the annihilator of the root Fox *vector*; by
`Work.ORLyndon.vann_iff_annAt_letters` it is the same as `annAt K (u ^ l) u (relatorLetters u)`.
This is exactly the input consumed by the Cohen--Lyndon reduction (`annAt` at the letters of the
root gives `vector_zero_of_annAt_letters`, hence `LyndonIndependence`, hence `LyndonIdentity`).

The theorem says: it suffices to prove `Vann` at *some* bijective Nielsen transform of every Case-2
root.  This is a genuine enlargement of the reach of every sufficient condition for `Vann` (the
level criterion `annAt_of_occTerm_dominated`, `isUnit_rootVec_of_letterOnce`, `annAt_of_twoOcc`, the
Magnus-subgroup criterion `annAt_of_support_le_magnusSubgroup`, ...): those may be applied to
`ψ u` rather than to `u`.

It is however **strictly weaker** than `EpsNeZeroDescent`, which needs `annAt` at *every* nonempty
subset `S ⊆ relatorLetters u`, hence at the singletons; `Vann` only gives `S = relatorLetters u`.
The singleton-level analogue needs the componentwise transfer (the Jacobian `(∂(ψ x)/∂y)` must be
monomial in the `x`-column), i.e. a shear `x ↦ x · u₀` of the letter `x` itself -- and the
congruence classes of the occurrence terms at `x` are provably *invariant* under such a shear when
all `x`-occurrences have the same sign, so that route does not enlarge the level criterion at `x`.
See `NOTES_epsNeZeroDescent_level.md` §18. -/
theorem annAt_letters_of_vann_nielsen
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∃ (ψ : FreeGroup A →* FreeGroup A), Function.Injective ψ ∧ Function.Surjective ψ ∧
        Vann K ((ψ v) ^ l) (ψ v)) :
    ∀ {A : Type u} [DecidableEq A] (u : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower u → Work.OROneRel.IsCyclicallyReducedRelator u →
      2 ≤ Work.OROneRel.relatorNorm u →
      (∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u ≠ 0) →
      annAt K (u ^ l) u (Work.OROneRel.relatorLetters u) := by
  intro A _ u l hl hpp hcyc hn hbad
  obtain ⟨ψ, hι, hσ, hvann⟩ := h u l hl hpp hcyc hn hbad
  exact annAt_letters_of_vann (vann_of_vann_psi ψ hι hσ u l hvann)

/-- **The Cohen--Lyndon theorem from `Vann` at a Nielsen transform.**  Combining the reduction above
with the order statement `Work.ORLyndon.orderOf_presentRho_eps_ne_zero` and the module form of the
Cohen--Lyndon theorem gives `LyndonIndependence`, the input on which the whole `ORLyndon` chapter is
built. -/
theorem lyndonIndependence_of_vann_nielsen
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∃ (ψ : FreeGroup A →* FreeGroup A), Function.Injective ψ ∧ Function.Surjective ψ ∧
        Vann K ((ψ v) ^ l) (ψ v)) :
    ∀ {A : Type u} [DecidableEq A] (u : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower u → Work.OROneRel.IsCyclicallyReducedRelator u →
      2 ≤ Work.OROneRel.relatorNorm u →
      (∀ x ∈ Work.OROneRel.relatorLetters u, Work.OROneRel.eps x u ≠ 0) →
      LyndonIndependence K (u ^ l) u := by
  intro A _ u l hl hpp hcyc hn hbad
  have hann := annAt_letters_of_vann_nielsen (K := K) h u l hl hpp hcyc hn hbad
  have hne : (Work.OROneRel.relatorLetters u).Nonempty :=
    relatorLetters_nonempty_of_ne_one (Work.OROneRel.ne_one_of_not_isProperPower hpp)
  exact lyndon_independence_of_rootVec_inj (u ^ l) u l hl rfl
    (orderOf_presentRho_eps_ne_zero u l hl hne hbad)
    (vector_zero_of_annAt_letters hann)

theorem epsNeZeroDescent_of_singleton_jacobian
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        ∃ (ψ : FreeGroup A →* FreeGroup A) (_ : Function.Injective ψ)
          (_ : Function.Surjective ψ),
          (∀ q : A, q ≠ x → foxD (K := K) x (ψ (FreeGroup.of q)) = 0) ∧
          annAt K ((ψ v) ^ l) (ψ v) {x}) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt (K := K) fun {A} _ v l hl hpp hcyc hn hbad x hx => ?_
  obtain ⟨ψ, hι, hσ, hJ, hann⟩ := h v l hl hpp hcyc hn hbad x hx
  exact annAt_of_jacobian_zero ψ hι hσ v l x hJ hann

/-- **The geometric-progression family of the residual.**  `EpsNeZeroDescent K` follows if for every
Case-2 root `v` and letter `x` the component `rootVec K (v ^ l) v x` factors as
`of g * (1 + of h + of h ^ 2 + ⋯ + of h ^ (k-1))` with `h ^ k` of infinite order in
`⟨α | v ^ l⟩`.

This is the case in which the occurrence terms of `∂v/∂x` form a *geometric progression*
`t_0, t_0 h, t_0 h^2, …, t_0 h^{k-1}` (so all consecutive gap ratios coincide); the criterion itself
is `Work.ORLyndon.annAt_of_geometric` (the support argument: `c * N_k(h) = 0` implies
`c * of h ^ k = c`, which forces the support to be invariant under the infinite cyclic group
`⟨h ^ k⟩`, hence `c = 0`).  Note that `h ^ k` of infinite order cannot be replaced by `h` alone, and
that when `h` *is* of finite order the component is a genuine zero divisor in small characteristic —
so the infinite-order hypothesis is essential. -/
theorem epsNeZeroDescent_of_geometric
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ x ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps x v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        ∃ (k : ℕ) (g hh : OneRelatorGroup (v ^ l)),
          rootVec K (v ^ l) v x =
            (MonoidAlgebra.of K (OneRelatorGroup (v ^ l)) g) *
              (∑ i ∈ Finset.range k, (MonoidAlgebra.of K (OneRelatorGroup (v ^ l)) hh) ^ i) ∧
          orderOf (hh ^ k) = 0) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt (K := K) fun {A} _ v l hl hpp hcyc hn hbad x hx => ?_
  obtain ⟨k, g, hh, hfac, hord⟩ := h v l hl hpp hcyc hn hbad x hx
  exact annAt_of_geometric (K := K) k g hh hfac hord

/-- **Shear invariance of the singleton statement.**  Let `x` be a generator and `u₀` a word not
involving `x`; let `ψ : x ↦ x · u₀`, other generators fixed (`shear_lift_bijective`, proved: `ψ` is
bijective and its Fox Jacobian satisfies `∂(ψ(of q))/∂x = if q = x then 1 else 0`).  Then the
`x`-component of the root Fox vector transforms by the induced isomorphism of group algebras,

`rootVec K ((ψu)^l) (ψu) x = ψ̄ (rootVec K (u^l) u x)`,

so the *singleton* statement `annAt K (·) (·) {x}` is the same for `u` and for `ψu`.  This is the
componentwise analogue of `Work.ORLyndon.vann_of_vann_psi`; by §18.4 of the notes, the congruence
classes of the occurrence terms at `x` are *invariant* under such a shear when all `x`-occurrences
carry the same sign, so this does not by itself enlarge the level criterion at `x`, but it does let
every other sufficient condition for `annAt` (`annAt_of_twoOcc`, `annAt_of_support_le_magnusSubgroup`,
the level criteria, `annAt_of_geometric`, ...) be tested at a sheared root. -/
theorem annAt_singleton_of_shear {A : Type u} [DecidableEq A] {K : Type v} [Field K]
    (x : A) (u₀ : FreeGroup A) (hx : x ∉ Work.OROneRel.relatorLetters u₀)
    (u : FreeGroup A) (l : ℕ) :
    annAt K
        ((FreeGroup.lift (fun z : A => if z = x then FreeGroup.of x * u₀ else FreeGroup.of z) u) ^ l)
        (FreeGroup.lift (fun z : A => if z = x then FreeGroup.of x * u₀ else FreeGroup.of z) u)
        {x} →
      annAt K (u ^ l) u {x} := by
  obtain ⟨hι, hσ, hJ⟩ := shear_lift_bijective (K := K) x u₀ hx
  refine annAt_of_jacobian_zero _ hι hσ u l x fun q hq => ?_
  rw [hJ q, if_neg hq]

/-! ## The clean-shortening reduction (session 14)

The residual (all occurrence terms of `∂u/∂x` congruent modulo `ℚ · eps u`) is invisible to *every*
character of the group (`Work.ORLyndon.annAt_of_occTerm_dominated` and its predecessors) and to every
character of a subgroup that extends to one; by §18.4 of the notes it is also invariant under
"clean" Nielsen transformations.  The route recorded here is the *only* remaining elementary one: it
does not *separate* the terms, it **shortens the root**.

Observation.  Let `ψ` be a bijective Nielsen transformation that is *clean at `x`*
(`∂(ψ q)/∂x = 0` for `q ≠ x`, e.g. `ψ = x ↦ x` extended by any automorphism of the free factor
`F(α ∖ {x})`).  Then `Work.ORLyndon.annAt_of_jacobian_zero` transports the singleton statement from
`ψ u` back to `u`.  Hence, **if `ψ u` is strictly shorter than `u` (and still cyclically reduced and
not a proper power), the singleton statement at `u` follows from the induction hypothesis at
`ψ u`** -- no matter how complicated `ψ u` is.  This is the analogue for `annAt` of the descent step
`Work.ORLyndon.annAt_of_epsZero_strong`, and it uses an entirely different permutation of the
letters: the automorphism of `F(α ∖ {x})` acts on the *gaps* `W_j` of the word
`u = t_0 (x W_1) (x W_2) ⋯ (x W_k)`.

Verified on the first residual example of the notes, `u = a b c · a c b · a b c`, `x = a`
(`Work.ORLyndon.annAt_singletons_of_clean_shortening` is unconditional in the *shortening*, so this
is a mathematical computation): the transvection `φ : c ↦ b⁻¹ c` of `F(b,c)` sends `u` to
`a c · a (b⁻¹c b) · a c`, of relator norm `8 < 9`, and the transfer applies.  The same trick works
for `u = [y,z] · (x y z)^k`.

**But shortening is *not* always available.**  For `u = [y²,z²] · (x y²z²)^k` (cyclically reduced,
not a proper power for `k ≥ 1`, residual) *no* clean transformation shortens: `|φ(y²z²)| ≥ 4` and
`|φ([y²,z²])| ≥ 8` for every `φ ∈ Aut(F(y,z))`, so `relatorNorm (ψ u) ≥ 4 + 5k = relatorNorm u` for
every clean `ψ` (the identity giving equality).  In that example all gaps `W_j = y²z²` are *equal*,
so the component factors as `of(t_0) · Σ_{i<k} of(h)^i` with `h = x y²z²` and
`Work.ORLyndon.annAt_of_geometric` applies as soon as `orderOf (h ^ k) = 0` -- and
`h^k = t_0⁻¹ · ū` **cannot** be certified by any character (it lies in the kernel of every
`G →* ℤ`).  So the residual splits into two cases:

* **(G) geometric** (all gaps equal): `annAt_of_geometric` reduces it to an *order* statement that
  every character kills -- the input that only KMS can supply;
* **(A) aperiodic** (some two gaps differ): the clean-shortening route, and no counterexample to it
  is known (the failures above all have equal gaps).

This file records the *reduction* of the whole target to (G) ∪ (A) in the weakest form that is
provable without further input: from the bare existence of a clean shortening for every root the
target follows by strong induction. -/

/-- **The clean transfer of the singleton statement.**  If `ψ` is bijective and *clean at `x`*
(`ψ (of q)` avoids `x` for every `q ≠ x`), then the `x`-component of the root Fox vector of `ψ u` is
the image of the `x`-component of the root Fox vector of `u` (times the right factor
`∂(ψ (of x))/∂x`), so the singleton statement transports backwards.  This is
`Work.ORLyndon.annAt_of_jacobian_zero` with the Jacobian hypothesis discharged by
`Work.ORLyndon.foxD_eq_zero_of_notMem_relatorLetters`. -/
theorem annAt_singleton_of_clean_lift (ψ : FreeGroup α →* FreeGroup α)
    (hι : Function.Injective ψ) (hσ : Function.Surjective ψ) (x : α)
    (hJ : ∀ q : α, q ≠ x → x ∉ Work.OROneRel.relatorLetters (ψ (FreeGroup.of q)))
    (u : FreeGroup α) (l : ℕ) :
    annAt K ((ψ u) ^ l) (ψ u) {x} → annAt K (u ^ l) u {x} :=
  annAt_of_jacobian_zero ψ hι hσ u l x fun q hq =>
    foxD_eq_zero_of_notMem_relatorLetters (K := K) x (ψ (FreeGroup.of q)) (hJ q hq)

/-- **The clean-shortening reduction.**  If every cyclically reduced root which is not a proper
power admits, at every one of its letters `x`, a *clean shortening* -- a bijective `ψ` with
`ψ (of q)` avoiding `x` for `q ≠ x`, `ψ u` still cyclically reduced, not a proper power, still
mentioning `x`, and `relatorNorm (ψ u) < relatorNorm u` -- then the singleton `annAt` statements hold
for **every** such root (not merely for the Case-2 ones), by strong induction on `relatorNorm`. -/
theorem annAt_singletons_of_clean_shortening
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A),
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        ∃ ψ : FreeGroup A →* FreeGroup A,
          Function.Injective ψ ∧ Function.Surjective ψ ∧
          (∀ q : A, q ≠ x → x ∉ Work.OROneRel.relatorLetters (ψ (FreeGroup.of q))) ∧
          Work.OROneRel.relatorNorm (ψ v) < Work.OROneRel.relatorNorm v ∧
          Work.OROneRel.IsCyclicallyReducedRelator (ψ v) ∧ ¬ Work.OROneRel.IsProperPower (ψ v) ∧
          x ∈ Work.OROneRel.relatorLetters (ψ v)) :
    ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ),
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      ∀ x ∈ Work.OROneRel.relatorLetters v, annAt K (v ^ l) v {x} := by
  have key : ∀ N {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ),
      Work.OROneRel.relatorNorm v < N →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      ∀ x ∈ Work.OROneRel.relatorLetters v, annAt K (v ^ l) v {x} := by
    intro N
    induction N with
    | zero =>
        intro A _ v l hN _ _ x _
        exact absurd hN (Nat.not_lt_zero _)
    | succ N ih =>
        intro A _ v l hN hpp hcyc x hx
        obtain ⟨ψ, hι, hσ, hJ, hlt, hcyc', hpp', hxψ⟩ := h v hpp hcyc x hx
        exact annAt_singleton_of_clean_lift (K := K) ψ hι hσ x hJ v l
          (ih (ψ v) l (by omega) hpp' hcyc' x hxψ)
  intro A _ v l hpp hcyc x hx
  exact key (Work.OROneRel.relatorNorm v + 1) v l (Nat.lt_succ_self _) hpp hcyc x hx

/-- **`EpsNeZeroDescent` from the clean-shortening hypothesis.**  The hypothesis of
`annAt_singletons_of_clean_shortening` implies every Case-2 root satisfies the singleton `annAt`
statements, hence -- by the trivial-witness Magnus descent
(`Work.ORLyndon.epsNeZeroDescent_of_singleton_annAt`) and the order statement
(`Work.ORLyndon.orderOf_presentRho_eps_ne_zero`) -- the full target. -/
theorem epsNeZeroDescent_of_clean_shortening
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A),
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        ∃ ψ : FreeGroup A →* FreeGroup A,
          Function.Injective ψ ∧ Function.Surjective ψ ∧
          (∀ q : A, q ≠ x → x ∉ Work.OROneRel.relatorLetters (ψ (FreeGroup.of q))) ∧
          Work.OROneRel.relatorNorm (ψ v) < Work.OROneRel.relatorNorm v ∧
          Work.OROneRel.IsCyclicallyReducedRelator (ψ v) ∧ ¬ Work.OROneRel.IsProperPower (ψ v) ∧
          x ∈ Work.OROneRel.relatorLetters (ψ v)) :
    EpsNeZeroDescent.{u, v} K :=
  epsNeZeroDescent_of_singleton_annAt (K := K) fun {A : Type u} _ v l _ hpp hcyc _ _ x hx =>
    annAt_singletons_of_clean_shortening (K := K) h (v := v) (l := l) hpp hcyc x hx

/-- **The geometric (case G) residual, pinned to its order statement.**  For a root of the shape
`u = t · (x W)^k` with `x` not occurring in `t` or `W` -- i.e. a root whose `x`-gaps are all equal --
the `x`-component of the root Fox vector is the geometric series `of t · Σ_{i<k} of (xW)^i`
(`Work.ORLyndon.rootVec_geom_factorisation`) and the singleton statement follows as soon as the
`k`-th power `(xW)^k` has infinite order in `⟨α | u^l⟩` (`Work.ORLyndon.annAt_of_geometric`).

In the residual setting the element `(xW)^k` equals `t⁻¹ · ū` and lies in the kernel of *every*
character `⟨α | u^l⟩ →* ℤ` (`eps t = 0` and `ū` is torsion), so this order statement is exactly the
input that only a torsion theorem can supply (notes §19.2). -/
theorem annAt_of_geometric_residual {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (x : α) (t W : FreeGroup α) (ht : x ∉ Work.OROneRel.relatorLetters t)
    (hW : x ∉ Work.OROneRel.relatorLetters W) (k l : ℕ) (hk : 1 ≤ k)
    (hord : orderOf
      ((presentRho ((t * (FreeGroup.of x * W) ^ k) ^ l) (FreeGroup.of x * W)) ^ k) = 0) :
    annAt K ((t * (FreeGroup.of x * W) ^ k) ^ l) (t * (FreeGroup.of x * W) ^ k) {x} :=
  annAt_of_geometric (K := K) (u := t * (FreeGroup.of x * W) ^ k) (l := l) (x := x) k
    (presentRho ((t * (FreeGroup.of x * W) ^ k) ^ l) t)
    (presentRho ((t * (FreeGroup.of x * W) ^ k) ^ l) (FreeGroup.of x * W))
    (rootVec_geom_factorisation x t W ht hW k l hk) hord

/-- **The clean transfer, with the Nielsen transformation exhibited by its two sides.**  Combines
`Work.ORLyndon.clean_lift_bijective` (the extension of an automorphism of the free factor `F(α∖{x})`
by `x ↦ x` is a bijective Nielsen transformation whose `x`-Jacobian is `δ_{q,x}`) with
`annAt_singleton_of_clean_lift`.  This is the shape in which the clean-shortening route (§19 of the
notes) consumes an explicit automorphism of `F(α ∖ {x})`. -/
theorem annAt_singleton_of_clean_automorphism (x : α) (g g' : α → FreeGroup α)
    (hgx : g x = FreeGroup.of x) (hg'x : g' x = FreeGroup.of x)
    (hgE : ∀ y : α, y ≠ x → x ∉ Work.OROneRel.relatorLetters (g y))
    (hinv1 : ∀ y : α, y ≠ x → FreeGroup.lift g' (g y) = FreeGroup.of y)
    (hinv2 : ∀ y : α, y ≠ x → FreeGroup.lift g (g' y) = FreeGroup.of y)
    (u : FreeGroup α) (l : ℕ) :
    annAt K (((FreeGroup.lift g) u) ^ l) ((FreeGroup.lift g) u) {x} →
      annAt K (u ^ l) u {x} := by
  obtain ⟨hι, hσ, _⟩ := clean_lift_bijective (K := K) x g g' hgx hg'x hgE hinv1 hinv2
  exact annAt_singleton_of_clean_lift (FreeGroup.lift g) hι hσ x
    (fun q hq => by rw [FreeGroup.lift_apply_of]; exact hgE q hq) u l

/-! ## The geometric case of the residual is closed

This block proves the *geometric* sub-case of the residual (case (G) of `NOTES_epsNeZeroDescent_level.md`
§19.2) outright.  The residual of the singleton statement `annAt K (u ^ l) u {x}` is the situation in
which every occurrence of `x^{±1}` in `u` has the same sign, say `k ≥ 2` of them, and the blocks
`B_1, …, B_k` between consecutive occurrences (words in the other letters) all have the *same* exponent
vector.  Writing `u = t · (x W_1) ⋯ (x W_k)` and `h_j := x W_j`, the occurrence terms of `∂u/∂x` are
the prefixes `P_j = t h_1 ⋯ h_j`, whose exponent vectors are `j · vec u / k`; so the residual condition
is exactly `vec W_j = vec u / k` for every `j` and `vec t = 0`.

The **geometric** sub-case is `W_1 = ⋯ = W_k =: W`: then `u = t · (x W)^k` and the component is the
finite geometric series `of t · Σ_{i<k} of (xW)^i` (`Work.ORLyndon.rootVec_geom_factorisation`), so
`annAt` follows from `orderOf ((xW)^k) = 0` (`Work.ORLyndon.annAt_of_geometric`).

That order statement is now *proved*, by the following observation.  In the torsion-free quotient
`⟨α | u⟩` the relation reads `h̄^k = t̄⁻¹`, so `h̄` has infinite order as soon as `t̄` does; and `t̄`
does: `t` is a word in the other letters, `t ≠ 1` (else `u = (xW)^k` is a proper power), so `t` lies
in the Magnus subgroup at `x`, which is free by the Freiheitssatz.  Finally infinite order ascends from
`⟨α | u⟩` to `⟨α | u^l⟩` along the quotient `⟨α | u^l⟩ ↠ ⟨α | u⟩` (which exists since
`⟨⟨u ^ l⟩⟩ ≤ ⟨⟨u⟩⟩`).  Consequently `orderOf ((x W)^k) = 0` — note that `h` itself, not only `h^k`, is
of infinite order, and an element of infinite order has all its non-zero powers of infinite order.

The key formal tool is the importable `Work.ORLyndon.exists_hom_oneRelatorGroup_pow`
(the quotient `⟨α | u ^ l⟩ →* ⟨α | u⟩`) together with the Freiheitssatz order certificate
`Work.ORLyndon.orderOf_presentedGroupMap_misses_eq_zero`. -/

/-- **The Magnus preimage of a word avoiding a letter.**  Every element of `F(α)` in which the
generator `x` does not occur is the image of an element of the free group on the other generators
under the Magnus inclusion `magIncl x`.  (Stated without a `DecidableEq` hypothesis so that the
`Classical` decidability instance used inside `Work.OROneRel.relatorLetters` is the one at which
`FreeGroup.toWord` is evaluated.) -/
theorem exists_magIncl_eq_of_notMem {β : Type u} (x : β) {t : FreeGroup β}
    (ht : x ∉ Work.OROneRel.relatorLetters t) :
    ∃ T : FreeGroup {z : β // z ≠ x}, magIncl x T = t := by
  classical
  obtain ⟨P, hP⟩ := magIncl_exists_eq_mk x (FreeGroup.toWord t) (by
    rw [Work.OROneRel.relatorLetters] at ht
    intro p hp hpx
    exact ht ⟨p.2, by rw [← hpx]; simpa using hp⟩)
  exact ⟨P, by rw [hP, FreeGroup.mk_toWord]⟩

/-- **Infinite order ascends from the base group.**  The quotient `⟨α | u ^ l⟩ ↠ ⟨α | u⟩` (which
exists because `⟨⟨u ^ l⟩⟩ ≤ ⟨⟨u⟩⟩`) pulls infinite order back: if the class of `w` in the
torsion-free base `⟨α | u⟩` has infinite order, so does its class in `⟨α | u ^ l⟩`.  This is the
elementary half of the order certificates used below. -/
theorem orderOf_presentRho_pow_eq_zero {u : FreeGroup α} {l : ℕ} {w : FreeGroup α}
    (hw : orderOf (presentRho u w) = 0) : orderOf (presentRho (u ^ l) w) = 0 := by
  obtain ⟨ψ, hψ⟩ := exists_hom_oneRelatorGroup_pow u l
  exact orderOf_eq_zero_of_map_eq_zero ψ (by rw [hψ]; exact hw)

/-- **The Freiheitssatz order certificate at the root presentation.**  A nontrivial word `t` in the
letters other than `x` has class of infinite order in `⟨α | u ^ l⟩`, for every `l`, as soon as `x` is
a letter of the cyclically reduced root `u`.  (The class lies in the Magnus subgroup at `x`, which the
Freiheitssatz identifies with the free group on the other generators.) -/
theorem orderOf_presentRho_magnus_eq_zero {u : FreeGroup α} {x : α}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hx : x ∈ Work.OROneRel.relatorLetters u) {t : FreeGroup α}
    (ht : x ∉ Work.OROneRel.relatorLetters t) (ht1 : t ≠ 1) (l : ℕ) :
    orderOf (presentRho (u ^ l) t) = 0 := by
  refine orderOf_presentRho_pow_eq_zero (l := l) ?_
  obtain ⟨T, hT⟩ := exists_magIncl_eq_of_notMem (x := x) ht
  have hT1 : T ≠ 1 := by intro h; rw [h, map_one] at hT; exact ht1 hT.symm
  rw [← hT, presentRho_magIncl_eq_presentedGroupMap]
  exact orderOf_presentedGroupMap_misses_eq_zero (u := u) hcyc (y := x) hx hT1

/-- **The geometric case of the residual, with no hypothesis left.**  For a root of the shape
`u = t · (x W)^k` with `x` occurring in neither `t` nor `W`, `t ≠ 1`, `k ≥ 1`, `u` cyclically reduced
and `x` a letter of `u`, the singleton statement `annAt K (u ^ l) u {x}` holds for *every* `l` and
every field `K`.

The mathematical content is the order certificate: `(xW)^k` has infinite order in `⟨α | u ^ l⟩`,
because its image `t̄⁻¹` in the torsion-free quotient `⟨α | u⟩` does (the Freiheitssatz applied to the
Magnus element `t`), and infinite order ascends along `⟨α | u ^ l⟩ ↠ ⟨α | u⟩`. -/
theorem annAt_of_geometric_of_ne_one
    (x : α) (t W : FreeGroup α) (ht : x ∉ Work.OROneRel.relatorLetters t)
    (hW : x ∉ Work.OROneRel.relatorLetters W) (ht1 : t ≠ 1)
    (k l : ℕ) (hk : 1 ≤ k)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (t * (FreeGroup.of x * W) ^ k))
    (hx : x ∈ Work.OROneRel.relatorLetters (t * (FreeGroup.of x * W) ^ k)) :
    annAt K ((t * (FreeGroup.of x * W) ^ k) ^ l) (t * (FreeGroup.of x * W) ^ k) {x} := by
  classical
  set u0 : FreeGroup α := t * (FreeGroup.of x * W) ^ k with hu
  have hcyc' : Work.OROneRel.IsCyclicallyReducedRelator u0 := by rw [hu]; exact hcyc
  have hx' : x ∈ Work.OROneRel.relatorLetters u0 := by rw [hu]; exact hx
  have hord : orderOf (((presentRho (u0 ^ l)) (FreeGroup.of x * W)) ^ k) = 0 := by
    obtain ⟨ψ, hψ⟩ := exists_hom_oneRelatorGroup_pow u0 l
    refine orderOf_eq_zero_of_map_eq_zero ψ ?_
    rw [map_pow, hψ]
    have h1 : (FreeGroup.of x * W) ^ k = t⁻¹ * u0 := by
      rw [hu]; group
    have h2 : (presentRho u0 (FreeGroup.of x * W)) ^ k = (presentRho u0 t)⁻¹ := by
      rw [← map_pow, h1, map_mul, map_inv, presentRho_relator, mul_one]
    rw [h2, orderOf_inv]
    obtain ⟨T, hT⟩ := exists_magIncl_eq_of_notMem (x := x) ht
    have hT1 : T ≠ 1 := by
      intro h; rw [h, map_one] at hT; exact ht1 hT.symm
    rw [← hT, presentRho_magIncl_eq_presentedGroupMap]
    exact orderOf_presentedGroupMap_misses_eq_zero (u := u0) hcyc' (y := x) hx' hT1
  rw [hu]
  exact annAt_of_geometric_residual (K := K) x t W ht hW k l hk hord

/-- **The residual after the geometric case.**  `EpsNeZeroDescent K` follows from the singleton
`annAt` statements for the roots which are *not* of the geometric shape `t · (x W)^k` (`t ≠ 1` and `x`
occurring in neither `t` nor `W`) at the letter `x` in question.  In the residual setting -- every
occurrence of `x` of the same sign and all blocks of equal exponent vector -- the remaining case is the
*aperiodic* one, in which two blocks differ (`NOTES_epsNeZeroDescent_level.md` §19.2, §19.5). -/
theorem epsNeZeroDescent_of_not_geometric
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ) (x : A), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ y ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps y v ≠ 0) →
      x ∈ Work.OROneRel.relatorLetters v →
      (∀ (t W : FreeGroup A) (k : ℕ), t ≠ 1 → x ∉ Work.OROneRel.relatorLetters t →
        x ∉ Work.OROneRel.relatorLetters W → 1 ≤ k →
        v ≠ t * (FreeGroup.of x * W) ^ k) →
      annAt K (v ^ l) v {x}) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt (K := K) ?_
  intro A _ v l hl hpp hcyc hn hbad x hx
  by_cases hg : ∃ (t W : FreeGroup A) (k : ℕ), t ≠ 1 ∧ x ∉ Work.OROneRel.relatorLetters t ∧
      x ∉ Work.OROneRel.relatorLetters W ∧ 1 ≤ k ∧ v = t * (FreeGroup.of x * W) ^ k
  · obtain ⟨t, W, k, ht1, ht, hW, hk, hv⟩ := hg
    subst hv
    exact annAt_of_geometric_of_ne_one x t W ht hW ht1 k l hk hcyc hx
  · refine h v l x hl hpp hcyc hn hbad hx ?_
    intro t W k ht1 ht hW hk heq
    exact hg ⟨t, W, k, ht1, ht, hW, hk, heq⟩

/-- **The `w`-power form of the residual.**  Suppose the root has the shape `u = t · w ^ r` with `x`
not occurring in `t`, `t ≠ 1`, `u` cyclically reduced and `x` a letter of `u`, and suppose the
`x`-component of the root Fox vector factors as

`(∂u/∂x) = of t̄ · (1 + of w̄ + ⋯ + of w̄ ^ (r-1)) · (∂w/∂x)`,

which is automatic when `x ∉ relatorLetters t` (`Work.ORLyndon.rootVec_pow_factorisation`).  If the
last factor `∂w/∂x` is a right non-zero-divisor of `K[⟨α | u ^ l⟩]`, then so is the component.

This is the framework behind the geometric case: there `w = of x * W` so that `∂w/∂x = 1` (a unit),
and `orderOf (w ^ r) = 0` follows from `w ^ r = t⁻¹ · u` together with the Freiheitssatz at `t`.  In
general one also needs the regularity of `∂w/∂x` — the case `w = x B x⁻¹ B`, where
`∂w/∂x = 1 - of (x B x⁻¹)`, cuts out the alternating mixed-sign residual instances
(`NOTES_epsNeZeroDescent_level.md` §20.3–20.4). -/
theorem annAt_of_pow_factorisation {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {t w : FreeGroup α} {x : α} {r l : ℕ}
    (hfac : rootVec K ((t * w ^ r) ^ l) (t * w ^ r) x =
      MonoidAlgebra.of K (OneRelatorGroup ((t * w ^ r) ^ l))
          (presentRho ((t * w ^ r) ^ l) t) *
        (∑ i ∈ Finset.range r,
          (MonoidAlgebra.of K (OneRelatorGroup ((t * w ^ r) ^ l))
            (presentRho ((t * w ^ r) ^ l) w)) ^ i) *
        (presentAlg K ((t * w ^ r) ^ l) (foxD (K := K) x w)))
    (ht : x ∉ Work.OROneRel.relatorLetters t)
    (ht1 : t ≠ 1)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (t * w ^ r))
    (hx : x ∈ Work.OROneRel.relatorLetters (t * w ^ r))
    (hβ : ∀ c : MonoidAlgebra K (OneRelatorGroup ((t * w ^ r) ^ l)),
      c * presentAlg K ((t * w ^ r) ^ l) (foxD (K := K) x w) = 0 → c = 0) :
    annAt K ((t * w ^ r) ^ l) (t * w ^ r) {x} := by
  classical
  set u : FreeGroup α := t * w ^ r with hu
  have hr : r ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    rw [hu] at hx
    exact ht hx
  have hpow : w ^ r = t⁻¹ * u := by rw [hu]; group
  have htM : orderOf (presentRho u t) = 0 := by
    obtain ⟨T, hT⟩ := exists_magIncl_eq_of_notMem (x := x) ht
    have hT1 : T ≠ 1 := by intro hh; rw [hh, map_one] at hT; exact ht1 hT.symm
    rw [← hT, presentRho_magIncl_eq_presentedGroupMap]
    exact orderOf_presentedGroupMap_misses_eq_zero (u := u) hcyc (y := x) hx hT1
  have hwu : orderOf (presentRho u w) = 0 := by
    refine orderOf_eq_zero_of_pow_eq_zero (n := r) hr ?_
    have h1 : (presentRho u w) ^ r = (presentRho u t)⁻¹ := by
      rw [← map_pow, hpow, map_mul, map_inv, presentRho_relator, mul_one]
    rw [h1, orderOf_inv]
    exact htM
  have hw : orderOf (presentRho (u ^ l) w) = 0 := by
    obtain ⟨ψ, hψ⟩ := exists_hom_oneRelatorGroup_pow u l
    exact orderOf_eq_zero_of_map_eq_zero ψ (by rw [hψ]; exact hwu)
  have hNr : orderOf ((presentRho (u ^ l) w) ^ r) = 0 := by
    rw [orderOf_eq_zero_iff'] at hw ⊢
    intro n hn hpow'
    refine hw (r * n) (Nat.mul_pos (Nat.pos_of_ne_zero hr) hn) ?_
    rw [← pow_mul] at hpow'
    exact hpow'
  have hN := geomSum_regular (K := K) (G := OneRelatorGroup (u ^ l))
    (h := presentRho (u ^ l) w) r hNr
  have key : ∀ c : MonoidAlgebra K (OneRelatorGroup (u ^ l)),
      c * (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (presentRho (u ^ l) t) *
        (∑ i ∈ Finset.range r,
          (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (presentRho (u ^ l) w)) ^ i) *
        presentAlg K (u ^ l) (foxD (K := K) x w)) = 0 → c = 0 := by
    intro c hc
    have h2 : (c * MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (presentRho (u ^ l) t)) *
        ((∑ i ∈ Finset.range r,
            (MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (presentRho (u ^ l) w)) ^ i) *
          presentAlg K (u ^ l) (foxD (K := K) x w)) = 0 := by
      simpa only [mul_assoc] using hc
    have h4 : c * MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) (presentRho (u ^ l) t) = 0 :=
      regular_mul hN hβ _ h2
    have h5 := congrArg
      (fun z => z * MonoidAlgebra.of K (OneRelatorGroup (u ^ l)) ((presentRho (u ^ l) t)⁻¹)) h4
    rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, zero_mul] at h5
  rw [hu]
  intro b hb
  exact key b (by rw [← hfac]; exact hb x (Set.mem_singleton x))

/-- **The level method on the occurrence subgroup.**  The character separating the occurrence terms
of `∂u/∂x` need only be defined on the subgroup `H` generated by them — not on all of
`⟨α | r⟩`.  In the residual setting this is essential: *every* character `⟨α | u ^ l⟩ →* ℤ` kills the
occurrence terms (a homomorphism to a torsion-free group must kill the root `ū`, and the terms differ
by rational multiples of `eps(u)`), so only a character of `H` — equivalently a proof that the ratio
`h₁ = xB₁` of two consecutive occurrence terms is *not torsion* in `H^{ab}` — can separate them
(`NOTES_epsNeZeroDescent_level.md` §16, §20.3–20.4).

The transport is the free `K[H]`-module structure of `K[⟨α | r⟩]`
(`Work.ORLyndon.signedSum_regular_of_subgroup`, `Work.ORLyndon.base_regularity_transport_of_le`). -/
theorem annAt_of_occTerm_subgroupChar {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {r u : FreeGroup α} {x : α}
    (H : Subgroup (OneRelatorGroup r))
    (hH : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      presentRho r (occTerm x (Work.OROneRel.wordOf u) i) ∈ H)
    (χ : H →* Multiplicative ℤ) (i₀ : Fin (Work.OROneRel.wordOf u).length)
    (hε : occEps K x (Work.OROneRel.wordOf u) i₀ ≠ 0)
    (hle : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      occEps K x (Work.OROneRel.wordOf u) i ≠ 0 →
      Multiplicative.toAdd (χ ⟨presentRho r (occTerm x (Work.OROneRel.wordOf u) i), hH i⟩) ≤
        Multiplicative.toAdd (χ ⟨presentRho r (occTerm x (Work.OROneRel.wordOf u) i₀), hH i₀⟩))
    (huniq : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      occEps K x (Work.OROneRel.wordOf u) i ≠ 0 →
      Multiplicative.toAdd (χ ⟨presentRho r (occTerm x (Work.OROneRel.wordOf u) i), hH i⟩) =
        Multiplicative.toAdd (χ ⟨presentRho r (occTerm x (Work.OROneRel.wordOf u) i₀), hH i₀⟩) →
      i = i₀) :
    annAt K r u {x} := by
  classical
  intro b hb
  have hb0 : b * rootVec K r u x = 0 := hb x (Set.mem_singleton x)
  set s : Finset (Fin (Work.OROneRel.wordOf u).length) :=
    Finset.univ.filter (fun i => occEps K x (Work.OROneRel.wordOf u) i ≠ 0) with hs
  have hmem : ∀ i : Fin (Work.OROneRel.wordOf u).length,
      i ∈ s ↔ occEps K x (Work.OROneRel.wordOf u) i ≠ 0 := by
    intro i
    rw [hs]
    simp
  have hsplit : (∑ i : Fin (Work.OROneRel.wordOf u).length,
        occEps K x (Work.OROneRel.wordOf u) i •
          MonoidAlgebra.of K (OneRelatorGroup r)
            (presentRho r (occTerm x (Work.OROneRel.wordOf u) i)))
      = ∑ i ∈ s,
        occEps K x (Work.OROneRel.wordOf u) i •
          MonoidAlgebra.of K (OneRelatorGroup r)
            (presentRho r (occTerm x (Work.OROneRel.wordOf u) i)) := by
    rw [hs, ← Finset.sum_subset (show Finset.univ.filter
        (fun i : Fin (Work.OROneRel.wordOf u).length =>
          occEps K x (Work.OROneRel.wordOf u) i ≠ 0) ⊆ Finset.univ
        from fun i _ => Finset.mem_univ i)]
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    rw [hi, zero_smul]
  rw [rootVec_eq_sum_occEps (K := K) (r := r) (u := u) x, hsplit] at hb0
  refine signedSum_regular_of_subgroup (K := K) (s := s)
    (g := fun i => presentRho r (occTerm x (Work.OROneRel.wordOf u) i))
    (ε := fun i => occEps K x (Work.OROneRel.wordOf u) i)
    (H := H) (hH := hH) (χ := χ) (i₀ := i₀)
    (hi₀ := (hmem i₀).mpr hε) (hε := hε)
    (hle := fun i hi => hle i ((hmem i).mp hi))
    (huniq := fun i hi => huniq i ((hmem i).mp hi)) b hb0

/-- **The residual in subgroup-character form** — the sharpest known reduction of
`EpsNeZeroDescent`.  It suffices that for every Case-2 root `v`, every `l ≥ 1` and every letter
`x` of `v` there is a subgroup `H ≤ ⟨α | v ^ l⟩` containing *all* the occurrence terms of `∂v/∂x`
together with a character `χ : H →* Multiplicative ℤ` having a unique strict maximiser among them.

By the analysis of `NOTES_epsNeZeroDescent_level.md` (§16, §20.9) this hypothesis is *exactly* the
residual, and it cannot be weakened to an ambient character: in the residual case the occurrence
terms all lie in one class modulo `ℚ · eps(v)`, so every homomorphism `⟨α | v ^ l⟩ →* ℤ` (which must
kill the root `ū`) takes the same value on all of them.  The subgroup character exists precisely when
the classes of the occurrence terms in `H ^ ab` are distinct modulo the torsion subgroup of `H ^ ab`
— i.e. when `H ^ ab` separates them; the exposed-vertex argument of §20.9 shows that any two terms
that are distinct modulo torsion are automatically separated by some character. -/
theorem epsNeZeroDescent_of_subgroupChar {K : Type v} [Field K]
    (h : ∀ {A : Type u} [DecidableEq A] (v : FreeGroup A) (l : ℕ), 1 ≤ l →
      ¬ Work.OROneRel.IsProperPower v → Work.OROneRel.IsCyclicallyReducedRelator v →
      2 ≤ Work.OROneRel.relatorNorm v →
      (∀ y ∈ Work.OROneRel.relatorLetters v, Work.OROneRel.eps y v ≠ 0) →
      ∀ x ∈ Work.OROneRel.relatorLetters v,
        ∃ (H : Subgroup (OneRelatorGroup (v ^ l)))
          (hH : ∀ i : Fin (Work.OROneRel.wordOf v).length,
            presentRho (v ^ l) (occTerm x (Work.OROneRel.wordOf v) i) ∈ H)
          (χ : H →* Multiplicative ℤ) (i₀ : Fin (Work.OROneRel.wordOf v).length),
          occEps K x (Work.OROneRel.wordOf v) i₀ ≠ 0 ∧
          (∀ i : Fin (Work.OROneRel.wordOf v).length,
            occEps K x (Work.OROneRel.wordOf v) i ≠ 0 →
            Multiplicative.toAdd
              (χ ⟨presentRho (v ^ l) (occTerm x (Work.OROneRel.wordOf v) i), hH i⟩) ≤
            Multiplicative.toAdd
              (χ ⟨presentRho (v ^ l) (occTerm x (Work.OROneRel.wordOf v) i₀), hH i₀⟩)) ∧
          (∀ i : Fin (Work.OROneRel.wordOf v).length,
            occEps K x (Work.OROneRel.wordOf v) i ≠ 0 →
            Multiplicative.toAdd
              (χ ⟨presentRho (v ^ l) (occTerm x (Work.OROneRel.wordOf v) i), hH i⟩) =
            Multiplicative.toAdd
              (χ ⟨presentRho (v ^ l) (occTerm x (Work.OROneRel.wordOf v) i₀), hH i₀⟩) →
            i = i₀)) :
    EpsNeZeroDescent.{u, v} K := by
  refine epsNeZeroDescent_of_singleton_annAt (K := K) ?_
  intro A _ v l hl hpp hcyc hn hbad x hx
  obtain ⟨H, hH, χ, i₀, hε, hle, huniq⟩ := h v l hl hpp hcyc hn hbad x hx
  exact annAt_of_occTerm_subgroupChar H hH χ i₀ hε hle huniq

/-! ## The Nielsen--Magnus (transvection) reduction of the residual

Every earlier route in this file tried to make the *level method* see the occurrence terms of
`∂u/∂x` — which is impossible in the residual, where all of them are congruent modulo `ℚ · eps u`.

The two lemmas below implement a completely different and much more elementary route.  Instead of
separating the terms, one *shortens the root by a Nielsen transformation*:

* `annAt_of_jacobian_zero_set` (the set form of `Work.ORLyndon.annAt_of_jacobian_zero`): if a
  bijective endomorphism `ψ` of the free group has Jacobian vanishing off the diagonal at every
  letter of `E`, then `annAt` at `E` for the root `ψ u` implies `annAt` at `E` for `u`;
* `annAt_of_epsZeroImage` composes this with the *exponent-sum-zero Magnus step*
  (`Work.ORLyndon.annAt_of_epsZero_strong`): if the Nielsen transform `ψ u` has vanishing `t`-exponent
  sum, then the base `annAt` of the Magnus rewriting of `ψ u` transfers first to `ψ u` and then back
  to `u`.

The point is that both transfers are *implications*: they need no knowledge of the base statement.
Consequently the composite is a valid `MagnusDescent` witness, with the witness root
`rootW t (ψ u) l` — which is markedly shorter than `ψ u` (`relatorNorm_rootW_le_nonTLetters`), hence
also shorter than `u` whenever the number of non-`t` letters of `ψ u` is smaller than
`relatorNorm u`. The concrete `ψ` (a single transvection `y ↦ t ^ (-m) * y`) and the verification of
the remaining combinatorial hypotheses are the subject of
`NOTES_epsNeZeroDescent_level.md` §21. -/

/-- **The set form of the componentwise Nielsen transfer.**  If `ψ` is a bijective endomorphism of
the free group whose Fox Jacobian vanishes off the diagonal at every letter of `E`, then the
`annAt` statement for the root `ψ u` implies the `annAt` statement for `u`, at the *same* set `E`. -/
theorem annAt_of_jacobian_zero_set {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (ψ : FreeGroup α →* FreeGroup α) (hι : Function.Injective ψ) (hσ : Function.Surjective ψ)
    (u : FreeGroup α) (l : ℕ) (E : Set α)
    (hJ : ∀ x ∈ E, ∀ q : α, q ≠ x → foxD (K := K) x (ψ (FreeGroup.of q)) = 0) :
    annAt K ((ψ u) ^ l) (ψ u) E → annAt K (u ^ l) u E := by
  intro h b hb
  set B := MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) b with hB
  have hzero : ∀ x ∈ E, B * rootVec K ((ψ u) ^ l) (ψ u) x = 0 := by
    intro x hx
    rw [rootVec_apply, foxD_comp_of_jacobian_zero ψ u x (hJ x hx), map_mul,
      ← mapDomainRingHom_psiBar_presentAlg ψ u l (foxD (K := K) x u),
      ← mul_assoc, ← map_mul, ← rootVec_apply]
    rw [hb x hx, map_zero, zero_mul]
  have hB0 : B = 0 := h B hzero
  have h0 : MonoidAlgebra.mapDomainRingHom K (psiBar ψ u l) b = 0 := by
    rw [← hB]; exact hB0
  exact MonoidAlgebra.mapDomain_injective (psiBar_injective ψ hι hσ u l)
    (by rw [MonoidAlgebra.mapDomain_zero]
        simpa only [MonoidAlgebra.mapDomainRingHom_apply] using h0)

/-- **The Nielsen--Magnus transfer.**  If the Nielsen transform `ψ u` of the root `u` has vanishing
`t`-exponent sum (`he`), is cyclically reduced (`hcyc`) and not a proper power (`hpp`), and if the
Jacobian of `ψ` vanishes off the diagonal at every letter `≠ t`, then an `annAt` statement at the
Magnus base of `ψ u` transfers to `annAt K (u ^ l) u (Subtype.val '' Em)`.

Both halves are *implications*, so no hypothesis on the base is consumed here. -/
theorem annAt_of_epsZeroImage {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (ψ : FreeGroup α →* FreeGroup α) (hι : Function.Injective ψ) (hσ : Function.Surjective ψ)
    (u : FreeGroup α) (l : ℕ) (t : α) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower (ψ u))
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (ψ u))
    (ht : t ∈ Work.OROneRel.relatorLetters (ψ u))
    (he : Work.OROneRel.eps t (ψ u) = 0)
    (hJ : ∀ x : α, x ≠ t → ∀ q : α, q ≠ x →
      foxD (K := K) x (ψ (FreeGroup.of q)) = 0)
    (Em : Set {x : α // x ≠ t}) (hEm : Em.Nonempty)
    (hb : annAt K (Work.OROneRel.mmW t ((ψ u) ^ l))
      (Work.OROneRel.rootW t (ψ u) l hcyc he hl)
      ((fun x : {x : α // x ≠ t} => Work.ORLyndon.mmTopSym t (ψ u) l x.1 x.2) '' Em)) :
    annAt K (u ^ l) u (Subtype.val '' Em) :=
  annAt_of_jacobian_zero_set ψ hι hσ u l (Subtype.val '' Em)
    (fun x hx q hq => by
      obtain ⟨y, _, rfl⟩ := hx
      exact hJ y.1 y.2 q hq)
    (annAt_of_epsZero_strong t (ψ u) l hl hpp hcyc ht he Em hEm hb)

/-- **`MagnusDescent` from a transvection image of the root.**  Given a bijective `ψ` whose Jacobian
vanishes off the diagonal at every letter `≠ t`, with `ψ u` cyclically reduced, not a proper power,
`t ∈ relatorLetters (ψ u)`, `eps t (ψ u) = 0`, and with the Magnus root of `ψ u` shorter than `u`,
one obtains `MagnusDescent K u l S` for every `S` meeting the complement of `{t}`.

This is the form in which the transvection route enters the descent: the witness root is
`rootW t (ψ u) l` in the decorated alphabet `mmBeta t (ψ u)`, and its `S'` is the set of top
decorated symbols of `S \ {t}`. -/
theorem magnusDescent_of_epsZeroImage {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    (ψ : FreeGroup α →* FreeGroup α) (hι : Function.Injective ψ) (hσ : Function.Surjective ψ)
    (u : FreeGroup α) (l : ℕ) (t : α) (hl : 1 ≤ l)
    (hpp : ¬ Work.OROneRel.IsProperPower (ψ u))
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (ψ u))
    (ht : t ∈ Work.OROneRel.relatorLetters (ψ u))
    (he : Work.OROneRel.eps t (ψ u) = 0)
    (hJ : ∀ x : α, x ≠ t → ∀ q : α, q ≠ x →
      foxD (K := K) x (ψ (FreeGroup.of q)) = 0)
    (hnorm : Work.OROneRel.relatorNorm (Work.OROneRel.rootW t (ψ u) l hcyc he hl)
      < Work.OROneRel.relatorNorm u)
    (S : Set α) (hS : ∃ x ∈ S, x ≠ t ∧ x ∈ Work.OROneRel.relatorLetters (ψ u)) :
    MagnusDescent K u l S := by
  classical
  refine ⟨Work.OROneRel.mmBeta t ((ψ u) ^ l), Work.OROneRel.rootW t (ψ u) l hcyc he hl,
    (Work.OROneRel.rootW t (ψ u) l hcyc he hl) ^ l,
    (fun x : {y : α // y ≠ t} => Work.ORLyndon.mmTopSym t (ψ u) l x.1 x.2) ''
      {y : {y : α // y ≠ t} | y.1 ∈ S ∧ y.1 ∈ Work.OROneRel.relatorLetters (ψ u)},
    Work.OROneRel.not_isProperPower_rootW t (ψ u) l hpp hcyc he hl, rfl,
    isCyclicallyReducedRelator_rootW t (ψ u) l hcyc he hl, hnorm, ?_, ?_, ?_⟩
  · obtain ⟨x, hxS, hxt, hxr⟩ := hS
    refine ⟨Work.ORLyndon.mmTopSym t (ψ u) l x hxt, ?_⟩
    exact ⟨(⟨x, hxt⟩ : {y : α // y ≠ t}), ⟨hxS, hxr⟩, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    exact Work.ORLyndon.mmTopSym_mem_relatorLetters t (ψ u) l hcyc he hl x.1 x.2 hx.2
  · intro hbase
    have hbase' := hbase
    rw [Work.OROneRel.rootW_pow t (ψ u) l hcyc he hl] at hbase'
    refine annAt_mono (K := K) (r := u ^ l) (u := u) (E := Subtype.val ''
        {y : {y : α // y ≠ t} | y.1 ∈ S ∧ y.1 ∈ Work.OROneRel.relatorLetters (ψ u)})
      (E' := S) ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      exact hx.1
    · obtain ⟨x, hxS, hxt, hxr⟩ := hS
      refine annAt_of_epsZeroImage (K := K) ψ hι hσ u l t hl hpp hcyc ht he hJ
        {y : {y : α // y ≠ t} | y.1 ∈ S ∧ y.1 ∈ Work.OROneRel.relatorLetters (ψ u)} ?_ hbase'
      refine ⟨(⟨x, hxt⟩ : {y : α // y ≠ t}), ?_⟩
      exact ⟨hxS, hxr⟩

/-- **`MagnusDescent` from a single elementary transvection.**  Let `ψ := transvectionLeft t y m`
(`y ↦ t ^ (-m) * y`, all other letters fixed), with `t ≠ y` and `m * eps y u = eps t u` (so that
`eps t (ψ u) = 0`, by `Work.ORLyndon.transvectionLeftProps`; the equivalent `he` is taken as a
hypothesis only so that `rootW` can be formed in the statement).  If moreover `ψ u` is cyclically
reduced and still contains the letter `t`, and if the Magnus root of `ψ u` is shorter than `u`, then
`MagnusDescent K u l S` holds for every `S` meeting the complement of `{t}`.

This is the transvection route of `NOTES_epsNeZeroDescent_level.md` §21 with all *algebraic* inputs
discharged: `¬IsProperPower (ψ u)` and the cleanliness of `ψ` off `t` come from
`Work.ORLyndon.transvectionLeftProps`, and the vanishing of `eps t (ψ u)` from the `eps`-shift
together with `hm`.  What remains is the combinatorial core of §21.4: the cyclicity of `ψ u`, the
membership `t ∈ relatorLetters (ψ u)`, and the numerical inequality `hnorm` (which follows from
`Work.OROneRel.nonTLetters t (ψ u) < Work.OROneRel.relatorNorm u`,
`Work.OROneRel.relatorNorm_rootW_le_nonTLetters` and
`Work.ORLyndon.nonTLetters_transvectionLeft_le`). -/
theorem magnusDescent_of_transvection {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {t y : α} (hyt : t ≠ y) (m : ℤ) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hppu : ¬ Work.OROneRel.IsProperPower u)
    (hm : m * Work.OROneRel.eps y u = Work.OROneRel.eps t u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (Work.ORLyndon.transvectionLeft t y m u))
    (he : Work.OROneRel.eps t (Work.ORLyndon.transvectionLeft t y m u) = 0)
    (ht : t ∈ Work.OROneRel.relatorLetters (Work.ORLyndon.transvectionLeft t y m u))
    (hnorm : Work.OROneRel.relatorNorm
      (Work.OROneRel.rootW t (Work.ORLyndon.transvectionLeft t y m u) l hcyc he hl)
      < Work.OROneRel.relatorNorm u)
    (S : Set α)
    (hS : ∃ x ∈ S, x ≠ t ∧
      x ∈ Work.OROneRel.relatorLetters (Work.ORLyndon.transvectionLeft t y m u)) :
    MagnusDescent K u l S :=
  magnusDescent_of_epsZeroImage (K := K) (Work.ORLyndon.transvectionLeft t y m)
    (transvectionLeftProps (K := K) hyt m).1 (transvectionLeftProps (K := K) hyt m).2.1
    u l t hl ((transvectionLeftProps (K := K) hyt m).2.2.2.2 u hppu) hcyc ht he
    (fun x hxt q hq => (transvectionLeftProps (K := K) hyt m).2.2.1 x hxt q hq) hnorm S hS

/-- **`MagnusDescent` from a transvection, with the numerical input discharged.**  This is
`Work.ORLyndon.magnusDescent_of_transvection` with the vanishing of `eps t (ψ u)` derived from
`m * eps y u = eps t u` and the `eps`-shift of `Work.ORLyndon.transvectionLeftProps`, and the norm
inequality derived from `Work.OROneRel.relatorNorm_rootW_le_nonTLetters`,
`Work.ORLyndon.nonTLetters_transvectionLeft_le_clean` and `Work.OROneRel.nonTLetters_lt_norm`:

`relatorNorm (rootW t (ψu) l hcyc he hl) ≤ nonTLetters t (ψu) ≤ nonTLetters t u < relatorNorm u`.

The **only** remaining hypotheses are the purely combinatorial ones (`ψ u` cyclically reduced and
`t ∈ relatorLetters (ψ u)`) together with `t ∈ relatorLetters u` (automatic when `t` is the first
letter of the word of `u`) and the requirement that `S` meets the complement of `{t}`. -/
theorem magnusDescent_of_transvectionData {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {t y : α} (hyt : t ≠ y) (m : ℤ) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hppu : ¬ Work.OROneRel.IsProperPower u)
    (hm : m * Work.OROneRel.eps y u = Work.OROneRel.eps t u)
    (htu : t ∈ Work.OROneRel.relatorLetters u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (Work.ORLyndon.transvectionLeft t y m u))
    (ht : t ∈ Work.OROneRel.relatorLetters (Work.ORLyndon.transvectionLeft t y m u))
    (S : Set α)
    (hS : ∃ x ∈ S, x ≠ t ∧
      x ∈ Work.OROneRel.relatorLetters (Work.ORLyndon.transvectionLeft t y m u)) :
    MagnusDescent K u l S := by
  have he : Work.OROneRel.eps t (Work.ORLyndon.transvectionLeft t y m u) = 0 := by
    rw [(transvectionLeftProps (K := K) hyt m).2.2.2.1 u, hm, sub_self]
  refine magnusDescent_of_transvection (K := K) hyt m u l hl hppu hm hcyc he ht ?_ S hS
  calc Work.OROneRel.relatorNorm
        (Work.OROneRel.rootW t (Work.ORLyndon.transvectionLeft t y m u) l hcyc he hl)
      ≤ Work.OROneRel.nonTLetters t (Work.ORLyndon.transvectionLeft t y m u) :=
        Work.OROneRel.relatorNorm_rootW_le_nonTLetters _ l t hcyc he hl
    _ ≤ Work.OROneRel.nonTLetters t u :=
        Work.ORLyndon.nonTLetters_transvectionLeft_le_clean u t y m
    _ < Work.OROneRel.relatorNorm u := Work.OROneRel.nonTLetters_lt_norm u t htu

/-- **The two-sided-shear route to `MagnusDescent`** (see `NOTES_epsNeZeroDescent_level.md` §22).

`ψ := Work.ORLyndon.shear t x m m'` is the Nielsen transformation `x ↦ t ^ (-m) * x * t ^ (-m')`
fixing all other generators; it is an automorphism of `F α`, it is *clean off* `t`, and its
exponent-shift is `eps t (ψ w) = eps t w - (m + m') * eps x w` (`Work.ORLyndon.shearProps`).  The
hypothesis `he : eps t u = (m + m') * eps x u` therefore makes `eps t (ψ u) = 0`, so that the
exponent-sum-zero Magnus step `Work.ORLyndon.annAt_of_epsZero_strong` applies at the letter `t` of
`ψ u`; and the non-`t` letter count is not increased by a shear
(`Work.ORLyndon.nonTLetters_shear_le`), so the Magnus base `rootW t (ψ u) l` is *strictly shorter*
than `u`.

Compared with `Work.ORLyndon.magnusDescent_of_transvectionData`, this version has a **two-parameter**
shear (`m` is free once `m + m'` is fixed), which is what allows the cyclicity of `ψ u` to be
arranged without changing the vanishing of `eps t`; all the algebraic inputs are discharged here,
and the only remaining hypotheses are the two word-combinatorial facts `hcyc` (cyclicity of `ψ u`)
and `ht` (membership of `t`). -/
theorem magnusDescent_of_shearData {α : Type u} [DecidableEq α] {K : Type v} [Field K]
    {t x : α} (hxt : t ≠ x) (m m' : ℤ) (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hppu : ¬ Work.OROneRel.IsProperPower u)
    (hm : Work.OROneRel.eps t u = (m + m') * Work.OROneRel.eps x u)
    (htu : t ∈ Work.OROneRel.relatorLetters u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator (Work.ORLyndon.shear t x m m' u))
    (ht : t ∈ Work.OROneRel.relatorLetters (Work.ORLyndon.shear t x m m' u))
    (S : Set α)
    (hS : ∃ x' ∈ S, x' ≠ t ∧
      x' ∈ Work.OROneRel.relatorLetters (Work.ORLyndon.shear t x m m' u)) :
    MagnusDescent K u l S := by
  have hprop := Work.ORLyndon.shearProps (α := α) (K := K) t x hxt m m'
  obtain ⟨hι, hσ, hJ, heps, hpp⟩ := hprop
  have he : Work.OROneRel.eps t (Work.ORLyndon.shear t x m m' u) = 0 := by
    rw [heps u, hm, sub_self]
  refine magnusDescent_of_epsZeroImage (K := K) (Work.ORLyndon.shear t x m m') hι hσ u l t hl
    (hpp u hppu) hcyc ht he hJ ?_ S hS
  calc Work.OROneRel.relatorNorm
        (Work.OROneRel.rootW t (Work.ORLyndon.shear t x m m' u) l hcyc he hl)
      ≤ Work.OROneRel.nonTLetters t (Work.ORLyndon.shear t x m m' u) :=
        Work.OROneRel.relatorNorm_rootW_le_nonTLetters _ l t hcyc he hl
    _ ≤ Work.OROneRel.nonTLetters t u := Work.ORLyndon.nonTLetters_shear_le u t x m m'
    _ < Work.OROneRel.relatorNorm u := Work.OROneRel.nonTLetters_lt_norm u t htu

-- NOTE (2026-10-01).  The statement
--
--   `theorem epsNeZeroDescent {K : Type*} [Field K] : Work.ORLyndon.EpsNeZeroDescent K`
--
-- which used to sit here as a `sorry`, had been removed on the ground that `EpsNeZeroDescent` is
-- the residual of the `annAt`/`Case2Input` route and is superseded by the `CLDirect` route.  That
-- route has meanwhile *proved* `Work.ORLyndon.lyndon_independence_of_pow` and hence Lyndon's
-- identity theorem `Work.ORLyndon.lyndonIdentity_of_pow`, and with it the residual is no longer
-- hard: the statement is restored below and **proved** from `lyndonIdentity_of_pow` through
-- `Work.ORLyndon.annAt_letters_of_lyndonIdentity_uncond` (this file) and the trivial-witness
-- reduction `Work.ORLyndon.magnusDescent_of_annAt`.  The chain is
--
--   `lyndonIdentity_of_pow` (Cohen--Lyndon, unconditional)
--     ⟹ `annAt K (u^l) u (relatorLetters u)`   [full letter set]
--     ⟹ `annAt K (u^l) u S` for every nonempty `S ⊆ relatorLetters u`   [`annAt_mono`]
--     ⟹ `MagnusDescent K u l S`   [trivial witness, `magnusDescent_of_annAt`]
--
-- together with the order statement `orderOf (presentRho (u^l) u) = l`, which is
-- `Work.ORLyndon.orderOf_presentRho_eps_ne_zero` (proved in session 1 without any KMS input).
-- Nothing in the argument uses the Case-2 structure beyond what `EpsNeZeroDescent` assumes.

/-! ## The residual `EpsNeZeroDescent` of the Cohen--Lyndon descent

For every cyclically reduced root `u` which is not a proper power, of relator norm `≥ 2`, none of
whose letters has vanishing exponent sum, every exponent `l ≥ 1` and every nonempty set `S` of
letters of `u`, there should be a Magnus descent datum for `(u, l, S)` and the class of `u` should
have order `l` in `⟨α | u ^ l⟩`.

**This statement is *not* proved here** — see the note below. -/

/- NOTE (2026-10-02, `ORFixes` session).  The declaration proving `Work.ORLyndon.EpsNeZeroDescent K`
that used to stand at this point has been **removed again**, because its proof cannot work with the
means available in the workspace; it was the only error in this file, and with it gone the module
(and hence `epsNeZeroDescent.olean`, which had been missing since 2026-10-01) builds `sorry`-free.

Why the proof that had been written here cannot work.

* `Work.ORLyndon.magnusDescent_of_annAt` builds the *trivial-witness* descent datum
  `v = of x₀`, `S' = {x₀}` for a given `S`; its transfer clause
  `annAt K (v ^ l) v {x₀} → annAt K (u ^ l) u S` is proved from its hypothesis
  `hann : annAt K (u ^ l) u S`.
* So the trivial witness discharges `EpsNeZeroDescent` only if one has
  `annAt K (u ^ l) u S` for **every** nonempty `S ⊆ relatorLetters u`, whereas
  `Work.ORLyndon.annAt_letters_of_lyndonIdentity_uncond` (and the Cohen--Lyndon/Lyndon identity
  results of `CLDirect`) provide it at `S = relatorLetters u` — the *weakest* statement in the
  family, because `annAt` is covariant in `E`: `annAt_mono` derives `annAt E'` from `annAt E` for
  `E ⊆ E'`.  The step `annAt_mono hSsub hann` therefore does not elaborate (Lean asks for
  `relatorLetters u ⊆ S`), and no reordering can fix it: the proper-subset case is strictly stronger.
* The proper-subset case is precisely the component-wise right-regularity of the Fox components,
  which the lead's design note `Submission/Work/ORLyndon/CASE2INPUT_LEAD.md` §1.2 records as
  **"not established; do not attempt"** for `l ≥ 2` (and out of reach for `l = 1`, where it needs
  Higman's theorem).  The same note's corrected reduction proves `LyndonIndependence` directly
  (skipping this descent), and the descent's residual `Work.ORLyndon.Case2Descent` remains a
  *hypothesis* of `Work.ORLyndon.descent_bundle`; nothing in the workspace consumes a proof of
  `EpsNeZeroDescent` as a term, so removing the declaration costs nothing.
* The statement itself is fine (and not vacuous); only its proof here was invalid.  Two smaller
  elaboration errors in the same proof (at the `rw [Work.OROneRel.relatorNorm, …]` steps) are a
  separate, easily repaired effect of the `Work.OROneRel.wordOf` refactor — `wordOf` now hardcodes
  `Classical.decEq α`, so a proof that rewrites with `relatorNorm` must first install the classical
  instance (a `classical` line, or an explicit `DecidableEq` matching `Classical.decEq`).

If a later session formalises node N2's Case 2 (the Masters--Linton/cyclic-cover descent, the
`sorry` of `Submission/Work/OROneRel/magnus_step_root.lean`), the natural shape of the result is a
genuine descent datum — *not* the trivial witness — and it should be reinstated here. -/


end Work.ORLyndon
