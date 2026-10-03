import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.magnusStepNielsenTorusFamily
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv
import Submission.Work.OROneRel.stepOneHnnOfFreeVertex
import Submission.Work.OROneRel.magnusStepData_one_of_freeGroupPresentation
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.OROneRel.magnusStepData_two_two

/-!
# The "no exponent sum zero" Magnus step, with the root tracked

This file contains the target lemma `Work.OROneRel.magnus_step_root_no_eps_zero` (with a `sorry`)
together with the definitions it is assembled from.  The combinatorial toolbox -- the gauge/loop
class machinery of the `ℤ`-cover of the presentation complex, including the telescoping identity
`gauge_decor_zero` -- lives in `Submission/Work/OROneRel/GaugeDefs.lean`.

## The route

`NOTES_magnus_step_root_no_eps_zero.md` (this directory) records the full route and the refuted
alternatives.  In short: the classical "Nielsen/Euclidean" reduction does not exist (there is no
automorphism `ψ` of `F α` with `eps t (ψ u) = 0` and `relatorNorm (mmW t (ψ u)) < relatorNorm u`;
see `mmStepData_of_pos_expsums.lean`), and the general-weight Magnus rewriting of `u` has a relator
of norm `|u|` -- so neither gives the strict decrease of the relator norm demanded here.  The
decrease comes from the one-relator `ℤ`-domain construction: for a weight `c` with `cohom c u = 1`,
the domain's fundamental group is `F (E \ T) / << v ^ l >>` where `v` is the word of the lift of `u`
with the `|u| - (V - 1)` tree edges deleted (`V ≥ 2` = number of levels visited by that lift), and
`G = ⟨α | u ^ l⟩` is the HNN extension of this one-relator group over the "extremal level"
subgroups, with the class of `u` the class of the root `v`.  The Bass--Serre recognition step is
`Work.OROneRel.hnn_of_telescoping`.

## State after the fourth session (what is proved, and what is left)

* The weighted Magnus step `Work.OROneRel.magnusStepCase2_of_weight` (proved) already gives the
  *conclusion of this file's target* whenever `u` satisfies the **divisibility condition**
  `∃ t ∈ relatorLetters u, ∃ c, c t = 1 ∧ cohom c u = 1` (equivalently `gcd {eps_x u : x ≠ t} ∣ eps_t u`).
  Its count-strengthened form `Work.OROneRel.magnusStepCase2_of_weight_count` bounds the produced
  root by the number of non-`t` letters of `u`.
* `Work.OROneRel.magnusStepNielsenRoute` (new, proved) transports the step along a Nielsen
  transformation (`MagnusStepData.of_aut`) and consequently proves the target from
  `∃ ψ, t, c` with `t ∈ relatorLetters (ψu)`, `c t = 1`, `cohom c (ψu) = 1` and
  `#{letters ≠ t in ψu} < relatorNorm u` (`magnusStepData_of_count_image`).
* `Work.OROneRel.magnusStepData_torusFamily` (new, proved) is a *family of new cases* reached that
  way: for `u = x ^ p y ^ q` (`p, q ≥ 2`) with `p m + q = ± 1` (`m < 0`) and
  `(p-1)|m| + (m+q) < p + q`, the target holds for every `l ≥ 1` (e.g. `(2,3)`, `(3,5)`, `(3,7)`,
  `(4,3)`, `(5,4)`).
* The **residual** is the case in which no letter of any automorphic image supplies the divisibility
  condition with a short enough image (`a ^ 3 b ^ 8`, `a ^ 4 b ^ 7`, `a ^ 6 b ^ 10 c ^ 15`, ...).
  For those, the `ℤ`-domain route is the known way: with the domain `D` one gets
  `G ≅ HNN (π₁ D, π₁ (D ∩ t⁻¹D), π₁ (D ∩ tD), conj_t)` with `π₁ D = ⟨β | v ^ l⟩`,
  `relatorNorm v ≤ |u| - (V-1) < |u|` and the class of `u` equal to that of the root `v`.  The two
  missing inputs are (A) the injectivity of the class map `⟨β | v ^ l⟩ → ⟨α | u ^ l⟩` (the
  Freiheitssatz for the domain) and (B) the graded meet conditions for the vertex group; both are
  consumed by the *proved* `Work.OROneRel.hnn_iso_of_meet_conditions_graded`.

## Session 5 (see `NOTES_magnus_step_root_no_eps_zero.md`, SESSION 5)

The conclusion of this target holds at `l = 1` for **every two-letter relator of the hypotheses**,
i.e. for `u = a ^ p * b ^ q` with `a ≠ b` and `2 ≤ p, q` (and, by Nielsen/conjugacy transport, for
all signed and rotated two-letter relators):

* `Submission/Work/OROneRel/magnusStepDataOne_cpRelator_general` (new, sorry-free, axiom-clean) —
  the rescaled weight `a ↦ q / gcd p q`, `b ↦ -(p / gcd p q)`, primitive and killing `u`, with a
  *free* kernel (`Work.OROneRel.isFreeGroup_ker_rescaledChi`), fed into
  `Work.OROneRel.magnusStepDataOne_of_freeKernel`; definitions in
  `Submission/Work/OROneRel/rescaledCPDefs.lean`;
* `Submission/Work/OROneRel/magnusStepData_cpRelator` — the coprime case via the ordinary
  exponent-sum character.

These are exactly the two-letter cases the Nielsen and divisibility routes provably cannot reach
(`x ^ 3 y ^ 8`, `x ^ 4 y ^ 7`, and the non-coprime pairs `(4,6)`, `(6,8)`, …).

**The `wordOf` split of the workspace has been repaired** (this session):
`wordOf`/`mk_wordOf` now live once, in `Submission/Work/OROneRel/wordOfDefs.lean`, imported by both
`MagnusGenDefs` and `weinbaumMonoDefs`; `Submission/Work/OROneRel/TwoCones.lean` imports the two
cones (free-kernel/torus-knot side *and* the Magnus-rewriting/`ℤ`-cover/coedge/domain side) plus
this file, and builds.  A *second* duplicate, `Work.OROneRel.rew` (`MagnusGenDefs` vs `RhoRewrite`,
two genuinely different functions), remains and blocks files that need both —
`magnus_step_root_eps_zero.lean` is one; see the notes for the list and the recommendation.

**For `l ≥ 2` the `⊤`-route is impossible**: a prover showed that the kernel of the character on
`⟨α | (a ^ p b ^ q) ^ l⟩` is a free product of infinitely many copies of `ℤ/l` with a free group
(two non-conjugate involutions for `(p,q,l) = (2,2,2)`), hence not of the form `⟨β | v ^ l⟩`.  The
vertex must be a `ℤ`-domain's fundamental group with *proper* associated subgroups, for `l ≥ 2` and
for relators on `≥ 3` letters alike.

## Session 7 (see `NOTES_magnus_step_root_no_eps_zero.md`, SESSION 7)

Diagnosis only, plus three proved reductions (no new case):

* the hypothesis `c t = 1` of `magnusStepCase2_of_weight` is *forced*, not bookkeeping: the
  transversal `{t^j}` of `ker χ` is a set of coset representatives only when `χ t = ±1`;
* the `⊤`-route is impossible for `d ≥ 3` at `l = 1` too (`χ(G) = 2 - d ≠ 0` vs `χ = 0` for
  `K ⋊ ℤ`), and the kernel route's hypothesis (`ker χ ≅ ⟨β | v ^ l⟩`,
  `residualKernelAssembly.magnusStepCase2_of_kernelData`) is likewise implausible there;
* so every remaining case needs Linton's Prop. 2.2.19.  The two families that *are* settled at
  `l = 1` beyond the divisibility/torus families are recorded here by
  `Submission/Work/OROneRel/stepOneHnnOfFreeVertex.lean` —
  `Work.OROneRel.magnusStepData_one_of_hnnOfFreeGroup`: any HNN splitting of `⟨α | u ^ 1⟩` over a
  *free* vertex group produces the conclusion (subsuming the free-kernel and
  free-product-with-`ℤ` routes) — and its corollary
  `Work.OROneRel.magnusStepData_one_of_freeGroupPresentation`
  (`Submission/Work/OROneRel/magnusStepData_one_of_freeGroupPresentation.lean`), the
  primitive-relator family.

## Session 9 (see `NOTES_magnus_step_root_no_eps_zero.md`, SESSION 9)

The residual is now understood to be the *same construction* as the solved (divisibility) case
`Work.OROneRel.magnusStepCase2_of_weight`, but with the spine `W k = t ^ k` of a weight-one letter
`t` replaced by a **tree of the level graph** (the first-arrival tree of the walk).  The weighted
Magnus rewriting of `Submission/Work/OROneRel/wgtMMDefs.lean` and its four successors is a complete,
*explicit*, Britton-free construction; what it needs from the spine, beyond the combinatorial
bookkeeping, is the *compatibility* relation `t · (loop class of e) · t⁻¹ = loop class of t · e` on
`D ∩ t⁻¹D`.  The new module `Submission/Work/OROneRel/spineShiftDefs.lean`:

* shows that this compatibility relation is *equivalent* to the constancy, in the group, of the
  ratios `spineRho W k = W (k+1) · (W k)⁻¹` on the relevant levels
  (`spineClass_conj_of_rho`, `hnnCompatible_of_rho`);
* proves that a traversal of a tree edge has trivial loop class (`gaugeMap_tree_triv`), so it is
  legitimately deleted, and that deleting such a traversal strictly decreases the norm
  (`deleted_length_lt`);
* records the spine case (`spineGauge`, `spineRho_spineGauge`, `hnnCompatible_spine`) as the proved
  instance of the compatibility relation.

The single remaining obligation is therefore: **find a gauge/tree with (i) a traversal of the walk
among its tree edges and (ii) constant ratios on the levels of `D ∩ t⁻¹D`.**  The first-arrival gauge
satisfies (i) (`coedge_root_norm_lt`) but fails (ii) (`spineRho 0 = 1` vs `spineRho 8 = a⁻¹` for
`u = a³b⁸`, `c = (8,-3)`).
-/


namespace Work.OROneRel

universe u

/-! ## The two inputs of the target, isolated

The target is the `Z`-domain step of the Magnus--Moldavanskii hierarchy for the case in which no
letter of the relator has exponent sum `0`.  Its proof decomposes into exactly two inputs:

* **the domain datum** `MagnusDomainDatum u l` -- what the `Z`-cover construction of
  `Submission/Work/OROneRel/domainRootExists.lean` (root, strict norm decrease, aperiodicity) and of
  the coedge development (`coedge_injective`, `coedge_root_class`: the base `F (β) →* F (α)` is
  injective, the root tracks `u`) is expected to produce: a subgroup `H ≤ ⟨α | u ^ l⟩` which is the
  fundamental group of a `Z`-domain, a stable letter `t`, a grading `φbar`, the two graded meet
  conditions of Linton's `Z`-domain theorem (instead of the false "meet constancy"), and an
  identification `⟨β | v ^ l⟩ ≃* H` carrying the root `v` to the class of `u`;
* **the recognition theorem** `MeetRecognition` -- the Bass--Serre statement that a subgroup `H` with
  those two meet conditions and `⟨H, t⟩ = G` *is* the base of an HNN decomposition of `G`.  Its
  mathematical content is the graded Britton normal form
  `Work.OROneRel.no_reduced_relation_graded` (`gradedBrittonMeet`), itself equivalent to the
  statement that the coset graph of `(H, t)` is a tree.

Everything else -- the norm bookkeeping, the aperiodicity of the root, the transport of the HNN
structure across the identification of the base, and the tracking of the root -- is done below,
sorry-free. -/

/-- **The data produced by the `Z`-domain construction.**  For `u` cyclically reduced, not a proper
power, of norm `≥ 2` and with all exponent sums non-zero, the `Z`-cover of `⟨α | u ^ l⟩` (with a
primitive weight `c` killing `u`, non-zero on some letter of `u`) is expected to produce:

* a root `v` over an alphabet `β` (the non-tree edges of a `Z`-domain), not a proper power, of norm
  strictly smaller than `relatorNorm u` -- `Work.OROneRel.domainRootExists` supplies the candidate
  (`β = coverBetaEdge (uGauge c u) c u`, `v = coedgeRoot (uGauge c u) c u`), the norm decrease is
  `Work.OROneRel.coedge_root_norm_lt` and the aperiodicity is the last component of
  `Work.OROneRel.domainRootExists`;
* a subgroup `H ≤ ⟨α | u ^ l⟩` (the fundamental group of the domain), a stable letter `t`, and the
  *HNN decomposition* of `⟨α | u ^ l⟩` over `H` with stable letter `t`;
* an isomorphism `⟨β | v ^ l⟩ ≃* H` carrying the class of the root `v` to the class of `u` -- this
  is the "Freiheitssatz for the domain" (`Work.OROneRel.coedge_injective` gives the injectivity of
  the class map `F (β) →* F (α)`, together with the normal-closure compatibility), and the root
  identification is the telescoping identity `Work.OROneRel.coedge_root_class`.

**The decomposition field `splits` cannot be replaced by group-theoretic "meet conditions".**  A
previous route derived `splits` from the two graded meet conditions
`H ⊓ ⨆_{i≥1} t^{i+1}Ht^{-(i+1)} = H ⊓ tHt⁻¹` and its mirror (`Work.OROneRel.hnn_of_telescoping`,
`Work.OROneRel.hnnIsoOfMeetConditionsGraded_free`, `Work.OROneRel.no_reduced_relation_graded`,
`Work.OROneRel.coset_isTree`).  That is **false**: see
`Submission/Work/OROneRel/NOTES_meet_conditions_insufficient.md` and
`Submission/Work/OROneRel/NOTES_coset_counterexample.md` for the counterexample
`G = ⟨a, t | a (t a t⁻¹) = (t a t⁻¹) a⟩`, `H = ⟨a⟩`, where all the hypotheses hold but
`G` has no such HNN decomposition.  The meet conditions control only the *one-sided generated
telescopes*, not the products `H · tHt⁻¹`; the missing control is exactly the connectivity input of
Linton's `Z`-domain theorem (`One-relator hierarchies`, Prop. 2.2.19), whose conclusion is the graph
of spaces splitting `π₁(X) ≅ HNN (π₁ D, π₁ (D ∩ t⁻¹D), π₁ (D ∩ tD), conj_t)` and which is therefore
recorded here as the field `splits` rather than rederived from group-theoretic hypotheses. -/
structure MagnusDomainDatum {α : Type u} (u : FreeGroup α) (l : ℕ) : Type (u + 1) where
  β : Type u
  v : FreeGroup β
  notProperPower : ¬ IsProperPower v
  norm_lt : relatorNorm v < relatorNorm u
  H : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α)))
  t : PresentedGroup ({u ^ l} : Set (FreeGroup α))
  splits : ∃ (A B : Subgroup ↥H) (φ : A ≃* B)
      (e : HNNExtension ↥H A B φ ≃* PresentedGroup ({u ^ l} : Set (FreeGroup α))),
    (∀ h : ↥H, e (HNNExtension.of h) = (h : PresentedGroup ({u ^ l} : Set (FreeGroup α)))) ∧
      e HNNExtension.t = t
  iso : PresentedGroup ({v ^ l} : Set (FreeGroup β)) ≃* ↥H
  root : ((iso (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) : ↥H) :
      PresentedGroup ({u ^ l} : Set (FreeGroup α)))
    = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u

/-- **The target follows from the domain datum.**  Nothing here is delegation: the norm decrease,
the aperiodicity and the root tracking are the *fields* of `MagnusDomainDatum`, the splitting over
`H` is its field `splits`, and the whole HNN transport (across the base identification
`⟨β | v ^ l⟩ ≃* H`, with the stable letter `t` and the conjugation relation `t a t⁻¹ = φ a`) is
carried out below.  At `l = 1` the tracking is automatic; for `l ≥ 2` it is exactly the field
`MagnusDomainDatum.root`. -/
theorem magnus_step_root_no_eps_zero_of_domainDatum {α : Type u} (u : FreeGroup α) (l : ℕ)
    (D : MagnusDomainDatum u l) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ IsProperPower v ∧ relatorNorm v < relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by
  obtain ⟨A, B, φ, e, he_of, _⟩ := D.splits
  obtain ⟨A', B', φ', E, _, _, hE_of, _⟩ := hnnExtension_iso_of_baseMulEquiv D.iso.symm A B φ
  -- the class of `u` lies in the vertex group
  have hmu : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u ∈ D.H := by
    rw [← D.root]
    exact (D.iso (PresentedGroup.mk ({D.v ^ l} : Set (FreeGroup D.β)) D.v)).2
  -- the inverse of the comparison map on the class of `u`
  have h1 : e.symm (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
      HNNExtension.of (⟨PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u, hmu⟩ : ↥D.H) := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, he_of]
  -- the base identification carries the root to the class of `u`
  have h2 : D.iso.symm (⟨PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u, hmu⟩ : ↥D.H)
      = PresentedGroup.mk ({D.v ^ l} : Set (FreeGroup D.β)) D.v := by
    rw [← MulEquiv.symm_apply_apply D.iso
      (PresentedGroup.mk ({D.v ^ l} : Set (FreeGroup D.β)) D.v)]
    exact (congrArg D.iso.symm (Subtype.ext D.root)).symm
  refine ⟨D.β, D.v, D.notProperPower, D.norm_lt, A', B', φ', e.symm.trans E, 1, ?_⟩
  simp only [one_mul, inv_one, mul_one]
  show (e.symm.trans E) (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
    HNNExtension.of (PresentedGroup.mk ({D.v ^ l} : Set (FreeGroup D.β)) D.v)
  rw [MulEquiv.trans_apply, h1, hE_of, h2]

/-! ## The target from the canonical splitting of the pair `(H, τ)`

The two inputs of the target, in the *sharpest* form reached so far: a subgroup `H ≤ ⟨α | u ^ l⟩`
identified with a one-relator group `⟨β | v ^ l⟩` of shorter root (`θ`, `hroot`), an element `τ`
which together with `H` generates (`hgen`), and -- the single remaining obligation -- the injectivity
of the canonical comparison map `hnnConjMap H τ : HNN(↥H, A, B, φ) →* ⟨α | u ^ l⟩` of
`Submission/Work/OROneRel/hnnConjSplit.lean` (whose well definedness is automatic, `φ` being defined
by conjugation by `τ`).  Nothing else is needed: the comparison map is surjective as soon as
`H ⊔ ⟨τ⟩ = ⊤`, and its inverse transports the HNN structure across `θ`. -/
theorem magnus_step_root_no_eps_zero_of_hnnSplit {α : Type u} (u : FreeGroup α) (l : ℕ)
    {β : Type u} (v : FreeGroup β)
    (hpp : ¬ IsProperPower v) (hnorm : relatorNorm v < relatorNorm u)
    (H : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α))))
    (θ : PresentedGroup ({v ^ l} : Set (FreeGroup β)) ≃* ↥H)
    (hroot : ((θ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) : ↥H) :
      PresentedGroup ({u ^ l} : Set (FreeGroup α))) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u)
    (τ : PresentedGroup ({u ^ l} : Set (FreeGroup α)))
    (hgen : H ⊔ Subgroup.closure {τ} = ⊤)
    (hinj : Function.Injective (hnnConjMap H τ)) :
    ∃ (β' : Type u) (v' : FreeGroup β'), ¬ IsProperPower v' ∧ relatorNorm v' < relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v' ^ l} : Set (FreeGroup β')))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v' ^ l} : Set (FreeGroup β'))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v' ^ l} : Set (FreeGroup β'))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v' ^ l} : Set (FreeGroup β')) v') * c⁻¹ := by
  classical
  have hmu : PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u ∈ H := by
    rw [← hroot]
    exact (θ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v)).2
  obtain ⟨A', B', φ', E, -, -, hE_of, -⟩ :=
    hnnExtension_iso_of_baseMulEquiv θ.symm ((hnnEdgeA H τ).subgroupOf H)
      ((hnnEdgeB H τ).subgroupOf H) (hnnConjEquiv H τ)
  refine ⟨β, v, hpp, hnorm, A', B', φ',
    ((MulEquiv.ofBijective (hnnConjMap H τ)
      (hnnConjMap_bijective H τ hinj hgen)).symm.trans E), 1, ?_⟩
  simp only [one_mul, inv_one, mul_one]
  rw [MulEquiv.trans_apply]
  have hsymm : (MulEquiv.ofBijective (hnnConjMap H τ)
      (hnnConjMap_bijective H τ hinj hgen)).symm
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
      HNNExtension.of (⟨PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u, hmu⟩ : ↥H) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [MulEquiv.ofBijective_apply, hnnConjMap_of]
  rw [hsymm, hE_of]
  have hθv : θ (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) =
      ⟨PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u, hmu⟩ := Subtype.ext hroot
  rw [show θ.symm (⟨PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u, hmu⟩ : ↥H) =
      PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v from by
    rw [← hθv]
    simp]

/-! ## The target lemma -/

theorem magnus_step_root_no_eps_zero {α : Type u} (u : FreeGroup α) (l : ℕ) (hl : 1 ≤ l)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0) :
    ∃ (β : Type u) (v : FreeGroup β), ¬ Work.OROneRel.IsProperPower v ∧
      Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm u ∧
      ∃ (A B : Subgroup (PresentedGroup ({v ^ l} : Set (FreeGroup β)))) (φ : A ≃* B)
        (e : PresentedGroup ({u ^ l} : Set (FreeGroup α)) ≃*
          HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ),
        ∃ c : HNNExtension (PresentedGroup ({v ^ l} : Set (FreeGroup β))) A B φ,
          e (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u) =
            c * HNNExtension.of (PresentedGroup.mk ({v ^ l} : Set (FreeGroup β)) v) * c⁻¹ := by sorry

end Work.OROneRel
