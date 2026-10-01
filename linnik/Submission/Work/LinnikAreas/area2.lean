import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.Kernel
import Submission.Work.LinnikAreas.Assembly
import Submission.Work.LinnikAreas.ClassIdentity
import Submission.Work.LinnikAreas.FarBoundOfDensity
import Submission.Work.LinnikAreas.FamilyZeroDensitySplitting
import Submission.Work.LinnikAreas.FamilyZeroCountTrivial
import Submission.Work.LinnikAreas.FarBoundJM
import Submission.Work.LinnikAreas.FarBoundOfJutilaCrudeWide
import Submission.Work.ZeroDensity.LogFree.logFreeNPInstances
import Submission.Work.LinnikAreas.LogFreeNPWiring

/-!
Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN Linnik contract (Submission/Work/LinnikContract/Areas.lean; composition
linnik_of_areas PROVED, so proving all seven areas closes the problem). Read first:
* Submission/Work/LinnikPlan/ROUTE_LEAD.md: §1.2 constants, §3.1 your area with the source and proof sketch, §4 numerics, §5 risks;
* LinnikContract/Defs.lean.
Never use the quarantined lemmas (LinnikContract/Quarantine.lean: q-dependent constants); the build guard will fail. The seeded
Submission/Commons/** is a large, fully proved analytic-number-theory library (ROUTE_LEAD §2.1 inventory); reuse it and do not re-request what
exists. Parallelise: request all independent pieces at once.

Area2 = the HB §13 reduction (Lemmas 13.1–13.2), uniform and signed: the explicit formula restricted to a box of zeros, plus a density
bound for the zeros outside it. It does NOT need Burgess. R = R(ε), q₀ = q₀(ε).

---

# Area 2 — state of the reduction (this module)

**Current state (single input).**  `area-2 theorem` below has exactly **one** gap,
`Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide` — the *crude* log-free non-principal family
estimate `Σ_{χ ≠ 1} N(σ,T,χ) ≤ C·(qT)^{(24/5+ε)(1-σ)}` on the constant range `σ ≥ 1 - 1021/5000`.
That one statement suffices for the whole far-zero bound
(`Work.LinnikAreas.FarBoundOfJutilaCrudeWide`, proved), because the crude coefficient is
irrelevant to the argument (§5 of `NOTE_area2_principal_character.md`) and the threshold
`1021/5000 > 1/4.9` is where the σ-blind count takes over.  The same input is *also* implied by
the shared chapter's two sharp targets, via the proved bridge
`FamilyZeroDensityJutilaCrudeWide_of_jutilaNP_and_mesh`; the older two-input route
(`area2_of_jutila_mesh`) remains proved as an alternative.

**Status: proved.**  `area-2 theorem : Work.LinnikContract.Area2` below is complete: the file
builds with no unproved declaration, and `#print axioms Work.LinnikAreas.area2` is
`[propext, Classical.choice, Quot.sound]`.  The final proof is
`area2_of_logFreeNP Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four`, i.e. the unified
log-free estimate of `Submission/Work/ZeroDensity/LogFree` through the bridges recorded in
`Submission/Work/LinnikAreas/LogFreeNPWiring.lean` and `FarBoundOfJutilaCrudeWide.lean`.

## Proved

* `Work.LinnikAreas.ClassIdentity` (`.../ClassIdentity.lean`) — **Heath-Brown's Lemma 13.1**,
  box-restricted and uniform in `q`: with `L = 11/2`, `K = 3/10`, `𝓛 = log q`, the tent-weighted
  prime sum over the class `a mod q` equals `𝓛·(K²/φ(q) − φ(q)⁻¹ Σ_{χ ≠ 1} χ̄(a)·(box sum of
  zeros))` up to `C/(φ(q)𝓛)`, the far-zero mass `φ(q)⁻¹ Σ_{χ ≠ 1} farSum`, and the prime-power
  tail `C·q^{-(L-2K)/2}/𝓛`.
* `Work.LinnikAreas.area2_of_classIdentity` (`.../Assembly.lean`) — the *assembly*: the
  φ(q)-bookkeeping, the ε-management and the passage from a positive weighted prime sum to a
  prime `p ≡ a (mod q)`, `p ≤ q^{11/2}`.
* `Work.LinnikAreas.FarBoundOfDensity` (`.../FarBoundOfDensity.lean`) — **Heath-Brown's Lemma 13.2
  from the family zero-density estimate**: the dyadic `(λ, |Im| log q)` shell decomposition of the
  far mass, using the density bound for the shells of height `≥ 1/ log q` and the σ-blind ball
  count for the rest.
* `Work.LinnikAreas.FamilyZeroCountTrivial` (`.../FamilyZeroCountTrivial.lean`) — the **σ-blind
  family count in log-free form**: `Σ_χ N(σ,T,χ) ≤ C_ε (qT)^{1+ε}` for all `q ≥ 2`, `σ ∈ [0,1]`,
  `T ≥ 1`.  (This is the workspace's own two σ-blind counts — `FamilyZeroCountNonPrincipal` and
  `PrincipalZeroCount` — with the logarithm absorbed into a power of `qT`.)
* `Work.LinnikAreas.familyZeroDensityHyp_of_trivial_and_nearLine`
  (`.../FamilyZeroDensitySplitting.lean`) — **reassembly**: the trivial count together with its
  near-line complement is exactly `FamilyZeroDensityHyp`.
* `Work.LinnikAreas.area2_of_farBound`, `area2_of_density` and `area2_of_nearLine` (below) —
  Area 2 from the far-zero bound, from the family zero-density estimate, and from the near-line
  core.
* `Work.LinnikAreas.LargeSieve` — the large-sieve inequality for Dirichlet characters, the tool a
  density estimate needs.
* kernel bounds (`.../Kernel.lean`): `‖F₂(z)‖ ≤ min(K², 4/‖z‖²)` and
  `‖Hk L K z‖ ≤ e^{-(L-2K)Re z}·min(K², 4/‖z‖²)` for `Re z ≥ 0`.

## The chain

    FamilyZeroCountTrivial  +  FamilyZeroDensityNearLine
        → FamilyZeroDensityHyp   (familyZeroDensityHyp_of_trivial_and_nearLine)
        → FarBoundHyp            (FarBoundOfDensity, Heath-Brown's Lemma 13.2)
        → Work.LinnikContract.Area2   (area2_of_farBound, via ClassIdentity + the assembly)

Every arrow is proved.  **The single missing input was
`Work.LinnikAreas.FamilyZeroDensityNearLine`**: Heath-Brown's (1.4),
`Σ_{χ mod q} N(σ,T,χ) ≪_ε (qT)^{(12/5+ε)(1−σ)}`, restricted to the range
`(12/5+ε)(1−σ) < 1+ε` — that is, to `σ > 1 − (1+ε)/(12/5+ε) ≈ 0.583`, the sub-trivial range where
the σ-blind counts of this workspace cannot reach.  [HB] states this without proof, attributing it
to "a combination of a log-free bound of Jutila [21] with a result of Huxley [17]": it is an
**imported deep input of the paper**, not a consequence of the workspace's library.

## How the remaining input is meant to be discharged (ROUTE_LEAD §3.1, bullet 3)

The plan of the paper (and of `ROUTE_LEAD.md`) is to take this near-line range apart, not by any
single imported theorem, but by splitting the dyadic shells `λ ∈ [m, m+1]`,
`|γ| log q ∈ [n, 2n]` of the far mass according to the size of `λ`:

* **(D-far-1)** for the *low* shells, `λ ≤ A log log q`: a **log-free** family estimate
  `Σ_χ N(σ,T,χ) ≤ C (qT)^{c(1−σ)}` with `c = 2+ε`.  This is HB §11's zero detector with `k`
  fixed; the *convexity* bound `φ = 1/2` suffices, so this piece does **not** need Burgess.
  (HB §11 with the same detector and `φ = 1/3` — Burgess — is the object of the in-progress
  `Submission/Work/LinnikAreas/Density4/**`.)
* **(D-far-2)** for the *high* shells, `λ ≥ A log log q`: **logarithms are harmless** here
  (they are absorbed by the geometric decay `e^{-4.9\lambda}` of the kernel, provided `A` is
  chosen larger than `B/(4.9 − c)`), so any estimate `Σ_χ N(σ,T,χ) ≤ C(qT)^{c(1−σ)}(log qT)^B`
  with `c < 4.9` will do.  Montgomery's density theorem (large sieve) supplies one.
* the σ-blind count for `1 − σ ≥ 0.2` (already proved, `FamilyZeroCountTrivial`).

Turning that into a proof of `FarBoundHyp` requires re-running the shell decomposition of
`FarBoundOfDensity` with the shell-dependent exponent `c = c(λ)` (the present `FarBoundOfDensity`
consumes a single, uniform-in-σ estimate `FamilyZeroDensityHyp`, hence needs the near-line range
without logarithms).  This is pure assembly work and is *not* part of the irreducible input.

## Weakening the near-line core (this session)

The single input `FamilyZeroDensityNearLine` (log-free `(12/5+ε)` on the *whole* near-line range
`σ > 7/12`) is more than the far-bound argument needs.  Re-running the dyadic shell decomposition
of the far mass *shell by shell* (`Submission/Work/LinnikAreas/FarBoundOfJutilaMontgomery`, with
the assembly in `Submission/Work/LinnikAreas/FarBoundJM`) shows that a logarithm is harmless on
all shells with `λ = (m+1) > 𝓛/5`, because there the `m`-sum is `≪ q^{-0.49}`; only the shells
`λ ≤ 𝓛/5` (that is, `σ ≥ 4/5`) need a *log-free* estimate.  Concretely (all proved):

* `FarBoundHyp_of_jutila_and_montgomery : FamilyZeroDensityJutila → FamilyZeroDensityMontgomery
  → FarBoundHyp`, and `area2_of_jutila_montgomery` the corresponding form of `Area2`;
* `FamilyZeroDensityJutila`    — `Σ_χ N(σ,T,χ) ≤ C(qT)^{(2+ε)(1−σ)}`, **log-free**, `σ ≥ 4/5`;
* `FamilyZeroDensityMontgomery` — `Σ_χ N(σ,T,χ) ≤ C(qT)^{(12/5+ε)(1−σ)}(log qT)^B`, `σ ≤ 4/5`.

Two further refinements of that pair are proved as well:

* `FamilyZeroDensityMontgomery_of_huxley : FamilyZeroDensityHuxley → FamilyZeroDensityMontgomery`
  (the logarithmic power only weakens the right-hand side, so this is a genuine relaxation);
* `FamilyZeroDensityMontgomeryMid` — the same statement restricted to `σ ∈ [7/12, 4/5]` — and
  `FamilyZeroDensityMontgomery_of_trivial_and_mid : TrivialFamilyCountForm →
  FamilyZeroDensityMontgomeryMid → FamilyZeroDensityMontgomery`: the σ-blind count settles
  `σ ≤ 7/12`, so Montgomery's theorem is only needed on `[7/12, 4/5]`.  Correspondingly
  `area2_of_jutila_montgomery_mid : FamilyZeroDensityJutila → TrivialFamilyCountForm →
  FamilyZeroDensityMontgomeryMid → Area2`.

Since `FamilyZeroDensityMontgomery` is implied by `FamilyZeroDensityHuxley` (take `B = 0`), this
pair is *strictly weaker* than (Jutila, Huxley), hence strictly weaker than
`FamilyZeroDensityNearLine`.  The split point is the one forced by the geometry: shells below
`𝓛/5` contribute an `m`-sum of size `O(1)`, so a factor `(log q)^B` there would survive the
`q → ∞` limit (`R = R(ε)` being fixed), while the shells above `𝓛/5` carry the decay.

## Session 4: the sharp Montgomery exponent suffices

The middle-range input `Work.LinnikAreas.FamilyZeroDensityMontgomery` (`12/5` on `σ ≤ 4/5`) is
*stronger than necessary*: the far-zero assembly only ever uses it through the *coefficient* of
`1 - σ`, and the `m`-sum

`Σ_{𝓛/5 < m+1 ≤ 5𝓛/12} e^{-4.9·m}·(qT)^{c(m+1)/𝓛}`

converges (with a power of `q` to spare) for *any* coefficient `c < 4.9`.  This session narrows
the requirement to the weakest form that the literature supplies:

* `Work.LinnikAreas.cellBoundJMsh` — the three-branch cell bound with the middle coefficient
  `2551/1000 = 2.551` (instead of `2451/1000`), and the parallel assembly
  `FarBoundHyp_of_jutila_and_mesh`, `area2_of_jutila_mesh` in `Work.LinnikAreas.FarBoundJM`;
* `Work.LinnikAreas.FamilyZeroDensityMesh` — the *log-free* statement
  `Σ_χ N(σ,T,χ) ≤ C(qT)^{(51/20+ε)(1-σ)}` for `7/12 ≤ σ ≤ 4/5`.  It is *strictly weaker* than
  either Montgomery form: `51/20 = 2.55 > 12/5 = 2.4` (so the `12/5` form implies it) and
  `51/20 > 5/2 ≥ 3/(2-σ)` on this range (so the *sharp* form implies it);
* the two bridges (`Work.LinnikAreas.FamilyZeroDensityMesh_of_montgomery` and
  `FamilyZeroDensityMesh_of_montgomerySharp`, both proved) — the logarithmic power of the sharp
  form is absorbed using the slack `1/20` in the coefficient and `1 - σ ≥ 1/5`.

Consequently `Work.LinnikAreas.area2_of_jutila_montgomerySharp` derives Area 2 from Jutila's
log-free bound together with the *sharp* exponent `3(1-σ)/(2-σ)+ε` of Montgomery's density
theorem — which needs **no Burgess input and no Huxley `12/5` estimate on `(3/4,4/5]`** — and
that is the pair the deliverable `area2` now consumes.  Note `3/(2-σ) ≤ 3/(2-4/5) = 5/2 < 51/20`,
so the sharp form is *weaker* than the middle-range input; the margin `51/20 - 5/2 = 1/20` is
exactly what accommodates the logarithmic power.

## Session 4 (continued): where the two inputs stand, and three concrete next steps

1. **The two inputs are exactly the targets of the shared chapter `Submission/Work/ZeroDensity`.**
   The bridges
   `Work.LinnikAreas.JMAuxSh.familyZeroDensityJutila_of_famDensityEpsRange : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2 → FamilyZeroDensityJutila`
   and
   `Work.LinnikAreas.JMAuxSh.familyZeroDensityMontgomerySharp_of_montgomerySharp : (∀ B > 0, Work.ZeroDensity.MontgomerySharp B) → FamilyZeroDensityMontgomerySharp`
   (`Submission/Work/LinnikAreas/JMAuxSh/ZeroDensityBridges.lean`, proved) transliterate the
   chapter's statements into the two Props below.  Note `Work.ZeroDensity.Jutila.jutilaLogFree`
   and `Work.ZeroDensity.NearLine.nearLineLogFree` were *stated* there (then unproved), and
   `Work.ZeroDensity.Basic` already contains the (`12/5`) Montgomery bridges, and the chapter has
   now *stated* the two targets as
   `Work.ZeroDensity.Jutila.jutilaLogFree : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2` and
   `Work.ZeroDensity.Montgomery.montgomerySharp : ∀ B > 0, Work.ZeroDensity.MontgomerySharp B`
   (both then unproved).  Once those were proved, the two gaps below were replaced by
   `(Work.LinnikAreas.JMAuxSh.familyZeroDensityJutila_of_famDensityEpsRange jutilaLogFree)` and
   `(Work.LinnikAreas.JMAuxSh.familyZeroDensityMontgomerySharp_of_montgomerySharp montgomerySharp)`,
   importing those two modules.

2. **The middle-range input would shrink to the window `[0.7958, 0.8]`** if the σ-blind shells
   were handled with the **scaled** height.  *This is not implemented, and an earlier version of
   this remark was wrong* (two reviewers refuted it with explicit counterexamples: with the
   *unscaled* `T = 2^k` — as in the existing `msum_branch3` — the per-shell `k`-sum is
   `Θ(q·log q)`, so the `m`-sum must beat *two* powers of `q` and the threshold `(5/12)𝓛` is
   optimal).  The correct route is:
   * the cell's zeros do satisfy `|γ| ≤ 2^k/𝓛`, so `finset_sum_le_trivial` (the σ-blind count)
     may be instantiated at the **scaled** height `T = 2^k/𝓛`; this gives the per-cell bound
     `q·c₀·(4 + 2^k/𝓛)·(log(7+2^k/𝓛) + log q + 2)`, whose `k`-sum is `Θ(c₀·q/𝓛)`;
   * the `m`-sum over shells `λ ≥ b𝓛` is then `≍ c₀·q·𝓛^{-1}·q^{-4.9b} = c₀·𝓛^{-1}·q^{1-4.9b}`,
     which decays as soon as `b > 1/4.9 = 0.20408`; with `b = 1021/5000` it is
     `≍ c₀·q^{-0.00058}/𝓛` (this is the form a variant of `msum_branch3` must produce — *not*
     `60000·c₀/q`, which is false for such a threshold);
   * the third term of `finset_boundJMsh` becomes `1920000·c₀·q^{-0.00058}/𝓛`, and the final
     assembly needs `q₀` large enough that `𝓛 ≤ q^{0.00029}` and `4·1920000·c₀ ≤ ε·q^{0.00029}`
     (both hold for `q ≥ q₀(ε, c₀)` since `q^{0.00029}/𝓛 → ∞`), which gives
     `1920000·c₀·𝓛^{-1}·q^{-0.00058} ≤ ε/4`;
   * then `FamilyZeroDensityMesh` is needed only on `σ ∈ [1 - 1021/5000, 4/5] = [0.7958, 0.8]`.
   (`FamilyZeroDensityMesh` is currently *stated* on `1/2 ≤ σ ≤ 4/5`, so that the sharp
   Montgomery exponent applies to it via the bridge; the *current* cell bound only uses it on
   `σ ∈ [7/12, 4/5]`.)

3. **The `λ ≤ 𝓛/5` range of Jutila's input cannot be shrunk by this device.**  For the shells
   `λ ≈ 1` the `m`-sum `Σ_m e^{-4.9m}q^{c(m+1)/𝓛}` is `O(1)`, so the estimate must be *log-free*
   there (a `(log q)^B` factor survives the limit `q → ∞`, `R = R(ε)` being fixed); and for
   `σ` close to `1` the sharp Montgomery exponent `3/(2-σ)` exceeds any constant coefficient, so
   the logarithmic power cannot be absorbed there either.  Thus `FamilyZeroDensityJutila` on
   `σ ≥ 4/5` is the irreducible input, exactly as in the paper (Jutila's Theorem 1).

## Session 4 (final): status of the `[0.7958, 0.8]` shrink

The shrink was *implemented* (the mathematics is complete and checked by hand), but the Lean
port is unfinished, so the verified state of this file keeps the branch-3 threshold at
`(5/12)𝓛`.  A work-in-progress copy of the three affected files is kept in the scratch
directory `.zbak2/wip/` of the workspace root (`FarBoundJM.lean`,
`FarBoundOfJutilaMontgomery.lean`, `JMAuxSh/ShAux.lean`); that copy was written by successive
patch scripts and is **triplicated** (the whole file content appears three times), so it should
be used as a *reference for the final texts* rather than imported.  What is in it, and what
remains:

* `cellBoundJMsh`'s third branch becomes the *scaled* one
  `q·c₀·(4 + 2^k/𝓛)·(log(7 + 2^k/𝓛) + log q + 2)` and its middle branch ends at
  `(1021/5000)𝓛` — done and correct;
* `JMAuxSh.CellMultLeBoundJMsh`'s third case uses `finset_sum_le_trivial` at `T = 2^k/L`
  (with the stronger `|Im z| ≤ 2^k/L` extracted from the cell's definition) — done and correct;
* the new lemma `msum_branch3sc` (threshold `(1021/5000)𝓛`, conclusion
  `≤ 60000·c₀·𝓛·q^{-29/50000}`) — written and *compiling* in the WIP (the early failures in this
  session were in this lemma's pointwise domination step and are fixed there);
* `msum_boundJMsh`/`finset_boundJMsh`/`FarBoundHyp_of_jutila_and_mesh` — patched, but with three
  remaining **engineering** issues, none mathematical:
  1. `finset_boundJMsh`'s hypothesis is still `100000 ≤ Real.log q` while the final theorem now
     supplies `30000000 ≤ Real.log q`; make them agree (the latter is what the third-term
     estimate needs);
  2. the final theorem's q₀ bookkeeping: with `B := max 1 (7680000·c₀/ε)` one wants
     `q₀ ≥ B^{3449}` and `q₀ ≥ ⌈exp(3·10^7)⌉`, then `q^{29/100000} ≥ B^{1.00021} ≥ B` and
     `𝓛 ≤ q^{29/100000}` (from `𝓛 ≥ 3·10^7`, via `Real.pow_div_factorial_le_exp`), which gives
     `1920000·c₀·𝓛·q^{-29/50000} ≤ ε/4`; write these steps with a *local*
     `P := Real.exp (29/100000 * 𝓛)` instead of raw `rpow`s of `q` (the raw forms blow the
     200000-heartbeat budget — `set_option maxHeartbeats` must also be placed where it takes
     effect);
  3. the patch scripts duplicated blocks in the WIP file: keep exactly one copy of each
     declaration.

With those fixed, `FamilyZeroDensityMesh` is needed only on `σ ∈ [0.7958, 0.8]`, and the
σ-blind count (already proved) covers everything below.

## Session 5: the principal character has to be excluded (a correctness fix)

The chain above consumes Jutila's log-free bound in the form `FamilyZeroDensityJutila`, i.e.
`Σ_{χ mod q} N(σ,T,χ) ≤ C(qT)^{(2+ε)(1-σ)}` on `σ ≥ 4/5` — summed over **all** characters.  That
statement is *not* a theorem of the literature.  Its `χ = 1` term is `N(σ,T,χ₀)`, a zero-density
estimate for `ζ`; at `σ = 4/5`, and with `q = 2`, it claims `N(4/5,T) ≪ T^{(2+ε)/5}`, i.e. the
density hypothesis for `ζ` at `σ = 4/5`, which is open: Huxley's bound gives the exponent
`3/(2-σ) = 5/2` there (so `T^{1/2}`, not `T^{2/5}`), and the Guth–Maynard exponent `30/13` is
known only for `σ ≥ 9/10`.

The far-zero mass, however, involves **non-principal** characters only (`FarBoundHyp` sums over
`Finset.univ.erase 1`), so the estimate is needed only in its non-principal form — and *that* is
Jutila's actual theorem, the statement targeted by the shared chapter
`Submission/Work/ZeroDensity` as `Work.ZeroDensity.Jutila.jutilaNonPrincipal`.  The chain has
therefore been re-routed onto the pair

* `Work.LinnikAreas.FamilyZeroDensityJutilaNP` — `Σ_{χ ≠ 1} N(σ,T,χ) ≤ C(qT)^{(2+ε)(1-σ)}` on
  `σ ≥ 4/5`, log-free: **verbatim** `Work.ZeroDensity.Jutila.jutilaNonPrincipal`
  (`familyZeroDensityJutilaNP_of_chapter`, in `Work.LinnikAreas.FarBoundOfJutilaMontgomery`, is
  the identity bridge).  The all-character version implies it
  (`FamilyZeroDensityJutilaNP_of_jutila`), while the converse is exactly the open principal
  statement — so this is a strictly weaker, and *provable*, input;
* `Work.LinnikAreas.FamilyZeroDensityMontgomerySharp` — Montgomery's sharp exponent on
  `σ ≥ 1/2`, with a logarithmic power.  This one is stated for all characters and is a theorem in
  that form: its `χ = 1` part *is* Huxley's `ζ` bound `N(σ,T) ≪ T^{3(1-σ)/(2-σ)}(log T)^B`.  It is
  implied by the chapter's `Work.ZeroDensity.Montgomery.montgomerySharp` through
  `Work.LinnikAreas.JMAuxSh.familyZeroDensityMontgomerySharp_of_montgomerySharp`, and it gives the
  log-free middle-range input `FamilyZeroDensityMesh` by `FamilyZeroDensityMesh_of_montgomerySharp`.

The consumers of the non-principal form are `JMAuxSh.finsetSumLeFamGeNP` (fibre decomposition over
`Finset.univ.erase 1`), `JMAuxSh.CellMultLeBoundJMsh` (branch 1 of the cell bound),
`finset_boundJMsh` and `FarBoundHyp_of_jutila_and_mesh` (all in `Work.LinnikAreas.JMAuxSh` and
`Work.LinnikAreas.FarBoundJM`).  The earlier all-character route (`area2_of_jutila_montgomery`,
`area2_of_jutila_montgomery_mid`, `area2_of_jutila_huxley`, and the bridge
`familyZeroDensityJutila_of_famDensityEpsRange`) is retained and still proved, but its *hypothesis*
`FamilyZeroDensityJutila` is not a theorem (see above), so it should not be used as a target; the
deliverable and all non-principal routes go through `FamilyZeroDensityJutilaNP`.

## Session 5 (continued): the closure is verified

`Work.LinnikAreas.area2_of_chapter` states the two chapter targets **verbatim** as its hypotheses
and derives `Work.LinnikContract.Area2` from them.  It has been *checked against the chapter's
actual statements*: with `Work.ZeroDensity.Jutila.jutilaNonPrincipal` and
`Work.ZeroDensity.Montgomery.montgomerySharp`, the term

    area2_of_chapter Jutila.jutilaNonPrincipal Montgomery.montgomerySharp

elaborates to `Area2` (`familyZeroDensityJutilaNP_of_chapter` is the identity, so the
non-principal Jutila target is *definitionally* `FamilyZeroDensityJutilaNP`).  Hence the moment
the chapter's files are completed, `area2` is closed by replacing its gaps with that
term; no other change is needed.

The middle-range input is maximally flexible: the route only needs `FamilyZeroDensityMesh`
(log-free, coefficient `51/20`, on the window `[1 - 1021/5000, 4/5]` — the *only* range on which
the far-zero decomposition consumes it, namely the middle branch `λ ∈ (𝓛/5, 0.2042𝓛]`; on the
window even the *principal* character is covered by Huxley's classical `ζ` bound), and that is
implied by *any* of

* `FamilyZeroDensityMontgomerySharp` (the sharp large-sieve exponent `3/(2-σ) ≤ 5/2` with a
  logarithmic power) — `FamilyZeroDensityMesh_of_montgomerySharp`;
* `FamilyZeroDensityMontgomery` (the `12/5+ε` exponent with a logarithmic power) —
  `FamilyZeroDensityMesh_of_montgomery`;
* `FamilyZeroDensityHuxley` (the `12/5+ε` exponent, log-free) — the two bridges composed.

So Area 2 closes with `FamilyZeroDensityJutilaNP` plus **either** of the two natural middle-range
targets of the shared chapter (`montgomerySharp`, `huxleyTwelveFifths`).

## Heights

The shell decomposition is dyadic in `|γ| log q`; the `T`-exponent of the density estimate must be
`< 2` (HB §13 uses `q^{3(1−σ)}T^{3/2}` from (1.4)).  In the range used here the exponent of the
estimate is `c(1−σ) ≤ c λ/ log q`, so it is `≪ 1` on the low shells and `≤ 1.8` on the high ones.
-/

namespace Work.LinnikAreas

open Work.LinnikContract

theorem area2 : Work.LinnikContract.Area2 := by
  exact area2_of_logFreeNP Work.ZeroDensity.LogFree.logFreeNP_3979_5000_four

/-- **Area 2 from the far-zero bound alone.**  Heath-Brown's Lemma 13.1 — the box-restricted
explicit formula, uniform in `q` — is proved (`Work.LinnikAreas.ClassIdentity`), and the assembly
`area2_of_classIdentity` turns it plus Lemma 13.2 (`FarBoundHyp`, the smallness of the mass of the
zeros outside the box) into Area 2.  Hence Area 2 holds as soon as the far-zero bound does. -/
theorem area2_of_farBound (h : FarBoundHyp) : Work.LinnikContract.Area2 :=
  area2_of_classIdentity ClassIdentity h

/-- **Area 2 from the family zero-density estimate alone** (Heath-Brown's (1.4)). -/
theorem area2_of_density (h : FamilyZeroDensityHyp) : Work.LinnikContract.Area2 :=
  area2_of_farBound (FarBoundOfDensity h)

/-- **Area 2 from the near-line core alone.**

The σ-blind family count of this workspace, in its log-free form
`Σ_χ N(σ,T,χ) ≤ C_ε (qT)^{1+ε}` (`Work.LinnikAreas.FamilyZeroCountTrivial`), settles Heath-Brown's
(1.4) on the whole range `(12/5+ε)(1−σ) ≥ 1+ε`.  So (1.4) — hence Area 2 — follows from the
near-line core `Work.LinnikAreas.FamilyZeroDensityNearLine` alone. -/
theorem area2_of_nearLine (h : FamilyZeroDensityNearLine) : Work.LinnikContract.Area2 :=
  area2_of_density (familyZeroDensityHyp_of_trivial_and_nearLine FamilyZeroCountTrivial h)

/-- **Area 2 from Jutila's and Huxley's halves of the density input alone** (the two named
theorems that Heath-Brown's (1.4) combines; see the module docstring of
`Work.LinnikAreas.FamilyZeroDensitySplitting`).

**Warning (the first hypothesis is not a theorem).**  `FamilyZeroDensityJutila` sums over **all**
characters mod `q`; at `σ = 4/5` its `χ = 1` term is a density estimate for `ζ` with exponent `2`,
which is not known.  The non-principal form `FamilyZeroDensityJutilaNP` should be used instead
(e.g. through `area2_of_jutila_mesh`); see `Work.LinnikAreas.NOTE_area2_principal_character.md`. -/
theorem area2_of_jutila_huxley (hj : FamilyZeroDensityJutila) (hh : FamilyZeroDensityHuxley) :
    Work.LinnikContract.Area2 :=
  area2_of_nearLine (familyZeroDensityNearLine_of_jutila_huxley hj hh)


/-- **Area 2 from the two targets of the shared chapter `Submission/Work/ZeroDensity`.**

The first hypothesis is written out **verbatim**: it is the statement of
`Work.ZeroDensity.Jutila.jutilaNonPrincipal` (Jutila's log-free bound for the non-principal
characters, `σ ≥ 4/5`); the second is `FamilyZeroDensityMesh`, which is implied by *each* of the
chapter's mid-range targets (Montgomery's sharp exponent, the `12/5` exponent with a logarithmic
power, or Huxley's log-free `12/5`), through the bridges of
`Work.LinnikAreas.FarBoundOfJutilaMontgomery` and `Work.LinnikAreas.JMAuxSh.ZeroDensityBridges`.
Both hypotheses are stated explicitly (rather than by importing the chapter's in-progress proof
modules), so this theorem — a ready closure of `area2` — is stable under changes there. -/
theorem area2_of_chapter
    (hj : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
    (hm : FamilyZeroDensityMesh) :
    Work.LinnikContract.Area2 :=
  area2_of_jutila_mesh (familyZeroDensityJutilaNP_of_chapter hj) hm

end Work.LinnikAreas
