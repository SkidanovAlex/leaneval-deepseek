import Mathlib
import Submission.Work.Peluse.UControl.bandCore
import Submission.Work.Peluse.UControl.petChapter5Holds
import Submission.Work.Peluse.UControl.linFamBoundLinC
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow
import Submission.Work.Peluse.Concat.concatAveraged
import Submission.Work.Peluse.Concat.ofReal_tsum_normSq_eq_pairSum
import Submission.Work.Peluse.Fourier.dftPlancherel
import Submission.Work.Peluse.UControl.piecePetSetup
import Submission.Work.Peluse.UControl.uNormPow_arithIcc_shrink_ambient
import Submission.Work.Peluse.Ulower.boxSumPow_shift_directions

/-!
# `Work.Peluse.UControl.bandStructureAprime` — status, the arithmetic of `Hyp`, and the interface
to the tree's band input

The requested statement (kept verbatim below) is the `A'`-**pointwise** form of the band's structure
input: for each `A' ≥ 1` there are `K₀ ≥ 1`, `cst > 0` such that on every `Hyp`-datum with exponent
`K ≥ K₀`,

  `cst * γ^{K₀} ≤ ‖g₂‖^{2^s}_{U^s_{κ[L]}(symIcc N₁)}`,  `κ = dirCoeff P`, `L = dirLen P δ' N`.

This is verbatim the hypothesis of the `sorry`-free consumer
`Work.Peluse.UControl.pieceBand_of_bandStructureAprime`, and it is the source-faithful shape (the
source's chain `Prop34 : (γ/A)^K ≤ famAvg`, `Prop36S : η^K ≤ A · uNormPow` produces its constants
*after* `A'`).  It is also *verbatim* `Work.Peluse.UControl.TargetAprime P s`
(`bandAprimeDefs.lean`), which is the A'-local "hard" input of the tree's band chapter.

## What is verified in this file

The target `bandStructureAprime` is **proved from the single named residual** through the chain

  `ResidualAprimeStrong2 P  →  ResidualAprimeStrong P  →  ResidualAprime P  →  target`,

whose three arrows are `residualAprimeStrong_of_residualAprimeStrong2`,
`residualAprime_of_residualAprimeStrong` and `bandStructureAprime_of_residualAprime` (the last
discharges the complements of the eleven branches and level-raises `2 → s`).  The three residuals are
*logically equivalent* (`residualAprimeStrong2_of_residualAprimeStrong` is the converse of the first
arrow, `residualAprimeStrong_of_residualAprime` of the second), so the obligation is stated once and
then *carved down* by each newly proved branch; the current frontier is the carved form
`ResidualAprimeStrong2` (its clauses 9–11 are the middle-mass condition, the no-large-modulation
condition and the new no-bulk-periodic-mass condition).  The thresholds are *explicit constants*
(`resEps = 10⁻⁶` for the Fourier/mean/level-one conditions, `resLb = 10⁶` for the direction length);
this is deliberate and *improves* the reduction, since a smaller `resEps` / larger `resLb` shrink the
residual's hypothesis-set while the proved branches (whose constants stay positive) cover the
complement.  The one `sorry` of the file sits on
`residualAprimeStrong2_holds : ResidualAprimeStrong2 P`, which is the band's coarse-scale inverse
theorem in its `Hyp`-normalisation — the *only* remaining obligation, and the same statement as the
tree's `ResidSharpEx` / `BandResidualSmallFourier` / `BandDegenerate` / `FlatBand` family (and as the
level-two dilated-autocorrelation form `DilatedAutocorrL2Crux`).  Everything else in the file is
proved and axiom-clean (`propext, Classical.choice, Quot.sound`).

**The residual's data are pinned to `γ → 1`** (`hyp_gammaPow_lower` below): `Hyp` forces
`1/N₁ ≤ γ^{K₀}`, so on the residual's data the conclusion `cst γ^{K₀} ≤ uNormPow 2 …` is a
*near-constant* lower bound.  That is why every elementary (small-`γ`) mechanism is useless here and
why the two *structural* branches added in session 10 (bulk periodicity, exact coherence) are the
right shape.

### The `Hyp`-arithmetic (proved)

Write `d = deg P`, `W := δ' N` (the PET window), `L = dirLen P δ' N`, `κ = dirCoeff P`.  `Hyp`
contains, besides the scale relations `N₁ ≤ A' N^d`, `N^d ≤ A' γ⁻¹ N₁`, the smallness
`C L ≤ γ^K N₁` and the PET non-degeneracy `C ≤ (γδ')^K W²`, with `C ≥ 1`.  The arithmetic used
throughout is:

* `hyp_petWindow_sqrt` (**new**): `1 ≤ (γδ')^{K/2}·(δ'N)` — the square-root form of the PET
  non-degeneracy;
* `hyp_dirLen_lower` (**new**): `N^{d-1} ≤ 2(γδ')^{K/2}·L` — the direction length is *long*
  (complementing the proved `hyp_dirLen_le_N₁ : L ≤ N₁`);
* `hyp_gamma_N_ge` (**new**): `1 ≤ 2A'·γ^{K/2}·N` — the `x`-range is forced to be large;
* `hyp_mass` (**new**): `γ·N₁ ≤ ∑'_x ‖g₂ x‖` (Peluse's mass lemma `PETTwo.sum_norm_f2_ge`),
  whence `γ ≤ 3√(Lmass N₁ g₂ 2)` (`hypGammaLeSqrtLmass`, delegated) — the residual's data have
  `ℓ²`-mass at least `≈ γ²`;
* `hyp_one_le_petWindow`, `hyp_gamma_mul_pow_le_N₁`, `hyp_petWindow_pow_le`, `hyp_largeness_core`,
  `hyp_delta_le_two_mul_gamma_pow`, `hyp_gamma_pow_ge` (the sharp form of "`γ` is forced large"),
  `hyp_dirLen_le_N₁`, `hyp_mono_K` (`Hyp` is monotone in `K`).
* `hyp_gammaPow_lower` (**new, session 10**): `K₀ ≤ K` ⟹ `1 / N₁ ≤ γ^{K₀}` — the smallness
  conjunct `C·L ≤ γ^K·N₁` with `C ≥ 1` and `L ≥ 1` reads `γ^K ≥ 1/N₁`, and `γ^{K₀} ≥ γ^K`.  Hence
  the residual's conclusion is a *near-constant* bound, and any branch producing a constant bound
  settles it (`le_uNormPow_of_const_le`, also new).  Sharper: raising the PET gauge to the power
  `K₀/(K(K+3))` gives `γ^{K₀} ≥ (2A')⁻¹N^{-2/(K₀+3)}`, i.e. `1 - γ ≲ log(A'N)/K₀²`.

  Note the *direction*: these are **lower** bounds for `γ^{K₀}`, so they do not weaken the target's
  obligation; what they do is confine the residual to the near-maximal-coherence regime (so the size
  branches are provably unavailable there, cf. session 9 §2c) and permit the constant-form
  bookkeeping.  `1 ≤ dirLen P δ' N` is the pre-existing `Hyp.one_le_dirLen` (`assembly.lean`).

### The branches of the target (proved)

At level two (whence every level `s ≥ 2` by `uNormPow_level_raise_win`):

* `targetAprimeTwo_of_largeFourier` — a large Fourier coefficient;
* `targetAprimeTwo_of_largeMean` — a large mean;
* `targetAprimeTwo_of_boundedDirLen` — a bounded direction length (`peelBound`);
* `targetAprimeTwo_of_largeUOne` (**new**) — a large **level-one** box norm (Gowers–Cauchy–Schwarz
  `uNormPow_two_ge_of_uNorm_one`), the sharp exponent `4`);
* `targetAprimeTwo_of_largeA` (**new**) — the **large-`A'`** regime (`N₁ ≤ massDiagC P·A'^4`), by
  transporting the tree's proved `bandConcl_of_massDiagonal` (`ℓ¹`-mass + iterated diagonal peel)
  through `bandHyp_of_hyp` at the *fixed* exponent `4`; this is the only branch that is **not**
  `A'`-uniform, so it restricts the residual to `A' ≲ N₁^{1/4}`;
* `targetAprimeTwo_of_largeLmass` (**new**) — a large **level-two diagonal mass**
  (`Lmass N₁ g₂ 2² ≳ γ⁴L`, from the flatness brick `uNormPow_two_ge_flatness_win'` at the single
  diagonal lag `m = 0`); this is the `ℓ²`-mass branch and it is strictly wider than the peel branch
  (`Lmass ≤ 1` allows `L` up to `1/(18(1+|κ|)γ⁴)`), the `ℓ¹`-mass branch `bandConcl_of_massDiagonal`
  being a different argument whose hypothesis `δN₀ ≤ ‖g₂‖₁` fails on the density family;
* `targetAprimeTwo_of_nearLag`, `targetAprimeTwo_of_nearLagSmallWindow` (**new, this session**) — a
  large **`γ̃`-weighted near-lag moment** (the multiplicative-convolution weights of the *products*
  `e·l`), via the proved `Concat.concatNearLagBound`; this branch sees the pair structure that the
  PET expansion of `Λ` produces for the quadratic `P`, and it covers the density family
  `g₂ = 1_A` (whose autocorrelation is `≈ ρ` at every lag) as soon as `ρ ≫ θ`.  The second form has
  the hypothesis at the **window `N₁`** (`nearLagMoment |κ| L L N₁ g₂`), which is the weaker — hence
  the sharper — of the two (the moment at the fitted window `max N₁ (|κ|L)` is the window ratio
  `ρ ≤ 1` times it, `nearLagMoment_window`); it is the form used in the assembly, hence in the
  residual.
* `targetAprimeTwo_of_largeAutocorr` (**new, this session**) — one large **dilated autocorrelation**
  (`θγ²L ≤ ‖autocorr N₁ g₂ (κe)‖` for some `|e| < L`); the flatness brick evaluated at the single
  term `e` of its `cntW`-sum (`cntW L e ≥ 1` for `|e| < L`).
* `targetAprimeTwo_of_flatProfile` (**new, session 8**) — the **flat profile**: *every* dilated
  autocorrelation at least half of the maximal value `Lmass N₁ g₂ 2`.  Via the tree's proved
  `Work.Peluse.UControl.uNormPow_two_ge_of_flatProfile` (`bandResidualShrink.lean`, whose triangular
  weights sum to `L²`) this gives the level-two conclusion at the **sharp exponent `4`** with a `γ⁴`
  bound and **no `1/L` loss** (whereas the diagonal term `m = 0` alone gives only `γ⁴/L`).
* `targetAprimeTwo_of_manyLargeAutocorr` (**new, session 9**) — the **averaged** flat profile, i.e.
  the *middle-mass* condition `θ·L·(Lmass N₁ g₂ 2/2)² ≤ Σ_{|m| ≤ ⌊L/2⌋} ‖autocorr N₁ g₂ (κm)‖²`
  (on the middle half of the lag range only).  It is *implied by* the pointwise flat profile, so
  this branch covers strictly more data, with the same sharp exponent `4` and the constant
  `θ/(1944(2|κ|+1))` (the underlying brick is
  `Work.Peluse.UControl.uNormPow_two_ge_of_dilatedAutocorrMiddleMass`).
* `targetAprimeTwo_of_largeModUOne` (**new, session 9**) — the **modulation-sharpened level-one**
  branch: `∃β, θγ² ≤ uNormPow 1 (κ[L]) (symIcc N₁) (g₂ · ee (β·))` gives the level-two conclusion at
  the sharp exponent `4` (via the tree's modulation invariance `BoxNorm.uNormPow_mul_ee` for
  `t ≥ 2` and the Gowers–Cauchy–Schwarz level raising `uNormPow_two_ge_of_uNorm_one`).  It sharpens
  `targetAprimeTwo_of_largeUOne` (the case `β = 0`) to the whole modulation orbit; spectrally its
  hypothesis is that *some window of width `1/(κL)` carries `θγ²` of the spectral mass of `g₂`*.

* `targetAprimeTwo_of_bulkPeriodicMass` / `targetAprimeTwo_of_bulkPeriodicConstMass` (**new,
  session 10**) — **bulk quasi-periodicity with a large fourth-moment mass**: `gB ∣ dirCoeff P`, a
  unit multiplier `lam`, a window `2|κ|L ≤ B ≤ N₁` on which `g₂` is `lam`-quasi-periodic, and
  `8(N₁−B) + θN₁ ≤ Σ_{x ∈ symIcc (B−2|κ|L)} ‖g₂ x‖⁴`, give `cst·θ ≤ uNormPow 2 (κ[L]) (symIcc N₁) g₂`
  — a **constant**, hence (by `le_uNormPow_of_const_le`) the target.  This is a one-liner over the
  tree's proved `Work.Peluse.UControl.bandCubeCollapse`, and it is the *only* branch of this file
  whose hypothesis is a **structural** (periodicity) condition rather than a size condition on `g₂`;
  its complement is clause 11 of `ResidualAprimeStrong2` below.
* (satellite module `bandStructureAprimeExactCoherence.lean`) `targetAprimeTwo_of_exactCoherence` —
  the **exact coherence** branch: `g₀ x·g₁ (x+y)·g₂ (x+P y) = μ` (`‖μ‖ = 1`) on every triple of the
  window, together with the fit `4|κ|L ≤ N₁`, gives the target's level-two conclusion.  Proof: the
  tree's proved `bandRigidConcl_of_pieces` applied to the rigidity input `BandRigidityInput P`
  (verbatim `bandRigidityBulk`, delegated) and to the proved `bandCubeCollapse`.

Their complements are exactly `ResidualAprimeStrong` — the *ninth* complement being the
**middle-mass negation** `¬(resEps·L·(Lmass N₁ g₂ 2/2)² ≤ Σ_{|m|≤⌊L/2⌋}‖autocorr N₁ g₂ (κm)‖²)`, which
is *stronger* than the non-flatness clause it replaces (since pointwise flatness implies the
middle-mass condition), and the *tenth* the **modulation clause**
`¬∃β, resEps γ² ≤ uNormPow 1 (κ[L]) (symIcc N₁) (g₂ · ee (β·))` — i.e. *the spectral measure of `g₂`
is spread at scale `1/(κL)`*, the exact negation of the source's §6 major-arc conclusion.  Both
remove in particular the *density family*, the family that saturates the target's exponent.
and the *eleventh* complement the **no-bulk-periodic-mass** clause
`¬ BulkPeriodicMassAt P δ' N N₁ g₂` (session 10), whose positive side is the bulk-periodicity branch
above.  `bandStructureAprime_of_residualAprime` assembles the complements of the branches, and the
sharp residual is reduced to the assembled one by `residualAprime_of_residualAprimeStrong` (one extra
case split: the middle-mass branch); the carved residual `ResidualAprimeStrong2` is reduced to
`ResidualAprimeStrong` by `residualAprimeStrong_of_residualAprimeStrong2` (the case split on
`BulkPeriodicMassAt`).  So a proof of `ResidualAprimeStrong2 P` — or of any input that implies
`ResidualAprime P` (or `ResidualAprimeStrong P`), in particular the tree's `HardInputAt 2 P` via
`bandStructureAprime_of_hardInputAt`, or the tree's weakest band interface `BandAprime P` via
`bandStructureAprime_of_bandAprime` — closes the target.  The single `sorry` of the file is
`residualAprimeStrong2_holds` (the bulk-periodicity-carved form of the residual, equivalent to
`ResidualAprimeStrong`).

### The equidistribution chapter (session 8): where the residual's content sits

By the proved `Concat.uNormPow_two_ge_autocorr_l2` the level-two conclusion follows from
`Σ_{|m|<L} cntW L m · ‖autocorr N₁ g₂ (κm)‖² ≳ L²γ^{K₀}`, and the diagonal term `m = 0` supplies only
`L·Lmass² ≥ Lγ⁴/81` — the obligation is exactly the factor `L`.  Three bricks relating that
`ℓ²`-mass to the *undilated* lags and to the spectrum are now in the tree (all proved, axiom-clean,
siblings of this file):

* `Work.Peluse.UControl.autocorrClassEnergy_le` — **coset domination**: for every residue class
  `r mod κ` the `cntW D`-weighted `ℓ²`-mass of `autocorr N f` on the class `r` is at most its mass
  on the zero class (Fejér positivity `Concat.geoSum_chr_sq_re` + character orthogonality);
* `Work.Peluse.UControl.autocorrZeroClass_ge` — consequently the zero class carries at least
  `1/|κ|`-th of the whole Fejér-weighted `ℓ²`-mass;
* `Work.Peluse.UControl.uNormPow_two_ge_of_cosetMass` — the interface:
  `uNormPow 2 (κ[D]) (symIcc N) f ≥ (3D²|κ|)⁻¹ · Σ_{|v|<D} cntW D v ‖autocorr N f v‖²`.

Read together with `Σ_{|v|<D} cntW D v ‖autocorr N f v‖² = Σ_k cntW D k ‖μ̂(k)‖²` (`μ` the spectral
measure, all Fejér coefficients nonnegative) these say: every *elementary* route to the residual's
conclusion — the diagonal, the coset route, the Jensen/energy bound — gives the same
`γ⁴/L`-strength bound and falls a factor `L` short, and no combination of the residual's nine
complement hypotheses (which are all *upper* bounds, condition (1) in particular putting the
spectrum of `g₂` at the **spread** end) can supply the missing factor.  What is missing is exactly
that the coherence `γ ≤ ‖ΛZ‖` forces the **spectral concentration** of `g₂` at scale `1/L`
(equivalently `Σ_k cntW L k ‖μ̂(k)‖² ≳ L²γ^{K₀}`), i.e. Peluse's major-arc/§6 analysis — for which
the tree's proved `Work.Peluse.Concat.twoDimInverse` (her Lemma 5.3, so far unused by this area) is
the natural inverse-theorem tool.  See `NOTES_bandStructureAprime_SESSION8.md` §3, §7.

### A structural fact about the level (`uNormPow_level_raise_win`)

`uNormPow_level_raise_win (s₀ s) (hss : s₀ ≤ s)` gives `c·(uNormPow s₀ …)^{2^{s-s₀}} ≤ uNormPow s …`:
the norm *increases* with the level up to a power.  Consequences (both used below):

* a lower bound at level `s₀` gives one at every level `s ≥ s₀` with the exponent multiplied by
  `2^{s-s₀}` (this is the assembly's bookkeeping `γ^{K₂·2^{s-2}}`);
* a lower bound at level `s₀ ≥ 3` does **not** give one at level `2` — the norm at level `2` can be
  much *smaller* (it is the U²-norm, the strongest of the family).  Since the target asks for *all*
  `s ≥ 2`, its level-`2` instance is the binding one (equivalently: the target is *equivalent* to its
  level-two instance, `targetAprime_of_levelTwoAprime`).  In particular any input produced by the
  source's §5 ladder at an *unspecified* level `s₀ ≥ 2` (the shape of `Prop36S`) is *not* directly
  usable for the level-`2` instance; the ladder must be pinned to level `2` (the trivial index
  datum, `ℓ = 2`) or assumed at every level, which is why the recorded `SourceT37`/`BandStructure`-
  style inputs carry `∀ s ≥ 2`.

### The `Hyp`-arithmetic of the earlier sessions

Write `d = deg P`, `W := δ' N` (the PET window).  `Hyp` contains, besides the scale relations
`N₁ ≤ A' N^d`, `N^d ≤ A' γ⁻¹ N₁`, the smallness `C L ≤ γ^K N₁` and the PET non-degeneracy
`C ≤ (γδ')^K W²`, with `C ≥ 1`.

* `hyp_one_le_petWindow` : `1 ≤ (γδ')^K W²`;
* `hyp_gamma_mul_pow_le_N₁` : `γ N^d ≤ A' N₁`;
* `hyp_petWindow_pow_le` : `1 ≤ (γδ')^{Kd} W^{2d}`;
* `hyp_largeness_core` : `γ^{2d} ≤ A'^{2d} δ'^{2d} (γδ')^{Kd} N₁^{2d}`, i.e.
  `N₁^{2d} ≥ γ^{2d}(γδ')^{-Kd} δ'^{-2d}A'^{-2d}` — **the `x`-range is forced to be large.**

Combined with the smallness conjunct this gives (via the proved `hypLargenessOrBounded`, which is a
*sibling* module — it imports this one, so it cannot be used here) the dichotomy

  `dirLen P δ' N ≤ C_p·2^{K_p}`  **or**  `C_p ≤ N₁ (γδ')^{K_p}`      (`K ≥ K₀(K_p,C_p,A',P)`),

i.e. on `Hyp`-data with large `K` the direction length is either bounded by an explicit constant
(and the elementary peel bound `Work.Peluse.UControl.peel_bound`,
`c_s γ^{2^s}/L^s ≤ uNormPow s (κ[L]) (symIcc N₁) g₂`, already gives the conclusion) or else the
source's *largeness* side condition holds.  The two *proved* siblings
`fullWindowBandOfDirLenLe` (bounded `L` ⟹ conclusion, from the peel bound) and
`fullWindowBandOfLargeMean` (mean `‖∑_{symIcc N₁} g₂‖ ≥ θγN₁` ⟹ conclusion, from the mean bound
`uNormPow_ge_mean_pow`) dispose of the two elementary branches of the full-window case.

### The `K`-quantifier of the target is redundant

`Hyp` is *monotone decreasing* in `K` (`hyp_mono_K`): since `γ ≤ 1` and `δ' ≤ 1`, the two
`K`-conjuncts `C L ≤ γ^K N₁`, `C ≤ (γδ')^K W²` only get *easier* when `K` is lowered.  Hence a datum
at exponent `K` is also a datum at any exponent `1 ≤ K' ≤ K`, and the target's `∀ K ≥ K₀` is
*equivalent* to its `K = K₀` instance (`bandStructureAprime_fixedK_iff`).  So the target's content
is exactly the **sharp form at the datum's own exponent**:

  for each `A'` there is `K₀` with `cst γ^{K₀} ≤ uNormPow s (κ[L]) (symIcc N₁) g₂`
  on every `Hyp`-datum whose exponent is `K₀`.

(Sharpness: for the "density family" `g₀ = g₁ = 1_{symIcc N₁}`, `g₂ = 1_A` with `|A|/N₁ = ρ`,
`‖Λ‖ ≈ 2ρ ≕ γ` and `uNormPow s ≈ ρ^{2^s} = γ^{2^s}`; so no `K₀ < 2^s` can work, and `K₀ = 2^s` is
the exponent at which the statement is *sharp*.  This is recorded in the docstrings of
`bandCore.lean` and `NOTES_bandCore_SESSION6.md`.)

### The target is exactly the tree's band input

`bandStructureAprime_of_hardInputAt` below: the whole target (at *every* level `s ≥ 2`) follows from
the tree's band input `Work.Peluse.UControl.HardInputAt s P` (`coreChapter_of_hard.lean`) via the
proved `hardness_of_hardAt` — i.e. the target's *content* is precisely the tree's band obligation
`HardInputAt` / `BandAprime` / `BandHardSharpAtAprime` / `AverResidAprime` / `BandDegenerate`
(equivalences recorded in `bandAprimeDefs.lean`, `Submission/Work/UControl/*
targetAprime_of_bandHardSharpAtAprime`, `residSharpAprime_of_averResidAprime`, …).  The converse
(`TargetAprime → BandAprime`) is the proved `bandAprime_of_bandStructureAprime`.

**The `A'`-local (weakest-interface) form** (`bandAprime.lean` session): for the band input in its
weakest shape, `Work.Peluse.UControl.BandAprime P` — the *same* data hypotheses plus the single
extra smallness `c·γ^{2^s}/L^s < c·γ^{K₀}`, whose complement the proved peel bound
`Work.Peluse.UControl.peelBound` settles outright — the file now *proves* the implication
(`bandStructureAprime_of_bandAprime` below) by the dichotomy of `hardness_of_hardAt`.  Hence

  `BandAprime P`  ⟺  `TargetAprime P 2`  ⟺  `ResidualAprime P`  ⟺  `bandStructureAprime`

are all *equivalent* statements (the residual ⟹ target direction is
`bandStructureAprime_of_residualAprime`; the target ⟹ residual direction is trivial, since the
residual's conclusion is the target's conclusion on data carrying the eight extra complement
hypotheses, with the same witnesses).  **Consequence (the reason to state
`bandStructureAprime_of_bandAprime`):** every proved reduction of the band's coarse-scale inverse
theorem in the workspace — `BandAprimeCarved`, `BandAprimeSpectral*`, `BandResidual*`,
`ResidSharpExAprime`, `BandDegenerate`, `BandNearMax` — *implies* `BandAprime P` through proved
implications, and therefore closes this file's target by the one-line instantiation
`bandStructureAprime P s hs A' hA' := bandStructureAprime_of_bandAprime P hband s hs A' hA'`.  So
this file's obligation is exactly the node `Work.Peluse.ucontrol_of_concat`'s obligation, in the
sharpest interface form.

### Why the target itself is not proved here, and where its content sits

With the elementary branches removed, the target's obligation is `Work.Peluse.UControl.FullWindowBand`
(`bandStructureAprimeOfInputs.lean`) together with the source's Theorem 3.7 in its largeness/small
shift regime.  Two facts localise the content further (analysis; the arithmetic is elementary and is
recorded here for the next worker):

* **The shift is small whenever the datum's exponent is used.**  `Hyp`'s smallness with the datum's
  `K`: `⌊δ'N^d⌋ ≥ δ'N^d/2` and `N₁ ≤ A'N^d` give `δ' ≤ 2A'γ^K`.  So the source's
  `A δ' ≤ γ^{K}` (with `A = 2A'`, the *same* exponent `K`) always holds; the previous session's
  extra side condition `δ'^{K_p} ≤ γ^{K_p}` in `SourceBand` is *stronger than necessary*.
* **The `C`-dichotomy.**  The source's Theorem 3.7 (`Defs.lean : Theorem37Chapter`, or Peluse's
  Thm 3.7 itself) has its own constant `C_src` and exponent `K_src`, and its hypothesis is
  `C_src L ≤ γ^{K_src} N₁`.  Given a `Hyp`-datum with exponent `K ≥ 2K_src`:
  `C_src L ≤ (C_src/C)·γ^K N₁ ≤ (C_src/C)·γ^{K_src} N₁` (using `γ ≤ 1` and `K ≥ K_src`), so the
  source's hypothesis holds as soon as `C ≥ C_src`.  Hence the *only* data the source's theorem does
  not reach are those with `C < C_src` — a **bounded** smallness constant — and there the conclusion
  is the "constant-strength coherence ⟹ constant box norm" statement (Peluse's Theorem 3.3/3.7
  inverse theorem, the tree's `BandHard`/`FlatBand`/`AverResidAprime`, the single open input of the
  whole band chapter).

  What makes the bounded-`C` residual genuinely hard (and not an artefact of the normalization) is
  the *flatness* of the dilated autocorrelations: by the proved
  `Concat.uNormPow_two_ge_autocorr_l2` the target follows from
  `∑_{|u|<L} cntW L u·‖autocorr N₁ g₂ (κu)‖² ≳ L²δ^{2^s}`; the single term `u = 0` supplies only
  `L·‖autocorr N₀‖² ≥ Lδ^{2^s}` (from the ℓ²-mass bound `mass_bound_of_lambdaZ`), i.e. the
  obligation is exactly the *factor `L`*: the autocorrelations at the dilated lags `κu`, `1 ≤ |u| < L`,
  must be comparable to `autocorr 0`.  The density family has exactly this flatness (a random `A` of
  density `ρ` has `autocorr (κu) ≈ ρ²` for `u ≠ 0`), which is why it is the extremal example, and
  the "dual-matched"/chirp examples (`NOTES_bandDegenerateFull_SESSION55.md`) show that no elementary
  Fourier or sup-norm bound can see it.

**Verdict.**  The statement is *true* (it is Peluse's Theorem 3.7 in the `Hyp`-normalisation, the
constants being A'-dependent as the source's are); it is **not** derivable from the present state of
the workspace, because its content is exactly the band's coarse-scale inverse theorem which the whole
area has open (`BandHard`, `ResidSharpEx`, `AverResidAprime`, `AbstractFlatBand`, `BandDegenerate`,
`HardInputAt`, …).  `declare_false` is therefore not appropriate: the statement is not false, it is
the frontier; and the tree's own `NOTES_UControl_pieceBand_SESSION.md` reached the same conclusion.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- **The PET window is never degenerate**: `Hyp`'s PET non-degeneracy with `C ≥ 1`. -/
lemma hyp_one_le_petWindow {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    1 ≤ (γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2 := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  exact le_trans hC1 hpet

/-- **The `x`-range against `N^d`**, cleared of `γ`: `Hyp`'s second scale relation times `γ > 0`. -/
lemma hyp_gamma_mul_pow_le_N₁ {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    γ * (N : ℝ) ^ P.natDegree ≤ A' * (N₁ : ℝ) := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have h1 : γ * (N : ℝ) ^ P.natDegree ≤ γ * (A' * γ⁻¹ * (N₁ : ℝ)) :=
    mul_le_mul_of_nonneg_left hsc2 hγ0.le
  have h2 : γ * (A' * γ⁻¹ * (N₁ : ℝ)) = A' * (N₁ : ℝ) := by
    field_simp
  exact le_of_le_of_eq h1 h2

/-- **The PET window raised to the `d`-th power**: `1 ≤ (γδ')^{Kd} W^{2d}`. -/
lemma hyp_petWindow_pow_le {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    1 ≤ (γ * δ') ^ (K * P.natDegree) * (δ' * (N : ℝ)) ^ (2 * P.natDegree) := by
  have h1 : 1 ≤ ((γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2) ^ P.natDegree :=
    one_le_pow₀ (hyp_one_le_petWindow h)
  have heq : (γ * δ') ^ (K * P.natDegree) * (δ' * (N : ℝ)) ^ (2 * P.natDegree)
      = ((γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2) ^ P.natDegree := by
    conv_lhs => rw [pow_mul, pow_mul, ← mul_pow]
  exact heq ▸ h1

/-- **The core largeness inequality.**  On every `Hyp`-datum, with `d = deg P`:

  `γ^{2d} ≤ A'^{2d} · δ'^{2d} · (γδ')^{Kd} · N₁^{2d}`,

equivalently `N₁^{2d} ≥ γ^{2d}(γδ')^{-Kd}δ'^{-2d}A'^{-2d}`: the `x`-range is forced to be large by the
PET non-degeneracy (through `N^d ≤ A'γ⁻¹N₁`), independently of the smallness conjunct. -/
lemma hyp_largeness_core {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    γ ^ (2 * P.natDegree)
      ≤ (A' ^ (2 * P.natDegree)) * (δ' ^ (2 * P.natDegree))
        * ((γ * δ') ^ (K * P.natDegree)) * ((N₁ : ℝ) ^ (2 * P.natDegree)) := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have hpet'' : 1 ≤ (γ * δ') ^ (K * P.natDegree) * (δ' ^ (2 * P.natDegree)
      * (N : ℝ) ^ (2 * P.natDegree)) := by
    have hp := hyp_petWindow_pow_le ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2,
      hC1, hK1, hsmall, hpet, hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩
    have heq2 : (δ' * (N : ℝ)) ^ (2 * P.natDegree)
        = δ' ^ (2 * P.natDegree) * (N : ℝ) ^ (2 * P.natDegree) := by
      rw [mul_pow]
    rwa [heq2] at hp
  have hγN : γ * (N : ℝ) ^ P.natDegree ≤ A' * (N₁ : ℝ) :=
    hyp_gamma_mul_pow_le_N₁ ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2,
      hC1, hK1, hsmall, hpet, hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩
  -- `γ^{2d} N^{2d} ≤ A'^{2d} N₁^{2d}`
  have hγN2 : γ ^ (2 * P.natDegree) * (N : ℝ) ^ (2 * P.natDegree)
      ≤ A' ^ (2 * P.natDegree) * (N₁ : ℝ) ^ (2 * P.natDegree) := by
    have hpow : (γ * (N : ℝ) ^ P.natDegree) ^ (2 * P.natDegree)
        ≤ (A' * (N₁ : ℝ)) ^ (2 * P.natDegree) :=
      pow_le_pow_left₀ (mul_nonneg hγ0.le (by positivity)) hγN (2 * P.natDegree)
    rw [mul_pow, mul_pow] at hpow
    have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNd : (N : ℝ) ^ (2 * P.natDegree) ≤ ((N : ℝ) ^ P.natDegree) ^ (2 * P.natDegree) := by
      have hle : 2 * P.natDegree ≤ P.natDegree * (2 * P.natDegree) := by
        have : 1 ≤ P.natDegree := by omega
        nlinarith
      calc (N : ℝ) ^ (2 * P.natDegree) ≤ (N : ℝ) ^ (P.natDegree * (2 * P.natDegree)) :=
            pow_le_pow_right₀ h1N hle
        _ = ((N : ℝ) ^ P.natDegree) ^ (2 * P.natDegree) := by rw [pow_mul]
    calc γ ^ (2 * P.natDegree) * (N : ℝ) ^ (2 * P.natDegree)
        ≤ γ ^ (2 * P.natDegree) * ((N : ℝ) ^ P.natDegree) ^ (2 * P.natDegree) :=
          mul_le_mul_of_nonneg_left hNd (by positivity)
      _ ≤ A' ^ (2 * P.natDegree) * (N₁ : ℝ) ^ (2 * P.natDegree) := hpow
  calc γ ^ (2 * P.natDegree)
      ≤ γ ^ (2 * P.natDegree)
        * ((γ * δ') ^ (K * P.natDegree) * δ' ^ (2 * P.natDegree)
            * (N : ℝ) ^ (2 * P.natDegree)) := by
        have h1 : (1 : ℝ) ≤ (γ * δ') ^ (K * P.natDegree) * δ' ^ (2 * P.natDegree)
            * (N : ℝ) ^ (2 * P.natDegree) := by
          simpa only [mul_assoc] using hpet''
        calc γ ^ (2 * P.natDegree) = γ ^ (2 * P.natDegree) * 1 := (mul_one _).symm
          _ ≤ γ ^ (2 * P.natDegree)
              * ((γ * δ') ^ (K * P.natDegree) * δ' ^ (2 * P.natDegree)
                  * (N : ℝ) ^ (2 * P.natDegree)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (γ ^ (2 * P.natDegree) * (N : ℝ) ^ (2 * P.natDegree))
        * ((γ * δ') ^ (K * P.natDegree) * δ' ^ (2 * P.natDegree)) := by ring
    _ ≤ (A' ^ (2 * P.natDegree) * (N₁ : ℝ) ^ (2 * P.natDegree))
        * ((γ * δ') ^ (K * P.natDegree) * δ' ^ (2 * P.natDegree)) :=
        mul_le_mul_of_nonneg_right hγN2 (by positivity)
    _ = (A' ^ (2 * P.natDegree)) * (δ' ^ (2 * P.natDegree))
        * ((γ * δ') ^ (K * P.natDegree)) * ((N₁ : ℝ) ^ (2 * P.natDegree)) := by ring

/-! ## The `K`-monotonicity of `Hyp`, and the redundancy of the target's `K`-quantifier -/

/-- **`Hyp` is monotone decreasing in the exponent `K`.**  Since `γ ≤ 1` and `δ' ≤ 1`, both
`K`-dependent conjuncts of `Hyp` (`C·L ≤ γ^K N₁` and `C ≤ (γδ')^K(δ'N)²`) hold for every smaller
exponent `1 ≤ K' ≤ K`.  So every `Hyp`-datum at exponent `K` is a `Hyp`-datum at exponent `K'`. -/
lemma hyp_mono_K {P : Polynomial ℤ} {A' C : ℝ} {K K' : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (hK : K' ≤ K) (h1 : 1 ≤ K')
    (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    Hyp P A' C K' N N₁ g₀ g₁ g₂ γ δ' := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have hγK : γ ^ K ≤ γ ^ K' := pow_le_pow_of_le_one hγ0.le hγ1 hK
  have hγδ1 : γ * δ' ≤ 1 := by
    have h := mul_le_mul hγ1 hδ1 hδ0.le (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  have hγδK : (γ * δ') ^ K ≤ (γ * δ') ^ K' :=
    pow_le_pow_of_le_one (mul_nonneg hγ0.le hδ0.le) hγδ1 hK
  refine ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, h1, ?_, ?_, hs0, hs1, hs2,
    hb0, hb1, hb2, hΛ⟩
  · calc C * (dirLen P δ' N : ℝ) ≤ γ ^ K * (N₁ : ℝ) := hsmall
      _ ≤ γ ^ K' * (N₁ : ℝ) := mul_le_mul_of_nonneg_right hγK (by positivity)
  · calc C ≤ (γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2 := hpet
      _ ≤ (γ * δ') ^ K' * (δ' * (N : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hγδK (by positivity)

/-- **The target's `K`-quantifier is redundant.**  The statement of `bandStructureAprime` (with
`∀ K ≥ K₀`) is *equivalent* to its instance at `K = K₀`: the forward direction is the instance at
`K := K₀`, and the backward direction converts a datum at exponent `K ≥ K₀` into one at exponent `K₀`
by `hyp_mono_K`.

So the target asserts exactly the *sharp form* at the datum's own exponent — the form in which the
density family `g₂ = 1_A` shows the exponent `2^s` to be optimal. -/
theorem targetAprime_fixedK_iff (P : Polynomial ℤ) (s : ℕ) :
    (∀ A' : ℝ, 1 ≤ A' → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ cst : ℝ, 0 < cst ∧
      ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
        Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
        cst * γ ^ K₀ ≤ uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂)
    ↔
    (∀ A' : ℝ, 1 ≤ A' → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ cst : ℝ, 0 < cst ∧
      ∀ C : ℝ, 1 ≤ C →
      ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
        Hyp P A' C K₀ N N₁ g₀ g₁ g₂ γ δ' →
        cst * γ ^ K₀ ≤ uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂) := by
  constructor
  · intro h A' hA'
    obtain ⟨K₀, hK₀, cst, hcst, hb⟩ := h A' hA'
    exact ⟨K₀, hK₀, cst, hcst, fun C hC N N₁ g₀ g₁ g₂ γ δ' hH =>
      hb C hC K₀ le_rfl N N₁ g₀ g₁ g₂ γ δ' hH⟩
  · intro h A' hA'
    obtain ⟨K₀, hK₀, cst, hcst, hb⟩ := h A' hA'
    exact ⟨K₀, hK₀, cst, hcst, fun C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH =>
      hb C hC N N₁ g₀ g₁ g₂ γ δ' (hyp_mono_K hK hK₀ hH)⟩

/-! ## The interface to the tree's band input -/

/-! ## Bridges supplied by this session's two new modules

`Submission/Work/Peluse/PET/pet_step_subtracted.lean` proves the PET step *without* the gauge
hypothesis of `Work.Peluse.PET.pet_step`; the corollary below is the form in which a consumer
(from the *averaged* form of Peluse's Lemma 4.10 needed by the assembly of `Prop34` — see
`NOTES_UControl_peluseProp34.md` §3, route (B) — and from `NOTES_bandStructureAprime_SESSION3.md`)
wants it: from *any* lower bound `γ ≤ ‖Λ‖²` it produces `γ ≤ 12(1+γ')·R + 100(1+γ')(Cne+1)γ'`,
with the van der Corput error displayed. -/

/-! ## Peluse's Proposition 3.4 (the `Prop34` route to the target's content)

The target below (`bandStructureAprime` = `TargetAprime P s`) is the `Hyp`-normalisation of
Peluse's Theorem 3.7, i.e. of the box-norm inverse theorem whose published proof is
`Prop 3.4 + Prop 3.6 + the Cauchy–Schwarz step`.  The *only provable* route to it is that source
route, and the `Prop 3.6` half is the §5 ladder (`UControl/prop36S.lean`, `petChapter5Holds.lean`).
This section contributes the `Prop 3.4` half: its **assembly** from the two chapters of its proof,

* `PetChapter5 P` — Peluse's Lemma 4.9, **proved** in `UControl/petChapter5Holds.lean`;
* the averaged Lemma 4.10 with a *linear* gauge and the `(2·Cne+1)²` normalisation of the
  per-fibre `LinFibBound` on the left of the inequality — the statement
  `Work.Peluse.UControl.linFamBoundLinC`, delegated to
  `Submission/Work/Peluse/UControl/linFamBoundLinC.lean`.

**A statement-level bug found and repaired this session.**  The interface recorded in
`UControl/peluseProp34Defs2.lean` (`LinFamBoundLin`) is **FALSE**: its conclusion is stated at the
`Cne`-parametrised support `symIcc ((4·Cne+1)·N)` while `Cne` is universally quantified and occurs
in the hypotheses only through the shift bound `|petDir·y+β| ≤ Cne·N`, which *relaxes* as `Cne`
grows; since `boxNormPow` is `|S|^{-1}` times a quantity independent of `S`
(`boxSumPow_eq_inv_mul_common`), letting `Cne → ∞` drives the right-hand side to `0` while the left
side stays fixed.  The repair (implemented as `LinFamBoundLinC'` here, mirroring the per-fibre
`LinFibBound`, whose statement is *proved* in `UControl/peluseProp34Defs.lean`) moves the
`(2·Cne+1)²`-loss to the *left* of the inequality and keeps the natural support
`symIcc ((4·Cne+1)·N)`.

With these two inputs the assembly below is pure bookkeeping: the three transfers
`boxNormPow_mono_symIcc` (proved in `UControl/uNormPow_arithIcc_shrink_ambient.lean`),
`BoxNorm.boxNormPow_le_one` and the local `boxNormPow_le_boxNorm'`, the unfolding of `famNorm` into
the `petDir`-directions, and definite inequalities in the scale constant `A` whose coefficients are
all produced before `A`. -/

/-- **The corrected averaged Lemma 4.10** (the statement delegated as
`Work.Peluse.UControl.linFamBoundLinC`): the averaged form of Peluse's Lemma 4.10 with a *linear*
gauge `δ' ≤ γ/C4` and the per-fibre normalisation `(2·Cne+1)²` on the **left** of the conclusion.
This is the form the assembly of `Prop34` consumes; the version recorded in
`peluseProp34Defs2.lean` is false (see the section docstring). -/
def LinFamBoundLinC' (P : Polynomial ℤ) (D : IdxDatum) : Prop :=
  ∃ K4 : ℕ, 1 ≤ K4 ∧ ∃ C4 : ℝ, 1 ≤ C4 ∧
    ∀ (N M : ℕ) (f : ℤ → ℂ) (δ' γ : ℝ) (Cne : ℕ)
      (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
      (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
      2 ≤ P.natDegree → 2 ≤ Fintype.card (D.I (P.natDegree - 1)) → 1 ≤ N → 2 ≤ M →
      0 < δ' → 0 < γ → γ ≤ 1 → 1 ≤ Cne →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      (∀ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
        ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
          |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i| ≤ (Cne : ℤ) * (N : ℤ)) →
      1 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      γ ≤ linFamAvg D P.natDegree P.leadingCoeff N M (⌊δ' * (M : ℝ)⌋).toNat f b β →
      δ' ≤ γ / C4 →
      (γ / (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4 ≤
        (((D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat).card : ℕ) : ℝ)⁻¹ *
          ∑ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
            boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
              (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
                arithIcc (petDir D P.natDegree P.leadingCoeff a i) (⌊δ' * (M : ℝ)⌋).toNat)
              (symIcc ((4 * Cne + 1) * N)) f

lemma boxNormPow_le_boxNorm' {t : ℕ} {Q : Fin t → Finset ℤ} {S : Finset ℤ} {f : ℤ → ℂ}
    (h1 : boxNormPow t Q S f ≤ 1) : boxNormPow t Q S f ≤ boxNorm t Q S f := by
  have hx0 : (0 : ℝ) ≤ ‖boxSumPow t Q S f‖ := norm_nonneg _
  rcases eq_or_lt_of_le hx0 with hzero | hpos
  · rw [boxNorm, boxNormPow, ← hzero]
    simp
  · have hx1 : ‖boxSumPow t Q S f‖ ≤ 1 := h1
    have hexp : 1 / ((2 : ℝ) ^ t) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    have hkey := Real.rpow_le_rpow_of_exponent_ge hpos hx1 hexp
    rw [Real.rpow_one] at hkey
    simpa only [boxNorm, boxNormPow] using hkey

lemma supp_of_supportIn {N : ℕ} {f : ℤ → ℂ} (h : SupportIn f N) :
    ∀ x : ℤ, x ∉ symIcc N → f x = 0 := by
  intro x hx
  apply h
  by_contra hlt
  exact hx (by
    rw [symIcc, Finset.mem_Icc]
    have hle : x.natAbs ≤ N := Nat.not_lt.mp hlt
    have h1 : (-x) ≤ (x.natAbs : ℤ) := by
      have := Int.le_natAbs (a := -x)
      rwa [Int.natAbs_neg] at this
    have h2 : x ≤ (x.natAbs : ℤ) := Int.le_natAbs (a := x)
    have h3 : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
    exact ⟨by omega, by omega⟩)

theorem prop34_of_chapters (P : Polynomial ℤ) (hpet : PetChapter5 P)
    (hfam : ∀ D : IdxDatum, LinFamBoundLinC' P D) : Prop34 P := by
  obtain ⟨D, hDcard, Cne₀, K₀, Cst₁, hCne₀, hK₀, hCst₁, hpetA⟩ := hpet
  obtain ⟨K4, hK4, C4, hC4, hfamH⟩ := hfam D
  have hC4pos : (0 : ℝ) < C4 := lt_of_lt_of_le zero_lt_one hC4
  have hCst₁pos : (0 : ℝ) < Cst₁ := lt_of_lt_of_le zero_lt_one hCst₁
  refine ⟨D, K₀ * K4 + 1, by omega, ?_⟩
  intro A₀ hA₀1
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = max 1 (max A₀ (max (Cst₁ * C4)
      ((Cst₁ * C4) ^ K4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ (2 * K4))))) := ⟨_, rfl⟩
  have hA1 : (1 : ℝ) ≤ A := by rw [hAdef]; exact le_max_left _ _
  have hAA₀ : A₀ ≤ A := by
    rw [hAdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hACst : Cst₁ * C4 ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hAbig : (Cst₁ * C4) ^ K4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ (2 * K4)) ≤ A := by
    rw [hAdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hCstC4pos : (0 : ℝ) < Cst₁ * C4 := mul_pos hCst₁pos hC4pos
  refine ⟨A, hA1, ?_⟩
  intro N M F γ δ' hd hN hM hNsc hMsc hγ0 hγ1 hδ'0 hwin hwin2 hFb hFs hΛ
  -- the chapter at scale A
  obtain ⟨Kc, hKc2, hKcK₀, Cst₀, hCst₀1, hCst₀le, Cne, hCne1, hCnele, hch⟩ := hpetA A hA1
  have hKc_le : Kc ≤ K₀ * K4 + 1 := by
    have h1 : Kc ≤ K₀ := hKcK₀
    have h2 : K₀ ≤ K₀ * K4 := Nat.le_mul_of_pos_right K₀ (by omega)
    omega
  have hγK : γ ^ (K₀ * K4 + 1) ≤ γ ^ Kc :=
    pow_le_pow_of_le_one hγ0.le hγ1 hKc_le
  have hAδ' : A * δ' ≤ γ ^ Kc := le_trans hwin hγK
  have hMsc' : (M : ℝ) ^ P.natDegree ≤ A * γ⁻¹ * (N : ℝ) := by
    have h : (M : ℝ) ^ P.natDegree ≤ A₀ * γ⁻¹ * (N : ℝ) := by
      have h1 : γ⁻¹ * (γ * (M : ℝ) ^ P.natDegree) ≤ γ⁻¹ * (A₀ * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hMsc (by positivity)
      have h2 : γ⁻¹ * (γ * (M : ℝ) ^ P.natDegree) = (M : ℝ) ^ P.natDegree := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hγ0), one_mul]
      rw [h2] at h1
      calc (M : ℝ) ^ P.natDegree ≤ γ⁻¹ * (A₀ * (N : ℝ)) := h1
        _ = A₀ * γ⁻¹ * (N : ℝ) := by ring
    calc (M : ℝ) ^ P.natDegree ≤ A₀ * γ⁻¹ * (N : ℝ) := h
      _ ≤ A * γ⁻¹ * (N : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hAA₀ (by positivity)
  obtain ⟨b, β, hβbd, hlevel⟩ := hch N M F γ δ' hd hN hM (le_trans hNsc (by
      calc A₀ * (M : ℝ) ^ P.natDegree ≤ A * (M : ℝ) ^ P.natDegree :=
            mul_le_mul_of_nonneg_right hAA₀ (by positivity)))
    hMsc' hγ0 hγ1 hδ'0 hAδ' hwin2 hFb hFs hΛ
  -- the two target quantities
  have hCst₀pos : (0 : ℝ) < Cst₀ := lt_of_lt_of_le zero_lt_one hCst₀1
  have hm : 2 ≤ Fintype.card (D.I (P.natDegree - 1)) := hDcard
  have hγs0 : (0 : ℝ) < γ ^ Kc / Cst₀ := by positivity
  have hγs1 : γ ^ Kc / Cst₀ ≤ 1 := by
    rw [div_le_one hCst₀pos]
    exact le_trans (pow_le_one₀ hγ0.le hγ1) hCst₀1
  have hγs_le : γ ^ Kc / Cst₀ ≤ linFamAvg D P.natDegree P.leadingCoeff N M
      (⌊δ' * (M : ℝ)⌋).toNat (F ⟨P.natDegree, Nat.lt_succ_self _⟩) b β := by
    rw [div_le_iff₀ hCst₀pos]
    rw [mul_comm]
    exact hlevel
  have hgauge : δ' ≤ (γ ^ Kc / Cst₀) / C4 := by
    rw [div_div]
    have h1 : A * δ' ≤ γ ^ Kc := hAδ'
    have h2 : δ' ≤ γ ^ Kc / A := by
      rw [le_div_iff₀ hApos]
      linarith [h1]
    have hden : Cst₀ * C4 ≤ A := by
      have h1 : Cst₀ * C4 ≤ Cst₁ * C4 :=
        mul_le_mul_of_nonneg_right hCst₀le hC4pos.le
      exact le_trans h1 hACst
    refine le_trans h2 ?_
    rw [div_le_div_iff₀ hApos (by positivity)]
    exact mul_le_mul_of_nonneg_left hden (by positivity)
  have hδ'le1 : δ' ≤ 1 := by
    have h2 : A * δ' ≤ 1 := by
      have h3 : γ ^ (K₀ * K4 + 1) ≤ 1 := pow_le_one₀ hγ0.le hγ1
      linarith [hwin, h3]
    nlinarith [h2, hA1]
  have hM2 : 2 ≤ M := by
    have h1 : (⌊δ' * (M : ℝ)⌋).toNat ≤ M := by
      rw [Int.toNat_le]
      have h2 : ⌊δ' * (M : ℝ)⌋ ≤ ⌊(M : ℝ)⌋ := Int.floor_mono (by
        calc δ' * (M : ℝ) ≤ 1 * (M : ℝ) :=
              mul_le_mul_of_nonneg_right hδ'le1 (Nat.cast_nonneg M)
          _ = (M : ℝ) := one_mul _)
      rwa [Int.floor_natCast] at h2
    omega
  have hchild := hfamH N M (F ⟨P.natDegree, Nat.lt_succ_self _⟩) δ' (γ ^ Kc / Cst₀) Cne b β
    hd hm hN hM2 hδ'0 hγs0 hγs1 hCne1 (fun x => hFb _ x) (fun x hx => hFs _ x hx) hβbd
    (by omega) hγs_le hgauge
  -- ## the averaged box-norm power dominates
  have havg_le : (((D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat).card : ℕ) : ℝ)⁻¹ *
        ∑ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
          boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
            (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
              arithIcc (petDir D P.natDegree P.leadingCoeff a i) (⌊δ' * (M : ℝ)⌋).toNat)
            (symIcc ((4 * Cne + 1) * N)) (F ⟨P.natDegree, Nat.lt_succ_self _⟩)
      ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N
          (F ⟨P.natDegree, Nat.lt_succ_self _⟩) := by
    rw [IdxDatum.famAvg]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a ha => ?_) (by positivity)
    have hmono := boxNormPow_mono_symIcc (t := Fintype.card (D.I (P.natDegree - 1)))
      (Q := fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
        arithIcc (petDir D P.natDegree P.leadingCoeff a i) (⌊δ' * (M : ℝ)⌋).toNat)
      (N := N) (N' := (4 * Cne + 1) * N) (by nlinarith [hCne1])
      (F ⟨P.natDegree, Nat.lt_succ_self _⟩)
    have hpow1 : boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
        (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
          arithIcc (petDir D P.natDegree P.leadingCoeff a i) (⌊δ' * (M : ℝ)⌋).toNat)
        (symIcc N) (F ⟨P.natDegree, Nat.lt_succ_self _⟩) ≤ 1 :=
      BoxNorm.boxNormPow_le_one (hFb ⟨P.natDegree, Nat.lt_succ_self _⟩)
        (supp_of_supportIn (hFs ⟨P.natDegree, Nat.lt_succ_self _⟩))
    have hle := boxNormPow_le_boxNorm' hpow1
    have hfam : D.famNorm P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N a
        (F ⟨P.natDegree, Nat.lt_succ_self _⟩)
        = boxNorm (Fintype.card (D.I (P.natDegree - 1)))
            (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
              arithIcc (petDir D P.natDegree P.leadingCoeff a i) (⌊δ' * (M : ℝ)⌋).toNat)
            (symIcc N) (F ⟨P.natDegree, Nat.lt_succ_self _⟩) := by
      simp only [IdxDatum.famNorm, petDir]
    rw [hfam]
    exact le_trans hmono hle
  have hchain : ((γ ^ Kc / Cst₀) / (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4
      ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N
          (F ⟨P.natDegree, Nat.lt_succ_self _⟩) := le_trans hchild havg_le
  -- ## the final arithmetic
  have hKcK4 : Kc * K4 ≤ K₀ * K4 := Nat.mul_le_mul_right K4 hKcK₀
  have hγpow : γ ^ (K₀ * K4 + 1) ≤ γ ^ (Kc * K4) :=
    pow_le_pow_of_le_one hγ0.le hγ1 (by omega)
  have hCneR : (Cne : ℝ) ≤ (Cne₀ : ℝ) * A := hCnele
  have h2Cne : ((2 * Cne + 1 : ℕ) : ℝ) ≤ ((2 * Cne₀ + 1 : ℕ) : ℝ) * A := by
    push_cast
    nlinarith [hCneR, hA1]
  have hD₂le : Cst₀ * (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))
      ≤ (Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) * A ^ 2 := by
    have hsq : (((2 * Cne + 1 : ℕ) : ℝ)) ^ 2 ≤ ((((2 * Cne₀ + 1 : ℕ) : ℝ)) * A) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2Cne 2
    have h1 : C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2)
        ≤ C4 * ((((2 * Cne₀ + 1 : ℕ) : ℝ)) * A) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hC4pos.le
    calc Cst₀ * (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))
        ≤ Cst₁ * (C4 * ((((2 * Cne₀ + 1 : ℕ) : ℝ)) * A) ^ 2) :=
          mul_le_mul hCst₀le h1 (by positivity) hCst₁pos.le
      _ = (Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) * A ^ 2 := by ring
  have hE : (Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) ^ K4 ≤ A ^ ((K₀ - 2) * K4 + 1) := by
    have heq : (Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) ^ K4
        = (Cst₁ * C4) ^ K4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ (2 * K4)) := by
      rw [show Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))
            = (Cst₁ * C4) * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2) by ring, mul_pow, ← pow_mul]
    rw [heq]
    exact le_trans hAbig (le_trans (le_of_eq (pow_one A).symm)
      (pow_le_pow_right₀ hA1 (by omega)))
  have hD₂pow : (Cst₀ * (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4 ≤ A ^ (K₀ * K4 + 1) := by
    have heq : ((Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) * A ^ 2) ^ K4
        = (Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) ^ K4 * A ^ (2 * K4) := by
      rw [mul_pow, ← pow_mul]
    calc (Cst₀ * (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4
        ≤ ((Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) * A ^ 2) ^ K4 :=
          pow_le_pow_left₀ (by positivity) hD₂le K4
      _ = (Cst₁ * (C4 * (((2 * Cne₀ + 1 : ℕ) : ℝ) ^ 2))) ^ K4 * A ^ (2 * K4) := heq
      _ ≤ A ^ ((K₀ - 2) * K4 + 1) * A ^ (2 * K4) :=
          mul_le_mul_of_nonneg_right hE (by positivity)
      _ = A ^ (K₀ * K4 + 1) := by
          rw [← pow_add]
          have h1 : (K₀ - 2) * K4 + 2 * K4 = K₀ * K4 := by
            rw [← Nat.add_mul, Nat.sub_add_cancel (by omega : 2 ≤ K₀)]
          rw [show (K₀ - 2) * K4 + 1 + 2 * K4 = K₀ * K4 + 1 by omega]
  have hmid : γ ^ (K₀ * K4 + 1) / A ^ (K₀ * K4 + 1)
      ≤ γ ^ (Kc * K4) / (Cst₀ * (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4 := by
    have hD₂pos : (0 : ℝ) < Cst₀ * (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2)) := by positivity
    rw [div_le_div_iff₀ (pow_pos hApos _) (pow_pos hD₂pos _)]
    exact mul_le_mul hγpow hD₂pow (by positivity) (by positivity)
  have hRHS : ((γ ^ Kc / Cst₀) / (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4
      = γ ^ (Kc * K4) / (Cst₀ * (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4 := by
    rw [div_div, div_pow, ← pow_mul]
  have hgoal : (γ / A) ^ (K₀ * K4 + 1)
      ≤ ((γ ^ Kc / Cst₀) / (C4 * (((2 * Cne + 1 : ℕ) : ℝ) ^ 2))) ^ K4 := by
    rw [hRHS, div_pow]
    exact hmid
  exact le_trans hgoal hchain


/-- **Peluse's Proposition 3.4, modulo the corrected averaged Lemma 4.10.**  The PET chapter is the
proved `UControl/petChapter5Holds`; the only remaining input is the delegated
`Work.Peluse.UControl.linFamBoundLinC`.  So `Prop34 P` — Peluse's §4, the first half of the source
route to this file's target — is one instantiation away. -/
theorem prop34Holds_of_linFamBoundLinC (P : Polynomial ℤ)
    (hfam : ∀ D : IdxDatum, LinFamBoundLinC' P D) : Prop34 P :=
  prop34_of_chapters P (petChapter5Holds P) hfam

/-- **Peluse's Proposition 3.4, proved.**  The two chapters of its proof are
* `PetChapter5 P` — Peluse's Lemma 4.9, proved in `UControl/petChapter5Holds.lean`;
* `LinFamBoundLinC' P D` — the corrected averaged Lemma 4.10, proved in
  `UControl/linFamBoundLinC.lean` (whose `linFamBoundLinC` has exactly this body).
So `Prop34 P` is now unconditional: it is the `§4` half of the source's route to this file's target
(the other half is `Prop36S`, the `§5` ladder).  `UControl/peluseProp34.lean`'s `sorry` can be
replaced by this theorem. -/
theorem prop34Holds (P : Polynomial ℤ) : Prop34 P :=
  prop34Holds_of_linFamBoundLinC P (fun D => linFamBoundLinC P D)

/-- **The PET shift parameter is bounded by a power of the correlation.** -/
lemma hyp_delta_le_two_mul_gamma_pow {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    δ' ≤ 2 * A' * γ ^ K := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have hh : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' := ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1,
    hsc2, hC1, hK1, hsmall, hpet, hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩
  have hL1 : 1 ≤ dirLen P δ' N := Hyp.one_le_dirLen hh
  have hLnn : (0 : ℝ) ≤ (dirLen P δ' N : ℝ) := by positivity
  have hLD : (1 : ℝ) ≤ (dirLen P δ' N : ℝ) := by exact_mod_cast hL1
  have hγK1 : γ ^ K ≤ 1 := pow_le_one₀ hγ0.le hγ1
  have hN₁0 : (1 : ℝ) ≤ (N₁ : ℝ) := by exact_mod_cast hN₁
  have hγKN₁ : (1 : ℝ) ≤ γ ^ K * (N₁ : ℝ) := by
    calc (1 : ℝ) ≤ (dirLen P δ' N : ℝ) := hLD
      _ = 1 * (dirLen P δ' N : ℝ) := (one_mul _).symm
      _ ≤ C * (dirLen P δ' N : ℝ) := by nlinarith [hLnn]
      _ ≤ γ ^ K * (N₁ : ℝ) := hsmall
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hA'0 : 0 < A' := by
    have h1 : (1 : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree := le_trans hN₁0 hsc1
    nlinarith
  -- `1 ≤ δ' * N`, from the window hypothesis
  have hz : (1 : ℤ) ≤ ⌊δ' * (N : ℝ)⌋ := by
    have hne : (⌊δ' * (N : ℝ)⌋).toNat ≠ 0 := by omega
    have hle : ¬ ⌊δ' * (N : ℝ)⌋ ≤ 0 := by simpa [Int.toNat_eq_zero] using hne
    omega
  have hδN : (1 : ℝ) ≤ δ' * (N : ℝ) := by simpa using (Int.le_floor.mp hz)
  have hδNd : (1 : ℝ) ≤ δ' * (N : ℝ) ^ P.natDegree := by
    have hNd : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      calc (N : ℝ) = (N : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (N : ℝ) ^ P.natDegree := pow_le_pow_right₀ (by exact_mod_cast hN) (by omega)
    nlinarith
  -- the floor identity
  have hfl : ((⌊δ' * (N : ℝ) ^ P.natDegree⌋).toNat : ℤ)
      = ⌊δ' * (N : ℝ) ^ P.natDegree⌋ :=
    Int.toNat_of_nonneg (le_trans (by norm_num : (0:ℤ) ≤ 1)
      (Int.le_floor.mpr (by simpa using hδNd)))
  have hxdir : δ' * (N : ℝ) ^ P.natDegree < (dirLen P δ' N : ℝ) + 1 := by
    have hx := Int.lt_floor_add_one (δ' * (N : ℝ) ^ P.natDegree)
    have hcast : ((⌊δ' * (N : ℝ) ^ P.natDegree⌋ : ℤ) : ℝ)
        = (dirLen P δ' N : ℝ) := by
      rw [dirLen, ← hfl]
      push_cast
      rfl
    simpa [hcast] using hx
  have hdirle : (dirLen P δ' N : ℝ) ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) := by
    calc (dirLen P δ' N : ℝ) ≤ C * (dirLen P δ' N : ℝ) := by nlinarith [hLnn]
      _ ≤ γ ^ K * (N₁ : ℝ) := hsmall
      _ ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) :=
          mul_le_mul_of_nonneg_left hsc1 (pow_nonneg hγ0.le K)
  have hone : (1 : ℝ) ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) := le_trans hLD hdirle
  have hbd : δ' * (N : ℝ) ^ P.natDegree < 2 * (γ ^ K * (A' * (N : ℝ) ^ P.natDegree)) := by
    calc δ' * (N : ℝ) ^ P.natDegree < (dirLen P δ' N : ℝ) + 1 := hxdir
      _ ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree) + 1 := by linarith
      _ ≤ γ ^ K * (A' * (N : ℝ) ^ P.natDegree)
          + γ ^ K * (A' * (N : ℝ) ^ P.natDegree) := by linarith
      _ = 2 * (γ ^ K * (A' * (N : ℝ) ^ P.natDegree)) := by ring
  have hquot : δ' < 2 * (A' * γ ^ K) := by
    have h1 : δ' < 2 * (γ ^ K * (A' * (N : ℝ) ^ P.natDegree)) / (N : ℝ) ^ P.natDegree :=
      (lt_div_iff₀ hNdpos).mpr hbd
    have h2 : 2 * (γ ^ K * (A' * (N : ℝ) ^ P.natDegree)) / (N : ℝ) ^ P.natDegree
        = 2 * (A' * γ ^ K) := by
      field_simp
    rwa [h2] at h1
  linarith [hquot]

/-- **`Hyp`'s PET non-degeneracy forces the correlation to be large.**  On every `Hyp`-datum,
`1 ≤ (2A')^{K+2}·γ^{K(K+3)}·N²`, i.e. `γ ≳ (2A')^{-(K+2)/(K(K+3))}·N^{-2/(K(K+3))}`: the
non-degeneracy of the PET window `δ'N` and the smallness `C·L ≤ γ^K N₁` together make the residual
of the band's inverse theorem the **high-`γ`** regime.  (Quantitative form of the "constant-strength
coherence" residual: the elementary branches — mass/peel/mean/Fourier — all fail exactly when `γ`
is not small compared with `N`.) -/
lemma hyp_gamma_pow_ge {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    1 ≤ (2 * A') ^ (K + 2) * γ ^ (K * (K + 3)) * (N : ℝ) ^ 2 := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have hh : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' := ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1,
    hsc2, hC1, hK1, hsmall, hpet, hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩
  have hδ := hyp_delta_le_two_mul_gamma_pow hh
  have hNn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hA'0 : 0 ≤ A' := by
    have h1 : (1 : ℝ) ≤ A' * (N : ℝ) ^ P.natDegree :=
      le_trans (by exact_mod_cast hN₁) hsc1
    nlinarith [hNn, pow_nonneg hNn P.natDegree]
  have hb : 0 ≤ 2 * A' * γ ^ K := by positivity
  have h1 : (1 : ℝ) ≤ (γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2 := le_trans hC1 hpet
  have h2 : δ' ^ K ≤ (2 * A' * γ ^ K) ^ K := pow_le_pow_left₀ hδ0.le hδ K
  have h3 : (δ' * (N : ℝ)) ^ 2 ≤ (2 * A' * γ ^ K * (N : ℝ)) ^ 2 := by
    have hle : δ' * (N : ℝ) ≤ 2 * A' * γ ^ K * (N : ℝ) := by nlinarith [hδ, hNn, hb]
    exact pow_le_pow_left₀ (by positivity) hle 2
  have hexp : γ ^ K * (2 * A' * γ ^ K) ^ K * (2 * A' * γ ^ K * (N : ℝ)) ^ 2
      = (2 * A') ^ (K + 2) * γ ^ (K * (K + 3)) * (N : ℝ) ^ 2 := by
    have e1 : (2 * A' * γ ^ K) ^ K = (2 * A') ^ K * γ ^ (K * K) := by
      rw [mul_pow, mul_pow, ← pow_mul]
    have e2 : (2 * A' * γ ^ K * (N : ℝ)) ^ 2
        = (2 * A') ^ 2 * γ ^ (K * 2) * (N : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, ← pow_mul]
    rw [e1, e2]
    have e3 : γ ^ K * ((2 * A') ^ K * γ ^ (K * K))
          * ((2 * A') ^ 2 * γ ^ (K * 2) * (N : ℝ) ^ 2)
        = ((2 * A') ^ K * (2 * A') ^ 2) * (γ ^ K * γ ^ (K * K) * γ ^ (K * 2))
          * (N : ℝ) ^ 2 := by ring
    rw [e3, ← pow_add, ← pow_add, ← pow_add]
    congr 2 <;> ring
  calc (1 : ℝ) ≤ (γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2 := h1
    _ = γ ^ K * δ' ^ K * (δ' * (N : ℝ)) ^ 2 := by rw [mul_pow]
    _ ≤ γ ^ K * (2 * A' * γ ^ K) ^ K * (2 * A' * γ ^ K * (N : ℝ)) ^ 2 := by
        have hδK : δ' ^ K * (δ' * (N : ℝ)) ^ 2
            ≤ (2 * A' * γ ^ K) ^ K * (2 * A' * γ ^ K * (N : ℝ)) ^ 2 :=
          mul_le_mul h2 h3 (by positivity) (by positivity)
        calc γ ^ K * δ' ^ K * (δ' * (N : ℝ)) ^ 2
            = γ ^ K * (δ' ^ K * (δ' * (N : ℝ)) ^ 2) := by ring
          _ ≤ γ ^ K * ((2 * A' * γ ^ K) ^ K * (2 * A' * γ ^ K * (N : ℝ)) ^ 2) :=
              mul_le_mul_of_nonneg_left hδK (by positivity)
          _ = γ ^ K * (2 * A' * γ ^ K) ^ K * (2 * A' * γ ^ K * (N : ℝ)) ^ 2 := by ring
    _ = (2 * A') ^ (K + 2) * γ ^ (K * (K + 3)) * (N : ℝ) ^ 2 := hexp

/-- **The direction length is bounded by the `x`-range.**  `C·L ≤ γ^K N₁` with `C ≥ 1` and
`γ^K ≤ 1`.  (This is the hypothesis `L ≤ N` that the level-raising lemmas need.) -/
lemma hyp_dirLen_le_N₁ {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    dirLen P δ' N ≤ N₁ := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have hLnn : (0 : ℝ) ≤ (dirLen P δ' N : ℝ) := by positivity
  have hle : (dirLen P δ' N : ℝ) ≤ γ ^ K * (N₁ : ℝ) := by
    calc (dirLen P δ' N : ℝ) ≤ C * (dirLen P δ' N : ℝ) := by nlinarith [hLnn]
      _ ≤ γ ^ K * (N₁ : ℝ) := hsmall
  have hγK1 : γ ^ K ≤ 1 := pow_le_one₀ hγ0.le hγ1
  have hN₁0 : (0 : ℝ) ≤ (N₁ : ℝ) := by positivity
  have hcast : (dirLen P δ' N : ℝ) ≤ (N₁ : ℝ) := by
    simpa using le_trans hle (mul_le_mul_of_nonneg_right hγK1 hN₁0)
  exact_mod_cast hcast

/-! ## The square-root form of the PET non-degeneracy, and the forced region of the parameters

`Hyp`'s PET non-degeneracy `1 ≤ (γδ')^K (δ'N)^2` is the *only* source of lower bounds in the
problem.  Its square-root form is what the scale bookkeeping actually needs (the exponent `K/2`,
not `K`):

  `1 ≤ (γδ')^{K/2} · (δ'N)`      (`hyp_petWindow_sqrt`),

and it immediately pins the **region** in which the target's data live:

* `N^{d-1} ≤ 2 (γδ')^{K/2} L`  (`hyp_dirLen_lower`) — the direction length `L = ⌊δ'N^d⌋` is *long*
  (this complements the proved upper bound `L ≤ N₁` of `hyp_dirLen_le_N₁`; it is the arithmetic
  content of "the target's hard case is large `L`");
* `1 ≤ 2A'γ^{K/2}N`  (`hyp_gamma_N_ge`) — the `x`-range, the correlation and the window are tied:
  `N` is forced to be large whenever `γ` is small.

Both are strictly sharper in shape than `hyp_gamma_pow_ge` (which has the exponent `K(K+3)` on `γ`
and `2` on `N`); they are the form in which the region is checked below. -/

/-- **The square-root form of the PET non-degeneracy**: `1 ≤ (γδ')^{K/2}·(δ'N)`. -/
lemma hyp_petWindow_sqrt {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    1 ≤ (γ * δ') ^ (K / 2) * (δ' * (N : ℝ)) := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have ha0 : 0 ≤ γ * δ' := mul_nonneg hγ0.le hδ0.le
  have ha1 : γ * δ' ≤ 1 := by nlinarith [hγ1, hδ1, hγ0.le, hδ0.le]
  have hb0' : 0 ≤ δ' * (N : ℝ) := mul_nonneg hδ0.le (by positivity)
  have hpet1 : 1 ≤ (γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2 := le_trans hC1 hpet
  have h2j : 2 * (K / 2) ≤ K := Nat.mul_div_le K 2
  have hmono : (γ * δ') ^ K ≤ (γ * δ') ^ (2 * (K / 2)) :=
    pow_le_pow_of_le_one ha0 ha1 h2j
  have h1 : 1 ≤ (γ * δ') ^ (2 * (K / 2)) * (δ' * (N : ℝ)) ^ 2 :=
    le_trans hpet1 (mul_le_mul_of_nonneg_right hmono (by positivity))
  have hpow2 : (γ * δ') ^ (2 * (K / 2)) = ((γ * δ') ^ (K / 2)) ^ 2 := by
    rw [Nat.mul_comm 2 (K / 2), pow_mul]
  have hsq : 1 ≤ ((γ * δ') ^ (K / 2) * (δ' * (N : ℝ))) ^ 2 := by
    calc (1 : ℝ) ≤ (γ * δ') ^ (2 * (K / 2)) * (δ' * (N : ℝ)) ^ 2 := h1
      _ = ((γ * δ') ^ (K / 2)) ^ 2 * (δ' * (N : ℝ)) ^ 2 := by rw [hpow2]
      _ = ((γ * δ') ^ (K / 2) * (δ' * (N : ℝ))) ^ 2 := by ring
  have hx0 : 0 ≤ (γ * δ') ^ (K / 2) * (δ' * (N : ℝ)) :=
    mul_nonneg (pow_nonneg ha0 _) hb0'
  by_contra hcon
  push_neg at hcon
  have hlt : ((γ * δ') ^ (K / 2) * (δ' * (N : ℝ))) ^ 2 < 1 :=
    pow_lt_one₀ hx0 hcon (by norm_num)
  linarith [hsq, hlt]

/-- **The direction length is *long***: `N^{d-1} ≤ 2 (γδ')^{K/2} L`, `L = dirLen P δ' N`, `d = deg P`.

`L ≥ ⌊δ'N^d⌋ ≥ δ'N^d/2 = (δ'N)·N^{d-1}/2` (using `L ≥ 1`, so `δ'N^d ≥ 1`), and
`δ'N ≥ (γδ')^{-K/2}` is `hyp_petWindow_sqrt`.  With `L ≤ N₁` (`hyp_dirLen_le_N₁`) this is the
quantitative form of "`L` is at the scale of `N₁` whenever `γδ'` is not tiny". -/
lemma hyp_dirLen_lower {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    (N : ℝ) ^ (P.natDegree - 1) ≤ 2 * (γ * δ') ^ (K / 2) * ((dirLen P δ' N : ℕ) : ℝ) := by
  have hh := h
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := hh
  have hL1 : 1 ≤ dirLen P δ' N := Hyp.one_le_dirLen h
  have ha0 : 0 ≤ γ * δ' := mul_nonneg hγ0.le hδ0.le
  have hsqrt := hyp_petWindow_sqrt h
  -- the floor bookkeeping
  have ht0 : (0 : ℝ) ≤ δ' * (N : ℝ) ^ P.natDegree := by positivity
  have hflZ : ((dirLen P δ' N : ℕ) : ℤ) = ⌊δ' * (N : ℝ) ^ P.natDegree⌋ := by
    rw [dirLen]
    exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr ht0)
  have hfl : ((dirLen P δ' N : ℕ) : ℝ) = ((⌊δ' * (N : ℝ) ^ P.natDegree⌋ : ℤ) : ℝ) := by
    exact_mod_cast hflZ
  have htL : δ' * (N : ℝ) ^ P.natDegree < ((dirLen P δ' N : ℕ) : ℝ) + 1 := by
    rw [hfl]
    exact_mod_cast Int.lt_floor_add_one (δ' * (N : ℝ) ^ P.natDegree)
  have hLr : (1 : ℝ) ≤ ((dirLen P δ' N : ℕ) : ℝ) := by exact_mod_cast hL1
  have ht2L : δ' * (N : ℝ) ^ P.natDegree ≤ 2 * ((dirLen P δ' N : ℕ) : ℝ) := by linarith
  -- `δ'·N^d = (δ'N)·N^{d-1}`
  have hd1 : 1 ≤ P.natDegree := by omega
  have hsplit : δ' * (N : ℝ) ^ P.natDegree
      = (δ' * (N : ℝ)) * (N : ℝ) ^ (P.natDegree - 1) := by
    rw [show (N : ℝ) ^ P.natDegree = (N : ℝ) ^ (P.natDegree - 1) * (N : ℝ) by
      rw [← pow_succ, Nat.sub_add_cancel hd1]]
    ring
  have hNp1 : (0 : ℝ) ≤ (N : ℝ) ^ (P.natDegree - 1) := by positivity
  -- multiply `hyp_petWindow_sqrt` by `N^{d-1}`
  have key : (N : ℝ) ^ (P.natDegree - 1)
      ≤ ((γ * δ') ^ (K / 2) * (δ' * (N : ℝ))) * (N : ℝ) ^ (P.natDegree - 1) := by
    calc (N : ℝ) ^ (P.natDegree - 1)
        = 1 * (N : ℝ) ^ (P.natDegree - 1) := (one_mul _).symm
      _ ≤ ((γ * δ') ^ (K / 2) * (δ' * (N : ℝ))) * (N : ℝ) ^ (P.natDegree - 1) :=
          mul_le_mul_of_nonneg_right hsqrt hNp1
  calc (N : ℝ) ^ (P.natDegree - 1)
      ≤ ((γ * δ') ^ (K / 2) * (δ' * (N : ℝ))) * (N : ℝ) ^ (P.natDegree - 1) := key
    _ = (γ * δ') ^ (K / 2) * (δ' * (N : ℝ) ^ P.natDegree) := by rw [hsplit]; ring
    _ ≤ (γ * δ') ^ (K / 2) * (2 * ((dirLen P δ' N : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ht2L (pow_nonneg ha0 _)
    _ = 2 * (γ * δ') ^ (K / 2) * ((dirLen P δ' N : ℕ) : ℝ) := by ring

/-- **The forced largeness of the `x`-range**: `1 ≤ 2A'γ^{K/2}N`.

Combine `hyp_dirLen_lower` with the two upper bounds `L ≤ N₁` (`hyp_dirLen_le_N₁`) and
`N₁ ≤ A'N^d` (`Hyp`'s first scale relation), and drop `δ' ≤ 1` from `(γδ')^{K/2} ≤ γ^{K/2}`.  So
`γ` small forces `N` large, in the clean form `γ ≳ (2A'N)^{-2/K}`. -/
lemma hyp_gamma_N_ge {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    1 ≤ 2 * A' * γ ^ (K / 2) * (N : ℝ) := by
  have hh := h
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := hh
  have hlow := hyp_dirLen_lower h
  have hLN : ((dirLen P δ' N : ℕ) : ℝ) ≤ (N₁ : ℝ) := by
    exact_mod_cast hyp_dirLen_le_N₁ h
  have ha0 : 0 ≤ γ * δ' := mul_nonneg hγ0.le hδ0.le
  have hle1 : (γ * δ') ^ (K / 2) ≤ γ ^ (K / 2) := by
    have hle : γ * δ' ≤ γ := by nlinarith [hδ1, hγ0.le, hδ0.le]
    exact pow_le_pow_left₀ (mul_nonneg hγ0.le hδ0.le) hle (K / 2)
  have hLnn : (0 : ℝ) ≤ ((dirLen P δ' N : ℕ) : ℝ) := by positivity
  have step1 : (N : ℝ) ^ (P.natDegree - 1) ≤ 2 * (γ * δ') ^ (K / 2) * (N₁ : ℝ) :=
    le_trans hlow (mul_le_mul_of_nonneg_left hLN (by positivity))
  have step2 : (N : ℝ) ^ (P.natDegree - 1) ≤ 2 * γ ^ (K / 2) * (A' * (N : ℝ) ^ P.natDegree) := by
    refine le_trans step1 ?_
    have h1 : 2 * (γ * δ') ^ (K / 2) * (N₁ : ℝ) ≤ 2 * γ ^ (K / 2) * (N₁ : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle1 (by norm_num)) (by positivity)
    have h2 : 2 * γ ^ (K / 2) * (N₁ : ℝ) ≤ 2 * γ ^ (K / 2) * (A' * (N : ℝ) ^ P.natDegree) :=
      mul_le_mul_of_nonneg_left hsc1 (by positivity)
    linarith [h1, h2]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (P.natDegree - 1) := by
    have hd1 : 1 ≤ P.natDegree - 1 := by omega
    exact pow_pos (lt_of_lt_of_le zero_lt_one hN1) _
  have hfact : (N : ℝ) ^ (P.natDegree - 1) * (N : ℝ) = (N : ℝ) ^ P.natDegree := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ P.natDegree)]
  -- `N^{d-1} ≤ 2γ^{K/2}A' N^d = (2A'γ^{K/2}N)·N^{d-1}`
  have hfin : (N : ℝ) ^ (P.natDegree - 1)
      ≤ (2 * A' * γ ^ (K / 2) * (N : ℝ)) * (N : ℝ) ^ (P.natDegree - 1) := by
    calc (N : ℝ) ^ (P.natDegree - 1) ≤ 2 * γ ^ (K / 2) * (A' * (N : ℝ) ^ P.natDegree) := step2
      _ = (2 * A' * γ ^ (K / 2) * (N : ℝ)) * (N : ℝ) ^ (P.natDegree - 1) := by
          rw [← hfact]; ring
  refine le_of_mul_le_mul_right ?_ hNpos
  simpa using hfin

/-- **FALSE — DO NOT USE (this session's counterexample).**  The level-one formulation below is
*false*, so every statement of this section is vacuous and the "reduction" it seems to give is
empty.  Refuting family (`P = X²`, so `dirCoeff P = 2!·1 = 2`; take `A' = 1`, `C = 1`, `K = 4`,
`N = ⌊√N₁⌋`, `N₁ ≥ 2^{28}`, `δ' = 1/16`, `γ = 1/2`, `g₀ = g₁ = 1_{symIcc N₁}`,
`g₂ (z) = e(z/3)·1_{symIcc N₁}`):

* `Hyp` **holds**: `ΛZ N₁ N X² g₀ g₁ g₂ = (N₁N)⁻¹ ∑_x [...] ∑_{y ≤ N} e(y²/3)`, and the inner sum
  is the linear-in-`N` Gauss-type sum `(N/3)(1 + 2ω)` (`ω = e^{2πi/3}`, `|1+2ω| = √3`), so
  `‖ΛZ‖ = |1 + 2ω|/3 = 1/√3 ≈ 0.577 > 1/2 = γ`; the PET non-degeneracy needs only
  `N₁ ≥ 2^{4·4+8}`.
* the conclusion **fails**: `∑_{m=1}^{L} e(2m/3) = O(1)` (the residues `2m mod 3` cycle with sum
  `1 + ω + ω̄ = 0`), so `∑'_x ‖∑_{a ∈ 2[L]} g₂ (x+a)‖² = O(N₁)` and
  `uNormPow 1 (arithIcc 2 L) (symIcc N₁) g₂ = O(L⁻²) → 0`, while `cst·γ^{K₀} = cst·2^{-K₀}` is a
  positive constant.  So `LevelOneCrux (X²)` is **false**, and with it `SlidingSumsCrux` and
  `LowFreqCrux`.

The mathematical reason is structural: the **dilated** direction AP `κ[L]` can only resolve
frequencies `θ` with `distInt (κθ)` small, while the level-two box norm is blind to the phases of a
*linear* character (its level-two cube terms telescope to `1`).  For that very family
`uNormPow 2 (arithIcc 2 L) (symIcc N₁) g₂ ≍ 3/4 ≫ cst·γ^{K₀}` — i.e. the target itself is
comfortable, and the tree's crux at level **two** is the correct level.  Hence: **the level-one
route to the band's inverse theorem is dead; the crux must be stated at level ≥ 2.**  The
definitions and implications below are kept only so that the delegated modules
(`lowFreqCrux_imp_slidingSums`, `levelOneCrux_of_autocorrAvg`) compile.

/-- **The target's crux in its *first-moment* (level-one) form** (see the warning above: false). -/

`uNormPow 1 (κ[L]) (symIcc N₁) g₂ = |symIcc N₁|⁻¹ L⁻² ∑_x ‖∑_{u=1}^{L} g₂ (x + κu)‖²` is the
normalised `ℓ²`-mass of the *sliding sums* of `g₂` along the dilated AP `κ[L]`
(equivalently — `Concat.uNormPow_one_eq_autocorr` — the `cntW`-weighted average of
`Re (autocorr N₁ g₂ (κu))` over the dilated lags `|u| < L`): a **first-moment** quantity, matching
the fact that the datum's hypothesis `γ ≤ ‖ΛZ‖` is itself a first-moment statement.

Its exponent `K₀` is *half* of the level-two obligation's: the target's level-two instance is
`cst γ^{K₀} ≤ uNormPow 2 (κ[L]) (symIcc N₁) g₂`, and `uNormPow 2 ≥ c·(uNormPow 1)²`
(`uNormPow_level_raise_win 1 2`), which is why `cst γ^2 ≤ uNormPow 1` suffices.  Both the density
family (`g₂ = 1_A`, `γ ≈ 2|A|/N₁`, `uNormPow 1 ≈ γ²/4`) and the comb family (`g₂ = 1_{qℤ}`,
`γ ≈ 1/q`, `uNormPow 1 ≈ 1/q²`) show `K₀ = 2` to be sharp, exactly as `K₀ = 4` is sharp at level
two.  The tree's pointwise flatness input `Work.Peluse.UControl.FlatBand` implies this
(*pointwise* `Re (autocorr N₁ g₂ (κm)) ≥ δ²/C` for `|m| ≤ L` averages to it), so `LevelOneCrux`
sits *between* the tree's crux and this file's target. -/
def LevelOneCrux (P : Polynomial ℤ) : Prop :=
  ∀ A' : ℝ, 1 ≤ A' → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ cst : ℝ, 0 < cst ∧
    ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      cst * γ ^ K₀ ≤ uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂

/-- **FALSE HYPOTHESIS (see the warning above).**  The whole target follows from the first-moment crux.  The level raising
`uNormPow_level_raise_win 1 s` (Gowers–Cauchy–Schwarz iterated `s - 1` times, *with* the window
slack needed when `|κ|L > N₁`) turns the level-one bound at exponent `K₁` into the level-`s` bound
at exponent `K₁·2^{s-1}` — the same doubling of the exponent that the density family forces. -/
theorem bandStructureAprime_of_levelOneCrux (P : Polynomial ℤ) (h : LevelOneCrux P) :
    ∀ (s : ℕ), 2 ≤ s → ∀ A' : ℝ, 1 ≤ A' → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ cst : ℝ, 0 < cst ∧
      ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
        Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
        cst * γ ^ K₀ ≤ uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂ := by
  intro s hs A' hA'
  obtain ⟨K₁, hK₁, c₁, hc₁, h1⟩ := h A' hA'
  by_cases hd : 2 ≤ P.natDegree
  · obtain ⟨c₂, hc₂, h2⟩ := uNormPow_level_raise_win (κ := dirCoeff P) 1 s (le_refl 1)
      (by omega) (dirCoeff_ne_zero hd)
    refine ⟨K₁ * 2 ^ (s - 1), Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
      (by positivity)), c₂ * c₁ ^ (2 ^ (s - 1)), by positivity, ?_⟩
    intro C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH
    have hH2 : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' := hH
    obtain ⟨hd', hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
      hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := hH2
    have hKK₁ : K₁ ≤ K := by
      calc K₁ ≤ K₁ * 2 ^ (s - 1) := Nat.le_mul_of_pos_right _ (by positivity)
        _ ≤ K := hK
    have hU1 := h1 C hC K hKK₁ N N₁ g₀ g₁ g₂ γ δ' hH
    have hraise := h2 (dirLen P δ' N) N₁ g₂ (hyp_dirLen_le_N₁ hH) (Hyp.one_le_dirLen hH) hs2
      hb2
    refine le_trans ?_ hraise
    have hpow : (c₁ * γ ^ K₁) ^ (2 ^ (s - 1))
        ≤ (uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂)
          ^ (2 ^ (s - 1)) :=
      pow_le_pow_left₀ (by positivity) hU1 _
    calc c₂ * c₁ ^ (2 ^ (s - 1)) * γ ^ (K₁ * 2 ^ (s - 1))
        = c₂ * (c₁ * γ ^ K₁) ^ (2 ^ (s - 1)) := by
          rw [mul_pow, ← pow_mul]; ring
      _ ≤ c₂ * (uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂)
            ^ (2 ^ (s - 1)) := mul_le_mul_of_nonneg_left hpow hc₂.le
  · refine ⟨1, le_refl 1, 1, one_pos, ?_⟩
    intro C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH
    exact absurd hH.1 hd

/-- **FALSE HYPOTHESIS (see the warning above).**  The first-moment crux in *elementary* (sliding-sums) language.

By `Work.Peluse.Peel.boxNormPow_one_tsum`, the level-one box-norm power of `g₂` at the direction
set `κ[L]` and window `symIcc N₁` is *literally*

  `|symIcc N₁|⁻¹ · L⁻² · ∑'_x ‖∑_{a ∈ κ[L]} g₂ (x + a)‖²`,

so `LevelOneCrux` is equivalent to the statement below — an inequality about the normalised
`ℓ²`-mass of the sliding sums of `g₂` along the dilated AP `κ[L]`, **with no box norms, no
autocorrelations, and no characters**.  This is the cleanest known language for the band's
inverse theorem: it is the exact place where `γ ≤ ‖ΛZ ‖` has to be exploited, and it is what a
prover should attempt. -/
def SlidingSumsCrux (P : Polynomial ℤ) : Prop :=
  ∀ A' : ℝ, 1 ≤ A' → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ cst : ℝ, 0 < cst ∧
    ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
    ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
      Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
      cst * γ ^ K₀ ≤ ((symIcc N₁).card : ℝ)⁻¹
        * (((arithIcc (dirCoeff P) (dirLen P δ' N)).card : ℝ))⁻¹ ^ 2
        * ∑' x : ℤ, ‖∑ a ∈ arithIcc (dirCoeff P) (dirLen P δ' N), g₂ (x + a)‖ ^ 2

/-- The level-one box-norm power at a dilated direction set is the normalised `ℓ²`-mass of the
sliding sums — `Work.Peluse.Peel.boxNormPow_one_tsum`, unpacked. -/
private lemma uNormPow_one_eq_sliding (κ : ℤ) (L N : ℕ) {f : ℤ → ℂ}
    (hsupp : SupportIn f N) :
    uNormPow 1 (arithIcc κ L) (symIcc N) f
      = ((symIcc N).card : ℝ)⁻¹ * (((arithIcc κ L).card : ℝ))⁻¹ ^ 2
        * ∑' x : ℤ, ‖∑ a ∈ arithIcc κ L, f (x + a)‖ ^ 2 := by
  rw [show uNormPow 1 (arithIcc κ L) (symIcc N) f
      = boxNormPow 1 (fun _ : Fin 1 => arithIcc κ L) (symIcc N) f from rfl,
    Work.Peluse.Peel.boxNormPow_one_tsum _ _ hsupp]

/-- **The two languages agree** (both sides false for `P = X²`; the equivalence is a theorem).  `Work.Peluse.Peel.boxNormPow_one_tsum` (the level-one box-norm
power is the normalised `ℓ²`-mass of the sliding sums) turns `LevelOneCrux` into `SlidingSumsCrux`
verbatim. -/
theorem levelOneCrux_iff_slidingSums (P : Polynomial ℤ) :
    LevelOneCrux P ↔ SlidingSumsCrux P := by
  constructor
  · intro h A' hA'
    obtain ⟨K₀, hK₀, cst, hcst, hb⟩ := h A' hA'
    refine ⟨K₀, hK₀, cst, hcst, ?_⟩
    intro C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH
    have hH2 : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' := hH
    obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
      hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := hH2
    have hmain := hb C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH
    rwa [uNormPow_one_eq_sliding (dirCoeff P) (dirLen P δ' N) N₁ hs2] at hmain
  · intro h A' hA'
    obtain ⟨K₀, hK₀, cst, hcst, hb⟩ := h A' hA'
    refine ⟨K₀, hK₀, cst, hcst, ?_⟩
    intro C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH
    have hH2 : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' := hH
    obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
      hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := hH2
    rw [uNormPow_one_eq_sliding (dirCoeff P) (dirLen P δ' N) N₁ hs2]
    exact hb C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH

/-- **FALSE HYPOTHESIS (see the warning above).**  The whole target follows from the sliding-sums crux. -/
theorem bandStructureAprime_of_slidingSumsCrux (P : Polynomial ℤ) (h : SlidingSumsCrux P) :
    ∀ (s : ℕ), 2 ≤ s → ∀ A' : ℝ, 1 ≤ A' → ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ cst : ℝ, 0 < cst ∧
      ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
        Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
        cst * γ ^ K₀ ≤ uNormPow s (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂ :=
  bandStructureAprime_of_levelOneCrux P ((levelOneCrux_iff_slidingSums P).mpr h)


/-! ## The crux in spectral (low-frequency) language

`SlidingSumsCrux` (above) is equivalent to a statement about the **Fourier transform** of `g₂`:
by Parseval on the circle and the elementary lower bound `|Σ_{m=1}^{L} e(mx)|² ≥ 4L²/π²` for
`distInt x ≤ 1/(2L)`, the `ℓ²`-mass of the sliding sums dominates `(4L²/π²)` times the `ℓ²`-mass of
the spectrum of `g₂` in the **Bohr neighbourhood** `distInt (κθ) ≤ 1/(2L)`:

  `(4/π²)·L²·LowFreqMass κ L g₂ ≤ ∑'_x ‖∑_{a ∈ κ[L]} g₂ (x+a)‖²`.

So the crux `cst γ^{K₀} ≤ uNormPow 1 (κ[L]) (symIcc N₁) g₂` follows from the *spectral* statement

  `cst' γ^{K₀}·|symIcc N₁| ≤ LowFreqMass (dirCoeff P) (dirLen P δ' N) g₂`  (`LowFreqCrux P`),

i.e. **a constant fraction of the `ℓ²`-mass of `g₂` is concentrated on the frequencies
`‖κθ‖ ≤ 1/(2L)`** — the frequency band that the direction AP `κ[L]` can resolve.  This is the
cleanest *positive* form of the band's inverse theorem: the datum supplies `γ ≤ ‖ΛZ‖` and the mass
bound `γ²N₁/3 ≤ ‖g₂‖₂²` (`mass_bound_of_lambdaZ`), and the obligation is a **spectral
concentration** statement at the single scale `1/L` — no box norms, no characters, no PET.
(The density family saturates it exactly: `g₂ = 1_A` has its spectrum concentrated at `θ = 0` in a
spike of width `1/N₁`, inside the Bohr set because `L ≤ N₁`, with mass `≍ |A|²/N₁ ≍ |S|γ²`.)

The implication `LowFreqCrux P → SlidingSumsCrux P` is delegated
(`Submission/Work/Peluse/UControl/lowFreqCrux_imp_slidingSums.lean`). -/

/-! ## The crux in the **level-two autocorrelation** form (the correct shape)

This is the `Hyp`-side counterpart of the tree's `BandSpreadAutocorr` / `FlatBand` /
`AverResidAprime`: the *second moment* of the dilated autocorrelation of `g₂`,
`∑_{|m| < L} cntW L m ‖autocorr N₁ g₂ (κ m)‖²`, must be `≳ L² γ^{K₀}`.  Unlike the level-one
formulations of the previous section (which the linear-character counterexample kills), this
shape **survives** every known test:

* the density family (`g₂ = 1_A`, `γ ≈ 2ρ`) has `‖autocorr‖ ≈ ρ²` at all dilated lags, so the sum
  is `≍ L²ρ⁴ = L²γ⁴/16` (sharp at `K₀ = 4`);
* the comb family (`g₂ = 1_{qℤ}`, `γ ≈ 1/q`) has `‖autocorr (κm)‖ ≍ 1/q` on the multiples of
  `q/gcd(q,κ)` and `0` elsewhere; the `cntW`-weighted sum is `≍ L²γ²`, again consistent;
* the linear-character family (`g₂ = e(z/3)·1`, `γ ≈ 1/√3`) has `‖autocorr (2m)‖ ≈ 1 - 2m/N₁ ≈ 1`,
  so the sum is `≍ L² ≫ L²γ^{K₀}`.

The proof below composes the *fit-free* flatness brick
`Work.Peluse.UControl.uNormPow_two_ge_flatness_win'` (the window ratio
`|symIcc N₁|/|symIcc (max N₁ (|κ|L))|` is `≥ 2/(3(1+|κ|))` on `Hyp`-data, because `Hyp` gives
`L ≤ N₁` and `κ = dirCoeff P` is fixed by `P`) with the level raising
`uNormPow_level_raise_win 2 s`. -/

/-! ## A **proved branch** of the target: the large-Fourier-coefficient data

The tree's `Work.Peluse.UControl.bandConcl_of_largeFourier` (`meanBoundPow.lean`, proved) gives the
band's conclusion on every `BandHyp`-datum having one large Fourier coefficient, and
`bandHyp_of_hyp` (`bandHypOfHyp.lean`, proved) says that every `Hyp`-datum **is** a `BandHyp`-datum
at the maximal direction length `L := dirLen P δ' N` and the correlation level `δ := γ`.  Chaining
the two (plus the exponent bookkeeping `γ^{2K₀} = γ^{K₀}·γ^{K₀}`) proves the **level-two target
itself** on all such data:

  on every `Hyp`-datum with `θ·γ·N₁ ≤ ‖∑_x g₂(x)·ee(βx)‖` for some `β` (any fixed `θ > 0`),

  `cst·γ^{K₀} ≤ uNormPow 2 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂`

with `K₀ = 2·K_{band}`, `cst = 1/(Cb·A'^{K_{band}})` — i.e. this branch is **not** part of the
residual.  (This is the `Hyp`-side form of the tree's session-52 "large-Fourier branch"; it is the
first *proved* instance of the target in this file, and it is exactly why the linear-character
counterexample of §0 is harmless for the target while it is fatal at level one.)

The remaining content of the target is therefore the data with **no** large Fourier coefficient
(the tree's `NoLargeFourier` residual), i.e. exactly where the tree's
`BandResidualSmallFourier`/`BandDegenerate` family lives. -/

/-! ## The `γ̃`-weighted **near-lag moment**, and the seventh **proved branch**

The proved `Work.Peluse.Concat.concatNearLagBound` bounds the `γ̃`-weighted **first moment** of the
autocorrelation — at the *multiplicative-convolution* weights of the pairs `(e,l) ↦ e·l`, i.e. the
divisor-like weights that the PET expansion of `Λ` produces for the quadratic `P` — by its `ℓ²`-sum
at the dilated lags:

  `(nearLagMoment κ M₁ L N f)² ≤ C₀ · L⁻² · ∑_{|u|<L} cntW L u · ‖autocorr N f (κ u)‖²`.

Feeding it into the flatness brick `uNormPow_two_ge_flatness_win'` (at the window
`M := max N₁ (|κ|L)`, which supplies the fit `|κ|L ≤ M` through the window ratio `ρ`, and with the
direction `|κ|` in place of `κ`) gives a **seventh proved branch of the target**: on `Hyp`-data
whose `γ̃`-weighted near-lag moment of `autocorr N₁ g₂` is at least `θγ²`, the level-two target
holds at the sharp exponent `4`, with the constant `θ²/(3C₀)`.

The branch sees the *products* `e·l`, so it is genuinely different from the six arithmetic
complements recorded in `ResidualAprime` (the flat weights `cntW L` of `uNormPow 1`, the mean, the
Fourier coefficient, the `ℓ²`-mass and the peel).  The family that saturates the target — the
density family `g₂ = 1_A` with `|A|/N₁ = ρ`, `γ ≈ 2ρ`, whose autocorrelation is `≈ ρ` at every lag
— satisfies this hypothesis as soon as `ρ ≫ θ`, so the branch removes that extremal family from the
residual; what remains are the data whose divisor-weighted first moment of `Re autocorr N₁ g₂ (κ·)`
also stays below `θγ²`. -/

/-- **The arithmetic of the near-lag branch** (pure real bookkeeping): the flatness brick
`(3L²)⁻¹ρS ≤ U`, the near-lag Cauchy–Schwarz `T² ≤ C₀(L²)⁻¹(ρ²S)` and the coherence `θγ² ≤ T`
give `θ²γ⁴/(3C₀) ≤ U` (the window ratio satisfies `ρ ≤ 1`). -/
private lemma nearLag_arith {C₀ ρ L T S U θ γ : ℝ} (hC₀ : 0 < C₀) (hρ : 0 < ρ) (hρle : ρ ≤ 1)
    (hL : 0 < L) (hγ : 0 < γ) (hθ : 0 < θ)
    (h1 : T ^ 2 ≤ C₀ * ((L ^ 2)⁻¹ * (ρ ^ 2 * S)))
    (h2 : θ * γ ^ 2 ≤ T)
    (h3 : (3 * L ^ 2)⁻¹ * ρ * S ≤ U) :
    θ ^ 2 / (3 * C₀) * γ ^ 4 ≤ U := by
  have hTL : T ^ 2 * L ^ 2 ≤ C₀ * ρ ^ 2 * S := by
    have h := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ L ^ 2)
    have heq : (C₀ * ((L ^ 2)⁻¹ * (ρ ^ 2 * S))) * L ^ 2 = C₀ * ρ ^ 2 * S := by
      field_simp
    linarith [h, heq.le, heq.ge]
  have hSge : T ^ 2 * L ^ 2 / (C₀ * ρ ^ 2) ≤ S := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hTL]
  have hmain : T ^ 2 / (3 * C₀ * ρ) ≤ U := by
    have hid : T ^ 2 / (3 * C₀ * ρ)
        = (3 * L ^ 2)⁻¹ * ρ * (T ^ 2 * L ^ 2 / (C₀ * ρ ^ 2)) := by
      field_simp
    rw [hid]
    exact le_trans (mul_le_mul_of_nonneg_left hSge (by positivity)) h3
  have hstep : (θ * γ ^ 2) ^ 2 / (3 * C₀ * ρ) ≤ T ^ 2 / (3 * C₀ * ρ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h2 2) (by positivity)
  have hfinal : θ ^ 2 / (3 * C₀) * γ ^ 4 ≤ (θ * γ ^ 2) ^ 2 / (3 * C₀ * ρ) := by
    have hnum : (θ * γ ^ 2) ^ 2 = θ ^ 2 * γ ^ 4 := by ring
    rw [hnum, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hnn : (0 : ℝ) ≤ θ ^ 2 * γ ^ 4 := by positivity
    have h3' : 3 * C₀ * ρ ≤ 3 * C₀ := by nlinarith [hρle, hC₀]
    exact mul_le_mul_of_nonneg_left h3' hnn
  exact le_trans hfinal (le_trans hstep hmain)

/-- **The arithmetic of the single-lag branch** (pure real bookkeeping): the flatness brick
`(3L²)⁻¹ρS ≤ U`, the single-lag bound `(θγ²L)² ≤ S` and `ρ ≥ 1/(3k)` give `θ²γ⁴/(9k) ≤ U`. -/
private lemma largeAutocorr_arith {ρ L S U θ γ k : ℝ} (hρ : 0 < ρ) (hρk : 1 / (3 * k) ≤ ρ)
    (hL : 0 < L) (hγ : 0 < γ) (hθ : 0 < θ) (hk : 1 ≤ k)
    (h1 : (3 * L ^ 2)⁻¹ * ρ * S ≤ U)
    (h2 : (θ * γ ^ 2 * L) ^ 2 ≤ S) :
    θ ^ 2 / (9 * k) * γ ^ 4 ≤ U := by
  have hk' : (0 : ℝ) < 3 * k := by positivity
  have hρk' : 1 ≤ ρ * (3 * k) := by
    have := (div_le_iff₀ hk').mp hρk
    simpa [mul_comm] using this
  have h3 : (θ * γ ^ 2 * L) ^ 2 = θ ^ 2 * γ ^ 4 * L ^ 2 := by ring
  have hstep : (3 * L ^ 2)⁻¹ * ρ * (θ ^ 2 * γ ^ 4 * L ^ 2) = ρ * θ ^ 2 * γ ^ 4 / 3 := by
    field_simp
  have hmid : θ ^ 2 / (9 * k) * γ ^ 4 ≤ ρ * θ ^ 2 * γ ^ 4 / 3 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hA : (0 : ℝ) ≤ θ ^ 2 * γ ^ 4 := by positivity
    have hB : 3 ≤ ρ * (9 * k) := by nlinarith [hρk']
    calc θ ^ 2 * γ ^ 4 * 3 ≤ θ ^ 2 * γ ^ 4 * (ρ * (9 * k)) :=
          mul_le_mul_of_nonneg_left hB hA
      _ = ρ * θ ^ 2 * γ ^ 4 * (9 * k) := by ring
  calc θ ^ 2 / (9 * k) * γ ^ 4 ≤ ρ * θ ^ 2 * γ ^ 4 / 3 := hmid
    _ = (3 * L ^ 2)⁻¹ * ρ * (θ ^ 2 * γ ^ 4 * L ^ 2) := hstep.symm
    _ = (3 * L ^ 2)⁻¹ * ρ * (θ * γ ^ 2 * L) ^ 2 := by rw [h3]
    _ ≤ (3 * L ^ 2)⁻¹ * ρ * S :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ U := h1

/-- **The arithmetic of the single-window near-lag branch**: the flatness brick
`(3L²)⁻¹ρS ≤ U`, the near-lag Cauchy–Schwarz `T² ≤ C₀(L²)⁻¹(ρ²S)`, the coherence `ρθγ² ≤ T` and
`ρ ≥ 1/(3k)` give `θ²γ⁴/(9kC₀) ≤ U`. -/
private lemma nearLagWindow_arith {C₀ ρ L T S U θ γ k : ℝ} (hC₀ : 0 < C₀) (hρ : 0 < ρ)
    (hL : 0 < L) (hγ : 0 < γ) (hθ : 0 < θ) (hk : 1 ≤ k) (hρk : 1 / (3 * k) ≤ ρ)
    (h1 : T ^ 2 ≤ C₀ * ((L ^ 2)⁻¹ * (ρ ^ 2 * S)))
    (h2 : ρ * (θ * γ ^ 2) ≤ T)
    (h3 : (3 * L ^ 2)⁻¹ * ρ * S ≤ U) :
    θ ^ 2 / (9 * k * C₀) * γ ^ 4 ≤ U := by
  have hTL : T ^ 2 * L ^ 2 ≤ C₀ * ρ ^ 2 * S := by
    have h := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ L ^ 2)
    have heq : (C₀ * ((L ^ 2)⁻¹ * (ρ ^ 2 * S))) * L ^ 2 = C₀ * ρ ^ 2 * S := by
      field_simp
    linarith [h, heq.le, heq.ge]
  have hSge : T ^ 2 * L ^ 2 / (C₀ * ρ ^ 2) ≤ S := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hTL]
  have hmain : T ^ 2 / (3 * C₀ * ρ) ≤ U := by
    have hid : T ^ 2 / (3 * C₀ * ρ)
        = (3 * L ^ 2)⁻¹ * ρ * (T ^ 2 * L ^ 2 / (C₀ * ρ ^ 2)) := by
      field_simp
    rw [hid]
    exact le_trans (mul_le_mul_of_nonneg_left hSge (by positivity)) h3
  have hfin : ρ * θ ^ 2 * γ ^ 4 / (3 * C₀) ≤ U := by
    have h0 : 0 ≤ ρ * (θ * γ ^ 2) := by positivity
    have hT2 : (ρ * (θ * γ ^ 2)) ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ h0 h2 2
    have h : (ρ * (θ * γ ^ 2)) ^ 2 / (3 * C₀ * ρ) ≤ T ^ 2 / (3 * C₀ * ρ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_right hT2 (by positivity)
    refine le_trans ?_ hmain
    refine le_trans (le_of_eq ?_) h
    field_simp
  calc θ ^ 2 / (9 * k * C₀) * γ ^ 4
      = (θ ^ 2 * γ ^ 4 / (3 * C₀)) * (1 / (3 * k)) := by
        field_simp
        ring
    _ ≤ (θ ^ 2 * γ ^ 4 / (3 * C₀)) * ρ :=
        mul_le_mul_of_nonneg_left hρk (by positivity)
    _ = ρ * θ ^ 2 * γ ^ 4 / (3 * C₀) := by ring
    _ ≤ U := hfin

/-! ## A sixth **proved branch**: the large-`A'` regime (the tree's `bandConcl_of_massDiagonal`)

`Work.Peluse.UControl.bandConcl_of_massDiagonal` (`bandConcl_of_massDiagonal.lean`, proved) is the
*large-`A'`* part of the band chapter, obtained from the `ℓ¹`-mass bound plus the iterated
diagonal peel: on `BandHyp`-data with `L ≤ δ^K N₀` (automatic here, `C ≥ 1`) and
`N₀^{s-1} ≤ c A'^K`, it gives `BandConcl` with `Cb = 1/c`, `c = 1/(K₁+1)`,
`K₁ = 3^{2^s}(2·bandCFit P + 3)`.  Transporting it along `bandHyp_of_hyp` and applying it at the
*fixed* exponent `K = 4` (legitimate by `hyp_mono_K`, so that `A'^K` becomes `A'^4`) yields the
level-two target on every `Hyp`-datum with `N₁ ≤ c A'^4` — a branch that is *not* `A'`-uniform, so
it strictly shrinks the residual (the residual only has to be proved for `A' ≲ N₁^{1/4}`). -/

/-! ## A fifth **proved branch**: large level-two *diagonal* mass

The flatness brick `Work.Peluse.UControl.uNormPow_two_ge_flatness_win'` (proved in `bandCore.lean`,
and already used by `bandStructureAprime_of_dilatedAutocorrL2` below) bounds the level-two box-norm
power below by the `cntW`-weighted `ℓ²`-sum of the dilated autocorrelations.  Dropping everything but
the **diagonal** term `m = 0` of that sum — whose value is `cntW L 0 · ‖autocorr N₁ g₂ 0‖² =
L · (Lmass N₁ g₂ 2)²` (`Concat.autocorr_zero_eq_Lmass`) — gives

  `(2/(9(1+|κ|))) · Lmass²/L ≤ uNormPow 2 (κ[L]) (symIcc N₁) g₂`,

i.e. the level-two target at the sharp exponent `4` whenever `Lmass² ≳ γ⁴ L`.  This is the `ℓ²`-mass
(diagonal) branch: it is *strictly wider* than the peel branch (which only reaches bounded `L`), since
`Lmass ≤ 1` allows `L` up to `1/(9(1+|κ|)γ⁴)` whenever the mass is comparable to `1`. -/

/-! ## A **proved branch of a new kind**: the *flat profile*

`Work.Peluse.UControl.uNormPow_two_ge_of_flatProfile` (`bandResidualShrink.lean`, proved,
axiom-clean) is the member of the flatness family of bricks that has **no `1/L` loss**: if *every*
dilated autocorrelation of `f` at the lags `κm`, `|m| < L`, is at least half of the maximal value
`Lmass N f 2`, then

  `δ⁴/(1458|κ|) ≤ uNormPow 2 (κ[L]) (symIcc N) f`.

This is what the diagonal term `m = 0` of the flatness sum alone cannot give (it only yields
`δ⁴/L`), and it is exactly the case realised by the *density family* (`g₂ = 1_A`, whose
autocorrelation is `≈ ρ²` at every lag), i.e. by the family that *saturates* the target's exponent
`K₀ = 2^s` at `s = 2`.  So its complement — "some dilated autocorrelation is below half of the
maximal value" — is a *free* restriction of the residual (the complement of a proved branch may
always be assumed), and it removes the extremal family from it.

The branch below states this in the target's own (`Hyp`) vocabulary, with the `ℓ²`-mass bound
`Work.Peluse.UControl.mass_bound_of_lambdaZ` supplying the brick's mass hypothesis. -/

/-! ## A fourth **proved branch**: large *level-one* box norm

`Work.Peluse.UControl.uNormPow_two_ge_of_uNorm_one` (`bandCore.lean`, proved) is the
Gowers–Cauchy–Schwarz level raising `c·(uNormPow 1 Q S f)² ≤ uNormPow 2 Q S f` at the *same*
direction set.  It turns every lower bound on the **level-one** box norm at the dilated AP `κ[L]`
into a lower bound on the level-two norm — with the *square* of the exponent.  Since the natural
scale of `uNormPow 1 (κ[L]) (symIcc N₁) g₂` on the extremal families (density: `≍ γ²/4`; comb:
`≍ γ²`) is `γ²`, this gives the level-two target at the **sharp** exponent `K₀ = 4`. -/

/-- **The large-level-one branch of the target** (`θ·γ² ≤ uNormPow 1 (κ[L]) (symIcc N₁) g₂` for a
fixed `θ > 0`), giving the level-two target at the sharp exponent `4` and constant `c·θ²`. -/
theorem targetAprimeTwo_of_largeUOne (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∃ cst : ℝ, 0 < cst ∧
      ∀ (θ : ℝ), 0 < θ → ∀ (A' : ℝ), 1 ≤ A' → ∀ C : ℝ, 1 ≤ C → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N N₁ : ℕ) (g₀ g₁ g₂ : ℤ → ℂ) (γ δ' : ℝ),
        Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ' →
        θ * γ ^ 2 ≤ uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂ →
        cst * θ ^ 2 * γ ^ K₀
          ≤ uNormPow 2 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂ := by
  obtain ⟨c, hc, hGCS⟩ := uNormPow_two_ge_of_uNorm_one (P := P) hd
  refine ⟨4, by norm_num, c, hc, ?_⟩
  intro θ hθ A' hA' C hC K hK N N₁ g₀ g₁ g₂ γ δ' hH hU1
  have hH0 := hH
  obtain ⟨hd', hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := hH0
  have hL1 : 1 ≤ dirLen P δ' N := Hyp.one_le_dirLen hH
  have hLN : dirLen P δ' N ≤ N₁ := hyp_dirLen_le_N₁ hH
  have hsq : (θ * γ ^ 2) ^ 2
      ≤ (uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hU1 2
  have hsq' : θ ^ 2 * γ ^ 4
      ≤ (uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂) ^ 2 := by
    have h2 : (θ * γ ^ 2) ^ 2 = θ ^ 2 * γ ^ 4 := by ring
    linarith [hsq, h2.le, h2.ge]
  calc c * θ ^ 2 * γ ^ 4 = c * (θ ^ 2 * γ ^ 4) := by ring
    _ ≤ c * (uNormPow 1 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq' hc.le
    _ ≤ uNormPow 2 (arithIcc (dirCoeff P) (dirLen P δ' N)) (symIcc N₁) g₂ :=
        hGCS (dirLen P δ' N) N₁ g₂ hL1 hLN hs2 hb2

/-! ## The **averaged** flat-profile (middle-mass) branch — the sharpest known form of the
## flatness input, and the branch that *replaces* the pointwise one

The flat-profile branch (`targetAprimeTwo_of_flatProfile`, proved above, brick
`bandResidualShrink.uNormPow_two_ge_of_flatProfile`) assumes the *pointwise* flatness
`Lmass N₁ g₂ 2 ≤ 2‖autocorr N₁ g₂ (κm)‖` for **every** `|m| < L`.  But the flatness brick
(`bandCore.uNormPow_two_ge_flatness_win'`) that underlies it only needs a lower bound for the
*weighted `ℓ²`-sum* of the dilated autocorrelations, so the pointwise hypothesis is far stronger
than necessary.  The sharp hypothesis is the **middle-mass** condition

  `θ·L·(Lmass N₁ g₂ 2 / 2)²  ≤  Σ_{|m| ≤ ⌊L/2⌋} ‖autocorr N₁ g₂ (κm)‖²`,

which is implied by the pointwise one (`Σ_{|m|≤L/2} ‖·‖² ≥ (⌊L/2⌋+1)(Lmass/2)²`), and which for
`θ = resEps` is *vastly* weaker (the `ℓ²`-mass on the *middle half* of the dilated lags may be as
small as `resEps·L·(Lmass/2)²`).

The brick `Work.Peluse.UControl.uNormPow_two_ge_of_dilatedAutocorrMiddleMass` (same session,
proved, axiom-clean) turns it into the level-two conclusion at the sharp exponent `4`, with the
constant `θ/(1944(2|κ|+1))` and **no `1/L` loss** — the same conclusion the pointwise branch gives,
on strictly more data.

**Consequence for the frontier.**  Since this branch's hypothesis is weaker than the pointwise
flatness, the *negation* of the middle-mass condition is a **strictly stronger** hypothesis than the
residual's `¬(flat)`, and it may replace it: the residual becomes

  `… ∧ ¬(resEps·L·(Lmass N₁ g₂ 2/2)² ≤ Σ_{|m| ≤ ⌊L/2⌋}‖autocorr N₁ g₂ (κm)‖²)`,

i.e. *"the `ℓ²`-mass of the dilated autocorrelation on the middle half is a negligible fraction of
`L·(Lmass)²`"*.  This is the sharpest known form of the band's remaining obligation, and it agrees
with the tree's `Work.Peluse.UControl.BandHardAveraged` (which is the *conclusion* side of the same
crux), so a proof of either closes the other. -/

/-- The **middle half** of the dilated lag range: the lag indices `|m| ≤ ⌊dirLen P δ' N / 2⌋`. -/
def middleLag (P : Polynomial ℤ) (δ' : ℝ) (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(((dirLen P δ' N / 2 : ℕ)) : ℤ)) (((dirLen P δ' N / 2 : ℕ)) : ℤ)

/-! ## A **sharpened level-one branch**: the modulation-invariant form

`Work.Peluse.BoxNorm.uNormPow_mul_ee` (`hs : 2 ≤ t`) says that the level-`t` box-norm power of a
finitely supported `f` is **unchanged** by modulating `f` by the character `x ↦ ee (β x)`.
Applied to the *level-one* norm of the modulated function and composed with the
Gowers–Cauchy–Schwarz level raising `uNormPow_two_ge_of_uNorm_one`, this gives, for every `β`,

  `c·(uNormPow 1 (κ[L]) (symIcc N₁) (g₂ · ee (β·)))² ≤ uNormPow 2 (κ[L]) (symIcc N₁) g₂`,

so the level-one branch `targetAprimeTwo_of_largeUOne` (the case `β = 0`) may be sharpened to
**all** `β`:

  `∃β, θγ² ≤ uNormPow 1 (κ[L]) (symIcc N₁) (g₂ · ee (β·))  ⟹  c·θ²·γ⁴ ≤ uNormPow 2 (κ[L]) … g₂`.

**Spectral reading.**  By `Concat.uNormPow_one_eq_autocorr`,
`uNormPow 1 (κ[L]) (symIcc N₁) (g₂·ee (β·))` is (up to `L⁻²`) the *Fejér transform of the dilated
autocorrelation*,
`Σ_{|e|<L} cntW L e · autocorr N₁ g₂ (κe) · ee (βκe) = ∫ K_L(κ(θ+β)) dμ(θ)` for the spectral measure
`μ` of `g₂`; since `K_L` is a (nonnegative) Fejér kernel of width `1/L`, this is, up to the Fejér
factor `L²`, **the mass of `μ` in the window of width `≈ 1/(κL)` around `−β`**.  Hence the
negation of the branch's hypothesis — the clause that goes into the residual — says:

> **no window of width `1/(κL)` carries more than `θγ²`-worth of the spectral mass of `g₂`,**

i.e. *the spectral measure of `g₂` is spread at scale `1/(κL)`*.  This is exactly the hypothesis
whose negation the source's §6 major-arc analysis (Peluse's Lemmas 3.9/3.10) must produce from the
coherence `γ ≤ ‖ΛZ‖`: with this clause the residual's content becomes the **contrapositive of the
major-arc lemma**, stated in the target's own vocabulary (see the residual below). -/

/-! ## The van der Corput (§4) chain of the coherence: from `ΛZ` to the polynomial-difference lags

The three proved steps of the source's §4 (its van der Corput/PET step, in its crudest one-round
form) are, all in the `Hyp`/`ΛZ` vocabulary:

1. `Work.Peluse.UControl.hyp_curveSecondMoment` — the coherence in *second moment* form:
   `γ²N₁N²/3 ≤ Σ_{x∈symIcc N₁} ‖Σ_{y ∈ [1,N]} g₁(x+y)·g₂(x+P(y))‖²` (Cauchy–Schwarz in `x`);
2. `Work.Peluse.UControl.hyp_curvePairLagSum` — the van der Corput inequality in `y`:
   the same sum is bounded by the **pair correlations at the polynomial differences**
   `P(y+hh) − P(y)`, i.e. by `Σ_{|hh|<N} Σ_x ‖Σ_{y: y, y+hh ∈ [1,N]} …‖` with `N` in the
   denominator;
3. `Work.Peluse.UControl.curvePair_inner_le_autocorr` — the change of variables `u = x + P(y)`
   turns each inner sum into a pure `g₂`-correlation at the lag `P(y+hh) − P(y)`;
4. `Work.Peluse.UControl.curvePair_ySum_le_autocorr` — the triangle inequality in `y` and the
   (proved) window inclusion `symIcc N₁ + P(y) ⊆` `symIcc N₁` (which is where `SupportIn g₂ N₁` is
   used) reassemble the `x`-sum into the *unshifted* autocorrelation sum.

The composition of 2 and 4 is the statement below: a lower bound for the sum, over the
difference-lag multiset `{P(y+hh) − P(y)}`, of the pair correlations `Σ_u ‖g₂ u‖‖g₂ (u+Δ)‖`.

**Where the chain stops (recorded, not re-derivable).**  The target needs a lower bound for the
*weighted `ℓ²`-sum* `Σ_{|m|<L} cntW L m ‖autocorr N₁ g₂ (dirCoeff P·m)‖²` at the *single* dilated AP
`dirCoeff P·[L]` — whereas the chain above produces an *`ℓ¹`-type* bound for a *multiset* of lags of
size `≈ N²`.  The two quantifiers are not comparable: `Σ_u ‖g₂ u‖‖g₂ (u+Δ)‖ ≥ |Σ_u conj (g₂ u) g₂
(u+Δ)|` bounds an `ℓ¹`-sum *above* by the ℓ²-quantities of the target, and the direction is wrong;
and for `deg P ≥ 3` the difference-lag multiset (`~N²` elements, spread over a range `~N^{deg P}`)
cannot even cover the AP `dirCoeff P·[L]` (`L = ⌊δ'N^{deg P}⌋` elements).  So this chain *documents*
the coherence's elementary consequences but does **not** reach the target: the missing input is the
*level-2 (or level-`s`) inverse theorem* of the residual below, exactly as the source's §5–§6
(concatenation + major arcs) says. -/

/-! ## The `γ^{K₀}`-arithmetic: the datum's own exponent vs `N₁`

Two facts about `Hyp` that every future prover of the residual needs, because they say *how small
`γ^{K₀}` can be* on the residual's data:

* `Hyp.one_le_dirLen` (`assembly.lean`, pre-existing) — `1 ≤ dirLen P δ' N`.  (Recorded here
  because it is the hypothesis `1 ≤ L` of every box-norm brick; `Hyp` itself records only the
  non-degeneracy of the *PET window*
  `⌊δ'N⌋`, not of the direction length `⌊δ'N^d⌋`; since `N^d ≥ N` for `d = deg P ≥ 2`, the latter
  follows.  This is the hypothesis `1 ≤ L` of every box-norm brick, and it is **not** available by
  `rfl` from `Hyp`.)
* `hyp_gammaPow_lower` — `1/N₁ ≤ γ^{K₀}` for `K₀ ≤ K`.  Together with the (sharper)
  `hyp_gamma_pow_ge` this is what pins the residual's data into the **near-maximal-coherence**
  regime: `Hyp`'s smallness conjunct `C·L ≤ γ^K·N₁` with `C ≥ 1`, `L ≥ 1` reads `γ^K ≥ 1/N₁`, and
  `γ^{K₀} ≥ γ^K` because `γ ≤ 1` and `K₀ ≤ K`.  (Sharper still: raising the PET gauge
  `1 ≤ (γδ')^K(δ'N)²` to the power `K₀/(K(K+3))` gives `γ^{K₀} ≥ (2A')^{-1}N^{-2/(K₀+3)}`, cf.
  `hyp_gamma_pow_ge`.)

Note the *direction*: these are **lower** bounds for `γ^{K₀}`, so they make the target's conclusion
`cst·γ^{K₀} ≤ uNormPow …` *harder*; what they buy is that the residual's data are confined to
`γ ≥ 1/N₁^{1/K₀}` — i.e. `γ → 1` as `K₀ → ∞` — which is the regime in which the band's *structure*
mechanisms (periodicity, dense invariance, rigidity) are the only ones available.  Recorded so that
nobody re-derives them and nobody tries the small-`γ` branches on the residual. -/

/-- **`γ^{K₀}` is at least `1/N₁`** (so the residual's conclusion is a *near-constant* lower bound
once `K₀` is large).  From `Hyp`'s `C·L ≤ γ^K N₁` with `C ≥ 1` and `L ≥ 1`. -/
lemma hyp_gammaPow_lower {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ}
    {g₀ g₁ g₂ : ℤ → ℂ} {γ δ' : ℝ} {K₀ : ℕ} (hK : K₀ ≤ K)
    (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') :
    1 / (N₁ : ℝ) ≤ γ ^ K₀ := by
  have hL1 := Hyp.one_le_dirLen h
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsmall, hpet,
    hs0, hs1, hs2, hb0, hb1, hb2, hΛ⟩ := h
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast hN₁
  have hone : 1 ≤ γ ^ K * (N₁ : ℝ) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
      _ ≤ C * (dirLen P δ' N : ℝ) :=
          mul_le_mul hC1 (by exact_mod_cast hL1) (by norm_num) (by linarith)
      _ ≤ γ ^ K * (N₁ : ℝ) := hsmall
  have h2 : 1 / (N₁ : ℝ) ≤ γ ^ K := by
    rw [div_le_iff₀ hN₁pos]
    linarith
  exact le_trans h2 (pow_le_pow_of_le_one hγ0.le hγ1 hK)

/-- **The residual's conclusion is a constant bound.**  Consequently the *constant* form of the
conclusion implies the target's `cst·γ^{K₀} ≤ uNormPow 2 …` form: since `γ ≤ 1` and `K₀ ≥ 1`, the
quantity `γ^{K₀}` is at most `1`.  (Recorded because every branch below is stated with a
`γ`-power, while the elementary mechanisms produce *constant* bounds; this is the lemma that lets
the two be compared.) -/
lemma le_uNormPow_of_const_le {κ : ℤ} {L N₁ : ℕ} {g₂ : ℤ → ℂ} {γ : ℝ} {K₀ : ℕ} {cst : ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hc0 : 0 ≤ cst)
    (hc : cst ≤ uNormPow 2 (arithIcc κ L) (symIcc N₁) g₂) :
    cst * γ ^ K₀ ≤ uNormPow 2 (arithIcc κ L) (symIcc N₁) g₂ := by
  have h1 : γ ^ K₀ ≤ 1 := pow_le_one₀ hγ0.le hγ1
  calc cst * γ ^ K₀ ≤ cst * 1 := mul_le_mul_of_nonneg_left h1 hc0
    _ = cst := mul_one _
    _ ≤ _ := hc

/-! ## A new branch: bulk quasi-periodicity with a large fourth-moment mass

`Work.Peluse.UControl.bandCubeCollapse` (proved, axiom-clean) is the analytic half of the tree's
*exact-coherence rigidity* (`Work.Peluse.UControl.bandRigidConcl`): if `f` is `1`-bounded, supported
in `symIcc N₁`, and **quasi-periodic with a unit multiplier `lam` and a period `g ∣ dirCoeff P`** on a
bulk window `symIcc B` (`B` up to `N₁`), then

  `c·(Σ_{x ∈ symIcc (B − 2|κ|L)} ‖f x‖⁴ − 8(N₁ − B))/N₁ ≤ uNormPow 2 (κ[L]) (symIcc N₁) f`.

Feeding it with a lower bound for the bulk fourth-moment mass gives a **constant** lower bound for
the level-two box-norm power, and hence the target (`le_uNormPow_of_const_le`).  This is a genuinely
new branch of the target — a *quantitative* "structure + mass" condition, not a Fourier/mean/
autocorrelation condition — and its complement is a new clause available to the residual.  It is the
first branch of this file that consumes a *periodicity* hypothesis rather than a size hypothesis on
`g₂`. -/

/-! ## The residual: the single remaining obligation, with every proved branch discharged

The eight proved branches above (`targetAprimeTwo_of_largeFourier`, `targetAprimeTwo_of_largeMean`,
`targetAprimeTwo_of_boundedDirLen`, `targetAprimeTwo_of_largeUOne`, `targetAprimeTwo_of_largeLmass`,
`targetAprimeTwo_of_largeA`, `targetAprimeTwo_of_nearLag`, `targetAprimeTwo_of_largeAutocorr`)
cover, at level two:

* every datum having **one large Fourier coefficient** (`resEps·γ·N₁ ≤ ‖∑_x g₂ x · ee(βx)‖`, some
  `β`);
* every datum of **large mean** (`resEps·γ·N₁ ≤ ‖∑_x g₂ x‖`);
* every datum of **bounded direction length** (`dirLen P δ' N ≤ resLb`);
* every datum of **large level-one box norm** (`resEps·γ² ≤ uNormPow 1 (κ[L]) (symIcc N₁) g₂`);
* every datum of **large level-two diagonal mass**
  (`18(1+|κ|)γ⁴L ≤ (Lmass N₁ g₂ 2)²`);
* every datum of **large `A'`** (`N₁ ≤ massDiagC P·A'^4`);
* every datum of **large `γ̃`-weighted near-lag moment**
  (`resEps·γ² ≤ nearLagMoment |κ| L L (max N₁ (|κ|L)) g₂`);
* every datum with **one large dilated autocorrelation**
  (`resEps·γ²·L ≤ ‖autocorr N₁ g₂ (κe)‖` for some `|e| < L`, in particular the diagonal case
  `e = 0`, i.e. `Lmass`).

Composing them with the level raising `uNormPow_level_raise_win 2 s` reduces the whole target to the
data lying in the **complement** of all eight (and of the ninth, `targetAprimeTwo_of_flatProfile`,
handled in the assembly's innermost layer), i.e. to the tree's residual
(`ResidSharpEx` / `BandResidualSmallFourier` / `BandDegenerate` / `FlatBand` in the `BandHyp`
normalisation).  That complement is packaged below; it is the single obligation that remains, and
it is *non-vacuous*: the comb datum `g₂ = 1_{qℤ}` satisfies the mean, direction-length, level-one,
mass and near-lag inequalities (it is settled by the *large-Fourier* branch), so this is genuinely
the crux and not an artefact of the quantifiers.  (Session 9 replaced the ninth complement — the
pointwise non-flatness — by the *middle-mass* one, in `ResidualAprimeStrong` below; see the section
on the averaged flat-profile branch.) -/

/-- The **threshold** of the residual's Fourier and mean conditions: an explicit small constant.
Taking it as small as possible *improves* the reduction: a smaller `ε` makes the residual's
hypothesis-set smaller (hence the residual easier), while the proved branches — whose constants
degrade with `ε` but stay positive — cover the complement. -/
def resEps : ℝ := 1 / 1000000

/-- The **threshold** of the residual's direction-length condition: an explicit large constant (same
remark: a larger `Λ` shrinks the residual's hypothesis-set). -/
def resLb : ℝ := 1000000

lemma resEps_pos : 0 < resEps := by rw [resEps]; norm_num

lemma resLb_ge_one : 1 ≤ resLb := by rw [resLb]; norm_num

/-! ## The twelfth complement: bulk quasi-periodicity with a large fourth-moment mass

The branch `targetAprimeTwo_of_bulkPeriodicMass` above produces a **constant** lower bound for
`uNormPow 2 (κ[L]) (symIcc N₁) g₂` (its `θ := 1` form is
`targetAprimeTwo_of_bulkPeriodicConstMass`), and hence settles the residual's conclusion, on every
datum for which `g₂` *is* quasi-periodic with a period dividing `κ` over a bulk window and carries
enough fourth-moment mass there.  Its hypothesis is packaged below as `BulkPeriodicMassAt`, and the
residual is restated with its **negation** as an extra clause.  This is the first clause of the
residual that is *structural* in the `L²`-sense — the earlier ones are all size conditions on `g₂`
(Fourier coefficients, mean, level-one norm, `Lmass`, autocorrelations, middle-half `ℓ²`-mass,
modulations) — and it upgrades the residual to the "no bulk periodic mass" form. -/

/-- **The bulk-periodicity-with-mass condition** whose *negation* is the residual's twelfth clause:
there is a period `gB ∣ dirCoeff P`, a unit multiplier `lam` and a bulk window `symIcc B`
(`B` up to `N₁`) on which `g₂` is `lam`-quasi-periodic, and the fourth-moment mass of `g₂` on the
shrunken window exceeds the annulus error `8(N₁ - B)` by at least `N₁`. -/
def BulkPeriodicMassAt (P : Polynomial ℤ) (δ' : ℝ) (N N₁ : ℕ) (g₂ : ℤ → ℂ) : Prop :=
  ∃ (gB : ℤ) (lam : ℂ) (B : ℕ),
    0 < gB ∧ gB ∣ dirCoeff P ∧ ‖lam‖ = 1 ∧
    2 * ((dirCoeff P).natAbs * dirLen P δ' N) ≤ B ∧ B ≤ N₁ ∧
    (∀ z : ℤ, z ∈ symIcc B → z + gB ∈ symIcc B → g₂ z ≠ 0 → g₂ (z + gB) = lam * g₂ z) ∧
    8 * ((N₁ - B : ℕ) : ℝ) + (N₁ : ℝ)
      ≤ ∑ x ∈ symIcc (B - 2 * ((dirCoeff P).natAbs) * (dirLen P δ' N)), ‖g₂ x‖ ^ 4

/-! ## The target (statement of the assignment; its content is the band's inverse theorem) -/

end

end Work.Peluse.UControl
