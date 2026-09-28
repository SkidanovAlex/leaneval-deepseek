import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.ballConeWeightedKw_alt
import Submission.Work.HP.MM2.lam_GamMix_le
import Submission.Work.HP.MM2.IcVol_point_unif
import Submission.Work.HP.coneSliceVol_GamMix
import Submission.Work.HP.detL_GamMix
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Lat.card_Mon
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.MDEstimates.ball_count_R0
import Submission.Work.HP.MM2.ballConeWeightedKw
import Submission.Work.HP.MM2.lam_GamMix_le
import Submission.Work.HP.MM2.IcVol_point_unif
import Submission.Work.HP.coneSliceVol_GamMix
import Submission.Work.HP.detL_GamMix

/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `Sk1_mix_ell` in namespace Work.HP.MM2; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.MM2.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.MM2.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

===== DESIGN_REVIEW.md =====
# annals_hasse_principle_random_fano: design review of H15 (`moment_mix_loc`) and H9 (`density`)

2026-09-27, about 21:45. The workspace on 3.144.32.173 was read only.

Files in this folder:
* `MMPair.lean`: statements for §1, namespace `Work.HP.MM2`.
* `DensityRoute.lean`: statements for §2, namespace `Work.HP.DN`.
* `coimport_check.lean`: a co-import test to run after fixes F1 and F2.

Both statement files elaborate against the workspace with
`lake env lean`. The only warnings are "declaration uses sorry". They import only `Defs`,
`MMDefs` and `density_aux`, so they are unaffected by the import clashes below. The new
namespaces are fresh, so nothing collides.

---

## 0. Workspace fixes first (lead actions; they unblock both nodes)

**"`EE ≍ B²` fails in the workspace" means the module does not elaborate. The statement is not false.**

* Lemma E is true, and both halves have sorry-free sources:
  * `EE_lower_all`: axioms are clean.
  * `EE_upper_all`: its closure has sorries only in `gon`, `FM.primBasis`, `Sig2.minkowski_prod`
    and `ball_count_schmidt`.
* `det_averages` has never had an olean, for two reasons:

**F1. `Work.HP.rk_le_card` is defined three times.**
* The copies are in `rk_le_card.lean:21`, `PairsAux.lean:40` and `ball_count_schmidt.lean:346`.
  The last one was added at 20:37.
* Result: `FM/schmidt_bound` fails with "environment already contains `Work.HP.rk_le_card`"
  and has no olean.
* Everything above it cannot be imported: `EE/ellAux`, `EE_upper_all`, `EE/ellXY_two_pub`,
  `FF_bound`, `det_averages`.
* Fix: keep `rk_le_card.lean`. In the other two files, delete the copy and
  `import Submission.Work.HP.rk_le_card`.

**F2. `Work.HP.toR_veronese` has two different statements.**
* `WedgeDefs.lean:63` states it with `veroneseR`. `eNorm_veronese_bounds.lean:37` states it with
  `veronese` over ℝ.
* `EE_upper_all` reaches `WedgeDefs` through `EE/wedgeNorm_veronese`. `EE_lower_all` reaches
  `eNorm_veronese_bounds`. So `det_averages` can never co-import its two halves.
* The same clash blocks `FM.key_lemma_one_vector`, `detGam_pt`, `EEupper.detL_Gam_lower`,
  `HP3.dmin_le_norm_mul_dual` and `FF_bound` against the N09 closure (via `MMVec`). I tested
  this on the box.
* Fix: in `WedgeDefs`, rename `toR_veronese` to `toR_veronese_R`. Update:
  * `WedgeDefs.lean` lines 72, 77, 82;
  * `EE/wedgeNorm_veronese.lean:209`.
* Also rename the duplicate `eNorm_eq_rNorm_toR` (`WedgeDefs:58`, which also exists in
  `eNorm_veronese_bounds:30`) to `eNorm_eq_rNorm_toR_W`. Update:
  * `WedgeDefs` lines 61, 72;
  * `EE/wedgeNorm_veronese:209`;
  * `Vero/lamR_dual_latOrth:77`;
  * `HP3/wedgeNorm_eq_of_sub:85`;
  * `veronese_wedge` lines 41, 394.
* Then rebuild the 8 importers of `WedgeDefs`.

**F3. `FM.key_lemma_one_vector` needs no new work.** Its 2 sorries have sorry-free twins:
* `FM/prod_vec_span` (child H5-L381) is `Work.HP.Vero.prodVec_span_eq_ker`. It needs `1 ≤ n`,
  which holds because `n ≥ d ≥ 2`.
* `FM/transf_dual_le` (child H5-L404) is `Work.HP.FM3.transf_extreme`. The statement is
  identical and the axioms are clean.
* I tested that the three modules co-import cleanly. Tell H5 to substitute them and cancel
  L381 and L404.

**F4. Rebuild `IcVolAsymp`.**
* Its olean dates from 17:44, which is before `IcVolEst/bandVolAsymp` was fixed at 20:05.
* `#print axioms Work.HP.IcVolAsymp` currently reports `sorryAx`. The source closure is sorry-free.

**F5. Latent clashes to fix before they bite.**
* `detL_GamLoc` redefines `Work.HP.isPrim_veronese` and `Work.HP.mem_latMod_iff`, which are
  also in `detL_GamMix`. Make them `private`; H15-L243 owns the file.
* `H5`'s `degen_count_free`, `ell_two_single_le` and `Diag/ell_single_count` are sorry'd.
  They state the same thing as the sorry-free `FM3.ell_two_count_free`, so close them by
  reference.
* Identical duplicates seem to be tolerated on import: `DiagDefs`/`MMReindex` `Xi_finite`
  co-import fine. Different proofs are not tolerated (`rk_le_card`).
* Rerun `coimport_check.lean` after F1 and F2.

---

## 1. H15 `moment_mix_loc`: the pair-summation route

### 1.1 Diagnosis

H15 has the reindexing (`DmixReindex`, `DlocReindex`), the Möbius identities, the cone count,
the determinant identities, the volume asymptotics and `moebiusZetaTail`. Three things are missing:

**(a) The per-pair asymptotic with a uniform relative error.** Two sub-points:
* The weighted cone count must carry the *weighted* short-vector term. With the unweighted
  count, the small-ball error is a factor `Y` too big.
* `MMtest4.IcVol_point` has `∃ C` *after* `x y`. Such a non-uniform constant cannot be summed
  over pairs. `IcVolAsymp`'s constant only depends on `ι`, so the uniform version is immediate.

**(b) Degenerate `x`, where `λ_{N-1}(Λ_{ν(x)})` is large.** The paper handles these with the
`G_{d,n}` sum `Σ_Ω μ(x)/det Γ ≪ B^{2+1/(n(n+1-d))}`. That sum needs a 4-fold dyadic interpolation.

**(c) The worry that the relative error is `(λ/u)/V` with `V ≍ Δ/α`.** This is harmless: `Δ(x,y) ≥ 1`,
so the relative error is `≤ αWλ(x)/A`.

### 1.2 Route (it deviates from the paper in the split)

**Split `Ω` by the intrinsic quantity `λ(x) := λ_{N-1}(Λ_{ν(x)})` (`MM2.lamX`).**
* `OmegaGood` is the set of pairs with `W λ(x) ≤ A^{3/4}`. `OmegaBad` is the rest.
* The paper splits at `μ(x) ≤ A/W`, which forces the μ-weighted `G` sum.
* With `A^{3/4}`, every per-pair error on `OmegaGood` is uniformly `≤ C/log A`. The worst ones are:
  * `αA^{-1/4}`;
  * `w^{-(N-3)}`;
  * `A^{-(N-3)/4}`;
  * the small-ball term `αW·log A·[(A^{-1/4})^{N-2} + A^{3(N-n-2)/4}B^d/A^{N-2}]`. This needs
    `9n/20 < (N-2)/4`, which holds because `N ≥ (n+1)(n+2)/2`.
* So `Σ₁` needs no `G` sum, and the key lemma is not used in `Σ₁`.
* `OmegaBad` needs only two things:
  * an **unweighted** pair sum, which is 3-fold dyadic with no `𝔡₂(x)` variable: `deg_pair_sum`;
  * single-vector degenerate sums, which are 1-fold dyadic: `degen_shell_sum`.

**Per-ℓ step.**
* `ballConeWeightedK'` does the Abel summation. Use it with `k=1, v=ν(y), w=0, Y=Qλ(x)` for the
  mixed moment, and with `k=2, Y=Q` for the local one.
* Then substitute `detL_GamMix`/`detL_GamLoc`, `coneSliceVol_*` and `IcVol/JcVol_point_unif`.
  The factor `(N-1)/(N-2)` cancels against the volume constant `(N-2)/(N-1)`, and likewise
  `N/(N-2)` against `(N-2)/N`.

**Per-pair step.** Apply `SstarMobiusMix`/`Loc`:
* For `ℓ ≤ L₀ = A/(Wλ)` (≥ `A^{1/4}`), use the per-ℓ lemma.
* For larger `ℓ`, use `S1ball(x, Wλ)` times `(1+log A)`.
* The `ℓ`-sum of `μ(ℓ)·gcd(ℓ,W)^k·g_ℓ/ℓ^{N-2+k}`, with `g_ℓ = gcd(W/gcd(ℓ,W), 𝒢)`, is handled by:
  * `gcd_div_gcd_eq`: `g_ℓ = 𝒢` for squarefree `ℓ` when `𝒢 | W/rad W`; otherwise `0 ≤ g_ℓ ≤ 𝒢`,
    and the indicator lands in `errXY`;
  * `moebius_gcd_zeta`: `ℓ | W` for `ℓ ≤ w` by `w_arith`.
* `DeltaXY_gcd_detL` then turns `V A^{N-2}Δ𝒢/(ζ αW‖ν(x)‖)` into `mixMain = 8ι A^{N-2}‖ν(y)‖/(αW det Γ)`.

**Sum over pairs.**
* The weight is `αW/(4‖ν(y)‖)`, which turns `mixMain` into `2ιA^{N-2}/det Γ`.
* So `Σ₁ = mainTerm − 2ιA^{N-2}Σ_{OmegaBad}1/det Γ + O(2ιA^{N-2}(FF + EE/log A))`.
* Close with `FF_bound`, `EE_lower_all` and `OmegaBad_mass`.
* **`EE_upper_all` and `det_averages` are not needed for N09.**

**`Σ₂^{mix}` (`OmegaBad`) is an upper bound only.**
* Start from `Sstar1 ≤ S1ball(x, A)`.
* Apply `S1ball_le` with `μ = max(A, C‖x‖/𝔡₂(x))`, using the key lemma.
* Use `Σ_y 1/‖ν(y)‖ ≪ B` (`FM4.xi_sum_vero`).
* Use `degen_shell_sum` with `s = −d` and `s = 0` (threshold `A^{3/4}/(CW)`), and with
  `s = n−1−d` (threshold `A/C`).
* Relative to `A^{N-2}B²`, the exponents are `6/5 − 9/4`, `1 − 4n/5` and `(24−11n)/20`.
  The worst case is `n = d = 3`, giving `A^{-9/20}`. The statement uses `A^{-1/20}`.

**`OmegaBad_mass`.**
* The key lemma gives `OmegaBad ⊆ {t𝔡₂(x) ≤ ‖x‖}` with `t = A^{3/4}/(CW)`.
* `detGam_pt` gives `1/det Γ ≤ C/(𝔡₂(x,y)‖x‖^{d-1}‖y‖^{d-1})`.
* `deg_pair_sum` then gives `≪ B²·X^{1/n}·log³/t`.
* Since `X^{1/n} ≤ B^{1/3} ≤ A^{2/5}`, this is `≤ B²A^{-1/4}`.

**`D^loc`.**
* There is no degenerate part: `λ_N(GamLoc(Q)) ≤ Q ≤ W` for every pair.
* The uniform errors are `α²W/A`, `w^{-(N-3)}`, `(W/A)^{N-3}` and `W^{N}α²W²/A^{N-2}`.

**Final assembly.** Combine `Dmix_split`, `Sigma1mix_estimate`, `Sigma2mix_bound` and
`Dloc_estimate`, using `A^{-1/20} ≤ (log A)^{-1/2}` eventually.

**`deg_pair_sum` proof, in one line.**
* Take a box `‖x‖~X`, `‖y‖~Y`, `𝔡₂(x,y)~Δ`.
* The number of pairs in the box is `≤ min(ℓ₁(X;X/t)·#B(Y), ℓ₂(X,Y;Δ)) ≤ a^{1/n}b^{1-1/n}`, where:
  * `ℓ₁` comes from `FM3.ell_two_count_free` and is sorry-free;
  * `ℓ₂` comes from `EE.ellXY_two_pub`.
* Summing over the box gives `X^{4-d}Y^{4-d-1/n}Δ^{n-3+1/n}/t`.
* Since `Δ ≤ XY`, this is `X^{n+1-d+1/n}Y^{n+1-d}/t`.
* Summing over `X, Y ≤ B^{1/(n+1-d)}` gives `B²X^{1/n}/t`.
* I checked this against the paper's `G_{d,n}` computation (TeX lines 3075–3106).

### 1.3 Lemmas: size (k lines, DeepSeek) and dependency order

| id | name (`Work.HP.MM2`) | uses | k |
|---|---|---|---|
| L0a | `lam_GamMix_le` | `index_GamMix`, `one_le_lam` | 0.2 |
| L0b | `lam_GamLoc_le` | `finrank_latMod_inf` | 0.15 |
| L0c | `ballConeWeightedK'` (**replaces** the in-flight `ballConeWeightedK`; the count version follows in 5 lines) | `ballConeCount` | 0.5–0.8 |
| L0d | `IcVol_point_unif` | `IcVolAsymp` (F4) | 0.1–0.2 |
| L0e | `JcVol_point_unif` | `JcVolAsymp` | 0.15 |
| L0f | `S1ball_le` | `latOrth_count_degenerate`, `latOrth_count_pivotal` (both sorry-free) | 0.3–0.5 |
| L0g | `moebius_gcd_zeta` | `moebiusZetaTail`, `w_arith` | 0.3–0.4 |
| L0h | `gcd_div_gcd_eq` | — | 0.1–0.2 |
| L0i | `degen_shell_sum` | `FM3.ell_two_count_free` | 0.3–0.5 |
| L0j | `deg_pair_sum` | `FM3.ell_two_count_free`, `EE.ellXY_two_pub` (F1) | 1.0–1.5 |
| L1a | `Sk1_mix_ell` | L0a, L0c, L0d, `detL_GamMix`, `coneSliceVol_GamMix` | 0.3–0.5 |
| L1b | `Sk2_loc_ell` | L0b, L0c, L0e, `detL_GamLoc`, `coneSliceVol_GamLoc` | 0.3–0.5 |
| L2a | `Sstar1_mix_pair` | L1a, L0f–h, `SstarMobiusMix`, `DeltaXY_gcd_detL`, `bigW_le_pow` | 0.8–1.2 |
| L2b | `Sstar2_loc_pair` | L1b, L0g–h, `SstarMobiusLoc` | 0.6–0.9 |
| L3a | `OmegaBad_mass` | L0j, key lemma (F2, F3), `detGam_pt` | 0.2–0.3 |
| L3b | `Dmix_split` | `DmixReindex` | 0.1–0.2 |
| L3c | `Sigma1mix_estimate` | L2a, L3a, `FF_bound` (F1, F2), `EE_lower_all` | 0.3–0.5 |
| L3d | `Sigma2mix_bound` | L0f, L0i, key lemma, `FM4.xi_sum_vero` | 0.5–0.8 |
| L3e | `Dloc_estimate` | L2b, `DlocReindex`, `FF_bound` | 0.3–0.5 |
| — | `moment_mix_loc` | L3b–e | 0.1 |

The new work totals about **6.5–10k**, on top of what H15 has already proved. Dispatch order:
* **Now, in parallel:** all L0.
* **Then:** L1 (needs L0c).
* **Then:** L2.
* **Then:** L3a–e.
* **Then:** the final assembly.

L0j is the long pole. Start it first.

### 1.4 What NOT to build (N09)

* No μ-weighted `G_{d,n}` sum and no `𝔡₂(x)`-dyadic variable. The `A^{3/4}` split removes them.
* No per-`t` partial-summation integrals. `ballConeWeightedK'` packages them.
* No key lemma inside `Σ₁` or `D^loc`. The intrinsic `lamX` suffices there.
* No `det_averages` or `EE_upper_all` import. Use `EE_lower_all` and `FF_bound`.
* Do not use H5's `degen_sum`/`degen_sum_free`. Their bounds `K A^{n-1}B` and `K A^n B` are too
  weak for `Σ₂^{mix}` by a factor `A`.
* Do not finish the unweighted `ballConeWeightedK` on its own; make L0c the lemma.
* Do not use `MMtest4.IcVol_point`, whose constant is not uniform.

---

## 2. H9 `density`: route

### 2.1 Diagnosis

H9's fixed level is `LocSet M`, with exponents `r_p(M)`. With it, the deep-failure loss
`Σ_{p≤M} p^{-r_p(M)/2}` is only `≍ 1/log M`. Showing it tends to 0 needs Chebyshev-type prime
counting. **Replace the fixed level** by
`SM M := RealSol ∧ ∀ p ≤ M prime, PrimModZero a p (4M)`. Its loss is `≤ M·4^{-M}`.

The analytic input H9 lacks is the existence of `lim ratio(SM M)`:
* primitivity;
* a real cone;
* congruences.

**Only existence is needed.** The route below is measure-theoretic: a Riemann/Jordan argument
with no error terms and no boundary counts.

### 2.2 Route (statements in `DensityRoute.lean`)

**D1 `card_shift_div_pow_tendsto`.**
* The claim: `#{z : (z+v)/m ∈ s}/m^N → vol s`, for `s` bounded with null frontier and `v ∈ [0,1]^N`.
* Proof: copy `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`
  (`tendsto_card_div_pow_atTop_volume`) with the tag `(ν+v)/m`.
* The tag stays in the closed box, so Riemann integrability still applies.
* Fallback: a cube sandwich between `{x : B(x,δ) ⊆ s}` and `cthickening δ s`, plus continuity
  of measure.

**D2 `realSolCone_facts`.** The cone is closed and scale-invariant, and
`frontier(cone ∩ ball)` is null. Case `d` odd:
* The cone is everything: `f(−x) = −f(x)` and the intermediate value theorem.

Case `d` even:
* Let `m(t) = min_{S^n} f_t` and `M(t) = max_{S^n} f_t`. Both are Lipschitz in `t`.
* The cone is `{m ≤ 0 ≤ M}`. Its interior contains `{m < 0 < M}`, by the intermediate value
  theorem on the connected sphere. So the frontier lies in `{m = 0} ∪ {M = 0}`.
* Let `u` be the coefficient vector of `Σx_i^d`. Then `m(t+su) > m(t)` for `s > 0`.
* So the translates `{m=0}+su` are pairwise disjoint and have equal measure. σ-finiteness
  forces measure 0.
* `{M = 0} = −{m = 0}`. The Euclidean sphere is null.

**D3 `periodic_count_tendsto`.**
* Sum D1 over the `Q^N` classes, with `v = c/Q` and `m = T/Q`.
* Handle real `T` by the floor/ceiling sandwich, as in Mathlib's `…_volume'`, using star-shapedness.

**D4 `prim_periodic_cone_tendsto`.**
* Möbius over `gcd(a)`: reuse `Sstar_moebius_abstract` with `k=0`.
* For each `k`, apply D3 to the `Q`-periodic `P(k•·)`.
* Pass to the limit with Tannery (`tendsto_tsum_of_dominated_convergence`) and the bound `C k^{-N}`.

**D5 and D5'.** `PrimModZero` is `p^r`-periodic, and the `p`-adic part of `SM` is `QM`-periodic.

**D6 `SM_ratio_tendsto`.** Apply D4 with `K` = the cone and with `K` = everything. Use
`count_basic` to make the denominator's limit positive.

**D7 `deep_failure_count`.** Consider a primitive zero mod `p^{4M}` that does not lift to `p^R`.
* Its gradient valuation is `e ≥ 2M`. Otherwise `hensel_lift` applies, because `2e+1 ≤ 4M`.
* So the residue class lies in `⋃_{e=2M}^{4M} NA.Rset e`.
* `NA.card_Rset_le` bounds this union by `4p^{4MN−2M}` classes. It is sorry-free.
* Count each class with `primCount_residue_le`, using `A ≥ p^{4M}`.
* Result: `≤ 4·3^N A^N p^{-2M}`.

**D8 `bad_prime_count`.**
* No primitive zero mod `p^R` forces `a mod p ∈ BadCls`. Otherwise `hensel_lift` applies with `e = 0`.
* `badclass.card_badCls_le` bounds `BadCls`. It is sorry-free, with exponent `n−1`.
* Count each class with `primCount_residue_le`, using `p ≤ w ≤ A`.
* Result: `≤ C A^N p^{-(n-1)}`.

**D9 `SM_sandwich`.**
* Eventually `LocSet(w A) ⊆ SM M`, because `r_p(w) ≥ 4M` for `p ≤ M`.
* The difference is covered by:
  * D7 for `p ≤ M`, which is `≤ M/4^M`;
  * D8 for `M < p ≤ w`, which is `≤ Σ_{p>M} p^{-2} ≤ 1/M` since `n ≥ 3`.

**D10 `density'`.**
* This is exactly the node statement.
* Set `L = lim_M lim_A ratio(SM M)`. It exists because `SM (M+1) ⊆ SM M`, so the limits are antitone.
* Squeeze with D6 and D9.

### 2.3 Size (k lines) and order

| id | k | depends on |
|---|---|---|
| D1 | 0.4–0.8 | Mathlib |
| D2 (+ `realSol_iff`) | 0.6–1.0 | — |
| D3 | 0.3–0.5 | D1 |
| D4 | 0.4–0.7 | D3, `Sstar_moebius_abstract` |
| D5, D5' | 0.1–0.2 | — |
| D6 | 0.2–0.3 | D2, D4, D5', `count_basic` |
| D7 | 0.3–0.6 | `hensel_lift`, `NA.card_Rset_le`, `primCount_residue_le` |
| D8 | 0.2–0.4 | `hensel_lift`, `card_badCls_le`, `primCount_residue_le` |
| D9 | 0.3–0.5 | D7, D8, `count_basic` |
| D10 | 0.15–0.25 | D6, D9 |

The total is about **3–5k**. Dispatch order:
* **Now, in parallel:** D1, D2, D5, D7 and D8.
* **Then:** D3, D4, D6 and D9.
* **Then:** D10.

`card_badCls_le` has no olean yet, though its closure is sorry-free. Build it.

### 2.4 What NOT to build (N14)

* No fixed level with `r_p(M)`. Use `4M`.
* No explicit density value, error rate or boundary-layer count.
* No cone extension of `card_ball_mod_sub`, and no use of `Uset`/`boundary` from N12.
* No ℚ_p-points, adelic construction or Poonen–Voloch.
* No further σ-moment work; `card_badCls_le` is enough.
* H9's `le_of_density_le` and `le_of_density_liminf` are tied to `LocSet M`. D9 and D10 replace
  them, and the replacement is shorter.

---

## 3. Where I am unsure

**The deviation from the paper.** The `A^{3/4}` split and the unweighted `deg_pair_sum` are
mine, not the paper's.
* I rechecked the exponents by hand. The margins are smallest at `n = d = 3`:
  * `A^{-0.45}` in `Σ₂`;
  * `A^{-7/20}` in `OmegaBad_mass`.
* `(3,3)` is inside N09's range, even though it is excluded overall.

**D1 may not transfer cleanly.** It assumes Mathlib's `UnitPartition` proof adapts to shifted
tags. Several of its lemmas are `private`, so the agent will have to copy them. The fallback is
the cube sandwich, estimated at 0.8k.

**The toleration of identical duplicate imports.** It is inferred from a successful co-import
(`DiagDefs`/`MMReindex`), not from reading the Lean source.

**`FF_bound` and `EE.ellXY_two_pub` still carry closure sorries** (`gon`, `FM.primBasis`,
`Sig2.minkowski_prod`, `ball_count_schmidt`), owned by H3, H11 and H4. The route above takes their
statements as given.
-/

namespace Work.HP.MM2

open Filter Finset MeasureTheory
open Work.HP

private lemma div_factor_alg (A Bv D G a q e x1 x2 : ℝ) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (ha : a ≠ 0) (hq : q ≠ 0) (he : e ≠ 0) :
    A * Bv * D * G / (a * q * e) = (x1 / x2 * A * (G / (q * e))) * (x2 / x1 * Bv * D / a) := by
  field_simp

private lemma div_detL_alg (x1 x2 Tv g q e Ic : ℝ) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (hg : g ≠ 0) (hq : q ≠ 0) (he : e ≠ 0) :
    x1 / x2 * Tv / (q * e / g) * Ic = x1 / x2 * Tv * (g / (q * e)) * Ic := by
  field_simp

private lemma err_alg (C Tv q lam g e : ℝ) (hq : q ≠ 0) (hg : g ≠ 0) (he : e ≠ 0) :
    C * Tv * (q * lam) / (q * e / g) = C * (Tv * lam * g / e) := by
  field_simp

lemma NN_ge_four (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 4 ≤ NN d n := by
  have hmain : (6 : ℕ) ≤ (n + d).choose d := by
    have h1 : (4).choose 2 = 6 := by decide
    have h2 : (4).choose 2 ≤ (2 * d).choose 2 := Nat.choose_le_choose 2 (by omega)
    have h3 : (2 * d).choose 2 ≤ (2 * d).choose ((2 * d) / 2) := Nat.choose_le_middle 2 (2 * d)
    have h3' : (2 * d) / 2 = d := by omega
    rw [h3'] at h3
    have h4 : (2 * d).choose d ≤ (n + d).choose d := Nat.choose_le_choose d (by omega)
    omega
  rw [NN, Lat.card_Mon]
  omega

lemma cgam_zero {ι : Type*} [Fintype ι] (γ : ℝ) : Cgam (0 : ι → ℝ) γ = Set.univ := by
  ext t; simp [Cgam, dotR, rNorm]

lemma S1ball_nonneg (d n : ℕ) [DecidableEq (Mon d n)] (x : Fin (n + 1) → ℤ) (T : ℝ) :
    0 ≤ S1ball d n x T := by
  rw [S1ball, finsum_mem_def]
  exact finsum_nonneg fun a => by
    by_cases h : a ∈ {a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T}
    · rw [Set.indicator_of_mem h]
      exact div_nonneg zero_le_one (eNorm_nonneg a)
    · rw [Set.indicator_of_notMem h]

lemma deltaXY_nonneg (d n : ℕ) (x y : Fin (n + 1) → ℤ) : 0 ≤ DeltaXY d n x y := by
  rw [DeltaXY, wedgeNorm]
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

lemma shortSum_le_S1ball (d n : ℕ) [DecidableEq (Mon d n)] (x y : Fin (n + 1) → ℤ)
    (Q : ℕ) (Y : ℝ) :
    (∑ᶠ a ∈ {a : Mon d n → ℤ | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ Y},
        1 / eNorm a ^ 1) ≤ S1ball d n x Y := by
  classical
  set A : Set (Mon d n → ℤ) := {a | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ Y} with hA
  set B : Set (Mon d n → ℤ) := {a | a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ Y} with hB
  have hCfin : ({a : Mon d n → ℤ | eNorm a ≤ Y} : Set (Mon d n → ℤ)).Finite :=
    MDBasic.finite_eNorm_le (ι := Mon d n) Y
  have hAsub : A ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := fun a ha => ha.2.2
  have hBsub : B ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := fun a ha => ha.2.2
  have hAB : A ⊆ B := fun a ha => ⟨(Submodule.mem_inf.mp ha.1).1, ha.2.1, ha.2.2⟩
  have hsuppA : Function.support (A.indicator (fun a => 1 / eNorm a ^ 1))
      ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := by
    intro a ha
    by_cases hle : eNorm a ≤ Y
    · exact hle
    · have hz : A.indicator (fun a => 1 / eNorm a ^ 1) a = 0 := by
        rw [Set.indicator_of_notMem (show a ∉ A from fun haA => hle (hAsub haA))]
      exact absurd hz ha
  have hsuppB : Function.support (B.indicator (fun a => 1 / eNorm a))
      ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := by
    intro a ha
    by_cases hle : eNorm a ≤ Y
    · exact hle
    · have hz : B.indicator (fun a => 1 / eNorm a) a = 0 := by
        rw [Set.indicator_of_notMem (show a ∉ B from fun haB => hle (hBsub haB))]
      exact absurd hz ha
  have h1 : (∑ᶠ a ∈ A, 1 / eNorm a ^ 1)
      = ∑ a ∈ hCfin.toFinset, A.indicator (fun a => 1 / eNorm a ^ 1) a := by
    rw [finsum_mem_def]
    exact finsum_eq_sum_of_support_subset_of_finite _ hsuppA hCfin
  have h2 : (∑ a ∈ hCfin.toFinset, B.indicator (fun a => 1 / eNorm a) a)
      = ∑ᶠ a ∈ B, 1 / eNorm a := by
    rw [finsum_mem_def]
    exact (finsum_eq_sum_of_support_subset_of_finite _ hsuppB hCfin).symm
  calc (∑ᶠ a ∈ A, 1 / eNorm a ^ 1)
      = ∑ a ∈ hCfin.toFinset, A.indicator (fun a => 1 / eNorm a ^ 1) a := h1
    _ ≤ ∑ a ∈ hCfin.toFinset, B.indicator (fun a => 1 / eNorm a) a := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases ha : a ∈ A
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hAB ha), pow_one]
        · rw [Set.indicator_of_notMem ha]
          by_cases hb : a ∈ B
          · rw [Set.indicator_of_mem hb]
            exact div_nonneg zero_le_one (eNorm_nonneg a)
          · rw [Set.indicator_of_notMem hb]
    _ = ∑ᶠ a ∈ B, 1 / eNorm a := h2
    _ = S1ball d n x Y := by rw [hB, S1ball]

/-- The cone-restricted short-vector term of the weighted Abel summation is also dominated by the
weighted small-ball sum of `Λ_{ν(x)}` (it is a sub-sum of the unrestricted one). -/
lemma shortSum_le_S1ball_cone (d n : ℕ) [DecidableEq (Mon d n)] (x y : Fin (n + 1) → ℤ)
    (Q : ℕ) (α Y : ℝ) :
    (∑ᶠ a ∈ {a : Mon d n → ℤ | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ Y ∧
        toR a ∈ Cgam (toR (veronese d n y)) α ∧ toR a ∈ Cgam (0 : Mon d n → ℝ) α},
        1 / eNorm a ^ 1) ≤ S1ball d n x Y := by
  classical
  set A : Set (Mon d n → ℤ) := {a | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ Y ∧
      toR a ∈ Cgam (toR (veronese d n y)) α ∧ toR a ∈ Cgam (0 : Mon d n → ℝ) α} with hA
  set B : Set (Mon d n → ℤ) := {a | a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ Y} with hB
  have hCfin : ({a : Mon d n → ℤ | eNorm a ≤ Y} : Set (Mon d n → ℤ)).Finite :=
    MDBasic.finite_eNorm_le (ι := Mon d n) Y
  have hAsub : A ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := fun a ha => ha.2.2.1
  have hBsub : B ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := fun a ha => ha.2.2
  have hAB : A ⊆ B := fun a ha => ⟨(Submodule.mem_inf.mp ha.1).1, ha.2.1, ha.2.2.1⟩
  have hsuppA : Function.support (A.indicator (fun a => 1 / eNorm a ^ 1))
      ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := by
    intro a ha
    by_cases hle : eNorm a ≤ Y
    · exact hle
    · have hz : A.indicator (fun a => 1 / eNorm a ^ 1) a = 0 := by
        rw [Set.indicator_of_notMem (show a ∉ A from fun haA => hle (hAsub haA))]
      exact absurd hz ha
  have hsuppB : Function.support (B.indicator (fun a => 1 / eNorm a))
      ⊆ {a : Mon d n → ℤ | eNorm a ≤ Y} := by
    intro a ha
    by_cases hle : eNorm a ≤ Y
    · exact hle
    · have hz : B.indicator (fun a => 1 / eNorm a) a = 0 := by
        rw [Set.indicator_of_notMem (show a ∉ B from fun haB => hle (hBsub haB))]
      exact absurd hz ha
  have h1 : (∑ᶠ a ∈ A, 1 / eNorm a ^ 1)
      = ∑ a ∈ hCfin.toFinset, A.indicator (fun a => 1 / eNorm a ^ 1) a := by
    rw [finsum_mem_def]
    exact finsum_eq_sum_of_support_subset_of_finite _ hsuppA hCfin
  have h2 : (∑ a ∈ hCfin.toFinset, B.indicator (fun a => 1 / eNorm a) a)
      = ∑ᶠ a ∈ B, 1 / eNorm a := by
    rw [finsum_mem_def]
    exact (finsum_eq_sum_of_support_subset_of_finite _ hsuppB hCfin).symm
  calc (∑ᶠ a ∈ A, 1 / eNorm a ^ 1)
      = ∑ a ∈ hCfin.toFinset, A.indicator (fun a => 1 / eNorm a ^ 1) a := h1
    _ ≤ ∑ a ∈ hCfin.toFinset, B.indicator (fun a => 1 / eNorm a) a := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases ha : a ∈ A
        · rw [Set.indicator_of_mem ha, Set.indicator_of_mem (hAB ha), pow_one]
        · rw [Set.indicator_of_notMem ha]
          by_cases hb : a ∈ B
          · rw [Set.indicator_of_mem hb]
            exact div_nonneg zero_le_one (eNorm_nonneg a)
          · rw [Set.indicator_of_notMem hb]
    _ = ∑ᶠ a ∈ B, 1 / eNorm a := h2
    _ = S1ball d n x Y := by rw [hB, S1ball]

/-- The main term of the per-`ℓ` mixed count, up to the relative error `min 1 (Δ²/α²)`. -/
theorem mainTerm_mix_ell (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hN : 3 ≤ NN d n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) (Q : ℕ) (hQ : 1 ≤ Q) {α T C₁ : ℝ} (hα : 0 < α)
    (hT : 0 ≤ T) (hC₁ : 0 < C₁)
    (hIc : |IcVol (toE (toR (veronese d n x)))
        (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) -
      ((NN d n : ℝ) - 2) / ((NN d n : ℝ) - 1) * ballVol (NN d n - 2) *
        DeltaXY d n x y / α|
      ≤ C₁ * (((NN d n : ℝ) - 2) / ((NN d n : ℝ) - 1) * ballVol (NN d n - 2) *
        DeltaXY d n x y / α) * min 1 (DeltaXY d n x y ^ 2 / α ^ 2)) :
    |((NN d n : ℝ) - 1) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) /
        detL (GamMix d n x y Q) * coneSliceVol (GamMix d n x y Q) (toR (veronese d n y)) 0 α -
      T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
        ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α * Q * eNorm (veronese d n x))|
      ≤ C₁ * (T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
        ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α * Q * eNorm (veronese d n x))) *
          min 1 (DeltaXY d n x y ^ 2 / α ^ 2) := by
  have hExne : eNorm (veronese d n x) ≠ 0 :=
    ne_of_gt (eNorm_pos_of_ne_zero (isPrim_ne_zero (isPrim_veronese d n (by omega) hx)))
  have hN1c : (1 : ℝ) < (NN d n : ℝ) := by exact_mod_cast (by omega : 1 < NN d n)
  have hN2c : (2 : ℝ) < (NN d n : ℝ) := by exact_mod_cast (by omega : 2 < NN d n)
  have hN1' : ((NN d n : ℝ) - 1) ≠ 0 := by intro hc; linarith [hN1c]
  have hN2' : ((NN d n : ℝ) - 2) ≠ 0 := by intro hc; linarith [hN2c]
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hg0 : ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.gcd_pos_of_pos_left _ (by omega : 0 < Q)))
  set F : ℝ := ((NN d n : ℝ) - 1) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) *
      (((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / ((Q : ℝ) * eNorm (veronese d n x))) with hF
  set c : ℝ := ((NN d n : ℝ) - 2) / ((NN d n : ℝ) - 1) * ballVol (NN d n - 2) *
      DeltaXY d n x y / α with hc
  have hF0 : 0 ≤ F := by
    rw [hF]
    exact mul_nonneg (mul_nonneg (div_nonneg (by linarith [hN1c]) (by linarith [hN2c]))
      (pow_nonneg hT _))
      (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (eNorm_nonneg _)))
  have hflat : T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
        ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α * Q * eNorm (veronese d n x)) = F * c := by
    rw [hF, hc]
    exact div_factor_alg _ _ _ _ _ _ _ _ _ hN1' hN2' hα.ne' hQ0 hExne
  have hmain : ((NN d n : ℝ) - 1) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) /
        detL (GamMix d n x y Q) * coneSliceVol (GamMix d n x y Q) (toR (veronese d n y)) 0 α
      = F * IcVol (toE (toR (veronese d n x)))
          (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) := by
    rw [hF, coneSliceVol_GamMix d n hd x y hx Q hQ α hα,
      detL_GamMix d n hd hn x y hx hy hxy Q hQ]
    exact div_detL_alg _ _ _ _ _ _ _ hN1' hN2' hg0 hQ0 hExne
  have hstep : |((NN d n : ℝ) - 1) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) /
        detL (GamMix d n x y Q) * coneSliceVol (GamMix d n x y Q) (toR (veronese d n y)) 0 α -
      T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
        ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α * Q * eNorm (veronese d n x))|
      = F * |IcVol (toE (toR (veronese d n x)))
            (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) -
          ((NN d n : ℝ) - 2) / ((NN d n : ℝ) - 1) * ballVol (NN d n - 2) *
            DeltaXY d n x y / α| := by
    rw [hmain, hflat, ← mul_sub, abs_mul, abs_of_nonneg hF0]
  have hle : F * |IcVol (toE (toR (veronese d n x)))
            (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) -
          ((NN d n : ℝ) - 2) / ((NN d n : ℝ) - 1) * ballVol (NN d n - 2) *
            DeltaXY d n x y / α|
      ≤ F * (C₁ * (((NN d n : ℝ) - 2) / ((NN d n : ℝ) - 1) * ballVol (NN d n - 2) *
            DeltaXY d n x y / α) * min 1 (DeltaXY d n x y ^ 2 / α ^ 2)) :=
    mul_le_mul_of_nonneg_left hIc hF0
  have heq : F * (C₁ * c * min 1 (DeltaXY d n x y ^ 2 / α ^ 2))
      = C₁ * (T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
          ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α * Q * eNorm (veronese d n x))) *
            min 1 (DeltaXY d n x y ^ 2 / α ^ 2) := by
    have h1 : F * (C₁ * c * min 1 (DeltaXY d n x y ^ 2 / α ^ 2))
        = C₁ * (F * c) * min 1 (DeltaXY d n x y ^ 2 / α ^ 2) := by ring
    have h2 : C₁ * (F * c) * min 1 (DeltaXY d n x y ^ 2 / α ^ 2)
        = C₁ * (T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
            ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α * Q * eNorm (veronese d n x))) *
              min 1 (DeltaXY d n x y ^ 2 / α ^ 2) := by
      rw [← hflat]
    exact h1.trans h2
  linarith [hstep.le, hstep.ge, hle, heq.le, heq.ge]

/-- (L1a) Per-`ℓ` mixed count: `ballConeWeightedKw` (`k = 1`, `v = ν(y)`, `w = 0`,
`Y = Qλ(x)`) + `detL_GamMix` + `coneSliceVol_GamMix` + `IcVol_point_unif` + `lam_GamMix_le`.
The `(N-1)/(N-2)` of the Abel summation cancels the `(N-2)/(N-1)` of the volume. -/
theorem Sk1_mix_ell (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x y : Fin (n + 1) → ℤ), IsPrim x → IsPrim y →
      LinearIndependent ℤ ![x, y] → ∀ (Q : ℕ) (α T : ℝ), 1 ≤ Q → 0 < α →
      (Q : ℝ) * lamX d n x ≤ T →
      |Sk d n 1 (GamMix d n x y Q) (TmixSet d n y T α) -
          T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
            ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) /
            (α * Q * eNorm (veronese d n x))|
        ≤ C * (T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
            ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) /
            (α * Q * eNorm (veronese d n x))) * min 1 (DeltaXY d n x y ^ 2 / α ^ 2)
          + C * T ^ (NN d n - 3) * lamX d n x *
              ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / eNorm (veronese d n x)
          + C * S1ball d n x ((Q : ℝ) * lamX d n x) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := ballConeWeightedKw_alt (ι := Mon d n) 1
  obtain ⟨C₁, hC₁pos, hC₁⟩ := IcVol_point_unif d n hd (by omega)
  refine ⟨C₀ + C₁ + 1, by linarith, ?_⟩
  intro x y hx hy hxy Q α T hQ hα hQT
  have hn : 1 ≤ n := le_trans (by omega : 1 ≤ d) hdn
  have hN4 : 4 ≤ NN d n := NN_ge_four d n hd hdn
  have hN3 : 3 ≤ NN d n := by omega
  obtain ⟨hrk, hlam_le⟩ := lam_GamMix_le d n hd hn x y hx Q hQ
  set Mt : ℝ := T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
      ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α * Q * eNorm (veronese d n x)) with hMt
  set M2 : ℝ := T ^ (NN d n - 3) * lamX d n x *
      ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / eNorm (veronese d n x) with hM2
  set M3 : ℝ := S1ball d n x ((Q : ℝ) * lamX d n x) with hM3
  obtain ⟨Mabs, hMabs⟩ : ∃ M : ℝ, M = ((NN d n : ℝ) - 1) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) /
      detL (GamMix d n x y Q) * coneSliceVol (GamMix d n x y Q) (toR (veronese d n y)) 0 α := ⟨_, rfl⟩
  have hνx : veronese d n x ≠ 0 := isPrim_ne_zero (isPrim_veronese d n (by omega) hx)
  have hExpos : 0 < eNorm (veronese d n x) := eNorm_pos_of_ne_zero hνx
  have hExne : eNorm (veronese d n x) ≠ 0 := ne_of_gt hExpos
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hg0 : ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.gcd_pos_of_pos_left _ (by omega : 0 < Q)))
  have hrkOrth : rk (latOrth (veronese d n x)) = NN d n - 1 := Vero.finrank_latOrth _ hνx
  have hlam1 : 1 ≤ lamX d n x := by
    rw [lamX]
    exact MDEstimates.one_le_lam _ (by omega) (by rw [hrkOrth])
  have hlampos : 0 < lamX d n x := lt_of_lt_of_le zero_lt_one hlam1
  have hY1 : (1 : ℝ) ≤ (Q : ℝ) * lamX d n x := by
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (Q : ℝ) * lamX d n x := mul_le_mul h1 hlam1 (by norm_num) (by norm_num)
  have hT0 : 0 ≤ T := le_trans (le_trans zero_le_one hY1) hQT
  have hΔ0 : 0 ≤ DeltaXY d n x y := deltaXY_nonneg d n x y
  have hcount := hC₀ (GamMix d n x y Q) (toR (veronese d n y)) (0 : Mon d n → ℝ) α T
      ((Q : ℝ) * lamX d n x) le_rfl (by rw [hrk]; omega) hα hY1
      (by rw [hrk]; exact hlam_le) hQT
  have hset : {a : Mon d n → ℤ | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ a ∈ TmixSet d n y T α}
      = {a : Mon d n → ℤ | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ T ∧
          toR a ∈ Cgam (toR (veronese d n y)) α ∧ toR a ∈ Cgam (0 : Mon d n → ℝ) α} := by
    ext a
    simp only [Set.mem_setOf_eq, TmixSet, cgam_zero, Set.mem_univ, and_true, and_assoc]
  have hSk_eq : Sk d n 1 (GamMix d n x y Q) (TmixSet d n y T α)
      = ∑ᶠ a ∈ {a : Mon d n → ℤ | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧ eNorm a ≤ T ∧
          toR a ∈ Cgam (toR (veronese d n y)) α ∧ toR a ∈ Cgam (0 : Mon d n → ℝ) α},
          1 / eNorm a ^ 1 := by
    simp only [Sk]
    rw [hset]
  have hnorm_main : ((rk (GamMix d n x y Q) : ℝ) /
        ((rk (GamMix d n x y Q) : ℝ) - (1 : ℝ))) * T ^ (rk (GamMix d n x y Q) - 1) /
        detL (GamMix d n x y Q) * coneSliceVol (GamMix d n x y Q) (toR (veronese d n y)) 0 α
      = Mabs := by
    rw [hMabs]
    have hc1 : ((NN d n - 1 : ℕ) : ℝ) = (NN d n : ℝ) - 1 := by
      have h1 : 1 ≤ NN d n := by omega
      rw [Nat.cast_sub h1, Nat.cast_one]
    have hexp : NN d n - 1 - 1 = NN d n - 2 := by omega
    simp only [hrk, hc1, hexp, Nat.cast_one]
    ring_nf
  have hnorm_err : C₀ * T ^ (rk (GamMix d n x y Q) - 1 - 1) * ((Q : ℝ) * lamX d n x) /
        detL (GamMix d n x y Q)
      = C₀ * T ^ (NN d n - 3) * ((Q : ℝ) * lamX d n x) / detL (GamMix d n x y Q) := by
    have hexp : NN d n - 1 - 1 - 1 = NN d n - 3 := by omega
    simp only [hrk, hexp]
  have hb1 : |Sk d n 1 (GamMix d n x y Q) (TmixSet d n y T α) - Mabs|
      ≤ C₀ * T ^ (NN d n - 3) * ((Q : ℝ) * lamX d n x) / detL (GamMix d n x y Q)
        + ∑ᶠ a ∈ {a : Mon d n → ℤ | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧
            eNorm a ≤ (Q : ℝ) * lamX d n x ∧ toR a ∈ Cgam (toR (veronese d n y)) α ∧
            toR a ∈ Cgam (0 : Mon d n → ℝ) α}, 1 / eNorm a ^ 1 := by
    have h1 := hcount
    simp only [Nat.cast_one] at h1
    rw [hnorm_main, hnorm_err] at h1
    rwa [hSk_eq]
  have hb1' : |Sk d n 1 (GamMix d n x y Q) (TmixSet d n y T α) - Mabs| ≤ C₀ * M2 + M3 := by
    have herr : C₀ * T ^ (NN d n - 3) * ((Q : ℝ) * lamX d n x) / detL (GamMix d n x y Q)
        = C₀ * M2 := by
      rw [hM2, detL_GamMix d n hd hn x y hx hy hxy Q hQ]
      exact err_alg _ _ _ _ _ _ hQ0 hg0 hExne
    have hshort : (∑ᶠ a ∈ {a : Mon d n → ℤ | a ∈ GamMix d n x y Q ∧ a ≠ 0 ∧
        eNorm a ≤ (Q : ℝ) * lamX d n x ∧ toR a ∈ Cgam (toR (veronese d n y)) α ∧
        toR a ∈ Cgam (0 : Mon d n → ℝ) α}, 1 / eNorm a ^ 1) ≤ M3 := by
      rw [hM3]
      exact shortSum_le_S1ball_cone d n x y Q α ((Q : ℝ) * lamX d n x)
    rw [herr] at hb1
    linarith [hb1, hshort]
  have hmain2 : |Mabs - Mt| ≤ C₁ * (Mt * min 1 (DeltaXY d n x y ^ 2 / α ^ 2)) := by
    have h := mainTerm_mix_ell d n hd hn hN3 x y hx hy hxy Q hQ hα hT0 hC₁pos
      (hC₁ x y hx hy hxy α hα)
    rw [← hMabs, ← hMt] at h
    calc |Mabs - Mt| ≤ C₁ * Mt * min 1 (DeltaXY d n x y ^ 2 / α ^ 2) := h
      _ = C₁ * (Mt * min 1 (DeltaXY d n x y ^ 2 / α ^ 2)) := by ring
  have hE1 : 0 ≤ Mt * min 1 (DeltaXY d n x y ^ 2 / α ^ 2) := by
    rw [hMt]
    have hQQ : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    refine mul_nonneg ?_ (le_min zero_le_one (div_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hT0 _)
      (by rw [ballVol]; exact ENNReal.toReal_nonneg)) hΔ0) (Nat.cast_nonneg _))
      (mul_pos (mul_pos hα hQQ) hExpos).le
  have hE2 : 0 ≤ M2 := by
    rw [hM2]
    exact div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hT0 _) hlampos.le)
      (Nat.cast_nonneg _)) hExpos.le
  have hE3 : 0 ≤ M3 := by
    rw [hM3]
    exact S1ball_nonneg d n x _
  have htri := abs_sub_le (Sk d n 1 (GamMix d n x y Q) (TmixSet d n y T α)) Mabs Mt
  have hfinal : (C₀ * M2 + M3) + C₁ * (Mt * min 1 (DeltaXY d n x y ^ 2 / α ^ 2))
      ≤ (C₀ + C₁ + 1) * Mt * min 1 (DeltaXY d n x y ^ 2 / α ^ 2) + (C₀ + C₁ + 1) * M2
        + (C₀ + C₁ + 1) * M3 := by
    have hA : 0 ≤ (C₀ + 1) * (Mt * min 1 (DeltaXY d n x y ^ 2 / α ^ 2)) :=
      mul_nonneg (by linarith) hE1
    have hB : 0 ≤ (C₁ + 1) * M2 := mul_nonneg (by linarith) hE2
    have hC : 0 ≤ (C₀ + C₁) * M3 := mul_nonneg (by linarith) hE3
    nlinarith [hA, hB, hC]
  have hM2r : (C₀ + C₁ + 1) * T ^ (NN d n - 3) * lamX d n x *
        ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / eNorm (veronese d n x)
      = (C₀ + C₁ + 1) * M2 := by
    rw [hM2]
    ring
  rw [hM2r]
  linarith [htri, hb1', hmain2, hfinal]

end Work.HP.MM2
