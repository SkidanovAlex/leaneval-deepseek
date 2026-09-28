import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.BallConeK.Defs
import Submission.Work.HP.BallConeK.layerCake
import Submission.Work.HP.BallConeK.mainTermIdent
import Submission.Work.HP.BallConeK.coneCountSub
import Submission.Work.HP.BallConeK.largeFilterCard
import Submission.Work.HP.BallConeK.integralDivPow
import Submission.Work.HP.BallConeK.weightedErrorIntegral
import Submission.Work.HP.BallVolIntrinsic
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.BCS.ballConeCountEst
import Submission.Work.HP.MM2.ConeSliceVolBound

/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `ballConeWeightedKw` in namespace Work.HP.MM2; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.MM2.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.MM2.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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

/-! ## Auxiliary integral identities -/

/-- `∫_A^B (k/t^{k+1})(t^r - A^r) dt` in closed form. -/
lemma integral_pow_sub (k r : ℕ) {A B : ℝ} (hkr : k + 1 < r) (hA : 0 < A) (hAB : A ≤ B) :
    ∫ t in A..B, ((k : ℝ) / t ^ (k + 1)) * (t ^ r - A ^ r)
      = (k : ℝ) * (B ^ (r - k) - A ^ (r - k)) / ((r - k : ℕ) : ℝ)
        - A ^ r * (1 / A ^ k - 1 / B ^ k) := by
  have hpt : ∀ t ∈ Set.uIcc A B, ((k : ℝ) / t ^ (k + 1)) * (t ^ r - A ^ r)
      = (k : ℝ) * t ^ (r - k - 1) - A ^ r * ((k : ℝ) / t ^ (k + 1)) := by
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hA ht.1)
    have h1 : t ^ r = t ^ (k + 1) * t ^ (r - k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1, mul_sub]
    have h2 : (k : ℝ) / t ^ (k + 1) * (t ^ (k + 1) * t ^ (r - k - 1))
        = (k : ℝ) * t ^ (r - k - 1) := by
      field_simp
    rw [h2]
    ring
  have hcont1 : ContinuousOn (fun t : ℝ => (k : ℝ) * t ^ (r - k - 1)) (Set.Icc A B) :=
    (continuous_const.mul (continuous_pow _)).continuousOn
  have hcont2 : ContinuousOn (fun t : ℝ => A ^ r * ((k : ℝ) / t ^ (k + 1))) (Set.Icc A B) :=
    continuousOn_const.mul (ContinuousOn.div continuousOn_const (continuousOn_pow _)
      (fun t ht => pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hA ht.1))))
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub (hcont1.intervalIntegrable_of_Icc hAB)
      (hcont2.intervalIntegrable_of_Icc hAB),
    intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const_mul, BallConeK.integralDivPow k hA hAB]
  have hsucc : (r - k - 1) + 1 = r - k := by omega
  have hden : ((r - k - 1 : ℕ) : ℝ) + 1 = ((r - k : ℕ) : ℝ) := by
    have h2 : ((r - k - 1 : ℕ) + 1 : ℕ) = (r - k : ℕ) := hsucc
    calc ((r - k - 1 : ℕ) : ℝ) + 1 = ((r - k - 1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by norm_num
      _ = (((r - k - 1 : ℕ) + 1 : ℕ) : ℝ) := by rw [Nat.cast_add]
      _ = ((r - k : ℕ) : ℝ) := by rw [h2]
  rw [hsucc, hden]
  ring

/-- `|a + b + c - d| ≤ |a| + |b| + |c| + |d|`. -/
lemma abs_add_add_sub_le (a b c d : ℝ) : |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c - d| ≤ |a + b + c| + |d| := by simpa using abs_sub_le (a + b + c) 0 d
    _ ≤ (|a + b| + |c|) + |d| := by linarith [abs_add_le (a + b) c]
    _ ≤ ((|a| + |b|) + |c|) + |d| := by linarith [abs_add_le a b]
    _ = |a| + |b| + |c| + |d| := by ring


/-! ## The main assembly -/

/-- The Abel-summation step, conditional on the lattice-point count `hcount` and the bound
`hvol` on the cone-slice volume. -/
lemma main_aux {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (Cc : ℝ) (hCc : 0 < Cc)
    (hcount : ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ t Y : ℝ),
      0 < γ → 1 ≤ rk L → 1 ≤ t → lam L (rk L) ≤ Y → Y ≤ t →
      |coneCount L v w γ t - t ^ (rk L) / detL L * coneSliceVol L v w γ|
        ≤ Cc * t ^ (rk L) / detL L * (Y / t))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hvol : ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ : ℝ),
      0 ≤ coneSliceVol L v w γ ∧ coneSliceVol L v w γ ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ T Y : ℝ),
      1 ≤ k → k + 1 < rk L → 0 < γ → 1 ≤ Y → lam L (rk L) ≤ Y → Y ≤ T →
      |(∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k) -
        ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L *
          coneSliceVol L v w γ|
        ≤ C * T ^ (rk L - k - 1) * Y / detL L
          + ∑ᶠ a ∈ ballSet L Y, 1 / eNorm a ^ k := by
  classical
  refine ⟨K * (Fintype.card ι : ℝ) + Cc * ((k : ℝ) + 3) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ K * (Fintype.card ι : ℝ) := mul_nonneg hK0 (Nat.cast_nonneg _)
    have h2 : 0 < Cc * ((k : ℝ) + 3) := mul_pos hCc (by positivity)
    linarith
  intro L v w γ T Y hk hkr hγ hY1 hlam hYT
  obtain ⟨hV0, hVK⟩ := hvol L v w γ
  have hrk1 : 1 ≤ rk L := by omega
  have hT1 : 1 ≤ T := le_trans hY1 hYT
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
  have hdet1 : 1 ≤ detL L := Work.HP.Lat.detL_ge_one L
  have hdetpos : 0 < detL L := lt_of_lt_of_le zero_lt_one hdet1
  have hrkcard : (rk L : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast rk_le_card L
  set Ys : ℝ := max 1 (lam L (rk L)) with hYsdef
  have hYs1 : 1 ≤ Ys := le_max_left _ _
  have hYspos : 0 < Ys := lt_of_lt_of_le one_pos hYs1
  have hlamYs : lam L (rk L) ≤ Ys := le_max_right _ _
  have hYsY : Ys ≤ Y := max_le hY1 hlam
  have hYsT : Ys ≤ T := le_trans hYsY hYT
  set q : ℝ := coneSliceVol L v w γ / detL L with hq
  set G : ℝ → ℝ := fun t => (k : ℝ) / t ^ (k + 1) with hG
  set ee : ℝ → ℝ := fun t => coneCount L v w γ t - q * t ^ (rk L) with hee
  set Dv : ℝ := T ^ (rk L - k - 1) * Y / detL L with hDv
  have hDvnn : 0 ≤ Dv := by rw [hDv]; positivity
  have hqnn : 0 ≤ q := by
    rw [hq]; exact div_nonneg hV0 (le_of_lt hdetpos)
  have hGcont : ContinuousOn G (Set.Icc Ys T) := by
    rw [hG]
    refine ContinuousOn.div continuousOn_const (continuousOn_pow _) ?_
    intro t ht
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hYspos ht.1))
  -- (1) the uniform count estimate at the short scale `Ys`
  have hcnt : ∀ t : ℝ, 1 ≤ t → Ys ≤ t → |ee t| ≤ Cc * t ^ (rk L - 1) * Ys / detL L := by
    intro t ht1 hYst
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos ht1)
    have h := hcount L v w γ t Ys hγ hrk1 ht1 hlamYs hYst
    have heq : coneCount L v w γ t - t ^ (rk L) / detL L * coneSliceVol L v w γ = ee t := by
      rw [hee, hq]; ring
    have hconv : Cc * t ^ (rk L) / detL L * (Ys / t) = Cc * t ^ (rk L - 1) * Ys / detL L := by
      have ht' : t ^ (rk L) = t ^ (rk L - 1) * t := by
        rw [← pow_succ, Nat.sub_add_cancel hrk1]
      field_simp
      rw [ht']
      ring
    rw [heq, hconv] at h
    exact h
  -- (2) splitting the sum at `Ys`
  have hfinS : (smallSet L v w γ Ys).Finite := finite_smallSet L v w γ Ys
  have hfinL : (largeSet L v w γ Ys T).Finite := finite_largeSet L v w γ Ys T
  have hsplitS : (∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k)
      = (∑ᶠ a ∈ smallSet L v w γ Ys, 1 / eNorm a ^ k)
        + (∑ᶠ a ∈ largeSet L v w γ Ys T, 1 / eNorm a ^ k) := by
    rw [fullSet_eq_union L v w γ Ys T hYsT,
      finsum_mem_union (disjoint_small_large L v w γ Ys T) hfinS hfinL]
  -- (3) the small part is bounded by the weighted ball sum of radius `Y`
  have hsmall : (∑ᶠ a ∈ smallSet L v w γ Ys, 1 / eNorm a ^ k)
      ≤ ∑ᶠ a ∈ ballSet L Y, 1 / eNorm a ^ k := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinS,
      finsum_mem_eq_finite_toFinset_sum _ (finite_ballSet L Y)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro a ha
      rw [Set.Finite.mem_toFinset] at ha ⊢
      exact ⟨ha.1, ha.2.1, le_trans ha.2.2.1 hYsY⟩
    · intro a _ _
      exact div_nonneg zero_le_one (pow_nonneg (eNorm_nonneg a) k)
  -- (4) layer cake for the large part
  have hYsle : ∀ a ∈ hfinL.toFinset, Ys ≤ eNorm a := by
    intro a ha
    exact le_of_lt (((Set.Finite.mem_toFinset hfinL).mp ha :
      a ∈ largeSet L v w γ Ys T).2.2.1)
  have hTle : ∀ a ∈ hfinL.toFinset, eNorm a ≤ T := by
    intro a ha
    exact ((Set.Finite.mem_toFinset hfinL).mp ha : a ∈ largeSet L v w γ Ys T).2.2.2.1
  have hpoint : ∀ a ∈ hfinL.toFinset, (1:ℝ) / eNorm a ^ k
      = 1 / T ^ k + ∫ t in (eNorm a)..T, G t := by
    intro a ha
    have ha' : a ∈ largeSet L v w γ Ys T := (Set.Finite.mem_toFinset hfinL).mp ha
    have hpos : 0 < eNorm a := lt_of_lt_of_le hYspos (le_of_lt ha'.2.2.1)
    have hle : eNorm a ≤ T := ha'.2.2.2.1
    have h := BallConeK.integralDivPow k hpos hle
    rw [hG]
    linarith [h]
  have hlc : ∑ a ∈ hfinL.toFinset, ∫ t in (eNorm a)..T, G t
      = ∫ t in Ys..T, G t * ((hfinL.toFinset.filter (fun a => eNorm a ≤ t)).card : ℝ) :=
    BallConeK.layerCake hfinL.toFinset (fun a => eNorm a) Ys T G hYsT hYsle hTle hGcont
  have hcardN : ((hfinL.toFinset.card : ℕ) : ℝ) = coneCount L v w γ T - coneCount L v w γ Ys := by
    have h := BallConeK.coneCountSub L v w γ T Ys hYsT (le_of_lt hYspos)
    have h' : coneCount L v w γ T - coneCount L v w γ Ys
        = (((largeSet L v w γ Ys T).ncard : ℕ) : ℝ) := h
    rw [Set.ncard_eq_toFinset_card _ hfinL] at h'
    exact h'.symm
  have hIntC : ∫ t in Ys..T, G t * (((hfinL.toFinset.filter (fun a => eNorm a ≤ t)).card : ℕ) : ℝ)
      = ∫ t in Ys..T, G t * (coneCount L v w γ t - coneCount L v w γ Ys) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hYsT] at ht
    rw [BallConeK.largeFilterCard L v w γ Ys T hfinL ht (le_of_lt hYspos)]
  have hlarge_eq : (∑ᶠ a ∈ largeSet L v w γ Ys T, 1 / eNorm a ^ k)
      = (coneCount L v w γ T - coneCount L v w γ Ys) / T ^ k
        + ∫ t in Ys..T, G t * (coneCount L v w γ t - coneCount L v w γ Ys) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinL]
    calc ∑ a ∈ hfinL.toFinset, (1:ℝ) / eNorm a ^ k
        = ∑ a ∈ hfinL.toFinset, (1 / T ^ k + ∫ t in (eNorm a)..T, G t) :=
            Finset.sum_congr rfl hpoint
      _ = (∑ a ∈ hfinL.toFinset, 1 / T ^ k)
            + ∑ a ∈ hfinL.toFinset, ∫ t in (eNorm a)..T, G t := Finset.sum_add_distrib
      _ = ((hfinL.toFinset.card : ℕ) : ℝ) * (1 / T ^ k)
            + ∫ t in Ys..T, G t * (coneCount L v w γ t - coneCount L v w γ Ys) := by
            rw [Finset.sum_const, nsmul_eq_mul, hlc, hIntC]
      _ = (coneCount L v w γ T - coneCount L v w γ Ys) / T ^ k
            + ∫ t in Ys..T, G t * (coneCount L v w γ t - coneCount L v w γ Ys) := by
            rw [hcardN]; ring
  -- (5) splitting the integral along the smooth part and the error
  have hGcont' : ContinuousOn G (Set.uIcc Ys T) := by rwa [Set.uIcc_of_le hYsT]
  have hsub1 : ContinuousOn (fun t : ℝ => t ^ (rk L) - Ys ^ (rk L)) (Set.Icc Ys T) :=
    ((continuous_pow (rk L)).sub continuous_const).continuousOn
  have hi1 : IntervalIntegrable (fun t => q * (G t * (t ^ (rk L) - Ys ^ (rk L)))) volume Ys T :=
    ((hGcont.mul hsub1).intervalIntegrable_of_Icc hYsT).const_mul q
  have hJ : IntervalIntegrable (fun t => G t * (coneCount L v w γ t - coneCount L v w γ Ys))
      volume Ys T := by
    have hmono : Monotone (fun t => coneCount L v w γ t - coneCount L v w γ Ys) :=
      fun s t hst => sub_le_sub_right (coneCount_mono L v w γ hst) _
    have h := (hmono.intervalIntegrable (μ := volume) (a := Ys) (b := T)).mul_continuousOn hGcont'
    refine (intervalIntegrable_congr ?_).mp h
    intro t ht
    exact mul_comm _ _
  have hKint : IntervalIntegrable (fun t => G t * (q * (t ^ (rk L) - Ys ^ (rk L)))) volume Ys T :=
    (hGcont.mul (continuousOn_const.mul hsub1)).intervalIntegrable_of_Icc hYsT
  have hi2 : IntervalIntegrable (fun t => G t * (ee t - ee Ys)) volume Ys T := by
    have hJK := hJ.sub hKint
    refine (intervalIntegrable_congr ?_).mp hJK
    intro t ht
    rw [hee]; ring
  have hpt2 : ∀ t ∈ Set.uIcc Ys T, G t * (coneCount L v w γ t - coneCount L v w γ Ys)
      = q * (G t * (t ^ (rk L) - Ys ^ (rk L))) + G t * (ee t - ee Ys) := by
    intro t ht
    rw [hee]; ring
  have hint_eq : ∫ t in Ys..T, G t * (coneCount L v w γ t - coneCount L v w γ Ys)
      = q * (∫ t in Ys..T, G t * (t ^ (rk L) - Ys ^ (rk L)))
        + ∫ t in Ys..T, G t * (ee t - ee Ys) := by
    rw [intervalIntegral.integral_congr hpt2, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul]
  -- (6) the error integral
  have hcntIcc : ∀ t ∈ Set.Icc Ys T, |ee t| ≤ Cc * t ^ (rk L - 1) * Ys / detL L :=
    fun t ht => hcnt t (le_trans hYs1 ht.1) ht.1
  have herr : |∫ t in Ys..T, G t * (ee t - ee Ys)| ≤ (Cc * ((k : ℝ) + 1)) * Dv := by
    have h := BallConeK.weightedErrorIntegral k (rk L) hk hkr hYspos hYsT hdetpos
      (le_of_lt hCc) ee hcntIcc hi2
    have h2 : (Cc * ((k : ℝ) + 1)) * (T ^ (rk L - k - 1) * Ys / detL L)
        ≤ (Cc * ((k : ℝ) + 1)) * Dv := by
      rw [hDv]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply div_le_div_of_nonneg_right ?_ (le_of_lt hdetpos)
      exact mul_le_mul_of_nonneg_left hYsY (by positivity)
    have h3 : |∫ t in Ys..T, G t * (ee t - ee Ys)|
        ≤ (Cc * ((k : ℝ) + 1)) * (T ^ (rk L - k - 1) * Ys / detL L) := by
      simpa only [hG] using h
    linarith
  -- (7) the model integral and the main term
  have hmodel : ∫ t in Ys..T, G t * (t ^ (rk L) - Ys ^ (rk L))
      = (k:ℝ) * (T ^ (rk L - k) - Ys ^ (rk L - k)) / ((rk L - k : ℕ) : ℝ)
        - Ys ^ (rk L) * (1 / Ys ^ k - 1 / T ^ k) := by
    have h := integral_pow_sub (k := k) (r := rk L) hkr hYspos hYsT
    simpa only [hG] using h
  have hmainP : ((T ^ (rk L) - Ys ^ (rk L)) / T ^ k)
      + (k:ℝ) * (T ^ (rk L - k) - Ys ^ (rk L - k)) / ((rk L - k : ℕ) : ℝ)
      - Ys ^ (rk L) * (1 / Ys ^ k - 1 / T ^ k)
      = ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (T ^ (rk L - k) - Ys ^ (rk L - k)) :=
    BallConeK.mainTermIdent (rk L) k hk hkr hYspos hTpos
  have hN : coneCount L v w γ T - coneCount L v w γ Ys
      = q * (T ^ (rk L) - Ys ^ (rk L)) + (ee T - ee Ys) := by
    rw [hee]; ring
  have hkey : (coneCount L v w γ T - coneCount L v w γ Ys) / T ^ k
        + (q * ((k:ℝ) * (T ^ (rk L - k) - Ys ^ (rk L - k)) / ((rk L - k : ℕ) : ℝ)
            - Ys ^ (rk L) * (1 / Ys ^ k - 1 / T ^ k))
          + ∫ t in Ys..T, G t * (ee t - ee Ys))
      = q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (T ^ (rk L - k) - Ys ^ (rk L - k)))
        + (ee T - ee Ys) / T ^ k
        + ∫ t in Ys..T, G t * (ee t - ee Ys) := by
    rw [hN]
    linear_combination q * hmainP
  have hSlarge : (∑ᶠ a ∈ largeSet L v w γ Ys T, 1 / eNorm a ^ k)
      = q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (T ^ (rk L - k) - Ys ^ (rk L - k)))
        + (ee T - ee Ys) / T ^ k
        + ∫ t in Ys..T, G t * (ee t - ee Ys) := by
    rw [hlarge_eq, hint_eq, hmodel, hkey]
  -- (8) the remaining bounds
  have hquot : |(ee T - ee Ys) / T ^ k| ≤ 2 * Cc * Dv := by
    have hTk1 : (1:ℝ) ≤ T ^ k := one_le_pow₀ hT1
    have hTkpos : (0:ℝ) < T ^ k := lt_of_lt_of_le zero_lt_one hTk1
    have h1 : |ee T - ee Ys| ≤ Cc * T ^ (rk L - 1) * Ys / detL L
        + Cc * Ys ^ (rk L - 1) * Ys / detL L := by
      have h2 := hcnt T hT1 hYsT
      have h3 := hcnt Ys hYs1 le_rfl
      have h4 : |ee T - ee Ys| ≤ |ee T| + |ee Ys| := by simpa using abs_sub_le (ee T) 0 (ee Ys)
      linarith
    rw [abs_div, abs_of_pos hTkpos]
    have hdiv : |ee T - ee Ys| / T ^ k
        ≤ (Cc * T ^ (rk L - 1) * Ys / detL L + Cc * Ys ^ (rk L - 1) * Ys / detL L) / T ^ k :=
      div_le_div_of_nonneg_right h1 (le_of_lt hTkpos)
    refine hdiv.trans ?_
    have hYp : Ys ^ (rk L - 1) * Ys = Ys ^ (rk L) := by
      rw [← pow_succ, Nat.sub_add_cancel hrk1]
    have hsplit2 : (Cc * T ^ (rk L - 1) * Ys / detL L + Cc * Ys ^ (rk L - 1) * Ys / detL L) / T ^ k
        = Cc * T ^ (rk L - 1) * Ys / (detL L * T ^ k)
          + Cc * Ys ^ (rk L) / (detL L * T ^ k) := by
      rw [← hYp]; ring
    rw [hsplit2]
    have hTp : T ^ (rk L - 1) / T ^ k = T ^ (rk L - k - 1) := by
      rw [div_eq_mul_inv]
      have h7 : rk L - k - 1 = rk L - 1 - k := by omega
      rw [h7]
      simpa using (pow_sub₀ T (ne_of_gt hTpos) (show k ≤ rk L - 1 by omega)).symm
    have hterm1 : Cc * T ^ (rk L - 1) * Ys / (detL L * T ^ k)
        = Cc * (T ^ (rk L - 1) / T ^ k) * Ys / detL L := by ring
    have hYZ : Ys ^ (rk L) ≤ T ^ (rk L - 1) * Y := by
      calc Ys ^ (rk L) ≤ Y ^ (rk L) := pow_le_pow_left₀ (le_of_lt hYspos) hYsY _
        _ = Y ^ (rk L - 1) * Y := by rw [← pow_succ, Nat.sub_add_cancel hrk1]
        _ ≤ T ^ (rk L - 1) * Y :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (le_of_lt hYpos) hYT (rk L - 1)) (le_of_lt hYpos)
    have h6 : Cc * Ys ^ (rk L) / (detL L * T ^ k) ≤ Cc * Dv := by
      have h7 : Ys ^ (rk L) / T ^ k ≤ T ^ (rk L - k - 1) * Y := by
        rw [div_le_iff₀ (pow_pos hTpos k)]
        have h8 : (T ^ (rk L - k - 1) * Y) * T ^ k = T ^ (rk L - 1) * Y := by
          have hp : rk L - k - 1 + k = rk L - 1 := by omega
          rw [mul_assoc, mul_comm Y (T ^ k), ← mul_assoc, ← pow_add, hp]
        rw [h8]
        exact hYZ
      have h9 : Cc * (Ys ^ (rk L) / T ^ k) / detL L ≤ Cc * (T ^ (rk L - k - 1) * Y) / detL L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h7 (le_of_lt hCc)) (le_of_lt hdetpos)
      have e1 : Cc * Ys ^ (rk L) / (detL L * T ^ k) = Cc * (Ys ^ (rk L) / T ^ k) / detL L := by ring
      have e2 : Cc * (T ^ (rk L - k - 1) * Y) / detL L = Cc * Dv := by
        rw [hDv, mul_div_assoc']
      rw [e1]
      exact h9.trans (le_of_eq e2)
    have hA : Cc * T ^ (rk L - 1) * Ys / (detL L * T ^ k) ≤ Cc * Dv := by
      have hleft : Cc * T ^ (rk L - 1) * Ys / (detL L * T ^ k)
          = Cc * T ^ (rk L - k - 1) * Ys / detL L := by
        rw [hterm1, hTp]
      have hbound : Cc * T ^ (rk L - k - 1) * Ys / detL L
          ≤ Cc * T ^ (rk L - k - 1) * Y / detL L :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hYsY (by positivity)) (le_of_lt hdetpos)
      have hright : Cc * T ^ (rk L - k - 1) * Y / detL L = Cc * Dv := by
        rw [hDv, mul_div_assoc']
        ring
      rw [hleft, ← hright]
      exact hbound
    have hsum : Cc * T ^ (rk L - 1) * Ys / (detL L * T ^ k) + Cc * Ys ^ (rk L) / (detL L * T ^ k)
        ≤ Cc * Dv + Cc * Dv := add_le_add hA h6
    linarith
  have hYsq : q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Ys ^ (rk L - k))
      ≤ (K * (Fintype.card ι : ℝ)) * Dv := by
    have hkrR : (0:ℝ) < (rk L : ℝ) - (k : ℝ) := by
      have : (k : ℝ) < (rk L : ℝ) := by exact_mod_cast (by omega : k < rk L)
      linarith
    have hRnn : 0 ≤ (rk L : ℝ) / ((rk L : ℝ) - (k : ℝ)) := div_nonneg (Nat.cast_nonneg _) (le_of_lt hkrR)
    have hYsT1 : Ys ^ (rk L - k) ≤ T ^ (rk L - k - 1) * Y := by
      calc Ys ^ (rk L - k) = Ys ^ (rk L - k - 1) * Ys := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ rk L - k)]
        _ ≤ T ^ (rk L - k - 1) * Y :=
            mul_le_mul (pow_le_pow_left₀ (le_of_lt hYspos) hYsT _) hYsY (le_of_lt hYspos)
              (by positivity)
    have hqYs : q * Ys ^ (rk L - k) ≤ K * Dv := by
      have h1 : q * Ys ^ (rk L - k) = (coneSliceVol L v w γ * Ys ^ (rk L - k)) / detL L := by
        rw [hq, div_mul_eq_mul_div]
      rw [h1]
      have h3 : K * Dv = (K * (T ^ (rk L - k - 1) * Y)) / detL L := by rw [hDv, mul_div_assoc']
      rw [h3]
      apply div_le_div_of_nonneg_right ?_ (le_of_lt hdetpos)
      calc coneSliceVol L v w γ * Ys ^ (rk L - k) ≤ K * Ys ^ (rk L - k) :=
            mul_le_mul_of_nonneg_right hVK (by positivity)
        _ ≤ K * (T ^ (rk L - k - 1) * Y) := mul_le_mul_of_nonneg_left hYsT1 hK0
    have hfac : (rk L : ℝ) / ((rk L : ℝ) - (k : ℝ)) ≤ (rk L : ℝ) := by
      have hkge : 1 ≤ (rk L : ℝ) - (k : ℝ) := by
        have h1 : k + 1 ≤ rk L := by omega
        have h2 : ((k + 1 : ℕ) : ℝ) ≤ (rk L : ℝ) := by exact_mod_cast h1
        push_cast at h2
        linarith
      have h1 : 1 / ((rk L : ℝ) - (k : ℝ)) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num) hkge
      have h2 : (rk L : ℝ) * (1 / ((rk L : ℝ) - (k : ℝ))) ≤ (rk L : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      have h3 : (rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))
          = (rk L : ℝ) * (1 / ((rk L : ℝ) - (k : ℝ))) := by rw [mul_one_div]
      rw [h3]
      simpa using h2
    calc q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Ys ^ (rk L - k))
        = ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (q * Ys ^ (rk L - k)) := by ring
      _ ≤ ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (K * Dv) := mul_le_mul_of_nonneg_left hqYs hRnn
      _ = (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * K) * Dv := by ring
      _ ≤ (K * (Fintype.card ι : ℝ)) * Dv := by
          apply mul_le_mul_of_nonneg_right ?_ hDvnn
          calc ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * K ≤ (rk L : ℝ) * K :=
                mul_le_mul_of_nonneg_right hfac hK0
            _ ≤ (Fintype.card ι : ℝ) * K := mul_le_mul_of_nonneg_right hrkcard hK0
            _ = K * (Fintype.card ι : ℝ) := by ring
  -- (9) final assembly
  have hmain : ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L
        * coneSliceVol L v w γ
      = q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k)) := by
    rw [hq, div_mul_eq_mul_div, div_mul_eq_mul_div]
    ring
  have hSmain : (∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k)
      - ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L * coneSliceVol L v w γ
      = (∑ᶠ a ∈ smallSet L v w γ Ys, 1 / eNorm a ^ k)
        + (ee T - ee Ys) / T ^ k
        + (∫ t in Ys..T, G t * (ee t - ee Ys))
        - q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Ys ^ (rk L - k)) := by
    rw [hsplitS, hSlarge, hmain]
    ring
  have habs : |(∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k)
      - ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L * coneSliceVol L v w γ|
      ≤ (∑ᶠ a ∈ ballSet L Y, 1 / eNorm a ^ k) + (K * (Fintype.card ι : ℝ)) * Dv
        + Cc * ((k : ℝ) + 3) * Dv := by
    rw [hSmain]
    have htri := abs_add_add_sub_le (∑ᶠ a ∈ smallSet L v w γ Ys, 1 / eNorm a ^ k)
      ((ee T - ee Ys) / T ^ k) (∫ t in Ys..T, G t * (ee t - ee Ys))
      (q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Ys ^ (rk L - k)))
    have hSnn : 0 ≤ ∑ᶠ a ∈ smallSet L v w γ Ys, 1 / eNorm a ^ k := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfinS]
      exact Finset.sum_nonneg fun a _ => div_nonneg zero_le_one (pow_nonneg (eNorm_nonneg a) k)
    have hQnn : 0 ≤ q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Ys ^ (rk L - k)) :=
      mul_nonneg hqnn (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (le_of_lt (by
        have hklt : (k : ℝ) < (rk L : ℝ) := by exact_mod_cast (by omega : k < rk L)
        linarith))) (pow_nonneg (le_of_lt hYspos) _))
    rw [abs_of_nonneg hSnn, abs_of_nonneg hQnn] at htri
    have he : Cc * ((k : ℝ) + 3) * Dv = 2 * Cc * Dv + Cc * ((k : ℝ) + 1) * Dv := by ring
    linarith [htri, hsmall, hYsq, hquot, herr, he.le, he.ge]
  calc |(∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k)
        - ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L
          * coneSliceVol L v w γ|
      ≤ (∑ᶠ a ∈ ballSet L Y, 1 / eNorm a ^ k) + (K * (Fintype.card ι : ℝ)) * Dv
          + Cc * ((k : ℝ) + 3) * Dv := habs
    _ = (K * (Fintype.card ι : ℝ) + Cc * ((k : ℝ) + 3)) * Dv
          + ∑ᶠ a ∈ ballSet L Y, 1 / eNorm a ^ k := by ring
    _ ≤ (K * (Fintype.card ι : ℝ) + Cc * ((k : ℝ) + 3) + 1) * Dv
          + ∑ᶠ a ∈ ballSet L Y, 1 / eNorm a ^ k := by
        have h1 : (K * (Fintype.card ι : ℝ) + Cc * ((k : ℝ) + 3)) * Dv
            ≤ (K * (Fintype.card ι : ℝ) + Cc * ((k : ℝ) + 3) + 1) * Dv :=
          mul_le_mul_of_nonneg_right (by linarith) hDvnn
        linarith
    _ = (K * (Fintype.card ι : ℝ) + Cc * ((k : ℝ) + 3) + 1) * T ^ (rk L - k - 1) * Y / detL L
          + ∑ᶠ a ∈ ballSet L Y, 1 / eNorm a ^ k := by
        rw [hDv, mul_div_assoc']
        ring

/-- (L0c) Weighted Abel summation of `ballConeCount`, with the WEIGHTED short-vector term.
This is stronger than the current `ballConeWeightedK` (whose additive term is the unweighted
count) and is the natural intermediate step: split the sum at `‖a‖ = Y`, bound the part
`‖a‖ ≤ Y` by the last term, and apply partial summation plus `ballConeCount` on `[Y, T]`. -/
theorem ballConeWeightedKw {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ T Y : ℝ),
      1 ≤ k → k + 1 < rk L → 0 < γ → 1 ≤ Y → lam L (rk L) ≤ Y → Y ≤ T →
      |(∑ᶠ a ∈ {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧
            toR a ∈ Cgam w γ}, 1 / eNorm a ^ k) -
        ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L *
          coneSliceVol L v w γ|
        ≤ C * T ^ (rk L - k - 1) * Y / detL L
          + ∑ᶠ a ∈ {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ Y}, 1 / eNorm a ^ k := by
  obtain ⟨Cc, hCc, hcnt⟩ := Work.HP.BCS.ballConeCountEst (ι := ι)
  obtain ⟨K, hKpos, hKcone⟩ := ConeSliceVolBound (ι := ι)
  exact main_aux (ι := ι) k Cc hCc
    (fun L v w γ t Y h1 h2 h3 h4 h5 => by
      simpa only [coneCount] using hcnt L v w γ t Y h1 h2 h3 h4 h5)
    K (le_of_lt hKpos)
    (fun L v w γ => ⟨by rw [coneSliceVol, subVol]; exact ENNReal.toReal_nonneg,
      hKcone L v w γ⟩)

end Work.HP.MM2
