import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.ballConeWeightedKw
import Submission.Work.HP.MM2.lam_GamLoc_le
import Submission.Work.HP.MM2.Sk2_short_sum_le
import Submission.Work.HP.detL_GamLoc
import Submission.Work.HP.coneSliceVol_GamLoc
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.JcVolAsymp
import Submission.Work.HP.JcVolDelta
import Submission.Work.HP.BCS.Setup
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.veronese_key
import Submission.Work.HP.Lat.card_Mon

/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `Sk2_loc_ell` in namespace Work.HP.MM2; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.MM2.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.MM2.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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

private lemma sk2_toE_const_mul {ι : Type*} (c : ℝ) (v : ι → ℝ) :
    toE (fun i => c * v i) = c • (toE v : EuclideanSpace ℝ ι) := by
  have h : (fun i => c * v i) = (c • v : ι → ℝ) := rfl
  rw [h]
  exact WithLp.toLp_smul 2 c v

private lemma sk2_deltaV_smul {ι : Type*} [Fintype ι] (c c' : ℝ) (u v : EuclideanSpace ℝ ι) :
    deltaV (c • u) (c' • v) = (c * c') ^ 2 * deltaV u v := by
  have h1 : ‖c • u‖ = |c| * ‖u‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖c' • v‖ = |c'| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h3 : inner ℝ (c • u) (c' • v) = c * c' * inner ℝ u v := by
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  rw [deltaV, h1, h2, h3, deltaV]
  rw [mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- (inline replacement for `MM2.JcVol_point_unif`) `JcVol` at the Veronese points. -/
private lemma sk2_jcVol_bound (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x y : Fin (n + 1) → ℤ), IsPrim x → IsPrim y →
      LinearIndependent ℤ ![x, y] → ∀ α : ℝ, 0 < α →
      |JcVol (toE (fun m => (2 * α / ‖toE (toR (veronese d n x))‖) * toR (veronese d n x) m))
          (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m))
        - ((NN d n : ℝ) - 2) / (NN d n : ℝ) * ballVol (NN d n - 2) *
            DeltaXY d n x y / α ^ 2| ≤
      C * (((NN d n : ℝ) - 2) / (NN d n : ℝ) * ballVol (NN d n - 2) *
            DeltaXY d n x y / α ^ 2) * min 1 (DeltaXY d n x y ^ 2 / α ^ 2) := by
  have hN : 3 ≤ NN d n := by
    rw [NN, Lat.card_Mon]
    have h : (d + 1).choose d ≤ (n + d).choose d := Nat.choose_le_choose d (by omega)
    rw [Nat.choose_succ_self_right d] at h
    omega
  obtain ⟨C, hCpos, hC⟩ := JcVolAsymp (Mon d n) hN
  refine ⟨C, hCpos, ?_⟩
  intro x y hx hy hxy α hα
  have hd1 : 1 ≤ d := by omega
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hy0 : y ≠ 0 := isPrim_ne_zero hy
  have hnx : veronese d n x ≠ 0 := veronese_ne_zero d n hd1 hx0
  have hny : veronese d n y ≠ 0 := veronese_ne_zero d n hd1 hy0
  have hEnx : 0 < eNorm (veronese d n x) := eNorm_pos_of_ne_zero hnx
  have hEny : 0 < eNorm (veronese d n y) := eNorm_pos_of_ne_zero hny
  have hν : LinearIndependent ℤ ![veronese d n x, veronese d n y] :=
    Sig2.nu_indep d n hd x y hx hy (ne_of_linInd x y hxy) (ne_neg_of_linInd x y hxy)
  set u : EuclideanSpace ℝ (Mon d n) := toE (toR (veronese d n x)) with hu
  set v : EuclideanSpace ℝ (Mon d n) := toE (toR (veronese d n y)) with hv
  have hnormu : ‖u‖ = eNorm (veronese d n x) := by rw [hu]; exact BCS.norm_toE_eq_eNorm _
  have hnormv : ‖v‖ = eNorm (veronese d n y) := by rw [hv]; exact BCS.norm_toE_eq_eNorm _
  have hupos : 0 < ‖u‖ := by rw [hnormu]; exact hEnx
  have hvpos : 0 < ‖v‖ := by rw [hnormv]; exact hEny
  have huv : LinearIndependent ℝ ![u, v] := by
    have h := BCS.linearIndependent_toEr_cast (κ := Fin 2) hν
    have heq : (fun i : Fin 2 => toEr (![veronese d n x, veronese d n y] i))
        = ![toEr (veronese d n x), toEr (veronese d n y)] := by
      funext i; fin_cases i <;> rfl
    rw [heq] at h
    rw [hu, hv]
    exact h
  have hinner : inner ℝ u v = dotR (toR (veronese d n x)) (toR (veronese d n y)) := by
    rw [hu, hv, BCS.inner_toE_toE, BCS.dotR_comm]
  have hwedge : deltaV u v = wedgeNorm (veronese d n x) (veronese d n y) ^ 2 := by
    have hpos : 0 < deltaV u v := JcVolDelta huv
    have hnn : 0 ≤ eNorm (veronese d n x) ^ 2 * eNorm (veronese d n y) ^ 2
        - dotR (toR (veronese d n x)) (toR (veronese d n y)) ^ 2 := by
      have h := hpos
      rw [deltaV, hnormu, hnormv, hinner] at h
      exact le_of_lt h
    rw [wedgeNorm, Real.sq_sqrt hnn, deltaV, hnormu, hnormv, hinner]
  have hwp : 0 < wedgeNorm (veronese d n x) (veronese d n y) := by
    have hpos : 0 < deltaV u v := JcVolDelta huv
    have h2 : wedgeNorm (veronese d n x) (veronese d n y) ^ 2 = deltaV u v := hwedge.symm
    have hnn : 0 ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
      rw [wedgeNorm]; exact Real.sqrt_nonneg _
    have hne : wedgeNorm (veronese d n x) (veronese d n y) ≠ 0 := by
      intro h0; rw [h0] at h2; simp at h2; linarith
    exact lt_of_le_of_ne hnn (Ne.symm hne)
  have hDxy : 0 < DeltaXY d n x y := by
    rw [DeltaXY]
    exact div_pos (mul_pos hEnx hEny) hwp
  set c : ℝ := 2 * α / ‖u‖ with hc
  set c' : ℝ := 2 * α / ‖v‖ with hc'
  have hcpos : 0 < c := by rw [hc]; positivity
  have hc'pos : 0 < c' := by rw [hc']; positivity
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hc'ne : c' ≠ 0 := ne_of_gt hc'pos
  set w : EuclideanSpace ℝ (Mon d n) := c • u with hw
  set z : EuclideanSpace ℝ (Mon d n) := c' • v with hz
  have harg1 : toE (fun m => c * toR (veronese d n x) m) = w := by
    rw [hw, sk2_toE_const_mul, ← hu]
  have harg2 : toE (fun m => c' * toR (veronese d n y) m) = z := by
    rw [hz, sk2_toE_const_mul, ← hv]
  have hind : LinearIndependent ℝ ![w, z] := by
    rw [hw, hz]
    exact (LinearIndependent.pair_smul_smul_iff (u := c) (v := c') (x := u) (y := v)
      (isUnit_iff_ne_zero.mpr hcne) (isUnit_iff_ne_zero.mpr hc'ne)).mpr huv
  have hδwz : deltaV w z = (c * c') ^ 2 * deltaV u v := by
    rw [hw, hz]; exact sk2_deltaV_smul c c' u v
  have hcp : c * c' * wedgeNorm (veronese d n x) (veronese d n y)
      = 4 * α ^ 2 / DeltaXY d n x y := by
    rw [hc, hc', hnormu, hnormv, DeltaXY]
    field_simp
    ring
  have hsq : deltaV w z = (4 * α ^ 2 / DeltaXY d n x y) ^ 2 := by
    rw [hδwz, hwedge, ← mul_pow, hcp]
  have hsqrt : Real.sqrt (deltaV w z) = 4 * α ^ 2 / DeltaXY d n x y := by
    rw [hsq, Real.sqrt_sq (by positivity)]
  have hnormw : ‖w‖ = 2 * α := by
    rw [hw, hc, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos,
      div_mul_cancel₀ _ (ne_of_gt hupos)]
  have hnormz : ‖z‖ = 2 * α := by
    rw [hz, hc', norm_smul, Real.norm_eq_abs, abs_of_pos hc'pos,
      div_mul_cancel₀ _ (ne_of_gt hvpos)]
  have hT : 4 * ((NN d n : ℝ) - 2) / (NN d n : ℝ) * ballVol (NN d n - 2)
        / Real.sqrt (deltaV w z)
      = ((NN d n : ℝ) - 2) / (NN d n : ℝ) * ballVol (NN d n - 2)
          * DeltaXY d n x y / α ^ 2 := by
    rw [hsqrt, div_div_eq_mul_div]; field_simp; try ring
  have hR : (‖w‖ + ‖z‖) ^ 2 / deltaV w z = DeltaXY d n x y ^ 2 / α ^ 2 := by
    rw [hnormw, hnormz, hsq, div_pow, div_div_eq_mul_div]; field_simp; try ring
  have hbound := hC w z hind
  rw [hT, hR] at hbound
  rw [harg1, harg2]
  exact hbound

private lemma Sk_eq_coneSum (d n : ℕ) [DecidableEq (Mon d n)] (L : Submodule ℤ (Mon d n → ℤ))
    (x y : Fin (n + 1) → ℤ) (T α : ℝ) :
    Sk d n 2 L (TlocSet d n x y T α) =
      ∑ᶠ a ∈ ({a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T ∧
        toR a ∈ Cgam (toR (veronese d n x)) α ∧ toR a ∈ Cgam (toR (veronese d n y)) α} : Set _),
        1 / eNorm a ^ 2 := by
  have hset : ({a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ a ∈ TlocSet d n x y T α} : Set _)
      = {a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T ∧
        toR a ∈ Cgam (toR (veronese d n x)) α ∧ toR a ∈ Cgam (toR (veronese d n y)) α} := by
    ext a
    simp only [Set.mem_ofPred_eq, TlocSet]
  unfold Sk
  rw [hset]

theorem Sk2_loc_ell (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x y : Fin (n + 1) → ℤ), IsPrim x → IsPrim y →
      LinearIndependent ℤ ![x, y] → ∀ (Q : ℕ) (α T : ℝ), 1 ≤ Q → 0 < α → (Q : ℝ) ≤ T →
      |Sk d n 2 (GamLoc d n x y Q) (TlocSet d n x y T α) -
          T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
            ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α ^ 2 * (Q : ℝ) ^ 2)|
        ≤ C * (T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y *
            ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / (α ^ 2 * (Q : ℝ) ^ 2)) *
            min 1 (DeltaXY d n x y ^ 2 / α ^ 2)
          + C * T ^ (NN d n - 3) * ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) / Q
          + C * (Q : ℝ) ^ (NN d n - 2) := by
  classical
  have hn : 1 ≤ n := by omega
  have hN6 : 6 ≤ NN d n := six_le_NN d n hd hdn
  have hN3 : 3 ≤ NN d n := by omega
  have hN2R : (0:ℝ) < (NN d n : ℝ) - 2 := by
    have h : (2:ℕ) < NN d n := by omega
    have h2 : (2:ℝ) < (NN d n : ℝ) := by exact_mod_cast h
    linarith
  obtain ⟨Cw, hCwpos, hCw⟩ := ballConeWeightedKw (ι := Mon d n) 2
  obtain ⟨Cj, hCjpos, hCj⟩ := sk2_jcVol_bound d n hd hn
  obtain ⟨Cs, hCspos, hCs⟩ := Sk2_short_sum_le (ι := Mon d n) hN3
  refine ⟨Cw + Cj + Cs, by positivity, ?_⟩
  intro x y hx hy hxy Q α T hQ hα hQT
  have hQpos : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hQ1R : (1:ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have hT0 : 0 ≤ T := le_trans hQpos.le hQT
  have hBV : 0 ≤ ballVol (NN d n - 2) := by
    rw [ballVol]; exact ENNReal.toReal_nonneg
  have hDel : 0 ≤ DeltaXY d n x y := by
    rw [DeltaXY]
    exact div_nonneg (mul_nonneg (eNorm_nonneg _) (eNorm_nonneg _)) (Real.sqrt_nonneg _)
  set L : Submodule ℤ (Mon d n → ℤ) := GamLoc d n x y Q with hL
  set gG : ℝ := ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) with hG
  set Mm : ℝ := T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y * gG / (α ^ 2 * (Q : ℝ) ^ 2) with hMM
  set ee : ℝ := min 1 (DeltaXY d n x y ^ 2 / α ^ 2) with hee
  obtain ⟨gJ, hJc⟩ : ∃ gJ : ℝ, gJ = JcVol
      (toE (fun m => (2 * α / ‖toE (toR (veronese d n x))‖) * toR (veronese d n x) m))
      (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) := ⟨_, rfl⟩
  obtain ⟨V0, hV0⟩ : ∃ V0 : ℝ, V0 = ((NN d n : ℝ) - 2) / (NN d n : ℝ) *
      ballVol (NN d n - 2) * DeltaXY d n x y / α ^ 2 := ⟨_, rfl⟩
  obtain ⟨Zz, hZz⟩ : ∃ Zz : ℝ, Zz = (NN d n : ℝ) / ((NN d n : ℝ) - 2) *
      T ^ (NN d n - 2) * gG / (Q : ℝ) ^ 2 := ⟨_, rfl⟩
  have hJ := hCj x y hx hy hxy α hα
  rw [← hJc, ← hV0, ← hee] at hJ
  obtain ⟨hrk, hlam⟩ := lam_GamLoc_le d n x y Q hQ
  have hrkL : rk L = NN d n := by rw [hL]; exact hrk
  have hlamL : lam L (rk L) ≤ (Q : ℝ) := by rw [hL, hrkL]; exact hlam
  have hklt : 2 + 1 < rk L := by rw [hrkL]; omega
  have hdet : detL L = (Q : ℝ) ^ 2 / gG := by
    rw [hL, hG]; exact detL_GamLoc d n hd hn x y hx hy hxy Q hQ
  have hcone : coneSliceVol L (toR (veronese d n x)) (toR (veronese d n y)) α = gJ := by
    rw [hL, hJc]; exact coneSliceVol_GamLoc d n hd x y Q hQ α hα
  have hshort := hCs L (Q : ℝ) hQ1R
  have hGpos : 0 < gG := by
    rw [hG]
    have hgp : 0 < Nat.gcd Q (gcdMinors2 x y).natAbs := by
      rcases Nat.eq_zero_or_pos (Nat.gcd Q (gcdMinors2 x y).natAbs) with h | h
      · rw [Nat.gcd_eq_zero_iff] at h; omega
      · exact h
    exact_mod_cast hgp
  have hGnn : 0 ≤ gG := hGpos.le
  have hGne : gG ≠ 0 := ne_of_gt hGpos
  have hbw := hCw L (toR (veronese d n x)) (toR (veronese d n y)) α T (Q : ℝ)
      (by norm_num) hklt hα hQ1R hlamL hQT
  have hsub2 : NN d n - 2 - 1 = NN d n - 3 := by omega
  have hbw' : |Sk d n 2 L (TlocSet d n x y T α) - Zz * gJ|
      ≤ Cw * T ^ (NN d n - 3) * (Q : ℝ) / ((Q : ℝ) ^ 2 / gG) +
        (∑ᶠ a ∈ ({a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ (Q : ℝ)} : Set _),
          1 / eNorm a ^ 2) := by
    have h1 : |Sk d n 2 L (TlocSet d n x y T α) -
          ((NN d n : ℝ) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) / ((Q : ℝ) ^ 2 / gG) * gJ)|
        ≤ Cw * T ^ (NN d n - 3) * (Q : ℝ) / ((Q : ℝ) ^ 2 / gG) +
          (∑ᶠ a ∈ ({a : Mon d n → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ (Q : ℝ)} : Set _),
            1 / eNorm a ^ 2) := by
      rw [← Sk_eq_coneSum d n L x y T α, hcone, hdet, hrkL, hsub2] at hbw
      exact hbw
    have h2 : (NN d n : ℝ) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) / ((Q : ℝ) ^ 2 / gG) * gJ
        = Zz * gJ := by
      rw [hZz, div_div_eq_mul_div]; try ring
    rwa [h2] at h1
  have hR2 : Cw * T ^ (NN d n - 3) * (Q : ℝ) / ((Q : ℝ) ^ 2 / gG)
      = Cw * (T ^ (NN d n - 3) * gG / (Q : ℝ)) := by
    field_simp
    try ring
  have hE1 : |Sk d n 2 L (TlocSet d n x y T α) - Zz * gJ|
      ≤ Cw * (T ^ (NN d n - 3) * gG / (Q : ℝ)) + Cs * (Q : ℝ) ^ (NN d n - 2) := by
    rw [hR2] at hbw'
    exact le_trans hbw' (add_le_add (le_refl _) hshort)
  have hratio : (NN d n : ℝ) / ((NN d n : ℝ) - 2) * (((NN d n : ℝ) - 2) / (NN d n : ℝ)) = 1 := by
    field_simp
    try ring
  have hZV : Zz * V0 = Mm := by
    rw [hZz, hV0, hMM]
    have key : ((NN d n : ℝ) / ((NN d n : ℝ) - 2) * T ^ (NN d n - 2) * gG / (Q : ℝ) ^ 2)
        * (((NN d n : ℝ) - 2) / (NN d n : ℝ) * ballVol (NN d n - 2) * DeltaXY d n x y / α ^ 2)
        = ((NN d n : ℝ) / ((NN d n : ℝ) - 2) * (((NN d n : ℝ) - 2) / (NN d n : ℝ)))
          * (T ^ (NN d n - 2) * ballVol (NN d n - 2) * DeltaXY d n x y * gG /
              (α ^ 2 * (Q : ℝ) ^ 2)) := by ring
    rw [key, hratio, one_mul]
  have hdiff : Zz * gJ - Mm = Zz * (gJ - V0) := by
    rw [← hZV]; ring
  have heenn : 0 ≤ ee := by
    rw [hee]
    exact le_min zero_le_one (div_nonneg (sq_nonneg _) (pow_nonneg hα.le 2))
  have hZnn : 0 ≤ Zz := by
    rw [hZz]
    exact div_nonneg (mul_nonneg (mul_nonneg (div_nonneg (by positivity) (le_of_lt hN2R))
      (pow_nonneg hT0 _)) hGnn) (pow_nonneg hQpos.le 2)
  have hMmnn : 0 ≤ Mm := by
    rw [hMM]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hT0 _) hBV) hDel) hGnn)
      (mul_nonneg (pow_nonneg hα.le 2) (pow_nonneg hQpos.le 2))
  have hE2 : |Zz * gJ - Mm| ≤ Cj * Mm * ee := by
    rw [hdiff, abs_mul]
    calc |Zz| * |gJ - V0| ≤ |Zz| * (Cj * V0 * ee) := mul_le_mul_of_nonneg_left hJ (abs_nonneg Zz)
      _ = Cj * Mm * ee := by rw [← hZV, abs_of_nonneg hZnn]; ring
  have hXnn : 0 ≤ T ^ (NN d n - 3) * gG / (Q : ℝ) :=
    div_nonneg (mul_nonneg (pow_nonneg hT0 _) hGnn) hQpos.le
  have hYnn : 0 ≤ (Q : ℝ) ^ (NN d n - 2) := pow_nonneg hQpos.le _
  have htri : |Sk d n 2 L (TlocSet d n x y T α) - Mm|
      ≤ |Sk d n 2 L (TlocSet d n x y T α) - Zz * gJ| + |Zz * gJ - Mm| := by
    have h : Sk d n 2 L (TlocSet d n x y T α) - Mm
        = (Sk d n 2 L (TlocSet d n x y T α) - Zz * gJ) + (Zz * gJ - Mm) := by ring
    rw [h]
    exact abs_add_le _ _
  have hCX : Cw * (T ^ (NN d n - 3) * gG / (Q : ℝ))
      ≤ (Cw + Cj + Cs) * (T ^ (NN d n - 3) * gG / (Q : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith [hCjpos, hCspos]) hXnn
  have hCY : Cs * (Q : ℝ) ^ (NN d n - 2) ≤ (Cw + Cj + Cs) * (Q : ℝ) ^ (NN d n - 2) :=
    mul_le_mul_of_nonneg_right (by linarith [hCwpos, hCjpos]) hYnn
  have hCm : Cj * (Mm * ee) ≤ (Cw + Cj + Cs) * (Mm * ee) :=
    mul_le_mul_of_nonneg_right (by linarith [hCwpos, hCspos]) (mul_nonneg hMmnn heenn)
  calc |Sk d n 2 L (TlocSet d n x y T α) - Mm|
      ≤ |Sk d n 2 L (TlocSet d n x y T α) - Zz * gJ| + |Zz * gJ - Mm| := htri
    _ ≤ (Cw * (T ^ (NN d n - 3) * gG / (Q : ℝ)) + Cs * (Q : ℝ) ^ (NN d n - 2)) + Cj * (Mm * ee) :=
        add_le_add hE1 (by rw [← mul_assoc]; exact hE2)
    _ ≤ (Cw * (T ^ (NN d n - 3) * gG / (Q : ℝ)) + Cs * (Q : ℝ) ^ (NN d n - 2))
          + (Cw + Cj + Cs) * (Mm * ee) := add_le_add (le_refl _) hCm
    _ ≤ ((Cw + Cj + Cs) * (T ^ (NN d n - 3) * gG / (Q : ℝ))
          + (Cw + Cj + Cs) * (Q : ℝ) ^ (NN d n - 2)) + (Cw + Cj + Cs) * (Mm * ee) :=
        add_le_add (add_le_add hCX hCY) (le_refl _)
    _ = (Cw + Cj + Cs) * Mm * ee + (Cw + Cj + Cs) * T ^ (NN d n - 3) * gG / Q
          + (Cw + Cj + Cs) * (Q : ℝ) ^ (NN d n - 2) := by ring

end Work.HP.MM2
