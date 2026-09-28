import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.latOrth_count_degenerate
import Submission.Work.HP.latOrth_count_pivotal
import Submission.Work.HP.lw_sum_inv_le_dyadic_shells
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.latOrth_weighted

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! Guidance from the project lead (the requester):
 from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `S1ball_le` in namespace Work.HP.MM2; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.MM2.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.MM2.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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




/-! ## Elementary helpers -/

/-- The set of nonzero lattice points of `Λ_{ν(x)}` of norm at most `T`. -/
private def SballSet (d n : ℕ) (x : Fin (n + 1) → ℤ) (T : ℝ) : Set (Mon d n → ℤ) :=
  {a | a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T}

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
private lemma one_le_eNorm_hp {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) : 1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h; push Not at h; exact hv (funext h)
  have h1 : (1 : ℝ) ≤ |(v i : ℝ)| := by
    have : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : |(v i : ℝ)| ≤ eNorm v := MDBasic.abs_apply_le_eNorm v i
  linarith

/-- `(2^{j+1}/T)·(T/2^j)^m = 2·(T/2^j)^{m-1}` for `T ≠ 0`, `m ≥ 1`. -/
private lemma dyadic_weight_mul {T : ℝ} (hT : T ≠ 0) (j m : ℕ) (hm : 1 ≤ m) :
    ((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j)^m = 2 * (T/(2:ℝ)^j)^(m-1) := by
  have h2j : (2:ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hx : T/(2:ℝ)^j ≠ 0 := div_ne_zero hT h2j
  have hkey : ((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j) = 2 := by
    have he : (2:ℝ)^(j+1) = (2:ℝ)^j * 2 := pow_succ _ _
    rw [he, div_mul_div_comm, mul_comm T ((2:ℝ)^j),
      mul_div_mul_right ((2:ℝ)^j * 2) ((2:ℝ)^j) (c := T) hT]
    exact mul_div_cancel_left₀ 2 h2j
  have hxJ : (T/(2:ℝ)^j)^m = (T/(2:ℝ)^j) * (T/(2:ℝ)^j)^(m-1) := by
    conv_lhs => rw [show m = (m-1)+1 from (Nat.sub_add_cancel hm).symm]
    rw [pow_succ]; ring
  rw [hxJ, ← mul_assoc, hkey]

/-- `(T/2^j)^m ≤ T^m·(1/2)^j` for `T ≥ 0`, `m ≥ 1`. -/
private lemma dyadic_pow_le (T : ℝ) (hT : 0 ≤ T) (j m : ℕ) (hm : 1 ≤ m) :
    (T/(2:ℝ)^j)^m ≤ T^m * ((1:ℝ)/2)^j := by
  have hbase : (0:ℝ) ≤ (1:ℝ)/2 := by norm_num
  have hTeq : T/(2:ℝ)^j = T * ((1:ℝ)/2)^j := by
    rw [div_eq_mul_inv, inv_eq_one_div, ← one_div_pow]
  rw [hTeq, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hle1 : ((1:ℝ)/2)^j ≤ 1 := pow_le_one₀ hbase (by norm_num)
  calc (((1:ℝ)/2)^j)^m ≤ (((1:ℝ)/2)^j)^1 := pow_le_pow_of_le_one (by positivity) hle1 hm
    _ = ((1:ℝ)/2)^j := pow_one _

/-- The dyadic shells above the threshold `μ` (pivotal regime). -/
private lemma pivot_shell_le (k J : ℕ) (Kp μ T C : ℝ) (B : ℕ → ℝ)
    (hC : 0 < C) (hT : 1 ≤ T) (hKp : 0 ≤ Kp) (hk3 : 3 ≤ k)
    (hPiv : ∀ j ≤ J, μ ≤ T / (2:ℝ)^j → B j ≤ Kp * (T / (2:ℝ)^j) ^ (k - 1) / C) :
    (∑ j ∈ (Finset.range (J+1)).filter (fun j => μ ≤ T/(2:ℝ)^j), ((2:ℝ)^(j+1)/T) * B j)
      ≤ 4 * Kp * (T^(k-2)/C) := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hTne : T ≠ 0 := ne_of_gt hT0
  have h1 : ∀ j ∈ (Finset.range (J+1)).filter (fun j => μ ≤ T/(2:ℝ)^j),
      ((2:ℝ)^(j+1)/T) * B j ≤ (2*Kp/C) * (T^(k-2) * ((1:ℝ)/2)^j) := by
    intro j hj
    obtain ⟨hjr, hjμ⟩ := Finset.mem_filter.mp hj
    have hjle : j ≤ J := by have := Finset.mem_range.mp hjr; omega
    have hWnn : 0 ≤ (2:ℝ)^(j+1)/T := by positivity
    calc ((2:ℝ)^(j+1)/T) * B j
        ≤ ((2:ℝ)^(j+1)/T) * (Kp * (T/(2:ℝ)^j)^(k-1) / C) :=
          mul_le_mul_of_nonneg_left (hPiv j hjle hjμ) hWnn
      _ = (Kp/C) * (((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j)^(k-1)) := by ring
      _ = (Kp/C) * (2 * (T/(2:ℝ)^j)^(k-2)) := by
          rw [dyadic_weight_mul hTne j (k-1) (by omega), show k - 1 - 1 = k - 2 from by omega]
      _ = (2*Kp/C) * (T/(2:ℝ)^j)^(k-2) := by ring
      _ ≤ (2*Kp/C) * (T^(k-2) * ((1:ℝ)/2)^j) := by
          refine mul_le_mul_of_nonneg_left (dyadic_pow_le T hT0.le j (k-2) (by omega)) ?_
          positivity
  calc (∑ j ∈ (Finset.range (J+1)).filter (fun j => μ ≤ T/(2:ℝ)^j), ((2:ℝ)^(j+1)/T) * B j)
      ≤ ∑ j ∈ (Finset.range (J+1)).filter (fun j => μ ≤ T/(2:ℝ)^j),
          (2*Kp/C) * (T^(k-2) * ((1:ℝ)/2)^j) := Finset.sum_le_sum h1
    _ = (2*Kp/C) * T^(k-2) * (∑ j ∈ (Finset.range (J+1)).filter (fun j => μ ≤ T/(2:ℝ)^j), ((1:ℝ)/2)^j) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ (2*Kp/C) * T^(k-2) * (∑ j ∈ Finset.range (J+1), ((1:ℝ)/2)^j) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => by positivity)
    _ ≤ (2*Kp/C) * T^(k-2) * 2 := by
        refine mul_le_mul_of_nonneg_left (lw_sum_half_pow_le (J+1)) (by positivity)
    _ = 4*Kp*(T^(k-2)/C) := by ring

/-- The dyadic shells below the threshold `μ` (degenerate regime). -/
private lemma degen_shell_le (k n J : ℕ) (Kd μ T C : ℝ) (B : ℕ → ℝ)
    (hC : 0 < C) (hT : 1 ≤ T) (hμ : 0 ≤ μ) (hKd : 0 ≤ Kd) (hkn : n + 3 ≤ k)
    (hDeg : ∀ j ≤ J, T / (2:ℝ)^j ≤ μ →
        B j ≤ Kd * ((T / (2:ℝ)^j) ^ (k - n) * μ ^ (n - 1) / C + (T / (2:ℝ)^j) ^ (k - n - 1))) :
    (∑ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)), ((2:ℝ)^(j+1)/T) * B j)
      ≤ 4 * Kd * (T^(k-n-1)*μ^(n-1)/C + T^(k-n-2)) := by
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hTne : T ≠ 0 := ne_of_gt hT0
  have h1 : ∀ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)),
      ((2:ℝ)^(j+1)/T) * B j
        ≤ (2*Kd*μ^(n-1)/C) * (T^(k-n-1) * ((1:ℝ)/2)^j) + (2*Kd) * (T^(k-n-2) * ((1:ℝ)/2)^j) := by
    intro j hj
    obtain ⟨hjr, hjμ⟩ := Finset.mem_filter.mp hj
    have hjle : j ≤ J := by have := Finset.mem_range.mp hjr; omega
    have hjle' : T/(2:ℝ)^j ≤ μ := le_of_lt (not_le.mp hjμ)
    have hWnn : 0 ≤ (2:ℝ)^(j+1)/T := by positivity
    calc ((2:ℝ)^(j+1)/T) * B j
        ≤ ((2:ℝ)^(j+1)/T) * (Kd * ((T/(2:ℝ)^j)^(k-n) * μ^(n-1)/C + (T/(2:ℝ)^j)^(k-n-1))) :=
          mul_le_mul_of_nonneg_left (hDeg j hjle hjle') hWnn
      _ = (Kd/C) * (((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j)^(k-n)) * μ^(n-1)
            + Kd * (((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j)^(k-n-1)) := by ring
      _ = (Kd/C) * (2 * (T/(2:ℝ)^j)^(k-n-1)) * μ^(n-1)
            + Kd * (2 * (T/(2:ℝ)^j)^(k-n-2)) := by
          rw [dyadic_weight_mul hTne j (k-n) (by omega),
              dyadic_weight_mul hTne j (k-n-1) (by omega),
              show k - n - 1 - 1 = k - n - 2 from by omega]
      _ = (2*Kd*μ^(n-1)/C) * (T/(2:ℝ)^j)^(k-n-1) + (2*Kd) * (T/(2:ℝ)^j)^(k-n-2) := by ring
      _ ≤ (2*Kd*μ^(n-1)/C) * (T^(k-n-1) * ((1:ℝ)/2)^j) + (2*Kd) * (T^(k-n-2) * ((1:ℝ)/2)^j) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul_of_nonneg_left (dyadic_pow_le T hT0.le j (k-n-1) (by omega)) ?_
            positivity
          · refine mul_le_mul_of_nonneg_left (dyadic_pow_le T hT0.le j (k-n-2) (by omega)) ?_
            positivity
  calc (∑ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)), ((2:ℝ)^(j+1)/T) * B j)
      ≤ ∑ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)),
          ((2*Kd*μ^(n-1)/C) * (T^(k-n-1) * ((1:ℝ)/2)^j) + (2*Kd) * (T^(k-n-2) * ((1:ℝ)/2)^j)) :=
        Finset.sum_le_sum h1
    _ = (2*Kd*μ^(n-1)/C) * T^(k-n-1) * (∑ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)), ((1:ℝ)/2)^j)
          + (2*Kd) * T^(k-n-2) * (∑ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)), ((1:ℝ)/2)^j) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
        · rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ (2*Kd*μ^(n-1)/C) * T^(k-n-1) * 2 + (2*Kd) * T^(k-n-2) * 2 := by
        refine add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => by positivity)) (lw_sum_half_pow_le (J+1))
        · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j _ _ => by positivity)) (lw_sum_half_pow_le (J+1))
    _ = 4 * Kd * (T^(k-n-1)*μ^(n-1)/C + T^(k-n-2)) := by ring

/-- The dyadic shell arithmetic: split the shells at `μ`, using the pivotal bound above and the
degenerate bound below. -/
private lemma shell_sum_bound (k n J : ℕ) (Kp Kd μ T C : ℝ) (B : ℕ → ℝ)
    (hC : 0 < C) (hT : 1 ≤ T) (hμ : 1 ≤ μ) (hkn : n + 3 ≤ k)
    (hJ : (2:ℝ)^J ≤ T) (hKp : 0 ≤ Kp) (hKd : 0 ≤ Kd)
    (hPiv : ∀ j ≤ J, μ ≤ T / (2:ℝ)^j → B j ≤ Kp * (T / (2:ℝ)^j) ^ (k - 1) / C)
    (hDeg : ∀ j ≤ J, T / (2:ℝ)^j ≤ μ →
        B j ≤ Kd * ((T / (2:ℝ)^j) ^ (k - n) * μ ^ (n - 1) / C + (T / (2:ℝ)^j) ^ (k - n - 1))) :
    (∑ j ∈ Finset.range (J + 1), ((2:ℝ) ^ (j + 1) / T) * B j)
      ≤ 4 * max Kp Kd * ((T ^ (k - 2) + T ^ (k - n - 1) * μ ^ (n - 1)) / C + T ^ (k - n - 2)) := by
  have hμ0 : 0 ≤ μ := le_trans zero_le_one hμ
  have hk3 : 3 ≤ k := by omega
  have hsplit : (∑ j ∈ (Finset.range (J+1)).filter (fun j => μ ≤ T/(2:ℝ)^j), ((2:ℝ)^(j+1)/T) * B j)
      + (∑ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)), ((2:ℝ)^(j+1)/T) * B j)
      = ∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) * B j :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [← hsplit]
  have hp := pivot_shell_le k J Kp μ T C B hC hT hKp hk3 hPiv
  have hd := degen_shell_le k n J Kd μ T C B hC hT hμ0 hKd hkn hDeg
  have hnn : 0 ≤ T^(k-2)/C := div_nonneg (pow_nonneg (le_trans zero_le_one hT) _) hC.le
  have hnn2 : 0 ≤ T^(k-n-1)*μ^(n-1)/C + T^(k-n-2) :=
    add_nonneg (div_nonneg (mul_nonneg (pow_nonneg (le_trans zero_le_one hT) _) (pow_nonneg hμ0 _)) hC.le)
      (pow_nonneg (le_trans zero_le_one hT) _)
  have hA : 4*Kp*(T^(k-2)/C) ≤ 4*max Kp Kd*(T^(k-2)/C) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left Kp Kd) (by norm_num : (0:ℝ) ≤ 4)) hnn
  have hB : 4*Kd*(T^(k-n-1)*μ^(n-1)/C + T^(k-n-2))
      ≤ 4*max Kp Kd*(T^(k-n-1)*μ^(n-1)/C + T^(k-n-2)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_right Kp Kd) (by norm_num : (0:ℝ) ≤ 4)) hnn2
  calc (∑ j ∈ (Finset.range (J+1)).filter (fun j => μ ≤ T/(2:ℝ)^j), ((2:ℝ)^(j+1)/T) * B j)
          + (∑ j ∈ (Finset.range (J+1)).filter (fun j => ¬ (μ ≤ T/(2:ℝ)^j)), ((2:ℝ)^(j+1)/T) * B j)
      ≤ 4*max Kp Kd*(T^(k-2)/C) + 4*max Kp Kd*(T^(k-n-1)*μ^(n-1)/C + T^(k-n-2)) :=
        add_le_add (le_trans hp hA) (le_trans hd hB)
    _ = 4 * max Kp Kd * ((T ^ (k - 2) + T ^ (k - n - 1) * μ ^ (n - 1)) / C + T ^ (k - n - 2)) := by ring

/-! ## `NN d n ≥ n + 3`

We exhibit an injection `Option (Fin (n+1)) ⊕ Unit → Mon d n` given by the `n+3` monomials
`x_i^d` (`i : Fin (n+1)`), `x_0^{d-1} x_1` and `x_0^{d-1} x_2`. -/

private def mkMon2 (d n : ℕ) (g : Fin (n + 1) → ℕ) (hg : ∀ i, g i ≤ d)
    (hsum : ∑ i, g i = d) : Mon d n :=
  ⟨fun i => ⟨g i, Nat.lt_succ_of_le (hg i)⟩, by simpa using hsum⟩

private lemma mkMon2_val (d n : ℕ) (g : Fin (n + 1) → ℕ) (hg : ∀ i, g i ≤ d)
    (hsum : ∑ i, g i = d) (j : Fin (n + 1)) :
    (((mkMon2 d n g hg hsum).1 j : Fin (d + 1)) : ℕ) = g j := rfl

private def famP2 (d n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun j => if j = i then d else 0

private def famD2 (d n : ℕ) (z o : Fin (n + 1)) : Fin (n + 1) → ℕ :=
  fun j => (if j = z then d - 1 else 0) + (if j = o then 1 else 0)

private lemma sum_famP2 (d n : ℕ) (i : Fin (n + 1)) : ∑ j, famP2 d n i j = d := by
  simp only [famP2]; rw [Fintype.sum_ite_eq']

private lemma le_famP2 (d n : ℕ) (i j : Fin (n + 1)) : famP2 d n i j ≤ d := by
  simp only [famP2]; split <;> omega

private lemma sum_famD2 (d n : ℕ) (hd : 1 ≤ d) (z o : Fin (n + 1)) (_h : z ≠ o) :
    ∑ j, famD2 d n z o j = d := by
  simp only [famD2]
  rw [Finset.sum_add_distrib, Fintype.sum_ite_eq', Fintype.sum_ite_eq']
  omega

private lemma le_famD2 (d n : ℕ) (hd : 2 ≤ d) (z o : Fin (n + 1)) (j : Fin (n + 1)) :
    famD2 d n z o j ≤ d := by
  simp only [famD2]; split_ifs <;> omega

private lemma famD2_self (d n : ℕ) (z o : Fin (n + 1)) (h : z ≠ o) :
    famD2 d n z o z = d - 1 := by
  show ((if z = z then d - 1 else 0) + (if z = o then 1 else 0) : ℕ) = d - 1
  rw [ite_eq_left rfl, ite_eq_right h, add_zero]

private lemma famD2_other (d n : ℕ) (z o : Fin (n + 1)) (h : z ≠ o) :
    famD2 d n z o o = 1 := by
  show ((if o = z then d - 1 else 0) + (if o = o then 1 else 0) : ℕ) = 1
  rw [ite_eq_right (Ne.symm h), ite_eq_left rfl, zero_add]

private def wit3 (d n : ℕ) (hd : 2 ≤ d) (z o w : Fin (n + 1)) (hzo : z ≠ o) (hzw : z ≠ w) :
    (Option (Fin (n + 1)) ⊕ Unit) → Mon d n
  | Sum.inl none => mkMon2 d n (famD2 d n z o) (le_famD2 d n hd z o) (sum_famD2 d n (by omega) z o hzo)
  | Sum.inl (some i) => mkMon2 d n (famP2 d n i) (le_famP2 d n i) (sum_famP2 d n i)
  | Sum.inr _ => mkMon2 d n (famD2 d n z w) (le_famD2 d n hd z w) (sum_famD2 d n (by omega) z w hzw)

private lemma wit3_none (d n : ℕ) (hd : 2 ≤ d) (z o w : Fin (n + 1)) (hzo : z ≠ o) (hzw : z ≠ w) :
    wit3 d n hd z o w hzo hzw (Sum.inl none)
      = mkMon2 d n (famD2 d n z o) (le_famD2 d n hd z o) (sum_famD2 d n (by omega) z o hzo) := rfl

private lemma wit3_some (d n : ℕ) (hd : 2 ≤ d) (z o w : Fin (n + 1)) (hzo : z ≠ o) (hzw : z ≠ w)
    (i : Fin (n+1)) :
    wit3 d n hd z o w hzo hzw (Sum.inl (some i))
      = mkMon2 d n (famP2 d n i) (le_famP2 d n i) (sum_famP2 d n i) := rfl

private lemma wit3_inr (d n : ℕ) (hd : 2 ≤ d) (z o w : Fin (n + 1)) (hzo : z ≠ o) (hzw : z ≠ w)
    (u : Unit) :
    wit3 d n hd z o w hzo hzw (Sum.inr u)
      = mkMon2 d n (famD2 d n z w) (le_famD2 d n hd z w) (sum_famD2 d n (by omega) z w hzw) := rfl

private lemma famD2_ne_famP2 (d n : ℕ) (hd : 2 ≤ d) (z o : Fin (n+1)) (hzo : z ≠ o) (i : Fin (n+1)) :
    famD2 d n z o z ≠ famP2 d n i z := by
  rw [famD2_self d n z o hzo]
  simp only [famP2]
  by_cases h : z = i
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h]; omega

private lemma famD2_ne_famD2' (d n : ℕ) (z o w : Fin (n+1)) (ho : o ≠ z) (how : o ≠ w) :
    famD2 d n z o o ≠ famD2 d n z w o := by
  rw [famD2_other d n z o (Ne.symm ho)]
  simp only [famD2]
  rw [ite_eq_right ho, ite_eq_right how, add_zero]
  norm_num

private theorem NN_ge_n_add_three (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : n + 3 ≤ NN d n := by
  let z : Fin (n + 1) := ⟨0, by omega⟩
  let o : Fin (n + 1) := ⟨1, by omega⟩
  let w : Fin (n + 1) := ⟨2, by omega⟩
  have hzo : z ≠ o := by intro h; have := congrArg Fin.val h; simp [z, o] at this
  have hzw : z ≠ w := by intro h; have := congrArg Fin.val h; simp [z, w] at this
  have how : o ≠ w := by intro h; have := congrArg Fin.val h; simp [o, w] at this
  have hkey : ∀ {m1 m2 : Mon d n} (c : Fin (n+1)),
      ((m1.1 c : Fin (d+1)) : ℕ) ≠ ((m2.1 c : Fin (d+1)) : ℕ) → m1 ≠ m2 :=
    fun c h hh => h (by rw [hh])
  have hinj : Function.Injective (wit3 d n hd z o w hzo hzw) := by
    intro a b hab
    cases a with
    | inl a' =>
      cases b with
      | inr u =>
        cases a' with
        | none =>
          exfalso
          refine hkey o ?_ hab
          rw [wit3_none, wit3_inr, mkMon2_val, mkMon2_val]
          exact famD2_ne_famD2' d n z o w (Ne.symm hzo) how
        | some i =>
          exfalso
          refine hkey z ?_ hab
          rw [wit3_some, wit3_inr, mkMon2_val, mkMon2_val]
          exact (famD2_ne_famP2 d n hd z w hzw i).symm
      | inl b' =>
        cases a' with
        | none =>
          cases b' with
          | none => rfl
          | some i =>
            exfalso
            refine hkey z ?_ hab
            rw [wit3_none, wit3_some, mkMon2_val, mkMon2_val]
            exact famD2_ne_famP2 d n hd z o hzo i
        | some i =>
          cases b' with
          | none =>
            exfalso
            refine hkey z ?_ hab
            rw [wit3_none, wit3_some, mkMon2_val, mkMon2_val]
            exact (famD2_ne_famP2 d n hd z o hzo i).symm
          | some i' =>
            refine congrArg (fun k => Sum.inl (some k)) ?_
            have hv := congrArg (fun m : Mon d n => ((m.1 i : Fin (d + 1)) : ℕ)) hab
            simp only [wit3_some, mkMon2_val] at hv
            simp only [famP2] at hv
            by_cases h : i = i'
            · exact h
            · rw [ite_eq_left trivial, ite_eq_right h] at hv; omega
    | inr u =>
      cases b with
      | inr u' => rfl
      | inl b' =>
        cases b' with
        | none =>
          exfalso
          refine hkey o ?_ hab
          rw [wit3_none, wit3_inr, mkMon2_val, mkMon2_val]
          exact (famD2_ne_famD2' d n z o w (Ne.symm hzo) how).symm
        | some i =>
          exfalso
          refine hkey z ?_ hab
          rw [wit3_some, wit3_inr, mkMon2_val, mkMon2_val]
          exact famD2_ne_famP2 d n hd z w hzw i
  have hcard : Fintype.card (Option (Fin (n + 1)) ⊕ Unit) = n + 3 := by
    rw [Fintype.card_sum, Fintype.card_option, Fintype.card_fin, Fintype.card_unit]
  rw [← hcard]
  exact Fintype.card_le_of_injective _ hinj

/-- (L0f) Weighted small-ball sum in `Λ_{ν(x)}`: dyadic shells, `latOrth_count_degenerate`
(its `n` := `n`, i.e. Lemma R0 with `R₀ = n-1`) below `μ`, `latOrth_count_pivotal` above `μ`. -/
theorem S1ball_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Fin (n + 1) → ℤ, IsPrim x → ∀ T μ : ℝ, 1 ≤ T → 1 ≤ μ →
      lamX d n x ≤ μ →
      S1ball d n x T ≤ K * ((T ^ (NN d n - 2) + T ^ (NN d n - n - 1) * μ ^ (n - 1)) /
          eNorm (veronese d n x) + T ^ (NN d n - n - 2) * (1 + Real.log T)) := by
  classical
  obtain ⟨Kp, hKppos, hPiv0⟩ := latOrth_count_pivotal (Mon d n)
  obtain ⟨Kd, hKdpos, hDeg0⟩ := latOrth_count_degenerate (Mon d n) n
  refine ⟨4 * max Kp Kd, by positivity, ?_⟩
  intro x hx T μ hT hμ hlam
  have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hcprim : IsPrim (veronese d n x) := isPrim_veronese d n (by omega) hx
  have hEpos : 0 < eNorm (veronese d n x) := eNorm_pos_of_ne_zero (isPrim_ne_zero hcprim)
  have hlamL : lam (latOrth (veronese d n x)) (NN d n - 1) ≤ μ := hlam
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, (2:ℝ)^J ≤ T ∧ T < (2:ℝ)^(J+1) := by
    have hfloor1 : 1 ≤ ⌊T⌋₊ := by
      have h := Nat.floor_mono hT
      simpa using h
    refine ⟨Nat.log 2 ⌊T⌋₊, ?_, ?_⟩
    · have h1' : 2^(Nat.log 2 ⌊T⌋₊) ≤ ⌊T⌋₊ := Nat.pow_log_le_self 2 (by omega)
      have h2' : ((2:ℕ)^(Nat.log 2 ⌊T⌋₊) : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast h1'
      have h3' : ((⌊T⌋₊ : ℕ) : ℝ) ≤ T := Nat.floor_le hT0.le
      calc (2:ℝ)^(Nat.log 2 ⌊T⌋₊) = ((2:ℕ)^(Nat.log 2 ⌊T⌋₊) : ℝ) := by push_cast; ring
        _ ≤ (⌊T⌋₊ : ℝ) := h2'
        _ ≤ T := h3'
    · have h1' : ⌊T⌋₊ < 2^((Nat.log 2 ⌊T⌋₊).succ) :=
        Nat.lt_pow_succ_log_self (by norm_num) ⌊T⌋₊
      have h2' : T < (⌊T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one T
      have h3' : ((⌊T⌋₊ : ℝ) + 1) ≤ (2:ℝ)^((Nat.log 2 ⌊T⌋₊).succ) := by
        have h4 : (⌊T⌋₊ + 1 : ℕ) ≤ 2^((Nat.log 2 ⌊T⌋₊).succ) := Nat.succ_le_of_lt h1'
        have h5 : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ ((2^((Nat.log 2 ⌊T⌋₊).succ) : ℕ) : ℝ) := by exact_mod_cast h4
        push_cast at h5 ⊢
        linarith
      exact lt_of_lt_of_le h2' h3'
  have hPfin : (SballSet d n x T).Finite :=
    (MDBasic.finite_eNorm_le (ι := Mon d n) T).subset (fun a ha => ha.2.2)
  have hP1 : ∀ a ∈ SballSet d n x T, 1 ≤ eNorm a := fun a ha => one_le_eNorm_hp ha.2.1
  have hP2 : ∀ a ∈ SballSet d n x T, eNorm a ≤ T := fun a ha => ha.2.2
  have hshell := lw_sum_inv_le_dyadic_shells (P := SballSet d n x T) hPfin hT hP1 hP2 J hJ2
  have hS1 : S1ball d n x T = ∑ᶠ a ∈ SballSet d n x T, 1 / eNorm a := rfl
  rw [hS1]
  have hcard : ∀ j, (({a | a ∈ SballSet d n x T ∧ eNorm a ≤ T/(2:ℝ)^j} : Set (Mon d n → ℤ)).ncard : ℝ)
      ≤ (ballCount (latOrth (veronese d n x)) (T/(2:ℝ)^j) : ℝ) := by
    intro j
    have hsub : ({a | a ∈ SballSet d n x T ∧ eNorm a ≤ T/(2:ℝ)^j} : Set (Mon d n → ℤ))
        ⊆ {a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ eNorm a ≤ T/(2:ℝ)^j} := by
      intro a ha
      exact ⟨ha.1.1, ha.2⟩
    have hfin : ({a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ eNorm a ≤ T/(2:ℝ)^j} : Set _).Finite :=
      (MDBasic.finite_eNorm_le (ι := Mon d n) _).subset (fun a ha => ha.2)
    have h := Set.ncard_le_ncard hsub hfin
    simpa [ballCount] using (Nat.cast_le (α := ℝ)).mpr h
  refine le_trans hshell ?_
  have hstep : (∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) *
        (({a | a ∈ SballSet d n x T ∧ eNorm a ≤ T/(2:ℝ)^j} : Set (Mon d n → ℤ)).ncard : ℝ))
      ≤ ∑ j ∈ Finset.range (J+1), ((2:ℝ)^(j+1)/T) *
        ((ballCount (latOrth (veronese d n x)) (T/(2:ℝ)^j) : ℕ) : ℝ) := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    exact mul_le_mul_of_nonneg_left (hcard j) (by positivity)
  refine le_trans hstep ?_
  have hPivB : ∀ j ≤ J, μ ≤ T / (2:ℝ)^j →
      (ballCount (latOrth (veronese d n x)) (T/(2:ℝ)^j) : ℝ)
        ≤ Kp * (T / (2:ℝ)^j) ^ (NN d n - 1) / eNorm (veronese d n x) := by
    intro j hjJ hjμ
    have h2jle : (2:ℝ)^j ≤ T := le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hjJ) hJ1
    have hTj1 : 1 ≤ T/(2:ℝ)^j := by rw [le_div_iff₀ (by positivity)]; linarith
    exact hPiv0 (veronese d n x) hcprim (T/(2:ℝ)^j) hTj1 (le_trans hlamL hjμ)
  have hDegB : ∀ j ≤ J, T / (2:ℝ)^j ≤ μ →
      (ballCount (latOrth (veronese d n x)) (T/(2:ℝ)^j) : ℝ)
        ≤ Kd * ((T / (2:ℝ)^j) ^ (NN d n - n) * μ ^ (n - 1) / eNorm (veronese d n x)
            + (T / (2:ℝ)^j) ^ (NN d n - n - 1)) := by
    intro j hjJ hjle
    have h2jle : (2:ℝ)^j ≤ T := le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hjJ) hJ1
    have hTj1 : 1 ≤ T/(2:ℝ)^j := by rw [le_div_iff₀ (by positivity)]; linarith
    exact hDeg0 (veronese d n x) hcprim μ (T/(2:ℝ)^j) hTj1 hjle hlamL
  have hssb := shell_sum_bound (NN d n) n J Kp Kd μ T (eNorm (veronese d n x))
      (fun j => (ballCount (latOrth (veronese d n x)) (T/(2:ℝ)^j) : ℝ))
      hEpos hT hμ (NN_ge_n_add_three d n hd hdn) hJ1 (le_of_lt hKppos) (le_of_lt hKdpos) hPivB hDegB
  refine le_trans hssb ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine add_le_add le_rfl ?_
  calc T^(NN d n - n - 2) = T^(NN d n - n - 2) * 1 := (mul_one _).symm
    _ ≤ T^(NN d n - n - 2) * (1 + Real.log T) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.log_nonneg hT]) (by positivity)


end Work.HP.MM2
