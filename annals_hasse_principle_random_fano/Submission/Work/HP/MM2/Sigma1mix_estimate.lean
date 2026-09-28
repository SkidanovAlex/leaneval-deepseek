import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.Sstar1_mix_pair
import Submission.Work.HP.MM2.OmegaBad_mass
import Submission.Work.HP.MM2.finsum_mem_mono
import Submission.Work.HP.MM2.finsum_mem_abs_le
import Submission.Work.HP.MM2.Sigma1mix_arith
import Submission.Work.HP.MMReindex
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.EE_lower_all
import Submission.Work.HP.MDBasic.nonneg_basic
import Submission.Work.HP.FF_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `Sigma1mix_estimate` in namespace Work.HP.MM2; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.MM2.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.MM2.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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

private lemma detL_nonneg_s1 {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) : 0 ≤ detL L := by
  rw [detL]; exact Real.sqrt_nonneg _

private lemma errXY_nonneg_s1 (d n : ℕ) (B : ℝ) (x y : Fin (n + 1) → ℤ) :
    0 ≤ errXY d n B x y := by
  unfold errXY
  refine add_nonneg (le_min (by norm_num) (div_nonneg (sq_nonneg _) (sq_nonneg _))) ?_
  split <;> norm_num

private lemma finsum_mem_nonneg_s1 {α : Type*} {S : Set α} {f : α → ℝ}
    (h : ∀ p ∈ S, 0 ≤ f p) : 0 ≤ ∑ᶠ p ∈ S, f p := by
  rw [finsum_mem_def]
  refine finsum_nonneg (fun p => ?_)
  by_cases hp : p ∈ S
  · rw [Set.indicator_of_mem hp]; exact h p hp
  · rw [Set.indicator_of_notMem hp]

private lemma eNorm_veronese_pos_s1 {d n : ℕ} (hd : 1 ≤ d) {x : Fin (n + 1) → ℤ}
    (hx : IsPrim x) : 0 < eNorm (veronese d n x) := by
  apply eNorm_pos_of_ne_zero
  intro h0
  have hprim := isPrim_veronese d n hd hx
  rw [IsPrim, h0] at hprim
  have hz : (Finset.univ.gcd (0 : Mon d n → ℤ)) = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun i _ => rfl)
  rw [hz] at hprim
  exact one_ne_zero hprim.symm

theorem Sigma1mix_estimate (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ K B₀ : ℝ, ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      |Sigma1mix d n A B - mainTerm d n A B|
        ≤ K * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by
  classical
  obtain ⟨C, Bs, hCpos, hS⟩ := Sstar1_mix_pair d n hd hdn h22
  obtain ⟨Kb, Bb, hKbpos, hOb⟩ := OmegaBad_mass d n hd hdn h22
  obtain ⟨Kf, Bf, hKfpos, hFF⟩ := FF_bound d n hd hdn h22
  obtain ⟨c, Be, hcpos, hEE⟩ := EE_lower_all d n hd hdn h22
  obtain ⟨Ka, Ba, hKapos, hArith⟩ := Sigma1mix_arith (Kb / c) (C * Kf / c) C
  refine ⟨Ka, |Bs| + |Bb| + |Bf| + |Be| + |Ba| + 100, ?_⟩
  intro A B hB hA1 hA2
  have hBs : Bs ≤ B := by
    have : Bs ≤ |Bs| + |Bb| + |Bf| + |Be| + |Ba| + 100 := by
      linarith [le_abs_self Bs, abs_nonneg Bb, abs_nonneg Bf, abs_nonneg Be, abs_nonneg Ba]
    linarith
  have hBb : Bb ≤ B := by
    have : Bb ≤ |Bs| + |Bb| + |Bf| + |Be| + |Ba| + 100 := by
      linarith [le_abs_self Bb, abs_nonneg Bs, abs_nonneg Bf, abs_nonneg Be, abs_nonneg Ba]
    linarith
  have hBf : Bf ≤ B := by
    have : Bf ≤ |Bs| + |Bb| + |Bf| + |Be| + |Ba| + 100 := by
      linarith [le_abs_self Bf, abs_nonneg Bs, abs_nonneg Bb, abs_nonneg Be, abs_nonneg Ba]
    linarith
  have hBe : Be ≤ B := by
    have : Be ≤ |Bs| + |Bb| + |Bf| + |Be| + |Ba| + 100 := by
      linarith [le_abs_self Be, abs_nonneg Bs, abs_nonneg Bb, abs_nonneg Bf, abs_nonneg Ba]
    linarith
  have hBa : Ba ≤ B := by
    have : Ba ≤ |Bs| + |Bb| + |Bf| + |Be| + |Ba| + 100 := by
      linarith [le_abs_self Ba, abs_nonneg Bs, abs_nonneg Bb, abs_nonneg Bf, abs_nonneg Be]
    linarith
  obtain ⟨hApos, hBpos, hlogApos, harith⟩ := hArith A B hBa hA1 hA2
  have hB100 : 100 ≤ B := by
    have : (100 : ℝ) ≤ |Bs| + |Bb| + |Bf| + |Be| + |Ba| + 100 := by
      linarith [abs_nonneg Bs, abs_nonneg Bb, abs_nonneg Bf, abs_nonneg Be, abs_nonneg Ba]
    linarith
  have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith : 1 < B)
  have hWpos : 0 < (bigW (wOf B) : ℝ) := by
    have h : (1 : ℝ) ≤ (bigW (wOf B) : ℝ) := by exact_mod_cast one_le_bigW (wOf B)
    linarith
  have hιnn : 0 ≤ iotaDN d n := MDBasic.iotaDN_nonneg d n
  have hEEnn : 0 ≤ EE d n B := MDBasic.EE_nonneg d n B
  set K2 : ℝ := 2 * iotaDN d n * A ^ (NN d n - 2) with hK2
  have hK2nn : 0 ≤ K2 := by
    rw [hK2]
    exact mul_nonneg (mul_nonneg (by norm_num) hιnn) (pow_nonneg hApos.le _)
  have hαWnn : 0 ≤ Real.log B * (bigW (wOf B) : ℝ) / 4 := by positivity
  have hfinG : (OmegaGood d n A B).Finite :=
    (Omega_finite d n B).subset (fun p hp => by
      simp only [OmegaGood, Set.mem_setOf_eq] at hp; exact hp.1)
  have hfinB : (OmegaBad d n A B).Finite :=
    (Omega_finite d n B).subset (fun p hp => by
      simp only [OmegaBad, Set.mem_setOf_eq] at hp; exact hp.1)
  have hdisj : Disjoint (OmegaGood d n A B) (OmegaBad d n A B) := by
    rw [Set.disjoint_left]
    intro p hp1 hp2
    simp only [OmegaGood, OmegaBad, Set.mem_setOf_eq] at hp1 hp2
    exact hp2.2 hp1.2
  have hunion : OmegaGood d n A B ∪ OmegaBad d n A B = Omega d n B := by
    ext p
    simp only [Set.mem_union, OmegaGood, OmegaBad, Set.mem_setOf_eq]
    tauto
  set Xg : ℝ := ∑ᶠ p ∈ OmegaGood d n A B,
      Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) /
        eNorm (veronese d n p.2) with hXg
  set Yg : ℝ := ∑ᶠ p ∈ OmegaGood d n A B, mixMain d n A B p / eNorm (veronese d n p.2) with hYg
  set Zg : ℝ := ∑ᶠ p ∈ OmegaGood d n A B, 1 / detL (Gam d n p.1 p.2) with hZg
  set Zb : ℝ := ∑ᶠ p ∈ OmegaBad d n A B, 1 / detL (Gam d n p.1 p.2) with hZb
  set Fg : ℝ := ∑ᶠ p ∈ OmegaGood d n A B, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2) with hFg
  set Ag : ℝ := ∑ᶠ p ∈ OmegaGood d n A B,
      (errXY d n B p.1 p.2 + 1 / Real.log A) / detL (Gam d n p.1 p.2) with hAg
  set Yg' : ℝ := ∑ᶠ p ∈ OmegaGood d n A B,
      mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) / eNorm (veronese d n p.2) with hYg'
  have hEEsplit : EE d n B = Zg + Zb := by
    rw [hZg, hZb]
    change (∑ᶠ p ∈ Omega d n B, 1 / detL (Gam d n p.1 p.2)) = _
    rw [← hunion]
    exact finsum_mem_union hdisj hfinG hfinB
  have hFFsplit : FF d n B
      = (∑ᶠ p ∈ OmegaGood d n A B, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2))
        + (∑ᶠ p ∈ OmegaBad d n A B, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2)) := by
    change (∑ᶠ p ∈ Omega d n B, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2)) = _
    rw [← hunion]
    exact finsum_mem_union hdisj hfinG hfinB
  have hZbnn : 0 ≤ Zb := by
    rw [hZb]
    exact finsum_mem_nonneg_s1 (fun p hp => div_nonneg zero_le_one (detL_nonneg_s1 _))
  have hFbnn : 0 ≤ ∑ᶠ p ∈ OmegaBad d n A B, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2) :=
    finsum_mem_nonneg_s1 (fun p hp => div_nonneg (errXY_nonneg_s1 d n B p.1 p.2) (detL_nonneg_s1 _))
  have hZgle : Zg ≤ EE d n B := by rw [hEEsplit]; linarith
  have hFgle : Fg ≤ FF d n B := by rw [hFFsplit, hFg]; linarith [hFbnn]
  have hSig : Sigma1mix d n A B = (Real.log B * (bigW (wOf B) : ℝ) / 4) * Xg := by
    rw [hXg]; rfl
  have hMT : mainTerm d n A B = K2 * EE d n B := by
    change 2 * iotaDN d n * A ^ (NN d n - 2) * EE d n B = K2 * EE d n B
    rw [hK2]
  have hP1 : ∀ p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ),
      eNorm (veronese d n p.2) ≠ 0 →
      (Real.log B * (bigW (wOf B) : ℝ) / 4) * (mixMain d n A B p / eNorm (veronese d n p.2))
        = 2 * iotaDN d n * A ^ (NN d n - 2) / detL (Gam d n p.1 p.2) := by
    intro p hg
    have hlogBne : Real.log B ≠ 0 := ne_of_gt hlogBpos
    have hWne : ((bigW (wOf B) : ℕ) : ℝ) ≠ 0 := ne_of_gt hWpos
    rw [mixMain]
    by_cases hd0 : detL (Gam d n p.1 p.2) = 0
    · rw [hd0]; simp
    · have h1 : Real.log B * ((bigW (wOf B) : ℕ) : ℝ) * detL (Gam d n p.1 p.2) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hlogBne hWne) hd0
      field_simp
      ring
  have hmix : (Real.log B * (bigW (wOf B) : ℝ) / 4) * Yg = K2 * Zg := by
    rw [hYg, hZg]
    simp only [mul_finsum_mem]
    apply finsum_mem_congr rfl
    intro p hp
    have hp' : p ∈ Omega d n B := by
      have h := hp; simp only [OmegaGood, Set.mem_setOf_eq] at h; exact h.1
    have hgpos : 0 < eNorm (veronese d n p.2) :=
      eNorm_veronese_pos_s1 (by omega : 1 ≤ d) hp'.2.1.1
    calc (Real.log B * (bigW (wOf B) : ℝ) / 4) * (mixMain d n A B p / eNorm (veronese d n p.2))
        = 2 * iotaDN d n * A ^ (NN d n - 2) / detL (Gam d n p.1 p.2) := hP1 p (ne_of_gt hgpos)
      _ = K2 * (1 / detL (Gam d n p.1 p.2)) := by rw [hK2]; ring
  have hdiff : Xg - Yg = ∑ᶠ p ∈ OmegaGood d n A B,
      (Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) - mixMain d n A B p) / eNorm (veronese d n p.2) := by
    rw [hXg, hYg]
    rw [← finsum_mem_sub_distrib
      (fun p => Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) / eNorm (veronese d n p.2))
      (fun p => mixMain d n A B p / eNorm (veronese d n p.2)) hfinG]
    exact finsum_mem_congr rfl (fun p hp => (sub_div _ _ _).symm)
  have hAbsDiff : |Xg - Yg| ≤ C * Yg' := by
    rw [hdiff]
    refine le_trans (finsum_mem_abs_le (OmegaGood d n A B) (fun p =>
        (Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) - mixMain d n A B p) / eNorm (veronese d n p.2))) ?_
    have h2 : (∑ᶠ p ∈ OmegaGood d n A B,
          |(Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) - mixMain d n A B p) / eNorm (veronese d n p.2)|)
        ≤ ∑ᶠ p ∈ OmegaGood d n A B,
            C * (mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) / eNorm (veronese d n p.2)) := by
      apply finsum_mem_mono hfinG
      intro p hp
      have hp' : p ∈ Omega d n B := by
        have h := hp; simp only [OmegaGood, Set.mem_setOf_eq] at h; exact h.1
      have hgpos : 0 < eNorm (veronese d n p.2) :=
        eNorm_veronese_pos_s1 (by omega : 1 ≤ d) hp'.2.1.1
      rw [abs_div, abs_of_pos hgpos]
      have hSp := hS A B hBs hA1 hA2 p hp
      calc |Sstar d n 1 (GamMix d n p.1 p.2 (bigW (wOf B))) (TmixSet d n p.2 A (Real.log B)) - mixMain d n A B p| / eNorm (veronese d n p.2)
          ≤ (C * mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A)) / eNorm (veronese d n p.2) :=
            div_le_div_of_nonneg_right hSp hgpos.le
        _ = C * (mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) / eNorm (veronese d n p.2)) := by ring
    refine le_trans h2 ?_
    rw [hYg']
    exact (mul_finsum_mem (fun p => mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) / eNorm (veronese d n p.2)) C).symm.le
  have hYg'1 : (Real.log B * (bigW (wOf B) : ℝ) / 4) * Yg' = K2 * Ag := by
    rw [hYg', hAg]
    simp only [mul_finsum_mem]
    apply finsum_mem_congr rfl
    intro p hp
    have hp' : p ∈ Omega d n B := by
      have h := hp; simp only [OmegaGood, Set.mem_setOf_eq] at h; exact h.1
    have hgpos : 0 < eNorm (veronese d n p.2) :=
      eNorm_veronese_pos_s1 (by omega : 1 ≤ d) hp'.2.1.1
    calc (Real.log B * (bigW (wOf B) : ℝ) / 4) * (mixMain d n A B p * (errXY d n B p.1 p.2 + 1 / Real.log A) / eNorm (veronese d n p.2))
        = ((Real.log B * (bigW (wOf B) : ℝ) / 4) * (mixMain d n A B p / eNorm (veronese d n p.2))) * (errXY d n B p.1 p.2 + 1 / Real.log A) := by ring
      _ = (2 * iotaDN d n * A ^ (NN d n - 2) / detL (Gam d n p.1 p.2)) * (errXY d n B p.1 p.2 + 1 / Real.log A) := by rw [hP1 p (ne_of_gt hgpos)]
      _ = K2 * ((errXY d n B p.1 p.2 + 1 / Real.log A) / detL (Gam d n p.1 p.2)) := by rw [hK2]; ring
  have hAg_le : Ag ≤ FF d n B + EE d n B / Real.log A := by
    have hdec : Ag = Fg + (1 / Real.log A) * Zg := by
      rw [hAg, hFg, hZg]
      simp only [mul_finsum_mem]
      rw [← finsum_mem_add_distrib (s := OmegaGood d n A B)
        (f := fun p => errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2))
        (g := fun p => (1 / Real.log A) * (1 / detL (Gam d n p.1 p.2))) hfinG]
      exact finsum_mem_congr rfl (fun p hp => by rw [add_div]; ring)
    rw [hdec]
    have h2 : (1 / Real.log A) * Zg ≤ EE d n B / Real.log A := by
      calc (1 / Real.log A) * Zg ≤ (1 / Real.log A) * EE d n B :=
            mul_le_mul_of_nonneg_left hZgle (by positivity)
        _ = EE d n B / Real.log A := by ring
    linarith [hFgle, h2]
  have hFFle : FF d n B ≤ Kf * B ^ 2 / Real.log B ^ ((1 : ℝ) / 2) := hFF B hBf
  have hZble : Zb ≤ Kb * B ^ 2 / A ^ ((1 : ℝ) / 4) := by rw [hZb]; exact hOb A B hBb hA1 hA2
  have hB2le : B ^ 2 ≤ EE d n B / c := by
    have h := hEE B hBe
    rw [le_div_iff₀ hcpos]
    nlinarith [h]
  have hbr : C * FF d n B + C * EE d n B / Real.log A + Zb
      ≤ EE d n B * (Ka / Real.log A ^ ((1 : ℝ) / 2)) := by
    have hslog : 0 ≤ Real.log B ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hlogBpos.le _
    have hsqA : 0 ≤ A ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hApos.le _
    have h1 : C * FF d n B ≤ EE d n B * ((C * Kf / c) / Real.log B ^ ((1 : ℝ) / 2)) := by
      calc C * FF d n B ≤ C * (Kf * B ^ 2 / Real.log B ^ ((1 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hFFle hCpos.le
        _ ≤ C * (Kf * (EE d n B / c) / Real.log B ^ ((1 : ℝ) / 2)) := by
              apply mul_le_mul_of_nonneg_left _ hCpos.le
              apply div_le_div_of_nonneg_right _ hslog
              exact mul_le_mul_of_nonneg_left hB2le hKfpos.le
        _ = EE d n B * ((C * Kf / c) / Real.log B ^ ((1 : ℝ) / 2)) := by ring
    have h3 : Zb ≤ EE d n B * ((Kb / c) / A ^ ((1 : ℝ) / 4)) := by
      calc Zb ≤ Kb * B ^ 2 / A ^ ((1 : ℝ) / 4) := hZble
        _ ≤ Kb * (EE d n B / c) / A ^ ((1 : ℝ) / 4) := by
              apply div_le_div_of_nonneg_right _ hsqA
              exact mul_le_mul_of_nonneg_left hB2le hKbpos.le
        _ = EE d n B * ((Kb / c) / A ^ ((1 : ℝ) / 4)) := by ring
    have h2 : C * EE d n B / Real.log A = EE d n B * (C / Real.log A) := by ring
    calc C * FF d n B + C * EE d n B / Real.log A + Zb
        ≤ EE d n B * ((C * Kf / c) / Real.log B ^ ((1 : ℝ) / 2)) + EE d n B * (C / Real.log A) + EE d n B * ((Kb / c) / A ^ ((1 : ℝ) / 4)) := by
            linarith [h1, h3, h2.le]
      _ = EE d n B * ((Kb / c) / A ^ ((1 : ℝ) / 4) + (C * Kf / c) / Real.log B ^ ((1 : ℝ) / 2) + C / Real.log A) := by ring
      _ ≤ EE d n B * (Ka / Real.log A ^ ((1 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left harith hEEnn
  have hAbsMain : |Sigma1mix d n A B - mainTerm d n A B|
      ≤ K2 * EE d n B * (Ka / Real.log A ^ ((1 : ℝ) / 2)) := by
    have hYg'1le : (Real.log B * (bigW (wOf B) : ℝ) / 4) * Yg'
        ≤ K2 * (FF d n B + EE d n B / Real.log A) := by
      rw [hYg'1]
      exact mul_le_mul_of_nonneg_left hAg_le hK2nn
    have hEq : Sigma1mix d n A B - mainTerm d n A B
        = (Real.log B * (bigW (wOf B) : ℝ) / 4) * (Xg - Yg) - K2 * Zb := by
      have hg1 : Sigma1mix d n A B = (Real.log B * (bigW (wOf B) : ℝ) / 4) * Xg := hSig
      have hm1 : mainTerm d n A B = K2 * EE d n B := hMT
      have he1 : EE d n B = Zg + Zb := hEEsplit
      have hy1 : (Real.log B * (bigW (wOf B) : ℝ) / 4) * Yg = K2 * Zg := hmix
      rw [hg1, hm1, he1]
      calc (Real.log B * (bigW (wOf B) : ℝ) / 4) * Xg - K2 * (Zg + Zb)
          = (Real.log B * (bigW (wOf B) : ℝ) / 4) * Xg - K2 * Zg - K2 * Zb := by ring
        _ = (Real.log B * (bigW (wOf B) : ℝ) / 4) * Xg - (Real.log B * (bigW (wOf B) : ℝ) / 4) * Yg - K2 * Zb := by rw [hy1]
        _ = (Real.log B * (bigW (wOf B) : ℝ) / 4) * (Xg - Yg) - K2 * Zb := by ring
    calc |Sigma1mix d n A B - mainTerm d n A B|
        = |(Real.log B * (bigW (wOf B) : ℝ) / 4) * (Xg - Yg) - K2 * Zb| := by rw [hEq]
      _ ≤ |(Real.log B * (bigW (wOf B) : ℝ) / 4) * (Xg - Yg)| + |K2 * Zb| := by
            simpa [sub_eq_add_neg] using abs_add_le ((Real.log B * (bigW (wOf B) : ℝ) / 4) * (Xg - Yg)) (-(K2 * Zb))
      _ = (Real.log B * (bigW (wOf B) : ℝ) / 4) * |Xg - Yg| + K2 * Zb := by
            rw [abs_mul, abs_of_nonneg hαWnn, abs_mul, abs_of_nonneg hK2nn, abs_of_nonneg hZbnn]
      _ ≤ (Real.log B * (bigW (wOf B) : ℝ) / 4) * (C * Yg') + K2 * Zb := by
            have := mul_le_mul_of_nonneg_left hAbsDiff hαWnn
            linarith
      _ = C * ((Real.log B * (bigW (wOf B) : ℝ) / 4) * Yg') + K2 * Zb := by ring
      _ ≤ C * (K2 * (FF d n B + EE d n B / Real.log A)) + K2 * Zb := by
            have := mul_le_mul_of_nonneg_left hYg'1le hCpos.le
            linarith
      _ = K2 * (C * FF d n B + C * EE d n B / Real.log A + Zb) := by ring
      _ ≤ K2 * (EE d n B * (Ka / Real.log A ^ ((1 : ℝ) / 2))) := mul_le_mul_of_nonneg_left hbr hK2nn
      _ = K2 * EE d n B * (Ka / Real.log A ^ ((1 : ℝ) / 2)) := by ring
  calc |Sigma1mix d n A B - mainTerm d n A B|
      ≤ K2 * EE d n B * (Ka / Real.log A ^ ((1 : ℝ) / 2)) := hAbsMain
    _ = Ka * mainTerm d n A B / Real.log A ^ ((1 : ℝ) / 2) := by
          rw [hMT, hK2]
          ring

end Work.HP.MM2
