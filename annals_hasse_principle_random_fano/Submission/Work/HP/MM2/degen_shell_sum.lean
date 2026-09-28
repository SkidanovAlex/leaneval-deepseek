import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.FM3.ell_two_count_free
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.ceil_logb_bounds

/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `degen_shell_sum` in namespace Work.HP.MM2; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.MM2.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.MM2.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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

/-- A `finsum` over a finite set is the sum over the corresponding `Finset`. -/
private lemma finsum_mem_eq_sum_toFinset {α : Type*} (s : Set α) (hs : s.Finite) (f : α → ℝ) :
    (∑ᶠ x ∈ s, f x) = ∑ x ∈ hs.toFinset, f x := by
  have hsupp : Function.support (s.indicator f) ⊆ ↑(hs.toFinset) := by
    intro x hx
    by_contra hxS
    refine hx (Set.indicator_of_notMem (fun h => hxS ?_) _)
    exact Finset.mem_coe.mpr (hs.mem_toFinset.mpr h)
  rw [finsum_mem_def, finsum_eq_finsetSum_of_support_subset (s.indicator f) hsupp]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Set.indicator_of_mem (hs.mem_toFinset.mp (Finset.mem_coe.mp hx))]

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
private lemma one_le_eNorm_of_ne_zero' {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) :
    1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (funext h)
  have h1 : (1 : ℝ) ≤ |(v i : ℝ)| := by
    have : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : |(v i : ℝ)| ≤ eNorm v := MDBasic.abs_apply_le_eNorm v i
  linarith

/-- For a nonzero vector `x` and `2 ≤ card ι`, the least determinant of a rank-two sublattice
containing `x` is at least `1`. -/
private lemma dmin_two_singleton_ge_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (x : ι → ℤ) (hx : x ≠ 0) :
    1 ≤ dmin 2 ({x} : Set (ι → ℤ)) := by
  obtain ⟨L, hL, hxL⟩ := Lat.exists_rk_two x hx hcard
  refine le_csInf ⟨detL L, L, hL, ?_, rfl⟩ ?_
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hxL
  · rintro D ⟨L', -, -, rfl⟩
    exact Lat.detL_ge_one L'

/-- Dyadic shell selection: for `1 ≤ r ≤ X` there is a shell index `j ≤ ⌈log₂ X⌉` with
`r ≤ X/2^j` and `X/2^j < 2r`. -/
private lemma shell_select (X r : ℝ) (hX : 1 ≤ X) (hr : 1 ≤ r) (hrX : r ≤ X) :
    ∃ j : ℕ, j ≤ ⌈Real.logb 2 X⌉₊ ∧ r ≤ X / (2 : ℝ) ^ j ∧ X / (2 : ℝ) ^ j < 2 * r := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hXr1 : 1 ≤ X / r := by rw [le_div_iff₀ hr0]; linarith
  have hlog0 : 0 ≤ Real.logb 2 (X / r) := Real.logb_nonneg (by norm_num) hXr1
  set j : ℕ := ⌊Real.logb 2 (X / r)⌋₊ with hjdef
  have hi : ((2 : ℝ) ^ j) ≤ X / r := by
    rw [← Real.rpow_natCast (2 : ℝ) j]
    calc (2 : ℝ) ^ ((j : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Real.logb 2 (X / r)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hjdef]; exact Nat.floor_le hlog0)
      _ = X / r := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  have hii : X / r < (2 : ℝ) ^ (j + 1) := by
    have hlog : Real.logb 2 (X / r) < (j : ℝ) + 1 := by
      rw [hjdef]; exact Nat.lt_floor_add_one _
    have h' : X / r < (2 : ℝ) ^ ((j : ℝ) + 1) := by
      have hlt := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hlog
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)] at hlt
    calc X / r < (2 : ℝ) ^ ((j : ℝ) + 1) := h'
      _ = (2 : ℝ) ^ (j + 1) := by
          rw [← Real.rpow_natCast (2 : ℝ) (j + 1)]
          congr 1
          push_cast
          ring
  have hiii : j ≤ ⌈Real.logb 2 X⌉₊ := by
    have h1 : (j : ℝ) ≤ Real.logb 2 (X / r) := by rw [hjdef]; exact Nat.floor_le hlog0
    have h2 : Real.logb 2 (X / r) ≤ Real.logb 2 X :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (div_le_self (le_of_lt hX0) hr)
    have h3 : Real.logb 2 X ≤ (⌈Real.logb 2 X⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast le_trans h1 (le_trans h2 h3)
  refine ⟨j, hiii, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    have h := (le_div_iff₀ hr0).mp hi
    nlinarith [h]
  · rw [div_lt_iff₀ (by positivity)]
    have h := (div_lt_iff₀ hr0).mp hii
    calc X < (2 : ℝ) ^ (j + 1) * r := h
      _ = 2 * r * (2 : ℝ) ^ j := by rw [pow_succ]; ring

/-- Pointwise dyadic shell bound: for `1 ≤ r ≤ X`, `r^s` is bounded by the weighted indicator
sum over the dyadic shells up to `⌈log₂ X⌉`. -/
private lemma shell_pointwise (X s r : ℝ) (hX : 1 ≤ X) (hr : 1 ≤ r) (hrX : r ≤ X) :
    r ^ s ≤ (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (⌈Real.logb 2 X⌉₊ + 1),
      (if r ≤ X / (2 : ℝ) ^ j then (X / (2 : ℝ) ^ j) ^ s else 0) := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  obtain ⟨j, hjJ, hj1, hj2⟩ := shell_select X r hX hr hrX
  have hYpos : 0 < X / (2 : ℝ) ^ j := by positivity
  have hkey : r ^ s ≤ (2 : ℝ) ^ |s| * (X / (2 : ℝ) ^ j) ^ s := by
    by_cases hs : 0 ≤ s
    · have h1 : r ^ s ≤ (X / (2 : ℝ) ^ j) ^ s := Real.rpow_le_rpow (le_of_lt hr0) hj1 hs
      have h2 : 1 ≤ (2 : ℝ) ^ |s| := Real.one_le_rpow (by norm_num) (abs_nonneg s)
      have h3 : 0 ≤ (X / (2 : ℝ) ^ j) ^ s := Real.rpow_nonneg (le_of_lt hYpos) s
      calc r ^ s ≤ (X / (2 : ℝ) ^ j) ^ s := h1
        _ = 1 * (X / (2 : ℝ) ^ j) ^ s := (one_mul _).symm
        _ ≤ (2 : ℝ) ^ |s| * (X / (2 : ℝ) ^ j) ^ s := mul_le_mul_of_nonneg_right h2 h3
    · have hsneg : s < 0 := not_le.mp hs
      have hs0 : 0 < -s := by linarith
      have h2rpos : 0 < 2 * r := by linarith
      have h1 : (X / (2 : ℝ) ^ j) ^ (-s) ≤ (2 * r) ^ (-s) :=
        Real.rpow_le_rpow (le_of_lt hYpos) (le_of_lt hj2) (le_of_lt hs0)
      have hneg1 : (2 * r) ^ s = ((2 * r) ^ (-s))⁻¹ := by
        have h := Real.rpow_neg (le_of_lt h2rpos) (-s)
        rwa [neg_neg] at h
      have hneg2 : (X / (2 : ℝ) ^ j) ^ s = ((X / (2 : ℝ) ^ j) ^ (-s))⁻¹ := by
        have h := Real.rpow_neg (le_of_lt hYpos) (-s)
        rwa [neg_neg] at h
      have h3 : (2 * r) ^ s ≤ (X / (2 : ℝ) ^ j) ^ s := by
        have h2 : ((2 * r) ^ (-s))⁻¹ ≤ ((X / (2 : ℝ) ^ j) ^ (-s))⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos h2rpos (-s))
            (Real.rpow_pos_of_pos hYpos (-s))).mpr h1
        rw [hneg1, hneg2]
        exact h2
      have hmul : (2 : ℝ) ^ (-s) * (2 * r) ^ s ≤ (2 : ℝ) ^ (-s) * (X / (2 : ℝ) ^ j) ^ s :=
        mul_le_mul_of_nonneg_left h3 (le_of_lt (Real.rpow_pos_of_pos (by norm_num) (-s)))
      have hleft : (2 : ℝ) ^ (-s) * (2 * r) ^ s = r ^ s := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hr0), ← mul_assoc, ← Real.rpow_add (by norm_num),
          neg_add_cancel, Real.rpow_zero, one_mul]
      have habs : |s| = -s := abs_of_neg hsneg
      rw [habs]
      rwa [← hleft]
  have hjmem : j ∈ Finset.range (⌈Real.logb 2 X⌉₊ + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hjJ)
  have hnn : ∀ i ∈ Finset.range (⌈Real.logb 2 X⌉₊ + 1),
      (0 : ℝ) ≤ (if r ≤ X / (2 : ℝ) ^ i then (X / (2 : ℝ) ^ i) ^ s else 0) := by
    intro i _
    split_ifs with h
    · exact Real.rpow_nonneg (by positivity) s
    · exact le_refl 0
  have hsingle : (if r ≤ X / (2 : ℝ) ^ j then (X / (2 : ℝ) ^ j) ^ s else 0)
      ≤ ∑ i ∈ Finset.range (⌈Real.logb 2 X⌉₊ + 1),
          (if r ≤ X / (2 : ℝ) ^ i then (X / (2 : ℝ) ^ i) ^ s else 0) :=
    Finset.single_le_sum hnn hjmem
  rw [if_pos hj1] at hsingle
  exact le_trans hkey (mul_le_mul_of_nonneg_left hsingle (Real.rpow_nonneg (by norm_num) |s|))

/-- The dyadic shell sum of `(X/2^j)^α` over `j ≤ J` is at most `X^α / (1 - 2^{-α})`. -/
private lemma shell_sum_geometric (X α : ℝ) (hX : 1 ≤ X) (hα : 0 < α) (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), (X / (2 : ℝ) ^ j) ^ α ≤ X ^ α / (1 - (2 : ℝ) ^ (-α)) := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have hq1 : (2 : ℝ) ^ (-α) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (show -α < 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hq0 : 0 ≤ (2 : ℝ) ^ (-α) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) (-α))
  have hden : 0 < 1 - (2 : ℝ) ^ (-α) := by linarith
  have hterm : ∀ j : ℕ, (X / (2 : ℝ) ^ j) ^ α = X ^ α * ((2 : ℝ) ^ (-α)) ^ j := by
    intro j
    have h1 : ((2 : ℝ) ^ j) ^ α = (((2 : ℝ) ^ (-α)) ^ j)⁻¹ := by
      have hb : (0 : ℝ) ≤ (2 : ℝ) ^ (-α) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) (-α))
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (-α)) j]
      rw [← Real.rpow_neg hb (j : ℝ)]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (-α) (-(j : ℝ))]
      rw [← Real.rpow_natCast (2 : ℝ) j]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) (j : ℝ) α]
      congr 1
      ring
    calc (X / (2 : ℝ) ^ j) ^ α = X ^ α / ((2 : ℝ) ^ j) ^ α :=
          Real.div_rpow (le_of_lt hX0) (by positivity) α
      _ = X ^ α / (((2 : ℝ) ^ (-α)) ^ j)⁻¹ := by rw [h1]
      _ = X ^ α * ((2 : ℝ) ^ (-α)) ^ j := by rw [div_inv_eq_mul]
  have hg : ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ (-α)) ^ j ≤ 1 / (1 - (2 : ℝ) ^ (-α)) := by
    rw [geom_sum_eq (ne_of_lt hq1) (J + 1)]
    have h2 : (((2 : ℝ) ^ (-α)) ^ (J + 1) - 1) / ((2 : ℝ) ^ (-α) - 1)
        = (1 - ((2 : ℝ) ^ (-α)) ^ (J + 1)) / (1 - (2 : ℝ) ^ (-α)) := by
      rw [show (2 : ℝ) ^ (-α) - 1 = -(1 - (2 : ℝ) ^ (-α)) by ring,
        show ((2 : ℝ) ^ (-α)) ^ (J + 1) - 1 = -(1 - ((2 : ℝ) ^ (-α)) ^ (J + 1)) by ring,
        neg_div_neg_eq]
    rw [h2]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hden)
    linarith [pow_nonneg hq0 (J + 1)]
  calc ∑ j ∈ Finset.range (J + 1), (X / (2 : ℝ) ^ j) ^ α
      = ∑ j ∈ Finset.range (J + 1), X ^ α * ((2 : ℝ) ^ (-α)) ^ j :=
        Finset.sum_congr rfl (fun j _ => hterm j)
    _ = X ^ α * ∑ j ∈ Finset.range (J + 1), ((2 : ℝ) ^ (-α)) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ X ^ α * (1 / (1 - (2 : ℝ) ^ (-α))) :=
        mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (le_of_lt hX0) α)
    _ = X ^ α / (1 - (2 : ℝ) ^ (-α)) := by rw [mul_one_div]

/-- Per-shell arithmetic: with `t ≤ Y ≤ X`, `1 ≤ t`, `1 ≤ X` and `0 ≤ K₀`, the weighted shell
contribution `Y^s · K₀ Y² (Y/t)^n log(2Y/t)` is at most `K₀ Y^{n+2+s} (1 + log X) / t^n`. -/
private lemma shell_term_le (n : ℕ) (s X t Y K₀ : ℝ) (hK₀ : 0 ≤ K₀) (hX : 1 ≤ X) (ht : 1 ≤ t)
    (hYt : t ≤ Y) (hYX : Y ≤ X) :
    Y ^ s * (K₀ * Y ^ 2 * (Y / t) ^ n * Real.log (2 * (Y / t)))
      ≤ K₀ * Y ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) / t ^ n := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hY1 : 1 ≤ Y := le_trans ht hYt
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY1
  have hlog : Real.log (2 * (Y / t)) ≤ 1 + Real.log X := by
    have h1 : 2 * (Y / t) ≤ 2 * X := by
      have h2 : Y / t ≤ X := by
        rw [div_le_iff₀ ht0]; nlinarith [hYX, ht]
      linarith
    calc Real.log (2 * (Y / t)) ≤ Real.log (2 * X) := Real.log_le_log (by positivity) h1
      _ = Real.log 2 + Real.log X := Real.log_mul (by norm_num) (ne_of_gt (by linarith))
      _ ≤ 1 + Real.log X := by
          have h3 : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
          linarith
  have hid : Y ^ s * Y ^ 2 * (Y / t) ^ n = Y ^ ((n : ℝ) + 2 + s) / t ^ n := by
    have h2 : Y ^ 2 = Y ^ (2 : ℝ) := (Real.rpow_natCast Y 2).symm
    have htn : t ^ n = t ^ ((n : ℝ)) := (Real.rpow_natCast t n).symm
    have hdn : (Y / t) ^ n = (Y / t) ^ ((n : ℝ)) := (Real.rpow_natCast (Y / t) n).symm
    rw [h2, htn, hdn, Real.div_rpow (le_of_lt hY0) (le_of_lt ht0)]
    rw [← mul_div_assoc, ← Real.rpow_add hY0 s 2, ← Real.rpow_add hY0 (s + 2) (n : ℝ)]
    rw [show s + 2 + (n : ℝ) = (n : ℝ) + 2 + s by ring]
  have hAn : 0 ≤ K₀ * Y ^ ((n : ℝ) + 2 + s) / t ^ n := by
    have h1 : 0 < t ^ n := pow_pos ht0 n
    have h2 : 0 ≤ Y ^ ((n : ℝ) + 2 + s) := Real.rpow_nonneg (le_of_lt hY0) _
    positivity
  have hkey : Y ^ s * (K₀ * Y ^ 2 * (Y / t) ^ n) = K₀ * Y ^ ((n : ℝ) + 2 + s) / t ^ n := by
    rw [show Y ^ s * (K₀ * Y ^ 2 * (Y / t) ^ n)
          = K₀ * (Y ^ s * Y ^ 2 * (Y / t) ^ n) by ring, hid]
    ring
  calc Y ^ s * (K₀ * Y ^ 2 * (Y / t) ^ n * Real.log (2 * (Y / t)))
      = (K₀ * Y ^ ((n : ℝ) + 2 + s) / t ^ n) * Real.log (2 * (Y / t)) := by
        rw [← hkey]; ring
    _ ≤ (K₀ * Y ^ ((n : ℝ) + 2 + s) / t ^ n) * (1 + Real.log X) :=
        mul_le_mul_of_nonneg_left hlog hAn
    _ = K₀ * Y ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) / t ^ n := by ring

/-- (L0i) Single-vector degenerate sums (one dyadic variable + `FM3.ell_two_count_free`). -/
theorem degen_shell_sum (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < (n : ℝ) + 2 + s) :
    ∃ K : ℝ, 0 < K ∧ ∀ X t : ℝ, 1 ≤ X → 1 ≤ t →
      (∑ᶠ x ∈ {x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ X ∧
          t * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x}, eNorm x ^ s)
        ≤ K * X ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) / t ^ n := by
  obtain ⟨K₀, hK₀pos, hK₀⟩ := FM3.ell_two_count_free n hn
  have hncard : 2 ≤ Fintype.card (Fin (n + 1)) := by simp [Fintype.card_fin]; omega
  set α : ℝ := (n : ℝ) + 2 + s with hαdef
  have hα : 0 < α := hs
  have hq1 : (2 : ℝ) ^ (-α) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (show -α < 0 by linarith)
    rwa [Real.rpow_zero] at h
  have hqpos : 0 < (2 : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) (-α)
  have hcpos : 0 < (2 : ℝ) ^ |s| := Real.rpow_pos_of_pos (by norm_num) |s|
  refine ⟨(2 : ℝ) ^ |s| * K₀ / (1 - (2 : ℝ) ^ (-α)), ?_, ?_⟩
  · exact div_pos (mul_pos hcpos hK₀pos) (by linarith)
  intro X t hX ht
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  set Sset : Set (Fin (n + 1) → ℤ) :=
    {x | x ≠ 0 ∧ eNorm x ≤ X ∧ t * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x} with hSdef
  have hSfin : Sset.Finite :=
    (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) X).subset (fun v hv => hv.2.1)
  set F : Finset (Fin (n + 1) → ℤ) := hSfin.toFinset with hFdef
  have hFmem : ∀ x, x ∈ F ↔ x ∈ Sset := by
    intro x; rw [hFdef]; exact hSfin.mem_toFinset
  set J : ℕ := ⌈Real.logb 2 X⌉₊ with hJdef
  have hstep0 : (∑ᶠ x ∈ Sset, eNorm x ^ s) = ∑ x ∈ F, eNorm x ^ s := by
    rw [hFdef]
    exact finsum_mem_eq_sum_toFinset Sset hSfin _
  have hackj : ∀ j : ℕ,
      (X / (2 : ℝ) ^ j) ^ s * ((F.filter (fun x => eNorm x ≤ X / (2 : ℝ) ^ j)).card : ℝ)
        ≤ K₀ * (X / (2 : ℝ) ^ j) ^ α * (1 + Real.log X) / t ^ n := by
    intro j
    set Y : ℝ := X / (2 : ℝ) ^ j with hYdef
    have hYpos : 0 < Y := by rw [hYdef]; positivity
    have hYX : Y ≤ X := by
      rw [hYdef, div_le_iff₀ (by positivity)]
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      nlinarith [hX0, h2]
    by_cases htY : t ≤ Y
    · have hY1 : 1 ≤ Y := le_trans ht htY
      have hcount : ((F.filter (fun x => eNorm x ≤ Y)).card : ℝ)
          ≤ K₀ * Y ^ 2 * (Y / t) ^ n * Real.log (2 * (Y / t)) := by
        have hsub : (((F.filter (fun x => eNorm x ≤ Y) : Finset (Fin (n + 1) → ℤ))) :
              Set (Fin (n + 1) → ℤ))
            ⊆ {x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ Y ∧
                dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Y / t} := by
          intro x hx
          rw [Finset.mem_coe, Finset.mem_filter] at hx
          obtain ⟨hxF, hxY⟩ := hx
          obtain ⟨hx0, -, hcond⟩ := (hFmem x).mp hxF
          refine ⟨hx0, hxY, ?_⟩
          rw [le_div_iff₀ ht0]
          linarith [hcond]
        have hfin : ({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ Y ∧
              dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Y / t} : Set (Fin (n + 1) → ℤ)).Finite :=
          (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) Y).subset (fun v hv => hv.2.1)
        have h1 : ((F.filter (fun x => eNorm x ≤ Y)).card : ℝ)
            ≤ (({x : Fin (n + 1) → ℤ | x ≠ 0 ∧ eNorm x ≤ Y ∧
                dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ Y / t} :
                Set (Fin (n + 1) → ℤ)).ncard : ℝ) := by
          have h2 := Set.ncard_le_ncard hsub hfin
          rw [Set.ncard_coe_finset] at h2
          exact_mod_cast h2
        have hYt1 : 1 ≤ Y / t := by
          rw [le_div_iff₀ ht0]; linarith
        exact le_trans h1 (hK₀ Y (Y / t) hY1 hYt1)
      have h2 := shell_term_le n s X t Y K₀ (le_of_lt hK₀pos) hX ht htY hYX
      have h3 : Y ^ s * ((F.filter (fun x => eNorm x ≤ Y)).card : ℝ)
          ≤ Y ^ s * (K₀ * Y ^ 2 * (Y / t) ^ n * Real.log (2 * (Y / t))) :=
        mul_le_mul_of_nonneg_left hcount (le_of_lt (Real.rpow_pos_of_pos hYpos s))
      have hgoal : K₀ * Y ^ ((n : ℝ) + 2 + s) * (1 + Real.log X) / t ^ n
          = K₀ * Y ^ α * (1 + Real.log X) / t ^ n := by rw [hαdef]
      rw [hgoal] at h2
      exact le_trans h3 h2
    · have hempty : F.filter (fun x => eNorm x ≤ Y) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxF, hxY⟩ := hx
        obtain ⟨hx0, -, hcond⟩ := (hFmem x).mp hxF
        have hd : 1 ≤ dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
          dmin_two_singleton_ge_one hncard x hx0
        have hte : t ≤ eNorm x := by nlinarith [hcond, hd, ht]
        linarith [hxY, not_le.mp htY]
      rw [hempty]
      simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
      have hpos : (0 : ℝ) ≤ K₀ * Y ^ α * (1 + Real.log X) / t ^ n := by
        have h1 : 0 < Y ^ α := Real.rpow_pos_of_pos hYpos α
        have h2 : 0 < t ^ n := pow_pos ht0 n
        have h3 : 0 ≤ 1 + Real.log X := by linarith
        positivity
      linarith
  have hstep1 : ∑ x ∈ F, eNorm x ^ s
      ≤ (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (J + 1),
          (X / (2 : ℝ) ^ j) ^ s * ((F.filter (fun x => eNorm x ≤ X / (2 : ℝ) ^ j)).card : ℝ) := by
    calc ∑ x ∈ F, eNorm x ^ s
        ≤ ∑ x ∈ F, (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (J + 1),
            (if eNorm x ≤ X / (2 : ℝ) ^ j then (X / (2 : ℝ) ^ j) ^ s else 0) := by
          refine Finset.sum_le_sum (fun x hx => ?_)
          obtain ⟨hx0, hxX, -⟩ := (hFmem x).mp hx
          exact shell_pointwise X s (eNorm x) hX (one_le_eNorm_of_ne_zero' hx0) hxX
      _ = (2 : ℝ) ^ |s| * ∑ x ∈ F, ∑ j ∈ Finset.range (J + 1),
            (if eNorm x ≤ X / (2 : ℝ) ^ j then (X / (2 : ℝ) ^ j) ^ s else 0) :=
          (Finset.mul_sum _ _ _).symm
      _ = (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (J + 1), ∑ x ∈ F,
            (if eNorm x ≤ X / (2 : ℝ) ^ j then (X / (2 : ℝ) ^ j) ^ s else 0) := by
          rw [Finset.sum_comm]
      _ = (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (J + 1),
            (X / (2 : ℝ) ^ j) ^ s * ((F.filter (fun x => eNorm x ≤ X / (2 : ℝ) ^ j)).card : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hstep2 : (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (J + 1),
          (X / (2 : ℝ) ^ j) ^ s * ((F.filter (fun x => eNorm x ≤ X / (2 : ℝ) ^ j)).card : ℝ)
      ≤ (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (J + 1),
          K₀ * (X / (2 : ℝ) ^ j) ^ α * (1 + Real.log X) / t ^ n :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hackj j)) (le_of_lt hcpos)
  have hstep3 : ∑ j ∈ Finset.range (J + 1),
        K₀ * (X / (2 : ℝ) ^ j) ^ α * (1 + Real.log X) / t ^ n
      ≤ K₀ * (1 + Real.log X) / t ^ n * (X ^ α / (1 - (2 : ℝ) ^ (-α))) := by
    have h1 : ∑ j ∈ Finset.range (J + 1),
          K₀ * (X / (2 : ℝ) ^ j) ^ α * (1 + Real.log X) / t ^ n
        = K₀ * (1 + Real.log X) / t ^ n * ∑ j ∈ Finset.range (J + 1),
            (X / (2 : ℝ) ^ j) ^ α := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1]
    refine mul_le_mul_of_nonneg_left (shell_sum_geometric X α hX hα J) ?_
    have h2 : 0 < t ^ n := pow_pos ht0 n
    have h3 : 0 ≤ 1 + Real.log X := by linarith
    positivity
  have hmain : (∑ᶠ x ∈ Sset, eNorm x ^ s)
      ≤ ((2 : ℝ) ^ |s| * K₀ / (1 - (2 : ℝ) ^ (-α))) * X ^ α * (1 + Real.log X) / t ^ n := by
    have hden : (1 : ℝ) - (2 : ℝ) ^ (-α) ≠ 0 := by linarith
    have htn : t ^ n ≠ 0 := ne_of_gt (pow_pos ht0 n)
    calc (∑ᶠ x ∈ Sset, eNorm x ^ s) = ∑ x ∈ F, eNorm x ^ s := hstep0
      _ ≤ (2 : ℝ) ^ |s| * ∑ j ∈ Finset.range (J + 1),
            K₀ * (X / (2 : ℝ) ^ j) ^ α * (1 + Real.log X) / t ^ n := le_trans hstep1 hstep2
      _ ≤ (2 : ℝ) ^ |s| * (K₀ * (1 + Real.log X) / t ^ n *
            (X ^ α / (1 - (2 : ℝ) ^ (-α)))) :=
          mul_le_mul_of_nonneg_left hstep3 (le_of_lt hcpos)
      _ = ((2 : ℝ) ^ |s| * K₀ / (1 - (2 : ℝ) ^ (-α))) * X ^ α * (1 + Real.log X) / t ^ n := by
          field_simp
  exact hmain

end Work.HP.MM2
