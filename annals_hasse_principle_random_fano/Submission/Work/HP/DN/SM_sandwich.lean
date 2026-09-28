import Mathlib
import Submission.Work.HP.DN.Defs
import Submission.Work.HP.count_basic
import Submission.Work.HP.DN.deep_failure_count
import Submission.Work.HP.DN.bad_prime_count
import Submission.Work.HP.DN.primCount_lower

/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `SM_sandwich` in namespace Work.HP.DN; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.DN.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.DN.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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

namespace Work.HP.DN

open Filter Finset MeasureTheory Pointwise
open Work.HP


noncomputable section

private def smC (d n M : ℕ) (a : Mon d n → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≤ M → PrimModZero d n a p (4 * M)

private def locC (d n : ℕ) (W : ℝ) (a : Mon d n → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ℝ) ≤ W → PrimModZero d n a p (rOf p W)

private def badC (d n M : ℕ) (W : ℝ) (a : Mon d n → ℤ) : Prop :=
  smC d n M a ∧ ¬ locC d n W a

private def T1C (d n M : ℕ) (W : ℝ) (p : ℕ) (a : Mon d n → ℤ) : Prop :=
  PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p (rOf p W)

private def T2C (d n : ℕ) (W : ℝ) (p : ℕ) (a : Mon d n → ℤ) : Prop :=
  ¬ PrimModZero d n a p (rOf p W)

private lemma rOf_ge_four_mul (p M : ℕ) (hp : p.Prime) (w : ℝ)
    (h : p ^ (4 * M) ≤ Nat.ceil w) : 4 * M ≤ rOf p w := by
  have hb : 1 < p := hp.one_lt
  have h1 : p ^ (4 * M) ≤ p ^ (Nat.clog p (Nat.ceil w)) :=
    h.trans (Nat.le_pow_clog hb (Nat.ceil w))
  have h2 : 4 * M ≤ Nat.clog p (Nat.ceil w) := (Nat.pow_le_pow_iff_right hb).mp h1
  show 4 * M ≤ Nat.clog p (Nat.ceil w) + 1
  omega

private lemma primModZero_mono' {d n : ℕ} {a : Mon d n → ℤ} {p r r' : ℕ}
    (h : PrimModZero d n a p r') (hr : r ≤ r') : PrimModZero d n a p r := by
  obtain ⟨x, hx, hdvd⟩ := h
  exact ⟨x, hx, (pow_dvd_pow _ hr).trans hdvd⟩

private lemma primCount_mono' {d n : ℕ} (A : ℝ) {P P' : (Mon d n → ℤ) → Prop}
    (hP : ∀ a, P a → P' a) : primCount d n A P ≤ primCount d n A P' := by
  have hsub : primSet d n A P ⊆ primSet d n A P' :=
    fun a ha => ⟨ha.1, ha.2.1, hP a ha.2.2⟩
  rw [primCount, primCount]
  exact_mod_cast Set.ncard_le_ncard hsub (primSet_finite d n A P')

private lemma ratio_mono' {d n : ℕ} (A : ℝ) {P P' : (Mon d n → ℤ) → Prop}
    (hP : ∀ a, P a → P' a) : ratio d n A P ≤ ratio d n A P' := by
  rw [ratio, ratio]
  exact div_le_div_of_nonneg_right (primCount_mono' A hP) (by rw [primCount]; positivity)

private lemma sum_inv_pow_le' (M : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) (hScard : S.card ≤ 2 * M) :
    ∑ p ∈ S, 1 / (p : ℝ) ^ (2 * M) ≤ 2 * (M : ℝ) / (4 : ℝ) ^ M := by
  have hterm : ∀ p ∈ S, 1 / (p : ℝ) ^ (2 * M) ≤ 1 / (4 : ℝ) ^ M := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
    have h4 : (4 : ℝ) ^ M = (2 : ℝ) ^ (2 * M) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_mul]
    rw [h4]
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hp2 (2 * M))
  calc ∑ p ∈ S, 1 / (p : ℝ) ^ (2 * M)
      ≤ ∑ _p ∈ S, 1 / (4 : ℝ) ^ M := Finset.sum_le_sum hterm
    _ = S.card * (1 / (4 : ℝ) ^ M) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (S.card : ℝ) / (4 : ℝ) ^ M := by ring
    _ ≤ 2 * (M : ℝ) / (4 : ℝ) ^ M :=
        div_le_div_of_nonneg_right (by exact_mod_cast hScard) (by positivity)

private lemma sum_primes_tail_le' (M Wn n : ℕ) (hM : 1 ≤ M) (hn : 3 ≤ n) :
    ∑ p ∈ ((Finset.range (Wn + 1)).filter Nat.Prime).filter (fun p => M < p),
      1 / (p : ℝ) ^ (n - 1) ≤ 1 / (M : ℝ) := by
  set S2 : Finset ℕ := ((Finset.range (Wn + 1)).filter Nat.Prime).filter (fun p => M < p) with hS2
  have hsub : S2 ⊆ Finset.Ioc M (max M Wn) := by
    intro p hp
    rw [hS2, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hp
    rw [Finset.mem_Ioc]
    exact ⟨hp.2, le_trans (Nat.lt_succ_iff.mp hp.1.1) (le_max_right _ _)⟩
  have hterm : ∀ p ∈ S2, 1 / (p : ℝ) ^ (n - 1) ≤ 1 / (p : ℝ) ^ 2 := by
    intro p hp
    rw [hS2, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hp
    have hp2 : (2 : ℕ) ≤ p := hp.1.2.two_le
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    exact one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_right₀ hp1 (by omega : 2 ≤ n - 1))
  calc ∑ p ∈ S2, 1 / (p : ℝ) ^ (n - 1)
      ≤ ∑ p ∈ S2, 1 / (p : ℝ) ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ x ∈ Finset.Ioc M (max M Wn), 1 / (x : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by positivity)
    _ ≤ 1 / (M : ℝ) - 1 / (max M Wn : ℝ) := by
        simpa only [one_div, Nat.cast_max] using
          (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := M) (n := max M Wn) (by omega)
            (le_max_left _ _))
    _ ≤ 1 / (M : ℝ) := by
        have : 0 ≤ 1 / (max M Wn : ℝ) := by positivity
        linarith

/-- (D9) Sandwich at a fixed level `M`: eventually `LocSet (w A) ⊆ SM M` (needs `r_p(w A) ≥ 4M`
for `p ≤ M` and `M ≤ w A`), and the difference is covered by D7 (`p ≤ M`) and D8
(`M < p ≤ w A ≤ A`), normalised by `count_basic`. -/
theorem SM_sandwich (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 1 ≤ M → ∀ w : ℝ → ℝ, Tendsto w atTop atTop →
      (∀ᶠ A in atTop, w A ≤ A) → ∀ᶠ A in atTop,
        ratio d n A (LocSet d n (w A)) ≤ ratio d n A (SM d n M) ∧
        ratio d n A (SM d n M) ≤
          ratio d n A (LocSet d n (w A)) + C * ((M : ℝ) / 4 ^ M + 1 / (M : ℝ)) := by
  classical
  obtain ⟨C2, hC2, hD8⟩ := bad_prime_count d n hd hn
  obtain ⟨c0, hc0, hc0low⟩ := primCount_lower d n hd hn
  let C1 : ℝ := 4 * (3 : ℝ) ^ (NN d n)
  have hC1 : 0 < C1 := by positivity
  have hD7 : ∀ (p M R : ℕ), p.Prime → 1 ≤ M → 4 * M ≤ R → ∀ A : ℝ,
      (p : ℝ) ^ (4 * M) ≤ A →
      primCount d n A (fun a => PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R)
        ≤ C1 * A ^ NN d n / (p : ℝ) ^ (2 * M) :=
    fun p M R hp hM hR A hA => deep_failure_count d n hd hn M p R hp hM hR A hA
  refine ⟨(2 * C1 + C2 + 1) / c0, div_pos (by linarith) hc0, ?_⟩
  intro M hM w hw hwAle
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hww : ∀ᶠ A in atTop, (M : ℝ) ^ (4 * M) ≤ w A :=
    (tendsto_atTop.mp hw) ((M : ℝ) ^ (4 * M))
  have hAA : ∀ᶠ A in atTop, (M : ℝ) ^ (4 * M) ≤ A := eventually_ge_atTop _
  filter_upwards [hwAle, hww, hAA, hc0low] with A hAle hwbig hAbig hPlow
  set W : ℝ := w A with hW
  have hWbig : (M : ℝ) ^ (4 * M) ≤ W := by rw [hW]; exact hwbig
  have hWleA : W ≤ A := by rw [hW]; exact hAle
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le (by positivity) hAbig
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le (by positivity) hWbig
  have hW0 : (0 : ℝ) ≤ W := le_of_lt hWpos
  have hceilM : M ^ (4 * M) ≤ Nat.ceil W := by
    have h1 : ((M ^ (4 * M) : ℕ) : ℝ) ≤ W := by
      rw [Nat.cast_pow]; exact hWbig
    exact_mod_cast (h1.trans (Nat.le_ceil W))
  have hp4M : ∀ p : ℕ, p.Prime → p ≤ M → 4 * M ≤ rOf p W := by
    intro p hp hpM
    refine rOf_ge_four_mul p M hp W (le_trans ?_ hceilM)
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpM) (4 * M)
  have hMW : (M : ℝ) ≤ W := by
    have h1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have h2 : (M : ℝ) ^ 1 ≤ (M : ℝ) ^ (4 * M) := pow_le_pow_right₀ h1 (by omega)
    exact le_trans (by simpa using h2) hWbig
  have hpMleW : ∀ p : ℕ, p.Prime → p ≤ M → (p : ℝ) ≤ W :=
    fun p _ hpM => le_trans (by exact_mod_cast hpM) hMW
  have hp4MleA : ∀ p : ℕ, p.Prime → p ≤ M → (p : ℝ) ^ (4 * M) ≤ A := by
    intro p _ hpM
    exact le_trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hpM) (4 * M)) hAbig
  have hfirst : ratio d n A (LocSet d n W) ≤ ratio d n A (SM d n M) := by
    apply ratio_mono'
    intro a ha
    exact ⟨ha.1, fun p hp hpM => primModZero_mono' (ha.2 p hp (hpMleW p hp hpM))
      (hp4M p hp hpM)⟩
  set ε : ℝ := (M : ℝ) / 4 ^ M + 1 / (M : ℝ) with hε
  have hεnn : 0 ≤ ε := by
    rw [hε]
    have h4 : (0 : ℝ) < (4 : ℝ) ^ M := pow_pos (by norm_num) M
    exact add_nonneg (div_nonneg (le_of_lt hMposR) (le_of_lt h4))
      (div_nonneg zero_le_one (le_of_lt hMposR))
  have hcore : ratio d n A (SM d n M) ≤
      ratio d n A (LocSet d n W) + (2 * C1 + C2 + 1) / c0 * ε := by
    rw [ratio, ratio]
    have hPpos : 0 < primCount d n A (fun _ => True) := by
      have h1 : 0 < c0 * A ^ (NN d n) := mul_pos hc0 (pow_pos hApos _)
      linarith
    have hcount : primCount d n A (SM d n M) ≤ primCount d n A (LocSet d n W) +
        (2 * C1 + C2) * A ^ (NN d n) * ε := by
      set S1 : Finset ℕ := (Finset.range (M + 1)).filter Nat.Prime with hS1
      set S2 : Finset ℕ := ((Finset.range (⌊W⌋₊ + 1)).filter Nat.Prime).filter
        (fun p => M < p) with hS2
      have hmemS1 : ∀ p : ℕ, p ∈ S1 ↔ p.Prime ∧ p ≤ M := by
        intro p
        rw [hS1]
        constructor
        · intro hp
          rw [Finset.mem_filter, Finset.mem_range] at hp
          exact ⟨hp.2, Nat.lt_succ_iff.mp hp.1⟩
        · rintro ⟨hp, hpM⟩
          rw [Finset.mem_filter, Finset.mem_range]
          exact ⟨Nat.lt_succ_iff.mpr hpM, hp⟩
      have hmemS2 : ∀ p : ℕ, p ∈ S2 ↔ p.Prime ∧ M < p ∧ p ≤ ⌊W⌋₊ := by
        intro p
        rw [hS2]
        constructor
        · intro hp
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hp
          exact ⟨hp.1.2, hp.2, Nat.lt_succ_iff.mp hp.1.1⟩
        · rintro ⟨hp, hMp, hpW⟩
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨Nat.lt_succ_iff.mpr hpW, hp⟩, hMp⟩
      have hstep1 : primCount d n A (SM d n M) ≤ primCount d n A (LocSet d n W) +
          primCount d n A (badC d n M W) := by
        have hsplit : primCount d n A (SM d n M) ≤ primCount d n A (LocSet d n W) +
            primCount d n A (fun a => SM d n M a ∧ ¬ LocSet d n W a) := by
          rw [primCount, primCount, primCount]
          have h1 : (primSet d n A (SM d n M)).ncard ≤
              (primSet d n A (LocSet d n W) ∪
                primSet d n A (fun a => SM d n M a ∧ ¬ LocSet d n W a)).ncard :=
            Set.ncard_le_ncard (fun a ha => by
              rw [primSet, Set.mem_ofPred_eq] at ha
              obtain ⟨hprim, hnorm, hsm⟩ := ha
              by_cases h : LocSet d n W a
              · exact Or.inl (by rw [primSet, Set.mem_ofPred_eq]; exact ⟨hprim, hnorm, h⟩)
              · exact Or.inr (by rw [primSet, Set.mem_ofPred_eq]; exact ⟨hprim, hnorm, hsm, h⟩))
              ((primSet_finite d n A (LocSet d n W)).union
                (primSet_finite d n A (fun a => SM d n M a ∧ ¬ LocSet d n W a)))
          have h2 := Set.ncard_union_le (primSet d n A (LocSet d n W))
            (primSet d n A (fun a => SM d n M a ∧ ¬ LocSet d n W a))
          exact_mod_cast (h1.trans h2)
        have hmono : primCount d n A (fun a => SM d n M a ∧ ¬ LocSet d n W a) ≤
            primCount d n A (badC d n M W) :=
          primCount_mono' A (fun a ha => ⟨ha.1.2, fun hloc => ha.2 ⟨ha.1.1, hloc⟩⟩)
        linarith
      have hnat : (primSet d n A (badC d n M W)).ncard ≤
          (∑ p ∈ S1, (primSet d n A (T1C d n M W p)).ncard) +
          (∑ p ∈ S2, (primSet d n A (T2C d n W p)).ncard) := by
        rw [Set.ncard_eq_toFinset_card (primSet d n A (badC d n M W)) (primSet_finite d n A _)]
        have hsub : (primSet_finite d n A (badC d n M W)).toFinset ⊆
            (S1.biUnion (fun p => (primSet_finite d n A (T1C d n M W p)).toFinset)) ∪
            (S2.biUnion (fun p => (primSet_finite d n A (T2C d n W p)).toFinset)) := by
          intro a ha
          rw [Set.Finite.mem_toFinset, primSet, Set.mem_ofPred_eq] at ha
          obtain ⟨hprim, hnorm, hbad⟩ := ha
          obtain ⟨hsm, hnotloc⟩ := hbad
          unfold locC at hnotloc
          push_neg at hnotloc
          obtain ⟨p, hpp, hpW, hpnot⟩ := hnotloc
          have hpfloor : p ≤ ⌊W⌋₊ := Nat.le_floor hpW
          by_cases hpM : p ≤ M
          · have h1 : p ∈ S1 := (hmemS1 p).mpr ⟨hpp, hpM⟩
            have h2 : a ∈ (primSet_finite d n A (T1C d n M W p)).toFinset := by
              rw [Set.Finite.mem_toFinset, primSet, Set.mem_ofPred_eq]
              exact ⟨hprim, hnorm, hsm p hpp hpM, hpnot⟩
            exact Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr (Exists.intro p (And.intro h1 h2))))
          · have h1 : p ∈ S2 := (hmemS2 p).mpr ⟨hpp, lt_of_not_ge hpM, hpfloor⟩
            have h2 : a ∈ (primSet_finite d n A (T2C d n W p)).toFinset := by
              rw [Set.Finite.mem_toFinset, primSet, Set.mem_ofPred_eq]
              exact ⟨hprim, hnorm, hpnot⟩
            exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr (Exists.intro p (And.intro h1 h2))))
        have hA1 : (S1.biUnion (fun p => (primSet_finite d n A (T1C d n M W p)).toFinset)).card ≤
            ∑ p ∈ S1, ((primSet_finite d n A (T1C d n M W p)).toFinset).card :=
          Finset.card_biUnion_le
        have hA2 : (S2.biUnion (fun p => (primSet_finite d n A (T2C d n W p)).toFinset)).card ≤
            ∑ p ∈ S2, ((primSet_finite d n A (T2C d n W p)).toFinset).card :=
          Finset.card_biUnion_le
        calc (primSet_finite d n A (badC d n M W)).toFinset.card
            ≤ ((S1.biUnion (fun p => (primSet_finite d n A (T1C d n M W p)).toFinset)) ∪
                (S2.biUnion (fun p => (primSet_finite d n A (T2C d n W p)).toFinset))).card :=
                Finset.card_le_card hsub
          _ ≤ (S1.biUnion (fun p => (primSet_finite d n A (T1C d n M W p)).toFinset)).card +
                (S2.biUnion (fun p => (primSet_finite d n A (T2C d n W p)).toFinset)).card :=
                Finset.card_union_le _ _
          _ ≤ (∑ p ∈ S1, ((primSet_finite d n A (T1C d n M W p)).toFinset).card) +
                (∑ p ∈ S2, ((primSet_finite d n A (T2C d n W p)).toFinset).card) :=
                add_le_add hA1 hA2
          _ = (∑ p ∈ S1, (primSet d n A (T1C d n M W p)).ncard) +
                (∑ p ∈ S2, (primSet d n A (T2C d n W p)).ncard) := by
              congr 1
              · apply Finset.sum_congr rfl
                intro p _
                exact (Set.ncard_eq_toFinset_card (primSet d n A (T1C d n M W p))
                  (primSet_finite d n A _)).symm
              · apply Finset.sum_congr rfl
                intro p _
                exact (Set.ncard_eq_toFinset_card (primSet d n A (T2C d n W p))
                  (primSet_finite d n A _)).symm
      have hstep2 : primCount d n A (badC d n M W) ≤
          (∑ p ∈ S1, primCount d n A (T1C d n M W p)) +
          (∑ p ∈ S2, primCount d n A (T2C d n W p)) := by
        have hcast : ((primSet d n A (badC d n M W)).ncard : ℝ) ≤
            (((∑ p ∈ S1, (primSet d n A (T1C d n M W p)).ncard) +
              (∑ p ∈ S2, (primSet d n A (T2C d n W p)).ncard) : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at hcast
        simpa only [primCount] using hcast
      have hS1b : (∑ p ∈ S1, primCount d n A (T1C d n M W p)) ≤
          C1 * A ^ (NN d n) * (2 * (M : ℝ) / (4 : ℝ) ^ M) := by
        have hterm : ∀ p ∈ S1, primCount d n A (T1C d n M W p) ≤
            C1 * A ^ (NN d n) / (p : ℝ) ^ (2 * M) := by
          intro p hp
          obtain ⟨hpp, hpM⟩ := (hmemS1 p).mp hp
          exact hD7 p M (rOf p W) hpp hM (hp4M p hpp hpM) A (hp4MleA p hpp hpM)
        calc (∑ p ∈ S1, primCount d n A (T1C d n M W p))
            ≤ ∑ p ∈ S1, C1 * A ^ (NN d n) / (p : ℝ) ^ (2 * M) := Finset.sum_le_sum hterm
          _ = C1 * A ^ (NN d n) * (∑ p ∈ S1, 1 / (p : ℝ) ^ (2 * M)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro p _; ring
          _ ≤ C1 * A ^ (NN d n) * (2 * (M : ℝ) / (4 : ℝ) ^ M) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (le_of_lt hC1) (pow_nonneg (le_of_lt hApos) _))
              refine sum_inv_pow_le' M S1 ?_ ?_
              · intro p hp; exact ((hmemS1 p).mp hp).1.two_le
              · have h1 : S1.card ≤ (Finset.range (M + 1)).card := by
                  rw [hS1]; exact Finset.card_le_card (Finset.filter_subset _ _)
                rw [Finset.card_range] at h1; omega
      have hS2b : (∑ p ∈ S2, primCount d n A (T2C d n W p)) ≤
          C2 * A ^ (NN d n) * (1 / (M : ℝ)) := by
        have hterm : ∀ p ∈ S2, primCount d n A (T2C d n W p) ≤
            C2 * A ^ (NN d n) / (p : ℝ) ^ (n - 1) := by
          intro p hp
          obtain ⟨hpp, hMp, hpfloor⟩ := (hmemS2 p).mp hp
          refine hD8 p (rOf p W) hpp ?_ A ?_
          · show 1 ≤ rOf p W
            rw [rOf]; omega
          · have h1 : (p : ℝ) ≤ (⌊W⌋₊ : ℝ) := by exact_mod_cast hpfloor
            have h2 : (⌊W⌋₊ : ℝ) ≤ W := Nat.floor_le hW0
            linarith
        calc (∑ p ∈ S2, primCount d n A (T2C d n W p))
            ≤ ∑ p ∈ S2, C2 * A ^ (NN d n) / (p : ℝ) ^ (n - 1) := Finset.sum_le_sum hterm
          _ = C2 * A ^ (NN d n) * (∑ p ∈ S2, 1 / (p : ℝ) ^ (n - 1)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl; intro p _; ring
          _ ≤ C2 * A ^ (NN d n) * (1 / (M : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_
                (mul_nonneg (le_of_lt hC2) (pow_nonneg (le_of_lt hApos) _))
              simpa only [hS2] using sum_primes_tail_le' M ⌊W⌋₊ n hM hn
      have hkey2 : C1 * A ^ (NN d n) * (2 * (M : ℝ) / (4 : ℝ) ^ M) +
            C2 * A ^ (NN d n) * (1 / (M : ℝ)) ≤ (2 * C1 + C2) * A ^ (NN d n) * ε := by
        rw [hε]
        have h4 : (0 : ℝ) < (4 : ℝ) ^ M := pow_pos (by norm_num) M
        have hAN : 0 ≤ A ^ (NN d n) := pow_nonneg (le_of_lt hApos) _
        have hC1' : 0 ≤ C1 := le_of_lt hC1
        have hC2' : 0 ≤ C2 := le_of_lt hC2
        have hv : 0 ≤ 1 / (M : ℝ) := div_nonneg zero_le_one (le_of_lt hMposR)
        have hu : 0 ≤ (M : ℝ) / (4 : ℝ) ^ M := div_nonneg (le_of_lt hMposR) (le_of_lt h4)
        have hP1 : 0 ≤ 2 * C1 * A ^ (NN d n) * (1 / (M : ℝ)) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC1') hAN) hv
        have hP2 : 0 ≤ C2 * A ^ (NN d n) * ((M : ℝ) / (4 : ℝ) ^ M) :=
          mul_nonneg (mul_nonneg hC2' hAN) hu
        have e : (2 * C1 + C2) * A ^ (NN d n) * ((M : ℝ) / (4 : ℝ) ^ M + 1 / (M : ℝ))
            = 2 * C1 * A ^ (NN d n) * ((M : ℝ) / (4 : ℝ) ^ M)
              + 2 * C1 * A ^ (NN d n) * (1 / (M : ℝ))
              + C2 * A ^ (NN d n) * ((M : ℝ) / (4 : ℝ) ^ M)
              + C2 * A ^ (NN d n) * (1 / (M : ℝ)) := by ring
        have e2 : C1 * A ^ (NN d n) * (2 * (M : ℝ) / (4 : ℝ) ^ M)
            = 2 * C1 * A ^ (NN d n) * ((M : ℝ) / (4 : ℝ) ^ M) := by ring
        rw [e, e2]
        linarith [hP1, hP2]
      calc primCount d n A (SM d n M)
          ≤ primCount d n A (LocSet d n W) + primCount d n A (badC d n M W) := hstep1
        _ ≤ primCount d n A (LocSet d n W) +
              ((∑ p ∈ S1, primCount d n A (T1C d n M W p)) +
               (∑ p ∈ S2, primCount d n A (T2C d n W p))) := by linarith [hstep2]
        _ ≤ primCount d n A (LocSet d n W) +
              (C1 * A ^ (NN d n) * (2 * (M : ℝ) / (4 : ℝ) ^ M) +
               C2 * A ^ (NN d n) * (1 / (M : ℝ))) := by linarith [hS1b, hS2b]
        _ ≤ primCount d n A (LocSet d n W) + (2 * C1 + C2) * A ^ (NN d n) * ε := by
              linarith [hkey2]
    have hc0A : 0 < c0 * A ^ (NN d n) := mul_pos hc0 (pow_pos hApos _)
    have hnn : 0 ≤ (2 * C1 + C2) * A ^ (NN d n) * ε :=
      mul_nonneg (mul_nonneg (by linarith) (pow_nonneg (le_of_lt hApos) _)) hεnn
    have hEP : (2 * C1 + C2) * A ^ (NN d n) * ε / primCount d n A (fun _ => True) ≤
        (2 * C1 + C2 + 1) / c0 * ε := by
      calc (2 * C1 + C2) * A ^ (NN d n) * ε / primCount d n A (fun _ => True)
          ≤ (2 * C1 + C2) * A ^ (NN d n) * ε / (c0 * A ^ (NN d n)) :=
            div_le_div_of_nonneg_left hnn hc0A hPlow
        _ = ((2 * C1 + C2) * ε) * A ^ (NN d n) / (c0 * A ^ (NN d n)) := by ring
        _ = (2 * C1 + C2) * ε / c0 := by
            rw [mul_div_mul_right _ _ (ne_of_gt (pow_pos hApos _))]
        _ = (2 * C1 + C2) / c0 * ε := by ring
        _ ≤ (2 * C1 + C2 + 1) / c0 * ε := by
            refine mul_le_mul_of_nonneg_right ?_ hεnn
            exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hc0)
    calc primCount d n A (SM d n M) / primCount d n A (fun _ => True)
        ≤ (primCount d n A (LocSet d n W) + (2 * C1 + C2) * A ^ (NN d n) * ε) /
            primCount d n A (fun _ => True) :=
          div_le_div_of_nonneg_right hcount (le_of_lt hPpos)
      _ = primCount d n A (LocSet d n W) / primCount d n A (fun _ => True) +
            (2 * C1 + C2) * A ^ (NN d n) * ε / primCount d n A (fun _ => True) := by ring
      _ ≤ primCount d n A (LocSet d n W) / primCount d n A (fun _ => True) +
            (2 * C1 + C2 + 1) / c0 * ε := by linarith [hEP]
  exact ⟨hfirst, hcore⟩

end

end Work.HP.DN
