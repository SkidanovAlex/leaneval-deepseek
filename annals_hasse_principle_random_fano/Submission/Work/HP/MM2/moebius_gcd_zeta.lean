import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.moebiusZetaTail
import Submission.Work.HP.w_arith

noncomputable section

/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `moebius_gcd_zeta` in namespace Work.HP.MM2; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.MM2.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.MM2.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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

/-! ## Arithmetic input: for `ℓ ≤ w`, `ℓ` divides `W = bigW w` -/

/-- `rad(W)` divides `W`. -/
private lemma radW_dvd_bigW (w : ℝ) : radW w ∣ bigW w := by
  rw [radW, bigW]
  refine Finset.prod_dvd_prod_of_dvd _ _ (fun p _ => ?_)
  exact dvd_pow_self p (by rw [rOf]; exact Nat.succ_ne_zero _)

/-- Every `m ≥ 1` with `m ≤ w` divides `W = bigW w`. -/
private lemma dvd_bigW_of_le (w : ℝ) (hw : 1 ≤ w) {m : ℕ} (hm : 1 ≤ m) (hmw : (m : ℝ) ≤ w) :
    m ∣ bigW w := by
  have hdiv : m ∣ bigW w / radW w :=
    (Work.HP.w_arith 3 (by norm_num)).1 w (by linarith) m hm hmw
  have h2 : m ∣ radW w * (bigW w / radW w) := dvd_mul_of_dvd_right hdiv (radW w)
  rwa [Nat.mul_div_cancel' (radW_dvd_bigW w)] at h2

/-! ## The two summands -/

/-- The summand of `moebius_gcd_zeta`: `μ(ℓ) · gcd(ℓ,W)^k / ℓ^{s+k}`. -/
private def mob (s k : ℕ) (W ℓ : ℕ) : ℝ :=
  (ArithmeticFunction.moebius ℓ : ℝ) * ((Nat.gcd ℓ W : ℕ) : ℝ) ^ k / (ℓ : ℝ) ^ (s + k)

/-- The corresponding Möbius summand `μ(ℓ)/ℓ^s`. -/
private def mobz (s : ℕ) (ℓ : ℕ) : ℝ := (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s

/-- For `1 ≤ ℓ ≤ w` the twisted summand agrees with `μ(ℓ)/ℓ^s`. -/
private lemma mob_eq_mobz (s k : ℕ) {w : ℝ} (hw : 1 ≤ w) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓw : (ℓ : ℝ) ≤ w) : mob s k (bigW w) ℓ = mobz s ℓ := by
  have h := dvd_bigW_of_le w hw hℓ hℓw
  show (ArithmeticFunction.moebius ℓ : ℝ) * ((Nat.gcd ℓ (bigW w) : ℕ) : ℝ) ^ k /
      (ℓ : ℝ) ^ (s + k) = (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s
  rw [Nat.gcd_eq_left h, pow_add]
  have hℓ0 : (ℓ : ℝ) ≠ 0 := by positivity
  field_simp

/-- Each twisted summand is bounded by `1/ℓ^s` in absolute value. -/
private lemma abs_mob_le (s k : ℕ) (W ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    |mob s k W ℓ| ≤ 1 / (ℓ : ℝ) ^ s := by
  show |(ArithmeticFunction.moebius ℓ : ℝ) * ((Nat.gcd ℓ W : ℕ) : ℝ) ^ k /
      (ℓ : ℝ) ^ (s + k)| ≤ 1 / (ℓ : ℝ) ^ s
  have hμ : |(ArithmeticFunction.moebius ℓ : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast (Nat.zero_le ℓ)
  have hg0 : (0 : ℝ) ≤ ((Nat.gcd ℓ W : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hg : ((Nat.gcd ℓ W : ℕ) : ℝ) ≤ (ℓ : ℝ) := by
    exact_mod_cast Nat.gcd_le_left W (by omega : 0 < ℓ)
  have hℓne : (ℓ : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    linarith
  rw [abs_div, abs_mul, abs_of_nonneg (pow_nonneg hg0 k),
    abs_of_nonneg (pow_nonneg hℓ0 (s + k))]
  calc |(ArithmeticFunction.moebius ℓ : ℝ)| * ((Nat.gcd ℓ W : ℕ) : ℝ) ^ k / (ℓ : ℝ) ^ (s + k)
      ≤ 1 * (ℓ : ℝ) ^ k / (ℓ : ℝ) ^ (s + k) := by
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul hμ (pow_le_pow_left₀ hg0 hg k) (by positivity) (by norm_num)
    _ = 1 / (ℓ : ℝ) ^ s := by
        rw [one_mul, pow_add]
        field_simp

/-! ## Splitting an `Icc`-sum at `M` -/

private lemma sum_Icc_split {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    (∑ ℓ ∈ Finset.Icc 1 N, f ℓ) = (∑ ℓ ∈ Finset.Icc 1 M, f ℓ) +
      ∑ ℓ ∈ Finset.Icc (M + 1) N, f ℓ := by
  rw [← Finset.Ico_succ_right_eq_Icc (1 : ℕ) N, ← Finset.Ico_succ_right_eq_Icc (1 : ℕ) M,
    ← Finset.Ico_succ_right_eq_Icc (M + 1) N]
  change (∑ ℓ ∈ Finset.Ico 1 (N + 1), f ℓ) =
    (∑ ℓ ∈ Finset.Ico 1 (M + 1), f ℓ) + ∑ ℓ ∈ Finset.Ico (M + 1) (N + 1), f ℓ
  rw [← Finset.Ico_union_Ico_eq_Ico (a := 1) (b := M + 1) (c := N + 1) (by omega) (by omega)]
  rw [Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Ico] at hx hx'
  omega

/-! ## The `p`-series tail -/

private lemma tail_bound (s : ℕ) (hs : 2 ≤ s) (M N : ℕ) (hM : 1 ≤ M) :
    (∑ ℓ ∈ Finset.Icc (M + 1) N, (1 : ℝ) / (ℓ : ℝ) ^ s) ≤
      (M : ℝ) ^ (1 - (s : ℝ)) / ((s : ℝ) - 1) := by
  have hs' : (1 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 1 < s)
  have hsum : Summable (fun j : ℕ => 1 / (((j + M + 1 : ℕ)) : ℝ) ^ ((s : ℝ))) := by
    have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ ((s : ℝ))) :=
      Real.summable_one_div_nat_rpow.mpr hs'
    have h1 := (summable_nat_add_iff (M + 1)).mpr h0
    refine h1.congr (fun n => ?_)
    have hc : ((n + (M + 1) : ℕ) : ℝ) = ((n + M + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hc]
  calc (∑ ℓ ∈ Finset.Icc (M + 1) N, (1 : ℝ) / (ℓ : ℝ) ^ s)
      = ∑ ℓ ∈ Finset.Icc (M + 1) N, (1 : ℝ) / (ℓ : ℝ) ^ ((s : ℝ)) :=
        Finset.sum_congr rfl (fun ℓ _ => by rw [Real.rpow_natCast])
    _ = ∑ k ∈ Finset.range (N - M), 1 / (((k + M + 1 : ℕ)) : ℝ) ^ ((s : ℝ)) := by
        rw [← Finset.Ico_succ_right_eq_Icc (M + 1) N, Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr ?_ (fun k _ => ?_)
        · simp
        · have hc : ((M + 1) + k : ℕ) = ((k + M + 1 : ℕ)) := by omega
          rw [hc]
    _ ≤ ∑' j : ℕ, 1 / (((j + M + 1 : ℕ)) : ℝ) ^ ((s : ℝ)) :=
        Summable.sum_le_tsum _ (fun i _ => by positivity) hsum
    _ ≤ (M : ℝ) ^ (1 - (s : ℝ)) / ((s : ℝ) - 1) :=
        Work.HP.MDEstimates.pSeries_tail_tsum_le _ hs' M hM

/-! ## The main lemma -/

/-- (L0g) Möbius sum twisted by `gcd(ℓ, W)^k`: for `ℓ ≤ w`, `ℓ ∣ W` (`w_arith`), so the sum
agrees with `Σ μ(ℓ)/ℓ^s` up to `min(L,w)`; then `moebiusZetaTail`. -/
theorem moebius_gcd_zeta (s k : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ w L : ℝ, 1 ≤ w → 1 ≤ L →
      |(∑ ℓ ∈ Finset.Icc 1 ⌊L⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) *
          ((Nat.gcd ℓ (bigW w) : ℕ) : ℝ) ^ k / (ℓ : ℝ) ^ (s + k)) - 1 / zetaR s|
        ≤ C / (min L w) ^ (s - 1) := by
  have hs1 : 1 ≤ s := by omega
  have hslt : (1 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 1 < s)
  have hspos : (0 : ℝ) < (s : ℝ) - 1 := by linarith
  obtain ⟨C1, hC1pos, hC1⟩ := Work.HP.moebiusZetaTail (s : ℝ) hslt
  refine ⟨2 ^ (s - 1) * (C1 + 1 / ((s : ℝ) - 1)), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 ^ (s - 1) := pow_pos (by norm_num) _
    have h3 : (0 : ℝ) < 1 / ((s : ℝ) - 1) := one_div_pos.mpr hspos
    exact mul_pos h1 (by linarith)
  · intro w L hw hL
    change |(∑ ℓ ∈ Finset.Icc 1 ⌊L⌋₊, mob s k (bigW w) ℓ) - 1 / zetaR s|
        ≤ (2 ^ (s - 1) * (C1 + 1 / ((s : ℝ) - 1))) / (min L w) ^ (s - 1)
    set n : ℕ := s - 1 with hndef
    have hexp : ((s : ℝ) - 1) = (n : ℝ) := by
      rw [hndef]
      have h : (((s - 1 : ℕ)) : ℝ) = (s : ℝ) - 1 := by
        rw [Nat.cast_sub (R := ℝ) hs1, Nat.cast_one]
      exact h.symm
    set x : ℝ := min L w with hxdef
    have hx1 : 1 ≤ x := by rw [hxdef]; exact le_min hL hw
    have hxpos : 0 < x := by linarith
    have hM1 : 1 ≤ ⌊x⌋₊ := by
      refine Nat.le_floor ?_
      push_cast
      exact hx1
    have hMpos : (0 : ℝ) < (((⌊x⌋₊ : ℕ)) : ℝ) := by
      have : (1 : ℝ) ≤ (((⌊x⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hM1
      linarith
    have hMx : (((⌊x⌋₊ : ℕ)) : ℝ) ≤ x := Nat.floor_le (le_of_lt hxpos)
    have hMw : (((⌊x⌋₊ : ℕ)) : ℝ) ≤ w := by
      rw [hxdef] at hMx ⊢
      exact le_trans hMx (min_le_right L w)
    have hMN : ⌊x⌋₊ ≤ ⌊L⌋₊ := by
      rw [hxdef]
      exact Nat.floor_le_floor (min_le_left L w)
    have hfloor : x / 2 ≤ (((⌊x⌋₊ : ℕ)) : ℝ) := by
      by_cases h2 : (2 : ℝ) ≤ x
      · have h3 : x - 1 < (((⌊x⌋₊ : ℕ)) : ℝ) := by
          have := Nat.lt_floor_add_one x
          linarith
        linarith
      · have h4 : x < 2 := not_le.mp h2
        have h5 : (1 : ℝ) ≤ (((⌊x⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hM1
        linarith
    -- the Möbius/zeta tail at `X = x`
    have hz : (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ ((s : ℝ))) = zetaR s := by
      show (∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ ((s : ℝ))) =
        ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ s
      exact tsum_congr (fun i => by rw [Real.rpow_natCast])
    have hxpow : x ^ ((s : ℝ) - 1) = x ^ n := by rw [hexp, Real.rpow_natCast]
    have hA : |(∑ ℓ ∈ Finset.Icc 1 ⌊x⌋₊, mobz s ℓ) - 1 / zetaR s| ≤ C1 / x ^ n := by
      have hsum : (∑ ℓ ∈ Finset.Icc 1 ⌊x⌋₊, mobz s ℓ) =
          ∑ ℓ ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ ((s : ℝ)) := by
        refine Finset.sum_congr rfl (fun ℓ _ => ?_)
        show (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s =
          (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ ((s : ℝ))
        rw [Real.rpow_natCast]
      have h := hC1 x hx1
      rw [hxpow, hz] at h
      rw [hsum]
      exact h
    -- the tail beyond `⌊x⌋₊`
    have hT : |∑ ℓ ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊L⌋₊, mob s k (bigW w) ℓ|
        ≤ (1 / ((s : ℝ) - 1)) / (((⌊x⌋₊ : ℕ)) : ℝ) ^ n := by
      have h1 : |∑ ℓ ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊L⌋₊, mob s k (bigW w) ℓ|
          ≤ ∑ ℓ ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊L⌋₊, (1 : ℝ) / (ℓ : ℝ) ^ s := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun ℓ hℓ => ?_))
        rw [Finset.mem_Icc] at hℓ
        exact abs_mob_le s k (bigW w) ℓ (by omega)
      have h2 : (∑ ℓ ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊L⌋₊, (1 : ℝ) / (ℓ : ℝ) ^ s)
          ≤ (((⌊x⌋₊ : ℕ)) : ℝ) ^ (1 - (s : ℝ)) / ((s : ℝ) - 1) :=
        tail_bound s hs ⌊x⌋₊ ⌊L⌋₊ hM1
      have h3 : (((⌊x⌋₊ : ℕ)) : ℝ) ^ (1 - (s : ℝ)) / ((s : ℝ) - 1)
          = (1 / ((s : ℝ) - 1)) / (((⌊x⌋₊ : ℕ)) : ℝ) ^ n := by
        rw [show (1 : ℝ) - (s : ℝ) = -(((s : ℝ) - 1)) by ring,
          Real.rpow_neg (le_of_lt hMpos), hexp, Real.rpow_natCast]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      exact le_trans h1 (le_trans h2 (le_of_eq h3))
    -- pointwise agreement on `Icc 1 ⌊x⌋₊`
    have hpt : ∀ ℓ ∈ Finset.Icc 1 ⌊x⌋₊, mob s k (bigW w) ℓ = mobz s ℓ := by
      intro ℓ hℓ
      rw [Finset.mem_Icc] at hℓ
      have hℓM : (ℓ : ℝ) ≤ (((⌊x⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hℓ.2
      exact mob_eq_mobz s k hw hℓ.1 (le_trans hℓM hMw)
    have hsplit := sum_Icc_split hMN (mob s k (bigW w))
    have hS : (∑ ℓ ∈ Finset.Icc 1 ⌊L⌋₊, mob s k (bigW w) ℓ) - 1 / zetaR s
        = ((∑ ℓ ∈ Finset.Icc 1 ⌊x⌋₊, mobz s ℓ) - 1 / zetaR s)
          + (∑ ℓ ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊L⌋₊, mob s k (bigW w) ℓ) := by
      rw [hsplit, Finset.sum_congr rfl hpt]
      ring
    have hmain : |(∑ ℓ ∈ Finset.Icc 1 ⌊L⌋₊, mob s k (bigW w) ℓ) - 1 / zetaR s|
        ≤ (2 ^ n * (C1 + 1 / ((s : ℝ) - 1))) / (min L w) ^ n := by
      rw [hS]
      refine le_trans (abs_add_le _ _) (le_trans (add_le_add hA hT) ?_)
      have hxnp : (0 : ℝ) < x ^ n := pow_pos hxpos n
      have hle1 : x ^ n / 2 ^ n ≤ (((⌊x⌋₊ : ℕ)) : ℝ) ^ n := by
        have h0 : (x / 2) ^ n ≤ (((⌊x⌋₊ : ℕ)) : ℝ) ^ n :=
          pow_le_pow_left₀ (by positivity) hfloor n
        rwa [div_pow] at h0
      have hC : C1 / x ^ n ≤ 2 ^ n * C1 / x ^ n := by
        have h2 : C1 * 1 ≤ C1 * 2 ^ n :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
            (le_of_lt hC1pos)
        have h3 : C1 / x ^ n ≤ C1 * 2 ^ n / x ^ n := by
          simpa using div_le_div_of_nonneg_right h2 (le_of_lt hxnp)
        have h4 : C1 * 2 ^ n / x ^ n = 2 ^ n * C1 / x ^ n := by
          rw [mul_comm C1 (2 ^ n)]
        exact le_trans h3 (le_of_eq h4)
      have hT' : (1 / ((s : ℝ) - 1)) / (((⌊x⌋₊ : ℕ)) : ℝ) ^ n
          ≤ 2 ^ n * (1 / ((s : ℝ) - 1)) / x ^ n := by
        have h1 : (1 / ((s : ℝ) - 1)) / (((⌊x⌋₊ : ℕ)) : ℝ) ^ n
            ≤ (1 / ((s : ℝ) - 1)) / (x ^ n / 2 ^ n) :=
          div_le_div_of_nonneg_left (le_of_lt (one_div_pos.mpr hspos))
            (by positivity) hle1
        have h2 : (1 / ((s : ℝ) - 1)) / (x ^ n / 2 ^ n)
            = 2 ^ n * (1 / ((s : ℝ) - 1)) / x ^ n := by
          have hs0 : ((s : ℝ) - 1) ≠ 0 := ne_of_gt hspos
          have hx0 : x ^ n ≠ 0 := ne_of_gt hxnp
          have h20 : (2 : ℝ) ^ n ≠ 0 := by positivity
          field_simp
        exact le_trans h1 (le_of_eq h2)
      refine le_trans (add_le_add hC hT') ?_
      rw [hxdef]
      rw [← add_div]
      refine div_le_div_of_nonneg_right (le_of_eq ?_) (pow_nonneg (le_of_lt hxpos) n)
      ring
    exact hmain

end Work.HP.MM2
