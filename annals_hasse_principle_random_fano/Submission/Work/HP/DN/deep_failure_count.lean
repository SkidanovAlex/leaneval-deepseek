import Mathlib
import Submission.Work.HP.DN.Defs
import Submission.Work.HP.density_aux
import Submission.Work.HP.primCount_residue_le
import Submission.Work.HP.NA.card_Rset_le
import Submission.Work.HP.lift.hensel_lift
import Submission.Work.HP.NA.primCount_le_fiber

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-! Guidance from the project lead (the requester):

LEAD NOTES (Hasse design review hasse2, 2026-09-27). Your node is `deep_failure_count` in namespace Work.HP.DN; find it in DESIGN_REVIEW.md below (§1 is the moment_mix_loc pair route in MM2, §2 the density route in DN). Definitions: Submission.Work.HP.DN.Defs (lead-placed, do not edit). All MM2/DN nodes are dispatched in parallel as Submission.Work.HP.DN.<name>. IMPORT siblings and proved workspace lemmas (FM3.ell_two_count_free, EE.ellXY_two_pub, hensel_lift, card_Rset_le, card_badCls_le, …); never reprove them or restate them under another name. The numaux/Vero/WedgeDefs import clashes were fixed by the lead at 22:0x. If you believe your statement is false, give a concrete counterexample.

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

/-! ## Auxiliary lemmas for the deep-failure count -/

/-- `NA.fev` and `formEval` agree on integer vectors. -/
private lemma fev_eq_formEval (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    NA.fev d n a x = formEval d n a x := rfl

/-- `NA.dfev` and `pderivEval` agree on integer vectors. -/
private lemma dfev_eq_pderivEval (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) : NA.dfev d n a x i = pderivEval d n a i x := by
  unfold NA.dfev pderivEval
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hprod : (∏ j : Fin (n + 1),
        x j ^ (if j = i then ((m.1 j : ℕ) - 1) else (m.1 j : ℕ)))
      = ∏ j : Fin (n + 1),
        x j ^ (((m.1 j : ℕ)) - if j = i then 1 else 0) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [hprod]

/-- In `ZMod (p^r)` with `k ≤ r`, divisibility of the reduction of an integer is the same as
`p`-adic divisibility of that integer. -/
private lemma dvd_iff_vpDvd (p r k : ℕ) (hp : p.Prime) (hk : k ≤ r) (z : ℤ) :
    NA.vpDvd p r k (z : ZMod (p ^ r)) ↔ (p : ℤ) ^ k ∣ z := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  constructor
  · rintro ⟨c, hc⟩
    have hcv : (((c.val : ℕ)) : ZMod (p ^ r)) = c := ZMod.natCast_zmod_val c
    rw [← hcv] at hc
    have hcast : (z : ZMod (p ^ r))
        = ((((p : ℤ) ^ k * (c.val : ℤ)) : ℤ) : ZMod (p ^ r)) := by
      rw [hc]; push_cast; ring
    have hdvd : (p : ℤ) ^ r ∣ (p : ℤ) ^ k * (c.val : ℤ) - z := by
      have hmod := (ZMod.intCast_eq_intCast_iff z ((p : ℤ) ^ k * (c.val : ℤ)) (p ^ r)).mp hcast
      simpa [Nat.cast_pow] using Int.modEq_iff_dvd.mp hmod
    have h1 : (p : ℤ) ^ k ∣ (p : ℤ) ^ r := pow_dvd_pow (p : ℤ) hk
    have h2 : (p : ℤ) ^ k ∣ (p : ℤ) ^ k * (c.val : ℤ) := dvd_mul_right _ _
    have h4 : (p : ℤ) ^ k
        ∣ ((p : ℤ) ^ k * (c.val : ℤ)) - (((p : ℤ) ^ k * (c.val : ℤ)) - z) :=
      dvd_sub h2 (dvd_trans h1 hdvd)
    have h5 : ((p : ℤ) ^ k * (c.val : ℤ)) - (((p : ℤ) ^ k * (c.val : ℤ)) - z) = z := by ring
    rwa [h5] at h4
  · rintro ⟨c, hc⟩
    refine ⟨(c : ZMod (p ^ r)), ?_⟩
    rw [hc]; push_cast; ring

/-- An integer not divisible by the prime `p` is a unit modulo `p^r` (`r ≥ 1`). -/
private lemma isUnit_intCast_of_not_dvd {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) {z : ℤ}
    (hz : ¬ (p : ℤ) ∣ z) : IsUnit ((z : ℤ) : ZMod (p ^ r)) := by
  have hnot : ¬ p ∣ z.natAbs := by
    intro hd
    obtain ⟨c, hc⟩ := hd
    have hcases : (((z.natAbs : ℕ)) : ℤ) = z ∨ (((z.natAbs : ℕ)) : ℤ) = -z := by
      rcases le_total 0 z with h | h
      · exact Or.inl (Int.natAbs_of_nonneg h)
      · exact Or.inr (Int.ofNat_natAbs_of_nonpos h)
    rcases hcases with h | h
    · exact hz ⟨(c : ℤ), by rw [← h, hc]; push_cast; ring⟩
    · refine hz ⟨-(c : ℤ), ?_⟩
      have hh : -z = (p : ℤ) * (c : ℤ) := by rw [← h, hc]; push_cast; ring
      rw [← neg_neg z, hh]; ring
  have h1 : IsUnit (((z.natAbs : ℕ)) : ZMod (p ^ r)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)).mpr hnot
  have h2 : (((z.natAbs : ℕ)) : ZMod (p ^ r)) = (z : ZMod (p ^ r))
      ∨ (((z.natAbs : ℕ)) : ZMod (p ^ r)) = -(z : ZMod (p ^ r)) := by
    rcases le_total 0 z with h | h
    · exact Or.inl (by rw [← Int.cast_natCast, Int.natAbs_of_nonneg h])
    · exact Or.inr (by rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos h]; simp)
  rcases h2 with h2 | h2
  · rwa [h2] at h1
  · rw [h2] at h1
    exact (IsUnit.neg_iff ((z : ℤ) : ZMod (p ^ r))).mp h1

/-- A primitive integer vector has a primitive reduction modulo `p^r`, `p` prime, `r ≥ 1`. -/
private lemma isPrimGen_intCast {d n p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r)
    (a : Mon d n → ℤ) (ha : IsPrim a) :
    NA.IsPrimGen (p ^ r) (fun m => (a m : ZMod (p ^ r))) := by
  obtain ⟨m, hm⟩ : ∃ m, ¬ (p : ℤ) ∣ a m := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
      rw [← ha]
      exact Finset.dvd_gcd (fun b _ => h b)
    obtain ⟨c, hc⟩ := hp1
    have h2 : p ∣ 1 := by
      have h3 : (1 : ℤ).natAbs = ((p : ℤ) * c).natAbs := by rw [hc]
      simp only [Int.natAbs_one, Int.natAbs_mul, Int.natAbs_natCast] at h3
      exact ⟨c.natAbs, h3⟩
    exact hp.not_dvd_one h2
  exact (NA.isPrimGen_iff_exists_isUnit hp hr _).mpr
    ⟨m, isUnit_intCast_of_not_dvd hp hr hm⟩

/-- Geometric bound: `∑_{j=0}^{J} p^{K-j} ≤ 2 p^K` for `p ≥ 2`, `J ≤ K`. -/
private lemma sum_pow_sub_le (p K J : ℕ) (hp : 2 ≤ p) (hJK : J ≤ K) :
    (∑ j ∈ Finset.range (J+1), p^(K-j)) ≤ 2 * p^K := by
  have key : ∀ J, J ≤ K → (∑ j ∈ Finset.range (J+1), p^(K-j)) + p^(K-J) ≤ 2 * p^K := by
    intro J
    induction J with
    | zero =>
      intro _
      have h0 : (∑ j ∈ Finset.range (0+1), p^(K-j)) = p^K := by
        rw [Finset.sum_range_succ]; simp
      rw [h0, Nat.sub_zero]
      omega
    | succ J ih =>
      intro hJK
      have hJ : J ≤ K := by omega
      have ih' := ih hJ
      have hb : p^(K-(J+1)) * 2 ≤ p^(K-J) := by
        rw [show K - J = K - (J+1) + 1 by omega, pow_succ]
        exact Nat.mul_le_mul_left _ hp
      have hstep : (∑ j ∈ Finset.range (Nat.succ J + 1), p^(K-j)) + p^(K-Nat.succ J)
          = (∑ j ∈ Finset.range (J+1), p^(K-j)) + p^(K-(J+1)) + p^(K-(J+1)) := by
        rw [show Nat.succ J = J+1 from rfl, Finset.sum_range_succ]
      rw [hstep]
      calc (∑ j ∈ Finset.range (J+1), p^(K-j)) + p^(K-(J+1)) + p^(K-(J+1))
          ≤ (∑ j ∈ Finset.range (J+1), p^(K-j)) + p^(K-J) := by omega
        _ ≤ 2 * p^K := ih'
  have := key J hJK
  omega

/-- The number of classes modulo `p^{4M}` lying in the union of the `Rset`-classes with
`2M ≤ e ≤ 4M` is at most `4 p^{4MN-2M}`. -/
private lemma card_le_Rset_classes (d n M p : ℕ) (hd : 1 ≤ d) (hp : Nat.Prime p) (hM : 1 ≤ M)
    (T : Finset (Mon d n → ZMod (p ^ (4 * M))))
    (hT : ∀ b ∈ T, ∃ e ∈ Finset.Icc (2 * M) (4 * M), NA.Rset d n p (4 * M) e b) :
    T.card ≤ 4 * p ^ (4 * M * NN d n - 2 * M) := by
  classical
  haveI : NeZero (p ^ (4 * M)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hN1 : 1 ≤ NN d n := by
    have := NA.succ_le_NN d n hd
    omega
  have hsub : T ⊆ (Finset.range (2*M+1)).biUnion
      (fun j => Finset.univ.filter (fun b => NA.Rset d n p (4*M) (2*M+j) b)) := by
    intro b hb
    obtain ⟨e, he, hRe⟩ := hT b hb
    rw [Finset.mem_Icc] at he
    refine Finset.mem_biUnion.mpr ⟨e - 2*M, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have heq : 2 * M + (e - 2 * M) = e := by omega
    rw [heq]
    exact hRe
  calc T.card
      ≤ ((Finset.range (2*M+1)).biUnion
          (fun j => Finset.univ.filter (fun b => NA.Rset d n p (4*M) (2*M+j) b))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (2*M+1),
          (Finset.univ.filter (fun b => NA.Rset d n p (4*M) (2*M+j) b)).card :=
        Finset.card_biUnion_le
    _ = ∑ j ∈ Finset.range (2*M+1),
          Nat.card {b : Mon d n → ZMod (p^(4*M)) // NA.Rset d n p (4*M) (2*M+j) b} := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [NA.natCard_eq_filter_card]
    _ ≤ ∑ j ∈ Finset.range (2*M+1), 2 * p ^ (4*M * NN d n - (2*M+j)) := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        exact NA.card_Rset_le d n p (4*M) (2*M+j) (by omega) hp (by omega) (by omega) (by omega)
    _ = 2 * (∑ j ∈ Finset.range (2*M+1), p ^ ((4*M * NN d n - 2*M) - j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        rw [show 4*M * NN d n - (2*M+j) = (4*M * NN d n - 2*M) - j by omega]
    _ ≤ 2 * (2 * p ^ (4*M * NN d n - 2*M)) := by
        apply Nat.mul_le_mul_left
        refine sum_pow_sub_le p (4*M * NN d n - 2*M) (2*M) hp2 ?_
        have hMNN : M ≤ M * NN d n := by
          calc M = M * 1 := (mul_one M).symm
            _ ≤ M * NN d n := Nat.mul_le_mul_left M hN1
        have h4 : 4 * M ≤ 4 * M * NN d n := by
          calc 4 * M ≤ 4 * (M * NN d n) := Nat.mul_le_mul_left 4 hMNN
            _ = 4 * M * NN d n := by ring
        omega
    _ = 4 * p ^ (4*M * NN d n - 2*M) := by ring

/-- The real arithmetic bound: `T.card ≤ 4p^{4MN-2M}` and `p^{4M} ≤ A` give
`T.card · (2A/p^{4M}+1)^N ≤ 4·3^N A^N / p^{2M}`. -/
private lemma classes_mul_le (d n M p : ℕ) (hd : 2 ≤ d) (hp : p.Prime) (hM : 1 ≤ M) (A : ℝ)
    (hA : (p : ℝ) ^ (4 * M) ≤ A) :
    (4 * (p : ℝ) ^ (4 * M * NN d n - 2 * M)) * (2 * A / (p : ℝ) ^ (4 * M) + 1) ^ NN d n
      ≤ 4 * 3 ^ NN d n * A ^ NN d n / (p : ℝ) ^ (2 * M) := by
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hQ0 : (0 : ℝ) < (p : ℝ) ^ (4 * M) := by positivity
  have hQne : (p : ℝ) ^ (4 * M) ≠ 0 := ne_of_gt hQ0
  have hA0 : (0 : ℝ) ≤ A := le_trans (pow_nonneg hpnn (4 * M)) hA
  have hbase0 : (0 : ℝ) ≤ 2 * A / (p : ℝ) ^ (4 * M) + 1 := by
    have h : (0 : ℝ) ≤ 2 * A / (p : ℝ) ^ (4 * M) :=
      div_nonneg (by linarith) (pow_nonneg hpnn _)
    linarith
  have hfour : (0 : ℝ) ≤ 4 * (p : ℝ) ^ (4 * M * NN d n - 2 * M) :=
    mul_nonneg (by norm_num) (pow_nonneg hpnn _)
  have hAle : (1 : ℝ) ≤ A / (p : ℝ) ^ (4 * M) := by
    rw [le_div_iff₀ hQ0]
    simpa using hA
  have hbase : 2 * A / (p : ℝ) ^ (4 * M) + 1 ≤ 3 * A / (p : ℝ) ^ (4 * M) := by
    have h1 : 2 * A / (p : ℝ) ^ (4 * M) = 2 * (A / (p : ℝ) ^ (4 * M)) := by ring
    have h2 : 3 * A / (p : ℝ) ^ (4 * M) = 3 * (A / (p : ℝ) ^ (4 * M)) := by ring
    rw [h1, h2]; nlinarith
  have hN1 : 1 ≤ NN d n := by
    have := NA.succ_le_NN d n (by omega : 1 ≤ d)
    omega
  have hMNN : M ≤ M * NN d n := by
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * NN d n := Nat.mul_le_mul_left M hN1
  have hexp : 4 * M * NN d n - 2 * M + 2 * M = 4 * M * NN d n := by
    apply Nat.sub_add_cancel
    calc 2 * M ≤ 4 * M := by omega
      _ ≤ 4 * (M * NN d n) := Nat.mul_le_mul_left 4 hMNN
      _ = 4 * M * NN d n := by ring
  have hkey : (p : ℝ) ^ (4 * M * NN d n - 2 * M) / (p : ℝ) ^ (4 * M * NN d n)
      = 1 / (p : ℝ) ^ (2 * M) := by
    rw [div_eq_div_iff (pow_ne_zero _ (ne_of_gt hp0)) (pow_ne_zero _ (ne_of_gt hp0))]
    rw [show (p : ℝ) ^ (4 * M * NN d n - 2 * M) * (p : ℝ) ^ (2 * M)
        = (p : ℝ) ^ (4 * M * NN d n - 2 * M + 2 * M) from (pow_add _ _ _).symm, hexp]
    ring
  calc (4 * (p : ℝ) ^ (4 * M * NN d n - 2 * M)) * (2 * A / (p : ℝ) ^ (4 * M) + 1) ^ NN d n
      ≤ (4 * (p : ℝ) ^ (4 * M * NN d n - 2 * M)) * (3 * A / (p : ℝ) ^ (4 * M)) ^ NN d n := by
        apply mul_le_mul_of_nonneg_left _ hfour
        exact pow_le_pow_left₀ hbase0 hbase (NN d n)
    _ = 4 * 3 ^ NN d n * A ^ NN d n / (p : ℝ) ^ (2 * M) := by
        rw [div_pow, mul_pow, ← pow_mul]
        rw [show (4 * (p : ℝ) ^ (4 * M * NN d n - 2 * M))
              * (3 ^ NN d n * A ^ NN d n / (p : ℝ) ^ (4 * M * NN d n))
            = 4 * 3 ^ NN d n * A ^ NN d n
              * ((p : ℝ) ^ (4 * M * NN d n - 2 * M) / (p : ℝ) ^ (4 * M * NN d n))
            from by ring]
        rw [hkey]
        ring

/-- Deep failures: a primitive vector with a primitive zero mod `p^{4M}` which does not lift to
`p^R` has gradient valuation `e ≥ 2M`, so its class mod `p^{4M}` lies in `Rset e` for some
`e ∈ [2M, 4M]`. -/
private lemma deep_failure_Rset (d n M p R : ℕ) (hp : p.Prime) (hM : 1 ≤ M) (hR : 4 * M ≤ R)
    (a : Mon d n → ℤ) (hprim : IsPrim a)
    (h1 : PrimModZero d n a p (4 * M)) (h2 : ¬ PrimModZero d n a p R) :
    ∃ e ∈ Finset.Icc (2 * M) (4 * M),
      NA.Rset d n p (4 * M) e (fun m => (a m : ZMod (p ^ (4 * M)))) := by
  classical
  have hr1 : 1 ≤ 4 * M := by omega
  obtain ⟨x, hxprim, hxzero⟩ := h1
  let b : Mon d n → ZMod (p ^ (4 * M)) := fun m => (a m : ZMod (p ^ (4 * M)))
  let y : Fin (n + 1) → ZMod (p ^ (4 * M)) := fun i => (x i : ZMod (p ^ (4 * M)))
  have hb : b = (fun m => (a m : ZMod (p ^ (4 * M)))) := rfl
  have hy : y = (fun i => (x i : ZMod (p ^ (4 * M)))) := rfl
  have hbgen : NA.IsPrimGen (p ^ (4 * M)) b := isPrimGen_intCast hp hr1 a hprim
  have hygen : NA.IsPrimGen (p ^ (4 * M)) y := by
    refine (NA.isPrimGen_iff_exists_isUnit hp hr1 _).mpr ?_
    obtain ⟨i, hi⟩ := hxprim
    exact ⟨i, isUnit_intCast_of_not_dvd hp hr1 hi⟩
  have hfev : NA.fev d n b y = 0 := by
    have h := (NA.map_fev_dfev d n (Int.castRingHom (ZMod (p ^ (4 * M)))) a x).1
    rw [fev_eq_formEval] at h
    have h0 : ((formEval d n a x : ℤ) : ZMod (p ^ (4 * M))) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hxzero
    rw [hb, hy]
    exact h.symm.trans h0
  have hgrad : ∀ j, NA.gradv d n b y j
      = ((pderivEval d n a j x : ℤ) : ZMod (p ^ (4 * M))) := by
    intro j
    have h := (NA.map_fev_dfev d n (Int.castRingHom (ZMod (p ^ (4 * M)))) a x).2 j
    rw [dfev_eq_pderivEval d n a x j] at h
    rw [hb, hy]
    exact h.symm
  let E : Finset ℕ := (Finset.range (4 * M + 1)).filter
      (fun k => ∀ j, NA.vpDvd p (4 * M) k (NA.gradv d n b y j))
  have hEne : E.Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      fun j => ⟨NA.gradv d n b y j, by simp⟩⟩⟩
  let e : ℕ := E.max' hEne
  have he_mem : e ∈ E := E.max'_mem hEne
  have he_le : e ≤ 4 * M := by
    have := (Finset.mem_filter.mp he_mem).1
    rw [Finset.mem_range] at this
    omega
  have he_all : ∀ j, NA.vpDvd p (4 * M) e (NA.gradv d n b y j) :=
    (Finset.mem_filter.mp he_mem).2
  have he_max : ∀ y' ∈ E, y' ≤ e := fun y' hy' => Finset.le_max' E y' hy'
  have he_exact : e < 4 * M → ¬ (∀ j, NA.vpDvd p (4 * M) (e + 1) (NA.gradv d n b y j)) := by
    intro hlt hcon
    have hmem : e + 1 ∈ E :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hcon⟩
    have := he_max (e + 1) hmem
    omega
  have he_ge : 2 * M ≤ e := by
    by_contra hlt
    push_neg at hlt
    have hR2 : 2 * e + 1 ≤ R := by omega
    have hzero : (p : ℤ) ^ (2 * e + 1) ∣ formEval d n a x :=
      dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hxzero
    have he_dvd : ∀ i, (p : ℤ) ^ e ∣ pderivEval d n a i x := by
      intro i
      have hg := he_all i
      rw [hgrad i] at hg
      exact (dvd_iff_vpDvd p (4 * M) e hp (by omega) (pderivEval d n a i x)).mp hg
    have hex' : ∃ i, ¬ (p : ℤ) ^ (e + 1) ∣ pderivEval d n a i x := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact he_exact (by omega) (fun j => by
        rw [hgrad j]
        exact (dvd_iff_vpDvd p (4 * M) (e + 1) hp (by omega) (pderivEval d n a j x)).mpr (hcon j))
    exact h2 (lift.hensel_lift d n p hp a x e R hxprim hzero he_dvd hex' hR2)
  exact ⟨e, Finset.mem_Icc.mpr ⟨he_ge, he_le⟩, hbgen, y, hygen, hfev, he_all, he_exact⟩

/-- (D7) Deep failures at `p ≤ M`: a primitive zero mod `p^{4M}` that does not lift to `p^R`
forces gradient valuation `e ≥ 2M` (else `hensel_lift` with `2e+1 ≤ 4M`), so
`a mod p^{4M} ∈ ⋃_{e=2M}^{4M} R^{(e)}(p^{4M})`; `NA.card_Rset_le` gives `≤ 4p^{4MN-2M}` classes;
`primCount_residue_le` per class, with `A ≥ p^{4M}`. -/
theorem deep_failure_count (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) (M p R : ℕ) (hp : p.Prime)
    (hM : 1 ≤ M) (hR : 4 * M ≤ R) (A : ℝ) (hA : (p : ℝ) ^ (4 * M) ≤ A) :
    primCount d n A (fun a => PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R)
      ≤ 4 * 3 ^ NN d n * A ^ NN d n / (p : ℝ) ^ (2 * M) := by
  classical
  haveI : NeZero (p ^ (4 * M)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hpnn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hA0 : (0 : ℝ) ≤ A := le_trans (pow_nonneg hpnn (4 * M)) hA
  have hq0 : 0 < p ^ (4 * M) := Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)
  let T : Finset (Mon d n → ZMod (p ^ (4 * M))) := Finset.univ.filter
      (fun b => ∃ e ∈ Finset.Icc (2 * M) (4 * M), NA.Rset d n p (4 * M) e b)
  have hcover : ∀ a, (IsPrim a ∧ (PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R))
      → (fun m => (a m : ZMod (p ^ (4 * M)))) ∈ T := by
    rintro a ⟨hpa, h1, h2⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      deep_failure_Rset d n M p R hp hM hR a hpa h1 h2⟩
  have hqv : ((p ^ (4 * M) : ℕ) : ℝ) = (p : ℝ) ^ (4 * M) := Nat.cast_pow p (4 * M)
  have hfib0 := NA.primCount_le_fiber d n (p ^ (4 * M)) hq0 A hA0
      (fun a => IsPrim a ∧ (PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R))
      (fun c => c ∈ T) hcover
  have hfib : primCount d n A (fun a => IsPrim a ∧
        (PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R))
      ≤ (2 * A / (p : ℝ) ^ (4 * M) + 1) ^ NN d n
        * (Nat.card {c : Mon d n → ZMod (p ^ (4 * M)) // c ∈ T} : ℝ) := by
    simpa only [hqv] using hfib0
  have hcardT : (Nat.card {c : Mon d n → ZMod (p ^ (4 * M)) // c ∈ T} : ℝ) = (T.card : ℝ) := by
    congr 1
    rw [NA.natCard_eq_filter_card, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hTle : T.card ≤ 4 * p ^ (4 * M * NN d n - 2 * M) :=
    card_le_Rset_classes d n M p (by omega) hp hM T (fun b hb => (Finset.mem_filter.mp hb).2)
  have hset : primSet d n A (fun a => IsPrim a ∧
        (PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R))
      = primSet d n A (fun a => PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R) := by
    ext a; simp only [primSet, Set.mem_setOf_eq]; tauto
  have hPeq : primCount d n A (fun a => IsPrim a ∧
        (PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R))
      = primCount d n A (fun a => PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R) := by
    unfold primCount
    rw [hset]
  calc primCount d n A (fun a => PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R)
      = primCount d n A (fun a => IsPrim a ∧
          (PrimModZero d n a p (4 * M) ∧ ¬ PrimModZero d n a p R)) := hPeq.symm
    _ ≤ (2 * A / (p : ℝ) ^ (4 * M) + 1) ^ NN d n
          * (Nat.card {c : Mon d n → ZMod (p ^ (4 * M)) // c ∈ T} : ℝ) := hfib
    _ = (T.card : ℝ) * (2 * A / (p : ℝ) ^ (4 * M) + 1) ^ NN d n := by rw [hcardT]; ring
    _ ≤ ((4 * p ^ (4 * M * NN d n - 2 * M) : ℕ) : ℝ)
          * (2 * A / (p : ℝ) ^ (4 * M) + 1) ^ NN d n := by
        have hb0 : (0 : ℝ) ≤ 2 * A / (p : ℝ) ^ (4 * M) + 1 := by
          have h : (0 : ℝ) ≤ 2 * A / (p : ℝ) ^ (4 * M) :=
            div_nonneg (by linarith) (pow_nonneg hpnn _)
          linarith
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hTle) (pow_nonneg hb0 _)
    _ = (4 * (p : ℝ) ^ (4 * M * NN d n - 2 * M))
          * (2 * A / (p : ℝ) ^ (4 * M) + 1) ^ NN d n := by
        push_cast
        ring
    _ ≤ 4 * 3 ^ NN d n * A ^ NN d n / (p : ℝ) ^ (2 * M) := classes_mul_le d n M p hd hp hM A hA

end Work.HP.DN
