import Mathlib
import Submission.Core.FaPolar
import Submission.Core.FaConcave
import Submission.Core.D3
import Submission.Core.FaArcs
import Submission.Core.FullPeriod

/-!
# KL-F3+F5: arc decomposition of the circle and the circle mean ≥ 0

(F3, F5 of Plan.md DESIGN NOTE 6.)  Let `z_j := E(θ_j)` be points on the
unit circle with weights `p_j ≥ 0`, `Σ_j p_j = n ≥ 1` (`hsum`), and
`a > 0`.  Let

    faE n a θ p σ := fa n a (fun j => E (θ j)) p (E σ)
                  = a · ∏_j (1 + E(σ − θ_j))^{p_j}

The "jump points" of the circle are the antipodes `-z_j` with `p_j > 0`,
i.e. the `σ ≡ θ_j + π (mod 2π)`; they split the circle into `m ≤ n` open
arcs (`m` = number of *distinct* jump points).  On each arc the continuous
argument lift

    T(σ) := Σ_j p_j · (Complex.log (1 + E(σ − θ_j))).im

is affine with slope `Σ_j p_j / 2 = n/2` (F2:
`faE_arg_hasDerivAt` + zero-derivative-implies-constant on an interval), and
`faE σ = ‖faE σ‖·E(T σ)` (F2: `faE_polar`).  Writing the arc's θ-points as
`σ(t)` (the inverse of `t = T(σ)`, affine with slope `2/n`), the function
`f(t) := faE (σ(t))` satisfies `f t = ‖f t‖ · E t` on the arc, is
continuous, has `‖f‖ ≤ c < 2` (uniform margin), and `‖f‖/2` is unimodal in
`t` on the arc (F4: `log_faE_concaveOn` + `unimodal_of_log_concave`).
`Submission.Core.D3.per_arc_bound` then gives, for the t-interval `I` of
the arc,

    ∫_I log‖2 − f(t)‖ dt ≥ (|I| − π)·log 2.

With `dθ = (2/n) dt`, summing the per-arc bounds over the `m` arcs
(t-lengths summing to `n·π` since the circle has θ-length `2π` and slope
`n/2`) yields the target:

    ∫_0^{2π} log‖2 − faE n a θ p σ‖ dσ ≥ (2/n)·(n−m)·π·log 2 ≥ 0.

PROVE THE TWO THEOREMS BELOW (`circle_mean_nonneg` and the continuity
lemma `continuous_faE_norm`), plus any helper lemmas you need.  Finish
every proof; none may remain unfinished; `lake build Submission.Core.F5Circle`.

## Suggested structure (you may reorganize; keep the public theorems' types)

1. **Continuity**: `fun σ => ‖faE n a θ p σ‖` is continuous on ℝ
   (`continuous_faE_norm` below; also `continuous_faE : Continuous (fun σ
   => faE n a θ p σ)` if needed).  Each factor `σ ↦ 1 + E(σ−θ_j)` is smooth
   and hits `0` only at jump points; `cPow z p` is continuous in `z` at
   `z ≠ 0` (`ContinuousAt.cpow_const` needs `z ∈ slitPlane`; at `z = 0` use
   `continuousAt_cpow_zero_of_re_pos` when `0 < p`, and for `p = 0` the
   factor is constantly `1` — `(0:ℂ) ^ (0:ℂ) = 1`).  `Finset.prod` and
   `norm` preserve continuity.

2. **Norm identity on the circle** (jump-free `σ`):
   `‖faE n a θ p σ‖ = a · ∏_j ‖1 + E(σ−θ_j)‖^{p_j}` — instantiate
   `fa_norm_on_circle` (F1Norm) with `z j := E (θ j)`, `w := E σ`
   (uses `norm_E`, `norm_one_add_mul_conj`, `E_add`; mirror the proof of
   `FaPolar.faE_eq`).  [Only needed for the *margin* step in the next
   module, not for F5 itself; you may skip it here.]

3. **Jumps and arcs.**  Let `m := ‖{j : p j ≠ 0}‖`-derived *distinct* jump
   set `J := (Finset.univ.filter (fun j => p j ≠ 0)).image (fun j =>
   toIocMod 0 (by norm_num : (0:ℝ) < 2*π) (θ j + π))`-style (or any
   canonical reduction of `θ_j + π` to an interval of length `2π`); sort
   `J` increasingly: `l : List ℝ` with `l.length = m`, strictly increasing,
   `l.get i` for `i : Fin m`.  Prove `m ≤ n` (image of a subset of `Fin n`)
   and the "arc" data:
   - consecutive pairs `(l_i, l_{i+1})` for `i+1 < m`, plus the wrap-around
     pair `(l_{m−1}, l_0 + 2π)`, partition the circle: total θ-length `2π`.
   - all jump points are `≡ θ_j + π (mod 2π)` for some `j` with `p_j ≠ 0`,
     and conversely every such point is a jump; on each open arc NO factor
     `1 + E(σ−θ_j)` vanishes (prove: a zero would make `σ` a jump point).
   - choose the fundamental domain `[l_0, l_0 + 2π]` (contains exactly the
     sorted jumps `l_0 < l_1 < … < l_{m−1}` in its interior up to the left
     endpoint).  `∫_{l_0}^{l_0+2π} = ∫_0^{2π}` because the integrand is
     `2π`-periodic in `σ` (`E (σ+2π) = E σ` ⟹ `faE n a θ p (σ+2π) =
     faE n a θ p σ`).

4. **Per-arc t-coordinate.**  On the open arc `(u,v)` (u = l_i or l_0,
   v = next jump or l_0+2π) the lift `T(σ) := Σ_j p_j·(Complex.log
   (1+E(σ−θ_j))).im` is differentiable with derivative `n/2`
   (`faE_arg_hasDerivAt` gives the pointwise derivative at every `σ` in the
   arc), hence `T` is affine on the arc: `T σ = T u + (n/2)(σ − u)` for all
   `σ ∈ [u,v]`.  To get affine-from-derivative, prove/use: a function on an
   interval with derivative identically `0` is constant
   (`isConstOn_of_derivWithin_eq_zero`-style or
   `intervalIntegral.integral_deriv_eq_sub`/FTC, or
   `eqOn_of_deriv_eq_zero`-type lemmas in Mathlib/Analysis/Calculus/
   MeanValue.lean); apply to `σ ↦ T σ − (n/2)·σ` on `[u,v]` (subtract two
   functions with the same derivative).  Define the t-interval of the arc
   as `I := (T u, T v)` (length `(n/2)(v−u)`); `σ(t) := u + (2/n)(t − T u)`
   maps `I` bijectively onto `(u,v)`.
   `faE_polar` (F2) gives `faE (σ t) = ‖faE (σ t)‖ · E (T(σ t)) = ‖…‖ · E t`.

5. **Per-arc bound.**  For the arc with `f(t) := faE (σ t)` on the closed
   t-interval `[T u, T v]`:
   - `f` continuous on the closed t-interval (from `continuous_faE` and
     continuity of `σ`), `f t = ‖f t‖·E t` (step 4), `‖f t‖ ≤ c` where
     `c < 2` is the margin (hypothesis `hmarg : ∀ σ, ‖faE n a θ p σ‖ ≤ c`),
     and `q := ‖f‖/2` is unimodal (`UnimodalOn`): log-concavity of
     `σ ↦ log‖faE n a θ p σ‖` on the open arc (`log_faE_concaveOn`,
     FaConcave; needs `0 < a`, `p_j ≥ 0`, jump-free on the arc), transfer
     through the affine change `σ(t)` (`concaveOn_comp_affine`) to get
     log-concavity of `t ↦ log‖f t‖` on the open t-interval, then
     `unimodal_of_log_concave` (FaConcave) with `q := ‖f‖/2` (continuous,
     positive inside) gives `∃ m, UnimodalOn (T u) (T v) m q`.
   - `per_arc_bound (T u) (T v) f (hle) (hfc) (harg) (hΦ) hc2 hu` gives
     `∫_{T u}^{T v} log‖2 − f t‖ dt ≥ ((T v − T u) − π)·log 2`.
   - Change of variable (`affine_change` in FaArcs, or direct
     substitution): `∫_u^v log‖2 − faE n a θ p σ‖ dσ =
     (2/n)·∫_{T u}^{T v} log‖2 − f t‖ dt` (here `g σ := log‖2 − faE n a
     θ p σ‖`, `σ = (2/n)(t − T u) + u`).

6. **Sum over the arcs.**  Index the arcs by `Fin m` (or a List); their
   θ-lengths sum to `2π` (step 3), so t-lengths `(n/2)·(θ-length)` sum to
   `n·π`.  Summing the per-arc bounds (like `D3.arc_sum_bound`) gives
   `Σ_j ∫_{arc_j} … ≥ (2/n)·(n·π − m·π)·log 2`; with `m ≤ n` and `log 2 >
   0` this is `≥ 0`.  Conclude `∫_{l_0}^{l_0+2π} ≥ 0`, then use
   periodicity to replace the domain by `0..2π`.

## Mathlib hints
- Interval integrals: `intervalIntegral.integral_add`,
  `intervalIntegral.integral_const`, `intervalIntegral.integral_congr`,
  `intervalIntegral.integral_comp_add_right`-style (periodicity),
  `intervalIntegral.integral_of_le`; `intervalIntegral.integral_undef` if a
  function fails to be integrable (should not happen: all integrands here
  are continuous on their intervals).
- `IntervalIntegrable` of continuous functions:
  `ContinuousOn.intervalIntegrable` (needs `ContinuousOn` on `uIcc`).
- Trig periodicity of `E`: `E_two_pi : E (t + 2π) = E t` (FullPeriod or
  prove locally), `E_add : E (a+b) = E a * E b`.
- Strict increase of sorted lists: `List.Sorted`, `Finset.sort`,
  `List.get`, `List.length_sort`; strictly increasing list values:
  `List.sorted_lt` etc.  Alternatively represent arcs by an explicit
  recursive construction over the sorted List (`List.Pairwise`).
- `toIocMod` (in Mathlib/Analysis/.../IocDiv?) reduces a real modulo
  `2π` into `(a, a+2π]`; alternatively use `Complex.arg (E t)` ∈ `(-π,π]`
  or `Int.fract (t/(2*π)) * (2*π)` ∈ `[0,2π)`; or avoid reduction
  altogether by working with the set of jump points modulo `2π` through
  `E`-values: jump points = `{w : Circle | w = -z_j}`-style in terms of the
  circle `Circle`, but note all the real analysis is on ℝ.
- You may *simplify the arc data* by choosing your own concrete
  fundamental-domain strategy (e.g., a half-open interval of length `2π`
  whose endpoints are NOT jump points, e.g. `(-π, π]`), sorting the jump
  points inside it, and forming the arcs cyclically — but make sure the
  partition, the total-length `nπ`, and `m ≤ n` are proved and used in the
  right places.  Keep the θ-arcs *open* and note their endpoints have
  measure zero, so interval integrals over closed vs open endpoints agree
  (`intervalIntegral.integral_congr_ae`, or integrate over closed arcs and
  note the endpoints are the same).
- When applying `per_arc_bound` remember it needs `a ≤ b`, continuity of
  `f` on `Icc a b`, the polar form, the uniform margin `c < 2`, and the
  unimodality; it returns the bound in `ℝ`.
- `Real.log 2 > 0`: `Real.log_two_pos`; `Real.pi_pos`.
- Everything is over `σ`/`t` real; open `Interval`, `MeasureTheory`.
- Final result uses `hmarg : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c` with `c < 2`
  (given); it is used ONLY to feed `per_arc_bound`'s `c`; no other
  analyticity is required beyond continuity of `faE`.
- `circle_mean_nonneg` must be proved for every `σ` margin (not only
  `σ ∈ [0,2π]`); use periodicity to restrict if convenient.
- Do NOT import `Submission.Core.LogMean` (not needed here).

============================================================================
RECOMMENDED ARCHITECTURE (read this before starting)
============================================================================
Work bottom-up.  A complete proof outline (each bullet is a lemma to prove;
use `by have ...` liberally; the file may grow helpers freely):

0. PERIODICITY: `faE n a θ p (σ + 2*π) = faE n a θ p σ` (E_two_pi) and the
   integrand is 2π-periodic; so you may integrate over any interval of
   length 2π (use `intervalIntegral.integral_comp_add_right` to shift).

1. CONTINUITY (`continuous_faE_norm`, `continuous_faE`): each factor
   `σ ↦ 1 + E(σ−θ_j)` is continuous and misses the negative real axis
   except at the jump points (where it is 0); `cPow z p` is continuous in
   z away from 0 (`ContinuousAt.cpow_const`, z in slitPlane: re ≥ 0 and
   ≠ 0 ⟹ slitPlane), and at z→0 with p>0 use
   `continuousAt_cpow_zero_of_re_pos` (0 < p.re), while p = 0 makes the
   factor constantly 1.  Products and norm preserve continuity.
   `E`-facts: `E (σ−θ_j) = (cos(σ−θ_j) : ℂ) + (sin(σ−θ_j) : ℂ) * I`;
   `re (1 + E x) = 1 + cos x`, `im = sin x`.

2. THE t-LIFT ON AN OPEN ARC (u,v) with NO jump inside: define
   `T σ := ∑ j, p j * (Complex.log (1 + E (σ - θ j))).im`.
   - `faE_arg_hasDerivAt` (FaPolar) gives, at every σ with all factors
     nonzero, `HasDerivAt T ((∑ p)/2) σ`; `hsum` makes this `n/2`.
   - Hence `σ ↦ T σ − (n/2)*σ` has derivative 0 on (u,v); prove it is
     constant on [u,v]: use `intervalIntegral.integral_eq_sub_of_hasDerivAt`
     (FTC; needs continuity of T on [u,v] and differentiability on the
     interval) or `Convex.is_const_on_of_fderivWithin_eq_zero`-type lemmas
     (MeanValue.lean) or the mean value theorem specialized to ℝ; add
     continuity of `T` on [u,v] (from continuity of log along the arc —
     factors are uniformly away from 0 on a compact subinterval; for the
     closed arc endpoints are jump points where some factor is 0, so either
     (a) prove affinity only on compact subintervals [u+δ, v−δ] and let
     δ→0 later, or (b) define T on the closed arc by the one-sided limit /
     note that per_arc_bound and all integrals only care about the open
     arc (endpoints are a measure-zero set), so prove affinity on the open
     arc (u,v) and integrate over the open arc).
   - CONSEQUENCE (the only form you need): for the arc with endpoints
     `x < y` in (u,v) (or the whole arc), `T y − T x = (n/2)·(y − x)`.

3. ARCS AND THE CUT: Let `J0 := {j : Fin n | p j ≠ 0}` and the multiset of
   jump angles be `θ j + π` for j ∈ J0, reduced modulo 2π into a fixed
   half-open interval of length 2π via `toIocMod Real.two_pi_pos a x` or
   `toIcoMod`, then take the image Finset `S : Finset ℝ` (this removes
   duplicates: m := S.card ≤ J0.card ≤ n).  Choose the fundamental domain
   `[l₀, l₀ + 2π]` where `l₀ : ℝ` is any point that is NOT ≡ a jump
   (exists because there are finitely many jump residues; pick e.g.
   `l₀ := 0` after rotating θ by a small amount, or handle the general
   case directly).  Sort `S ∪ {l₀+2π}` (or `S` and add the final point):
   get a strictly increasing list `l : List ℝ`, `l.length = m + 1`,
   `l.head = l₀`, `l.getLast = l₀ + 2π`; the arcs are
   `(l[i], l[i+1])` for `i = 0, …, m−1`, θ-lengths summing to `2π`.
   SUGGESTED list API: `Finset.sort (· ≤ ·) S`, `List.length_sort`,
   `List.Sorted`, `List.get`, `List.getLast`, `List.pairwise`; or
   alternative: prove by well-founded induction over the Finset that
   `∫_a^b g = ∑ over consecutive gaps` using
   `Finset.max'` / `Finset.min'` (split at the extreme jump and recurse on
   the remaining set in the smaller interval) — no explicit list needed if
   you define the gap-sum recursively.

4. PER-ARC INEQUALITY on the arc (α, β) (α < β, no jumps inside):
   choose `σ₀ := (α+β)/2`; set `t₀ := T σ₀`, `c := t₀ − (n/2)·σ₀`; the
   arc's t-interval is `(T α⁺, T β⁻)` = `(t₀ + (n/2)(α−σ₀),
   t₀ + (n/2)(β−σ₀))` — by (2) `T σ = c + (n/2)·σ` on the arc.  Define
   `f (t) := faE n a θ p ((t − c) / (n/2))` — the θ-inverse is affine;
   then:
   - `f t = ‖f t‖ * E t`: from `faE_polar` (FaPolar) applied at
     `σ = (t−c)/(n/2)` (a jump-free point), using `T σ = t`.
   - `f` continuous on the closed t-interval (continuity of faE and of the
     affine map; at the endpoints faE is continuous too — for closed
     intervals take limits or integrate over the open arc and use that the
     per-arc bound is continuous in the endpoints).
   - `‖f t‖ ≤ c` for all t (margin, `hmarg`).
   - unimodality of `t ↦ ‖f t‖ / 2`: `log‖faE n a θ p σ‖` is concave in σ
     on the open arc (`log_faE_concaveOn`, FaConcave — requires `0 < a`;
     handle `a = 0` separately: then `faE ≡ 0` and `circle_mean_nonneg` is
     trivial since the integrand is `log 2`), transfer through the affine
     σ(t) (`concaveOn_comp_affine`), then `unimodal_of_log_concave`
     (FaConcave) with the positive-continuous function `‖f‖/2`.
   - `per_arc_bound` (D3) gives `∫_{T α⁺}^{T β⁻} log‖2 − f t‖ dt ≥
     (((T β⁻ − T α⁺)) − π) · log 2`.
   - CHANGE OF VARIABLE: `∫_α^β log‖2 − faE σ‖ dσ = (2/n) · ∫_{T α⁺}^{T β⁻}
     log‖2 − f t‖ dt` — either by `affine_change` (FaArcs) or directly via
     `intervalIntegral.integral_comp_mul_add`/`integral_comp_add_right`
     with `σ = (t−c)·(2/n)`.

5. SUM OVER ARCS and conclusion: index arcs by a List/Fin; the per-arc
   inequalities and the substitution give
   `∫ over the fundamental domain ≥ (2/n)·(Σ over arcs ((t-length) − π))·log 2`
   `= (2/n)·((n/2)·2π − m·π)·log 2 = (2π/n)·(n − m)·log 2 ≥ 0` since
   `m ≤ n`.  Note: only the arc where the fundamental domain wraps needs
   care with its t-endpoints (both are jump points of the same residue
   class); use the open-arc version and integrate over the open arcs, or
   choose the fundamental domain with non-jump endpoints and add the two
   boundary "half-arcs" as extra arcs (increasing m by up to 1 but keeping
   m' ≤ n + 1... CAREFUL: to keep `m' ≤ n` choose endpoints at the SAME
   jump so that no extra arcs are created, or re-derive the final
   inequality with m' = m + 2 and check the constant still works: if the
   domain endpoints are NOT jumps there are m+1 arcs and Σ(t-lengths) =
   (n/2)·2π still, so the loss is (m+1)π; the final lower bound is
   (2/n)·(nπ − (m+1)π)·log 2 ≥ 0 still requires m+1 ≤ n: NOT always true!
   Therefore PREFER the fundamental domain [l₀, l₀+2π] with l₀ a jump
   point (then exactly m arcs and m ≤ n, and the bound closes).  If l₀ is
   a jump, the FIRST and LAST t-intervals have endpoints where T has
   one-sided limits differing by the jump; integrate each open arc (α,β)
   with both endpoints jumps: `∫_α^β` over the OPEN arc equals the
   interval integral over [α,β] because the endpoints have measure zero.)
6. Finally shift the domain `[l₀, l₀+2π]` back to `[0, 2π]` with
   `intervalIntegral.integral_comp_add_right` (integrand is periodic).
============================================================================
-/

noncomputable section

open scoped Real Complex BigOperators
open Complex
open MeasureTheory
open Interval

namespace Submission.CoreB

open Submission.Core

/-! ## Local plumbing: periodicity and factor continuity -/

/-- `E (t + 2π) = E t`. -/
private lemma E_two_pi_periodic (t : ℝ) : E (t + 2 * Real.pi) = E t := by
  calc
    E (t + 2 * Real.pi) = E t * E (2 * Real.pi) := by rw [E_add]
    _ = E t * 1 := by
      congr 1
      dsimp [E]
      have h : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h]
      rw [Complex.exp_two_pi_mul_I]
    _ = E t := by ring

/-- `faE` is `2π`-periodic in the circle parameter. -/
private lemma faE_periodic (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) :
    faE n a θ p (σ + 2 * Real.pi) = faE n a θ p σ := by
  rw [faE_eq, faE_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  congr 1
  calc
    E ((σ + 2 * Real.pi) - θ j) = E ((σ - θ j) + 2 * Real.pi) := by congr 1; ring
    _ = E (σ - θ j) := E_two_pi_periodic (σ - θ j)

/-- Each circle factor `σ ↦ (1 + E (σ - θ))^{p}` is continuous for `0 ≤ p`
(complex principal power; at a vanishing base use `p > 0`, and `p = 0`
makes the factor constantly `1`). -/
private lemma factor_continuous (θ : ℝ) (p : ℝ) (hp : 0 ≤ p) :
    Continuous (fun σ : ℝ => cPow (1 + E (σ - θ)) p) := by
  by_cases hp0 : p = 0
  · have hpj : p = 0 := hp0
    have hc : Continuous (fun σ : ℝ => cPow (1 + E (σ - θ)) p) := by
      rw [hpj]
      have h : (fun σ : ℝ => cPow (1 + E (σ - θ)) 0) = fun _ : ℝ => (1 : ℂ) := by
        funext σ
        simp [cPow]
      rw [h]
      exact continuous_const
    exact hc
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
    rw [continuous_iff_continuousAt]
    intro σ₀
    let z : ℂ := 1 + E (σ₀ - θ)
    have hzcond : 0 ≤ z.re ∨ z.im ≠ 0 := by
      by_cases hz : z = 0
      · left
        simp [z, hz]
      · have hsp : z ∈ slitPlane := by
          dsimp [z]
          exact one_add_E_mem_slitPlane hz
        rw [Complex.mem_slitPlane_iff] at hsp
        rcases hsp with hre | him
        · left
          exact le_of_lt hre
        · right
          exact him
    have hcpow : ContinuousAt (fun x : ℂ => x ^ (p : ℂ)) z := by
      exact Complex.continuousAt_cpow_const_of_re_pos hzcond (by simpa using hp')
    have hbase : ContinuousAt (fun σ : ℝ => (1 + E (σ - θ) : ℂ)) σ₀ := by
      fun_prop
    have hcomp : ContinuousAt (fun σ : ℝ => (1 + E (σ - θ) : ℂ) ^ (p : ℂ)) σ₀ := by
      change ContinuousAt ((fun x : ℂ => x ^ (p : ℂ)) ∘
        (fun σ : ℝ => (1 + E (σ - θ) : ℂ))) σ₀
      exact ContinuousAt.comp hcpow hbase
    simpa [cPow] using hcomp

/-- **Continuity of `faE` in the circle parameter.**  With `0 ≤ a` and
`p_j ≥ 0`, `σ ↦ faE n a θ p σ` is continuous. -/
theorem continuous_faE (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j) :
    Continuous (fun σ : ℝ => faE n a θ p σ) := by
  classical
  have hfac : ∀ j : Fin n, Continuous (fun σ : ℝ => cPow (1 + E (σ - θ j)) (p j)) := by
    intro j
    exact factor_continuous (θ j) (p j) (hp j)
  let F : Fin n → ℝ → ℂ := fun j σ => cPow (1 + E (σ - θ j)) (p j)
  have hF : ∀ j : Fin n, Continuous (F j) := by
    intro j
    simpa [F] using hfac j
  have hprod : Continuous (fun σ : ℝ => ∏ j : Fin n, F j σ) := by
    simpa using
      (continuous_finset_prod (s := (Finset.univ : Finset (Fin n))) (f := F)
        (by intro j hj; exact hF j))
  have hcont : Continuous (fun σ : ℝ => (a : ℂ) * ∏ j : Fin n, F j σ) :=
    (continuous_const.mul hprod)
  have hEqFun : (fun σ : ℝ => faE n a θ p σ) = fun σ : ℝ => (a : ℂ) * ∏ j : Fin n, F j σ := by
    funext σ
    dsimp [F]
    rw [faE_eq]
  rw [hEqFun]
  exact hcont

/-- **Continuity of the modulus of `faE` in the circle parameter.**  With
`0 ≤ a` and `p_j ≥ 0`, `σ ↦ ‖faE n a θ p σ‖` is continuous. -/
theorem continuous_faE_norm (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ)
    (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j) :
    Continuous (fun σ : ℝ => ‖faE n a θ p σ‖) := by
  exact (continuous_faE n a ha θ p hp).norm

def IsJump (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) : Prop :=
  ∃ j : Fin n, p j ≠ 0 ∧ E (σ - θ j) = -1

noncomputable def argLift (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) : ℝ :=
  ∑ j : Fin n, p j * (Complex.log (1 + E (σ - θ j))).im

noncomputable def circleG (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) (σ : ℝ) : ℝ :=
  Real.log ‖(2 : ℂ) - faE n a θ p σ‖

lemma faE_zero_of_jump (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) {σ : ℝ}
    (hj : IsJump n θ p σ) :
    faE n a θ p σ = 0 := by
  rcases hj with ⟨j, hpj, hE⟩
  rw [faE_eq]
  have hfac : cPow (1 + E (σ - θ j)) (p j) = 0 := by
    dsimp [cPow]
    rw [hE]
    have hpz : (p j : ℂ) ≠ 0 := by exact_mod_cast hpj
    simp [zero_cpow hpz]
  have hprod : (∏ k : Fin n, cPow (1 + E (σ - θ k)) (p k)) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) hfac
  simp [hprod]

lemma norm_faE_zero_of_jump (n : ℕ) (a : ℝ) (θ : Fin n → ℝ) (p : Fin n → ℝ) {σ : ℝ}
    (hj : IsJump n θ p σ) :
    ‖faE n a θ p σ‖ = 0 := by
  rw [faE_zero_of_jump n a θ p hj]
  norm_num

lemma norm_faE_pos (n : ℕ) (a : ℝ) (ha : 0 < a) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    {σ : ℝ} (hne : ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) : 0 < ‖faE n a θ p σ‖ := by
  rw [faE_norm n a (le_of_lt ha) θ p (σ := σ) hne]
  apply mul_pos ha
  apply Finset.prod_pos
  intro j hj
  apply Real.rpow_pos_of_pos
  exact norm_pos_iff.mpr (hne j)

lemma hasDerivAt_argLift (n : ℕ) (θ : Fin n → ℝ) (p : Fin n → ℝ) {σ₀ : ℝ}
    (hne : ∀ j : Fin n, (1 : ℂ) + E (σ₀ - θ j) ≠ 0) :
    HasDerivAt (argLift n θ p) ((∑ j : Fin n, p j) / 2) σ₀ := by
  change HasDerivAt (fun σ : ℝ => ∑ j : Fin n,
      p j * (Complex.log (1 + E (σ - θ j))).im) ((∑ j : Fin n, p j) / 2) σ₀
  exact faE_arg_hasDerivAt n θ p (σ₀ := σ₀) hne

lemma argLift_eqOn_arc {n : ℕ} (θ : Fin n → ℝ) (p : Fin n → ℝ) {u v : ℝ}
    (hno : ∀ σ ∈ Set.Ioo u v, ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) :
    ∃ c : ℝ, ∀ σ ∈ Set.Ioo u v,
      argLift n θ p σ = ((∑ j : Fin n, p j) / 2) * σ + c := by
  let s : Set ℝ := Set.Ioo u v
  let f : ℝ → ℝ := argLift n θ p
  let g : ℝ → ℝ := fun σ : ℝ => ((∑ j : Fin n, p j) / 2) * σ
  have hs : IsOpen s := isOpen_Ioo
  have hconn : IsPreconnected s := isPreconnected_Ioo
  have hf : DifferentiableOn ℝ f s := by
    intro σ hσ
    exact (hasDerivAt_argLift n θ p (σ₀ := σ) (fun j => hno σ hσ j)).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ g s := by
    intro σ hσ
    exact ((hasDerivAt_id σ).const_mul ((∑ j : Fin n, p j) / 2)).differentiableAt.differentiableWithinAt
  have hfd : s.EqOn (deriv f) (deriv g) := by
    intro σ hσ
    have hf' : deriv f σ = (∑ j : Fin n, p j) / 2 :=
      (hasDerivAt_argLift n θ p (σ₀ := σ) (fun j => hno σ hσ j)).deriv
    have hg' : deriv g σ = (∑ j : Fin n, p j) / 2 := by
      dsimp [g]
      simpa using ((hasDerivAt_id σ).const_mul ((∑ j : Fin n, p j) / 2)).deriv
    rw [hf', hg']
  rcases hs.exists_eq_add_of_deriv_eq hconn hf hg hfd with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro σ hσ
  have := hc hσ
  dsimp [g] at this
  exact this

/-- positivity of ‖2 - faE‖ from the uniform margin -/
lemma two_sub_faE_norm_pos {n : ℕ} {a : ℝ} (θ : Fin n → ℝ) (p : Fin n → ℝ)
    {c : ℝ} (hc : c < 2) (hmarg : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c) (σ : ℝ) :
    0 < ‖(2 : ℂ) - faE n a θ p σ‖ := by
  have hn : ‖(2 : ℂ)‖ ≤ ‖(2 : ℂ) - faE n a θ p σ‖ + ‖faE n a θ p σ‖ := by
    have := norm_add_le (a := (2 : ℂ) - faE n a θ p σ) (b := faE n a θ p σ)
    simpa using this
  have h2c : 0 < 2 - c := sub_pos.mpr hc
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hle : ‖faE n a θ p σ‖ ≤ c := hmarg σ
  nlinarith

/-- continuity of the circle integrand -/
lemma continuous_circleG {n : ℕ} (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : ∀ j : Fin n, 0 ≤ p j) {c : ℝ} (hc : c < 2)
    (hmarg : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c) :
    Continuous (fun σ : ℝ => circleG n a θ p σ) := by
  rw [continuous_iff_continuousAt]
  intro σ₀
  have hfa : ContinuousAt (fun σ : ℝ => faE n a θ p σ) σ₀ :=
    (continuous_faE n a ha θ p hp).continuousAt
  have hsub : ContinuousAt (fun σ : ℝ => (2 : ℂ) - faE n a θ p σ) σ₀ := by
    fun_prop
  have hnz' : ‖(2 : ℂ) - faE n a θ p σ₀‖ ≠ 0 :=
    ne_of_gt (two_sub_faE_norm_pos θ p hc hmarg σ₀)
  have hnorm : ContinuousAt (fun σ : ℝ => ‖(2 : ℂ) - faE n a θ p σ‖) σ₀ := hsub.norm
  have hlog : ContinuousAt (fun x : ℝ => Real.log x) ‖(2 : ℂ) - faE n a θ p σ₀‖ := by
    exact Real.continuousAt_log hnz'
  have hc : ContinuousAt (fun σ : ℝ => Real.log (‖(2 : ℂ) - faE n a θ p σ‖)) σ₀ := by
    let H : ℝ → ℝ := fun σ : ℝ => ‖(2 : ℂ) - faE n a θ p σ‖
    have hcH : ContinuousAt H σ₀ := by
      simpa [H] using hnorm
    have hlogH : ContinuousAt (fun x : ℝ => Real.log x) (H σ₀) := by
      simpa [H] using hlog
    change ContinuousAt (fun σ : ℝ => Real.log (H σ)) σ₀
    exact hlogH.comp hcH
  change ContinuousAt (fun σ : ℝ => circleG n a θ p σ) σ₀
  simpa [circleG] using hc

-- (test) it all compiles so far


/-- Unimodality of `t ↦ ‖faE (σfun t)‖/2` on `[A,B]` for an arc: transfer of
the log-concavity of `‖faE‖` in `σ ∈ (u,v)` through the affine map
`t ↦ (t - coff)/r` (with `A = r·u + coff`, `B = r·v + coff`). -/
lemma arc_unimodal {n : ℕ} (a : ℝ) (ha : 0 < a) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    (hp : ∀ j : Fin n, 0 ≤ p j) {u v coff r : ℝ} (hr : 0 < r) (huv : u < v)
    (hno : ∀ σ ∈ Set.Ioo u v, ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0)
    (A B : ℝ) (hAB : A = r * u + coff) (hBB : B = r * v + coff) :
    ∃ m : ℝ, UnimodalOn A B m (fun t : ℝ => ‖faE n a θ p ((t - coff) / r)‖ / 2) := by
  have hle : A ≤ B := by
    rw [hAB, hBB]
    have : r * u ≤ r * v := mul_le_mul_of_nonneg_left (le_of_lt huv) (le_of_lt hr)
    linarith
  let q : ℝ → ℝ := fun t : ℝ => ‖faE n a θ p ((t - coff) / r)‖ / 2
  have hqcont : ContinuousOn q (Set.Icc A B) := by
    have hc : Continuous (fun t : ℝ => ‖faE n a θ p ((t - coff) / r)‖) := by
      refine (continuous_faE_norm n a (le_of_lt ha) θ p hp).comp ?_
      fun_prop
    have : ContinuousOn (fun t : ℝ => ‖faE n a θ p ((t - coff) / r)‖) (Set.Icc A B) :=
      hc.continuousOn
    simpa [q] using this.div_const 2
  have hqpos : ∀ t : ℝ, A < t → t < B → 0 < q t := by
    intro t htA htB
    have hu1 : u < (t - coff) / r := by
      rw [lt_div_iff₀ hr]
      have h1 : r * u < t - coff := by
        rw [hAB] at htA
        linarith
      simpa [mul_comm] using h1
    have hv1 : (t - coff) / r < v := by
      rw [div_lt_iff₀ hr]
      have h1 : t - coff < r * v := by
        rw [hBB] at htB
        linarith
      simpa [mul_comm] using h1
    have htm : (t - coff) / r ∈ Set.Ioo u v := ⟨hu1, hv1⟩
    have hpos : 0 < ‖faE n a θ p ((t - coff) / r)‖ :=
      norm_faE_pos n a ha θ p (σ := (t - coff) / r) (hno ((t - coff) / r) htm)
    dsimp [q]
    positivity
  -- log-concavity in t
  have hcF : ConcaveOn ℝ (Set.Ioo u v) (fun σ : ℝ => Real.log ‖faE n a θ p σ‖) :=
    log_faE_concaveOn n a ha θ p hp (u := u) (v := v) huv hno
  have hcFt : ConcaveOn ℝ (Set.Ioo (r * u + coff) (r * v + coff))
      (fun t : ℝ => Real.log ‖faE n a θ p ((t - coff) / r)‖) := by
    exact concaveOn_comp_affine (u := u) (v := v) (r := r) (c := coff) hr hcF
  have hcFt' : ConcaveOn ℝ (Set.Ioo A B)
      (fun t : ℝ => Real.log ‖faE n a θ p ((t - coff) / r)‖) := by
    simpa [hAB, hBB] using hcFt
  have hcL : ConcaveOn ℝ (Set.Ioo A B)
      (fun t : ℝ => Real.log (‖faE n a θ p ((t - coff) / r)‖ / 2)) := by
    -- log(‖f‖/2) = log‖f‖ - log 2 pointwise on (A,B)
    have hsub : ConcaveOn ℝ (Set.Ioo A B)
        (fun t : ℝ => Real.log ‖faE n a θ p ((t - coff) / r)‖ - Real.log 2) := by
      have hconst : ConvexOn ℝ (Set.Ioo A B) (fun _ : ℝ => Real.log 2) :=
        convexOn_const (Real.log 2) (convex_Ioo A B)
      exact hcFt'.sub hconst
    refine hsub.congr ?_
    intro t ht
    have hq : 0 < q t := hqpos t ht.1 ht.2
    have hpos : 0 < ‖faE n a θ p ((t - coff) / r)‖ := by
      dsimp [q] at hq
      have hqlt : 0 * 2 < ‖faE n a θ p ((t - coff) / r)‖ :=
        (lt_div_iff₀ (by norm_num : 0 < (2 : ℝ))).mp hq
      simpa using hqlt
    change Real.log ‖faE n a θ p ((t - coff) / r)‖ - Real.log 2 =
      Real.log (‖faE n a θ p ((t - coff) / r)‖ / 2)
    rw [Real.log_div (ne_of_gt hpos) (by norm_num : (2 : ℝ) ≠ 0)]
  refine unimodal_of_log_concave hle q ?hqcont ?hqpos ?hlog
  · simpa [q] using hqcont
  · intro t htA htB
    have := hqpos t htA htB
    simpa [q] using this
  · simpa [q] using hcL

/-- Polar form of `faE` in the arc coordinate: on the closed t-interval
`[r·u+coff, r·v+coff]`, with `u,v` zeros of `faE` and the argument lift
affine with slope `r` on the open arc, `faE((t-coff)/r) = ‖·‖·E t`. -/
lemma arc_polar {n : ℕ} (a : ℝ) (ha : 0 ≤ a) (θ : Fin n → ℝ) (p : Fin n → ℝ)
    {u v coff r : ℝ} (hr : 0 < r)
    (hu0 : ‖faE n a θ p u‖ = 0) (hv0 : ‖faE n a θ p v‖ = 0)
    (hno : ∀ σ ∈ Set.Ioo u v, ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0)
    (haff : ∀ σ ∈ Set.Ioo u v, argLift n θ p σ = r * σ + coff)
    {t : ℝ} (htA : r * u + coff ≤ t) (htB : t ≤ r * v + coff) :
    faE n a θ p ((t - coff) / r) = ‖faE n a θ p ((t - coff) / r)‖ * E t := by
  by_cases htAe : t = r * u + coff
  · rw [htAe]
    have heq : ((r * u + coff - coff) / r) = u := by
      field_simp [ne_of_gt hr]
      ring
    rw [heq]
    have hz : faE n a θ p u = 0 := norm_eq_zero.mp hu0
    rw [hz]
    simp [hu0]
  · by_cases htBe : t = r * v + coff
    · rw [htBe]
      have heq : ((r * v + coff - coff) / r) = v := by
        field_simp [ne_of_gt hr]
        ring
      rw [heq]
      have hz : faE n a θ p v = 0 := norm_eq_zero.mp hv0
      rw [hz]
      simp [hv0]
    · -- interior
      have htAs : r * u + coff < t := lt_of_le_of_ne htA (Ne.symm htAe)
      have htBs : t < r * v + coff := lt_of_le_of_ne htB htBe
      let σ : ℝ := (t - coff) / r
      have hσu : u < σ := by
        dsimp [σ]
        rw [lt_div_iff₀ hr]
        have h1 : r * u < t - coff := by linarith
        simpa [mul_comm] using h1
      have hσv : σ < v := by
        dsimp [σ]
        rw [div_lt_iff₀ hr]
        have h1 : t - coff < r * v := by linarith
        simpa [mul_comm] using h1
      have hσm : σ ∈ Set.Ioo u v := ⟨hσu, hσv⟩
      have hne : ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0 := hno σ hσm
      have hpol := faE_polar n a ha θ p (σ := σ) hne
      have halt : argLift n θ p σ = t := by
        have h' := haff σ hσm
        dsimp [σ] at h'
        -- argLift σ = r * σ + coff = t
        rw [h']
        field_simp [ne_of_gt hr]
        ring
      have hpol' : faE n a θ p σ = ‖faE n a θ p σ‖ * E (argLift n θ p σ) := by
        simpa [argLift] using hpol
      change faE n a θ p σ = ‖faE n a θ p σ‖ * E t
      rw [← halt]
      exact hpol'

/-- Per-arc bound in σ-space: for an arc `(u,v)` whose endpoints are zeros
of `faE` and with no factor vanishing inside, the circle integral over the
arc is at least `((v-u) - 2π/N)·log 2`. -/
lemma per_arc_faE_bound {n N : ℕ} (hN : 0 < N) (a : ℝ) (ha : 0 < a)
    (θ : Fin n → ℝ) (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j)
    (hsum : (∑ j : Fin n, p j) = (N : ℝ)) {c : ℝ} (hc : c < 2)
    (hmarg : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c) {u v : ℝ} (huv : u < v)
    (hu0 : ‖faE n a θ p u‖ = 0) (hv0 : ‖faE n a θ p v‖ = 0)
    (hno : ∀ σ ∈ Set.Ioo u v, ∀ j : Fin n, (1 : ℂ) + E (σ - θ j) ≠ 0) :
    (∫ σ in u..v, circleG n a θ p σ)
      ≥ ((v - u) - (2 : ℝ) * Real.pi / (N : ℝ)) * Real.log 2 := by
  let r : ℝ := (N : ℝ) / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  -- affine offset of the argument lift on the arc
  rcases argLift_eqOn_arc θ p (u := u) (v := v) hno with ⟨coff, hcoff⟩
  have hcoff' : ∀ σ ∈ Set.Ioo u v, argLift n θ p σ = r * σ + coff := by
    intro σ hσ
    have h' := hcoff σ hσ
    have hs : ((∑ j : Fin n, p j) / 2) = r := by
      dsimp [r]
      rw [hsum]
    rw [hs] at h'
    exact h'
  let A : ℝ := r * u + coff
  let B : ℝ := r * v + coff
  let f : ℝ → ℂ := fun t : ℝ => faE n a θ p ((t - coff) / r)
  have hAB : A < B := by
    dsimp [A, B]
    have : r * u < r * v := mul_lt_mul_of_pos_left huv hr
    linarith
  have hle : A ≤ B := le_of_lt hAB
  have harg : ∀ t ∈ Set.Icc A B, f t = ‖f t‖ * E t := by
    intro t ht
    dsimp [f, A, B] at ht ⊢
    have hpt := arc_polar (n := n) a (le_of_lt ha) θ p (u := u) (v := v) (coff := coff) (r := r)
      hr hu0 hv0 hno hcoff' (t := t) ht.1 ht.2
    simpa using hpt
  have hfcont : ContinuousOn f (Set.Icc A B) := by
    dsimp [f]
    have hc1 : Continuous (fun t : ℝ => faE n a θ p ((t - coff) / r)) := by
      refine (continuous_faE n a (le_of_lt ha) θ p hp).comp ?_
      fun_prop
    exact hc1.continuousOn
  have hΦ : ∀ t ∈ Set.Icc A B, ‖f t‖ ≤ c := by
    intro t ht
    dsimp [f]
    exact hmarg ((t - coff) / r)
  have huq : ∃ m : ℝ, UnimodalOn A B m (fun t : ℝ => ‖f t‖ / 2) := by
    have hu := arc_unimodal (n := n) a ha θ p hp (u := u) (v := v) (coff := coff) (r := r)
      hr huv hno A B (by rfl) (by rfl)
    simpa [f] using hu
  have hR := per_arc_bound A B f (c := c) hle hfcont harg hΦ hc huq
  -- ∫_u^v g = (2/N) · ∫_A^B g(σfun)
  have hcontG : Continuous (fun σ : ℝ => circleG n a θ p σ) :=
    continuous_circleG (n := n) a (le_of_lt ha) θ p hp hc hmarg
  have hsubst : (∫ σ in u..v, circleG n a θ p σ) =
      (2 : ℝ) / (N : ℝ) * (∫ t in A..B, circleG n a θ p ((t - coff) / r)) := by
    -- affine_change with r0 := 2/N and c0 := -coff*(2/N)
    let r0 : ℝ := (2 : ℝ) / (N : ℝ)
    let c0 : ℝ := -coff * ((2 : ℝ) / (N : ℝ))
    have hr0 : 0 < r0 := by
      dsimp [r0]
      positivity
    have hmapA : r0 * A + c0 = u := by
      dsimp [r0, c0, A]
      field_simp [ne_of_gt hN]
      ring
    have hmapB : r0 * B + c0 = v := by
      dsimp [r0, c0, B]
      field_simp [ne_of_gt hN]
      ring
    have hsub := affine_change A B c0 (r := r0) hr0 (circleG n a θ p)
      (by simpa [hmapA, hmapB] using hcontG.continuousOn)
    -- hsub : ∫ t in r0*A+c0..r0*B+c0, g = r0 * ∫ θ in A..B, g (r0θ+c0)
    -- want ∫_u^v g = (2/N) ∫_A^B g((θ-coff)/r)
    rw [hmapA, hmapB] at hsub
    have hargr : ∀ w : ℝ, r0 * w + c0 = (w - coff) / r := by
      intro w
      dsimp [r0, c0, r]
      field_simp [ne_of_gt hN]
      ring
    have hEqInt : (∫ s in A..B, circleG n a θ p (r0 * s + c0)) =
        ∫ s in A..B, circleG n a θ p ((s - coff) / r) := by
      apply intervalIntegral.integral_congr
      intro s hs
      change circleG n a θ p (r0 * s + c0) = circleG n a θ p ((s - coff) / r)
      rw [hargr s]
    rw [hEqInt] at hsub
    -- hsub : ∫_u^v g = r0 * ∫_A^B g((θ-coff)/r)
    dsimp [r0] at hsub
    exact hsub
  -- combine
  have hG : (∫ t in A..B, circleG n a θ p ((t - coff) / r)) =
      (∫ t in A..B, Real.log ‖(2 : ℂ) - f t‖) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [f, circleG]
  rw [hsubst]
  -- ∫_u^v g = (2/N) ∫_A^B g∘σfun ≥ (2/N)((B-A) - π) log 2
  have hNpos : 0 < (N : ℝ) := by positivity
  have hscale : 0 ≤ (2 : ℝ) / (N : ℝ) := by positivity
  have hineq := mul_le_mul_of_nonneg_left hR hscale
  -- hR : ∫_A^B log‖2-f‖ ≥ (B-A-π)log2
  calc
    (2 : ℝ) / (N : ℝ) * (∫ t in A..B, circleG n a θ p ((t - coff) / r))
        ≥ (2 : ℝ) / (N : ℝ) * ((B - A) - Real.pi) * Real.log 2 := by
          rw [hG]
          nlinarith  -- since (2/N)*((B-A)-π)*log2 etc hmm careful multiplication
    _ = ((v - u) - (2 : ℝ) * Real.pi / (N : ℝ)) * Real.log 2 := by
          dsimp [A, B, r]
          ring_nf
          field_simp [ne_of_gt hN]
          ring

private lemma E_two_pi_value : E (2 * Real.pi) = 1 := by
  dsimp [E]
  have h : ((2 * Real.pi : ℝ) : ℂ) * Complex.I = (2 * (Real.pi : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [h]
  rw [Complex.exp_two_pi_mul_I]

private lemma E_zeroL : E 0 = 1 := by simp [E]

private lemma E_piL : E Real.pi = -1 := by
  dsimp [E]
  rw [Complex.exp_pi_mul_I]

/-- E of an integer multiple of 2π is 1. -/
private lemma E_zsmul_two_pi (z : ℤ) : E (z • (2 * Real.pi)) = 1 := by
  have hper : Function.Periodic (fun t : ℝ => E t) (2 * Real.pi) := fun t => E_two_pi_periodic t
  have hz := hper.zsmul z
  calc
    E (z • (2 * Real.pi)) = E (0 + z • (2 * Real.pi)) := by simp
    _ = E 0 := hz 0
    _ = 1 := E_zeroL

/-- E of a real integer multiple of 2π is 1. -/
private lemma E_int_mul_two_pi (z : ℤ) : E ((z : ℝ) * (2 * Real.pi)) = 1 := by
  rw [← zsmul_eq_mul (a := (2 * Real.pi : ℝ)) z]
  exact E_zsmul_two_pi z

/-- `E x = 1` iff `x` is an integer multiple of `2π`. -/
private lemma E_eq_one_iff_int (y : ℝ) : E y = 1 ↔ ∃ z : ℤ, y = (z : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    dsimp [E] at h
    rcases Complex.exp_eq_one_iff.mp h with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hz'' : (y : ℂ) * Complex.I = ((z : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
      rw [mul_assoc] at hz
      simpa [mul_assoc] using hz
    have hz' : (y : ℂ) = (z : ℂ) * (2 * (Real.pi : ℂ)) := by
      exact mul_right_cancel₀ (by norm_num : Complex.I ≠ 0) hz''
    have hzr : y = (z : ℝ) * (2 * Real.pi) := by
      exact_mod_cast hz'
    exact hzr
  · rintro ⟨z, hz⟩
    rw [hz]
    exact E_int_mul_two_pi z

/-- `E x = -1` iff `x ≡ π (mod 2π)`. -/
private lemma E_neg_one_iff_int (x : ℝ) : E x = -1 ↔ ∃ z : ℤ, x = Real.pi + (z : ℝ) * (2 * Real.pi) := by
  constructor
  · intro hx
    have hadd : E (x - Real.pi + Real.pi) = E (x - Real.pi) * E Real.pi :=
      E_add (x - Real.pi) Real.pi
    have hx' : E (x - Real.pi + Real.pi) = -1 := by simpa using hx
    have hmain : E (x - Real.pi) * E Real.pi = -1 := hadd.symm.trans hx'
    rw [E_piL] at hmain
    have hsub : E (x - Real.pi) = 1 := by
      have h := congrArg (fun w : ℂ => -w) hmain
      simpa using h
    rcases (E_eq_one_iff_int (x - Real.pi)).mp hsub with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : x = (x - Real.pi) + Real.pi := by ring
    rw [this, hz]
    ring
  · rintro ⟨z, hz⟩
    rw [hz]
    calc
      E (Real.pi + (z : ℝ) * (2 * Real.pi)) = E Real.pi * E ((z : ℝ) * (2 * Real.pi)) := by rw [E_add]
      _ = -1 * 1 := by rw [E_piL, E_int_mul_two_pi]
      _ = -1 := by ring

/-- `1 + E φ = 0` iff `E φ = -1`. -/
private lemma factor_zero_iff_E_neg (σ θ : ℝ) : (1 : ℂ) + E (σ - θ) = 0 ↔ E (σ - θ) = -1 := by
  constructor
  · intro h
    have h' : (1 : ℂ) = -E (σ - θ) := eq_neg_of_add_eq_zero_left h
    exact neg_eq_iff_eq_neg.mp h'.symm
  · intro h
    rw [h]
    norm_num

/-- a factor vanishes exactly at jump points (positive weights) -/
private lemma factor_zero_jump {k : ℕ} (θ : Fin k → ℝ) (p : Fin k → ℝ)
    (hp : ∀ j : Fin k, 0 < p j) {σ : ℝ} {j : Fin k} (h : (1 : ℂ) + E (σ - θ j) = 0) :
    IsJump k θ p σ := by
  refine ⟨j, ?_, ?_⟩
  · exact ne_of_gt (hp j)
  · exact (factor_zero_iff_E_neg σ (θ j)).mp h

/-- positive weights: no factor zero on an interval iff no jump point in it -/
private lemma no_factor_zero_of_no_jump {k : ℕ} (θ : Fin k → ℝ) (p : Fin k → ℝ)
    (hp : ∀ j : Fin k, 0 < p j) {u v : ℝ} (hno_jump : ∀ σ ∈ Set.Ioo u v, ¬ IsJump k θ p σ) :
    ∀ σ ∈ Set.Ioo u v, ∀ j : Fin k, (1 : ℂ) + E (σ - θ j) ≠ 0 := by
  intro σ hσ j hj
  exact hno_jump σ hσ (factor_zero_jump θ p hp (σ := σ) (j := j) hj)

/-- If `b` is the minimum of the jump set `S` inside `(current, END)`, then no
factor vanishes on `(current,b)`. -/
private lemma no_jump_before_min {k : ℕ} (θ : Fin k → ℝ) (p : Fin k → ℝ)
    (hp : ∀ j : Fin k, 0 < p j) {current END : ℝ} {S : Finset ℝ} (hne : S.Nonempty)
    (hS : ∀ x : ℝ, x ∈ S ↔ IsJump k θ p x ∧ current < x ∧ x < END) :
    ∀ σ ∈ Set.Ioo current (S.min' hne), ∀ j : Fin k, (1 : ℂ) + E (σ - θ j) ≠ 0 := by
  apply no_factor_zero_of_no_jump θ p hp
  intro σ hσ hj
  have hb : S.min' hne < END := ((hS (S.min' hne)).1 (S.min'_mem hne)).2.2
  have hSσ : σ ∈ S := (hS σ).2 ⟨hj, hσ.1, lt_trans hσ.2 hb⟩
  exact (not_lt_of_ge ((S.isLeast_min' hne).2 hSσ)) hσ.2

/-- Recursive per-domain bound: with jump set `S` in `(current, END)` and
`current, END` zeros of `faE`, `∫_current^END ≥ (END-current-(S.card+1)·2π/N)·log 2`. -/
private lemma domain_arcs_bound {k N : ℕ} (hN : 0 < N) (a : ℝ) (ha : 0 < a)
    (θ : Fin k → ℝ) (p : Fin k → ℝ) (hp : ∀ j : Fin k, 0 < p j)
    (hsum : (∑ j : Fin k, p j) = (N : ℝ)) {c : ℝ} (hc : c < 2)
    (hmarg : ∀ σ : ℝ, ‖faE k a θ p σ‖ ≤ c)
    {current END : ℝ} (hcur0 : ‖faE k a θ p current‖ = 0) (hEND0 : ‖faE k a θ p END‖ = 0)
    (hlt : current < END) (S : Finset ℝ)
    (hS : ∀ x : ℝ, x ∈ S ↔ IsJump k θ p x ∧ current < x ∧ x < END) :
    (∫ σ in current..END, circleG k a θ p σ)
      ≥ (END - current - ((S.card + 1 : ℕ) : ℝ) * ((2 : ℝ) * Real.pi / (N : ℝ))) * Real.log 2 := by
  classical
  let L : ℝ := (2 : ℝ) * Real.pi / (N : ℝ)
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp0 : ∀ j : Fin k, 0 ≤ p j := fun j => le_of_lt (hp j)
  have hcont : Continuous (fun σ : ℝ => circleG k a θ p σ) :=
    continuous_circleG (n := k) a (le_of_lt ha) θ p hp0 hc hmarg
  have hmain : ∀ (m : ℕ), ∀ (current END : ℝ) (S : Finset ℝ),
      S.card = m →
      ‖faE k a θ p current‖ = 0 → ‖faE k a θ p END‖ = 0 → current < END →
      (∀ x : ℝ, x ∈ S ↔ IsJump k θ p x ∧ current < x ∧ x < END) →
      (∫ σ in current..END, circleG k a θ p σ)
        ≥ (END - current - ((S.card + 1 : ℕ) : ℝ) * L) * Real.log 2 := by
    intro m
    refine Nat.strong_induction_on m ?_
    intro m ih current END S hcard hcur0' hEND0' hlt' hS'
    by_cases hSempty : S = ∅
    · have hmem : S.card = 0 := by rw [hSempty]; simp
      have hno_j : ∀ σ ∈ Set.Ioo current END, ¬ IsJump k θ p σ := by
        intro σ hσ hj
        have hSσ : σ ∈ S := (hS' σ).2 ⟨hj, hσ.1, hσ.2⟩
        rw [hSempty] at hSσ
        simpa using hSσ
      have hno := no_factor_zero_of_no_jump θ p hp (u := current) (v := END) hno_j
      have hR := per_arc_faE_bound (n := k) (N := N) hN a ha θ p hp0 hsum (c := c) hc hmarg
        (u := current) (v := END) hlt' hcur0' hEND0' hno
      have hR' : (∫ σ in current..END, circleG k a θ p σ)
          ≥ (END - current - ((S.card + 1 : ℕ) : ℝ) * L) * Real.log 2 := by
        have hsc : ((S.card + 1 : ℕ) : ℝ) * L = L := by
          rw [hmem]
          simp [L]
        rw [hsc]
        simpa [L] using hR
      exact hR'
    · have hne : S.Nonempty := (Finset.nonempty_iff_ne_empty).2 hSempty
      let b : ℝ := S.min' hne
      have hbmem : b ∈ S := by
        dsimp [b]
        exact S.min'_mem hne
      have hSb : IsJump k θ p b ∧ current < b ∧ b < END := (hS' b).1 hbmem
      have hcurb : current < b := hSb.2.1
      have hb0 : ‖faE k a θ p b‖ = 0 := norm_faE_zero_of_jump k a θ p hSb.1
      have hno1 := no_jump_before_min θ p hp (current := current) (END := END) (S := S) hne hS'
      have hArc := per_arc_faE_bound (n := k) (N := N) hN a ha θ p hp0 hsum (c := c) hc hmarg
        (u := current) (v := b) hcurb hcur0' hb0 hno1
      have hcarderase : (S.erase b).card < m := by
        have hltc : (S.erase b).card < S.card := Finset.card_erase_lt_of_mem hbmem
        rwa [← hcard]
      have hS2 : ∀ x : ℝ, x ∈ S.erase b ↔ IsJump k θ p x ∧ b < x ∧ x < END := by
        intro x
        constructor
        · intro hx
          have hx1 : x ∈ S := Finset.mem_of_mem_erase hx
          have hx2 : x ≠ b := Finset.ne_of_mem_erase hx
          have hxS : IsJump k θ p x ∧ current < x ∧ x < END := (hS' x).1 hx1
          have hbmin : b ≤ x := by
            dsimp [b]
            exact (S.isLeast_min' hne).2 hx1
          have hb_lt : b < x := lt_of_le_of_ne hbmin (Ne.symm hx2)
          exact ⟨hxS.1, hb_lt, hxS.2.2⟩
        · intro hx
          have hxS : IsJump k θ p x ∧ b < x ∧ x < END := hx
          have hmem' : x ∈ S := (hS' x).2 ⟨hxS.1, lt_trans hcurb hxS.2.1, hxS.2.2⟩
          exact Finset.mem_erase.mpr ⟨ne_of_gt hxS.2.1, hmem'⟩
      have ihR := ih (S.erase b).card hcarderase b END (S.erase b) rfl hb0 hEND0'
        hSb.2.2 hS2
      have hb_END : b < END := hSb.2.2
      have h_int1 : IntervalIntegrable (fun σ : ℝ => circleG k a θ p σ) volume current b :=
        hcont.intervalIntegrable current b
      have h_int2 : IntervalIntegrable (fun σ : ℝ => circleG k a θ p σ) volume b END :=
        hcont.intervalIntegrable b END
      have hsplit : (∫ σ in current..END, circleG k a θ p σ) =
          (∫ σ in current..b, circleG k a θ p σ) +
            (∫ σ in b..END, circleG k a θ p σ) := by
        exact (intervalIntegral.integral_add_adjacent_intervals h_int1 h_int2).symm
      have hcardAdd : ((S.erase b).card + 1 : ℕ) = S.card := by
        have hc1 : (S.erase b).card = S.card - 1 := Finset.card_erase_of_mem hbmem
        have hpos : 0 < S.card := (Finset.card_pos).2 hne
        omega
      calc
        (∫ σ in current..END, circleG k a θ p σ)
            = (∫ σ in current..b, circleG k a θ p σ) +
              (∫ σ in b..END, circleG k a θ p σ) := hsplit
        _ ≥ (b - current - L) * Real.log 2 +
              (END - b - (((S.erase b).card + 1 : ℕ) : ℝ) * L) * Real.log 2 := by
                exact add_le_add hArc ihR
        _ = (END - current - ((S.card + 1 : ℕ) : ℝ) * L) * Real.log 2 := by
                have hca : (((S.erase b).card + 1 : ℕ) : ℝ) = (S.card : ℝ) := by
                  exact_mod_cast hcardAdd
                rw [hca]
                norm_num
                ring
  exact hmain S.card current END S rfl hcur0 hEND0 hlt hS

/-- A jump point inside the fundamental domain is its own representative. -/
private lemma jump_mem_image {k : ℕ} (θ : Fin k → ℝ) (p : Fin k → ℝ)
    {l₀ x : ℝ} (j : Fin k) (hx : l₀ ≤ x) (hx2 : x < l₀ + 2 * Real.pi)
    (hjump : E (x - θ j) = -1) :
    x ∈ (Finset.univ.image (fun i : Fin k => toIcoMod Real.two_pi_pos l₀ (θ i + Real.pi)) : Finset ℝ) := by
  have hmod : toIcoMod Real.two_pi_pos l₀ (θ j + Real.pi) = x := by
    rw [toIcoMod_eq_iff]
    constructor
    · exact ⟨hx, hx2⟩
    · rcases (E_neg_one_iff_int (x - θ j)).mp hjump with ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      calc
        θ j + Real.pi = x - (x - θ j) + Real.pi := by ring
        _ = x - (Real.pi + (z : ℝ) * (2 * Real.pi)) + Real.pi := by rw [hz]
        _ = x + (-(z : ℝ)) * (2 * Real.pi) := by ring
        _ = x + (-z : ℤ) • (2 * Real.pi) := by
          rw [zsmul_eq_mul]
          norm_num
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hmod⟩

/-- Every representative `toIcoMod l₀ (θ_j + π)` is a jump point in the
half-open fundamental domain. -/
private lemma image_mem_jump {k : ℕ} (θ : Fin k → ℝ) (p : Fin k → ℝ)
    (hp : ∀ j : Fin k, 0 < p j) {l₀ : ℝ} (j : Fin k) :
    IsJump k θ p (toIcoMod Real.two_pi_pos l₀ (θ j + Real.pi)) := by
  let rep : ℝ := toIcoMod Real.two_pi_pos l₀ (θ j + Real.pi)
  let z : ℤ := toIcoDiv Real.two_pi_pos l₀ (θ j + Real.pi)
  have hrel : rep + z • (2 * Real.pi) = θ j + Real.pi := by
    dsimp [rep, z]
    exact toIcoMod_add_toIcoDiv_zsmul Real.two_pi_pos l₀ (θ j + Real.pi)
  have hrep_eq : rep = θ j + Real.pi - z • (2 * Real.pi) := by
    calc
      rep = (rep + z • (2 * Real.pi)) - z • (2 * Real.pi) := by ring
      _ = (θ j + Real.pi) - z • (2 * Real.pi) := by rw [hrel]
  have hsub : rep - θ j = Real.pi - z • (2 * Real.pi) := by
    calc
      rep - θ j = (θ j + Real.pi - z • (2 * Real.pi)) - θ j := by rw [hrep_eq]
      _ = Real.pi - z • (2 * Real.pi) := by ring
  refine ⟨j, ne_of_gt (hp j), ?_⟩
  calc
    E (rep - θ j) = E (Real.pi - z • (2 * Real.pi)) := by rw [hsub]
    _ = E (Real.pi + (-z) • (2 * Real.pi)) := by
        congr 1
        rw [sub_eq_add_neg, neg_smul]
    _ = E Real.pi * E ((-z) • (2 * Real.pi)) := by rw [E_add]
    _ = -1 * 1 := by rw [E_piL, E_zsmul_two_pi (-z)]
    _ = -1 := by ring

/-- The main lemma in the all-positive-weight case. -/
private lemma circle_mean_nonneg_pos {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N)
    (a : ℝ) (ha : 0 ≤ a) (θ : Fin k → ℝ) (p : Fin k → ℝ) (hp : ∀ j : Fin k, 0 < p j)
    (hsum : (∑ j : Fin k, p j) = (N : ℝ)) {c : ℝ} (hc : c < 2)
    (hmarg : ∀ σ : ℝ, ‖faE k a θ p σ‖ ≤ c) :
    0 ≤ ∫ σ in 0..2 * Real.pi, circleG k a θ p σ := by
  classical
  by_cases ha0 : a = 0
  · -- faE ≡ 0; integrand is log 2
    have hval : ∀ σ : ℝ, circleG k 0 θ p σ = Real.log 2 := by
      intro σ
      dsimp [circleG]
      have hfa : faE k 0 θ p σ = 0 := by
        rw [faE_eq]
        simp
      rw [hfa]
      norm_num
    have hcst : (∫ σ in 0..2 * Real.pi, Real.log 2) = (2 * Real.pi) * Real.log 2 := by
      rw [intervalIntegral.integral_const]
      ring
    rw [ha0]
    have hcc : (∫ σ in 0..2 * Real.pi, circleG k 0 θ p σ) = (2 * Real.pi) * Real.log 2 := by
      calc
        (∫ σ in 0..2 * Real.pi, circleG k 0 θ p σ) = ∫ σ in 0..2 * Real.pi, Real.log 2 := by
          apply intervalIntegral.integral_congr
          intro σ hσ
          exact hval σ
        _ = (2 * Real.pi) * Real.log 2 := by
          rw [intervalIntegral.integral_const]
          ring
    rw [hcc]
    positivity
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let j0 : Fin k := ⟨0, hk⟩
    let l₀ : ℝ := θ j0 + Real.pi
    let J : Finset ℝ := (Finset.univ : Finset (Fin k)).image
      (fun j : Fin k => toIcoMod Real.two_pi_pos l₀ (θ j + Real.pi))
    let S0 : Finset ℝ := J.erase l₀
    let END : ℝ := l₀ + 2 * Real.pi
    have hN : 0 < N := by
      have hsumpos : 0 < (∑ j : Fin k, p j) := by
        have hterm : 0 < p j0 := hp j0
        have hsum_ge : p j0 ≤ ∑ j : Fin k, p j := by
          exact Finset.single_le_sum (fun j hj => le_of_lt (hp j)) (Finset.mem_univ j0)
        linarith
      have : 0 < (N : ℝ) := by
        rw [← hsum]
        exact hsumpos
      exact_mod_cast this
    -- l₀ is a jump (index j0)
    have hl0jump : IsJump k θ p l₀ := by
      refine ⟨j0, ne_of_gt (hp j0), ?_⟩
      have : l₀ - θ j0 = Real.pi := by dsimp [l₀]; ring
      rw [this]
      exact E_piL
    have hl0_0 : ‖faE k a θ p l₀‖ = 0 := norm_faE_zero_of_jump k a θ p hl0jump
    have hEND0 : ‖faE k a θ p END‖ = 0 := by
      dsimp [END]
      rw [faE_periodic]
      exact hl0_0
    have hlt : l₀ < END := by
      dsimp [END]
      linarith [Real.two_pi_pos]
    have hS_init : ∀ x : ℝ, x ∈ S0 ↔ IsJump k θ p x ∧ l₀ < x ∧ x < END := by
      intro x
      constructor
      · intro hx
        have hxJ : x ∈ J := Finset.mem_of_mem_erase hx
        have hxne : x ≠ l₀ := Finset.ne_of_mem_erase hx
        rcases Finset.mem_image.mp hxJ with ⟨j, hjmem, hxj⟩
        have hxj' : toIcoMod Real.two_pi_pos l₀ (θ j + Real.pi) = x := hxj
        have hIco : x ∈ Set.Ico l₀ (l₀ + 2 * Real.pi) := by
          rw [← hxj']
          exact toIcoMod_mem_Ico Real.two_pi_pos l₀ (θ j + Real.pi)
        have hge : l₀ ≤ x := (Set.mem_Ico.mp hIco).1
        have hltEND : x < END := by
          dsimp [END]
          exact (Set.mem_Ico.mp hIco).2
        have hlt_l0 : l₀ < x := lt_of_le_of_ne hge hxne.symm
        have hjx : IsJump k θ p x := by
          rw [← hxj']
          exact image_mem_jump θ p hp (j := j) (l₀ := l₀)
        exact ⟨hjx, hlt_l0, hltEND⟩
      · intro hx
        rcases hx with ⟨hjump, hlt_l0, hltEND⟩
        rcases hjump with ⟨j, hpj, hE⟩
        have hxJ : x ∈ J := by
          dsimp [J]
          exact jump_mem_image θ p (j := j) (le_of_lt hlt_l0) hltEND hE
        exact Finset.mem_erase.mpr ⟨ne_of_gt hlt_l0, hxJ⟩
    have hbound := domain_arcs_bound (k := k) (N := N) hN a hapos θ p hp hsum
      (c := c) hc hmarg (current := l₀) (END := END) hl0_0 hEND0 hlt S0 hS_init
    -- m = J.card
    have hl0J : l₀ ∈ J := by
      dsimp [J]
      exact Finset.mem_image.mpr ⟨j0, Finset.mem_univ j0, by
        dsimp [l₀, j0]
        exact toIcoMod_apply_left Real.two_pi_pos (θ ⟨0, hk⟩ + Real.pi)⟩
    have hS0card : S0.card = J.card - 1 := by
      dsimp [S0]
      exact Finset.card_erase_of_mem hl0J
    have hposJ : 0 < J.card := (Finset.card_pos).2 ⟨l₀, hl0J⟩
    have hcardEq : ((S0.card + 1 : ℕ) : ℝ) = (J.card : ℝ) := by
      have : S0.card + 1 = J.card := by
        rw [hS0card]
        omega
      exact_mod_cast this
    have hJleK : J.card ≤ k := by
      dsimp [J]
      have h1 : (Finset.univ.image (fun j : Fin k => toIcoMod Real.two_pi_pos l₀ (θ j + Real.pi))).card
          ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      simpa using h1
    have hJleN : (J.card : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_trans hJleK hkN)
    have hlen : END - l₀ = 2 * Real.pi := by
      dsimp [END]
      ring
    -- simplify the RHS of hbound
    have hI : (∫ σ in l₀..END, circleG k a θ p σ)
        ≥ (2 * Real.pi - (J.card : ℝ) * ((2 : ℝ) * Real.pi / (N : ℝ))) * Real.log 2 := by
      have hb := hbound
      rw [hcardEq, hlen] at hb
      simpa using hb
    have hRN : 0 ≤ (2 * Real.pi - (J.card : ℝ) * ((2 : ℝ) * Real.pi / (N : ℝ))) * Real.log 2 := by
      have hlog : 0 ≤ Real.log 2 := le_of_lt (Real.log_pos (by norm_num))
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
      have hbase : 0 ≤ 2 * Real.pi - (J.card : ℝ) * ((2 : ℝ) * Real.pi / (N : ℝ)) := by
        have hle' : (J.card : ℝ) * (2 * Real.pi) ≤ (N : ℝ) * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hJleN (by positivity)
        have hb2 : 0 ≤ (N : ℝ) * (2 * Real.pi) - (J.card : ℝ) * (2 * Real.pi) := by
          linarith
        have heq : 2 * Real.pi - (J.card : ℝ) * ((2 : ℝ) * Real.pi / (N : ℝ)) =
            ((N : ℝ) * (2 * Real.pi) - (J.card : ℝ) * (2 * Real.pi)) / (N : ℝ) := by
          field_simp [hNpos.ne']
        rw [heq]
        exact div_nonneg hb2 (le_of_lt hNpos)
      exact mul_nonneg hbase hlog
    have hzero_le : 0 ≤ ∫ σ in l₀..END, circleG k a θ p σ := by
      exact le_trans hRN hI
    -- relate to the [0,2π] domain
    have hper : Function.Periodic (circleG k a θ p) (2 * Real.pi) := by
      intro σ
      dsimp [circleG]
      rw [faE_periodic]
    have hdom : (∫ σ in 0..2 * Real.pi, circleG k a θ p σ) =
        ∫ σ in l₀..END, circleG k a θ p σ := by
      have h := hper.intervalIntegral_add_eq l₀ 0
      -- h : ∫_{l₀}^{l₀ + 2π} g = ∫_0^{0+2π} g
      dsimp [END] at h ⊢
      simpa using h.symm
    rw [hdom]
    exact hzero_le

/-- General case (nonnegative weights): reduce to all-positive weights and use
`circle_mean_nonneg_pos`. -/
private lemma circle_mean_nonneg_general (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a)
    (θ : Fin n → ℝ) (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j)
    (hsum : (∑ j : Fin n, p j) = (n : ℝ)) {c : ℝ} (hc : c < 2)
    (hmarg : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c) :
    0 ≤ ∫ σ in 0..2 * Real.pi, circleG n a θ p σ := by
  classical
  let B : Finset (Fin n) := (Finset.univ : Finset (Fin n)).filter (fun j : Fin n => p j ≠ 0)
  let m : ℕ := B.card
  have hBmem : ∀ j : Fin n, j ∈ B ↔ p j ≠ 0 := by
    intro j
    dsimp [B]
    simp
  have hmpos : 0 < m := by
    have hsome : ∃ j : Fin n, p j ≠ 0 := by
      by_contra h
      push_neg at h
      have hzero : (∑ j : Fin n, p j) = 0 := by simp [h]
      have hsum0 : (n : ℝ) = 0 := by rw [← hsum, hzero]
      have hn0 : n = 0 := by exact_mod_cast hsum0
      exact (by omega : ¬ n = 0) hn0
    rcases hsome with ⟨j, hpj⟩
    dsimp [m]
    exact (Finset.card_pos).2 ⟨j, (hBmem j).2 hpj⟩
  have hmn : m ≤ n := by
    dsimp [m]
    have h1 : B.card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (s := B) (t := (Finset.univ : Finset (Fin n))) (by intro x hx; simp)
    simpa using h1
  let e : Fin m ↪o Fin n := B.orderEmbOfFin (by dsimp [m])
  let θ' : Fin m → ℝ := fun i : Fin m => θ (e i)
  let p' : Fin m → ℝ := fun i : Fin m => p (e i)
  have he_mem : ∀ i : Fin m, e i ∈ B := by
    intro i
    dsimp [e]
    exact B.orderEmbOfFin_mem (by dsimp [m]) i
  have hp' : ∀ i : Fin m, 0 < p' i := by
    intro i
    dsimp [p', e]
    have hpi : 0 ≤ p (B.orderEmbOfFin (by dsimp [m]) i) := hp _
    have hne : p (B.orderEmbOfFin (by dsimp [m]) i) ≠ 0 := (hBmem _).1 (B.orderEmbOfFin_mem (by dsimp [m]) i)
    exact lt_of_le_of_ne hpi (Ne.symm hne)
  have himage : (Finset.univ : Finset (Fin m)).image (fun i : Fin m => e i) = B := by
    dsimp [e, m]
    simp
  have hsum' : (∑ i : Fin m, p' i) = (n : ℝ) := by
    dsimp [p']
    have hstep1 : (∑ i : Fin m, p (e i)) =
        ∑ j ∈ (Finset.univ : Finset (Fin m)).image (fun i : Fin m => e i), p j := by
      rw [Finset.sum_image]
      exact (B.orderEmbOfFin (by dsimp [m])).injective.injOn
    rw [hstep1, himage]
    have hBc : (∑ j ∈ Bᶜ, p j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjB : j ∉ B := (Finset.mem_compl).mp hj
      have hp0 : p j = 0 := by
        by_contra h
        exact hjB ((hBmem j).2 h)
      rw [hp0]
    have hsplit := Finset.sum_compl_add_sum B p
    have hBsum : (∑ j ∈ B, p j) = ∑ j : Fin n, p j := by
      have : (∑ j ∈ Bᶜ, p j) + (∑ j ∈ B, p j) = ∑ j : Fin n, p j := hsplit
      simpa [hBc] using this
    rw [hBsum, hsum]
  have hfa_eq : ∀ σ : ℝ, faE n a θ p σ = faE m a θ' p' σ := by
    intro σ
    rw [faE_eq, faE_eq]
    congr 1
    let f : Fin n → ℂ := fun j : Fin n => cPow (1 + E (σ - θ j)) (p j)
    let g : Fin m → ℂ := fun i : Fin m => cPow (1 + E (σ - θ' i)) (p' i)
    have hge : ∀ i : Fin m, g i = f (e i) := by
      intro i
      dsimp [g, f, θ', p']
    calc
      (∏ j : Fin n, f j) = ∏ j ∈ B, f j := by
        have hBc : (∏ j ∈ Bᶜ, f j) = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          have hjB : j ∉ B := (Finset.mem_compl).mp hj
          have hp0 : p j = 0 := by
            by_contra h
            exact hjB ((hBmem j).2 h)
          dsimp [f]
          rw [hp0]
          simp [cPow]
        have hsplit := Finset.prod_mul_prod_compl B f
        have hBres : (∏ j ∈ B, f j) * 1 = ∏ j : Fin n, f j := by
          simpa [hBc] using hsplit
        have hres : (∏ j ∈ B, f j) = ∏ j : Fin n, f j := by
          simpa using hBres
        exact hres.symm
      _ = ∏ j ∈ (Finset.univ : Finset (Fin m)).image (fun i : Fin m => e i), f j := by
        rw [← himage]
      _ = ∏ i : Fin m, f (e i) := by
        rw [Finset.prod_image]
        exact (B.orderEmbOfFin (by dsimp [m])).injective.injOn
      _ = ∏ i : Fin m, g i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact (hge i).symm
  have hmar' : ∀ σ : ℝ, ‖faE m a θ' p' σ‖ ≤ c := by
    intro σ
    rw [← hfa_eq σ]
    exact hmarg σ
  have hpos := circle_mean_nonneg_pos (k := m) (N := n) hmpos hmn a ha θ' p' hp' hsum'
    (c := c) hc hmar'
  have hIeq : (∫ σ in 0..2 * Real.pi, circleG m a θ' p' σ) =
      ∫ σ in 0..2 * Real.pi, circleG n a θ p σ := by
    apply intervalIntegral.integral_congr
    intro σ hσ
    dsimp [circleG]
    rw [hfa_eq σ]
  calc
    0 ≤ ∫ σ in 0..2 * Real.pi, circleG m a θ' p' σ := hpos
    _ = ∫ σ in 0..2 * Real.pi, circleG n a θ p σ := hIeq

/-- **Circle mean ≥ 0 (F5).**  For circle points `z_j := E(θ_j)`, weights
`p_j ≥ 0` summing to `n ≥ 1`, `a ≥ 0`, if `‖faE n a θ p σ‖ ≤ c` for all
`σ` with `c < 2` (uniform margin), then
`∫_0^{2π} log‖2 − faE n a θ p σ‖ dσ ≥ 0`. -/
theorem circle_mean_nonneg (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 ≤ a)
    (θ : Fin n → ℝ) (p : Fin n → ℝ) (hp : ∀ j : Fin n, 0 ≤ p j)
    (hsum : (∑ j : Fin n, p j) = (n : ℝ)) {c : ℝ} (hc : c < 2)
    (hmarg : ∀ σ : ℝ, ‖faE n a θ p σ‖ ≤ c) :
    0 ≤ ∫ σ in 0..2 * Real.pi, Real.log ‖(2 : ℂ) - faE n a θ p σ‖ := by
  classical
  change 0 ≤ ∫ σ in 0..2 * Real.pi, circleG n a θ p σ
  exact circle_mean_nonneg_general n hn a ha θ p hp hsum (c := c) hc hmarg

end Submission.CoreB

end
