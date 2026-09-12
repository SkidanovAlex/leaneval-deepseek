import Submission.MarkovInterval
import Submission.SerreExample
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Division by a linear factor costs a polynomial factor (unweighted)

**Lemma (interval form of Smith's `lem:Remez`, unweighted)**: for
`α ∈ [aSerre,bSerre]` and a real polynomial `P` of degree `m ≥ 1` with
`P = (X − C α)·Q`, the sup-norm of `Q` over the Serre interval is bounded by
a polynomial (in `m`) times the sup-norm of `P`:

    supNorm Q ≤ (16·m²/(bSerre−aSerre)) · supNorm P

## Proof (self-contained; uses Markov's inequality only)

Let `‖·‖` denote sup over `[aSerre,bSerre]`, `L := bSerre−aSerre`, `d := L/(8m²)`.
Split `[aSerre,bSerre]` at distance `d` from `α`:

* outside (`|x−α| ≥ d`): `|Q(x)| = |P(x)|/|x−α| ≤ ‖P‖/d` (direct);
* inside (`|x−α| < d`): let `x*` attain the sup `A := ‖Q‖`.  If `x*` is
  outside, `A ≤ ‖P‖/d`.  Otherwise walk from `x*` in the direction away from
  `α` to a point `y ∈ [aSerre,bSerre]` with `|y−α| ≥ d` and `|x*−y| ≤ 2d`
  (possible because `α ∈ [aSerre,bSerre]` and `d ≤ L/8`); then
  `A = |Q(x*)| ≤ |Q(y)| + |x*−y|·sup|Q'| ≤ ‖P‖/d + 2d·(2(m−1)²/L)·A`,
  so `A ≤ ‖P‖/d + A/2` and `A ≤ 2‖P‖/d = 16m²‖P‖/L`.
-/

noncomputable section

open scoped Real
open Polynomial

namespace Submission.DivLinear

open Submission.SerreExample
open Submission.MarkovInterval

/-- Sup-norm of a real polynomial on the Serre interval. -/
noncomputable def supNorm (P : Polynomial ℝ) : ℝ :=
  sSup ((fun x : ℝ => |P.eval x|) '' Set.Icc aSerre bSerre)

private lemma cont_abs_eval (P : Polynomial ℝ) :
    Continuous (fun x : ℝ => |P.eval x|) := by
  have h : Continuous (fun x : ℝ => Polynomial.aeval x P) :=
    Polynomial.continuous_aeval (p := P)
  have hh : (fun x : ℝ => Polynomial.aeval x P) = (fun x : ℝ => P.eval x) := by
    funext x
    rw [Polynomial.aeval_def]
    simp
  simpa [hh] using h.abs

private lemma img_bddAbove (P : Polynomial ℝ) :
    BddAbove ((fun x : ℝ => |P.eval x|) '' Set.Icc aSerre bSerre) := by
  exact (isCompact_Icc.image_of_continuousOn (cont_abs_eval P).continuousOn).bddAbove

private lemma img_nonempty (P : Polynomial ℝ) :
    ((fun x : ℝ => |P.eval x|) '' Set.Icc aSerre bSerre).Nonempty := by
  exact ⟨|P.eval aSerre|, ⟨aSerre, ⟨le_rfl, a_le_b⟩, rfl⟩⟩

/-- Sup-norm bounds |P| pointwise. -/
lemma abs_eval_le_supNorm {P : Polynomial ℝ} (x : ℝ) (hx : x ∈ Set.Icc aSerre bSerre) :
    |P.eval x| ≤ supNorm P := by
  unfold supNorm
  exact le_csSup_of_le (img_bddAbove P) ⟨x, hx, rfl⟩ le_rfl

/-- supNorm is nonnegative. -/
lemma supNorm_nonneg (P : Polynomial ℝ) : 0 ≤ supNorm P := by
  exact (abs_nonneg (P.eval aSerre)).trans (abs_eval_le_supNorm (P := P) aSerre (by
    constructor <;> linarith [aSerre_pos, a_lt_b]))

/-- The sup-norm is an upper bound of the pointwise values (reverse direction). -/
lemma supNorm_le_iff {P : Polynomial ℝ} {M : ℝ} :
    supNorm P ≤ M ↔ ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |P.eval x| ≤ M := by
  unfold supNorm
  constructor
  · intro h x hx
    exact (abs_eval_le_supNorm (P := P) x hx).trans h
  · intro h
    exact csSup_le (img_nonempty P) (by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact h x hx)


/-- evaluation of the factorization pointwise -/
private lemma hfac_eval_iff {P Q : Polynomial ℝ} {α : ℝ}
    (hfac : P = (Polynomial.X - Polynomial.C α) * Q) (x : ℝ) :
    P.eval x = (x - α) * Q.eval x := by
  rw [hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- far-from-α points: |Q(x)| = |P(x)|/|x−α| is controlled by the sup of P -/
private lemma q_bound_outside {P Q : Polynomial ℝ} {x α d : ℝ}
    (hfac : P = (Polynomial.X - Polynomial.C α) * Q)
    (hx : x ∈ Set.Icc aSerre bSerre) (hdpos : 0 < d) (hd : d ≤ |x - α|) :
    |Q.eval x| ≤ supNorm P / d := by
  have hxane_pos : 0 < |x - α| := lt_of_lt_of_le hdpos hd
  have hPx : P.eval x = (x - α) * Q.eval x := hfac_eval_iff hfac x
  have hPabs : |P.eval x| = |x - α| * |Q.eval x| := by
    rw [hPx, abs_mul]
  have hmain : |Q.eval x| ≤ |P.eval x| / |x - α| := by
    rw [le_div_iff₀ hxane_pos]
    rw [hPabs, mul_comm]
  have h2 : |P.eval x| / |x - α| ≤ |P.eval x| / d :=
    div_le_div_of_nonneg_left (abs_nonneg _) hdpos hd
  have h3 : |P.eval x| / d ≤ supNorm P / d :=
    div_le_div_of_nonneg_right (abs_eval_le_supNorm (P := P) x hx) (le_of_lt hdpos)
  exact le_trans (le_trans hmain h2) h3

/-- near-α points: walk in the direction away from α to a point y at distance ≥ d -/
private lemma far_point_away {x α d : ℝ}
    (hα : α ∈ Set.Icc aSerre bSerre) (_hx : x ∈ Set.Icc aSerre bSerre)
    (hdpos : 0 < d) (hdle : d ≤ (bSerre - aSerre) / 2) (hclose : |x - α| < d) :
    ∃ y ∈ Set.Icc aSerre bSerre, d ≤ |y - α| ∧ |x - y| ≤ 2 * d := by
  have hclose' : -d < x - α ∧ x - α < d := abs_lt.mp hclose
  by_cases hright : d ≤ bSerre - α
  · use α + d
    constructor
    · constructor
      · linarith [hα.1, hdpos]
      · linarith
    · constructor
      · have hval : |(α + d) - α| = d := by
          rw [show (α + d) - α = d by ring]
          rw [abs_of_nonneg (le_of_lt hdpos)]
        rw [hval]
      · have hsame : x - (α + d) = (x - α) - d := by ring
        have hnonpos : (x - α) - d ≤ 0 := by linarith [hclose'.2]
        have habs : |(x - α) - d| = d - (x - α) := by
          rw [abs_of_nonpos hnonpos]
          ring
        rw [hsame, habs]
        linarith [hclose'.1]
  · have hrightlt : bSerre - α < d := lt_of_not_ge hright
    use α - d
    constructor
    · constructor
      · have hleft : d ≤ α - aSerre := by
          have h2d : 2 * d ≤ bSerre - aSerre := by linarith [hdle]
          calc
            d ≤ (bSerre - aSerre) - d := by linarith
            _ ≤ (bSerre - aSerre) - (bSerre - α) := by
              have hb : bSerre - α ≤ d := le_of_lt hrightlt
              linarith
            _ = α - aSerre := by ring
        linarith
      · linarith [hα.2, hdpos]
    · constructor
      · have hval : |(α - d) - α| = d := by
          rw [show (α - d) - α = -d by ring]
          rw [abs_neg, abs_of_nonneg (le_of_lt hdpos)]
        rw [hval]
      · have hsame : x - (α - d) = (x - α) + d := by ring
        have hnonneg : 0 ≤ (x - α) + d := by linarith [hclose'.1]
        rw [hsame, abs_of_nonneg hnonneg]
        linarith [hclose'.2]

/-- Markov's inequality makes |Q(u)−Q(v)| ≤ (2m²/L)·‖Q‖·|u−v| on the interval -/
private lemma q_lipschitz {Q : Polynomial ℝ} {m : ℕ} (hdegQ : Q.natDegree ≤ m)
    {u v : ℝ} (hu : u ∈ Set.Icc aSerre bSerre) (hv : v ∈ Set.Icc aSerre bSerre) :
    |Q.eval u - Q.eval v| ≤
      ((2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm Q) * |u - v| := by
  let f : ℝ → ℝ := fun x => Q.eval x
  let C : ℝ := (2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm Q
  have hbdQ : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x| ≤ supNorm Q := by
    intro x hx
    exact abs_eval_le_supNorm (P := Q) x hx
  have hdiff : ∀ x ∈ Set.Icc aSerre bSerre, DifferentiableAt ℝ f x := by
    intro x hx
    dsimp [f]
    exact (Polynomial.hasDerivAt Q x).differentiableAt
  have hbound : ∀ x ∈ Set.Icc aSerre bSerre, ‖deriv f x‖ ≤ C := by
    intro x hx
    dsimp [f, C]
    have hM := markov_interval (P := Q) (n := m) hdegQ (supNorm_nonneg Q) hbdQ x hx
    rw [Polynomial.deriv]
    simpa [Real.norm_eq_abs] using hM
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ) (f := f)
    (s := Set.Icc aSerre bSerre) (x := u) (y := v) (C := C) hdiff hbound
    (convex_Icc aSerre bSerre) hu hv
  dsimp [f, C] at hmain
  simpa [Real.norm_eq_abs, abs_sub_comm] using hmain
/-- Division-by-linear-factor bound: `‖Q‖ ≤ (16m²/L)·‖P‖` for
`P = (X−Cα)·Q`, `deg P = m ≥ 1`, `α ∈ [aSerre,bSerre]`.

Proof sketch (fill in; `L := bSerre - aSerre`, `d := L / (8 * m^2)`):
1. `hfac` gives `∀ x, P.eval x = (x - α) * Q.eval x` (`eval_sub`, `eval_mul`,
   `eval_C`, `eval_X`), so `|Q.eval x| = |P.eval x| / |x - α|` whenever
   `x ≠ α`, hence `|Q.eval x| ≤ supNorm P / d` for every
   `x ∈ Icc aSerre bSerre` with `d ≤ |x - α|` (use `div_le_iff₀`-style and
   `abs_eval_le_supNorm`).
2. `Q.natDegree ≤ m - 1` (from `hfac`, `hdeg`, `natDegree_mul` /
   `natDegree_X_sub_C`; also `Q.natDegree ≤ m` suffices for Markov).
3. Let `x* ∈ Icc aSerre bSerre` be any point with `|Q.eval x*|` close to
   `supNorm Q` (e.g. `supNorm Q - ε` or use `supNorm_le_iff`).  If
   `d ≤ |x* - α|`, step 1 bounds `|Q.eval x*| ≤ supNorm P / d`.
4. Otherwise `|x* - α| < d`.  Because `α ∈ Icc aSerre bSerre` and
   `d ≤ L/8 ≤ L/2`, choose `y ∈ Icc aSerre bSerre` on the side of `x*` away
   from `α` with `d ≤ |y - α|` and `|x* - y| ≤ 2d` (if `α - d ≥ aSerre`
   walk down to `α - d`; else walk up to `α + d`).  Then
   `|Q.eval x*| ≤ |Q.eval y| + |x* - y| * |Q.derivative.eval c|` for some
   `c` between (mean value theorem; or bound
   `|Q.eval x*| ≤ |Q.eval y| + |x* - y| * (2*(m-1)^2/L) * supNorm Q` directly
   via `markov_interval` + a Lipschitz bound `|Q.eval u - Q.eval v| ≤
   |u-v| * supNorm Q.derivative` = `Convex.norm_image_sub_le`-style).
   With `2d * (2*(m-1)^2/L) ≤ 1/2` this yields
   `supNorm Q ≤ supNorm P / d + supNorm Q / 2`, i.e. `supNorm Q ≤
   2 * supNorm P / d = (16*m^2/L) * supNorm P`.
   (Handle `x* = α` by continuity/`Q.eval α = P.derivative.eval α` via
   `derivative_mul` on `hfac`, then Markov again.)
5. Assemble with `supNorm_le_iff` (both directions) and `supNorm_nonneg` to
   keep the estimates honest.  Constants: keep `(m:ℝ)^2`, `(m-1)` as naturals
   via `norm_num`/`positivity`; do NOT be afraid to strengthen intermediate
   constants as long as the final displayed constant `16*m²/L` is reached
   (e.g. prove `supNorm Q ≤ 2 * supNorm P / d` and rewrite `d`). -/
lemma div_linear_bound {P Q : Polynomial ℝ} {α : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hdeg : P.natDegree = m) (hα : α ∈ Set.Icc aSerre bSerre)
    (hfac : P = (Polynomial.X - Polynomial.C α) * Q) :
    supNorm Q ≤ (16 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm P := by
  let d : ℝ := (bSerre - aSerre) / (8 * (m : ℝ) ^ 2)
  have hLpos : 0 < bSerre - aSerre := by norm_num [aSerre, bSerre]
  have hLne : bSerre - aSerre ≠ 0 := ne_of_gt hLpos
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmRpos : 0 < (m : ℝ) := by linarith
  have hmRne0 : (m : ℝ) ≠ 0 := ne_of_gt hmRpos
  have hm2ge1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith [hmR]
  have hm2pos : 0 < (m : ℝ) ^ 2 := sq_pos_of_ne_zero hmRne0
  have hm8pos : 0 < 8 * (m : ℝ) ^ 2 := mul_pos (by norm_num) hm2pos
  have hm8ne0 : 8 * (m : ℝ) ^ 2 ≠ 0 := ne_of_gt hm8pos
  have hdpos : 0 < d := by
    dsimp [d]
    exact div_pos hLpos hm8pos
  have hdle : d ≤ (bSerre - aSerre) / 2 := by
    have hdle' : (bSerre - aSerre) / (8 * (m : ℝ) ^ 2) ≤ (bSerre - aSerre) / 2 :=
      div_le_div_of_nonneg_left (le_of_lt hLpos) (by norm_num) (by nlinarith [hm2ge1])
    simpa [d] using hdle'
  -- degree of Q
  have hPne0 : P ≠ 0 := by
    intro hP0
    have hm0 : m = 0 := by
      calc m = P.natDegree := hdeg.symm
        _ = 0 := by rw [hP0]; simp
    omega
  have hXne : (Polynomial.X - Polynomial.C α : Polynomial ℝ) ≠ 0 :=
    (Polynomial.monic_X_sub_C α).ne_zero
  have hQne0 : Q ≠ 0 := by
    intro hQ0
    apply hPne0
    rw [hfac, hQ0]
    simp
  have hdegQ : Q.natDegree ≤ m := by
    have hsum : m = 1 + Q.natDegree := by
      calc
        m = P.natDegree := hdeg.symm
        _ = ((Polynomial.X - Polynomial.C α) * Q).natDegree := by rw [hfac]
        _ = (Polynomial.X - Polynomial.C α).natDegree + Q.natDegree :=
          Polynomial.natDegree_mul hXne hQne0
        _ = 1 + Q.natDegree := by rw [Polynomial.natDegree_X_sub_C]
    omega
  -- point x* in the interval attaining the sup of |Q|
  have hcontQ : ContinuousOn (fun x : ℝ => |Q.eval x|) (Set.Icc aSerre bSerre) :=
    ContinuousOn.mono (cont_abs_eval Q).continuousOn (Set.subset_univ _)
  have hIccne : (Set.Icc aSerre bSerre : Set ℝ).Nonempty := ⟨aSerre, le_rfl, a_le_b⟩
  obtain ⟨xs, hxsI, hxsmax⟩ := isCompact_Icc.exists_isMaxOn hIccne hcontQ
  have hxsmax' : ∀ t : ℝ, t ∈ Set.Icc aSerre bSerre → |Q.eval t| ≤ |Q.eval xs| := by
    intro t ht
    exact (isMaxOn_iff.mp hxsmax) t ht
  have hxseq : |Q.eval xs| = supNorm Q := by
    apply le_antisymm
    · exact abs_eval_le_supNorm (P := Q) xs hxsI
    · dsimp [supNorm]
      exact csSup_le (img_nonempty Q) (by
        intro b hb
        rcases hb with ⟨t, ht, rfl⟩
        exact hxsmax' t ht)
  have hrel : (16 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm P =
      2 * (supNorm P / d) := by
    dsimp [d]
    field_simp [hLne, hm8ne0]
    ring
  by_cases hfar : d ≤ |xs - α|
  · have hout : |Q.eval xs| ≤ supNorm P / d :=
      q_bound_outside (P := P) (Q := Q) (x := xs) (α := α) (d := d) hfac hxsI hdpos hfar
    have hA1 : supNorm Q ≤ supNorm P / d := by
      rw [← hxseq]
      exact hout
    rw [hrel]
    have hqd : 0 ≤ supNorm P / d := div_nonneg (supNorm_nonneg P) (le_of_lt hdpos)
    nlinarith
  · have hclose : |xs - α| < d := lt_of_not_ge hfar
    obtain ⟨y, hyI, hyd, hxy⟩ := far_point_away (x := xs) (α := α) (d := d) hα hxsI hdpos hdle hclose
    have hout_y : |Q.eval y| ≤ supNorm P / d :=
      q_bound_outside (P := P) (Q := Q) (x := y) (α := α) (d := d) hfac hyI hdpos hyd
    have hlip : |Q.eval xs - Q.eval y| ≤
        ((2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm Q) * |xs - y| :=
      q_lipschitz hdegQ hxsI hyI
    have hCnonneg : 0 ≤ (2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm Q := by
      have hc : 0 ≤ 2 * (m : ℝ) ^ 2 / (bSerre - aSerre) := by
        exact div_nonneg (by positivity) (le_of_lt hLpos)
      exact mul_nonneg hc (supNorm_nonneg Q)
    have hcoef : (2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * (2 * d) = 1 / 2 := by
      dsimp [d]
      field_simp [hLne, hm8ne0]
      ring
    have hstep : |Q.eval xs - Q.eval y| ≤ supNorm Q / 2 := by
      calc
        |Q.eval xs - Q.eval y| ≤ ((2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm Q) * |xs - y| := hlip
        _ ≤ ((2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm Q) * (2 * d) := by
          exact mul_le_mul_of_nonneg_left hxy hCnonneg
        _ = supNorm Q * (1 / 2) := by
          calc
            ((2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * supNorm Q) * (2 * d)
                = supNorm Q * ((2 * (m : ℝ) ^ 2 / (bSerre - aSerre)) * (2 * d)) := by ring
            _ = supNorm Q * (1 / 2) := by rw [hcoef]
        _ = supNorm Q / 2 := by ring
    have htri : |Q.eval xs| ≤ |Q.eval xs - Q.eval y| + |Q.eval y| := by
      calc
        |Q.eval xs| = |(Q.eval xs - Q.eval y) + Q.eval y| := by
          congr 1
          ring
        _ ≤ |Q.eval xs - Q.eval y| + |Q.eval y| := abs_add_le _ _
    have hmain2 : |Q.eval xs| ≤ supNorm Q / 2 + supNorm P / d := by
      calc
        |Q.eval xs| ≤ |Q.eval xs - Q.eval y| + |Q.eval y| := htri
        _ ≤ supNorm Q / 2 + supNorm P / d := add_le_add hstep hout_y
    have hA2 : supNorm Q ≤ supNorm P / d + supNorm Q / 2 := by
      rw [← hxseq]
      linarith
    rw [hrel]
    have hhalf : supNorm Q / 2 ≤ supNorm P / d := by linarith
    have hmul := mul_le_mul_of_nonneg_left hhalf (by norm_num : 0 ≤ (2 : ℝ))
    have h2 : 2 * (supNorm Q / 2) = supNorm Q := by ring
    rwa [h2] at hmul
end Submission.DivLinear
