import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.HasLoj.Reductions
import Submission.Work.WilE3.Loj.loj_of_gradient_bound
import Submission.Work.WilE3.eaEval_analytic

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor: the elementary reduction lemmas of the
  Łojasiewicz development.

  This module is the low half of `Submission/Work/WilE3/Taylor/hasLoj_of_multiplicity.lean`
  (split out of it because the workspace build guard caps a module at 30 KB).  It contains

  * `hasLoj_sq` — the `Φ ↦ Φ²` reduction (so `(SINGLE)` may be assumed for `Φ ≥ 0`);
  * `radMinor`, `eaEval_radMinor` — the radial polar minors;
  * `hasLoj_of_leading_bound` — the case of a *definite* leading form;
  * `hasLoj_of_gradient_bound` — the integration step of Gabrielov 1995, p. 15, in the
    exponent form used by `(SINGLE)`;
  * `hasLoj_single_of_gradient` — `(SINGLE)` from the (unrestricted) effective gradient
    inequality; retained as a true implication, but superseded by
    `Work.WilE3.Taylor.ea_grad_of_multiplicity`, whose statement carries the *necessary*
    hypothesis `Φ y = 0`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor

variable {k r : ℕ}

/-- **The `Φ ↦ Φ²` reduction.**  `eaEval c (Φ ^ 2) x = (eaEval c Φ x) ^ 2` and
`{Φ ^ 2 = 0} = {Φ = 0}`, so `|Φ| ≥ C · d ^ q` near `y` iff `|Φ²| ≥ C² · d ^ (2q)` near `y`.
Hence the single-EA-polynomial Łojasiewicz statement for all EA polynomials follows from its
`Φ ≥ 0` case (apply it to `Φ ^ 2`). -/
theorem hasLoj_sq (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (q : ℕ)
    (h : Work.WilE3.HasLoj (fun x => |eaEval c (Φ ^ 2) x|)
      {x : Fin k → ℝ | eaEval c (Φ ^ 2) x = 0} y (2 * q)) :
    Work.WilE3.HasLoj (fun x => |eaEval c Φ x|) {x : Fin k → ℝ | eaEval c Φ x = 0} y q := by
  obtain ⟨C, hC, hCbound⟩ := h
  -- `eaEval` of a square is the square
  have hsq : ∀ x : Fin k → ℝ, eaEval c (Φ ^ 2) x = (eaEval c Φ x) ^ 2 := by
    intro x
    have h1 := map_pow (MvPolynomial.eval (Sum.elim x fun j => Real.exp (c.ell j x))) Φ 2
    simpa [eaEval] using h1
  -- the two zero sets agree
  have hset : {x : Fin k → ℝ | eaEval c (Φ ^ 2) x = 0}
      = {x : Fin k → ℝ | eaEval c Φ x = 0} := by
    ext x
    simp [hsq x]
  rw [hset] at hCbound
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  filter_upwards [hCbound] with x hx
  -- `hx : C * infDist ^ (2q) ≤ |eaEval c (Φ^2) x|`
  have hx2 : C * (Metric.infDist x {x : Fin k → ℝ | eaEval c Φ x = 0} ^ q) ^ 2
      ≤ (eaEval c Φ x) ^ 2 := by
    have hp : Metric.infDist x {x : Fin k → ℝ | eaEval c Φ x = 0} ^ (2 * q)
        = (Metric.infDist x {x : Fin k → ℝ | eaEval c Φ x = 0} ^ q) ^ 2 := by
      rw [mul_comm, pow_mul]
    have hx' : C * Metric.infDist x {x : Fin k → ℝ | eaEval c Φ x = 0} ^ (2 * q)
        ≤ (eaEval c Φ x) ^ 2 := by
      rw [hsq x] at hx
      simpa using hx
    rwa [hp] at hx'
  have hle : Real.sqrt C * Metric.infDist x {x : Fin k → ℝ | eaEval c Φ x = 0} ^ q
      ≤ |eaEval c Φ x| := by
    nlinarith [hx2, Real.sq_sqrt hC.le, sq_abs (eaEval c Φ x),
      sq_nonneg (Real.sqrt C * Metric.infDist x {x : Fin k → ℝ | eaEval c Φ x = 0} ^ q),
      abs_nonneg (eaEval c Φ x)]
  simpa using hle

/-- **The "definite leading form" case.**  If `Φ` vanishes at `y` and is bounded below near `y` by
`c ‖· - y‖^d` with `c > 0` and `d ≥ 1` (the situation produced by a *definite* leading Taylor form
`P_d` of `Φ` at `y`), then the Łojasiewicz inequality holds with the exponent `d`: indeed
`dist (x, {Φ = 0}) ≤ ‖x - y‖` because `y ∈ {Φ = 0}`, and `Φ x ≥ c ‖x - y‖^d ≥ 0`. -/
theorem hasLoj_of_leading_bound {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {d : ℕ} {c : ℝ}
    (hd : 0 < d) (hc : 0 < c) (hΦy : Φ y = 0)
    (hΦ : ∀ᶠ x in 𝓝 y, c * ‖x - y‖ ^ d ≤ Φ x) :
    Work.WilE3.HasLoj (fun x => |Φ x|) {x : Fin k → ℝ | Φ x = 0} y d := by
  refine ⟨c, hc, ?_⟩
  filter_upwards [hΦ] with x hx
  have hmem : y ∈ {x : Fin k → ℝ | Φ x = 0} := hΦy
  have hdist : Metric.infDist x {x : Fin k → ℝ | Φ x = 0} ≤ ‖x - y‖ := by
    have h := Metric.infDist_le_dist_of_mem (x := x) hmem
    simpa [dist_eq_norm] using h
  have h3 : 0 ≤ Φ x :=
    le_trans (mul_nonneg hc.le (pow_nonneg (norm_nonneg _) d)) hx
  have hfin : c * Metric.infDist x {x : Fin k → ℝ | Φ x = 0} ^ d ≤ Φ x :=
    le_trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ Metric.infDist_nonneg hdist d) hc.le) hx
  simpa [abs_of_nonneg h3] using hfin

/-- **The radial polar minors of `Φ` about `y`.**  `radMinor c Φ y i j` is the (symbolic) EA
polynomial `∂ᵢΦ · (xⱼ - yⱼ) - ∂ⱼΦ · (xᵢ - yᵢ)`; its vanishing for all `i, j` says `∇Φ(x) ∥ (x - y)`,
i.e. `x` lies on the radial polar set `Q` of `Φ` about `y` (`Work.WilE3.Taylor.Polar`).  These are
the equations of the square system `(Φ - ε, radMinor …)` whose nondegenerate zeros
`MultiplicityBound` counts (`Work.WilE3.Taylor.HasLoj.polar_count_deformed`). -/
def radMinor (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i j : Fin k) : EAPoly k r :=
  eaD c i Φ * (MvPolynomial.X (Sum.inl j) - MvPolynomial.C (y j)) -
    eaD c j Φ * (MvPolynomial.X (Sum.inl i) - MvPolynomial.C (y i))

/-- Evaluation of the radial polar minors. -/
theorem eaEval_radMinor (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (i j : Fin k)
    (x : Fin k → ℝ) :
    eaEval c (radMinor c Φ y i j) x =
      eaEval c (eaD c i Φ) x * (x j - y j) - eaEval c (eaD c j Φ) x * (x i - y i) := by
  simp [radMinor, eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_mul]

/-- **The gradient route to the single-EA-polynomial Łojasiewicz inequality.**

If `Φ` is `C¹`, `Φ y = 0`, and near `y` the *gradient inequality* `c |Φ x|^κ ≤ ‖∇Φ x‖` holds with
`0 < c`, `0 ≤ κ < 1` and `1/(1-κ) ≤ q`, then `HasLoj (|Φ|) {Φ = 0} y q`.

This is the integration step of Gabrielov 1995, p. 15 — proved, and axiom-clean
(`#print axioms` gives only `propext, Classical.choice, Quot.sound`), as
`Work.WilE3.Loj.loj_of_gradient_bound` — together with the exponent bookkeeping: from
`1/(1-κ) ≤ q` and `Metric.infDist · {Φ = 0} ≤ 1` near `y` (true because `y ∈ {Φ = 0}`) the real
exponent `1/(1-κ)` dominates the natural exponent `q`. -/
theorem hasLoj_of_gradient_bound {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {κ c : ℝ} {q : ℕ}
    (hC1 : ContDiff ℝ 1 Φ) (hy : Φ y = 0) (hc : 0 < c) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hq : 1 / (1 - κ) ≤ (q : ℝ))
    (hgrad : ∀ᶠ x in 𝓝 y, c * |Φ x| ^ κ ≤ ‖fderiv ℝ Φ x‖) :
    Work.WilE3.HasLoj (fun x => |Φ x|) {x | Φ x = 0} y q := by
  obtain ⟨a, ha, -, hmain⟩ :=
    Work.WilE3.Loj.loj_of_gradient_bound hC1 hy hc hκ0 hκ1 hgrad
  refine ⟨a, ha, ?_⟩
  -- `infDist · {Φ = 0} ≤ 1` near `y`, because `y ∈ {Φ = 0}`
  have hbdd : ∀ᶠ x in 𝓝 y, Metric.infDist x {x : Fin k → ℝ | Φ x = 0} ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1)] with x hx
    have h1 : Metric.infDist x {x : Fin k → ℝ | Φ x = 0} ≤ dist x y :=
      Metric.infDist_le_dist_of_mem hy
    have h2 : dist x y < 1 := by simpa [Metric.mem_ball] using hx
    linarith
  have hqpos : (0 : ℝ) < (q : ℝ) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (1 - κ)) hq
  filter_upwards [hmain, hbdd] with x hx1 hx2
  have hpowr : Metric.infDist x {z : Fin k → ℝ | Φ z = 0} ^ (q : ℝ)
      ≤ Metric.infDist x {z : Fin k → ℝ | Φ z = 0} ^ (1 / (1 - κ)) := by
    rcases eq_or_lt_of_le
      (Metric.infDist_nonneg (x := x) (s := {z : Fin k → ℝ | Φ z = 0})) with h0 | h0
    · rw [← h0, Real.zero_rpow (ne_of_gt hqpos),
        Real.zero_rpow (by positivity : (1 / (1 - κ)) ≠ 0)]
    · exact Real.rpow_le_rpow_of_exponent_ge h0 hx2 hq
  have hpow : Metric.infDist x {z : Fin k → ℝ | Φ z = 0} ^ q
      ≤ Metric.infDist x {z : Fin k → ℝ | Φ z = 0} ^ (1 / (1 - κ)) := by
    rw [← Real.rpow_natCast (Metric.infDist x {z : Fin k → ℝ | Φ z = 0}) q]
    exact hpowr
  calc a * Metric.infDist x {z : Fin k → ℝ | Φ z = 0} ^ q
      ≤ a * Metric.infDist x {z : Fin k → ℝ | Φ z = 0} ^ (1 / (1 - κ)) :=
        mul_le_mul_of_nonneg_left hpow ha.le
    _ ≤ |Φ x| := hx1
    _ ≤ |(|Φ x|)| := le_abs_self _

/-- **(SINGLE) from the effective gradient inequality** (the unrestricted form).

This is the modular form of the target: it isolates the *entire* remaining mathematical content of
`Work.WilE3.Taylor.hasLoj_single` as the **effective gradient inequality** for EA functions.  The
hypothesis here carries *no* restriction on `Φ y`; that unrestricted form is in fact unprovable
(`Φ = 1 + x²` at `y = 0` admits no `κ ∈ [0,1)`), so the lemma is retained only as a true
implication; the file uses `Work.WilE3.Taylor.ea_grad_of_multiplicity`, whose hypothesis includes
the necessary `eaEval c Φ y = 0`. -/
theorem hasLoj_single_of_gradient
    (hgrad : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
        (y : Fin k → ℝ), k + r ≤ F →
        ∃ (κ cst : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < cst ∧ 1 / (1 - κ) ≤ ((K.eval (atomDeg Φ) : ℕ) : ℝ) ∧
          (∀ᶠ x in 𝓝 y, cst * |eaEval c Φ x| ^ κ ≤
            ‖fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x‖)) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
      (y : Fin k → ℝ) (q : ℕ), k + r ≤ F → K.eval (atomDeg Φ) < q →
      Work.WilE3.HasLoj (fun x => |eaEval c Φ x|) {x | eaEval c Φ x = 0} y q := by
  intro F
  obtain ⟨K, hK⟩ := hgrad F
  refine ⟨K, ?_⟩
  intro k r c Φ y q hkr hKq
  obtain ⟨κ, cst, hκ0, hκ1, hcst, hKκ, hgr⟩ := hK k r c Φ y hkr
  have hC1 : ContDiff ℝ 1 (fun z : Fin k → ℝ => eaEval c Φ z) :=
    contDiff_iff_contDiffAt.mpr (fun x => (Work.WilE3.eaEval_analytic c Φ x).contDiffAt)
  have hQ : 1 / (1 - κ) ≤ (q : ℝ) := by
    have h1 : ((K.eval (atomDeg Φ) : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast hKq
    linarith
  by_cases hy : eaEval c Φ y = 0
  · exact hasLoj_of_gradient_bound hC1 hy hcst hκ0 hκ1 hQ hgr
  · refine Work.WilE3.Taylor.hasLoj_of_pos ?_ ?_ q
    · exact (Work.WilE3.eaEval_analytic c Φ y).continuousAt.abs
    · simpa [abs_abs] using abs_pos.mpr hy

end Work.WilE3.Taylor
