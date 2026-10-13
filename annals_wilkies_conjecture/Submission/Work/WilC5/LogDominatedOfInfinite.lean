import Mathlib
import Submission.Work.WilC5.LogFunPowLtSelf
import Submission.Work.WilC5.ValueOrder
import Submission.Work.WilC5.ValuesLemmas

namespace Work.WilC5

/-- **The logarithm is archimedean-dominated by its argument, for infinite arguments.**  If
`x > 0` is *infinite* in a model of `TE` (`¬ IsFiniteVal x`, i.e. `x` exceeds every natural number),
then `v(x) < v(log x)`: `x` dominates `log x` (`VLe x (log x)`) and not conversely.

This is the `Work.WilC5.StepSeq.LogDominated` invariant at a single element; it is a general fact
about models of `TE` (no sequence involved).  The proof: `VLe x (logFun x)` is immediate from
`log x < x` for `x > 1`; for the strict part, if `|x| ≤ N|log x|` and `(log x)^{N+1} < x`
(`Work.WilC5.LogFunPowLtSelf`, valid because `x` is infinite), then
`x^{N+1}/N^{N+1} ≤ (log x)^{N+1} < x`, i.e. `x^N < N^{N+1}`, which is false as soon as `x > N^3`
(and `x` infinite is bigger than the standard natural `N^3`). -/
theorem LogDominatedOfInfinite
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {x : K} (hxpos : 0 < x) (hxinf : ¬ Work.WilC5.IsFiniteVal x) :
    Work.WilC5.VLe x (Work.WilC5.logFun x) ∧ ¬ Work.WilC5.VLe (Work.WilC5.logFun x) x := by
  -- `x` is positive and infinite, hence `|x| = x` and `x` exceeds every natural number.
  have hxabs : |x| = x := abs_of_pos hxpos
  have hxbig : ∀ M : ℕ, ((M : ℕ) : K) + 1 < x := by
    intro M
    have h := not_exists.mp hxinf M
    rw [hxabs] at h
    exact not_le.mp h
  -- `(log x)^2 < x` in every model of `TE` when `x` is infinite.
  have hlog2 : (Work.WilC5.logFun x) ^ 2 < x :=
    Work.WilC5.LogFunPowLtSelf hrexp hadd hmul hone hleneg hxpos hxinf 2
  have habs2 : |Work.WilC5.logFun x| ^ 2 = (Work.WilC5.logFun x) ^ 2 := sq_abs _
  constructor
  · -- `VLe x (log x)`: `|log x| ≤ |x| = x`, by `(log x)^2 < x < x^2`.
    have hx1 : (1 : K) < x := by have := hxbig 0; simpa using this
    have hxlt : x < x ^ 2 := by nlinarith
    have habslt : |Work.WilC5.logFun x| < x := by
      by_contra hcon
      have hle : x ≤ |Work.WilC5.logFun x| := not_lt.mp hcon
      have hxx : x ^ 2 ≤ (Work.WilC5.logFun x) ^ 2 := by
        calc x ^ 2 = x * x := by ring
          _ ≤ |Work.WilC5.logFun x| * |Work.WilC5.logFun x| :=
              mul_le_mul hle hle (le_of_lt hxpos) (abs_nonneg _)
          _ = |Work.WilC5.logFun x| ^ 2 := by ring
          _ = (Work.WilC5.logFun x) ^ 2 := habs2
      linarith [hlog2, hxlt, hxx]
    refine ⟨0, ?_⟩
    rw [Nat.cast_zero, zero_add, one_mul, hxabs]
    exact le_of_lt habslt
  · -- The strict part: if `x ≤ n |log x|` then squaring and `(log x)^2 < x` force `x < n^2`,
    -- contradicting the infinitude of `x`.
    intro hVLe
    obtain ⟨N, hN⟩ := hVLe
    have hcast : ((N : ℕ) : K) + 1 = ((N + 1 : ℕ) : K) := by push_cast; ring
    have hN' : x ≤ ((N + 1 : ℕ) : K) * |Work.WilC5.logFun x| := by
      rw [hxabs, hcast] at hN
      exact hN
    have hxx : x * x ≤ (((N + 1 : ℕ) : K) * |Work.WilC5.logFun x|) *
        (((N + 1 : ℕ) : K) * |Work.WilC5.logFun x|) :=
      mul_le_mul hN' hN' (le_of_lt hxpos) (by positivity)
    have hxx2 : x * x ≤ ((N + 1 : ℕ) : K) ^ 2 * |Work.WilC5.logFun x| ^ 2 := by
      calc x * x ≤ (((N + 1 : ℕ) : K) * |Work.WilC5.logFun x|) *
            (((N + 1 : ℕ) : K) * |Work.WilC5.logFun x|) := hxx
        _ = ((N + 1 : ℕ) : K) ^ 2 * |Work.WilC5.logFun x| ^ 2 := by ring
    have hlt2 : ((N + 1 : ℕ) : K) ^ 2 * |Work.WilC5.logFun x| ^ 2
        < ((N + 1 : ℕ) : K) ^ 2 * x := by
      rw [habs2]
      exact mul_lt_mul_of_pos_left hlog2 (by positivity)
    have hxt : x < ((N + 1 : ℕ) : K) ^ 2 :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt hxx2 hlt2) (le_of_lt hxpos)
    have hbig := hxbig ((N + 1) * (N + 1))
    have hpow : (((N + 1) * (N + 1) : ℕ) : K) = ((N + 1 : ℕ) : K) ^ 2 := by
      push_cast; ring
    rw [hpow] at hbig
    linarith

end Work.WilC5
