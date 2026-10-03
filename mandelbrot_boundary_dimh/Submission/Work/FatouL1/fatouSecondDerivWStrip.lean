import Mathlib
import Submission.Work.FatouL1.wideStripDefs
import Submission.Work.FatouL1.wideDerivSmall
import Submission.Work.FatouL1.abelSegmentMean
import Submission.Work.FatouL1.hcSolverDerivBoundM
import Submission.Work.FatouL1.hcSolverShiftRigidity
import Submission.Work.FatouL1.normOneSubMulDerivLe

/-!
# FATOU-L1: the second-derivative bound on the wide strip (target `fatouSecondDerivWStrip`)

Target (do not restate):
`∃ Φ, IsFatouCoordOn F Φ (Qreg b₁ b₂) ∧ ∀ z ∈ wStrip x₀, ‖iteratedDeriv 2 Φ z‖ ≤ 1/35`
under `QAdm`, `NearTranslationL1`, `h₁ : b₁.re + 1 < x₀`, `h₂ : x₀ + 3 < b₂.re`.

## Roadmap (session-9 lead notes)

The canonical Fatou coordinate `Φ` (`FatouUnique` ⇒ `Φ''` is canonical) satisfies, with
`v := F - id`, `g := F' - 1 = v'`:

* `‖g‖ ≤ 1/150` on `wStrip x₀` (`wideDerivSmall`), `‖g‖ ≤ 1/32` on `Qreg`;
* `T := φ₀ - Φ` (`φ₀` a primitive of `1/v` on the strip `(x₀-1, x₀+3) ⊆ Qreg`) satisfies the
  *exact* identities `T (F z) - T z = e z` with `e z = ∫₀¹ (v z - v (z+tv z))/v (z+tv z) dt`,
  and `T' = v · R` with `R z = ∫₀¹ (1-t) Φ'' (z+tv z) dt`;
* `Φ'' = (1/v)' - T''`, so `‖Φ''‖ ≤ ‖g/v²‖ + ‖T''‖ ≤ 0.0072 + ‖T''‖` and it suffices to bound
  `‖T''‖` on `wStrip x₀` by `1/35 - 0.0072`.

The route to `‖T''‖`: the *unit shift* defect `h := T(·+1) - T` is `h = e - ε·(mean of T')` with
`‖h‖ ≤ 0.0044` (self-consistent), and `T = c - hcSolver h` by the rigidity
(`hcSolverShiftRigidity`), whence `T'' = -(hcSolver h)''` and the `π`-trick
(`hcSolverDerivBoundM`, strengthened below to the region `Re z < b + 1/2`, which removes the
"sliver" of `wStrip x₀` near `x₀ + 17/8`) gives `‖T''‖ ≤ π ‖h‖ ≤ 0.0138 ≤ 0.0215`.

Two inputs are consumed here and are *not* consequences of the statement's hypotheses in the
trivial way (see the session-7/8 notes): the finiteness of the line mass of `h` and the
boundedness of `T` on a unit window.  Both are the "end behaviour" of `T' = 1/v - Φ'`.
-/

namespace Work.FatouL1

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

/-- **The `π`-trick for the Cauchy–Heine solver, on the full region of holomorphy.**

Same as `Work.FatouL1.hcSolverDerivBoundM` but with the second hypothesis `Re z < b + 1/2`
(instead of `Re z < b - 1/2`): the fixed-contour representation `hcSolverLocalRep` only needs the
contour `Re w = Re z - 1/2` to lie inside `(a,b)`, i.e. exactly `Re z < b + 1/2`.  This is what
removes the "sliver" `{b₂.re - 1 < Re z < x₀ + 17/8}` of the wide strip in the rigidity route. -/
theorem hcSolverDerivBoundMr {a b m : ℝ} (hab : a < b) {h : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    {z : ℂ} (hz1 : a + 1 / 2 < z.re) (hz2 : z.re < b + 1 / 2) {M : ℝ}
    (hMnn : 0 ≤ M) (hM : ∀ y : ℝ, ‖h (z - 1 / 2 + y * Complex.I)‖ ≤ M) :
    ‖deriv (Work.FatouL1.hcSolver h) z‖ ≤ M ∧
      ‖iteratedDeriv 2 (Work.FatouL1.hcSolver h) z‖ ≤ Real.pi * M := by
  set c : ℝ := z.re - 1 / 2 with hc
  have hca : a < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  have hzc : z.re = c + 1 / 2 := by rw [hc]; ring
  have hband1 : c < z.re := by rw [hzc]; linarith
  have hband2 : z.re < c + 1 := by rw [hzc]; linarith
  have hle : ∀ y : ℝ, ‖h ((c : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M := by
    intro y
    have hz_eq : z - 1 / 2 + ((y - z.im : ℝ) : ℂ) * Complex.I
        = (c : ℂ) + (y : ℂ) * Complex.I := by
      rw [hc]; apply Complex.ext <;> simp <;> ring
    rw [← hz_eq]
    exact hM (y - z.im)
  obtain ⟨hD1, hD2⟩ := cotContourHasDeriv hab hint hmass hca hcb
  have hd1 := hD1 z hband1 hband2
  have hd2 := hD2 z hband1 hband2
  have hev := hcSolverLocalRep hab hhol hint hmass hz1 (by linarith)
  have hev' : Work.FatouL1.hcSolver h =ᶠ[nhds z] fun w : ℂ => -(1 / 2) *
      ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w)) := by
    simpa only [← hc] using hev
  have hderiv1 : deriv (Work.FatouL1.hcSolver h) z = -(1 / 2) *
      (∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2)) := by
    rw [hev'.deriv_eq]
    exact (hd1.const_mul (-(1 / 2))).deriv
  have hband_nhds : ∀ᶠ w in nhds z, c < w.re ∧ w.re < c + 1 := by
    have hopen : IsOpen {w : ℂ | c < w.re ∧ w.re < c + 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    exact hopen.mem_nhds ⟨hband1, hband2⟩
  have hFeq : deriv (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) =ᶠ[nhds z]
      (fun w : ℂ => ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) ^ 2)) := by
    filter_upwards [hband_nhds] with w hw
    exact (hD1 w hw.1 hw.2).deriv
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.mp hev'
  have hderiv_eq : deriv (Work.FatouL1.hcSolver h) =ᶠ[nhds z] deriv (fun w : ℂ => -(1 / 2) *
      ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    have hwU : Work.FatouL1.hcSolver h =ᶠ[nhds w] fun w : ℂ => -(1 / 2) *
        ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w)) :=
      Filter.eventually_of_mem (hUopen.mem_nhds hw) hUsub
    exact hwU.deriv_eq
  have hderiv_chain : deriv (fun w : ℂ => -(1 / 2) *
      ∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w)))
      =ᶠ[nhds z] (fun w : ℂ => -(1 / 2) * deriv (fun w : ℂ => ∫ y : ℝ,
        h ((c : ℂ) + (y : ℂ) * Complex.I) *
          Complex.cot (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - w))) w) := by
    filter_upwards [hband_nhds] with w hw
    exact deriv_const_mul (-(1 / 2)) (hD1 w hw.1 hw.2).differentiableAt
  have hderiv2 : deriv (deriv (Work.FatouL1.hcSolver h)) z = -(1 / 2) *
      (∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
        ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
          (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)) := by
    rw [hderiv_eq.deriv_eq, hderiv_chain.deriv_eq]
    exact (((hFeq.hasDerivAt_iff).mpr hd2).const_mul (-(1 / 2))).deriv
  have hnorm : ‖(-(1 / 2) : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  constructor
  · rw [hderiv1, norm_mul, hnorm]
    have hK := (hcDerivKernel).1 (c := c) (z := z) (S := M) (h := h) hzc hMnn hle
    calc (1 / 2 : ℝ) * ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          ((Real.pi : ℂ) / (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 2)‖
        ≤ (1 / 2) * (2 * M) := mul_le_mul_of_nonneg_left hK (by norm_num)
      _ = M := by ring
  · have hit : iteratedDeriv 2 (Work.FatouL1.hcSolver h) z =
        deriv (deriv (Work.FatouL1.hcSolver h)) z := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hit, hderiv2, norm_mul, hnorm]
    have hK := (hcDerivKernel).2 (c := c) (z := z) (S := M) (h := h) hzc hMnn hle
    calc (1 / 2 : ℝ) * ‖∫ y : ℝ, h ((c : ℂ) + (y : ℂ) * Complex.I) *
          ((2 : ℂ) * (Real.pi : ℂ) ^ 2 * Complex.cos (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z)) /
            (Complex.sin (Real.pi * ((c : ℂ) + (y : ℂ) * Complex.I - z))) ^ 3)‖
        ≤ (1 / 2) * (2 * Real.pi * M) := mul_le_mul_of_nonneg_left hK (by norm_num)
      _ = Real.pi * M := by ring


/-- **The rigidity identity on the full holomorphy region.**  `Work.FatouL1.hcSolverShiftRigidity`
gives `T = c - hcSolver h` only on `(a+1/2, b-1)`; since both sides are holomorphic on the (convex,
hence preconnected) strip `(a+1/2, b)` and agree on the nonempty open subset `(a+1/2, b-1)`, the
identity extends by analytic uniqueness.  This is what lets the `π`-trick be applied up to
`Re z < b + 1/2` (i.e. on the whole right margin of the target strip). -/
theorem hcSolverShiftRigidity_ext {a b m B : ℝ} (hab : a < b) (hab' : 2 < b - a) {T h : ℂ → ℂ}
    (hT : DifferentiableOn ℂ T {z : ℂ | a < z.re ∧ z.re < b})
    (hh : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    (heq : ∀ z : ℂ, a < z.re → z.re < b → T (z + 1) - T z = h z)
    (hbdd : ∀ z : ℂ, a < z.re → z.re < b → ‖T z‖ ≤ B) :
    ∃ c : ℂ, ∀ z : ℂ, a + 1 / 2 < z.re → z.re < b → T z = c - Work.FatouL1.hcSolver h z := by
  obtain ⟨c, hc⟩ := hcSolverShiftRigidity hab hab' hT hh hint hmass heq hbdd
  refine ⟨c, ?_⟩
  have hSopen : IsOpen {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hSconn : IsPreconnected {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} := by
    have heq' : {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b}
        = Complex.reCLM ⁻¹' (Set.Ioo (a + 1 / 2) b) := by
      ext z; simp [Complex.reCLM_apply]
    rw [heq']
    exact (Convex.linear_preimage (convex_Ioo _ _) Complex.reCLM.toLinearMap).isPreconnected
  have hS₀open : IsOpen {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b - 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hS₀sub : {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b - 1} ⊆ {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} :=
    fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hz₀ : (((a + 1 / 2 + (b - 1)) / 2 : ℝ) : ℂ) ∈ {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b - 1} := by
    constructor <;> simp only [Complex.ofReal_re] <;> linarith
  have hT_sub : {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} ⊆ {z : ℂ | a < z.re ∧ z.re < b} :=
    fun z hz => ⟨by linarith [hz.1], hz.2⟩
  have hcS_hol : DifferentiableOn ℂ (Work.FatouL1.hcSolver h)
      {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} := (hcSolverBound hab hh hint hmass).1
  have hcS_sub : {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b}
      ⊆ {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b + 1 / 2} :=
    fun z hz => ⟨hz.1, by linarith [hz.2]⟩
  have hT_an : AnalyticOnNhd ℂ T {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} :=
    (hT.mono hT_sub).analyticOnNhd hSopen
  have hR_an : AnalyticOnNhd ℂ (fun z : ℂ => c - Work.FatouL1.hcSolver h z)
      {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} :=
    ((hcS_hol.mono hcS_sub).const_sub c).analyticOnNhd hSopen
  have hEq : Set.EqOn T (fun z : ℂ => c - Work.FatouL1.hcSolver h z)
      {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} :=
    hT_an.eqOn_of_preconnected_of_eventuallyEq hR_an hSconn (hS₀sub hz₀)
      (Filter.eventually_of_mem (hS₀open.mem_nhds hz₀) (fun w hw => hc w hw.1 hw.2))
  intro z hz1 hz2
  exact hEq ⟨hz1, hz2⟩

/-- **The unit-shift data bound.**  Let `T` be holomorphic on the strip `(a,b)` (`b - a > 2`),
bounded by `B`, with `Δ₁ T = h` on `(a,b)` where `h` has finite line masses `≤ m`.  Then for
`a + 1/2 < Re z < b` and any pointwise bound `M ≥ 0` for `‖h (z - 1/2 + iy)‖`, one has
`‖T'' z‖ ≤ π M`.  (`M` is normally taken to be `sup_y ‖h (z - 1/2 + iy)‖`; the self-consistency of
the route makes it small.) -/
theorem secondDeriv_le_of_unitShift {a b m B : ℝ} (hab : a < b) (hab' : 2 < b - a) {T h : ℂ → ℂ}
    (hT : DifferentiableOn ℂ T {z : ℂ | a < z.re ∧ z.re < b})
    (hh : DifferentiableOn ℂ h {z : ℂ | a < z.re ∧ z.re < b})
    (hint : ∀ x ∈ Set.Ioo a b, MeasureTheory.Integrable (fun y : ℝ => h ((x : ℂ) + y * Complex.I)))
    (hmass : ∀ x ∈ Set.Ioo a b,
      ∫⁻ y : ℝ, ENNReal.ofReal ‖h ((x : ℂ) + y * Complex.I)‖ ≤ ENNReal.ofReal m)
    (heq : ∀ z : ℂ, a < z.re → z.re < b → T (z + 1) - T z = h z)
    (hbdd : ∀ z : ℂ, a < z.re → z.re < b → ‖T z‖ ≤ B) :
    ∀ z : ℂ, a + 1 / 2 < z.re → z.re < b → ∀ M : ℝ, 0 ≤ M →
      (∀ y : ℝ, ‖h (z - 1 / 2 + y * Complex.I)‖ ≤ M) → ‖iteratedDeriv 2 T z‖ ≤ Real.pi * M := by
  intro z hz1 hz2 M hMnn hM
  obtain ⟨c, hc⟩ := hcSolverShiftRigidity_ext hab hab' hT hh hint hmass heq hbdd
  have hSopen : IsOpen {z : ℂ | a + 1 / 2 < z.re ∧ z.re < b} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hne : T =ᶠ[nhds z] (fun w : ℂ => c - Work.FatouL1.hcSolver h w) :=
    Filter.eventually_of_mem (hSopen.mem_nhds ⟨hz1, hz2⟩) (fun w hw => hc w hw.1 hw.2)
  have h2 : iteratedDeriv 2 T z = -iteratedDeriv 2 (Work.FatouL1.hcSolver h) z := by
    have hEq1 : iteratedDeriv 2 T z
        = iteratedDeriv 2 (fun w : ℂ => c - Work.FatouL1.hcSolver h w) z :=
      (hne.iteratedDeriv 2).eq_of_nhds
    rw [hEq1, iteratedDeriv_const_sub (by norm_num : 0 < 2), iteratedDeriv_neg]
  have hbound := (hcSolverDerivBoundMr hab hh hint hmass hz1 (by linarith) hMnn hM).2
  rw [h2, norm_neg]
  exact hbound


/-- **Arithmetic closure of the route to `‖Φ''‖ ≤ 1/35`.**

Let `A ≥ sup_{wStrip} ‖(1/v)'‖ = sup ‖v'/v²‖`, `E ≥ sup ‖e‖` (the flow defect) and `M` be the
target sup `sup_{wStrip} ‖Φ''‖`.  The three *exact* identities
`Φ'' = (1/v)' - T''`, `T' = v·(mean of Φ'' over the flow segment)` and
`h = Δ₁T = e - ε·(mean of T')` give, using `‖h(z-1/2+iy)‖ ≤ sup‖h‖` in the `π`-trick
(`secondDeriv_le_of_unitShift`),

  `M ≤ A + π·(E + (1/32)·(1/2)·(33/32)·M)`.

With the numerically verified inputs of `wideStripDefs`/`wideDerivSmall`
(`A = 71/10000 = (32/31)²/150`) and `E = 4/1000` (`flowDefectSmall` gives `1/100`, which is *too
stingy* for this arithmetic: the sharper `e = ∫₀¹ (v z - v (z+tv))/(v (z+tv))` with
`‖v'‖ ≤ 1/150` gives `‖e‖ ≤ (1/2)(33/31)(1/150)(33/32) ≤ 4/1000`), this yields `M ≤ 1/35`.

The lemma is stated with the inequality as a hypothesis because its purpose is to record that the
*constants* close with a comfortable margin (`M ≤ 0.0208 < 0.02857`), so nothing but the two
qualitative end-behaviour inputs of `secondDeriv_le_of_unitShift` is missing. -/
theorem secondDeriv_arith_closure {A E M : ℝ} (hA : A ≤ 71 / 10000) (hE : E ≤ 4 / 1000)
    (hAM : M ≤ A + Real.pi * (E + (1 / 32) * ((1 / 2) * (33 / 32) * M))) :
    M ≤ 1 / 35 := by
  have hpi := Real.pi_lt_d4
  have hpi0 := Real.pi_pos
  rcases le_total 0 M with hM | hM
  · nlinarith [hA, hE, hAM, hpi, hpi0, hM]
  · linarith


/-! ## Session 10: geometry of the working strip `(x₀-1, x₀+9/5)`

The route of `NOTES_fatouSecondDerivWStrip_session10.md` uses the mass region
`(a,b) := (x₀-1, x₀+9/5)`, the conclusion region `(a, b+1) = (x₀-1, x₀+14/5)` and the "reach
region" `(x₀-5/8, x₀+14/5)`.  Its elementary content is the following pair of facts: the cones of
`Qreg` point *outward*, so any vertical strip between the two vertices is contained in `Qreg`, and
in particular every point `w` of the mass region has `w + 1 ∈ Qreg` with `Re (w+1) < x₀ + 3`.
-/

/-- **The working strip.**  If `b₁` sits at least `1` to the left of `x₀` and `b₂` at least `3`
to the right, then the whole vertical strip `(x₀-1, x₀+9/5) × ℝ` lies in `Qreg b₁ b₂`: for a point
of that strip both cone conditions hold trivially (`x > β₁ > β₁ - |y-γ₁|` and
`x < β₂ < β₂ + |y-γ₂|`). -/
lemma strip10_subset_Qreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 9 / 5} ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z hz
  rw [← Complex.re_add_im z]
  exact mem_Qreg_of_re (fun a ha => by have := h₁ a ha; linarith [hz.1])
    (fun b hb => by have := h₂ b hb; linarith [hz.2])

/-- **The wide working strip `(x₀-1, x₀+14/5)`.**  It contains the mass region and its unit
translate, and lies in `Qreg b₁ b₂` because `x₀ + 14/5 < x₀ + 3 < b.re`. -/
lemma strip14_subset_Qreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    {z : ℂ | x₀ - 1 < z.re ∧ z.re < x₀ + 14 / 5} ⊆ MandelDim.Qreg b₁ b₂ := by
  intro z hz
  rw [← Complex.re_add_im z]
  exact mem_Qreg_of_re (fun a ha => by have := h₁ a ha; linarith [hz.1])
    (fun b hb => by have := h₂ b hb; linarith [hz.2])

/-- **`w + 1` stays in `Qreg`.**  For `w` in the working strip `(x₀-1, x₀+9/5)` the translate
`w + 1` still lies in `Qreg b₁ b₂` (its real part is `< x₀ + 14/5 < x₀ + 3 < b.re`).  This is what
makes the unit-shift defect `Δ₁T (w) = T (w+1) - T w` well defined on the mass region. -/
lemma add_one_mem_Qreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {w : ℂ}
    (hw : x₀ - 1 < w.re ∧ w.re < x₀ + 9 / 5) :
    w + 1 ∈ MandelDim.Qreg b₁ b₂ := by
  have hre : (w + 1).re = w.re + 1 := by simp
  refine strip14_subset_Qreg h₁ h₂ ⟨?_, ?_⟩
  · rw [hre]; linarith [hw.1]
  · rw [hre]; linarith [hw.2]

/-- The horizontal unit segment from a point `w` of the working strip stays in `Qreg b₁ b₂`
(the strip `(x₀-1, x₀+14/5)` is convex and contained in `Qreg` by `strip14_subset_Qreg`). -/
lemma unit_segment_mem_Qreg {b₁ b₂ : Option ℂ} {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) {w : ℂ}
    (hw : x₀ - 1 < w.re ∧ w.re < x₀ + 9 / 5) :
    ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → w + t ∈ MandelDim.Qreg b₁ b₂ := by
  intro t ht
  have hre : (w + (t : ℂ)).re = w.re + t := by simp
  refine strip14_subset_Qreg h₁ h₂ ⟨?_, ?_⟩
  · rw [hre]; linarith [ht.1, hw.1]
  · rw [hre]; linarith [ht.2, hw.2]

end

end Work.FatouL1
