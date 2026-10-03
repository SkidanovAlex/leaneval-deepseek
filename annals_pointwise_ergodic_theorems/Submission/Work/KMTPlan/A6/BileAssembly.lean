/-
# Assembly of the lifting proof of Theorem `bile` at `r = 1` (paper: Proposition `bile-2`)

This module contains the *wiring* of the lifting proof of `Work.KMTPlan.A6.MdlBileR1OfImprov`,
together with the elementary limit-extraction primitives it needs.  It is written against the
statements of the five delegated pieces

* `BileWindowLimits`     -- the window `ψ` (`‖ψ‖_{L²} = 1`, `𝓕ψ` supported in `[-1,1]`) and the
                            two Riemann-sum limits (ℓ² up, weighted ℓ¹ down),
* `BileLiftKmtProjZero`  -- the lift is minor arc at height `l`: `kmtProj ρ l k (bileLift ψ R f) = 0`,
* `BileLiftAhalfLimit`   -- `‖bileLiftSum P ψ R N u v‖_{ℓ¹} → ‖bileHalvedAvg P N u v‖_{L¹(μ)}`
                            as `R → ∞` at *fixed* `N`,
* `BileHalvedAvgLimit`   -- `‖bileHalvedAvg P N u v‖_{L¹(μ)} → ½‖polyBilinearAverageZMod X P Q u v‖`
                            as `N → ∞`,
* `ImprovKMT`            -- the given single-scale minor arc estimate (`hI`).

## The wiring, with constants

Fix `ρ ∈ (0,1]`, `Q`, `l`, and `f, g` with `MdlIwMinorArc ρ l Q f` (the other case is the same on
the `g`-side, at height `P.natDegree * (l - logN N)`).  Let `c` be the rate of `hI` and `C_ρ` its
constant at `ρ`.  For `ε > 0`:

1. choose `N ≥ 4 · 2^l · Q · iwQl ρ l` (so that `2^{l-logN N}·(Q·iwQl ρ l) < 1/4`, which is the
   separation hypothesis of `BileLiftKmtProjZero` at `k = l - logN N`), and `N` large enough that
   `⟨logN N⟩^{-c/ρ} ≤ ε` and that `BileHalvedAvgLimit` gives
   `‖bileHalvedAvg P N f g‖ ≤ (½ + ε)‖A(f,g)‖`, `A := polyBilinearAverageZMod X P Q`;
2. choose `R ≥ max (4·Q·iwQl ρ l) R₀(N, ε)` large enough for `BileWindowLimits` (applied to `f`,
   to `g` and to `u := bileHalvedAvg P N f g`) and for `BileLiftAhalfLimit` (so that
   `‖bileLiftSum‖ ≤ (1+ε)‖bileHalvedAvg‖`).  This is legitimate because `BileLiftAhalfLimit` is a
   limit at *fixed* `N`, so `R` may be chosen after `N`;
3. by `BileLiftKmtProjZero` the lift is minor arc, so `hI` gives
   `‖bileLiftSum P ψ R N f g‖_{ℓ¹} ≤ C_ρ (2^{-cl} + ⟨logN N⟩^{-c/ρ}) ‖bileLift ψ R f‖₂ ‖bileLift ψ R g‖₂
     ≤ C_ρ (2^{-cl} + ε)(1+ε)² ‖f‖_{L²} ‖g‖_{L²}`;
4. the same `R` satisfies the weighted lower bound of `BileWindowLimits` at
   `u := bileHalvedAvg P N f g`; together with the pointwise asymptotic
   `bileLiftSum ≈ R⁻¹ ψ(·/R)² · bileHalvedAvg(· mod Q)` (the content of `BileLiftAhalfLimit`)
   this turns the bound of step 3 into
   `‖bileHalvedAvg P N f g‖_{L¹(μ)} ≤ C_ρ (2^{-cl}+ε)(1+ε)³/(1-ε) ‖f‖_{L²}‖g‖_{L²}`;
5. feed this into step 1 and let `ε → 0`:
   `½‖A(f,g)‖_{L¹(μ)} ≤ C_ρ 2^{-cl}‖f‖_{L²}‖g‖_{L²}`, i.e.
   `‖A(f,g)‖_{L¹(μ)} ≤ (2 C_ρ) 2^{-cl}‖f‖_{L²}‖g‖_{L²}`.

The exponent is exactly `hI`'s rate (independent of `ρ`), and the constant is `2 C_ρ` — matching
the required `∃ c, ∀ ρ, ∃ C(ρ)` shape.

## Contents of this module

The generic primitives that turn each piece's `Tendsto` (at a limit `ENNReal.ofReal a`) into the
eventual additive `ε`-bounds consumed by the wiring, and the squeeze that closes it.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BileLiftKmtProjZero
import Submission.Work.KMTPlan.A6.memLp_bileLift
import Submission.Work.KMTPlan.A6.BileLiftSum_eq_AhalfR

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

noncomputable section

open Filter MeasureTheory Polynomial Finset
open scoped ENNReal NNReal

/-- **Eventual upper bound from a limit.**  If `f : ℕ → ℝ≥0∞` tends to `ENNReal.ofReal a` with
`0 ≤ a`, then for every `ε > 0` one has `f R ≤ ofReal (a + ε)` for all large `R`. -/
theorem eventually_le_of_tendsto_ofReal {f : ℕ → ENNReal} {a : ℝ} (ha : 0 ≤ a)
    (h : Filter.Tendsto f Filter.atTop (nhds (ENNReal.ofReal a))) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → f R ≤ ENNReal.ofReal (a + ε) := by
  intro ε hε
  have hpos : (0 : ℝ) < a + ε := by linarith
  have hlt : ENNReal.ofReal a < ENNReal.ofReal (a + ε) := by
    rw [ENNReal.ofReal_lt_ofReal_iff hpos]
    linarith
  have hev : Filter.Eventually (fun R => f R < ENNReal.ofReal (a + ε)) Filter.atTop :=
    h.eventually (isOpen_Iio.mem_nhds hlt)
  obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨R₀, fun R hR => le_of_lt (hR₀ R hR)⟩

/-- **Eventual lower bound from a limit.**  If `f : ℕ → ℝ≥0∞` tends to `ENNReal.ofReal a` with
`0 ≤ a`, then for every `ε > 0` one has `ofReal (a - ε) ≤ f R` for all large `R`. -/
theorem eventually_ge_of_tendsto_ofReal {f : ℕ → ENNReal} {a : ℝ} (ha : 0 ≤ a)
    (h : Filter.Tendsto f Filter.atTop (nhds (ENNReal.ofReal a))) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ENNReal.ofReal (a - ε) ≤ f R := by
  intro ε hε
  by_cases hneg : a - ε ≤ 0
  · refine ⟨0, fun R _ => ?_⟩
    rw [ENNReal.ofReal_eq_zero.mpr hneg]
    exact zero_le
  · have hpos : (0 : ℝ) < a - ε := not_le.mp hneg
    have hapos : (0 : ℝ) < a := by linarith
    have hlt : ENNReal.ofReal (a - ε) < ENNReal.ofReal a := by
      rw [ENNReal.ofReal_lt_ofReal_iff hapos]
      linarith
    have hev : Filter.Eventually (fun R => ENNReal.ofReal (a - ε) < f R) Filter.atTop :=
      h.eventually (isOpen_Ioi.mem_nhds hlt)
    obtain ⟨R₀, hR₀⟩ := Filter.eventually_atTop.mp hev
    exact ⟨R₀, fun R hR => le_of_lt (hR₀ R hR)⟩

/-- **Squeeze.**  If `g → ofReal a`, `h → ofReal b` with `0 ≤ a`, `0 ≤ b`, and eventually `g ≤ h`,
then `a ≤ b`.  This is the step that closes the wiring once `ε` has been sent to `0`. -/
theorem le_of_tendsto_of_le {g h : ℕ → ENNReal} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hg : Filter.Tendsto g Filter.atTop (nhds (ENNReal.ofReal a)))
    (hh : Filter.Tendsto h Filter.atTop (nhds (ENNReal.ofReal b)))
    (hle : Filter.Eventually (fun R => g R ≤ h R) Filter.atTop) : a ≤ b := by
  by_contra hcon
  have hba : b < a := not_le.mp hcon
  obtain ⟨m, hbm, hma⟩ : ∃ m : ℝ, b < m ∧ m < a := ⟨(a + b) / 2, by linarith, by linarith⟩
  have hm0 : (0 : ℝ) < m := lt_of_le_of_lt hb hbm
  have h1 : ENNReal.ofReal b < ENNReal.ofReal m := by
    rw [ENNReal.ofReal_lt_ofReal_iff hm0]
    exact hbm
  have h2 : ENNReal.ofReal m < ENNReal.ofReal a := by
    rw [ENNReal.ofReal_lt_ofReal_iff (lt_trans hm0 hma)]
    exact hma
  have e1 : Filter.Eventually (fun R => h R < ENNReal.ofReal m) Filter.atTop :=
    hh.eventually (isOpen_Iio.mem_nhds h1)
  have e2 : Filter.Eventually (fun R => ENNReal.ofReal m < g R) Filter.atTop :=
    hg.eventually (isOpen_Ioi.mem_nhds h2)
  have hcomb : Filter.Eventually (fun R =>
      h R < ENNReal.ofReal m ∧ (ENNReal.ofReal m < g R ∧ g R ≤ h R)) Filter.atTop :=
    e1.and (e2.and hle)
  obtain ⟨R, hR1, hR2, hR3⟩ := hcomb.exists
  exact absurd (lt_of_lt_of_le hR2 (le_trans hR3 (le_of_lt hR1))) (lt_irrefl _)

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open Filter MeasureTheory Polynomial Finset
open scoped ENNReal NNReal

open Submission.PointwiseErgodicTheorems

/-! ## Item 2: discharging `ImprovKMT`'s hypothesis via `BileLiftKmtProjZero`

`BileLiftKmtProjZero` (proved in its own module) says that the lift `bileLift ψ R f` has
`kmtProj ρ l k (bileLift ψ R f) = 0` for `k = l - logN N`, provided `2^k·(Q·iwQl ρ l) < 1/4` and
`R > 4·Q·iwQl ρ l`.  Here it is fed into the minor-arc hypothesis of the (given) single-scale
estimate `ImprovKMT`, together with the two `MemLp` facts for the lifts, and the result is
transported from `AhalfR TZ` to `bileLiftSum` by the bridge. -/

/-- **Item 2.**  The single-scale minor-arc estimate, applied to the two lifts, in the form used by
the wiring: with `k = l - logN N` on the `f`-side (the `g`-side case is identical, with
`P.natDegree * (l - logN N)` and swapping the roles of `f` and `g`).

The bridge `bileLiftSum = AhalfR TZ …` is taken as an explicit hypothesis here (it is the
obligation of the companion module `BileLiftSum_eq_AhalfR`), as are the two `MemLp` facts (the
obligation of `memLp_bileLift`); everything else is discharged by the *proved*
`BileLiftKmtProjZero`. -/
theorem bileLiftSum_le_of_improv {P : Polynomial ℤ} (ψ : SchwartzMap ℝ ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Q : ℕ} [NeZero Q] {c : ℝ} (hc : 0 < c) {C : ℝ≥0}
    (hIρ : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      (Work.KMTContract.kmtProj ρ l (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) f = 0 ∨
        Work.KMTContract.kmtProj ρ l
          ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) g = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ => AhalfR TZ (N : NNReal) Polynomial.X P f g x)
          1 MeasureTheory.Measure.count
        ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
            (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
    {N l R : ℕ} (hN : 1 ≤ N) (hR : 0 < R)
    (hψ : ∀ ξ : ℝ, 1 < |ξ| → Work.Analysis.InverseTheory.realFourier (ψ : ℝ → ℂ) ξ = 0)
    (hk : (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) *
        ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < 1 / 4)
    (hRl : 4 * ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < (R : ℝ))
    {f g : ZMod Q → ℂ} (hf : MdlIwMinorArc ρ l Q f)
    (hbr : bileLiftSum P (ψ : ℝ → ℂ) R N f g
      = AhalfR TZ (N : NNReal) Polynomial.X P (bileLift (ψ : ℝ → ℂ) R f)
          (bileLift (ψ : ℝ → ℂ) R g))
    (hmf : MeasureTheory.MemLp (bileLift (ψ : ℝ → ℂ) R f) 2 MeasureTheory.Measure.count)
    (hmg : MeasureTheory.MemLp (bileLift (ψ : ℝ → ℂ) R g) 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (bileLiftSum P (ψ : ℝ → ℂ) R N f g) 1 MeasureTheory.Measure.count
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
          (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
        MeasureTheory.eLpNorm (bileLift (ψ : ℝ → ℂ) R f) 2 MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm (bileLift (ψ : ℝ → ℂ) R g) 2 MeasureTheory.Measure.count := by
  have hzero : Work.KMTContract.kmtProj ρ l
      (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) (bileLift (ψ : ℝ → ℂ) R f) = 0 :=
    BileLiftKmtProjZero ψ hρ hρ1 hR hψ hk hRl f hf
  have hmain := hIρ N l (bileLift (ψ : ℝ → ℂ) R f) (bileLift (ψ : ℝ → ℂ) R g) hN hmf hmg
    (Or.inl hzero)
  rwa [← hbr] at hmain

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open Filter MeasureTheory Polynomial Finset
open scoped ENNReal NNReal

open Submission.PointwiseErgodicTheorems

/-! ## Item 3: the ℓ² limits of the window, folded into the bounds

`BileWindowLimits` provides, for the window `ψ` and every `u : ZMod Q → ℂ` and `ε > 0`, the
eventual bound `‖bileLift ψ R u‖_{ℓ²} ≤ (1 + ε) ‖u‖_{L²(μ)}`.  Here it is (a) restated for
`bileLift` and (b) combined with the `ImprovKMT` bound of Item 2, so that the two factors
`‖bileLift ψ R f‖₂ ‖bileLift ψ R g‖₂` are replaced by the desired
`ofReal ((1+ε)·‖f‖_{L²}) · ofReal ((1+ε)·‖g‖_{L²})`. -/

/-- **Item 3(a).**  The eventual ℓ² bound for the lift, from the corresponding clause of
`BileWindowLimits` (taken here as an explicit hypothesis). -/
theorem bileLift_eLpNorm_two_le_of_window {ψ : SchwartzMap ℝ ℂ} {Q : ℕ} [NeZero Q]
    (hwin : ∀ (u : ZMod Q → ℂ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      MeasureTheory.eLpNorm (fun n : ℤ =>
          ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ))) * u (n : ZMod Q))
        2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (1 + ε) *
            ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 u))
    (u : ZMod Q → ℂ) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLift (ψ : ℝ → ℂ) R u) 2
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (1 + ε) *
            ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 u) := by
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := hwin u ε hε
  refine ⟨R₀, fun R hR => ?_⟩
  have hfun : (fun n : ℤ => ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ))) *
        u (n : ZMod Q)) = Work.KMTPlan.A6.bileLift (ψ : ℝ → ℂ) R u := rfl
  rw [← hfun]
  exact hR₀ R hR

/-- **Item 3(b).**  Folding the two ℓ² bounds into the `ImprovKMT` bound: the product of the two
`ℓ²` norms of the lifts is replaced by `ofReal ((1+ε)·‖f‖_{L²(μ)}) · ofReal ((1+ε)·‖g‖_{L²(μ)})`
(via `ENNReal.ofReal_mul`, applied to each factor separately — the *pair* is not a subterm of the
target, so it must be split factor by factor). -/
theorem bileLiftSum_le_of_gains {P : Polynomial ℤ} {ψ : SchwartzMap ℝ ℂ}
    {Q : ℕ} [NeZero Q] {N R l : ℕ} {f g : ZMod Q → ℂ} {c ρ : ℝ} {C : ℝ≥0} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hmain : MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLiftSum P (ψ : ℝ → ℂ) R N f g)
          1 MeasureTheory.Measure.count
        ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
            (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
          MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLift (ψ : ℝ → ℂ) R f) 2
            MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLift (ψ : ℝ → ℂ) R g) 2
            MeasureTheory.Measure.count)
    (hf : MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLift (ψ : ℝ → ℂ) R f) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (1 + ε) *
          ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 f))
    (hg : MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLift (ψ : ℝ → ℂ) R g) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (1 + ε) *
          ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 g)) :
    MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLiftSum P (ψ : ℝ → ℂ) R N f g) 1
        MeasureTheory.Measure.count
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
          (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
        ENNReal.ofReal ((1 + ε) * Work.Analysis.Concentration.LpNormZMod Q 2 f) *
        ENNReal.ofReal ((1 + ε) * Work.Analysis.Concentration.LpNormZMod Q 2 g) := by
  have h1ε : (0 : ℝ) ≤ 1 + ε := by linarith
  -- split each factor of the target separately: the *pair* is not a subterm of the goal
  have h1 : ENNReal.ofReal ((1 + ε) * Work.Analysis.Concentration.LpNormZMod Q 2 f)
      = ENNReal.ofReal (1 + ε) *
          ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 f) :=
    ENNReal.ofReal_mul h1ε
  have h2 : ENNReal.ofReal ((1 + ε) * Work.Analysis.Concentration.LpNormZMod Q 2 g)
      = ENNReal.ofReal (1 + ε) *
          ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 g) :=
    ENNReal.ofReal_mul h1ε
  refine hmain.trans ?_
  rw [h1, h2]
  exact (mul_le_mul' (mul_le_mul' le_rfl hf) le_rfl).trans (mul_le_mul' le_rfl hg)

end

end Work.KMTPlan.A6

/-
## Item 4: the `ε → 0` assembly (plan, refined while working it out)

All the pieces it consumes are now *fixed statements*, so the chain below can be written directly
against them; the only remaining explicit hypotheses are `hIρ` (the `ρ`-instantiation of
`ImprovKMT`), the bridge `BileLiftSum_eq_AhalfR` and the two `MemLp` facts (`memLp_bileLift`).

**Simplification found while working it out.**  The weighted-sum clause of `BileWindowLimits`
(Item 1(c)) is *not needed*: the `R → ∞` limit at fixed `N` (`BileLiftAhalfLimit`) already gives a
two-sided comparison between `‖bileLiftSum P ψ R N f g‖_{ℓ¹}` and
`‖bileHalvedAvg P N f g‖_{L¹(μ)}` — the `≤ (1+ε)` half by `eventually_le_of_tendsto_ofReal`
(Item 1(a)), and the reverse half `‖bileHalvedAvg‖ ≤ ‖bileLiftSum‖ + ε` by
`eventually_ge_of_tendsto_ofReal` applied to the *same* limit (the `ge`-companion of Item 1(a)).
The weighted sum was only a device for passing to the finite model, and the norm limit does that
job directly.

**Ordering: `N` first, then `R`.**  `BileHalvedAvgLimit` is an `N → ∞` limit, and
`BileLiftAhalfLimit` is a limit in `R` at *fixed* `N`; so for `ε > 0`:

1. choose `N ≥ 4 · 2^l · Q · iwQl ρ l` (this is `hk` of `BileLiftKmtProjZero` at
   `k = l - logN N`) and large enough that `⟨logN N⟩^{-c/ρ} ≤ ε` and that Item 1(b) gives
   `‖½ A(f,g)‖_{L¹(μ)} - ε ≤ ‖bileHalvedAvg P N f g‖_{L¹(μ)}`;
2. choose `R > 4 · Q · iwQl ρ l` (`hRl`) and large enough for the two halves of Item 1(a) and for
   the two ℓ² bounds of Item 3(a);
3. combine: `‖½A‖ - ε ≤ ‖bileHalvedAvg‖ ≤ (1+ε)‖bileLiftSum‖` (Item 1(a) reversed), and
   `‖bileLiftSum‖ ≤ C_ρ(2^{-cl}+ε)‖bileLift ψ R f‖₂‖bileLift ψ R g‖₂` (Item 2, using
   `MdlIwMinorArc ρ l Q f` and the *proved* `BileLiftKmtProjZero`), and those two ℓ² factors are
   `≤ ofReal ((1+ε)‖f‖_{L²})`, `≤ ofReal ((1+ε)‖g‖_{L²})` (Item 3(a)/(b));
4. let `ε → 0`: `½‖A(f,g)‖_{L¹(μ)} ≤ C_ρ 2^{-cl}‖f‖_{L²}‖g‖_{L²}`, i.e.
   `‖A(f,g)‖_{L¹(μ)} ≤ (2C_ρ) 2^{-cl}‖f‖_{L²}‖g‖_{L²}` — the claim of
   `Work.KMTPlan.A6.MdlBileR1OfImprov` at this `ρ`, with the rate `c` of `hI` (independent of
   `ρ`) and the constant `2C_ρ`.

The last step is closed by `le_of_tendsto_of_le` after combining the `ε`-bounds into a single
eventual inequality in `R` at the chosen `N`, and then sending `N → ∞`; the `ε`-bookkeeping is the
only remaining work, and it is the bookkeeping for which the three primitives of this module were
written.
-/

namespace Work.KMTPlan.A6

noncomputable section

open Filter MeasureTheory Polynomial Finset
open scoped ENNReal

/-- The normalized `L^p`-norm on `ℤ/Qℤ` is nonnegative. -/
theorem LpNormZMod_nonneg (Q : ℕ) [NeZero Q] (p : ℝ) (f : ZMod Q → ℂ) :
    0 ≤ Work.Analysis.Concentration.LpNormZMod Q p f := by
  unfold Work.Analysis.Concentration.LpNormZMod
  refine Real.rpow_nonneg (mul_nonneg (by positivity) ?_) _
  exact Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p

/-- **Item 1(a).**  From the `R`-limit at fixed `N`: for every `ε > 0` and all large `R`,
`‖bileLiftSum P ψ R N u v‖_{ℓ¹} ≤ ‖bileHalvedAvg P N u v‖_{L¹(μ)} + ε`. -/
theorem bileLiftSum_le_of_tendsto {P : Polynomial ℤ} {ψ : ℝ → ℂ}
    {Q N : ℕ} [NeZero Q] {u v : ZMod Q → ℂ}
    (hlim : Filter.Tendsto (fun R : ℕ => MeasureTheory.eLpNorm
        (Work.KMTPlan.A6.bileLiftSum P ψ R N u v) 1 MeasureTheory.Measure.count)
      Filter.atTop
      (nhds (ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
        (Work.KMTPlan.A6.bileHalvedAvg P N u v))))) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      MeasureTheory.eLpNorm (Work.KMTPlan.A6.bileLiftSum P ψ R N u v)
          1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
            (Work.KMTPlan.A6.bileHalvedAvg P N u v) + ε) :=
  eventually_le_of_tendsto_ofReal (LpNormZMod_nonneg Q 1 _) hlim

/-- **Item 1(b).**  From the `N`-limit: for every `ε > 0` and all large `N`,
`‖½ A(u,v)‖_{L¹(μ)} - ε ≤ ‖bileHalvedAvg P N u v‖_{L¹(μ)}`. -/
theorem bileHalvedAvg_ge_of_tendsto {P : Polynomial ℤ}
    {Q : ℕ} [NeZero Q] {u v : ZMod Q → ℂ}
    (hlim : Filter.Tendsto (fun N : ℕ => ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
        (Work.KMTPlan.A6.bileHalvedAvg P N u v)))
      Filter.atTop
      (nhds (ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
        (fun z : ZMod Q => (1 / 2 : ℂ) *
          Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q u v z))))) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Work.Analysis.Concentration.LpNormZMod Q 1
          (fun z : ZMod Q => (1 / 2 : ℂ) *
            Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q u v z) - ε
        ≤ Work.Analysis.Concentration.LpNormZMod Q 1
            (Work.KMTPlan.A6.bileHalvedAvg P N u v) := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_ge_of_tendsto_ofReal (LpNormZMod_nonneg Q 1 _) hlim ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  have h := hN₀ N hN
  rwa [ENNReal.ofReal_le_ofReal_iff (LpNormZMod_nonneg Q 1 _)] at h

/-- **Item 1(c).**  The weighted-sum lower bound of `BileWindowLimits`, in the real form used by
the wiring: for every `ε > 0` and all large `R`,
`(1 - ε) ‖u‖_{L¹(μ)} ≤ R⁻¹ ∑_x ‖ψ(x/R)‖² ‖u (x mod Q)‖`. -/
theorem bileWeightedSum_ge_of_window (ψ : ℝ → ℂ) {Q : ℕ} [NeZero Q] (u : ZMod Q → ℂ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ENNReal.ofReal ((1 - ε) * Work.Analysis.Concentration.LpNormZMod Q 1 u)
        ≤ ENNReal.ofReal ((R : ℝ)⁻¹ *
            tsum (fun x : ℤ => (‖ψ ((x : ℝ) / (R : ℝ))‖ ^ 2) * ‖u (x : ZMod Q)‖))) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      (1 - ε) * Work.Analysis.Concentration.LpNormZMod Q 1 u
        ≤ (R : ℝ)⁻¹ * tsum (fun x : ℤ => (‖ψ ((x : ℝ) / (R : ℝ))‖ ^ 2) * ‖u (x : ZMod Q)‖) := by
  intro ε hε
  obtain ⟨R₀, hR₀⟩ := h ε hε
  refine ⟨R₀, fun R hR => ?_⟩
  have h' := hR₀ R hR
  have hnn : (0 : ℝ) ≤ (R : ℝ)⁻¹ * tsum (fun x : ℤ =>
      (‖ψ ((x : ℝ) / (R : ℝ))‖ ^ 2) * ‖u (x : ZMod Q)‖) :=
    mul_nonneg (by positivity) (tsum_nonneg fun x => mul_nonneg (by positivity) (norm_nonneg _))
  rwa [ENNReal.ofReal_le_ofReal_iff hnn] at h'

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open Filter MeasureTheory Polynomial Finset
open scoped ENNReal NNReal

/-- **The four-factor `ofReal` product.**  `(C : ℝ≥0∞) · ofReal G · ofReal a · ofReal b` is the
`ofReal`-image of the real product `C · G · a · b` (all nonnegative).  This is what turns the
`ℝ≥0∞`-valued conclusions of Items 2 and 3 into the real inequality of Item 4. -/
theorem ofReal_mul_four (C : NNReal) (G a b : ℝ) (hG : 0 ≤ G) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (C : ENNReal) * ENNReal.ofReal G * ENNReal.ofReal a * ENNReal.ofReal b
      = ENNReal.ofReal ((C : ℝ) * G * a * b) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  rw [← ENNReal.ofReal_mul (NNReal.coe_nonneg C),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]

/-- **Item 1(d).**  The `ge`-companion of Item 1(a): for every `ε > 0` and all large `R` the
halved average is dominated by the lifted sum, `‖bileHalvedAvg‖ - ε ≤ ‖bileLiftSum‖`.  Together
with Item 1(a) this is the two-sided comparison at fixed `N`. -/
theorem bileHalvedAvg_le_of_window_ge {P : Polynomial ℤ} {ψ : ℝ → ℂ} {Q N : ℕ} [NeZero Q]
    {u v : ZMod Q → ℂ}
    (hlim : Filter.Tendsto (fun R : ℕ => MeasureTheory.eLpNorm
        (bileLiftSum P ψ R N u v) 1 MeasureTheory.Measure.count)
      Filter.atTop
      (nhds (ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
        (bileHalvedAvg P N u v))))) :
    ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1 (bileHalvedAvg P N u v) - ε)
        ≤ MeasureTheory.eLpNorm (bileLiftSum P ψ R N u v) 1 MeasureTheory.Measure.count :=
  eventually_ge_of_tendsto_ofReal (LpNormZMod_nonneg Q 1 _) hlim

/-- **Item 2, `g`-side.**  The companion of `bileLiftSum_le_of_improv` for the case that the
*second* input carries the Ionescu--Wainger minor-arc condition: the `ImprovKMT` hypothesis is then
discharged through the *second* alternative
`kmtProj ρ l (d · k) (bileLift ψ R g) = 0`, which is again `BileLiftKmtProjZero` applied to `g`
at the height `k = d · (l - Log N)`. -/
theorem bileLiftSum_le_of_improvG {P : Polynomial ℤ} (ψ : SchwartzMap ℝ ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Q : ℕ} [NeZero Q] {c : ℝ} (hc : 0 < c) {C : NNReal}
    (hIρ : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      (Work.KMTContract.kmtProj ρ l (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) f = 0 ∨
        Work.KMTContract.kmtProj ρ l
          ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) g = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.AhalfR
          Submission.PointwiseErgodicTheorems.TZ (N : NNReal) Polynomial.X P f g x)
          1 MeasureTheory.Measure.count
        ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
            (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
    {N l R : ℕ} (hN : 1 ≤ N) (hR : 0 < R)
    (hψ : ∀ ξ : ℝ, 1 < |ξ| → Work.Analysis.InverseTheory.realFourier (ψ : ℝ → ℂ) ξ = 0)
    (hk : (2 : ℝ) ^ ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) *
        ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < 1 / 4)
    (hRl : 4 * ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < (R : ℝ))
    {f g : ZMod Q → ℂ} (hg : MdlIwMinorArc ρ l Q g)
    (hbr : bileLiftSum P (ψ : ℝ → ℂ) R N f g
      = Submission.PointwiseErgodicTheorems.AhalfR Submission.PointwiseErgodicTheorems.TZ
          (N : NNReal) Polynomial.X P (bileLift (ψ : ℝ → ℂ) R f) (bileLift (ψ : ℝ → ℂ) R g))
    (hmf : MeasureTheory.MemLp (bileLift (ψ : ℝ → ℂ) R f) 2 MeasureTheory.Measure.count)
    (hmg : MeasureTheory.MemLp (bileLift (ψ : ℝ → ℂ) R g) 2 MeasureTheory.Measure.count) :
    MeasureTheory.eLpNorm (bileLiftSum P (ψ : ℝ → ℂ) R N f g) 1 MeasureTheory.Measure.count
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
          (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
        MeasureTheory.eLpNorm (bileLift (ψ : ℝ → ℂ) R f) 2 MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm (bileLift (ψ : ℝ → ℂ) R g) 2 MeasureTheory.Measure.count := by
  have hzero : Work.KMTContract.kmtProj ρ l
      ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ)))
      (bileLift (ψ : ℝ → ℂ) R g) = 0 :=
    BileLiftKmtProjZero ψ hρ hρ1 hR hψ hk hRl g hg
  have hmain := hIρ N l (bileLift (ψ : ℝ → ℂ) R f) (bileLift (ψ : ℝ → ℂ) R g) hN hmf hmg
    (Or.inr hzero)
  rwa [← hbr] at hmain

/-- **Item 4 (the fixed-scale step).**  Putting Items 1(d), 2 (both sides), 3(a) and 3(b) together:
for `N` large enough (the hypotheses `hN1`, `hQN`, `hkf`, `hkg`, `hδ`) and `f` or `g` minor
arc, there is `R₀` such that for all `R ≥ R₀`

  `‖bileHalvedAvg P N f g‖_{L¹(μ)} ≤ C · (2^{-cl} + η) · ((1+η)‖f‖₂) · ((1+η)‖g‖₂) + η`.

The `η` on the right is the price of replacing the limit `(Log N)^{-c/ρ}` (which is `≤ η` by
`hδ`) and of the two-sided comparison in `R`. -/
theorem bileHalvedAvg_le_of_improv {P : Polynomial ℤ} (ψ : SchwartzMap ℝ ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Q : ℕ} [NeZero Q] (hQ : 1 ≤ Q)
    {c : ℝ} (hc : 0 < c) {C : NNReal}
    (hIρ : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      (Work.KMTContract.kmtProj ρ l (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) f = 0 ∨
        Work.KMTContract.kmtProj ρ l
          ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) g = 0) →
      MeasureTheory.eLpNorm (fun x : ℤ => Submission.PointwiseErgodicTheorems.AhalfR
          Submission.PointwiseErgodicTheorems.TZ (N : NNReal) Polynomial.X P f g x)
          1 MeasureTheory.Measure.count
        ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
            (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
    (hψ : ∀ ξ : ℝ, 1 < |ξ| → Work.Analysis.InverseTheory.realFourier (ψ : ℝ → ℂ) ξ = 0)
    (hwin : ∀ (u : ZMod Q → ℂ) (ε : ℝ), 0 < ε → ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      MeasureTheory.eLpNorm (fun n : ℤ =>
          ((Real.sqrt (R : ℝ))⁻¹ : ℂ) * (ψ ((n : ℝ) / (R : ℝ))) * u (n : ZMod Q))
        2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (1 + ε) *
            ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 2 u))
    (hlimR : ∀ (N : ℕ) (u v : ZMod Q → ℂ), Q ≤ N →
      Filter.Tendsto (fun R : ℕ => MeasureTheory.eLpNorm
          (bileLiftSum P (ψ : ℝ → ℂ) R N u v) 1 MeasureTheory.Measure.count)
        Filter.atTop
        (nhds (ENNReal.ofReal (Work.Analysis.Concentration.LpNormZMod Q 1
          (bileHalvedAvg P N u v)))))
    {l N : ℕ} (hN1 : 1 ≤ N) (hQN : Q ≤ N) {η : ℝ} (hη : 0 < η)
    (hkf : (2 : ℝ) ^ (-(Work.Analysis.EndVar.logN N) + (l : ℤ)) *
        ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < 1 / 4)
    (hkg : (2 : ℝ) ^ ((P.natDegree : ℤ) * (-(Work.Analysis.EndVar.logN N) + (l : ℤ))) *
        ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < 1 / 4)
    (hδ : (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ)) ≤ η)
    {f g : ZMod Q → ℂ} (hm : MdlIwMinorArc ρ l Q f ∨ MdlIwMinorArc ρ l Q g) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      Work.Analysis.Concentration.LpNormZMod Q 1 (bileHalvedAvg P N f g) ≤
        (C : ℝ) * ((2 : ℝ) ^ (-(c * (l : ℝ))) + η) *
          ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 f) *
          ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 g) + η := by
  obtain ⟨R₁, hR₁⟩ := bileHalvedAvg_le_of_window_ge (hlimR N f g hQN) η hη
  obtain ⟨R₂, hR₂⟩ := bileLift_eLpNorm_two_le_of_window hwin f η hη
  obtain ⟨R₃, hR₃⟩ := bileLift_eLpNorm_two_le_of_window hwin g η hη
  refine ⟨max (max R₁ R₂) (max R₃ (4 * (Q * Work.Analysis.IonescuWainger.iwQl ρ l) + 1)),
    fun R hR => ?_⟩
  have hR1 : R₁ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hR2 : R₂ ≤ R := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hR3 : R₃ ≤ R := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hR
  have hR4 : 4 * (Q * Work.Analysis.IonescuWainger.iwQl ρ l) + 1 ≤ R :=
    le_trans (le_max_right R₃ (4 * (Q * Work.Analysis.IonescuWainger.iwQl ρ l) + 1))
      (le_trans (le_max_right (max R₁ R₂)
        (max R₃ (4 * (Q * Work.Analysis.IonescuWainger.iwQl ρ l) + 1))) hR)
  have hRpos : 0 < R := by omega
  have hRl : 4 * ((Q : ℝ) * (Work.Analysis.IonescuWainger.iwQl ρ l : ℝ)) < (R : ℝ) := by
    have h : (4 * (Q * Work.Analysis.IonescuWainger.iwQl ρ l) + 1 : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast hR4
    push_cast at h
    linarith
  have ha := hR₁ R hR1
  have hbr : bileLiftSum P (ψ : ℝ → ℂ) R N f g
      = Submission.PointwiseErgodicTheorems.AhalfR Submission.PointwiseErgodicTheorems.TZ
          (N : NNReal) Polynomial.X P (bileLift (ψ : ℝ → ℂ) R f) (bileLift (ψ : ℝ → ℂ) R g) :=
    BileLiftSum_eq_AhalfR P (ψ : ℝ → ℂ) R N Q f g
  have hmf := memLp_bileLift ψ R f
  have hmg := memLp_bileLift ψ R g
  have hmain : MeasureTheory.eLpNorm (bileLiftSum P (ψ : ℝ → ℂ) R N f g) 1
        MeasureTheory.Measure.count
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ))) +
          (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
        MeasureTheory.eLpNorm (bileLift (ψ : ℝ → ℂ) R f) 2 MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm (bileLift (ψ : ℝ → ℂ) R g) 2 MeasureTheory.Measure.count := by
    rcases hm with hf | hg
    · exact bileLiftSum_le_of_improv ψ hρ hρ1 hc hIρ hN1 hRpos hψ hkf hRl hf hbr hmf hmg
    · exact bileLiftSum_le_of_improvG ψ hρ hρ1 hc hIρ hN1 hRpos hψ hkg hRl hg hbr hmf hmg
  have hlf := hR₂ R hR2
  have hlg := hR₃ R hR3
  have hgains := bileLiftSum_le_of_gains hη.le hmain hlf hlg
  have hcomb := ha.trans hgains
  have hlogNnn : (0 : ℝ) ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    simp only [Work.Analysis.EndVar.logN]
    positivity
  have hGnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(c * (l : ℝ))) +
      (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ)) :=
    add_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hlogNnn _)
  have hAnn : (0 : ℝ) ≤ (1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 f :=
    mul_nonneg (by linarith) (LpNormZMod_nonneg Q 2 f)
  have hBnn : (0 : ℝ) ≤ (1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 g :=
    mul_nonneg (by linarith) (LpNormZMod_nonneg Q 2 g)
  rw [ofReal_mul_four C ((2 : ℝ) ^ (-(c * (l : ℝ))) +
      (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ)))
      ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 f)
      ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 g) hGnn hAnn hBnn] at hcomb
  have hreal : Work.Analysis.Concentration.LpNormZMod Q 1 (bileHalvedAvg P N f g) - η
      ≤ (C : ℝ) * ((2 : ℝ) ^ (-(c * (l : ℝ))) +
          (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
        ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 f) *
        ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 g) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (NNReal.coe_nonneg C) hGnn)
      hAnn) hBnn)).mp hcomb
  have h1 : (2 : ℝ) ^ (-(c * (l : ℝ))) + (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))
      ≤ (2 : ℝ) ^ (-(c * (l : ℝ))) + η := by linarith
  have hstep : (C : ℝ) * ((2 : ℝ) ^ (-(c * (l : ℝ))) +
        (Work.Analysis.EndVar.logN N : ℝ) ^ (-(c / ρ))) *
      ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 f) *
      ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 g)
      ≤ (C : ℝ) * ((2 : ℝ) ^ (-(c * (l : ℝ))) + η) *
      ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 f) *
      ((1 + η) * Work.Analysis.Concentration.LpNormZMod Q 2 g) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h1 (NNReal.coe_nonneg C)) hAnn) hBnn
  linarith [hreal, hstep]

end

end Work.KMTPlan.A6

namespace Work.KMTPlan.A6

noncomputable section

open Filter MeasureTheory Polynomial Finset
open scoped ENNReal NNReal

/-- **The `η`-absorption.**  For nonnegative `C, G, A, B` and every `ε > 0` one can choose `η > 0`
small enough that the perturbation `(G+η)(1+η)²` of `G` and the extra `+η` cost at most `ε`.  This
is the last step of the assembly: the `ε`-form of the estimate is converted into the `η = 0` form. -/
theorem bile_eta_absorption {C G A B ε : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ C * (G + η) * ((1 + η) * A) * ((1 + η) * B) + η
      ≤ C * G * A * B + ε := by
  set D : ℝ := C * A * B * (3 * G + 4) + 1 with hD
  have hDpos : 0 < D := by
    rw [hD]
    have : 0 ≤ C * A * B * (3 * G + 4) := by positivity
    linarith
  refine ⟨min 1 (ε / D), lt_min one_pos (div_pos hε hDpos), ?_⟩
  set η : ℝ := min 1 (ε / D) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos hε hDpos)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / D := min_le_right _ _
  -- the polynomial core: `(G+η)(1+η)² ≤ G + η(3G+4)` for `0 < η ≤ 1`
  have hkey : (G + η) * (1 + η) ^ 2 ≤ G + η * (3 * G + 4) := by
    have h1 : 0 ≤ G * (1 - η) := mul_nonneg hG (by linarith)
    have h2 : 0 ≤ 3 - 2 * η - η ^ 2 := by nlinarith [hη1, hη0.le, sq_nonneg η]
    nlinarith [h1, h2, hη0.le]
  have hAB : (0 : ℝ) ≤ A * B := mul_nonneg hA hB
  have hstep : C * (G + η) * ((1 + η) * A) * ((1 + η) * B)
      ≤ C * G * A * B + η * (C * A * B * (3 * G + 4)) := by
    have h1 : (G + η) * (1 + η) * (1 + η) * (A * B) ≤ (G + η * (3 * G + 4)) * (A * B) :=
      mul_le_mul_of_nonneg_right (by nlinarith [hkey]) hAB
    have h2 : C * ((G + η) * (1 + η) * (1 + η) * (A * B))
        ≤ C * ((G + η * (3 * G + 4)) * (A * B)) := mul_le_mul_of_nonneg_left h1 hC
    calc C * (G + η) * ((1 + η) * A) * ((1 + η) * B)
        = C * ((G + η) * (1 + η) * (1 + η) * (A * B)) := by ring
      _ ≤ C * ((G + η * (3 * G + 4)) * (A * B)) := h2
      _ = C * G * A * B + η * (C * A * B * (3 * G + 4)) := by ring
  have hfin : η * (C * A * B * (3 * G + 4)) + η ≤ ε := by
    have h1 : η * (C * A * B * (3 * G + 4)) + η ≤ η * D := by
      rw [hD]; nlinarith [hη0.le]
    have h2 : η * D ≤ ε := by
      have := mul_le_mul_of_nonneg_right hηε hDpos.le
      rwa [div_mul_cancel₀ ε hDpos.ne'] at this
    linarith
  linarith [hstep, hfin]

end

end Work.KMTPlan.A6
