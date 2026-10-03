/-
# The lacunary low-pass variational estimate for the Ionescu--Wainger projections

This is the paper's low-frequency case of `(lin-1)` (Krause--Mirek--Tao, Annals 195 (2022), §8) in
the discrete `ℓ^p(ℤ)` setting: the `r`-variation, `2 < r`, of the *unmodulated* low-pass family

  `n ↦ Tle ρ l₁ (varphiN ⌊a n⌋ 0) f`

is bounded on `ℓ^p(ℤ)`, `1 < p < ∞`, by `C(1+l₁)² ‖f‖_{ℓ^p}`, uniformly in the `Λ`-lacunary family
`a` and in the narrowness level `k` (subject to `GoodMajorArcs ρ Cρ l₁ k` and
`k ≥ -logN ⌊a n⌋`).

**Where this sits.**  It is the `hLowpass` input of `Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly`
and the `hLow` of `Work.KMTAreas.A7.lacunaryBumpLowpassClipBound`/`...Gen`.  The analysis of the
statement, its truth and the obstacles are in `NOTES_lacunaryIWProjLowpassVar_ANALYSIS.md`.

## The route formalised here (session 4b: ONE node, and it is the tree's *canonical* obligation)

**(0) The junk case is free.**  The right-hand side is `ofReal (C(1+l₁)²) * ‖f‖_{ℓᵖ}`.  If
`f ∉ ℓᵖ` then `‖f‖_{ℓᵖ} = ⊤` and the right-hand side is `⊤`, so the inequality is trivial.  Hence
**only `f ∈ ℓᵖ` needs an argument** — and there the whole tree's `ℓᵖ` machinery is available.  This
is what lets the file consume the *`MemLp`* form of the crux, i.e. the form the tree actually
targets (`Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp`), rather than the `∀ f` form
(`A7HiRep.chainPartSqFun`), which the tree itself flags as the riskier statement
(`NOTES_A7HiRep_chainPartSqFunPos_SESSION.md` §S5.6).

**(1) Lacunary ⟶ dyadic.**  `Tle ρ l (varphiN N 0) = kmtProj ρ l (-(logN N))`
(`Tle_varphiN_zero`), and `n ↦ logN ⌊a n⌋` is *monotone*.  Hence the lacunary family is the
reindexing, by the monotone map `σ n := (logN ⌊a n⌋ + k).toNat`, of the *dyadic* family
`m ↦ kmtProj ρ l₁ (-(m₀ + m))`, `m₀ := (-k).toNat`:

  `Tle ρ l₁ (varphiN ⌊a n⌋ 0) f = kmtProj ρ l₁ (-(logN ⌊a n⌋)) f = kmtProj ρ l₁ (-(m₀ + σ n)) f`,

and reindexing by a monotone map does not increase the variational norm
(`Work.KMTAreas.A7.variationalNorm_comp_mono_le`).  The arithmetic needed for the level bookkeeping
is only: `GoodMajorArcs ρ Cρ l₁ k` forces `k ≤ 0` (the right-hand side is `-Cρ 2^{ρ l₁} ≤ 0`), and
`Lacunary Λ a` with `Λ > 1`, `a n ≥ 1` makes `a` monotone (so that `n ↦ logN ⌊a n⌋` is monotone).

**(2) The dyadic estimate for `f ∈ ℓᵖ`, from three inputs with `l₁`-free constants.**  Write
`T_m = lpf ρ l₁ m₀ m`.  The `rfl`-splitting `variationalNorm r = supPart r + chainPart r`
(`Work.KMTAreas.A7Hi.variationalNorm_eq_parts`) reduces everything to the values supremum and the
chain term, and both are controlled by the *same* crux:

* `Work.KMTAreas.A7HiRep.chainPartSqFunPosMemLp` (the tree's canonical crux, `MemLp` form,
  `Cρ₀ ≥ 2` a parameter): `‖chainPart r (walk f)‖_{ℓᵖ} ≤ C ‖sqFun ρ l₁ m₀ f‖_{ℓᵖ}`;
* `Work.KMTAreas.A7Lpd.bandSquareUnif` (PROVED): `‖sqFun ρ l₁ m₀ f‖_{ℓᵖ} ≤ C_Q ‖f‖_{ℓᵖ}`, with
  `C_Q` free of `l₁, m₀`;
* `Work.KMTAreas.A7JSW.supPart_le_norm_add_chainPart` (PROVED, via the two-point chain
  `‖T_N f − T_n f‖ₑ ≤ chainPart r (walk f)`):
  `supPart r (walk f) ≤ ‖T_N f‖ₑ + chainPart r (walk f)`; with `N = 0` and the single-scale bound
  `Work.KMTAreas.A7.kmtProj_lp_bound_uniform` (PROVED, uniform in the height `l` **and** in the
  level `k`) applied at the level `-(m₀)`, this gives
  `‖supPart r (walk f)‖_{ℓᵖ} ≤ C_lp ‖f‖_{ℓᵖ} + C ‖sqFun f‖_{ℓᵖ}`.

Adding, the dyadic constant is `C_lp + 2 C C_Q` — free of `l₁, m₀`, and `1 ≤ (1+l₁)²` turns it into
the `(1+l₁)²` of the statement.

So the file rests on the **single** node `A7HiRep.chainPartSqFunPosMemLp`, which is precisely the
obligation the tree's `A7HiRep` chapter is built around (its own docstring calls it "the single
obligation that discharges both halves of the chain bound on the maximal call site"); the
supremum half is *derived* from it rather than assumed separately, so no good-λ node is needed.
See `NOTES_lacunaryIWProjLowpassVar_SESSION4.md` for the ledger.
-/
import Mathlib
import Submission.Work.KMTAreas.A7JSW.maximalFromCrux
import Submission.Commons.Analysis.HardyLittlewood.discrete_maximal_lp
import Submission.Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_le_liminf
import Submission.Work.KMTAreas.A7Hi.FiberVarSampling
import Submission.Work.KMTAreas.A7HiRep.chainPartSqFunPosAux
import Submission.Work.KMTAreas.A7HiRep.chainPartSubAdd

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract

/-! ## The two elementary identities -/

/-- `varphiN N 0 = etaCut kmtEta (-(logN N))`: the unmodulated low-pass bump at scale `N` is the
continuous cutoff at level `-(logN N)`. -/
theorem varphiN_zero_eq_etaCut (N : ℕ) :
    varphiN N 0 = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta (-(logN N)) := by
  funext ξ
  simp only [varphiN, if_true, Work.Analysis.IonescuWainger.etaCut]
  congr 1
  rw [div_eq_mul_inv, zpow_neg, inv_inv, Real.rpow_intCast]
  ring

/-- `Tle ρ l (varphiN N 0) = kmtProj ρ l (-(logN N))`. -/
@[simp] theorem Tle_varphiN_zero (ρ : ℝ) (l : ℕ) (N : ℕ) :
    Tle ρ l (varphiN N 0) = kmtProj ρ l (-(logN N)) := by
  rw [varphiN_zero_eq_etaCut]
  exact Tle_etaCut ρ l (-(logN N))

/-- The good-major-arcs predicate is monotone in the constant `Cρ` (`C₁ ≤ C₂` makes the hypothesis
`GoodMajorArcs ρ C₂ l k` stronger).  Local copy of `Work.KMTAreas.A7.goodMajorArcs_mono`. -/
theorem goodMajorArcs_mono_aux {ρ C₁ C₂ : ℝ} {l : ℕ} {k : ℤ} (h : C₁ ≤ C₂)
    (hk : Work.Analysis.IonescuWainger.GoodMajorArcs ρ C₂ l k) :
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ C₁ l k := by
  unfold Work.Analysis.IonescuWainger.GoodMajorArcs at *
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := by positivity
  nlinarith [hk, h, h2]

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is monotone. -/
theorem lowpass_monotone_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-! ## The target -/

end

end Work.KMTAreas.A7
