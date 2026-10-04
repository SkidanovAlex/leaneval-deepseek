import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.summable_wt_zpow
import Submission.Work.Diff.STE.Comp.young_conv_lp
import Submission.Work.Diff.STE.flat.Sobolev

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp `L^{2p}` Sobolev bound on the torus — and a defect in the requested statement

## The requested statement is FALSE

The lemma requested at this path was

```
theorem norm_seriesFun_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (hp : 1 ≤ p) (j : ℝ)
    (hj : (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) < j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => ((Work.Diff.STE.wt k) ^ j) * ‖γ k‖ ^ 2) →
      (∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖Work.Diff.STE.seriesFun γ x‖ ^ (2 * p)) ^ (1 / (2 * p))
        ≤ C * (∑' k : ι → ℤ, ((Work.Diff.STE.wt k) ^ j) * ‖γ k‖ ^ 2) ^ (1 / 2)
```

The exponent `(1 / 2)` of the right-hand side carries no type ascription, so Lean elaborates it as
**natural** number division; since `(1 : ℕ) / 2 = 0` (`nat_exp_default` below), the requested
right-hand side is `C * S ^ (0 : ℕ) = C * 1 = C`.  The requested statement therefore asserts the
*uniform* bound `‖seriesFun γ‖_{L^{2p}} ≤ C`, with a constant `C` independent of `γ`, and is
**false**: `requested_statement_false` below exhibits, for every `C`, a coefficient family `γ`
(namely `γ = n • δ₀`, whose Fourier series is the constant function `n`) whose weighted mass
`Σ_k (wt k)^j ‖γ k‖²` is finite while `‖seriesFun γ‖_{L^{2p}} = n > C`.

The statement *intended* by the docstring — with the real exponent `(1 / 2 : ℝ)` — is the sharp
Sobolev embedding `H^j(𝕋^ι) ⊆ L^{2p}(𝕋^ι)` for `j > card ι * (1/2 - 1/(2p))`.  It is true and is
proved in `Submission/Work/Diff/STE/flat/Sobolev/rnorm_seriesFun_rpow_le.lean`
(`Work.Diff.STE.flat.Sobolev.rnorm_seriesFun_rpow_le`).  The present file contains the assembly of
that proof (`exists_bound_of_pieces`) together with the formal refutation of the requested text.

## The proof of the intended statement

Split the frequency lattice into the dyadic annuli `annulus m = {k | 2^{2m} ≤ ⟨k⟩² < 2^{2m+2}}`
(see `Sobolev.lean`); estimate each block `seriesFun (blockCoeff m γ)` by its sup norm and its `L²`
norm (Hölder interpolation gives the factor `2^{-m(j - n(1/2-1/(2p)))}`); sum the resulting
geometric series with Cauchy–Schwarz in the block index; the countable `L^q` triangle inequality
(Minkowski) transfers the estimate to the whole series.

The assembly below takes the four analytic inputs as explicit hypotheses (so that it could be
developed independently of them); they are supplied by
`Submission/Work/Diff/STE/flat/Sobolev/block_rnorm_le.lean`,
`.../tsum_annulus.lean`, `.../summable_blockMass.lean` and `.../rnorm_tsum_le.lean`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The assembly of the sharp Sobolev bound.**  Given the per-block estimate, the dyadic
rearrangement, the summability of the block masses and Minkowski's inequality for series in `L^q`,
one has `‖seriesFun γ‖_{L^{2p}} ≤ C · (Σ_k ⟨k⟩^{2j} ‖γ k‖²)^{1/2}` whenever
`j > card ι * (1/2 - 1/(2p))`. -/
theorem exists_bound_of_pieces
    (p : ℝ) (hp : 1 ≤ p) (j : ℝ)
    (hj : (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) < j)
    (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η)
    (hblock : ∀ (m : ℕ) (γ : (ι → ℤ) → ℂ), Summable (fun k : ι → ℤ => ‖γ k‖) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) →
      rnorm (2 * p) (Work.Diff.STE.seriesFun (blockCoeff m γ))
        ≤ K * (2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ))
    (hrearrC : ∀ (g : (ι → ℤ) → ℂ), Summable g →
      (∑' m : ℕ, ∑' k : ι → ℤ, blockFun m g k) = ∑' k : ι → ℤ, g k)
    (hrearrR : ∀ (g : (ι → ℤ) → ℝ), Summable g →
      (∑' m : ℕ, ∑' k : ι → ℤ, blockFun m g k) = ∑' k : ι → ℤ, g k)
    (hsummass : ∀ (γ : (ι → ℤ) → ℂ), Summable (fun k : ι → ℤ => ‖γ k‖) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) →
      Summable (fun m : ℕ => blockMass j m γ))
    (hmink : ∀ (q : ℝ), 1 ≤ q → ∀ {g : ℕ → (ι → ℝ) → ℂ} {f : (ι → ℝ) → ℂ},
      (∀ m : ℕ, MemLp (g m) (ENNReal.ofReal q)
        (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) →
      AEMeasurable f (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) →
      (∀ x : ι → ℝ, f x = ∑' m : ℕ, g m x) →
      Summable (fun m : ℕ => rnorm q (g m)) →
      rnorm q f ≤ ∑' m : ℕ, rnorm q (g m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) →
      rnorm (2 * p) (Work.Diff.STE.seriesFun γ)
        ≤ C * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have h2p : 2 ≤ 2 * p := by linarith
  -- the geometric ratio of the summation over the dyadic blocks
  have hr0 : 0 ≤ (2 : ℝ) ^ (-(2 * η)) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-(2 * η)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable fun m : ℕ => ((2 : ℝ) ^ (-(2 * η))) ^ m :=
    summable_geometric_of_lt_one hr0 hr1
  have hGnn : 0 ≤ ∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m :=
    tsum_nonneg fun m => pow_nonneg hr0 m
  -- the square of the per-block weight is the geometric term
  have hsq : ∀ m : ℕ, ((2 : ℝ) ^ (-(m : ℝ) * η)) ^ (2 : ℝ) = ((2 : ℝ) ^ (-(2 * η))) ^ m := by
    intro m
    have hL : ((2 : ℝ) ^ (-(m : ℝ) * η)) ^ (2 : ℝ)
        = (2 : ℝ) ^ (-(2 * η) * (m : ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hR : ((2 : ℝ) ^ (-(2 * η))) ^ m = (2 : ℝ) ^ (-(2 * η) * (m : ℝ)) := by
      rw [← Real.rpow_natCast (x := (2 : ℝ) ^ (-(2 * η))) (n := m),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hL, hR]
  refine ⟨max 1 (K * (∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m) ^ (1 / 2 : ℝ)),
    le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro γ h2
  by_cases h1 : Summable fun k : ι → ℤ => ‖γ k‖
  · -- main case: `γ ∈ ℓ¹`
    -- (1) the pointwise dyadic decomposition of the series
    have hdec : ∀ x : ι → ℝ, Work.Diff.STE.seriesFun γ x
        = ∑' m : ℕ, Work.Diff.STE.seriesFun (blockCoeff m γ) x := by
      intro x
      have hsum : Summable (fun k : ι → ℤ => γ k * Work.Diff.STE.fourierExp k x) := by
        refine Summable.of_norm_bounded (g := fun k : ι → ℤ => ‖γ k‖) h1 (fun k => ?_)
        rw [norm_mul, Work.Diff.STE.BesselCont.norm_fourierExp_char, mul_one]
      have h := hrearrC (fun k : ι → ℤ => γ k * Work.Diff.STE.fourierExp k x) hsum
      show (∑' k : ι → ℤ, γ k * Work.Diff.STE.fourierExp k x)
        = ∑' m : ℕ, Work.Diff.STE.seriesFun (blockCoeff m γ) x
      rw [← h]
      refine tsum_congr fun m => ?_
      show (∑' k : ι → ℤ, blockFun m (fun k : ι → ℤ => γ k * Work.Diff.STE.fourierExp k x) k)
        = ∑' k : ι → ℤ, blockCoeff m γ k * Work.Diff.STE.fourierExp k x
      refine tsum_congr fun k => ?_
      by_cases hk : k ∈ annulus m
      · simp only [blockCoeff, blockFun]
        simp [hk]
      · simp only [blockCoeff, blockFun]
        simp [hk]
    -- (2) the finite mass of each block and the identity for the total mass
    have hmassid : (∑' m : ℕ, blockMass j m γ)
        = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2 := by
      have h := hrearrR
        (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) h2
      rw [← h]
      refine tsum_congr fun m => ?_
      rw [blockMass]
      refine tsum_congr fun k => ?_
      by_cases hk : k ∈ annulus m
      · simp only [blockCoeff, blockFun]
        simp [hk]
      · simp only [blockCoeff, blockFun]
        simp [hk]
    have hWsumm : Summable fun m : ℕ => blockMass j m γ := hsummass γ h1 h2
    -- (3) Hölder in the block index
    have hHolder := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
      (p := 2) (q := 2) Real.HolderConjugate.two_two
      (fun m : ℕ => Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (-(m : ℝ) * η))
      (fun m : ℕ => Real.rpow_nonneg (blockMass_nonneg j m γ) (1 / 2 : ℝ))
      (hgeom.congr fun m => (hsq m).symm)
      (hWsumm.congr fun m => by
        rw [← Real.rpow_mul (blockMass_nonneg j m γ),
          show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one])
    -- (4) the block estimates and their summability
    have hblk : ∀ m : ℕ, rnorm (2 * p) (Work.Diff.STE.seriesFun (blockCoeff m γ))
        ≤ K * (2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ) :=
      fun m => hblock m γ h1 h2
    have hblksum : Summable fun m : ℕ =>
        rnorm (2 * p) (Work.Diff.STE.seriesFun (blockCoeff m γ)) := by
      refine Summable.of_nonneg_of_le (fun m => rnorm_nonneg _ _) (fun m => ?_)
        (hHolder.1.mul_left K)
      calc rnorm (2 * p) (Work.Diff.STE.seriesFun (blockCoeff m γ))
          ≤ K * (2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ) := hblk m
        _ = K * ((2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ)) := by ring
    -- (5) the blocks are `L^{2p}` functions
    have hmem : ∀ m : ℕ, MemLp (fun x : ι → ℝ =>
          Work.Diff.STE.seriesFun (blockCoeff m γ) x)
        (ENNReal.ofReal (2 * p)) (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
      intro m
      have hδ : Summable fun k : ι → ℤ => ‖blockCoeff m γ k‖ := by
        refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) h1
        by_cases hk : k ∈ annulus m
        · simp only [blockCoeff, blockFun]
          simp [hk]
        · simp only [blockCoeff, blockFun]
          simp [hk]
      have hnorm : ∀ (k : ι → ℤ) (x : ι → ℝ),
          ‖blockCoeff m γ k * Work.Diff.STE.fourierExp k x‖ = ‖blockCoeff m γ k‖ :=
        fun k x => by rw [norm_mul, Work.Diff.STE.BesselCont.norm_fourierExp_char, mul_one]
      have hsup : ∀ x : ι → ℝ,
          ‖Work.Diff.STE.seriesFun (blockCoeff m γ) x‖ ≤ ∑' k : ι → ℤ, ‖blockCoeff m γ k‖ := by
        intro x
        rw [Work.Diff.STE.seriesFun]
        calc ‖∑' k : ι → ℤ, blockCoeff m γ k * Work.Diff.STE.fourierExp k x‖
            ≤ ∑' k : ι → ℤ, ‖blockCoeff m γ k * Work.Diff.STE.fourierExp k x‖ :=
              norm_tsum_le_tsum_norm (hδ.congr fun k => (hnorm k x).symm)
          _ = ∑' k : ι → ℤ, ‖blockCoeff m γ k‖ := tsum_congr fun k => hnorm k x
      have hcont : Continuous (Work.Diff.STE.seriesFun (blockCoeff m γ)) :=
        continuous_seriesFun _ hδ
      haveI := Work.Diff.STE.BesselCont.isFiniteMeasure_restrict_unitCube (ι := ι)
      exact MemLp.of_bound hcont.aestronglyMeasurable _
        (Filter.Eventually.of_forall hsup)
    have hfmeas : AEMeasurable (Work.Diff.STE.seriesFun γ)
        (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
      (continuous_seriesFun γ h1).aemeasurable
    -- (6) Minkowski's inequality and the summation
    have hminkapp := hmink (2 * p) (by linarith) hmem hfmeas hdec hblksum
    have hsumg : (∑' m : ℕ, ((2 : ℝ) ^ (-(m : ℝ) * η)) ^ (2 : ℝ))
        = ∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m := tsum_congr hsq
    have hsumsq : (∑' m : ℕ, ((blockMass j m γ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ))
        = ∑' m : ℕ, blockMass j m γ := tsum_congr fun m => by
      rw [← Real.rpow_mul (blockMass_nonneg j m γ),
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
    have hgm : Summable fun m : ℕ =>
        K * ((2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ)) :=
      hHolder.1.mul_left K
    calc rnorm (2 * p) (Work.Diff.STE.seriesFun γ)
        ≤ ∑' m : ℕ, rnorm (2 * p) (Work.Diff.STE.seriesFun (blockCoeff m γ)) := hminkapp
      _ ≤ ∑' m : ℕ, K * ((2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ)) := by
          refine Summable.tsum_le_tsum (fun m => ?_) hblksum hgm
          calc rnorm (2 * p) (Work.Diff.STE.seriesFun (blockCoeff m γ))
              ≤ K * (2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ) := hblk m
            _ = K * ((2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ)) := by ring
      _ = K * ∑' m : ℕ, (2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ) := by
          rw [tsum_mul_left]
      _ ≤ K * ((∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m) ^ (1 / 2 : ℝ)
            * (∑' m : ℕ, blockMass j m γ) ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          calc (∑' m : ℕ, (2 : ℝ) ^ (-(m : ℝ) * η) * (blockMass j m γ) ^ (1 / 2 : ℝ))
              ≤ (∑' m : ℕ, ((2 : ℝ) ^ (-(m : ℝ) * η)) ^ 2) ^ (1 / 2 : ℝ)
                * (∑' m : ℕ, ((blockMass j m γ) ^ (1 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ) :=
                hHolder.2
            _ = (∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m) ^ (1 / 2 : ℝ)
                * (∑' m : ℕ, blockMass j m γ) ^ (1 / 2 : ℝ) := by
                rw [hsumg, hsumsq]
      _ = K * (∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m) ^ (1 / 2 : ℝ)
            * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := by
          rw [hmassid]
          ring
      _ ≤ max 1 (K * (∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m) ^ (1 / 2 : ℝ))
            * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ ?_
          · exact le_max_right _ _
          · exact Real.rpow_nonneg (tsum_nonneg fun k =>
              mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _)) _
  · -- the `ℓ¹`-failing case: the series is identically zero
    have hzero : Work.Diff.STE.seriesFun γ = 0 :=
      seriesFun_eq_zero_of_not_summable γ h1
    have hL : rnorm (2 * p) (Work.Diff.STE.seriesFun γ) = 0 := by
      rw [hzero, rnorm]
      have hz : ∀ x : ι → ℝ, ‖(0 : (ι → ℝ) → ℂ) x‖ ^ (2 * p) = 0 := fun x => by
        rw [Pi.zero_apply, norm_zero, Real.zero_rpow (by positivity)]
      simp only [hz, integral_zero]
      exact Real.zero_rpow (by positivity)
    rw [hL]
    exact mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      (Real.rpow_nonneg (tsum_nonneg fun k =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _)) _)

/-! ## The refutation of the requested statement -/

/-- The exponent `(1 / 2)` of the requested statement is *natural* number division: `(1 : ℕ)/2 = 0`,
so the requested right-hand side `C * (Σ_k (wt k)^j ‖γ k‖²) ^ (1 / 2)` is the constant `C`. -/
theorem nat_exp_default : ((1 : ℕ) / 2 : ℕ) = 0 := rfl

/-- **The requested statement is false.**  For every `C` there is a coefficient family `γ` whose
weighted mass `Σ_k (wt k)^j ‖γ k‖²` is summable (so that the hypothesis of the requested statement
holds) but whose Fourier series has `L^{2p}` norm larger than the requested right-hand side
`C * (Σ_k (wt k)^j ‖γ k‖²) ^ (1 / 2) = C`.

The example is `ι = Fin 1`, `p = 1`, `j = 1`, and `γ = n • δ₀` with `n = max C 0 + 1`: its Fourier
series is the constant function `n`, whose `L²` norm on the unit cube (of measure one) is `n > C`,
while the exponent `(1 : ℕ) / 2` makes the right-hand side `C`.  The parameters satisfy the
hypotheses of the requested statement: `1 ≤ 1` and `card ι * (1/2 - 1/(2·1)) = 0 < 1`. -/
theorem requested_statement_false :
    ∀ C : ℝ, ∃ γ : (Fin 1 → ℤ) → ℂ,
      Summable (fun k : Fin 1 → ℤ => (Work.Diff.STE.wt k) ^ (1 : ℝ) * ‖γ k‖ ^ 2) ∧
      C * (∑' k : Fin 1 → ℤ, (Work.Diff.STE.wt k) ^ (1 : ℝ) * ‖γ k‖ ^ 2) ^ (1 / 2)
        < (∫ x in Work.Diff.STE.unitCube (ι := Fin 1),
            ‖Work.Diff.STE.seriesFun γ x‖ ^ (2 * (1 : ℝ))) ^ (1 / (2 * (1 : ℝ))) := by
  intro C
  set n : ℝ := max C 0 + 1 with hn
  have hn0 : 0 ≤ n := by rw [hn]; positivity
  have hnC : C < n := by
    have h1 : C ≤ max C 0 := le_max_left _ _
    rw [hn]; linarith
  refine ⟨fun k : Fin 1 → ℤ => if k = 0 then ((n : ℝ) : ℂ) else 0, ?_, ?_⟩
  · have h : HasSum (fun k : Fin 1 → ℤ => (Work.Diff.STE.wt k) ^ (1 : ℝ)
        * ‖(if k = 0 then ((n : ℝ) : ℂ) else 0)‖ ^ 2)
        ((Work.Diff.STE.wt 0) ^ (1 : ℝ) * ‖((n : ℝ) : ℂ)‖ ^ 2) :=
      hasSum_single 0 fun b hb => by simp [hb]
    exact h.summable
  · have hS : ((∑' k : Fin 1 → ℤ, (Work.Diff.STE.wt k) ^ (1 : ℝ)
        * ‖(if k = 0 then ((n : ℝ) : ℂ) else 0)‖ ^ 2) : ℝ) ^ (1 / 2) = 1 := by
      rw [show (1 : ℕ) / 2 = 0 from rfl, pow_zero]
    rw [hS, mul_one]
    have hfun : Work.Diff.STE.seriesFun
        (fun k : Fin 1 → ℤ => if k = 0 then ((n : ℝ) : ℂ) else 0)
        = fun _ : Fin 1 → ℝ => ((n : ℝ) : ℂ) := by
      funext x
      rw [Work.Diff.STE.seriesFun,
        tsum_eq_single (L := SummationFilter.unconditional (Fin 1 → ℤ)) 0
          (fun b hb => by simp [hb])]
      rw [show Work.Diff.STE.fourierExp (0 : Fin 1 → ℤ) x = 1 by
        simp [Work.Diff.STE.fourierExp], mul_one, if_pos rfl]
    have hvol : (volume : Measure (Fin 1 → ℝ)) (Work.Diff.STE.unitCube (ι := Fin 1)) = 1 := by
      rw [Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
      simp
    have hInt : (∫ x in Work.Diff.STE.unitCube (ι := Fin 1),
        ‖Work.Diff.STE.seriesFun
          (fun k : Fin 1 → ℤ => if k = 0 then ((n : ℝ) : ℂ) else 0) x‖ ^ (2 * (1 : ℝ)))
        = n ^ (2 : ℝ) := by
      have hpt : ∀ x : Fin 1 → ℝ,
          ‖Work.Diff.STE.seriesFun
            (fun k : Fin 1 → ℤ => if k = 0 then ((n : ℝ) : ℂ) else 0) x‖ ^ (2 * (1 : ℝ))
            = n ^ (2 : ℝ) := by
        intro x
        rw [hfun, show (2 : ℝ) * 1 = 2 by norm_num]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn0]
      simp only [hpt]
      rw [MeasureTheory.setIntegral_const]
      rw [show (volume : Measure (Fin 1 → ℝ)).real (Work.Diff.STE.unitCube (ι := Fin 1)) = 1 by
        rw [MeasureTheory.Measure.real, hvol]; norm_num]
      simp
    rw [hInt, show (2 : ℝ) * 1 = 2 by norm_num, ← Real.rpow_mul hn0,
      show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    exact hnC

end Work.Diff.STE.flat
