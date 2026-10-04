import Mathlib
import Submission.Work.Diff.STE.flat.Sobolev
import Submission.Work.Diff.STE.flat.norm_seriesFun_rpow_le
import Submission.Work.Diff.STE.flat.Sobolev.block_rnorm_le_rpow
import Submission.Work.Diff.STE.flat.Sobolev.tsum_annulus
import Submission.Work.Diff.STE.flat.Sobolev.summable_blockMass
import Submission.Work.Diff.STE.flat.Sobolev.rnorm_tsum_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sharp `L^{2p}` Sobolev bound with a constant uniform in the exponent

`Work.Diff.STE.flat.Sobolev.rnorm_seriesFun_rpow_le` (and the assembly
`Work.Diff.STE.flat.exists_bound_of_pieces` in `flat/norm_seriesFun_rpow_le.lean`)
proves the sharp Sobolev embedding `H^j ⊆ L^{2p}` on the torus for each *fixed* pair `(p, j)`:
`‖seriesFun γ‖_{L^{2p}} ≤ C(p,j) · (Σ_k ⟨k⟩^{2j}‖γ k‖²)^{1/2}`.  The constant there is
existential, so it is not *a priori* bounded as `p` varies — but in the applications (the `L^p`
bounds for the derivatives of the inverse metric used in the Leibniz/Hölder step of the
Gårding estimate) one needs a single constant valid for all exponents `p ≥ 1` at once.

The present file exposes the constant of the dyadic assembly: the per-block estimate
`Sobolev.block_rnorm_le_rpow` has the *explicit* right-hand side
`6^{nθ} · 2^{-m(j-nθ)} · (blockMass j m γ)^{1/2}` with `θ = 1/2 - 1/(2p)`, and the assembly's
constant is `max 1 (K · (Σ_m (2^{-2η})^m)^{1/2})`.  Choosing the *uniform* inputs
`K := 6^{n/2}` and `η := 1/2` (legitimate as soon as `j ≥ nθ + 1/2`, i.e. `η = j - nθ ≥ 1/2`)
makes that constant independent of `p`, which yields

`rnorm_seriesFun_uniform`: `∃ C, ∀ p ≥ 1, ∀ j ≥ n(1/2 - 1/(2p)) + 1/2, ∀ γ`,
`‖seriesFun γ‖_{L^{2p}} ≤ C (Σ_k ⟨k⟩^{2j}‖γ k‖²)^{1/2}`,

with a constant depending only on the index type `ι` (not on `p`, `j` or `γ`).

`exists_bound_of_pieces_explicit` below is the assembly of `exists_bound_of_pieces` with the
constant exposed (the body is copied verbatim, only the `∃ C` introduction is removed).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_bound_of_pieces_explicit
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
    ∀ γ : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) →
      rnorm (2 * p) (Work.Diff.STE.seriesFun γ)
        ≤ max 1 (K * (∑' m : ℕ, ((2 : ℝ) ^ (-(2 * η))) ^ m) ^ (1 / 2 : ℝ))
          * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := by
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

/-! ## The uniform-in-`p` form of the sharp Sobolev bound -/

/-- **The sharp `L^{2p}` Sobolev bound with a constant uniform in the exponent `p`.**

There is a constant `C`, depending only on the index type `ι`, such that for every real `p ≥ 1`,
every real level `j ≥ card ι · (1/2 - 1/(2p)) + 1/2` and every coefficient family `γ` with
`Σ_k ⟨k⟩^{2j}‖γ k‖² < ∞` one has
`‖seriesFun γ‖_{L^{2p}} ≤ C · (Σ_k ⟨k⟩^{2j}‖γ k‖²)^{1/2}`.

The proof re-runs the dyadic assembly `exists_bound_of_pieces_explicit` with the *uniform* inputs
`K = 6^{card ι/2}` and `η = 1/2`: since the per-block estimate
`Sobolev.block_rnorm_le_rpow` gives `K = 6^{card ι·θ}` and `η = j - card ι·θ` with
`θ = 1/2 - 1/(2p) ≤ 1/2`, and `η ≥ 1/2` by hypothesis, the resulting constant
`max 1 (K · (Σ_m (2^{-2η})^m)^{1/2})` is bounded by the `p`-independent number
`max 1 (6^{card ι/2} · (Σ_m 2^{-m})^{1/2})`. -/
theorem rnorm_seriesFun_uniform {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ) (hp : 1 ≤ p) (j : ℝ),
      (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) + 1 / 2 ≤ j →
      ∀ γ : (ι → ℤ) → ℂ,
        Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) →
        rnorm (2 * p) (Work.Diff.STE.seriesFun γ)
          ≤ C * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := by
  classical
  refine ⟨max 1 ((6 : ℝ) ^ (((Fintype.card ι : ℕ) : ℝ) / 2)
      * (∑' m : ℕ, ((2 : ℝ) ^ (-(1 : ℝ))) ^ m) ^ (1 / 2 : ℝ)),
    le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro p hp j hj γ hγ
  have h2p : (2 : ℝ) ≤ 2 * p := by linarith
  have h2ppos : (0 : ℝ) < 2 * p := by linarith
  have hθnn : (0 : ℝ) ≤ 1 / (2 * p) := (one_div_pos.mpr h2ppos).le
  have hjgt : (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) < j := by linarith
  have hη : 0 < j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) := by linarith
  have hηge : 1 / 2 ≤ j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) := by linarith
  -- the per-block estimate with the uniform constants `K = 6^{card ι · θ}` and `η = j - card ι · θ`
  have hblock : ∀ (m : ℕ) (γ' : (ι → ℤ) → ℂ), Summable (fun k : ι → ℤ => ‖γ' k‖) →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ j * ‖γ' k‖ ^ 2) →
      rnorm (2 * p) (Work.Diff.STE.seriesFun (blockCoeff m γ'))
        ≤ (6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
          * (2 : ℝ) ^ (-(m : ℝ) * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))))
          * (blockMass j m γ') ^ (1 / 2 : ℝ) :=
    fun m γ' h1 h2 => Sobolev.block_rnorm_le_rpow p hp j (le_of_lt hjgt) m γ' h1 h2
  have hmain : rnorm (2 * p) (Work.Diff.STE.seriesFun γ)
      ≤ max 1 ((6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
          * (∑' m : ℕ,
              ((2 : ℝ) ^ (-(2 * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))))) ^ m)
            ^ (1 / 2 : ℝ))
        * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) :=
    exists_bound_of_pieces_explicit (ι := ι) p hp j hjgt
      ((6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))))
      (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
      (Real.rpow_nonneg (by norm_num) _) hη hblock
      (fun g hg => Sobolev.tsum_annulus (E := ℂ) g hg)
      (fun g hg => Sobolev.tsum_annulus (E := ℝ) g hg)
      (fun γ' h1 h2 => Sobolev.summable_blockMass j γ' h2)
      (fun q hq g f hm hf hfg hsum => Sobolev.rnorm_tsum_le q hq hm hf hfg hsum) γ hγ
  -- the two factors of the constant are bounded by the uniform ones
  have hKle : (6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
      ≤ (6 : ℝ) ^ (((Fintype.card ι : ℕ) : ℝ) / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hc : (0 : ℝ) ≤ (Fintype.card ι : ℕ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (show 1 / 2 - 1 / (2 * p) ≤ 1 / 2 by linarith) hc]
  have hAle : (∑' m : ℕ,
        ((2 : ℝ) ^ (-(2 * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))))) ^ m)
        ^ (1 / 2 : ℝ)
      ≤ (∑' m : ℕ, ((2 : ℝ) ^ (-(1 : ℝ))) ^ m) ^ (1 / 2 : ℝ) := by
    have hr0 : (0 : ℝ) ≤ (2 : ℝ) ^
        (-(2 * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))))) :=
      Real.rpow_nonneg (by norm_num) _
    have hr1 : (2 : ℝ) ^
        (-(2 * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p))))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hr0' : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    have hr1' : (2 : ℝ) ^ (-(1 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    have hrr : (2 : ℝ) ^ (-(2 * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))))
        ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    refine Real.rpow_le_rpow (tsum_nonneg fun m => pow_nonneg hr0 m) ?_ (by norm_num)
    exact Summable.tsum_le_tsum (fun m => pow_le_pow_left₀ hr0 hrr m)
      (summable_geometric_of_lt_one hr0 hr1) (summable_geometric_of_lt_one hr0' hr1')
  have hconst : max 1 ((6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
        * (∑' m : ℕ,
            ((2 : ℝ) ^ (-(2 * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))))) ^ m)
          ^ (1 / 2 : ℝ))
      ≤ max 1 ((6 : ℝ) ^ (((Fintype.card ι : ℕ) : ℝ) / 2)
          * (∑' m : ℕ, ((2 : ℝ) ^ (-(1 : ℝ))) ^ m) ^ (1 / 2 : ℝ)) :=
    max_le_max le_rfl
      (mul_le_mul hKle hAle
        (Real.rpow_nonneg (tsum_nonneg fun m => pow_nonneg (Real.rpow_nonneg (by norm_num) _) m) _)
        (Real.rpow_nonneg (by norm_num) _))
  have hmn : (0 : ℝ) ≤ (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) j) (sq_nonneg _)) _
  calc rnorm (2 * p) (Work.Diff.STE.seriesFun γ)
      ≤ max 1 ((6 : ℝ) ^ ((Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))
          * (∑' m : ℕ,
              ((2 : ℝ) ^ (-(2 * (j - (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)))))) ^ m)
            ^ (1 / 2 : ℝ))
        * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) := hmain
    _ ≤ max 1 ((6 : ℝ) ^ (((Fintype.card ι : ℕ) : ℝ) / 2)
          * (∑' m : ℕ, ((2 : ℝ) ^ (-(1 : ℝ))) ^ m) ^ (1 / 2 : ℝ))
        * (∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ j * ‖γ k‖ ^ 2) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hconst hmn

end Work.Diff.STE.flat
