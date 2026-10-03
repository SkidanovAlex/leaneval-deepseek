import Mathlib
import Submission.Work.KMTAreas.iw_family
import Submission.Work.KMTAreas.khintchine_lower_orthonormal_basis
import Submission.Work.KMTAreas.khintchine_upper_orthonormal_basis

/-!
# The scalar `ℓ^q` Ionescu–Wainger bound implies the vector-valued one

`Work.Analysis.IWMultiplier.IWLqBoundScalar A Φ q C` is the `ℓ^q(ℤ; ℂ)` bound for the
Ionescu–Wainger multiplier with symbol `iwSymbolSet A Φ`; `Work.Analysis.IWMultiplier.IWLqBound`
is the corresponding bound on `ℓ^q(ℤ; H)` for *every* finite dimensional Hilbert space `H`, with a
constant independent of `H`.  This file proves that the scalar bound implies the vector-valued one
(and hence the two formulations are equivalent): for every `q ∈ [1,∞)` there is a constant
`C' > 0` (depending only on `q` and on the scalar constant) with

`‖iwConv A Φ f‖_{ℓ^q(ℤ;H)} ≤ C' ‖f‖_{ℓ^q(ℤ;H)}`  for all finitely supported `f : ℤ → H`.

## The argument

Fix an orthonormal basis `b₁,…b_d` of `H` and let `v_ε = ∑ᵢ εᵢ bᵢ` be the `2^d` sign sums.
Khintchine's inequality for the coefficients `⟪bᵢ,x⟫` of a vector `x ∈ H` gives, pointwise in `n`,
the two bounds (`p = q.toReal`)

`‖x‖^p ≤ c^{-p} 2^{-d} ∑_ε ‖⟪v_ε,x⟫‖^p`,      `2^{-d} ∑_ε ‖⟪v_ε,x⟫‖^p ≤ (C_k p^{1/2})^p ‖x‖^p`,

which are `Work.KMTAreas.khintchine_lower_orthonormal_basis` and
`Work.KMTAreas.khintchine_upper_orthonormal_basis` (both deduced from the workspace's
`Commons.Analysis.Walsh.exists_khintchine_hilbert`).  Applying the lower bound at `x = iwConv f n`
and using that the IW multiplier acts coordinatewise (`inner_iwConv`), the scalar sequences
`g_ε = ⟪v_ε, f⟫` satisfy

`∑_n ‖iwConv f n‖^p ≤ c^{-p} 2^{-d} ∑_ε ∑_n ‖iwConv g_ε n‖^p`
`        ≤ c^{-p} 2^{-d} C^p ∑_ε ∑_n ‖g_ε n‖^p`      (scalar hypothesis, one `ε` at a time)
`        ≤ C^p C_k^p p^{p/2} c^{-p} ∑_n ‖f n‖^p`      (upper Khintchine).

Raising to the power `1/p` gives the `ℓ^q(ℤ;H)` bound with `C' = C C_k √p / c`, which is
independent of `H`.  Taking the `p`-th powers of the `eLpNorm`s turns all the series above into
`∑'` over `ℤ` in `ℝ≥0∞`, so no summability or measurability hypotheses are ever needed.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators ENNReal NNReal InnerProductSpace
open MeasureTheory

namespace Work.KMTAreas

open Work.Analysis.IWMultiplier
open Work.Analysis.IonescuWainger

/-- `eLpNorm · (ofReal p)` over the counting measure on `ℤ`, raised to the `p`-th power, is the
sum of the `p`-th powers of the `enorm`s: `(eLpNorm u (ofReal p))^p = ∑' n, ‖u n‖ₑ^p`. -/
theorem eLpNorm_count_eq_tsum_rpow {E : Type*} [NormedAddCommGroup E] {p : ℝ} (hp0 : 0 < p)
    (u : ℤ → E) :
    (eLpNorm u (ENNReal.ofReal p) Measure.count) ^ p = ∑' n : ℤ, enorm (u n) ^ p := by
  rw [Commons.Analysis.DiscreteCZ.eLpNorm_count_eq_tsum hp0 u, ← ENNReal.rpow_mul,
    show (1/p) * p = 1 by field_simp, ENNReal.rpow_one]

theorem IWLqBound_of_scalar {A : Finset Work.Analysis.IonescuWainger.Circle}
    {Φ : Work.Analysis.IonescuWainger.Circle → ℂ} {q : ENNReal} (hq1 : 1 ≤ q) (hq2 : q < ⊤)
    {C : NNReal} (h : Work.Analysis.IWMultiplier.IWLqBoundScalar A Φ q C) :
    ∃ C' : NNReal, 0 < C' ∧ Work.Analysis.IWMultiplier.IWLqBound A Φ q C' := by
  classical
  obtain ⟨p, hp1, hqeq⟩ : ∃ p : ℝ, 1 ≤ p ∧ q = ENNReal.ofReal p :=
    ⟨q.toReal,
      by rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (lt_top_iff_ne_top.mp hq2) hq1,
      (ENNReal.ofReal_toReal (lt_top_iff_ne_top.mp hq2)).symm⟩
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  obtain ⟨C₀, hC₀le, hC₀pos, h'⟩ : ∃ C₀ : NNReal, C ≤ C₀ ∧ 0 < C₀ ∧ IWLqBoundScalar A Φ q C₀ :=
    ⟨max C 1, le_max_left _ _, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun f hf => le_trans (h f hf) (mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (by exact_mod_cast le_max_left C 1)) bot_le)⟩
  have h'' : IWLqBoundScalar A Φ (ENNReal.ofReal p) C₀ := by rw [← hqeq]; exact h'
  obtain ⟨c, hc, hlow⟩ := khintchine_lower_orthonormal_basis p hp1
  obtain ⟨Ck, hCk, hup⟩ := khintchine_upper_orthonormal_basis p hp1
  have hCpos : (0:ℝ) < (C₀ : ℝ) := by exact_mod_cast hC₀pos
  have hKp : 0 < p ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hp0 _
  set X : ℝ := ((c ^ p)⁻¹ * (C₀ : ℝ) ^ p) * (Ck * p ^ ((1:ℝ)/2)) ^ p with hXdef
  have hXpos : 0 < X := by
    rw [hXdef]
    have h1 : 0 < (c ^ p)⁻¹ * (C₀ : ℝ) ^ p :=
      mul_pos (inv_pos.mpr (Real.rpow_pos_of_pos hc p)) (Real.rpow_pos_of_pos hCpos p)
    have h2 : 0 < (Ck * p ^ ((1:ℝ)/2)) ^ p := Real.rpow_pos_of_pos (mul_pos hCk hKp) p
    exact mul_pos h1 h2
  refine ⟨⟨X ^ (1/p), le_of_lt (Real.rpow_pos_of_pos hXpos _)⟩,
    Real.rpow_pos_of_pos hXpos _, ?_⟩
  intro H _ _ _ f hf
  rw [hqeq]
  set d : ℕ := Module.finrank ℂ H with hd
  set bb : OrthonormalBasis (Fin d) ℂ H := stdOrthonormalBasis ℂ H with hbb
  set v : (Fin d → Bool) → H :=
    fun ε => ∑ i, (if ε i then (1 : ℂ) else -1) • bb i with hv
  set g : (Fin d → Bool) → ℤ → ℂ := fun ε n => inner ℂ (v ε) (f n) with hgd
  have hgfin : ∀ ε, (Function.support (g ε)).Finite := by
    intro ε
    refine hf.subset ?_
    intro n hn
    rw [Function.mem_support] at hn ⊢
    intro hfn
    exact hn (by simp [hgd, hv, hfn])
  have hkey : ∀ (ε : Fin d → Bool) (n : ℤ),
      inner ℂ (v ε) (iwConv A Φ f n) = iwConv A Φ (g ε) n := by
    intro ε n
    have h1 := inner_iwConv A Φ f hf (v ε) n
    rwa [show (fun m => inner ℂ (v ε) (f m)) = g ε from funext fun m => rfl] at h1
  have hlow' : ∀ x : H, enorm x ^ p ≤ (ENNReal.ofReal (c ^ p))⁻¹ *
      (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ * ∑ ε : Fin d → Bool, enorm (inner ℂ (v ε) x) ^ p := by
    intro x
    exact hlow (x := x)
  have hup' : ∀ x : H, (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
      ∑ ε : Fin d → Bool, enorm (inner ℂ (v ε) x) ^ p
      ≤ ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm x ^ p := by
    intro x
    exact hup (x := x)
  -- pointwise lower bound
  have hpt : ∀ n : ℤ, enorm (iwConv A Φ f n) ^ p ≤
      ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
        ∑ ε, enorm (iwConv A Φ (g ε) n) ^ p := by
    intro n
    refine (hlow' (iwConv A Φ f n)).trans_eq ?_
    refine congrArg _ ?_
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [hkey ε n]
  -- pointwise upper bound
  have hpu : ∀ n : ℤ, ∑ ε, enorm (g ε n) ^ p ≤
      ENNReal.ofReal ((2:ℝ) ^ d) *
        (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm (f n) ^ p) := by
    intro n
    have hD0 : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (by norm_num) d)
    have hDtop : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ ⊤ := ENNReal.ofReal_ne_top
    have h1 := hup' (f n)
    calc ∑ ε, enorm (g ε n) ^ p
        = ENNReal.ofReal ((2:ℝ) ^ d) *
            ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ * ∑ ε, enorm (g ε n) ^ p) := by
          rw [ENNReal.mul_inv_cancel_left hD0 hDtop]
      _ ≤ ENNReal.ofReal ((2:ℝ) ^ d) *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm (f n) ^ p) :=
          mul_le_mul_of_nonneg_left h1 bot_le
  have hA : (∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ (ENNReal.ofReal (C₀ : ℝ)) ^ p *
        ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p := by
    calc ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p
        ≤ ∑ ε, (ENNReal.ofReal (C₀ : ℝ) *
            eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p := by
          refine Finset.sum_le_sum fun ε _ => ?_
          exact ENNReal.rpow_le_rpow (h'' (g ε) (hgfin ε)) hp0.le
      _ = (ENNReal.ofReal (C₀ : ℝ)) ^ p *
            ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ε _ => ?_
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
  have hB : (∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ ENNReal.ofReal ((2:ℝ) ^ d) *
        (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) := by
    calc ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p
        = ∑ ε, ∑' n : ℤ, enorm (g ε n) ^ p := by
          refine Finset.sum_congr rfl fun ε _ => ?_
          exact eLpNorm_count_eq_tsum_rpow hp0 (g ε)
      _ = ∑' n : ℤ, ∑ ε, enorm (g ε n) ^ p := by
          rw [show (∑ ε : Fin d → Bool, ∑' n : ℤ, enorm (g ε n) ^ p)
              = ∑' ε : Fin d → Bool, ∑' n : ℤ, enorm (g ε n) ^ p from (tsum_fintype _).symm,
            ENNReal.tsum_comm]
          simp only [tsum_fintype]
      _ ≤ ∑' n : ℤ, ENNReal.ofReal ((2:ℝ) ^ d) *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * enorm (f n) ^ p) :=
          ENNReal.tsum_le_tsum hpu
      _ = ENNReal.ofReal ((2:ℝ) ^ d) *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have hB' : (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
        (∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by
    have hD0 : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (pow_pos (by norm_num) d)
    have hDtop : (ENNReal.ofReal ((2:ℝ) ^ d)) ≠ ⊤ := ENNReal.ofReal_ne_top
    calc (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
          (∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p)
        ≤ (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            (ENNReal.ofReal ((2:ℝ) ^ d) *
              (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p)) :=
          mul_le_mul_of_nonneg_left hB bot_le
      _ = ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDtop, one_mul]
  have hAB : (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
        (∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p)
      ≤ (ENNReal.ofReal (C₀ : ℝ)) ^ p *
        (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) := by
    calc (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
          (∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p)
        ≤ (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            ((ENNReal.ofReal (C₀ : ℝ)) ^ p *
              ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p) :=
          mul_le_mul_of_nonneg_left hA bot_le
      _ = (ENNReal.ofReal (C₀ : ℝ)) ^ p *
            ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
              ∑ ε, (eLpNorm (g ε) (ENNReal.ofReal p) Measure.count) ^ p) := by
          rw [← mul_assoc,
            mul_comm ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) ((ENNReal.ofReal (C₀ : ℝ)) ^ p),
            mul_assoc]
      _ ≤ (ENNReal.ofReal (C₀ : ℝ)) ^ p *
            (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p) :=
          mul_le_mul_of_nonneg_left hB' bot_le
  have hstep1 : ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p ≤
      (ENNReal.ofReal (c ^ p))⁻¹ * ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
        ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p) := by
    calc ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p
        ≤ ∑' n : ℤ, ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑ ε, enorm (iwConv A Φ (g ε) n) ^ p := ENNReal.tsum_le_tsum hpt
      _ = ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑' n : ℤ, ∑ ε, enorm (iwConv A Φ (g ε) n) ^ p := ENNReal.tsum_mul_left
      _ = ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑ ε, ∑' n : ℤ, enorm (iwConv A Φ (g ε) n) ^ p := by
          congr 1
          rw [show (∑ ε : Fin d → Bool, ∑' n : ℤ, enorm (iwConv A Φ (g ε) n) ^ p)
              = ∑' ε : Fin d → Bool, ∑' n : ℤ, enorm (iwConv A Φ (g ε) n) ^ p
              from (tsum_fintype _).symm, ENNReal.tsum_comm]
          simp only [tsum_fintype]
      _ = ((ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal ((2:ℝ) ^ d))⁻¹) *
            ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p := by
          congr 1
          refine Finset.sum_congr rfl fun ε _ => ?_
          exact (eLpNorm_count_eq_tsum_rpow hp0 (iwConv A Φ (g ε))).symm
      _ = (ENNReal.ofReal (c ^ p))⁻¹ * ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p) := by
          rw [mul_assoc]
  have harith : (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal (C₀ : ℝ)) ^ p *
      ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) = ENNReal.ofReal ((X ^ (1/p)) ^ p) := by
    rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hc p),
      ENNReal.ofReal_rpow_of_nonneg (le_of_lt hCpos) hp0.le,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos hc p))),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hXdef, ← Real.rpow_mul hXpos.le, show (1/p) * p = 1 by field_simp, Real.rpow_one]
  have hmain : ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p ≤
      ENNReal.ofReal ((X ^ (1/p)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by
    calc ∑' n : ℤ, enorm (iwConv A Φ f n) ^ p
        ≤ (ENNReal.ofReal (c ^ p))⁻¹ * ((ENNReal.ofReal ((2:ℝ) ^ d))⁻¹ *
            ∑ ε, (eLpNorm (iwConv A Φ (g ε)) (ENNReal.ofReal p) Measure.count) ^ p) :=
          hstep1
      _ ≤ (ENNReal.ofReal (c ^ p))⁻¹ *
            ((ENNReal.ofReal (C₀ : ℝ)) ^ p *
              (ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p)) :=
          mul_le_mul_of_nonneg_left hAB bot_le
      _ = (ENNReal.ofReal (c ^ p))⁻¹ * (ENNReal.ofReal (C₀ : ℝ)) ^ p *
            ENNReal.ofReal ((Ck * p ^ ((1:ℝ)/2)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by
          rw [mul_assoc, mul_assoc]
      _ = ENNReal.ofReal ((X ^ (1/p)) ^ p) * ∑' n : ℤ, enorm (f n) ^ p := by rw [harith]
  have hfin : (eLpNorm (iwConv A Φ f) (ENNReal.ofReal p) Measure.count) ^ p ≤
      (ENNReal.ofReal (X ^ (1/p)) * eLpNorm f (ENNReal.ofReal p) Measure.count) ^ p := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      eLpNorm_count_eq_tsum_rpow hp0 (iwConv A Φ f), eLpNorm_count_eq_tsum_rpow hp0 f,
      ENNReal.ofReal_rpow_of_nonneg (le_of_lt (Real.rpow_pos_of_pos hXpos (1/p))) hp0.le]
    exact hmain
  exact (ENNReal.rpow_le_rpow_iff hp0).mp hfin

end Work.KMTAreas
