import Mathlib
import Submission.Work.KMTPlan.A6.BallBoundDefs
import Submission.Work.KMTPlan.A6.ballDevBound
import Submission.Work.KMTPlan.A6.periodizeBallDev
import Submission.Work.KMTPlan.A6.ballDevSqSum
import Submission.Work.KMTAreas.A7.varShiftDiffPrep
import Submission.Work.KMTAreas.A7LoLin.kernel0
import Submission.Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top
import Submission.Work.KMTAreas.A7G.plainBumpVarG
import Submission.Work.KMTPlan.A6.eLpNorm_varNorm_two_le_sqSum
import Submission.Work.KMTPlan.A6.tsum_eLpNorm_sq_iwConv_le
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

/-
# The modulated height-`0` "ball" family is `R`-variationally bounded on `ℓ²`

Target: `Work.KMTPlan.A6.ballVarBound` (with `BallZeroBound` from
`Submission.Work.KMTPlan.A6.BallBoundDefs`): for `1 < Λ`, `2 < R`, every `ρ ∈ (0,1]` there is
`C > 0` with, for every `Λ`-lacunary family `a` with `a n ≥ 1`, every `t ∈ [1/2,1]` and every
`h : ℤ → ℂ`,

  `‖ V^R_n ( Tle ρ 0 (φ̃_{N_n,t}) h ) ‖_{ℓ²(ℤ)} ≤ C ‖h‖₂`,  `N_n = ⌊a n⌋`,  `φ̃_{N,t} = varphitildeNtj P N 0 0 t`.

This is the `(k₂,j₂) = (0,0)` ("ball") case of the `g`-side low-pass arithmetic-free estimate; it is
the only piece of `Work.KMTPlan.A6.MdlSliceLowpassG` below the two `A7Hi2` sockets (`SupPiece`,
`ChainPiece`) that is *not* covered by the exact-height (`Gcl`) assembly: at height `0` the
`Gcl`-carrier vanishes (`Tex_zero_level`), while the height-`0` carrier of the modulated bump is
non-zero.

## Route (verified against the tree)

`Tle ρ 0 ψ` is `iwConv {0} (periodize ψ)`, i.e. the Fourier multiplier with symbol
`periodize ψ` (`iwArithFreqs ρ 0 = {0}`, since `iwP ρ 0 = {1}`).  Split the bump:

  `φ̃_{N,t} = φ̃_N + (φ̃_{N,t} − φ̃_N)`,   `φ̃_N = varphitildeN P.natDegree N 0`,
  `φ̃_{N,t}(ξ) = φ̃_N(ξ) · e(P(N t) ξ)`  (`varphitildeNt`, `Large/Defs.lean`),

and use `Tle ρ 0 (u+v) = Tle ρ 0 u + Tle ρ 0 v` (linearity of `periodize`/`iwConv`) together with
the pointwise subadditivity of the variational norm (`PointwiseErgodicTheorems.variationalNorm_add_le`,
`Submission/VarNorm.lean`).

* **unmodulated part**: `n ↦ Tle ρ 0 (varphitildeN d ⌊a n⌋ 0) h` is bounded by
  `Work.KMTAreas.A7G.plainBumpVarG` (PROVED, sorry-free) at `p = 2` — this is the
  Jones–Seeger–Wright/Lépingle lacunary dilation estimate, so nothing has to be redone here.
* **deviation part**: `dev_n = φ̃_{N_n,t} − φ̃_{N_n} = φ̃_{N_n}·(e(P(N_n t)·) − 1)`.  Its symbol
  vanishes at the origin, so the *square-function* route works:
  `Work.KMTPlan.A6.eLpNorm_varNorm_two_le_sqSum` (PROVED) and
  `Work.KMTPlan.A6.tsum_eLpNorm_sq_iwConv_le` (PROVED) reduce the `R`-variation of the deviation
  family to the **pointwise symbol square-sum bound**

    `∃ W, ∀ θ, Σ'_n ‖periodize (dev_n) θ‖² ≤ W²`,

  which is elementary: `periodize (dev_n)(θ) = Σ_{k∈ℤ} φ̃_{N_n}(θ+k)(e(P(N_n t)(θ+k)) − 1)`, and only
  the (at most two) integers `k` with `|θ + k| ≲ 1/σ_n` contribute, where `σ_n = 2^{d·Log N_n}` is
  the reciprocal width of the bump.  Because the polynomial value is *comparable to the scale*,
  `|P(N_n t)| ≲ σ_n` (t ∈ [1/2,1], `P ≠ 0`, `d = P.natDegree`), the factor `|e(P(N_n t) ξ) − 1|` is
  `≲ σ_n |ξ| ≲ 1` on the support `|ξ| ≲ 1/σ_n`, and the `n`-sum is controlled by the geometric
  growth of the scales `σ_n` (`lacunaryFloorGap`, `lacunaryFloorCount` in
  `Submission/Work/KMTPlan/A6/`, which handle the repetitions of `⌊log₂ ⌊a n⌋⌋`):
  `Σ_n |φ̃(σ_n ξ)|² min(1, C σ_n|ξ|)² ≲ 1 + Σ_{k≥0} Λ^{-2dk}`.

  Useful existing material: `Work.KMTPlan.A6.varphitildeNtj_support` (reverse support
  `2^{d(logN N − k₂)}|z| ≤ 1` on the support), `Work.KMTPlan.A6.varphitildeNtj_bounds` /
  `varphitildeNtjPointwise` (sup-norm and profile bounds), `Work.KMTPlan.A6.varphitildeNtj_zero`
  (`φ̃_{N,0,0} = φ̃_{N,0}`), `Work.KMTAreas.A7.varphitildeN_support_all`, and
  `Work.KMTPlan.A6.periodizeVarphitildeNtjBall` (support transfer to the periodisation).

  (`‖e^{2πi y} − 1‖ ≤ min 2 (2π|y|)` and the polynomial bound `|P(N t)| ≤ (Σ|c|)(1+N)^d` are the
  only analytic inputs; `P.natDegree = d ≥ 2`.)
-/
open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **Additivity of `Tle` in the symbol for the modulated `g`-bump**, for bounded input: splitting
`φ̃_{N,t} = φ̃_N + ballDev P N t` (an *exact* pointwise identity) at the level of the operator. -/
theorem Tle_varphitildeNtj_split (P : Polynomial ℤ) (ρ : ℝ) (l N : ℕ) (t : ℝ)
    {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Work.KMTAreas.A7.Tle ρ l (varphitildeNtj P N 0 0 t) f
      = Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphitildeN P.natDegree N 0) f
        + Work.KMTAreas.A7.Tle ρ l (ballDev P N t) f := by
  have hsum : varphitildeNtj P N 0 0 t
      = (fun ξ : ℝ => Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ) + ballDev P N t := by
    funext ξ
    simp only [Pi.add_apply, ballDev]
    ring
  rw [hsum]
  refine Work.KMTAreas.A7LoLin.Tle_add_of_bounded ?_ ?_ hf
  · exact Work.KMTAreas.A7.adm_of_bump (Work.KMTAreas.A7.contDiff_varphitildeN _ _ _)
      (Work.KMTAreas.A7.hasCompactSupport_varphitildeN _ _ _)
  · rw [ballDev_eq]
    exact Work.KMTAreas.A7.adm_of_bump
      ((Work.KMTAreas.A7.contDiff_varphitildeN _ _ _).mul
        ((Work.KMTAreas.A7.contDiff_ee_const_mul 2 _).sub contDiff_const))
      ((Work.KMTAreas.A7.hasCompactSupport_varphitildeN _ _ _).mul_right)


theorem ballVarBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (R : NNReal) (hR : 2 < R) :
    ∀ (Λ : NNReal), 1 < Λ → BallZeroBound P R Λ := by
  intro Λ hΛ ρ hρ hρ1
  have hR1 : (1 : NNReal) ≤ R := le_trans (by norm_num) (le_of_lt hR)
  obtain ⟨Cp, hCppos, hp⟩ :=
    Work.KMTAreas.A7G.plainBumpVarG P.natDegree (by omega) ρ Λ hΛ R hR 2 (by norm_num) (by norm_num)
  obtain ⟨Cv, hCvpos, hCv⟩ := eLpNorm_varNorm_two_le_sqSum R hR
  obtain ⟨Cb, hCbpos, hCb⟩ := ballDevBound P
  obtain ⟨W, hW⟩ := ballDevSqSum P hd Λ hΛ Cb hCbpos hCb
    (fun N t ξ h => ballDev_vanish P N t h) (fun N t θ => periodizeBallDev P N t θ)
  refine ⟨Cp + Cv * (W : ℝ), by positivity, ?_⟩
  intro a ha ha1 t ht h
  by_cases htop : MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr
      (by positivity : (0 : ℝ) < Cp + Cv * (W : ℝ)))]
    exact le_top
  · have hmem : MeasureTheory.MemLp h 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr htop)
    obtain ⟨B, hB⟩ := Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top (p := 2)
      (by norm_num) (lt_top_iff_ne_top.mpr htop)
    have hsplit : ∀ n : ℕ, Work.KMTAreas.A7.Tle ρ 0
          (varphitildeNtj P (Nat.floor (a n)) 0 0 t) h
        = Work.KMTAreas.A7.Tle ρ 0
            (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) h
          + Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h :=
      fun n => Tle_varphitildeNtj_split P ρ 0 (Nat.floor (a n)) t hB
    -- the deviation part, by the pointwise symbol square-sum bound
    have hdev : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h x))
          2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Cv * (W : ℝ)) * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
      have hW' : ∀ θ : Work.Analysis.IonescuWainger.Circle,
          (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0)
              (Work.Analysis.IonescuWainger.periodize (ballDev P (Nat.floor (a n)) t)) θ‖ₑ
                ^ (2 : ℝ)) ≤ (W : ENNReal) ^ 2 := by
        intro θ
        simp only [Work.KMTAreas.A7.iwArithFreqs_zero, iwSymbolSet_singleton_zero]
        exact hW a ha ha1 t ht θ
      have hconv := tsum_eLpNorm_sq_iwConv_le (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0)
        (fun n : ℕ => ballDev P (Nat.floor (a n)) t) h hmem W hW'
      have hsq := hCv (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h)
      calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h x))
            2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal Cv * (∑' n : ℕ, (MeasureTheory.eLpNorm
                (Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h) 2
                  MeasureTheory.Measure.count) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hsq
        _ ≤ ENNReal.ofReal Cv * ((W : ENNReal)
              * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count) :=
            mul_le_mul_of_nonneg_left hconv (by simp)
        _ = ENNReal.ofReal (Cv * (W : ℝ))
              * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
            rw [← mul_assoc, ENNReal.coe_nnreal_eq W, ← ENNReal.ofReal_mul hCvpos.le]
    have hplain := hp a ha ha1 h
    have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
          Work.KMTAreas.A7.Tle ρ 0 (varphitildeNtj P (Nat.floor (a n)) 0 0 t) h x)
        ≤ PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
              Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) h x)
          + PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
              Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h x) := by
      intro x
      have hfun : (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
            (varphitildeNtj P (Nat.floor (a n)) 0 0 t) h x)
          = (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) h x)
            + (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h x) := by
        funext n
        simp only [Pi.add_apply, hsplit n]
      rw [hfun]
      exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le hR1 _ _
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (varphitildeNtj P (Nat.floor (a n)) 0 0 t) h x))
          2 MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) h x)
            + PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
                Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h x))
            2 MeasureTheory.Measure.count := by
          refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
          rw [enorm_eq_self, enorm_eq_self]
          exact hpt x
        _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) h x))
              2 MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ballDev P (Nat.floor (a n)) t) h x))
              2 MeasureTheory.Measure.count :=
            MeasureTheory.eLpNorm_add_le (by norm_num)
        _ ≤ ENNReal.ofReal Cp * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count
            + ENNReal.ofReal (Cv * (W : ℝ))
              * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count :=
            add_le_add hplain hdev
        _ = ENNReal.ofReal (Cp + Cv * (W : ℝ))
              * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
            rw [← add_mul, ← ENNReal.ofReal_add hCppos.le (by positivity)]

end

end Work.KMTPlan.A6
