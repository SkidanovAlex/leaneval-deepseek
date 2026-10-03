import Mathlib
import Submission.Work.KMTAreas.A7Hi.sublatticeReproL2Quarter
import Submission.Work.KMTAreas.A7Hi.winRotResidueBoundDec
import Submission.Port.Aesm

/-!
# The packet rotation residue bound at the quarter threshold `δ q ≤ 1/4`

This file proves `Work.KMTAreas.A7Hi.PacketRotationResidueBoundQuarter`: the `ℓᵖ(ℤ)`-norm of the
**residue average** over `n₀ < q` of the variational norms of the rotated window synthesis
`winRot A (f n) n₀` is bounded by the `ℓᵖ(ℤ)`-norm of the variational norm of the unrotated
synthesis `winSynth A (f n)`, uniformly in the family, with a constant depending only on `p` and
`r`, under the *quarter* decimation hypothesis `δ * q ≤ 1/4` — the same statement as the already
proved sibling `Work.KMTAreas.A7Hi.PacketRotationResidueBoundLpGeTwo`, whose hypothesis is the
*stronger* `δ * q ≤ 1/8`.

## The argument

The proof is the proof of the sibling, verbatim, with the decimation kernel replaced: the `1/8`
statement is fed by the `ℓ²`-band sublattice Shannon reproduction `reproL2BandAux` (band `1/8`),
whereas the quarter threshold `1/4` is exactly the range of validity of the kernel
`Work.KMTAreas.A7Hi.sublatticeReproL2Quarter` (proved, axiom-clean, in
`Submission/Work/KMTAreas/A7Hi/sublatticeReproL2Quarter.lean`).  Indeed its multiplier
`χ_q(ξ) = q · ψ(2qξ)` (with `ψ ≡ 1` on `[-1/2,1/2]`, `ψ ≡ 0` off `(-1,1)`) already vanishes at the
aliases `η - j/q`, `j ≠ 0`, of the band `|η| ≤ β` precisely when `β q ≤ 1/4`.

The residue average is unrolled into the `q`-power sum
`Σ_x (residueLp p q W x)^p = q⁻¹ Σ_{n₀<q} Σ_x (W x n₀)^p`, and the `x`-sum is decimated into the
residues `ρ < q` of `x = q z + ρ` (`periodDecompLocal`).  At a decimated point the `q`-torsion
characters `α ∈ A` (`q • α = 0`) are constant on the residue class, so (`winRot_decim`,
`winSynth_decim`)

  `W (q z + ρ) n₀ = Vʳ_n (G^{(ρ+n₀) mod q}_n (q z + ρ))`,   `S (q z + ρ) = Vʳ_n (G^{(ρ)}_n (q z + ρ))`

where `G^{(s)}_n x = Σ_{α∈A} fourier (-s) α · f n α x` is the rephased synthesis — again a band-`δ`
`ℓ²` family (`rephrase_memℓp_support`).  The two residual cosets `qℤ + ρ` and `qℤ + s` of the *same*
family `G^{(s)}` are compared by the sampled sublattice reproduction
(`decimLatticeCompareLocal`, fed by the quarter-threshold kernel `sublatticeReproL2Quarter`) and the
weighted Schur/Hölder step `weightedHolderTsum`.  The remaining bookkeeping is the bijection
`ρ ↦ (ρ + n₀) mod q` of the residue classes (`sum_range_add_mod`) and the cancellation of `q⁻¹ · q`.
-/

namespace Work.KMTAreas.A7Hi

set_option maxHeartbeats 4000000

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

theorem PacketRotationResidueBoundQuarter (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) (hq : 0 < q) (δ : ℝ) (hδ : 0 < δ) (hdec : δ * (q : ℝ) ≤ 1 / 4)
        (A : Finset Work.Analysis.IonescuWainger.Circle)
        (hA : ∀ α ∈ A, q • α = 0)
        (f : ℕ → Work.Analysis.IonescuWainger.Circle → ℤ → ℂ)
        (hbd : ∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle), α ∈ A →
          ∃ hh : Memℓp (f n α) 2,
            Work.BourgainPlan.IonescuWainger.HasFreqSupport (f n α) hh
              (Work.BourgainPlan.IonescuWainger.arcSet 0 δ)),
        MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7.residueLp p q (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7Hi.winRot A (f n) (n₀ : ℤ) y)) x)
            (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7Hi.winSynth A (f n) x)) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨Ck, hCkpos, hCk⟩ := sublatticeReproL2Quarter
  have hC₀pos : 0 < max Ck 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC₀1 : 1 ≤ max Ck 1 := le_max_right _ _
  refine ⟨max Ck 1, hC₀pos, ?_⟩
  intro q hq δ hδ hdec A hA f hbd
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num : (1 : NNReal) < 2) hr)
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have h1p : (0 : ℝ) ≤ 1 / p := by positivity
  set W : ℤ → ℕ → ENNReal := fun x n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => winRot A (f n) (n₀ : ℤ) x) with hW
  set S : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => winSynth A (f n) x) with hS
  set G : ℕ → ℕ → ℤ → ℂ := fun s n x => ∑ α ∈ A, fourier (T := 1) (-(s : ℤ)) α * f n α x with hG
  set Psum : ENNReal := ∑' x : ℤ, (Work.KMTAreas.A7.residueLp p q W x) ^ p with hPsum
  set Qsum : ENNReal := ∑' x : ℤ, (S x) ^ p with hQsum
  change MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q W x)
      (ENNReal.ofReal p) MeasureTheory.Measure.count
    ≤ ENNReal.ofReal (max Ck 1) * MeasureTheory.eLpNorm S
      (ENNReal.ofReal p) MeasureTheory.Measure.count
  -- (1) the residue `ℓ^p` norm is a power
  have hres : ∀ x : ℤ, (Work.KMTAreas.A7.residueLp p q W x) ^ p
      = ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q, (W x n₀) ^ p := by
    intro x
    rw [show Work.KMTAreas.A7.residueLp p q W x
        = (ENNReal.rpow (q : ENNReal) (-1) *
            ∑ n₀ ∈ Finset.range q, (W x n₀) ^ p) ^ (1 / p) from rfl, ← ENNReal.rpow_mul,
      show (1 / p) * p = 1 by field_simp, ENNReal.rpow_one]
  have hP1 : Psum = ENNReal.rpow (q : ENNReal) (-1) *
      ∑ n₀ ∈ Finset.range q, ∑' x : ℤ, (W x n₀) ^ p := by
    rw [hPsum, tsum_congr hres, ENNReal.tsum_mul_left, tsum_finset_sum_ennreal]
  have hper : ∀ n₀ : ℕ, (∑' x : ℤ, (W x n₀) ^ p)
      = ∑ ρ ∈ Finset.range q, ∑' z : ℤ, (W ((q : ℤ) * z + (ρ : ℤ)) n₀) ^ p :=
    fun n₀ => periodDecompLocal q hq (fun x : ℤ => (W x n₀) ^ p)
  -- (2) the character collapse
  have hWdec : ∀ (n₀ ρ : ℕ) (z : ℤ), W ((q : ℤ) * z + (ρ : ℤ)) n₀
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => G ((ρ + n₀) % q) n ((q : ℤ) * z + (ρ : ℤ))) := by
    intro n₀ ρ z
    simp only [hW, hG]
    exact congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v)
      (funext fun n => winRot_decim A f hA n₀ ρ n z)
  have hSdec : ∀ (ρ : ℕ) (z : ℤ), S ((q : ℤ) * z + (ρ : ℤ))
      = PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => G ρ n ((q : ℤ) * z + (ρ : ℤ))) := by
    intro ρ z
    simp only [hS, hG]
    exact congrArg (fun v => PointwiseErgodicTheorems.variationalNorm r v)
      (funext fun n => winSynth_decim A f hA ρ n z)
  have hP2 : Psum = ENNReal.rpow (q : ENNReal) (-1) *
      ∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, ∑' z : ℤ,
        (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => G ((ρ + n₀) % q) n ((q : ℤ) * z + (ρ : ℤ)))) ^ p := by
    rw [hP1]
    congr 1
    refine Finset.sum_congr rfl fun n₀ _ => ?_
    rw [hper n₀]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    exact tsum_congr fun z => congrArg (fun v => v ^ p) (hWdec n₀ ρ z)
  have hQ : Qsum = ∑ ρ ∈ Finset.range q, ∑' z : ℤ,
      (PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => G ρ n ((q : ℤ) * z + (ρ : ℤ)))) ^ p := by
    rw [hQsum]
    rw [periodDecompLocal q hq (fun x : ℤ => (S x) ^ p)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    exact tsum_congr fun z => congrArg (fun v => v ^ p) (hSdec ρ z)
  -- (3) the crux: the decimated lattice sums are comparable
  have hcrux : ∀ (s ρ : ℕ), ρ < q →
      (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => G s n ((q : ℤ) * z + (ρ : ℤ)))) ^ p)
        ≤ ENNReal.ofReal ((max Ck 1) ^ p) *
          (∑' z : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => G s n ((q : ℤ) * z + (s : ℤ)))) ^ p) := by
    intro s ρ _
    obtain ⟨K, hKs, hKsp, hid⟩ := hCk δ hδ q hq hdec (s : ℤ)
    have hex : ∀ n : ℕ, ∃ hh : Memℓp (G s n) 2,
        Work.BourgainPlan.IonescuWainger.HasFreqSupport (G s n) hh
          (Work.BourgainPlan.IonescuWainger.arcSet 0 δ) :=
      fun n => rephrase_memℓp_support A f δ hbd s n
    exact decimLatticeCompareLocal p hp r hr1 q hq δ hδ (max Ck 1) hC₀pos hC₀1
      K hKs (fun t => (hKsp t).trans (le_max_left _ _)) (s : ℤ) (ρ : ℤ) hid
      (fun n : ℕ => G s n) (fun n => (hex n).choose) (fun n => (hex n).choose_spec)
  -- (4) assembling
  have hP3 : (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, ∑' z : ℤ,
        (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => G ((ρ + n₀) % q) n ((q : ℤ) * z + (ρ : ℤ)))) ^ p)
      ≤ ENNReal.ofReal ((max Ck 1) ^ p) * ((q : ENNReal) *
        (∑ s ∈ Finset.range q, ∑' z : ℤ,
          (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => G s n ((q : ℤ) * z + (s : ℤ)))) ^ p)) := by
    set Ψ : ℕ → ENNReal := fun s => ∑' z : ℤ,
      (PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => G s n ((q : ℤ) * z + (s : ℤ)))) ^ p with hΨ
    have hstep1 : (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, ∑' z : ℤ,
          (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => G ((ρ + n₀) % q) n ((q : ℤ) * z + (ρ : ℤ)))) ^ p)
        ≤ ∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q,
            ENNReal.ofReal ((max Ck 1) ^ p) * Ψ ((ρ + n₀) % q) := by
      refine Finset.sum_le_sum fun n₀ _ => Finset.sum_le_sum fun ρ hρ' => ?_
      exact hcrux ((ρ + n₀) % q) ρ (Finset.mem_range.mp hρ')
    have hstep2 : (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q,
            ENNReal.ofReal ((max Ck 1) ^ p) * Ψ ((ρ + n₀) % q))
        = ENNReal.ofReal ((max Ck 1) ^ p) *
          (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, Ψ ((ρ + n₀) % q)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n₀ _ => ?_
      rw [Finset.mul_sum]
    have hstep3 : (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, Ψ ((ρ + n₀) % q))
        = ∑ ρ ∈ Finset.range q, ∑ s ∈ Finset.range q, Ψ s := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ρ _ => sum_range_add_mod q hq ρ Ψ
    have hstep4 : (∑ ρ ∈ Finset.range q, ∑ s ∈ Finset.range q, Ψ s)
        = (q : ENNReal) * ∑ s ∈ Finset.range q, Ψ s := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, ∑' z : ℤ,
          (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => G ((ρ + n₀) % q) n ((q : ℤ) * z + (ρ : ℤ)))) ^ p)
        ≤ ∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q,
            ENNReal.ofReal ((max Ck 1) ^ p) * Ψ ((ρ + n₀) % q) := hstep1
      _ = ENNReal.ofReal ((max Ck 1) ^ p) *
          (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, Ψ ((ρ + n₀) % q)) := hstep2
      _ = ENNReal.ofReal ((max Ck 1) ^ p) * (∑ ρ ∈ Finset.range q, ∑ s ∈ Finset.range q, Ψ s) := by
          rw [hstep3]
      _ = ENNReal.ofReal ((max Ck 1) ^ p) * ((q : ENNReal) * ∑ s ∈ Finset.range q, Ψ s) := by
          rw [hstep4]
  have hqinv : ENNReal.rpow (q : ENNReal) (-1) * (q : ENNReal) = 1 := by
    have hq0 : (q : ENNReal) ≠ 0 := by simpa using hq.ne'
    have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
    have hq1 : (q : ENNReal) = ENNReal.rpow (q : ENNReal) 1 := (ENNReal.rpow_one _).symm
    calc ENNReal.rpow (q : ENNReal) (-1) * (q : ENNReal)
        = ENNReal.rpow (q : ENNReal) (-1) * ENNReal.rpow (q : ENNReal) 1 := by
          nth_rw 2 [hq1]
      _ = ENNReal.rpow (q : ENNReal) ((-1) + 1) := (ENNReal.rpow_add (-1) 1 hq0 hqt).symm
      _ = ENNReal.rpow (q : ENNReal) 0 := by norm_num
      _ = 1 := ENNReal.rpow_zero
  have hPle : Psum ≤ ENNReal.ofReal ((max Ck 1) ^ p) * Qsum := by
    rw [hP2, hQ]
    calc ENNReal.rpow (q : ENNReal) (-1) *
          (∑ n₀ ∈ Finset.range q, ∑ ρ ∈ Finset.range q, ∑' z : ℤ,
            (PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => G ((ρ + n₀) % q) n ((q : ℤ) * z + (ρ : ℤ)))) ^ p)
        ≤ ENNReal.rpow (q : ENNReal) (-1) *
            (ENNReal.ofReal ((max Ck 1) ^ p) * ((q : ENNReal) *
              (∑ s ∈ Finset.range q, ∑' z : ℤ,
                (PointwiseErgodicTheorems.variationalNorm r
                  (fun n : ℕ => G s n ((q : ℤ) * z + (s : ℤ)))) ^ p))) :=
          mul_le_mul_of_nonneg_left hP3 bot_le
      _ = ENNReal.ofReal ((max Ck 1) ^ p) *
            (∑ s ∈ Finset.range q, ∑' z : ℤ,
              (PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => G s n ((q : ℤ) * z + (s : ℤ)))) ^ p) := by
          rw [show ENNReal.rpow (q : ENNReal) (-1) *
                (ENNReal.ofReal ((max Ck 1) ^ p) * ((q : ENNReal) *
                  (∑ s ∈ Finset.range q, ∑' z : ℤ,
                    (PointwiseErgodicTheorems.variationalNorm r
                      (fun n : ℕ => G s n ((q : ℤ) * z + (s : ℤ)))) ^ p)))
              = (ENNReal.rpow (q : ENNReal) (-1) * (q : ENNReal)) *
                (ENNReal.ofReal ((max Ck 1) ^ p) *
                  (∑ s ∈ Finset.range q, ∑' z : ℤ,
                    (PointwiseErgodicTheorems.variationalNorm r
                      (fun n : ℕ => G s n ((q : ℤ) * z + (s : ℤ)))) ^ p)) from by
                simp only [mul_assoc, mul_left_comm, mul_comm],
            hqinv, one_mul]

  have hLp : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q W x)
      (ENNReal.ofReal p) MeasureTheory.Measure.count = Psum ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le, MeasureTheory.lintegral_count]
    simp only [enorm_eq_self, hPsum]
  have hLs : MeasureTheory.eLpNorm S (ENNReal.ofReal p) MeasureTheory.Measure.count
      = Qsum ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm)
      (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0.le, MeasureTheory.lintegral_count]
    simp only [enorm_eq_self, hQsum]
  have hpow1 : (ENNReal.ofReal ((max Ck 1) ^ p)) ^ (1 / p) = ENNReal.ofReal (max Ck 1) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (x := (max Ck 1) ^ p) (p := 1 / p)
        (Real.rpow_nonneg (le_of_lt hC₀pos) p) h1p,
      show ((max Ck 1) ^ p) ^ (1 / p) = max Ck 1 by
        rw [← Real.rpow_mul (le_of_lt hC₀pos), show p * (1 / p) = 1 by field_simp,
          Real.rpow_one]]
  calc MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q W x)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = Psum ^ (1 / p) := hLp
    _ ≤ (ENNReal.ofReal ((max Ck 1) ^ p) * Qsum) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hPle h1p
    _ = ENNReal.ofReal (max Ck 1) * Qsum ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1p, hpow1]
    _ = ENNReal.ofReal (max Ck 1) *
        MeasureTheory.eLpNorm S (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [hLs]

end

end Work.KMTAreas.A7Hi
