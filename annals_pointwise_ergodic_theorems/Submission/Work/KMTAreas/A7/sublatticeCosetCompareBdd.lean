import Mathlib
import Submission.Work.KMTAreas.A7.samplingReproIntegrableUnitProved
import Submission.Work.KMTAreas.A7.convCosetRepIdentityBdd
import Submission.Work.KMTAreas.A7.integrableContinuousBandCompMulAdd
import Submission.Work.KMTAreas.A7Hi.variationalNorm_tsum_le
import Submission.Work.KMTAreas.A7Hi.VrSamplingShift

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform Topology

noncomputable section

/-- Reindexing a sum over `ℤ` by the involution `m ↦ a - m`. -/
lemma tsum_subLeft_ennreal_bdd (f : ℤ → ENNReal) (a : ℤ) :
    (∑' m : ℤ, f (a - m)) = ∑' d : ℤ, f d := by
  rw [← Equiv.tsum_eq (Equiv.subLeft a) f]
  exact tsum_congr (fun m => by rw [Equiv.subLeft_apply])

/-- Reindexing a sum over `ℤ` by a translation. -/
lemma tsum_addRight_ennreal_bdd (f : ℤ → ENNReal) (a : ℤ) :
    (∑' m : ℤ, f (m + a)) = ∑' d : ℤ, f d := by
  rw [← Equiv.tsum_eq (Equiv.addRight a) f]
  exact tsum_congr (fun m => by rw [Equiv.coe_addRight])

/-! ## The uniform sublattice Shannon kernel -/

/-- **A uniform family of sublattice Shannon kernels.**  There is `A > 0` such that for every
`β > 0` and `q ≥ 1` with `β q ≤ 1/4` there is a kernel `K : ℤ → ℂ` whose coset spread is bounded by
`A` uniformly in the coset, and which reproduces every integrable continuous band-`β` function from
its samples on *every* coset `qℤ + r₀`. -/
theorem uniformSublatticeKernelBdd :
    ∃ A : ℝ, 0 < A ∧
      ∀ (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : 0 < q) (hβq : β * (q : ℝ) ≤ 1 / 4),
        ∃ K : ℤ → ℂ,
          (∀ d : ℤ, (∑' u : ℤ, ‖K (q * u + d)‖ₑ) ≤ ENNReal.ofReal A) ∧
          ∀ (r₀ : ℤ) (G : ℤ → ℂ) (γ : ℝ → ℂ), MeasureTheory.Integrable γ → Continuous γ →
            (∀ m : ℤ, γ (m : ℝ) = G m) →
            (∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β → FourierTransform.fourier γ ξ = 0) →
            ∀ x : ℤ, G x = ∑' m : ℤ, G (q * m + r₀) * K (x - (q * m + r₀)) := by
  obtain ⟨ψ, hψ1, hψs⟩ := A7Hi.exists_samplingWindowHi (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨M, hMpos, _hMsub, hMadd⟩ := A7Hi.latticeMassHi ψ
  refine ⟨M, hMpos, ?_⟩
  intro β hβ q hq hβq
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : ((q : ℝ)) ≠ 0 := hqpos.ne'
  let K : ℤ → ℂ := fun n => ψ ((n : ℝ) / (q : ℝ))
  refine ⟨K, ?_, ?_⟩
  · intro d
    have harg : ∀ u : ℤ, (((q : ℤ) * u + d : ℤ) : ℝ) / (q : ℝ) = (d : ℝ) / (q : ℝ) + (u : ℝ) := by
      intro u
      push_cast
      field_simp
      ring
    calc (∑' u : ℤ, ‖K (q * u + d)‖ₑ)
        = ∑' u : ℤ, ‖ψ ((d : ℝ) / (q : ℝ) + (u : ℝ))‖ₑ := by
          refine tsum_congr (fun u => ?_)
          show ‖ψ ((((q : ℤ) * u + d : ℤ) : ℝ) / (q : ℝ))‖ₑ = ‖ψ ((d : ℝ) / (q : ℝ) + (u : ℝ))‖ₑ
          rw [harg u]
      _ ≤ ENNReal.ofReal M := hMadd ((d : ℝ) / (q : ℝ))
  · intro r₀ G γ hγint hγcont hGγ hγband x
    obtain ⟨hFint, hFcont, hFband⟩ :=
      integrableContinuousBandCompMulAdd (q := q) hq (β := β) (r₀ := r₀) hγint hγcont hγband
    have hFband' : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) →
        FourierTransform.fourier (fun t : ℝ => γ ((q : ℝ) * t + (r₀ : ℝ))) ξ = 0 := by
      intro ξ hξ
      refine hFband ξ (fun hmem => hξ ?_)
      exact ⟨by linarith [hβq, hmem.1], by linarith [hβq, hmem.2]⟩
    have hkey := samplingReproIntegrableUnitProved (1 / 4) (by norm_num) (by norm_num) ψ hψ1 hψs
      (fun t : ℝ => γ ((q : ℝ) * t + (r₀ : ℝ))) hFint hFcont hFband'
      (((x : ℝ) - (r₀ : ℝ)) / (q : ℝ))
    have hargx : (q : ℝ) * (((x : ℝ) - (r₀ : ℝ)) / (q : ℝ)) + (r₀ : ℝ) = (x : ℝ) := by
      field_simp
      ring
    rw [hargx] at hkey
    rw [← hGγ x, hkey]
    refine tsum_congr (fun m => ?_)
    have h1 : γ ((q : ℝ) * (m : ℝ) + (r₀ : ℝ)) = G (q * m + r₀) := by
      rw [← hGγ (q * m + r₀)]
      congr 1
      push_cast
      ring
    have h2 : ψ (((x : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ))
        = K (x - (q * m + r₀)) := by
      show ψ (((x : ℝ) - (r₀ : ℝ)) / (q : ℝ) - (m : ℝ))
        = ψ ((((x - (q * m + r₀) : ℤ)) : ℝ) / (q : ℝ))
      congr 1
      push_cast
      field_simp
      ring
    rw [h2, h1, mul_comm]

/-! ## The coset comparison -/

/-- **The weighted Schur/power-mean step of the coset comparison.** -/
theorem cosetSchurCompareBdd (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 1 ≤ r)
    (q : ℕ) (c c' : ℤ) (K : ℤ → ℂ) (A : ℝ) (hA : 0 ≤ A) (Ξ : ℕ → ℤ → ℂ)
    (hKspread : ∀ d : ℤ, (∑' u : ℤ, ‖K (q * u + d)‖ₑ) ≤ ENNReal.ofReal A)
    (hid : ∀ (n : ℕ) (x : ℤ), Ξ n x = ∑' m : ℤ, K (x - (q * m + c')) * Ξ n (q * m + c')) :
    (∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Ξ n (q * u + c))) ^ p)
      ≤ ENNReal.ofReal (A ^ (p - 1) * A) *
          (∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Ξ n (q * u + c'))) ^ p) := by
  have hpoint : ∀ u : ℤ,
      (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Ξ n (q * u + c))) ^ p
        ≤ (∑' m : ℤ, ‖K (q * (u - m) + (c - c'))‖ₑ *
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Ξ n (q * m + c'))) ^ p := by
    intro u
    refine ENNReal.rpow_le_rpow ?_ (by linarith : (0 : ℝ) ≤ p)
    have hfun : (fun n : ℕ => Ξ n (q * u + c))
        = fun n : ℕ => ∑' m : ℤ, K (q * (u - m) + (c - c')) * Ξ n (q * m + c') := by
      funext n
      rw [hid n (q * u + c)]
      apply tsum_congr
      intro m
      congr 2
      push_cast
      ring
    rw [hfun]
    exact (A7Hi.variationalNorm_tsum_le r hr
      (fun m : ℤ => K (q * (u - m) + (c - c'))) (fun m n => Ξ n (q * m + c')))
  have hrow : ∀ u : ℤ, (∑' m : ℤ, ‖K (q * (u - m) + (c - c'))‖ₑ) ≤ ENNReal.ofReal A := by
    intro u
    rw [tsum_subLeft_ennreal_bdd (fun d : ℤ => ‖K (q * d + (c - c'))‖ₑ) u]
    exact hKspread (c - c')
  have hcol : ∀ m : ℤ, (∑' u : ℤ, ‖K (q * (u - m) + (c - c'))‖ₑ) ≤ ENNReal.ofReal A := by
    intro m
    have h1 : (∑' u : ℤ, ‖K (q * (u - m) + (c - c'))‖ₑ)
        = ∑' d : ℤ, ‖K (q * d + (c - c'))‖ₑ :=
      tsum_addRight_ennreal_bdd (fun d : ℤ => ‖K (q * d + (c - c'))‖ₑ) (-m)
    rw [h1]
    exact hKspread (c - c')
  calc (∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Ξ n (q * u + c))) ^ p)
      ≤ ∑' u : ℤ, (∑' m : ℤ, ‖K (q * (u - m) + (c - c'))‖ₑ *
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Ξ n (q * m + c'))) ^ p := ENNReal.tsum_le_tsum hpoint
    _ ≤ ENNReal.ofReal (A ^ (p - 1) * A) * (∑' u : ℤ,
          (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Ξ n (q * u + c'))) ^ p) :=
        A7Hi.weightedSchurHi p hp
          (W := fun u m => ‖K (q * (u - m) + (c - c'))‖ₑ)
          (v := fun m => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Ξ n (q * m + c'))) (A := A) (B := A) hA hrow hcol

/-- **The coset comparison for band-`β` convolution families** (the "θ-uniformity" of the
quantitative Shannon sampling result, in the form the caller needs). -/
theorem convSublatticeCosetCompareBdd (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 1 ≤ r) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : 0 < q) (hβq : β * (q : ℝ) ≤ 1 / 4)
        (kappa : ℕ → ℤ → ℂ) (kext : ℕ → ℝ → ℂ),
        (∀ n : ℕ, MeasureTheory.Integrable (kext n) ∧ Continuous (kext n) ∧
          (∀ m : ℤ, kext n (m : ℝ) = kappa n m) ∧
          (∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β → FourierTransform.fourier (kext n) ξ = 0)) →
        (∀ n : ℕ, Summable (fun j : ℤ => ‖kappa n j‖)) →
        ∀ (h : ℕ → ℤ → ℤ → ℂ) (B : ℝ), (∀ n y z, ‖h n y z‖ ≤ B) →
        ∀ (y c c' : ℤ),
          (∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, kappa n j * h n y (q*u + c - j)))^p)
          ≤ ENNReal.ofReal C * (∑' u : ℤ, (PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => ∑' j : ℤ, kappa n j * h n y (q*u + c' - j)))^p) := by
  obtain ⟨A, hApos, hKern⟩ := uniformSublatticeKernelBdd
  refine ⟨A ^ p, Real.rpow_pos_of_pos hApos p, ?_⟩
  intro β hβ q hq hβq κ kext hdata hκsum h B hB y c c'
  obtain ⟨K, hKenorm, hKrep⟩ := hKern β hβ q hq hβq
  have hAp : A ^ (p - 1) * A = A ^ p := by
    have h2 : A ^ (p - 1) * A ^ (1 : ℝ) = A ^ p := by
      rw [← Real.rpow_add hApos (p - 1) 1, sub_add_cancel]
    rwa [Real.rpow_one] at h2
  have hrep : ∀ (n : ℕ) (r₀ j : ℤ),
      κ n j = ∑' m : ℤ, K (j - (q * m + r₀)) * κ n (q * m + r₀) := by
    intro n r₀ j
    have h := hKrep r₀ (κ n) (kext n) (hdata n).1 (hdata n).2.1 (hdata n).2.2.1
      (hdata n).2.2.2 j
    rw [h]
    refine tsum_congr (fun m => ?_)
    ring
  have hid : ∀ (n : ℕ) (x : ℤ), (∑' j : ℤ, κ n j * h n y (x - j))
      = ∑' m : ℤ, K (x - (q * m + c')) * (∑' j : ℤ, κ n j * h n y (q * m + c' - j)) :=
    fun n x => convCosetRepIdentityBdd q hq c' K (κ n) (h n y) A B hApos.le hKenorm
      (hκsum n) (hrep n) (fun z => hB n y z) x
  have hmain := cosetSchurCompareBdd p hp r hr q c c' K A hApos.le
    (fun n z => ∑' j : ℤ, κ n j * h n y (z - j)) hKenorm hid
  rw [hAp] at hmain
  exact hmain

end

end Work.KMTAreas.A7
