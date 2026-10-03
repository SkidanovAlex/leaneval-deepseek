import Mathlib
import Submission.Work.KMTAreas.A7Hi.FiberSliceAlgebra
import Submission.Work.KMTAreas.A7Hi.winRotResidueBoundDec
import Submission.Work.KMTAreas.A7.eLpNorm_residueLp_le
import Submission.Port.Aesm

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- **Residue decomposition of a sum over `ℤ` into the shifted classes `q ℤ + (r - M)`.**

For `q ≥ 1`, every integer is uniquely of the form `q z + (r - M)` with `0 ≤ r < q` and `z : ℤ`
(the shift `-M` just permutes the `q` residue classes), so the sum over `ℤ` splits accordingly. -/
lemma cosetShift_decomp (q : ℕ) (hq : 0 < q) (F : ℤ → ENNReal) (M : ℤ) :
    (∑ r ∈ Finset.range q, ∑' z : ℤ, F ((q : ℤ) * z + ((r : ℤ) - M))) = ∑' x : ℤ, F x := by
  haveI : NeZero q := ⟨hq.ne'⟩
  let e₀ : Fin q × ℤ ≃ ℤ := (Equiv.prodComm (Fin q) ℤ).trans (Int.divModEquiv q).symm
  have he₀ : ∀ p : Fin q × ℤ, e₀ p = (q : ℤ) * p.2 + ((p.1 : ℤ)) := by
    intro p
    simp [e₀, Equiv.trans_apply, Int.divModEquiv_symm_apply, mul_comm]
  let e : Fin q × ℤ ≃ ℤ := e₀.trans (Equiv.subRight M)
  have he : ∀ p : Fin q × ℤ, e p = (q : ℤ) * p.2 + ((p.1 : ℤ) - M) := by
    intro p
    rw [show e p = e₀ p - M from rfl, he₀ p]
    ring
  calc (∑ r ∈ Finset.range q, ∑' z : ℤ, F ((q : ℤ) * z + ((r : ℤ) - M)))
      = ∑ r : Fin q, ∑' z : ℤ, F ((q : ℤ) * z + ((r : ℤ) - M)) :=
        (Fin.sum_univ_eq_sum_range (fun r => ∑' z : ℤ, F ((q : ℤ) * z + ((r : ℤ) - M))) q).symm
    _ = ∑' r : Fin q, ∑' z : ℤ, F ((q : ℤ) * z + ((r : ℤ) - M)) :=
        (tsum_fintype (fun r : Fin q => ∑' z : ℤ, F ((q : ℤ) * z + ((r : ℤ) - M)))).symm
    _ = ∑' p : Fin q × ℤ, F ((q : ℤ) * p.2 + ((p.1 : ℤ) - M)) :=
        (ENNReal.tsum_prod (f := fun (a : Fin q) (b : ℤ) => F ((q : ℤ) * b + ((a : ℤ) - M)))).symm
    _ = ∑' p : Fin q × ℤ, F (e p) := tsum_congr (fun p => by rw [he p])
    _ = ∑' x : ℤ, F x := Equiv.tsum_eq e F

/-- **The residue-fibre bound of the large-`L` regime of `FiberVarSamplingG`.**

For a family `u` of bounded sequences lying in the range of the *wide* cut
`fiberOp ρ l₂ (mStargF d U) 0`, the residue average (over the residue classes modulo `q` of the
second variable) of the variational norm of the twisted fibre `fiberOpP ρ P l₂ (mStargF d U) n₀`
is bounded in `ℓ^p` by the variational norm of `u` itself, with a constant depending only on
`ρ, p, r` (in fact only on `p` and the sampling engine).

The proof combines the per-coset comparison `exists_coset_compare_fibre` (steps (1)--(5) of the
fibre route: the slice algebra, the decimation engine `convSublatticeCosetCompareBdd` and the
range identity `hrange`) with the residue bookkeeping of the `ℓ^p`-norm over the residues
(`residueLp`): decompose the spatial variable `x` into the classes `q ℤ + r`, apply the coset
comparison, and re-sum the matching cosets `q ℤ + (r - P(n₀))`, which are again a partition of
`ℤ`. -/
theorem residueLp_fiberOpP_le_of_range
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r)
    (p : ℝ) (hp : 1 < p) (d l₂ U q : ℕ) (hd : 1 ≤ d) (hU : 1 ≤ U) (hq : 0 < q)
    (hband : (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) * (q : ℝ) ≤ 1 / 4)
    (u : ℕ → ℤ → ℂ) (B : ℝ) (hB : ∀ n x, ‖u n x‖ ≤ B)
    (hrange : ∀ n, Work.KMTAreas.A7.fiberOp ρ l₂ (Work.KMTAreas.A7.mStargF d U) 0 (u n) = u n)
    (hqtor : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂, q • α = 0) :
    ∃ C : ℝ, 0 < C ∧
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂
              (Work.KMTAreas.A7.mStargF d U) (n₀ : ℤ) (u n) y)) x)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
        (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀pos, hcomp⟩ :=
    exists_coset_compare_fibre ρ hρ hρ1 P r hr p hp d l₂ U q hd hU hq hband u B hB hrange hqtor
  set W : ℤ → ℕ → ENNReal := fun x n₀ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF d U)
        (n₀ : ℤ) (u n) x) with hW
  set S : ℤ → ENNReal := fun x =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x) with hS
  set Qsum : ENNReal := ∑' x : ℤ, (S x) ^ p with hQsum
  set Cbig : ℝ := max C₀ 1 with hCbig
  have hCbig1 : 1 ≤ Cbig := hCbig ▸ le_max_right C₀ 1
  have hCbigpos : 0 < Cbig := lt_of_lt_of_le zero_lt_one hCbig1
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  have h1p : (0 : ℝ) ≤ 1 / p := by positivity
  have hC₀_le : C₀ ≤ Cbig ^ p := by
    rcases le_total (1 : ℝ) C₀ with h | h
    · have hCb : Cbig = C₀ := by rw [hCbig, max_eq_left h]
      calc C₀ = C₀ ^ (1 : ℝ) := (Real.rpow_one C₀).symm
        _ ≤ C₀ ^ p := Real.rpow_le_rpow_of_exponent_le h (le_of_lt hp)
        _ = Cbig ^ p := by rw [hCb]
    · calc C₀ ≤ 1 := h
        _ ≤ Cbig ^ p := Real.one_le_rpow hCbig1 hp0.le
  refine ⟨Cbig, hCbigpos, ?_⟩
  change MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q W x)
      (ENNReal.ofReal p) MeasureTheory.Measure.count
    ≤ ENNReal.ofReal Cbig * MeasureTheory.eLpNorm S (ENNReal.ofReal p) MeasureTheory.Measure.count
  -- ## the per-residue bound
  have hkey : ∀ n₀ : ℕ, (∑' x : ℤ, (W x n₀) ^ p)
      ≤ ENNReal.ofReal (Cbig ^ p) * Qsum := by
    intro n₀
    rw [periodDecompLocal q hq (fun x : ℤ => (W x n₀) ^ p)]
    calc ∑ ρ ∈ Finset.range q, ∑' z : ℤ, (W ((q : ℤ) * z + (ρ : ℤ)) n₀) ^ p
        ≤ ∑ ρ ∈ Finset.range q, ENNReal.ofReal C₀ *
            (∑' z : ℤ, (S ((q : ℤ) * z + ((ρ : ℤ) - P.eval (n₀ : ℤ)))) ^ p) := by
          refine Finset.sum_le_sum (fun ρ _ => ?_)
          exact hcomp (n₀ : ℤ) (ρ : ℤ)
      _ = ENNReal.ofReal C₀ * (∑ ρ ∈ Finset.range q,
            ∑' z : ℤ, (S ((q : ℤ) * z + ((ρ : ℤ) - P.eval (n₀ : ℤ)))) ^ p) := by
          rw [Finset.mul_sum]
      _ = ENNReal.ofReal C₀ * Qsum := by
          rw [cosetShift_decomp q hq (fun x : ℤ => (S x) ^ p) (P.eval (n₀ : ℤ)), hQsum]
      _ ≤ ENNReal.ofReal (Cbig ^ p) * Qsum :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hC₀_le) bot_le
  -- ## the residue bookkeeping
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hPsum : (∑' x : ℤ, (Work.KMTAreas.A7.residueLp p q W x) ^ p)
      ≤ ENNReal.ofReal (Cbig ^ p) * Qsum := by
    have hres : ∀ x : ℤ, (Work.KMTAreas.A7.residueLp p q W x) ^ p
        = (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, (W x n₀) ^ p :=
      fun x => Work.KMTAreas.A7.residueLp_rpow_pow_eq p hp0 q W x
    rw [tsum_congr hres, ENNReal.tsum_mul_left,
      tsum_finset_sum_ennreal (Finset.range q) (fun x n₀ => (W x n₀) ^ p)]
    calc (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q, ∑' x : ℤ, (W x n₀) ^ p
        ≤ (q : ENNReal)⁻¹ * ((q : ENNReal) * (ENNReal.ofReal (Cbig ^ p) * Qsum)) := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          calc ∑ n₀ ∈ Finset.range q, ∑' x : ℤ, (W x n₀) ^ p
              ≤ ∑ n₀ ∈ Finset.range q, ENNReal.ofReal (Cbig ^ p) * Qsum :=
                Finset.sum_le_sum (fun n₀ _ => hkey n₀)
            _ = (q : ENNReal) * (ENNReal.ofReal (Cbig ^ p) * Qsum) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ENNReal.ofReal (Cbig ^ p) * Qsum := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqt, one_mul]
  -- ## the `ℓ^p` norms
  have hpne : (ENNReal.ofReal p) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp0
  have hpt : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hLp : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q W x)
      (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∑' x : ℤ, (Work.KMTAreas.A7.residueLp p q W x) ^ p) ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hpt, htoReal,
      MeasureTheory.lintegral_count]
    simp only [enorm_eq_self]
  have hLs : MeasureTheory.eLpNorm S (ENNReal.ofReal p) MeasureTheory.Measure.count
      = Qsum ^ (1 / p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hpt, htoReal,
      MeasureTheory.lintegral_count]
    simp only [enorm_eq_self, hQsum]
  have hpow1 : (ENNReal.ofReal (Cbig ^ p)) ^ (1 / p) = ENNReal.ofReal Cbig := by
    rw [ENNReal.ofReal_rpow_of_nonneg (x := Cbig ^ p) (p := 1 / p)
        (Real.rpow_nonneg hCbigpos.le p) h1p,
      show (Cbig ^ p) ^ (1 / p) = Cbig by
        rw [← Real.rpow_mul hCbigpos.le, show p * (1 / p) = 1 by field_simp, Real.rpow_one]]
  calc MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp p q W x)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      = (∑' x : ℤ, (Work.KMTAreas.A7.residueLp p q W x) ^ p) ^ (1 / p) := hLp
    _ ≤ (ENNReal.ofReal (Cbig ^ p) * Qsum) ^ (1 / p) := ENNReal.rpow_le_rpow hPsum h1p
    _ = ENNReal.ofReal Cbig * Qsum ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1p, hpow1]
    _ = ENNReal.ofReal Cbig *
        MeasureTheory.eLpNorm S (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [hLs]

end

end Work.KMTAreas.A7Hi
