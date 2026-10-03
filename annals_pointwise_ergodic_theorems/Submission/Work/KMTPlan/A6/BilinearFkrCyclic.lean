import Mathlib
import Submission.Work.KMTAreas.A7.Btwist_bilinear_of_bounded
import Submission.Work.KMTAreas.A7.FiberGeneral
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Work.KMTAreas.tsum_inv_sq_shift_le
import Submission.Work.KMTPlan.A6.BilinearFkr
import Submission.Work.KMTPlan.A6.MdlDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.KMTPlan.A6.BilinearFkrCyclic`

The *cyclic* (finite group `ZMod Q` with the counting measure) form of the paper's Corollary
`bilinear-fkr` (Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear
polynomial averages*, arXiv:2008.00857, §10), in the **packet** form: the bilinear operator `B` is
only assumed *additive* in each variable, and the operator estimate is assumed only for the pairs
`(u m - u n, v l)` and `(u l, v m - v n)` that occur in the Lipschitz decomposition

`B (u n) (v n) - B (u m) (v m) = B (u n - u m) (v n) + B (u m) (v n - v m)`

(which itself only needs additivity).

* The reference form of the theorem for a general measure space, with the operator estimate
  assumed for *all* pairs, is `Work.KMTPlan.A6.BilinearFkr`.
* The form here is the one needed by the §8 model tuple: the operator estimate is only available
  for the packets that actually occur (cf. `Work.KMTPlan.A6.MdlSliceFkrPackets`), and the test
  space is the finite cyclic group.

The two ingredients are

* `FkrInterchangeUnif` — the paper's Lemma `fkr`, in the form where a *single* constant works for
  every measure space (the target below quantifies over `Q`, so a uniform constant is needed);
* `bilinearFkrPacketsGen` — the packet estimate on an arbitrary measure space, following the
  assembly of `MdlSliceFkrPackets`.

On `ZMod Q` the measurable space is discrete, so *every* function is (a.e.-strongly) measurable;
this is what makes the additivity-only form provable (the general statement
`Work.KMTPlan.A6.BilinearFkr` has to assume measurability of all `B e f`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal BigOperators

/-- The variational part of a pointwise measurable sequence is measurable: it is a supremum over
the countable family of finite monotone index selections (v4.35 port helper). -/
private lemma measurable_varPart_local {X : Type*} [MeasurableSpace X] {r : NNReal}
    (hr : 0 < (r : ℝ)) {u : ℕ → X → ℂ} (hu : ∀ n, Measurable (u n)) :
    Measurable (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun n => u n x)) := by
  have hfun : (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun n => u n x))
      = fun x => ⨆ (J : ℕ) (w : Fin (J + 1) → ℕ) (_ : Monotone w),
            ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
              (fun i : Fin J => u (w i.succ) x - u (w i.castSucc) x))‖ := by
    funext x
    unfold Submission.PointwiseErgodicTheorems.varPart
    apply le_antisymm
    · refine iSup_le (fun K => iSup_le (fun N => iSup_le (fun hN => ?_)))
      refine le_iSup_of_le K ?_
      refine le_iSup_of_le (fun j : Fin (K + 1) => N (j : ℕ)) ?_
      refine le_iSup_of_le (fun _ _ h => hN h) ?_
      exact le_rfl
    · refine iSup_le (fun K => iSup_le (fun w => iSup_le (fun hw => ?_)))
      let N : ℕ → ℕ := fun k => w ⟨min k K, Nat.lt_succ_of_le (Nat.min_le_right k K)⟩
      have hNmono : Monotone N := by
        intro x y hxy
        refine hw ?_
        simp only [Fin.le_def]
        omega
      refine le_iSup_of_le K ?_
      refine le_iSup_of_le N ?_
      refine le_iSup_of_le hNmono ?_
      have h1 : ∀ i : Fin K, N ((i : ℕ)) = w i.castSucc := by
        intro i
        simp only [N]
        congr 1
        exact Fin.ext (Nat.min_eq_left i.isLt.le)
      have h2 : ∀ i : Fin K, N ((i : ℕ) + 1) = w i.succ := by
        intro i
        simp only [N]
        congr 1
        exact Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt i.isLt))
      have hv : (fun i : Fin K => u (w i.succ) x - u (w i.castSucc) x)
          = (fun i : Fin K => u (N ((i : ℕ) + 1)) x - u (N (i : ℕ)) x) := by
        funext i
        rw [h1 i, h2 i]
      rw [hv]
  rw [hfun]
  refine Measurable.iSup (fun J => Measurable.iSup (fun w => Measurable.iSup (fun _ => ?_)))
  have hterm : (fun x => ENNReal.ofReal ‖(WithLp.toLp (r : ℝ≥0∞)
      (fun i : Fin J => u (w i.succ) x - u (w i.castSucc) x))‖)
      = fun x => ENNReal.ofReal ((∑ i : Fin J,
          ‖u (w i.succ) x - u (w i.castSucc) x‖ ^ (r : ℝ)) ^ (1 / (r : ℝ))) := by
    funext x
    congr 1
    rw [PiLp.norm_eq_sum (p := (r : ℝ≥0∞)) (by rw [ENNReal.coe_toReal]; exact hr)]
    simp [ENNReal.coe_toReal]
  rw [hterm]
  refine ENNReal.continuous_ofReal.measurable.comp ?_
  refine (Real.continuous_rpow_const (by positivity)).measurable.comp ?_
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (Real.continuous_rpow_const hr.le).measurable.comp (((hu _).sub (hu _)).norm)

/-- Every complex-valued function on `ZMod Q` is a.e.-strongly measurable for the counting measure
(the measurable space on `ZMod Q` is discrete). -/
theorem aestronglyMeasurable_count_zmod (Q : ℕ) (f : ZMod Q → ℂ) :
    AEStronglyMeasurable f (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q)) := by
  have h : Measurable f := by fun_prop
  exact h.aestronglyMeasurable

/-- **The paper's Lemma `fkr`, with a constant uniform in the measure space.**  For `1 ≤ R < r`
there is `C > 0` such that for *every* measure space `(X, μ)` and every sequence
`f : ℕ → X → ℂ` of a.e.-strongly-measurable functions,

`‖x ↦ varPart r (fun k => f k x)‖_{L^r(μ)} ≤ C · ‖f‖_{V^R(ℕ; L^r(μ))}`.

This is the statement of `Work.KMTPlan.A6.FkrInterchange` with the quantifiers over `(X, μ)`
moved inside the `∃ C`; the constant exhibited in that proof,
`20 · 2^{1/R} / (1 - 2^{1/r - 1/R})`, does not depend on the measure space, so the same proof
applies verbatim. -/
theorem FkrInterchangeUnif {R : ℝ} {r : NNReal} (hR : 1 ≤ R) (hRr : R < (r : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
      (f : ℕ → X → ℂ), (∀ k, AEStronglyMeasurable (f k) μ) →
      eLpNorm (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun k => f k x))
          (r : ENNReal) μ
        ≤ ENNReal.ofReal C * fkrW μ R r f := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := le_trans hR hRr.le
  have hr0 : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr1
  have hrE : (1 : ENNReal) ≤ (r : ENNReal) := by exact_mod_cast hr1
  have hrE0 : (r : ENNReal) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hrE)
  have hρ1 : (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R) < 1 := by
    have h : 1 / (r : ℝ) < 1 / R := one_div_lt_one_div_of_lt hR0 hRr
    have hy : (0 : ℝ) < -(1 / (r : ℝ) - 1 / R) := by linarith
    have h2 : (1 : ℝ) < 2 := by norm_num
    have hpos : (1 : ℝ) < (2 : ℝ) ^ (-(1 / (r : ℝ) - 1 / R)) := Real.one_lt_rpow h2 hy
    rw [show (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R)
        = ((2 : ℝ) ^ (-(1 / (r : ℝ) - 1 / R)))⁻¹ from by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf]
    exact inv_lt_one_of_one_lt₀ hpos
  have hCpos : 0 < 20 * (2 : ℝ) ^ (1 / R) / (1 - (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R)) := by
    have hlt : (0 : ℝ) < 1 - (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R) := by linarith
    positivity
  refine ⟨20 * (2 : ℝ) ^ (1 / R) / (1 - (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R)), hCpos, ?_⟩
  intro X _ μ f hf
  set g : ℕ → X → ℂ := fun k => AEMeasurable.mk (f k) ((hf k).aemeasurable) with hgdef
  have hgmeas : ∀ k, Measurable (g k) := fun k => AEMeasurable.measurable_mk _
  have hge : ∀ k, f k =ᵐ[μ] g k := fun k => AEMeasurable.ae_eq_mk _
  have hgate : (fun x => fun k => f k x) =ᵐ[μ] (fun x => fun k => g k x) := by
    filter_upwards [ae_all_iff.mpr (fun k => hge k)] with x hx
    exact funext hx
  have hvar : (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun k => f k x))
      =ᵐ[μ] (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun k => g k x)) := by
    filter_upwards [hgate] with x hx
    rw [hx]
  have hW : fkrW μ R r g = fkrW μ R r f := by
    simp only [fkrW]
    refine iSup_congr fun J => iSup_congr fun k => iSup_congr fun hk => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact eLpNorm_congr_ae (((hge (k i.succ)).sub (hge (k i.castSucc))).symm)
  rw [eLpNorm_congr_ae hvar, ← hW]
  rcases eq_or_ne (fkrW μ R r g) ⊤ with hWtop | hWtop
  · rw [hWtop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCpos).ne']
    exact le_top
  rcases eq_or_ne (fkrW μ R r g) 0 with hW0 | hW0
  · rw [fkrW_zero_varPart (X := X) μ hR0 hr0 g
      (fun k => (hgmeas k).aestronglyMeasurable) hW0, hW0, mul_zero]
  · have hwpos : 0 < (fkrW μ R r g).toReal := ENNReal.toReal_pos hW0 hWtop
    have hstep : ∀ K, eLpNorm
          (fun x => varKc (r : ℝ) K (fun k => g k x)) (r : ENNReal) μ
        ≤ ENNReal.ofReal (20 * (2 : ℝ) ^ (1 / R) / (1 - (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R)))
          * fkrW μ R r g := by
      intro K
      rw [← ENNReal.ofReal_toReal hWtop]
      exact fkr_step μ hR hr1 hRr g hgmeas hwpos (ENNReal.ofReal_toReal hWtop).symm K
    have hle : eLpNorm
          (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun k => g k x))
          (r : ENNReal) μ
        ≤ eLpNorm (fun x => ⨆ K, varKc (r : ℝ) K (fun k => g k x)) (r : ENNReal) μ := by
      refine eLpNorm_mono_ennreal ENNReal.coe_ne_top (fun x => ?_) μ
        (measurable_varPart_local hr0 hgmeas).aestronglyMeasurable
      exact varPart_le_iSup_varKc r hr1 (fun k => g k x)
    have hmct : eLpNorm (fun x => ⨆ K, varKc (r : ℝ) K (fun k => g k x)) (r : ENNReal) μ
        = ⨆ K, eLpNorm (fun x => varKc (r : ℝ) K (fun k => g k x)) (r : ENNReal) μ := by
      refine Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone hrE0 ENNReal.coe_ne_top
        (fun K => measurable_varKc hgmeas (r : ℝ) K) ?_
      intro m n hmn x
      exact varKc_mono (r : ℝ) hmn (fun k => g k x)
    calc eLpNorm (fun x => Submission.PointwiseErgodicTheorems.varPart r (fun k => g k x))
          (r : ENNReal) μ
        ≤ eLpNorm (fun x => ⨆ K, varKc (r : ℝ) K (fun k => g k x)) (r : ENNReal) μ := hle
      _ = ⨆ K, eLpNorm (fun x => varKc (r : ℝ) K (fun k => g k x)) (r : ENNReal) μ := hmct
      _ ≤ ENNReal.ofReal (20 * (2 : ℝ) ^ (1 / R) / (1 - (2 : ℝ) ^ (1 / (r : ℝ) - 1 / R)))
            * fkrW μ R r g := iSup_le hstep

/-- **The packet form of Corollary `bilinear-fkr` on an arbitrary measure space**: `B` is additive
in each variable and the operator estimate is assumed only for the pairs `(u m - u n, v l)` and
`(u l, v m - v n)` (the two terms of the Lipschitz decomposition).  The constant is uniform in the
measure space. -/
theorem bilinearFkrPacketsGen {R : ℝ} {r : NNReal} (hR : 1 ≤ R) (hRr : R < (r : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
      (hmeas : ∀ f : X → ℂ, AEStronglyMeasurable f μ)
      {M : ℝ} (hM : 0 ≤ M)
      (B : (X → ℂ) → (X → ℂ) → (X → ℂ))
      (hadd₁ : ∀ e e' f : X → ℂ, B (e + e') f = B e f + B e' f)
      (hadd₂ : ∀ e f f' : X → ℂ, B e (f + f') = B e f + B e f')
      (u v : ℕ → X → ℂ)
      (hB1 : ∀ m n l : ℕ, eLpNorm (fun x => B (u m - u n) (v l) x) (r : ENNReal) μ
        ≤ ENNReal.ofReal M * eLpNorm (u m - u n) 2 μ * eLpNorm (v l) 2 μ)
      (hB2 : ∀ m n l : ℕ, eLpNorm (fun x => B (u l) (v m - v n) x) (r : ENNReal) μ
        ≤ ENNReal.ofReal M * eLpNorm (u l) 2 μ * eLpNorm (v m - v n) 2 μ),
      eLpNorm (fun x => Submission.PointwiseErgodicTheorems.varPart r
          (fun n : ℕ => B (u n) (v n) x)) (r : ENNReal) μ
      ≤ ENNReal.ofReal (C * M) *
          ((⨆ n : ℕ, eLpNorm (u n) 2 μ) +
            (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
              ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
                ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 μ) R) (1 / R))) *
          ((⨆ n : ℕ, eLpNorm (v n) 2 μ) +
            (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
              ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
                ENNReal.rpow (eLpNorm (v (k i.succ) - v (k i.castSucc)) 2 μ) R) (1 / R))) := by
  obtain ⟨C, hCpos, hC⟩ := FkrInterchangeUnif (R := R) (r := r) hR hRr
  refine ⟨C, hCpos, ?_⟩
  intro X _ μ hmeas M hM B hadd₁ hadd₂ u v hB1 hB2
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hrE : (1 : ENNReal) ≤ (r : ENNReal) := by exact_mod_cast le_trans hR hRr.le
  set Su : ENNReal := ⨆ n : ℕ, eLpNorm (u n) 2 μ with hSu
  set Vu : ENNReal := ⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 μ) R) (1 / R) with hVu
  set Sv : ENNReal := ⨆ n : ℕ, eLpNorm (v n) 2 μ with hSv
  set Vv : ENNReal := ⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (v (k i.succ) - v (k i.castSucc)) 2 μ) R) (1 / R) with hVv
  suffices hmain : eLpNorm (fun x : X => Submission.PointwiseErgodicTheorems.varPart r
        (fun n : ℕ => B (u n) (v n) x)) (r : ENNReal) μ
      ≤ ENNReal.ofReal (C * M) * (Su + Vu) * (Sv + Vv) by
    simpa only [hSu, hVu, hSv, hVv] using hmain
  have hCg : eLpNorm (fun x : X => Submission.PointwiseErgodicTheorems.varPart r
        (fun n : ℕ => B (u n) (v n) x)) (r : ENNReal) μ
      ≤ ENNReal.ofReal C * fkrW μ R r (fun n x => B (u n) (v n) x) :=
    hC (X := X) μ (fun n x => B (u n) (v n) x) (fun n => hmeas _)
  have hfkrW : fkrW μ R r (fun n x => B (u n) (v n) x)
      ≤ ENNReal.ofReal M * ((Su + Vu) * (Sv + Vv)) := by
    refine iSup_le (fun J => iSup_le (fun k => iSup_le (fun hk => ?_)))
    set au : Fin J → ENNReal := fun i =>
      eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 μ with hau
    set av : Fin J → ENNReal := fun i =>
      eLpNorm (v (k i.succ) - v (k i.castSucc)) 2 μ with hav
    set a : Fin J → ENNReal := fun i =>
      ENNReal.ofReal M * au i * eLpNorm (v (k i.succ)) 2 μ with ha
    set b : Fin J → ENNReal := fun i =>
      ENNReal.ofReal M * eLpNorm (u (k i.castSucc)) 2 μ * av i with hb
    have hstep : ∀ i : Fin J,
        eLpNorm (fun x : X => B (u (k i.succ)) (v (k i.succ)) x
            - B (u (k i.castSucc)) (v (k i.castSucc)) x)
          (r : ENNReal) μ ≤ a i + b i := by
      intro i
      have hdiff : (fun x : X => B (u (k i.succ)) (v (k i.succ)) x
            - B (u (k i.castSucc)) (v (k i.castSucc)) x)
          = (fun x : X => B (u (k i.succ) - u (k i.castSucc)) (v (k i.succ)) x)
            + (fun x : X => B (u (k i.castSucc)) (v (k i.succ) - v (k i.castSucc)) x) :=
        bfkr_bilinear_increment_decomp B hadd₁ hadd₂ u v (k i.castSucc) (k i.succ)
      rw [hdiff]
      refine (eLpNorm_add_le hrE).trans ?_
      rw [ha, hb]
      exact add_le_add (hB1 (k i.succ) (k i.castSucc) (k i.succ))
        (hB2 (k i.succ) (k i.castSucc) (k i.castSucc))
    have hsum1 : (∑ i : Fin J, (eLpNorm (fun x : X =>
            B (u (k i.succ)) (v (k i.succ)) x
          - B (u (k i.castSucc)) (v (k i.castSucc)) x)
          (r : ENNReal) μ) ^ R) ^ (1 / R)
        ≤ (∑ i : Fin J, (a i + b i) ^ R) ^ (1 / R) := by
      refine ENNReal.rpow_le_rpow (Finset.sum_le_sum (fun i _ =>
        ENNReal.rpow_le_rpow (hstep i) hR0.le)) ?_
      exact le_of_lt (one_div_pos.mpr hR0)
    have hsum2 : (∑ i : Fin J, (a i + b i) ^ R) ^ (1 / R)
        ≤ (∑ i : Fin J, (a i) ^ R) ^ (1 / R) + (∑ i : Fin J, (b i) ^ R) ^ (1 / R) :=
      ENNReal.Lp_add_le Finset.univ a b hR
    have hA : (∑ i : Fin J, (a i) ^ R) ^ (1 / R) ≤ (ENNReal.ofReal M * Sv) * Vu := by
      rw [ha]
      refine (bfkr_ennreal_lp_weight_le hR (Finset.univ : Finset (Fin J)) (ENNReal.ofReal M)
        (fun i : Fin J => au i) (fun i : Fin J => eLpNorm (v (k i.succ)) 2 μ)).trans ?_
      have hsv' : (⨆ i : Fin J, eLpNorm (v (k i.succ)) 2 μ) ≤ Sv := by
        rw [hSv]
        exact iSup_le (fun i => le_iSup (fun n : ℕ => eLpNorm (v n) 2 μ) (k i.succ))
      have hvu : (∑ i : Fin J, (au i) ^ R) ^ (1 / R) ≤ Vu := by
        rw [hVu]
        exact le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
      calc ENNReal.ofReal M * (⨆ i : Fin J, eLpNorm (v (k i.succ)) 2 μ)
            * (∑ i : Fin J, (au i) ^ R) ^ (1 / R)
          ≤ ENNReal.ofReal M * Sv * (∑ i : Fin J, (au i) ^ R) ^ (1 / R) :=
            bfkr_mul_le_left _ (bfkr_mul_le_right _ hsv')
        _ ≤ ENNReal.ofReal M * Sv * Vu := bfkr_mul_le_right _ hvu
    have hBv : (∑ i : Fin J, (b i) ^ R) ^ (1 / R) ≤ (ENNReal.ofReal M * Su) * Vv := by
      rw [hb]
      have hswap : ∀ i : Fin J, ENNReal.ofReal M
            * eLpNorm (u (k i.castSucc)) 2 μ * av i
          = ENNReal.ofReal M * av i * eLpNorm (u (k i.castSucc)) 2 μ :=
        fun i => by ring
      simp only [hswap]
      refine (bfkr_ennreal_lp_weight_le hR (Finset.univ : Finset (Fin J)) (ENNReal.ofReal M)
        (fun i : Fin J => av i) (fun i : Fin J => eLpNorm (u (k i.castSucc)) 2 μ)).trans ?_
      have hsu' : (⨆ i : Fin J, eLpNorm (u (k i.castSucc)) 2 μ) ≤ Su := by
        rw [hSu]
        exact iSup_le (fun i => le_iSup (fun n : ℕ => eLpNorm (u n) 2 μ) (k i.castSucc))
      have hvv : (∑ i : Fin J, (av i) ^ R) ^ (1 / R) ≤ Vv := by
        rw [hVv]
        exact le_iSup_of_le J (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
      calc ENNReal.ofReal M * (⨆ i : Fin J, eLpNorm (u (k i.castSucc)) 2 μ)
            * (∑ i : Fin J, (av i) ^ R) ^ (1 / R)
          ≤ ENNReal.ofReal M * Su * (∑ i : Fin J, (av i) ^ R) ^ (1 / R) :=
            bfkr_mul_le_left _ (bfkr_mul_le_right _ hsu')
        _ ≤ ENNReal.ofReal M * Su * Vv := bfkr_mul_le_right _ hvv
    calc (∑ i : Fin J, (eLpNorm (fun x : X =>
            B (u (k i.succ)) (v (k i.succ)) x
          - B (u (k i.castSucc)) (v (k i.castSucc)) x)
          (r : ENNReal) μ) ^ R) ^ (1 / R)
        ≤ (∑ i : Fin J, (a i + b i) ^ R) ^ (1 / R) := hsum1
      _ ≤ (∑ i : Fin J, (a i) ^ R) ^ (1 / R) + (∑ i : Fin J, (b i) ^ R) ^ (1 / R) := hsum2
      _ ≤ (ENNReal.ofReal M * Sv) * Vu + (ENNReal.ofReal M * Su) * Vv := add_le_add hA hBv
      _ = ENNReal.ofReal M * (Sv * Vu + Su * Vv) := by rw [mul_assoc, mul_assoc, ← mul_add]
      _ ≤ ENNReal.ofReal M * ((Su + Vu) * (Sv + Vv)) :=
          bfkr_mul_le_right _ (bfkr_ennreal_add_mul_le Su Vu Sv Vv)
  calc eLpNorm (fun x : X => Submission.PointwiseErgodicTheorems.varPart r
        (fun n : ℕ => B (u n) (v n) x)) (r : ENNReal) μ
      ≤ ENNReal.ofReal C * fkrW μ R r (fun n x => B (u n) (v n) x) := hCg
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal M * ((Su + Vu) * (Sv + Vv))) :=
        bfkr_mul_le_right _ hfkrW
    _ = ENNReal.ofReal (C * M) * (Su + Vu) * (Sv + Vv) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hCpos.le, mul_assoc]

open Lean.Parser.Term in
syntax "∀ " (ppSpace bracketedBinder)+ " :" term : term

macro_rules
  | `(∀ $[$bs]* : $body) => `(∀ $[$bs]*, $body)

theorem BilinearFkrCyclic {R : ℝ} {r : NNReal} (hR : 1 ≤ R) (hRr : R < (r : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q : ℕ} (hQ : 1 ≤ Q) {M : ℝ} (hM : 0 ≤ M)
    (B : (ZMod Q → ℂ) → (ZMod Q → ℂ) → (ZMod Q → ℂ))
    (hadd₁ : ∀ e e' f : ZMod Q → ℂ, B (e + e') f = B e f + B e' f)
    (hadd₂ : ∀ e f f' : ZMod Q → ℂ, B e (f + f') = B e f + B e f')
    (u v : ℕ → ZMod Q → ℂ)
    (hB1 : ∀ m n l : ℕ, MeasureTheory.eLpNorm (fun ρ : ZMod Q => B (u m - u n) (v l) ρ)
        (r : ENNReal) (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))
      ≤ ENNReal.ofReal M * MeasureTheory.eLpNorm (u m - u n) 2
          (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))
        * MeasureTheory.eLpNorm (v l) 2
          (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q)))
    (hB2 : ∀ m n l : ℕ, MeasureTheory.eLpNorm (fun ρ : ZMod Q => B (u l) (v m - v n) ρ)
        (r : ENNReal) (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))
      ≤ ENNReal.ofReal M * MeasureTheory.eLpNorm (u l) 2
          (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))
        * MeasureTheory.eLpNorm (v m - v n) 2
          (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))) :
      MeasureTheory.eLpNorm (fun ρ : ZMod Q => Submission.PointwiseErgodicTheorems.varPart r
          (fun n : ℕ => B (u n) (v n) ρ))
        (r : ENNReal) (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))
      ≤ ENNReal.ofReal (C * M) *
          ((⨆ n : ℕ, MeasureTheory.eLpNorm (u n) 2
                (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))) +
            (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
              ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
                ENNReal.rpow (MeasureTheory.eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
                  (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))) R) (1 / R))) *
          ((⨆ n : ℕ, MeasureTheory.eLpNorm (v n) 2
                (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))) +
            (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
              ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
                ENNReal.rpow (MeasureTheory.eLpNorm (v (k i.succ) - v (k i.castSucc)) 2
                  (MeasureTheory.Measure.count : MeasureTheory.Measure (ZMod Q))) R) (1 / R))) := by
  obtain ⟨C, hCpos, hC⟩ := bilinearFkrPacketsGen (R := R) (r := r) hR hRr
  refine ⟨C, hCpos, ?_⟩
  intro Q _hQ M hM B hadd₁ hadd₂ u v hB1 hB2
  exact hC (X := ZMod Q) (μ := (Measure.count : MeasureTheory.Measure (ZMod Q)))
    (hmeas := fun f => aestronglyMeasurable_count_zmod Q f) (M := M) (hM := hM) (B := B)
    (hadd₁ := hadd₁) (hadd₂ := hadd₂) (u := u) (v := v) (hB1 := hB1) (hB2 := hB2)

end Work.KMTPlan.A6
