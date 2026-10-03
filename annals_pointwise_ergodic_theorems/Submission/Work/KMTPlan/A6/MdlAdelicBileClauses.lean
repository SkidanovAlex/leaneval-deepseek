/-
# The arithmetic bilinear clauses of the adelic form (`AdelicFormPropRange`), group (B)

This module provides the **arithmetic** part of the adelic form of KMT §8,
`Work.KMTPlan.A6.AdelicFormPropRange` (`MdlAdelicRange.lean`): the paper's Theorem `bile` for the
two packet families, i.e. the clauses

* `hbase` : `‖B(u n X, v n X)‖_{L^r(zmodProb Q)} ≤ M‖u n X‖₂‖v n X‖₂`,
* `hB1`   : the same for `(u m X - u n X, v l X)`,
* `hB2`   : the same for `(u l X, v m X - v n X)`,

with `B = zmodAvg (negReflect P) Q` and the gain constant
`M = Cb · 2^{-(c · max l₁ l₂)}` — exactly the three hypotheses `hbase`/`hB1`/`hB2` of the proved
`ZMod Q` variational chain `Work.KMTPlan.A6.ZModVariationalChainProb : ZModChainPropP`.

The input is the *Ionescu–Wainger minor-arc property* of the packets at their (exact) heights
`l₁` (the `f`-side family `u`) and `l₂` (the `g`-side family `v`) — which is what the packet
construction of §8 produces; it is taken here as a hypothesis, so this module is independent of
the (still in flight) construction of the packets.

The three ingredients are all proved:

* `Work.KMTPlan.A6.MdlBileOfR1Improv` (paper Theorem `bile`, from the contract's `ImprovKMT`):
  `LpNormZMod Q r (polyBilinearAverageZMod X P Q f g) ≤ C 2^{-cl} ‖f‖₂‖g‖₂` whenever one of
  `f, g` is `MdlIwMinorArc ρ l Q`;
* `Work.KMTPlan.A6.ZModAvgNegBridge`:
  `zmodAvg (negReflect P) Q u v = polyBilinearAverageZMod X P Q u v`;
* `zmodProb_eLpNorm_ofReal`: the `ℒ^p`-seminorm against the probability measure `zmodProb Q` is
  the `ofReal` of the probability-normalised `LpNormZMod`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlBileOfR1Improv
import Submission.Work.KMTPlan.A6.ZModAvgNegBridge
import Submission.Work.KMTPlan.A6.MdlAdelicRange

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.Concentration

/-! ## The two elementary bridges -/

/-- **The probability-normalised `ℒ^p`-seminorm on `ZMod Q`.**  Against the probability measure
`zmodProb Q = Q⁻¹ • count` the `eLpNorm` is the `ofReal` of the probability-normalised finite
`LpNormZMod` — the normalisation in which the paper's arithmetic estimates are stated. -/
theorem zmodProb_eLpNorm_ofReal (Q : ℕ) [NeZero Q] {p : ℝ} (hp : 0 < p) (f : ZMod Q → ℂ) :
    eLpNorm f (ENNReal.ofReal p) (zmodProb Q)
      = ENNReal.ofReal (LpNormZMod Q p f) := by
  have hQposR : (0 : ℝ) < (Q : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQtop : (Q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top Q
  rw [zmodProb, eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.mpr hQtop) f
    (ENNReal.ofReal p) (Measure.count : Measure (ZMod Q))]
  have hexp : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofReal hp.le]
  rw [hexp, eLpNorm_count_eq_ofReal Q hp f]
  have hQinv : ((Q : ENNReal)⁻¹) = ENNReal.ofReal ((Q : ℝ)⁻¹) := by
    rw [← ENNReal.ofReal_natCast Q, ← ENNReal.ofReal_inv_of_pos hQposR]
  rw [hQinv, ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hQposR.le)
    (by positivity : (0 : ℝ) ≤ 1 / p)]
  rw [smul_eq_mul, ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr hQposR.le) _)]
  congr 1
  rw [LpNormZMod, ← Real.mul_rpow (inv_nonneg.mpr hQposR.le)
    (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) p)]

/-- **The Ionescu–Wainger minor-arc condition is closed under differences** (the discrete Fourier
transform is additive). -/
theorem MdlIwMinorArc_sub {ρ : ℝ} {l Q : ℕ} [NeZero Q] {f g : ZMod Q → ℂ}
    (hf : MdlIwMinorArc ρ l Q f) (hg : MdlIwMinorArc ρ l Q g) :
    MdlIwMinorArc ρ l Q (f - g) := by
  intro ξ hξ
  have h1 : ZMod.dft (f - g) ξ = ZMod.dft f ξ - ZMod.dft g ξ := by
    rw [map_sub]
    rfl
  rw [h1, hf ξ hξ, hg ξ hξ, sub_zero]

/-! ## The bilinear clauses -/

/-- **The arithmetic bilinear clauses of `AdelicFormPropRange`** (paper Theorem `bile` for the two
packet families).

If both packet families are Ionescu–Wainger minor-arc at a common height `L` (for the §8 packets
this holds at `L = lᵢ - 1`: their `ZMod`-spectrum sits on the *exact*-height level `lᵢ`, so the
discrete Fourier transform vanishes on all frequencies of height `≤ 2^{lᵢ-1}`; see
`NOTES_MdlAdelicFormPlus_countNormalization_FALSE.md` and `MdlAdelicRange.lean`), then the three
bilinear estimates of the adelic form hold for `B = zmodAvg (negReflect P) Q` with the constant
`Cb · 2^{-(c·L)}`.

**How this is consumed.**  `AdelicFormPropRange`'s clause (4) asks for
`ofReal M ≤ (Cin Λ) · ofReal (2^{-(c₀·max l₁ l₂)})` for its *own* rate `c₀`; the prover takes
`M := Cb · 2^{-(c·L)}` here and, when instantiating `L = lᵢ - 1` (so that `L ≥ max l₁ l₂ - 1`),
chooses the outer `c₀ ≤ c` and absorbs the constant factor `2^{c}` into `Cin` (the outer `c₀`, `A`
and `Cin` are all chosen by the prover of `AdelicFormPropRange`).  With this `M` the three clauses
below are *literally* the hypotheses `hbase`/`hB1`/`hB2` of the proved chain
`Work.KMTPlan.A6.ZModVariationalChainProb`. -/
theorem MdlAdelicBileClauses (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P) (r : NNReal) (hr : 2 < r)
    (hrT : (r : ℝ) < adelicRTop P) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Q : ℕ) [NeZero Q] (L : ℕ) (u v : ℕ → ℝ → ZMod Q → ℂ),
        (∀ (n : ℕ) (X : ℝ), MdlIwMinorArc ρ L Q (u n X)) →
        (∀ (n : ℕ) (X : ℝ), MdlIwMinorArc ρ L Q (v n X)) →
        (∀ (X : ℝ) (n : ℕ),
          eLpNorm (fun ρ' : ZMod Q => zmodAvg (negReflect P) Q (u n X) (v n X) ρ')
              (r : ENNReal) (zmodProb Q)
            ≤ ENNReal.ofReal (Cb * (2 : ℝ) ^ (-(c * (L : ℝ))))
              * eLpNorm (u n X) 2 (zmodProb Q) * eLpNorm (v n X) 2 (zmodProb Q)) ∧
        (∀ (X : ℝ) (m n l : ℕ),
          eLpNorm (fun ρ' : ZMod Q => zmodAvg (negReflect P) Q (u m X - u n X) (v l X) ρ')
              (r : ENNReal) (zmodProb Q)
            ≤ ENNReal.ofReal (Cb * (2 : ℝ) ^ (-(c * (L : ℝ))))
              * eLpNorm (u m X - u n X) 2 (zmodProb Q) * eLpNorm (v l X) 2 (zmodProb Q)) ∧
        (∀ (X : ℝ) (m n l : ℕ),
          eLpNorm (fun ρ' : ZMod Q => zmodAvg (negReflect P) Q (u l X) (v m X - v n X) ρ')
              (r : ENNReal) (zmodProb Q)
            ≤ ENNReal.ofReal (Cb * (2 : ℝ) ^ (-(c * (L : ℝ))))
              * eLpNorm (u l X) 2 (zmodProb Q) * eLpNorm (v m X - v n X) 2 (zmodProb Q)) := by
  classical
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.le
  have hrpos : (0 : ℝ) < (r : ℝ) := lt_trans (by norm_num) hr
  have hrT' : (r : ℝ) < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) := hrT
  obtain ⟨c, hc, hb⟩ := MdlBileOfR1Improv P hd hI (r : ℝ) hr2 hrT'
  refine ⟨c, hc, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨C, hC, hbC⟩ := hb ρ hρ hρ1
  refine ⟨C, hC, ?_⟩
  intro Q _ L u v hu hv
  have h2nn : (0 : ℝ) < 2 := by norm_num
  have hLp : ∀ (h : ZMod Q → ℂ), 0 ≤ LpNormZMod Q 2 h := by
    intro h
    rw [LpNormZMod]
    exact Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg Q))
      (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) 2)) _
  -- the single-scale step: Theorem `bile` transported to `zmodAvg` and the probability measure
  have key : ∀ (f g : ZMod Q → ℂ),
      (MdlIwMinorArc ρ L Q f ∨ MdlIwMinorArc ρ L Q g) →
      eLpNorm (fun ρ' : ZMod Q => zmodAvg (negReflect P) Q f g ρ') (r : ENNReal) (zmodProb Q)
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(c * (L : ℝ))))
          * eLpNorm f 2 (zmodProb Q) * eLpNorm g 2 (zmodProb Q) := by
    intro f g h
    have hbase := hbC Q L f g h
    have hrew : (fun ρ' : ZMod Q => zmodAvg (negReflect P) Q f g ρ')
        = polyBilinearAverageZMod Polynomial.X P Q f g := ZModAvgNegBridge P Q f g
    rw [hrew, ← ENNReal.ofReal_coe_nnreal (p := r)]
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) from by norm_num,
      zmodProb_eLpNorm_ofReal Q hrpos,
      zmodProb_eLpNorm_ofReal Q h2nn,
      zmodProb_eLpNorm_ofReal Q h2nn]
    refine le_trans (ENNReal.ofReal_le_ofReal hbase) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (hLp f)),
      ENNReal.ofReal_mul (by positivity)]
  refine ⟨?_, ?_, ?_⟩
  · intro X n
    exact key (u n X) (v n X) (Or.inl (hu n X))
  · intro X m n l
    exact key (u m X - u n X) (v l X) (Or.inl (MdlIwMinorArc_sub (hu m X) (hu n X)))
  · intro X m n l
    exact key (u l X) (v m X - v n X) (Or.inr (MdlIwMinorArc_sub (hv m X) (hv n X)))

end

end Work.KMTPlan.A6
