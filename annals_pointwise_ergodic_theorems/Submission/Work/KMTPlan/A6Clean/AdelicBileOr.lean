/-
# The arithmetic bilinear clauses of the adelic form with a *one-sided* minor-arc hypothesis

`Work.KMTPlan.A6.MdlAdelicBileClauses` (`A6/MdlAdelicBileClauses.lean`) proves the three packet
bilinear estimates of the §8 adelic form (paper Theorem `bile`) under the hypothesis that **both**
packet families are Ionescu–Wainger minor arc at a common height `L`:

  `∀ n X, MdlIwMinorArc ρ L Q (u n X)` and `∀ n X, MdlIwMinorArc ρ L Q (v n X)`.

For the packets that actually occur the two families sit at *different* exact heights `l₁ ≠ l₂`
(the `f`-side family at exact height `l₁`, the `g`-side family at exact height `l₂`), so with
`L = max l₁ l₂ − 1` only the family at the *larger* height is minor arc; the other one has its
`ZMod Q`-spectrum inside the low frequencies of height `≤ L`.  The theorem below is the form the
§8 assembly needs: the hypothesis is the *disjunction*

  `(∀ n X, MdlIwMinorArc ρ L Q (u n X)) ∨ (∀ n X, MdlIwMinorArc ρ L Q (v n X))`.

This is legitimate because the arithmetic input `Work.KMTPlan.A6.MdlBileOfR1Improv` (the paper's
Theorem `bile`, from the contract's `ImprovKMT`) requires only that *one* of the two factors be
minor arc, and because the minor-arc condition is closed under differences
(`Work.KMTPlan.A6.MdlIwMinorArc_sub`) — so the same side works for the incremental clauses
`hB1` (`u m − u n` against `v l`) and `hB2` (`u l` against `v m − v n`).

Everything else is verbatim the proof of `MdlAdelicBileClauses`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicBileClauses

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6Clean

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.Concentration

/-- **The arithmetic bilinear clauses of the adelic form, with a one-sided minor-arc
hypothesis.**  Same conclusion as `Work.KMTPlan.A6.MdlAdelicBileClauses` (the three estimates
`hbase`, `hB1`, `hB2` with the gain `Cb · 2^{-(c·L)}`), but the hypothesis on the two packet
families is the disjunction "all `u`'s are minor arc at height `L`, or all `v`'s are". -/
theorem MdlAdelicBileClausesOr (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P) (r : NNReal) (hr : 2 < r)
    (hrT : (r : ℝ) < Work.KMTPlan.A6.adelicRTop P) :
    ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ Cb : ℝ, 0 < Cb ∧
      ∀ (Q : ℕ) [NeZero Q] (L : ℕ) (u v : ℕ → ℝ → ZMod Q → ℂ),
        ((∀ (n : ℕ) (X : ℝ), Work.KMTPlan.A6.MdlIwMinorArc ρ L Q (u n X)) ∨
          (∀ (n : ℕ) (X : ℝ), Work.KMTPlan.A6.MdlIwMinorArc ρ L Q (v n X))) →
        (∀ (X : ℝ) (n : ℕ),
          eLpNorm (fun ρ' : ZMod Q => Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q
              (u n X) (v n X) ρ')
              (r : ENNReal) (Work.KMTPlan.A6.zmodProb Q)
            ≤ ENNReal.ofReal (Cb * (2 : ℝ) ^ (-(c * (L : ℝ))))
              * eLpNorm (u n X) 2 (Work.KMTPlan.A6.zmodProb Q)
              * eLpNorm (v n X) 2 (Work.KMTPlan.A6.zmodProb Q)) ∧
        (∀ (X : ℝ) (m n l : ℕ),
          eLpNorm (fun ρ' : ZMod Q => Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q
              (u m X - u n X) (v l X) ρ')
              (r : ENNReal) (Work.KMTPlan.A6.zmodProb Q)
            ≤ ENNReal.ofReal (Cb * (2 : ℝ) ^ (-(c * (L : ℝ))))
              * eLpNorm (u m X - u n X) 2 (Work.KMTPlan.A6.zmodProb Q)
              * eLpNorm (v l X) 2 (Work.KMTPlan.A6.zmodProb Q)) ∧
        (∀ (X : ℝ) (m n l : ℕ),
          eLpNorm (fun ρ' : ZMod Q => Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q
              (u l X) (v m X - v n X) ρ')
              (r : ENNReal) (Work.KMTPlan.A6.zmodProb Q)
            ≤ ENNReal.ofReal (Cb * (2 : ℝ) ^ (-(c * (L : ℝ))))
              * eLpNorm (u l X) 2 (Work.KMTPlan.A6.zmodProb Q)
              * eLpNorm (v m X - v n X) 2 (Work.KMTPlan.A6.zmodProb Q)) := by
  classical
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.le
  have hrpos : (0 : ℝ) < (r : ℝ) := lt_trans (by norm_num) hr
  have hrT' : (r : ℝ) < 2 * (P.natDegree : ℝ) / ((P.natDegree : ℝ) - 1) := hrT
  obtain ⟨c, hc, hb⟩ := Work.KMTPlan.A6.MdlBileOfR1Improv P hd hI (r : ℝ) hr2 hrT'
  refine ⟨c, hc, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨C, hC, hbC⟩ := hb ρ hρ hρ1
  refine ⟨C, hC, ?_⟩
  intro Q _ L u v huv
  have h2nn : (0 : ℝ) < 2 := by norm_num
  have hLp : ∀ (h : ZMod Q → ℂ), 0 ≤ LpNormZMod Q 2 h := by
    intro h
    rw [LpNormZMod]
    exact Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg Q))
      (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (norm_nonneg _) 2)) _
  -- the single-scale step: Theorem `bile` transported to `zmodAvg` and the probability measure
  have key : ∀ (f g : ZMod Q → ℂ),
      (Work.KMTPlan.A6.MdlIwMinorArc ρ L Q f ∨ Work.KMTPlan.A6.MdlIwMinorArc ρ L Q g) →
      eLpNorm (fun ρ' : ZMod Q => Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q f g ρ')
          (r : ENNReal) (Work.KMTPlan.A6.zmodProb Q)
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(c * (L : ℝ))))
          * eLpNorm f 2 (Work.KMTPlan.A6.zmodProb Q) * eLpNorm g 2 (Work.KMTPlan.A6.zmodProb Q) := by
    intro f g h
    have hbase := hbC Q L f g h
    have hrew : (fun ρ' : ZMod Q => Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q f g ρ')
        = polyBilinearAverageZMod Polynomial.X P Q f g :=
      Work.KMTPlan.A6.ZModAvgNegBridge P Q f g
    rw [hrew, ← ENNReal.ofReal_coe_nnreal (p := r)]
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) from by norm_num,
      Work.KMTPlan.A6.zmodProb_eLpNorm_ofReal Q hrpos,
      Work.KMTPlan.A6.zmodProb_eLpNorm_ofReal Q h2nn,
      Work.KMTPlan.A6.zmodProb_eLpNorm_ofReal Q h2nn]
    refine le_trans (ENNReal.ofReal_le_ofReal hbase) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (hLp f)),
      ENNReal.ofReal_mul (by positivity)]
  rcases huv with hu | hv
  · exact ⟨fun X n => key (u n X) (v n X) (Or.inl (hu n X)),
      fun X m n l => key (u m X - u n X) (v l X)
        (Or.inl (Work.KMTPlan.A6.MdlIwMinorArc_sub (hu m X) (hu n X))),
      fun X m n l => key (u l X) (v m X - v n X) (Or.inl (hu l X))⟩
  · exact ⟨fun X n => key (u n X) (v n X) (Or.inr (hv n X)),
      fun X m n l => key (u m X - u n X) (v l X) (Or.inr (hv l X)),
      fun X m n l => key (u l X) (v m X - v n X)
        (Or.inr (Work.KMTPlan.A6.MdlIwMinorArc_sub (hv m X) (hv n X)))⟩

end

end Work.KMTPlan.A6Clean
