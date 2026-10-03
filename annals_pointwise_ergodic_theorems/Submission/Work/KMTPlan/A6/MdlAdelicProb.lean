/-
# The §8 chain and the adelic data in the *probability* normalization

Krause--Mirek--Tao's §8 chain (Annals **195** (2022)) is stated on the adelic integers `Ẑ`
**with the probability Haar measure** (`L²(Ẑ)`, `L^r(Ẑ)`, `L¹(Ẑ; V^r)`, `V^R(ℤ; L²(Ẑ))`).  In the
finite model `ZMod Q` this is the measure `zmodProb Q = Q⁻¹ • count`, *not* the counting measure:
the two differ by a factor `Q^{1/2}` per `L²`-norm, i.e. by `Q` in a product of two data terms.

This distinction is not cosmetic, and it is the reason this module exists.  The paper's linear
input (the vector-valued `(lin-1)`/`(lin-2)`) bounds `‖F̅‖_{L²(ℝ; L²(Ẑ))}` by
`lossWeight · ‖f‖_{ℓ²}`, i.e. the **normalized** datum: the adelic constants `Ku, Kv` of the chain
are the normalized ones, and the paper's arithmetic bilinear estimate (Theorem `bile`) is the
**normalized** `L²(Ẑ) × L²(Ẑ) → L^r(Ẑ)` bound with the gain `2^{-c l}`.  (The paper even warns:
"one needs to check that none of the bounds lose any factor of `Q` (or even `log Q`) as this would
be fatal to the argument".)

Accordingly this module fixes the vocabulary used by the §8 reduction of
`Work.KMTPlan.A6.MdlSliceCoreGainMemLp`:

* `zmodProb Q` — the probability Haar measure on `ZMod Q` (`Q ≥ 1`);
* `VrLiftDataP R Q u` — the `V^R(ℤ; L²(ZMod Q, zmodProb Q))`-datum of a packet family
  (`L²` against the *probability* measure);
* `ZModChainPropP` — the §8 chain with all norms normalized: Hölder on the *probability* space
  `ZMod Q` (`L¹ ≤ L^r`), the paper's Corollary `bilinear-fkr` (the tree's `fkrInterchangeGenAll`,
  plus the sup-part handled by `sup_n |b_n| ≤ |b_0| + V^1 ≤ |b_0| + V^r`), the Lipschitz
  decomposition of `B` (additivity only), and Cauchy--Schwarz in the real variable.

`ZModChainPropP` is `Work.KMTPlan.A6.ZModChainProp` (`MdlAdelicDefs.lean`) with `Measure.count`
replaced by `zmodProb Q` in every norm; the counting-measure form is *weaker* than the needed one
(by `Q^{1/r}`), which is why the reduction has to go through the present form.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs
import Submission.Work.Analysis.Variation.fkrInterchangeGenAll

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-- **The probability Haar measure on `ZMod Q`**: the counting measure normalized to total mass
`1`.  This is the measure in which the paper's §8 (and its linear and bilinear inputs) is
stated. -/
noncomputable def zmodProb (Q : ℕ) : Measure (ZMod Q) :=
  (Q : ENNReal)⁻¹ • (Measure.count : Measure (ZMod Q))

/-- The total mass of `zmodProb Q` is `1` for `Q ≠ 0`: it is a probability measure.  (Recorded
here for reference; the proof is `Measure.smul_apply` + `Measure.count_univ` + `ZMod.card`.) -/
lemma zmodProb_univ {Q : ℕ} [NeZero Q] : zmodProb Q Set.univ = 1 := by
  rw [zmodProb, Measure.smul_apply, MeasureTheory.Measure.count_univ,
    ENat.card_eq_coe_fintype_card, ZMod.card]
  have h0 : (Q : ENNReal) ≠ 0 := by
    have hQ : Q ≠ 0 := NeZero.ne Q
    intro h
    exact hQ (Nat.cast_eq_zero.mp (by simpa using h : ((Q : ℕ) : ENNReal) = 0))
  exact ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top Q)

/-- **The packet data of the frozen slice, in the probability normalization of the paper.**

`VrLiftDataP R Q u` is the `V^R(ℤ; L²(ZMod Q))`-datum of a packet family `u`, all `L²`-norms
being taken against the probability measure `zmodProb Q` — the normalization in which the paper's
linear estimate `(lin-1)`/`(lin-2)` bounds it by `lossWeight A ρ l₁ l₂ k₁ k₂ · ‖f‖₂`. -/
noncomputable def VrLiftDataP (R : ℝ) (Q : ℕ) (u : ℕ → ZMod Q → ℂ) : ℝ≥0∞ :=
  (⨆ n : ℕ, eLpNorm (u n) 2 (zmodProb Q)) +
    (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2 (zmodProb Q)) R) (1 / R))

/-- **The `ZMod Q` variational chain of §8, in the probability normalization.**

For `1 ≤ R < r` there is `Cd > 0` such that for every modulus `Q ≥ 1`, every bilinear form `B` that
is *additive* in each variable, every pair of packet families `u, v : ℕ → ℝ → ZMod Q → ℂ` with

* the arithmetic bilinear estimates at exponent `r` (`hbase`, `hB1`, `hB2`) with constant `M`
  (the paper's Theorem `bile`, in the normalized `L²(ZMod Q) × L²(ZMod Q) → L^r(ZMod Q)` form:
  for the model's packets `M ≲ 2^{-c·l}`),
* the packet data bounds `∫ (VrLiftDataP R Q (u · X))² ≤ Ku²` (resp. `Kv²`) (the paper's
  `(lin-1)`/`(lin-2)` in the normalized form, with `Ku ≲ lossWeight·‖f‖₂`),

one has, with `zmodProb Q` the probability measure on `ZMod Q`,

`∫_ℝ ∫_{ZMod Q} V^r (B(u_n(X), v_n(X)))_n  dμ  dX ≤ Cd · M · Ku · Kv`.

The proof is the chain of §8 after `form-2`: Hölder on the probability space `ZMod Q`
(`L¹ ≤ L^r`), the paper's Corollary `bilinear-fkr` (`Work.Analysis.Variation.fkrInterchangeGenAll`
— the `L^r`-interchange of variational and Lebesgue norms, applied to the `varPart`, with the
`sup_n`-part handled by `sup_n |b_n| ≤ |b_0| + V¹ ≤ |b_0| + V^r`), together with the additivity
decomposition `B(u n,v n) - B(u m,v m) = B(u n - u m, v n) + B(u m, v n - v m)`, and
Cauchy--Schwarz in the real variable. -/
def ZModChainPropP : Prop :=
  ∀ {r : NNReal} (hr : 1 ≤ r) {R : ℝ} (hR : 1 ≤ R) (hRr : R < (r : ℝ)),
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ {Q : ℕ} (hQ : 1 ≤ Q) {M Ku Kv : ℝ} (hM : 0 ≤ M) (hKu : 0 ≤ Ku) (hKv : 0 ≤ Kv)
      {B : (ZMod Q → ℂ) → (ZMod Q → ℂ) → (ZMod Q → ℂ)}
      (hadd₁ : ∀ e e' f : ZMod Q → ℂ, B (e + e') f = B e f + B e' f)
      (hadd₂ : ∀ e f f' : ZMod Q → ℂ, B e (f + f') = B e f + B e f')
      {u v : ℕ → ℝ → ZMod Q → ℂ}
      (humeas : ∀ (n : ℕ) (θ : ZMod Q), AEMeasurable (fun X : ℝ => u n X θ))
      (hvmeas : ∀ (n : ℕ) (θ : ZMod Q), AEMeasurable (fun X : ℝ => v n X θ))
      (hbase : ∀ (X : ℝ) (n : ℕ),
        eLpNorm (fun ρ : ZMod Q => B (u n X) (v n X) ρ) (r : ENNReal) (zmodProb Q)
          ≤ ENNReal.ofReal M * eLpNorm (u n X) 2 (zmodProb Q)
              * eLpNorm (v n X) 2 (zmodProb Q))
      (hB1 : ∀ (X : ℝ) (m n l : ℕ),
        eLpNorm (fun ρ : ZMod Q => B (u m X - u n X) (v l X) ρ) (r : ENNReal) (zmodProb Q)
          ≤ ENNReal.ofReal M * eLpNorm (u m X - u n X) 2 (zmodProb Q)
              * eLpNorm (v l X) 2 (zmodProb Q))
      (hB2 : ∀ (X : ℝ) (m n l : ℕ),
        eLpNorm (fun ρ : ZMod Q => B (u l X) (v m X - v n X) ρ) (r : ENNReal) (zmodProb Q)
          ≤ ENNReal.ofReal M * eLpNorm (u l X) 2 (zmodProb Q)
              * eLpNorm (v m X - v n X) 2 (zmodProb Q))
      (hSu : ∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => u n X)) ^ (2 : ℕ)
          ≤ ENNReal.ofReal (Ku ^ 2))
      (hSv : ∫⁻ X : ℝ, (VrLiftDataP R Q (fun n : ℕ => v n X)) ^ (2 : ℕ)
          ≤ ENNReal.ofReal (Kv ^ 2)),
      ∫⁻ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q,
          variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
        ≤ ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv

end

end Work.KMTPlan.A6
