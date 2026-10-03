/-
# The flat `(p,z)`-sum calculus of the normal form `mdlNF` (area A6)

The operator-level integration-by-parts identities of §6 are proved by writing the *same* object in
two ways as a single absolutely convergent sum over the pair `q = (p, z)` of `(ℤ²) × (ℤ²)`:

  `∑' q, c q.2 * mdlKFG K F G x q.1 q.2`,

with `c : ℤ² → ℂ` the `t`-integral (or the pointwise value) of the product of the two convolution
coefficients `mdlIWKer ρ lᵢ ψ` and `mdlKFG K F G x p z = K (p₁-z₁) (p₂-z₂) F (x-p₁) G (x-p₂)` the
constant attached to the pair `(p,z)`.  This module collects the three rewritings that produce this
form:

* `MdlBtwistFreezeFlat`: at a *fixed* `t`, `Btwist_{m₁⊗m₂}(Tle ψ F, Tle χ G)` is the flat sum with
  the coefficient `c z = κ z₁ κ' z₂` cut by an arbitrary constant `c` (the frozen slice of the
  identity at `t = 1` or `t = 1/2`, multiplied by the weight `W₁`);
* `MdlBtwistIntervalFlat`: the `t`-integral against a weight `w` of the same quantity is the flat
  sum with `c = mdlCoeff w κ κ'` (the `t`-integrated terms of the identity);
* `MdlTsumCombine`: if the coefficients are related pointwise by
  `L = c₁ A - c₁ B - c₂ C + c₁ E`, then the flat sums satisfy the corresponding relation — this is
  the endgame of both identities, which combine five such sums.

The flattened forms are obtained from the already proved normal form `mdlNF`
(`Btwist_Tle_eq_mdlNF`) by the Fubini engine `MdlNFIntegral` and the summability of the flat family
`MdlFlatSummable`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlFlatSummable

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## Linearity of the flat series in the coefficient -/

/-- **Linearity of the flat `(p,z)`-series.**  If the five coefficient families are related
pointwise by `L z = c₁ (A z) - c₁ (B z) - c₂ (C z) + c₁ (E z)` and the five flat families are
summable, then the flat sums satisfy the same relation. -/
theorem MdlTsumCombine (D : (ℤ × ℤ) × (ℤ × ℤ) → ℂ) (A B C E L : ℤ × ℤ → ℂ) (c₁ c₂ : ℂ)
    (hA : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => A q.2 * D q)
    (hB : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => B q.2 * D q)
    (hC : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => C q.2 * D q)
    (hE : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => E q.2 * D q)
    (hL : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) => L q.2 * D q)
    (hcoef : ∀ z : ℤ × ℤ, L z = c₁ * A z - c₁ * B z - c₂ * C z + c₁ * E z) :
    (∑' q : (ℤ × ℤ) × (ℤ × ℤ), L q.2 * D q)
      = c₁ * ((∑' q : (ℤ × ℤ) × (ℤ × ℤ), A q.2 * D q)
          - (∑' q : (ℤ × ℤ) × (ℤ × ℤ), B q.2 * D q))
        - c₂ * (∑' q : (ℤ × ℤ) × (ℤ × ℤ), C q.2 * D q)
        + c₁ * (∑' q : (ℤ × ℤ) × (ℤ × ℤ), E q.2 * D q) := by
  have hAB : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q) :=
    (hA.mul_left c₁).sub (hB.mul_left c₁)
  have hABC : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      (c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q)) - c₂ * (C q.2 * D q) :=
    hAB.sub (hC.mul_left c₂)
  have h1 : (∑' q : (ℤ × ℤ) × (ℤ × ℤ), L q.2 * D q)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          ((c₁ * (A q.2 * D q) - c₁ * (B q.2 * D q)) - c₂ * (C q.2 * D q)
            + c₁ * (E q.2 * D q)) := by
    refine tsum_congr (fun q => ?_)
    rw [hcoef q.2]
    ring
  rw [h1, Summable.tsum_add hABC (hE.mul_left c₁),
    Summable.tsum_sub hAB (hC.mul_left c₂),
    Summable.tsum_sub (hA.mul_left c₁) (hB.mul_left c₁),
    Summable.tsum_mul_left c₁ hA, Summable.tsum_mul_left c₁ hB,
    Summable.tsum_mul_left c₂ hC, Summable.tsum_mul_left c₁ hE]
  ring

/-! ## The frozen slice of the identity -/

/-- **The frozen slice of `Btwist` on two `Tle`-images, in flat `(p,z)`-form.**  At a fixed `t` the
product `Tle ρ l₁ Φ F ⊗ Tle ρ l₂ Ψ G` under `Btwist` is the flat sum over `q = (p,z)` of the
coefficient `κ z₁ κ' z₂` (the product of the two convolution kernels) times the constant
`mdlKFG K F G x p z`; multiplying by a constant `c` (the weight `W₁(t)`) is absorbed into the
coefficient. -/
theorem MdlBtwistFreezeFlat (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ) (Φ Ψ : ℝ → ℂ) (F G : ℤ → ℂ) {CF CG : ℝ} (c : ℂ)
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hK : Summable fun p : ℤ × ℤ => ‖mdlBtwK ρ P l₁ l₂ m₁ m₂ p.1 p.2‖)
    (hκ : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ Φ i‖)
    (hκ' : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ Ψ i‖) (x : ℤ) :
    c * (Btwist ρ P l₁ l₂ m₁ m₂ (Tle ρ l₁ Φ F) (Tle ρ l₂ Ψ G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          (c * (mdlIWKer ρ l₁ Φ q.2.1 * mdlIWKer ρ l₂ Ψ q.2.2))
            * mdlKFG (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 := by
  have hS : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      (mdlIWKer ρ l₁ Φ q.2.1 * mdlIWKer ρ l₂ Ψ q.2.2)
        * mdlKFG (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 :=
    MdlFlatSummable (K := mdlBtwK ρ P l₁ l₂ m₁ m₂) hF hG hK
      (c := fun z : ℤ × ℤ => mdlIWKer ρ l₁ Φ z.1 * mdlIWKer ρ l₂ Ψ z.2)
      (a := fun i : ℤ => ‖mdlIWKer ρ l₁ Φ i‖)
      (a' := fun i : ℤ => ‖mdlIWKer ρ l₂ Ψ i‖)
      hκ hκ' (fun i => norm_nonneg _) (fun i => norm_nonneg _) (Ca := 1) zero_le_one
      (fun z => by rw [norm_mul, one_mul]) x
  have hmain : Btwist ρ P l₁ l₂ m₁ m₂ (Tle ρ l₁ Φ F) (Tle ρ l₂ Ψ G) x
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          (mdlIWKer ρ l₁ Φ q.2.1 * mdlIWKer ρ l₂ Ψ q.2.2)
            * mdlKFG (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 := by
    rw [Btwist_Tle_eq_mdlNF ρ P l₁ l₂ m₁ m₂ Φ Ψ F G hF hG hK hκ hκ' x]
    exact mdlNF_eq_tsum_prod hF hG hK hκ hκ' x
  rw [hmain]
  have hcongr : (∑' q : (ℤ × ℤ) × (ℤ × ℤ),
        (c * (mdlIWKer ρ l₁ Φ q.2.1 * mdlIWKer ρ l₂ Ψ q.2.2))
          * mdlKFG (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          c * ((mdlIWKer ρ l₁ Φ q.2.1 * mdlIWKer ρ l₂ Ψ q.2.2)
            * mdlKFG (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2) :=
    tsum_congr (fun q => by ring)
  rw [hcongr, Summable.tsum_mul_left c hS]

/-! ## The `t`-integrated slices of the identity -/

/-- **The `t`-integral of the weighted slices, in flat `(p,z)`-form.**  The interval integral over
`(1/2,1]` of `w t · Btwist (Tle (Φ t) F) (Tle (Ψ t) G) x` is the flat sum whose coefficient
`mdlCoeff w κ κ' z` is the `t`-integral of the product of the two convolution kernels. -/
theorem MdlBtwistIntervalFlat (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (m₁ m₂ : ℝ → ℂ) (Φ Ψ : ℝ → ℝ → ℂ) (w : ℝ → ℂ) (F G : ℤ → ℂ) {CF CG Cw : ℝ}
    (hF : ∀ y : ℤ, ‖F y‖ ≤ CF) (hG : ∀ y : ℤ, ‖G y‖ ≤ CG)
    (hw : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ‖w t‖ ≤ Cw)
    (hwm : MeasureTheory.AEStronglyMeasurable w MeasureTheory.volume)
    (a a' : ℤ → ℝ) (ha : Summable a) (ha' : Summable a')
    (hb : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖mdlIWKer ρ l₁ (Φ t) i‖ ≤ a i)
    (hb' : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ i : ℤ, ‖mdlIWKer ρ l₂ (Ψ t) i‖ ≤ a' i)
    (hm : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₁ (Φ t) i) MeasureTheory.volume)
    (hm' : ∀ i : ℤ, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => mdlIWKer ρ l₂ (Ψ t) i) MeasureTheory.volume)
    (hK : Summable fun p : ℤ × ℤ => ‖mdlBtwK ρ P l₁ l₂ m₁ m₂ p.1 p.2‖) (x : ℤ) :
    (∫ t in (1/2 : ℝ)..1,
        w t * Btwist ρ P l₁ l₂ m₁ m₂ (Tle ρ l₁ (Φ t) F) (Tle ρ l₂ (Ψ t) G) x)
      = ∑' q : (ℤ × ℤ) × (ℤ × ℤ),
          mdlCoeff w (fun t i => mdlIWKer ρ l₁ (Φ t) i) (fun t i => mdlIWKer ρ l₂ (Ψ t) i) q.2
            * mdlKFG (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 := by
  have hI : (1/2 : ℝ) ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hCw : 0 ≤ Cw := le_trans (norm_nonneg _) (hw (1/2) hI)
  have ha0 : ∀ i : ℤ, 0 ≤ a i := fun i => le_trans (norm_nonneg _) (hb (1/2) hI i)
  have ha0' : ∀ i : ℤ, 0 ≤ a' i := fun i => le_trans (norm_nonneg _) (hb' (1/2) hI i)
  have hS : Summable fun q : (ℤ × ℤ) × (ℤ × ℤ) =>
      mdlCoeff w (fun t i => mdlIWKer ρ l₁ (Φ t) i) (fun t i => mdlIWKer ρ l₂ (Ψ t) i) q.2
        * mdlKFG (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G x q.1 q.2 :=
    MdlFlatSummable (K := mdlBtwK ρ P l₁ l₂ m₁ m₂) hF hG hK
      (c := mdlCoeff w (fun t i => mdlIWKer ρ l₁ (Φ t) i)
        (fun t i => mdlIWKer ρ l₂ (Ψ t) i))
      ha ha' ha0 ha0' hCw
      (fun z => mdl_coeff_intervalIntegral_bound hw hCw ha0 ha0' hb hb' z) x
  have hpt : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      Btwist ρ P l₁ l₂ m₁ m₂ (Tle ρ l₁ (Φ t) F) (Tle ρ l₂ (Ψ t) G) x
        = mdlNF (mdlBtwK ρ P l₁ l₂ m₁ m₂) (fun i => mdlIWKer ρ l₁ (Φ t) i)
            (fun i => mdlIWKer ρ l₂ (Ψ t) i) F G x := by
    intro t ht
    have hs : Summable fun i : ℤ => ‖mdlIWKer ρ l₁ (Φ t) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb t ht i) ha
    have hs' : Summable fun i : ℤ => ‖mdlIWKer ρ l₂ (Ψ t) i‖ :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hb' t ht i) ha'
    exact Btwist_Tle_eq_mdlNF ρ P l₁ l₂ m₁ m₂ (Φ t) (Ψ t) F G hF hG hK hs hs' x
  have hstep : (∫ t in (1/2 : ℝ)..1, w t * Btwist ρ P l₁ l₂ m₁ m₂
        (Tle ρ l₁ (Φ t) F) (Tle ρ l₂ (Ψ t) G) x)
      = ∫ t in (1/2 : ℝ)..1, w t * mdlNF (mdlBtwK ρ P l₁ l₂ m₁ m₂)
          (fun i => mdlIWKer ρ l₁ (Φ t) i) (fun i => mdlIWKer ρ l₂ (Ψ t) i) F G x := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    rw [hpt t ht]
  rw [hstep, MdlNFIntegral (mdlBtwK ρ P l₁ l₂ m₁ m₂) F G hF hG hK w hw hwm
    (fun t i => mdlIWKer ρ l₁ (Φ t) i) (fun t i => mdlIWKer ρ l₂ (Ψ t) i) a a' ha ha'
    hb hb' hm hm' x]
  rw [hS.tsum_prod]
  refine tsum_congr (fun p => tsum_congr (fun z => ?_))
  simp only [mdlCoeff, mdlKFG]

end

end Work.KMTPlan.A6
