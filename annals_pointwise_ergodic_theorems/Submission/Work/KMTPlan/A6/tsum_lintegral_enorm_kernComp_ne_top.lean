/-
# `∑'`-finiteness of the `L¹`-masses of the composed kernel family

For a bilinear kernel `K : ℤ → ℤ → ℂ` and two *time-dependent* linear kernels
`κ κ' : ℝ → ℤ → ℂ` whose `ℓ¹`-masses are bounded on `Ioc (1/2) 1` by `B1`, `B2`, the composed
kernel `kernComp K (κ t) (κ' t)` (`Work.KMTAreas.A7.kernComp`) has a summable `ℓ¹`-mass, uniformly
in `t ∈ Ioc (1/2) 1`.  This file proves the measure-theoretic form of that statement: the
**`∑'`-sum over the two space variables `p : ℤ × ℤ` of the level-wise (in `t`) `L¹(ℝ)`-seminorms
is finite**, i.e. the family of `L¹`-masses is summable in the first argument.

The estimate is the `ℝ≥0∞`-valued Fubini/Fatou argument for the fourfold convolution:

* the *dominating* double series of `‖kernComp K (κ t) (κ' t) p.1 p.2‖ₑ`,
  `B p t = ∑'_z ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ)`,
  is a.e. measurable in `t` (it is a sum over `ℤ × ℤ` of constant multiples of products of
  a.e. measurable functions), and it dominates `‖kernComp …‖ₑ` pointwise
  (`enorm_tsum_le_tsum_enorm`, twice);
* summing `B p t` over `p` and reindexing by the bijection `(p, z) ↦ (p - z, z)` of `(ℤ²)²`
  factorises the double sum: `∑'_p ∑'_z a (p - z) b z = (∑' a) (∑' b)` for `ℝ≥0∞`-valued `a, b`
  (`tsum_tsum_sub_mul` below — no summability is needed precisely because the series take values
  in `ℝ≥0∞`);
* hence, for `t ∈ Ioc (1/2) 1`, `∑'_p B p t ≤ B_K * (B_1 * B_2)`, using `hKb`, `hκb`, `hκb'` and
  `ENNReal.ofReal_tsum_of_nonneg`;
* `lintegral_tsum` (measurability of each `B p`) turns `∑'_p ∫⁻_t … ‖kernComp …‖ₑ` into
  `∫⁻_t ∑'_p B p t`, and `lintegral_mono_ae` (which needs no measurability of the smaller
  integrand) bounds the latter by `(B_K B_1 B_2) * volume (Ioc (1/2) 1) < ⊤`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.tsum_norm_kernComp_le
import Submission.Work.KMTPlan.A6Aux.enorm_kernComp_le_tsum
import Submission.Work.KMTPlan.A6Aux.aemeasurable_tsum_enorm_kernDom

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory

/-- The `ℝ≥0∞`-valued "sum over the group of a convolution factorises" identity: for
`a, b : ℤ × ℤ → ℝ≥0∞`,

  `∑'_p ∑'_z a (p - z) * b z = (∑'_r a r) * (∑'_z b z)`.

No summability hypothesis is needed: every `ℝ≥0∞`-series has a value, and the identity is the
reindexing `(p, z) ↦ (p - z, z)` of `(ℤ²)²` (`Work.A7.ModelApproxCore_aux.kernCompSubEquiv`)
followed by Fubini and the factorisation of a product of two independent series
(`ENNReal.tsum_prod`, `ENNReal.tsum_mul_left`, `ENNReal.tsum_mul_right`). -/
theorem tsum_tsum_sub_mul (a b : ℤ × ℤ → ENNReal) :
    (∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ, a (p - z) * b z)
      = (∑' r : ℤ × ℤ, a r) * (∑' z : ℤ × ℤ, b z) := by
  have h : (∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ, a (p - z) * b z)
      = ∑' w : (ℤ × ℤ) × (ℤ × ℤ), a w.1 * b w.2 := by
    rw [← ENNReal.tsum_prod (f := fun p z : ℤ × ℤ => a (p - z) * b z)]
    exact Equiv.tsum_eq Work.A7.ModelApproxCore_aux.kernCompSubEquiv
      (fun w : (ℤ × ℤ) × (ℤ × ℤ) => a w.1 * b w.2)
  rw [h, ENNReal.tsum_prod (f := fun r z : ℤ × ℤ => a r * b z)]
  rw [tsum_congr (fun r : ℤ × ℤ => ENNReal.tsum_mul_left (a := a r)
    (f := fun z : ℤ × ℤ => b z))]
  rw [ENNReal.tsum_mul_right]

/-- The `ℝ≥0∞`-valued "product of two independent series" identity on `ℤ × ℤ`:
`∑'_{z : ℤ × ℤ} c z.1 * d z.2 = (∑' c) * (∑' d)`. -/
theorem tsum_fst_mul_snd (c d : ℤ → ENNReal) :
    (∑' z : ℤ × ℤ, c z.1 * d z.2) = (∑' j : ℤ, c j) * (∑' j : ℤ, d j) := by
  rw [ENNReal.tsum_prod (f := fun i j : ℤ => c i * d j)]
  rw [tsum_congr (fun i : ℤ => ENNReal.tsum_mul_left (a := c i) (f := d))]
  rw [ENNReal.tsum_mul_right]

theorem tsum_lintegral_enorm_kernComp_ne_top (K : ℤ → ℤ → ℂ) (κ κ' : ℝ → ℤ → ℂ)
    (BK B1 B2 : ℝ)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖)
    (hKb : (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) ≤ BK)
    (hκ : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable fun j : ℤ => ‖κ t j‖)
    (hκ' : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable fun j : ℤ => ‖κ' t j‖)
    (hκb : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, (∑' j : ℤ, ‖κ t j‖) ≤ B1)
    (hκb' : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, (∑' j : ℤ, ‖κ' t j‖) ≤ B2)
    (hBK : 0 ≤ BK) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hmκ : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ t j) volume)
    (hmκ' : ∀ j : ℤ, AEMeasurable (fun t : ℝ => κ' t j) volume) :
    (∑' p : ℤ × ℤ, ∫⁻ t, ‖Work.KMTAreas.A7.kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
      ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) ≠ ⊤ := by
  classical
  -- The a.e. statement that `t` lies in the interval.
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)), t ∈ Set.Ioc (1 / 2 : ℝ) 1 :=
    MeasureTheory.self_mem_ae_restrict measurableSet_Ioc
  -- Pointwise (in `t`) domination of `‖kernComp …‖ₑ` by the double series `B p t`.
  have hFB : ∀ p : ℤ × ℤ, ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      ‖Work.KMTAreas.A7.kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
        ≤ ∑' z : ℤ × ℤ, ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ) :=
    fun p => Filter.Eventually.of_forall fun t =>
      Work.KMTPlan.A6Aux.enorm_kernComp_le_tsum (K := K) (κ := κ t) (κ' := κ' t) p.1 p.2
  -- A.e. measurability of the dominating series.
  have hBmeas : ∀ p : ℤ × ℤ, AEMeasurable (fun t : ℝ =>
      ∑' z : ℤ × ℤ, ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ))
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
    fun p => (Work.KMTPlan.A6Aux.aemeasurable_tsum_enorm_kernDom (ν := volume) hmκ hmκ' p).mono_measure
      Measure.restrict_le_self
  -- The uniform bound on the dominating series.
  have hBbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      (∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
          ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ))
        ≤ ENNReal.ofReal (BK * B1 * B2) := by
    refine hae.mono fun t ht => ?_
    -- Turning the `ℝ≥0∞`-sums of norms into `ofReal` of the corresponding `ℝ`-sums.
    have hKsum : (∑' r : ℤ × ℤ, ‖K r.1 r.2‖ₑ) = ENNReal.ofReal (∑' r : ℤ × ℤ, ‖K r.1 r.2‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun r => norm_nonneg _) hK]
      simp
    have hκsum : (∑' j : ℤ, ‖κ t j‖ₑ) = ENNReal.ofReal (∑' j : ℤ, ‖κ t j‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) (hκ t ht)]
      simp
    have hκ'sum : (∑' j : ℤ, ‖κ' t j‖ₑ) = ENNReal.ofReal (∑' j : ℤ, ‖κ' t j‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) (hκ' t ht)]
      simp
    have hz : (∑' z : ℤ × ℤ, ‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ)
        = (∑' j : ℤ, ‖κ t j‖ₑ) * (∑' j : ℤ, ‖κ' t j‖ₑ) := tsum_fst_mul_snd (fun j : ℤ => ‖κ t j‖ₑ) (fun j : ℤ => ‖κ' t j‖ₑ)
    calc (∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
            ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ))
        = (∑' r : ℤ × ℤ, ‖K r.1 r.2‖ₑ)
            * (∑' z : ℤ × ℤ, ‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ) :=
          tsum_tsum_sub_mul (fun r : ℤ × ℤ => ‖K r.1 r.2‖ₑ)
            (fun z : ℤ × ℤ => ‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ)
      _ = ENNReal.ofReal (∑' r : ℤ × ℤ, ‖K r.1 r.2‖)
            * (ENNReal.ofReal (∑' j : ℤ, ‖κ t j‖)
              * ENNReal.ofReal (∑' j : ℤ, ‖κ' t j‖)) := by
          rw [hz, hKsum, hκsum, hκ'sum]
      _ ≤ ENNReal.ofReal BK * (ENNReal.ofReal B1 * ENNReal.ofReal B2) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hKb)
            (mul_le_mul' (ENNReal.ofReal_le_ofReal (hκb t ht))
              (ENNReal.ofReal_le_ofReal (hκb' t ht)))
      _ = ENNReal.ofReal (BK * B1 * B2) := by
          rw [← ENNReal.ofReal_mul hB1, ← ENNReal.ofReal_mul hBK]
          congr 1
          ring
  -- The finiteness of the reference integral.
  have htop : ENNReal.ofReal (BK * B1 * B2) * (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) Set.univ
      < ⊤ := by
    rw [Measure.restrict_apply (μ := volume) (s := Set.Ioc (1 / 2 : ℝ) 1)
      (t := Set.univ) MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.mul_lt_top_iff.mpr
      (Or.inl ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
  have hmain : (∑' p : ℤ × ℤ, ∫⁻ t,
        ‖Work.KMTAreas.A7.kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
      ≤ ENNReal.ofReal (BK * B1 * B2) * (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) Set.univ := by
    calc (∑' p : ℤ × ℤ, ∫⁻ t,
          ‖Work.KMTAreas.A7.kernComp K (κ t) (κ' t) p.1 p.2‖ₑ
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        ≤ ∑' p : ℤ × ℤ, ∫⁻ t,
            (∑' z : ℤ × ℤ,
              ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ))
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
          ENNReal.tsum_le_tsum fun p => lintegral_mono_ae (hFB p)
      _ = ∫⁻ t, (∑' p : ℤ × ℤ, ∑' z : ℤ × ℤ,
              ‖K (p.1 - z.1) (p.2 - z.2)‖ₑ * (‖κ t z.1‖ₑ * ‖κ' t z.2‖ₑ))
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
          (lintegral_tsum hBmeas).symm
      _ ≤ ∫⁻ _t, ENNReal.ofReal (BK * B1 * B2)
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
          lintegral_mono_ae hBbound
      _ = ENNReal.ofReal (BK * B1 * B2)
            * (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) Set.univ :=
          lintegral_const _
  exact ne_of_lt (lt_of_le_of_lt hmain htop)

end Work.KMTPlan.A6
