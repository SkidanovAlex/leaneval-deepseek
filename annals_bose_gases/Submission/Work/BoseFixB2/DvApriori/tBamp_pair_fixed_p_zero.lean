import Mathlib
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 400000

namespace Work.BoseFixB2.DvApriori

noncomputable section

set_option maxHeartbeats 4000000

open MeasureTheory
open scoped ComplexConjugate

open Submission.BoseGases Work.BoseKinLoc

/-- **The conjugate of the windowed amplitude.**  `tBamp A p W j x = ∫_z A(z)e^{−i⟪p,z⟫}
W(x_{j←z})dz` is an integral of a complex-valued function; since `A` and `W` are real valued, its
conjugate is the same integral with the exponential `e^{+i⟪p,z⟫}`. -/
theorem star_tBamp {n : ℕ} (A : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (W : X n → ℝ) (j : Fin n) (x : X n) :
    star (Work.SmallBoxTBWord.tBamp A p W j x)
      = ∫ z : EuclideanSpace ℝ (Fin 3),
          (A z : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ))
            * (W (Function.update x j z) : ℂ) := by
  rw [Complex.star_def]
  rw [Work.SmallBoxTBWord.tBamp, ← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  have hexp : conj (Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))
      = Complex.exp (Complex.I * (inner ℝ p z : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [map_mul, Complex.conj_ofReal, hexp]

/-- The (conjugate-side) amplitude kernel `A(z)e^{i⟪p,z⟫}W(x_{j←z})`. -/
private def pairF (A : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (W : X n → ℝ) (j : Fin n) (x : X n) (z : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (A z : ℂ) * Complex.exp (Complex.I * (inner ℝ p z : ℂ)) * (W (Function.update x j z) : ℂ)

/-- The amplitude kernel `A(z)e^{−i⟪p,z⟫}V(x_{j←z})`. -/
private def pairG (A : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (V : X n → ℝ) (j : Fin n) (x : X n) (z : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (A z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (V (Function.update x j z) : ℂ)

/-- The product of the two amplitude kernels, as a function of the pair of momenta. -/
private def pairH (A : EuclideanSpace ℝ (Fin 3) → ℝ) (p : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (W V : X n → ℝ) (j : Fin n) (x : X n)
    (q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) : ℂ :=
  pairF A p W j x q.1 * pairG A p V j x q.2

/-- The box indicator is `1` on the configuration box. -/
private lemma indU_zero_eq_one_of_mem {n : ℕ} {ℓ : ℝ} {x : X n} (j : Fin n)
    (hx : x ∈ abox n ℓ) : indU ℓ 0 (x j) = 1 := by
  have hmem : x j ∈ lamBox ℓ 0 := by
    simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hx j
  rw [Work.BoseKinLoc.indU, Set.indicator_of_mem hmem]

/-- **The fixed-momentum pair integral vanishes.**  For the anchored window `χ₀ = chiScale ℓ`
(`ℓ > 0`), the box integral of the complex product `conj(tBamp χ₀ p W j x)·tBamp χ₀ p V j x` is the
double integral of `W(x_j←z)V(x_j←z')` against the exponential factor; each inner integral
vanishes by `hpeel`, and Fubini (justified by the compact support of `χ₀` on the box) kills the
whole thing.  We also record the integrability of the complex integrand on the box. -/
private lemma complex_pair_data {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j : Fin n}
    {W V : X n → ℝ} (hW : Continuous W) (hV : Continuous V)
    (hpeel : ∀ z z' : EuclideanSpace ℝ (Fin 3),
      (∫ x in abox n ℓ, W (Function.update x j z) * V (Function.update x j z')) = 0)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (Integrable (fun x : X n => star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
        * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x)
        ((volume : Measure (X n)).restrict (abox n ℓ)))
    ∧ (∫ x in abox n ℓ, star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
        * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x) = 0 := by
  classical
  have hχcont : Continuous (chiScale ℓ) := (chiScale_contDiff (ne_of_gt hℓ)).continuous
  have hχsupp : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ acube ℓ → chiScale ℓ z = 0 := by
    intro z hz
    by_contra h
    exact hz (chiScale_mem_acube hℓ h)
  have hK0c : IsCompact (acube ℓ) := acube_compact hℓ
  -- the two amplitudes as integrals over the small cube
  have hstar : ∀ x : X n, star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
      = ∫ z in acube ℓ, pairF (chiScale ℓ) p W j x z := by
    intro x
    rw [star_tBamp]
    rw [show (∫ z in acube ℓ, pairF (chiScale ℓ) p W j x z)
        = ∫ z : EuclideanSpace ℝ (Fin 3), pairF (chiScale ℓ) p W j x z from
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun z : EuclideanSpace ℝ (Fin 3) => pairF (chiScale ℓ) p W j x z)
        (fun z hz => by simp [pairF, hχsupp z hz])]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp [pairF]
  have htb : ∀ x : X n, Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x
      = ∫ z in acube ℓ, pairG (chiScale ℓ) p V j x z := by
    intro x
    rw [Work.SmallBoxTBWord.tBamp]
    rw [show (∫ z in acube ℓ, pairG (chiScale ℓ) p V j x z)
        = ∫ z : EuclideanSpace ℝ (Fin 3), pairG (chiScale ℓ) p V j x z from
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (f := fun z : EuclideanSpace ℝ (Fin 3) => pairG (chiScale ℓ) p V j x z)
        (fun z hz => by simp [pairG, hχsupp z hz])]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp [pairG]
  -- continuity of the amplitude kernels in `(x, z)` and in `(x, z, z')`
  have hcF : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
      pairF (chiScale ℓ) p W j s.1 s.2) := by
    have h1 : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) => (chiScale ℓ s.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (hχcont.comp continuous_snd)
    have h2 : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (Complex.I * (inner ℝ p s.2 : ℂ))) :=
      Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.inner continuous_snd)))
    have h3 : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
        (W (Function.update s.1 j s.2) : ℂ)) :=
      Complex.continuous_ofReal.comp (hW.comp (continuous_update j))
    have h4 : Continuous ((fun s : X n × EuclideanSpace ℝ (Fin 3) => (chiScale ℓ s.2 : ℂ)) *
        (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (Complex.I * (inner ℝ p s.2 : ℂ))) *
        (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
          (W (Function.update s.1 j s.2) : ℂ))) := (h1.mul h2).mul h3
    exact h4.congr (fun s => by simp [pairF, Pi.mul_apply])
  have hcG : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
      pairG (chiScale ℓ) p V j s.1 s.2) := by
    have h1 : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) => (chiScale ℓ s.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (hχcont.comp continuous_snd)
    have h2 : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
        Complex.exp (-(Complex.I * (inner ℝ p s.2 : ℂ)))) :=
      Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.inner continuous_snd))).neg)
    have h3 : Continuous (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
        (V (Function.update s.1 j s.2) : ℂ)) :=
      Complex.continuous_ofReal.comp (hV.comp (continuous_update j))
    have h4 : Continuous ((fun s : X n × EuclideanSpace ℝ (Fin 3) => (chiScale ℓ s.2 : ℂ)) *
        (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-(Complex.I * (inner ℝ p s.2 : ℂ)))) *
        (fun s : X n × EuclideanSpace ℝ (Fin 3) =>
          (V (Function.update s.1 j s.2) : ℂ))) := (h1.mul h2).mul h3
    exact h4.congr (fun s => by simp [pairG, Pi.mul_apply])
  have hF' : Continuous (fun r : X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      pairF (chiScale ℓ) p W j r.1 r.2.1) := by
    simp only [pairF]
    fun_prop
  have hG' : Continuous (fun r : X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      pairG (chiScale ℓ) p V j r.1 r.2.2) := by
    simp only [pairG]
    fun_prop
  have hHcont : Continuous (fun r : X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      pairF (chiScale ℓ) p W j r.1 r.2.1 * pairG (chiScale ℓ) p V j r.1 r.2.2) :=
    (hF'.mul hG').congr (fun r => by simp [Pi.mul_apply])
  -- the pointwise vanishing for fixed pair of momenta
  have hpt : ∀ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
      (∫ x in abox n ℓ, pairH (chiScale ℓ) p W V j x q) = 0 := by
    rintro ⟨z1, z2⟩
    have hfac : ∀ x : X n, pairH (chiScale ℓ) p W V j x (z1, z2)
        = ((chiScale ℓ z1 : ℂ) * Complex.exp (Complex.I * (inner ℝ p z1 : ℂ))
            * (chiScale ℓ z2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z2 : ℂ))))
          * ((W (Function.update x j z1) * V (Function.update x j z2) : ℝ) : ℂ) := by
      intro x
      simp only [pairH, pairF, pairG, Complex.ofReal_mul]
      ring
    calc (∫ x in abox n ℓ, pairH (chiScale ℓ) p W V j x (z1, z2))
        = ∫ x in abox n ℓ,
            ((chiScale ℓ z1 : ℂ) * Complex.exp (Complex.I * (inner ℝ p z1 : ℂ))
              * (chiScale ℓ z2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z2 : ℂ))))
              * ((W (Function.update x j z1) * V (Function.update x j z2) : ℝ) : ℂ) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          exact hfac x
      _ = ((chiScale ℓ z1 : ℂ) * Complex.exp (Complex.I * (inner ℝ p z1 : ℂ))
            * (chiScale ℓ z2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z2 : ℂ))))
          * ∫ x in abox n ℓ,
              ((W (Function.update x j z1) * V (Function.update x j z2) : ℝ) : ℂ) := by
          rw [MeasureTheory.integral_const_mul]
      _ = ((chiScale ℓ z1 : ℂ) * Complex.exp (Complex.I * (inner ℝ p z1 : ℂ))
            * (chiScale ℓ z2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z2 : ℂ))))
          * (((∫ x in abox n ℓ,
                W (Function.update x j z1) * V (Function.update x j z2)) : ℝ) : ℂ) := by
          have h := Complex.ofRealLI.integral_comp_comm
            (μ := (volume : Measure (X n)).restrict (abox n ℓ))
            (fun x => W (Function.update x j z1) * V (Function.update x j z2))
          have h2 := congrArg (fun t : ℂ =>
            ((chiScale ℓ z1 : ℂ) * Complex.exp (Complex.I * (inner ℝ p z1 : ℂ))
              * (chiScale ℓ z2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z2 : ℂ)))) * t) h
          simpa using h2
      _ = ((chiScale ℓ z1 : ℂ) * Complex.exp (Complex.I * (inner ℝ p z1 : ℂ))
            * (chiScale ℓ z2 : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z2 : ℂ))))
            * ((0 : ℝ) : ℂ) := by
          rw [hpeel z1 z2]
      _ = 0 := by simp
  -- integrability of the uncurried integrand on the product measure
  have hμν : Integrable (fun r : X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
      pairF (chiScale ℓ) p W j r.1 r.2.1 * pairG (chiScale ℓ) p V j r.1 r.2.2)
      (((volume : Measure (X n)).restrict (abox n ℓ)).prod
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (EuclideanSpace ℝ (Fin 3)))).restrict (acube ℓ ×ˢ acube ℓ))) := by
    have hIntOn : IntegrableOn
        (fun r : X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
          pairF (chiScale ℓ) p W j r.1 r.2.1 * pairG (chiScale ℓ) p V j r.1 r.2.2)
        (abox n ℓ ×ˢ (acube ℓ ×ˢ acube ℓ))
        ((volume : Measure (X n)).prod
          (volume : Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))) :=
      (hHcont.continuousOn).integrableOn_compact ((abox_compact n hℓ).prod (hK0c.prod hK0c))
    have hIntOn' : Integrable
        (fun r : X n × (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) =>
          pairF (chiScale ℓ) p W j r.1 r.2.1 * pairG (chiScale ℓ) p V j r.1 r.2.2)
        (((volume : Measure (X n)).prod
          (volume : Measure (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)))).restrict
            (abox n ℓ ×ˢ (acube ℓ ×ˢ acube ℓ))) := hIntOn.integrable
    rw [← Measure.prod_restrict] at hIntOn'
    exact hIntOn'
  have hInt : Integrable (Function.uncurry (pairH (chiScale ℓ) p W V j))
      (((volume : Measure (X n)).restrict (abox n ℓ)).prod
        (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
            (volume : Measure (EuclideanSpace ℝ (Fin 3)))).restrict (acube ℓ ×ˢ acube ℓ))) :=
    hμν.congr (Filter.Eventually.of_forall (fun r => by
      simp only [Function.uncurry, pairH, Pi.mul_apply]))
  -- the Fubini swap
  have h1 : (∫ x in abox n ℓ, star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
      * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x)
      = ∫ x in abox n ℓ, (∫ z in acube ℓ, pairF (chiScale ℓ) p W j x z)
            * (∫ z in acube ℓ, pairG (chiScale ℓ) p V j x z) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only [hstar x, htb x]
  have h2 : (∫ x in abox n ℓ, (∫ z in acube ℓ, pairF (chiScale ℓ) p W j x z)
            * (∫ z in acube ℓ, pairG (chiScale ℓ) p V j x z))
      = ∫ x in abox n ℓ, ∫ q in acube ℓ ×ˢ acube ℓ,
            pairH (chiScale ℓ) p W V j x q ∂(volume.prod volume) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have h := MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
      (f := fun z : EuclideanSpace ℝ (Fin 3) => pairF (chiScale ℓ) p W j x z)
      (g := fun z : EuclideanSpace ℝ (Fin 3) => pairG (chiScale ℓ) p V j x z)
      (s := acube ℓ) (t := acube ℓ)
    simpa only [pairH] using h.symm
  have hswap := MeasureTheory.integral_integral_swap
    (μ := (volume : Measure (X n)).restrict (abox n ℓ))
    (ν := ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))).restrict (acube ℓ ×ˢ acube ℓ)) hInt
  have hzero : (∫ x in abox n ℓ, star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
      * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x) = 0 := by
    calc (∫ x in abox n ℓ, star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
          * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x)
        = ∫ x in abox n ℓ, (∫ z in acube ℓ, pairF (chiScale ℓ) p W j x z)
              * (∫ z in acube ℓ, pairG (chiScale ℓ) p V j x z) := h1
      _ = ∫ x in abox n ℓ, ∫ q in acube ℓ ×ˢ acube ℓ,
              pairH (chiScale ℓ) p W V j x q ∂(volume.prod volume) := h2
      _ = ∫ q, ∫ x, pairH (chiScale ℓ) p W V j x q
            ∂((volume : Measure (X n)).restrict (abox n ℓ))
            ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
                (volume : Measure (EuclideanSpace ℝ (Fin 3)))).restrict (acube ℓ ×ˢ acube ℓ)) :=
          hswap
      _ = 0 := by
          have hz : (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
                ∫ x, pairH (chiScale ℓ) p W V j x q
                  ∂((volume : Measure (X n)).restrict (abox n ℓ))) = fun _ => (0 : ℂ) :=
            funext hpt
          rw [hz]
          simp
  -- integrability of the configuration-space integrand, from the Fubini integrability
  have hzint0 : Integrable (fun x : X n => ∫ q, Function.uncurry (pairH (chiScale ℓ) p W V j) (x, q)
      ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (EuclideanSpace ℝ (Fin 3)))).restrict (acube ℓ ×ˢ acube ℓ)))
      ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    Integrable.integral_prod_left
      (f := Function.uncurry (pairH (chiScale ℓ) p W V j)) hInt
  have hzint : Integrable (fun x : X n => star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
      * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x)
      ((volume : Measure (X n)).restrict (abox n ℓ)) := by
    refine hzint0.congr (Filter.Eventually.of_forall (fun x => ?_))
    change (∫ q in acube ℓ ×ˢ acube ℓ,
          Function.uncurry (pairH (chiScale ℓ) p W V j) (x, q) ∂(volume.prod volume))
        = star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
            * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x
    rw [show (∫ q in acube ℓ ×ˢ acube ℓ,
          Function.uncurry (pairH (chiScale ℓ) p W V j) (x, q) ∂(volume.prod volume))
        = (∫ z in acube ℓ, pairF (chiScale ℓ) p W j x z)
            * (∫ z in acube ℓ, pairG (chiScale ℓ) p V j x z) from by
      simpa only [Function.uncurry, pairH, Pi.mul_apply] using
        (MeasureTheory.setIntegral_prod_mul (μ := volume) (ν := volume)
          (f := fun z : EuclideanSpace ℝ (Fin 3) => pairF (chiScale ℓ) p W j x z)
          (g := fun z : EuclideanSpace ℝ (Fin 3) => pairG (chiScale ℓ) p V j x z)
          (s := acube ℓ) (t := acube ℓ))]
    rw [← hstar x, ← htb x]
  exact ⟨hzint, hzero⟩

/-- For fixed momentum `p`, the box integral of `star(tBamp χ₀ p W j x)·tBamp χ₀ p V j x`
vanishes when `W` is mean-free in a slot `k ≠ j` and `V` is independent of that slot: expanding
both `tBamp`'s as the `z`, `z'` integrals against the window `χ₀ = bsWin ℓ 0` and exchanging the
`x`-integration with those (compactly supported) integrals reduces the claim to the vanishing of
`∫_x 1_{abox}(x)·W(x_j←z)V(x_j←z')`, which is the hypothesis `hpeel`. -/
theorem tBamp_pair_fixed_p_zero {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {j k : Fin n} (hjk : j ≠ k)
    {W V : Submission.BoseGases.X n → ℝ} (hW : Continuous W) (hV : Continuous V)
    (hpeel : ∀ z z' : EuclideanSpace ℝ (Fin 3), (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j)
          * (W (Function.update x j z) * V (Function.update x j z'))) = 0)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
      (star (Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p W j x) *
        Work.SmallBoxTBWord.tBamp (Work.BSKinetic.bsWin ℓ 0) p V j x).re) = 0 := by
  classical
  -- replace the anchored window `bsWin ℓ 0` by the corpus bump `chiScale ℓ`
  rw [show Work.BSKinetic.bsWin ℓ 0 = chiScale ℓ from by
    funext z
    simp [Work.BSKinetic.bsWin]]
  -- a.e. triviality of the box indicator on the configuration box
  have hInd : ∀ᵐ x ∂((volume : Measure (X n)).restrict (abox n ℓ)), indU ℓ 0 (x j) = 1 := by
    rw [MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
    filter_upwards with x hx
    exact indU_zero_eq_one_of_mem j hx
  -- the peeling hypothesis, stripped of the (a.e. trivial) indicator
  have hpeel' : ∀ z z' : EuclideanSpace ℝ (Fin 3),
      (∫ x in abox n ℓ, W (Function.update x j z) * V (Function.update x j z')) = 0 := by
    intro z z'
    have h := hpeel z z'
    rw [← h]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hInd] with x hx
    rw [hx, one_mul]
  -- drop the indicator from the goal
  have hgoal1 : (∫ x in abox n ℓ, indU ℓ 0 (x j) *
      (star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
        * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x).re)
      = ∫ x in abox n ℓ, (star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
          * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x).re := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hInd] with x hx
    rw [hx, one_mul]
  obtain ⟨hzint, hzero⟩ := complex_pair_data hℓ hW hV hpeel' p
  rw [hgoal1]
  change (∫ x in abox n ℓ, RCLike.re (star (Work.SmallBoxTBWord.tBamp (chiScale ℓ) p W j x)
      * Work.SmallBoxTBWord.tBamp (chiScale ℓ) p V j x)) = 0
  rw [integral_re hzint, hzero]
  simp

end

end Work.BoseFixB2.DvApriori
