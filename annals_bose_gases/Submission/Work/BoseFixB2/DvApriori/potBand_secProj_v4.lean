import ChallengeDeps
import Submission.Work.BoseFixB2.DvApriori.Band.UniversalTwo
import Submission.Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword_radial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
/-!
# `Work.BoseFixB2.DvApriori.potBand_secProj_v4`

The two **band identities** of FS §6 for the two-body potential word `potWordU`: with the
`qLHSden` normalisation of the weight,

* band 1: `Σ_{i} ⟨1_{n₊=i}Φ, potWordU 1_{n₊=i+1}Φ⟩ = (1/2)(q1word + q3word)`;
* band 2: `Σ_{i} ⟨1_{n₊=i}Φ, potWordU 1_{n₊=i+2}Φ⟩
            = (1/2)Σ_{p∈pairSet}∫ (P_{p₁}P_{p₂}Φ)(x)·(Q_{p₂}Q_{p₁}Φ)(x)·w(x_{p₁},x_{p₂})`.

The engine is the linearity of the band functionals in the weight (`Band/Assembly.lean`) and
the few-slot evaluations `bandFun_single`/`bandFun_pair` (`Band/Assembly.lean`) resp.
`bandFunTwo_single`/`bandFunTwo_pair` (`Band/UniversalTwo.lean`).  The hypothesis `IsRadial v`
of the statement is used exactly twice: pointwise (through `wPairC_v_sym`) to compare the
`Σ_{i<j}`-convention of `potWordU` with the `pairSet`-convention of `qLHSden`/`q1word`/`q3word`,
and in the `pairSet` reindexing of the band-1 pair sum.
-/

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

noncomputable section

/-! ## 1. Integrability of the slot weights -/

/-- The two-slot weight `wPairC ℓ h (x i) (x j)` is integrable over the centred box. -/
lemma integrableOn_wPairC_pair {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * chiR0) {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      wPairC ℓ h (x i) (x j)) (abox N ℓ) MeasureTheory.volume := by
  have h1 := integrableOn_slot_wPair (N := N) hℓ hi hsupp hRℓ hij
    (S := fun _ : Submission.BoseGases.X N => (1 : ℝ)) continuous_const
  simpa [wPairC] using h1

/-- The one-slot fibre weight `w1Fibre ℓ (wPairC ℓ h) (x i)` is integrable over the box. -/
lemma integrableOn_w1Fibre_coord {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {h : EuclideanSpace ℝ (Fin 3) → ℝ} (hi : MeasureTheory.Integrable h)
    (hsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → h z = 0)
    (hR : 0 ≤ R) (hRℓ : R ≤ ℓ * chiR0) {N : ℕ} (i : Fin N) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      w1Fibre ℓ (wPairC ℓ h) (x i)) (abox N ℓ) MeasureTheory.volume := by
  have hFm : MeasureTheory.AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∫ y in acube ℓ, wPair ℓ h z y) (MeasureTheory.volume.restrict (acube ℓ)) :=
    fibre_acube_aem hi
  have hC : ∀ z ∈ acube ℓ,
      |(fun z : EuclideanSpace ℝ (Fin 3) => ∫ y in acube ℓ, wPair ℓ h z y) z|
        ≤ chiSup ^ 2 * 2 * ∫ z : EuclideanSpace ℝ (Fin 3), |h z| :=
    fun z _ => fibre_acube_abs_le hℓ hR hRℓ hi hsupp z
  have h1 := integrableOn_slot_fibre (N := N) hℓ i hFm hC
    (S := fun _ : Submission.BoseGases.X N => (1 : ℝ)) continuous_const
  simpa [w1Fibre, wPairC] using h1

/-! ## 2. Pointwise slot algebra (function-level versions) -/

lemma aQ_comm_fun {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    aQ ℓ i (aQ ℓ j Φ) = aQ ℓ j (aQ ℓ i Φ) :=
  funext fun x => aQ_comm hℓ hij hΦ x

lemma aP_aQ_comm_fun {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    aP ℓ i (aQ ℓ j Φ) = aQ ℓ j (aP ℓ i Φ) :=
  funext fun x => aP_aQ_comm hℓ hij hΦ x

lemma aP_comm_fun {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (i j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    aP ℓ i (aP ℓ j Φ) = aP ℓ j (aP ℓ i Φ) :=
  funext fun x => aP_comm hℓ i j hΦ x

/-! ## 3. Linearity of the band functionals in the weight -/

lemma bandFun_congr_pt {ℓ : ℝ} {n : ℕ} {W W' : Submission.BoseGases.X n → ℝ}
    (h : ∀ x, W x = W' x) (Φ : Submission.BoseGases.X n → ℝ) :
    bandFun ℓ n W Φ = bandFun ℓ n W' Φ := by
  unfold bandFun
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [h x]

lemma bandFunTwo_congr_pt {ℓ : ℝ} {n : ℕ} {W W' : Submission.BoseGases.X n → ℝ}
    (h : ∀ x, W x = W' x) (Φ : Submission.BoseGases.X n → ℝ) :
    bandFunTwo ℓ n W Φ = bandFunTwo ℓ n W' Φ := by
  unfold bandFunTwo
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [h x]

lemma bandFun_const_mul {ℓ : ℝ} {n : ℕ} (c : ℝ) (W : Submission.BoseGases.X n → ℝ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    bandFun ℓ n (fun x => c * W x) Φ = c * bandFun ℓ n W Φ := by
  unfold bandFun
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (∫ x in abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * (c * W x) * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
      = ∫ x in abox n ℓ,
        c * (Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
      from by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring]
  rw [MeasureTheory.integral_const_mul]

/-! ## 4. The `pairSet` reindexing by the order swap -/

lemma mem_pairSet {n : ℕ} {p : Fin n × Fin n} : p ∈ pairSet n ↔ p.1 ≠ p.2 := by
  simp [pairSet]

/-- The ordered-pair set is invariant under the swap of the two entries, so summing a
function of the swapped pair is the same as summing the function itself. -/
lemma sum_pairSet_swap {n : ℕ} (F : Fin n × Fin n → ℝ) :
    (∑ p ∈ pairSet n, F (p.2, p.1)) = ∑ p ∈ pairSet n, F p := by
  refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [mem_pairSet] using (mem_pairSet.mp hp).symm
  · intro p _ q _ h
    exact Prod.ext (by simpa using congrArg Prod.snd h) (by simpa using congrArg Prod.fst h)
  · intro q hq
    exact ⟨(q.2, q.1), by simpa [mem_pairSet] using (mem_pairSet.mp hq).symm, by simp⟩
  · intro p _
    rfl

lemma sum_pairSet_add_swap {n : ℕ} (F : Fin n × Fin n → ℝ) :
    (∑ p ∈ pairSet n, (F p + F (p.2, p.1))) = 2 * ∑ p ∈ pairSet n, F p := by
  rw [Finset.sum_add_distrib, sum_pairSet_swap F, two_mul]

/-! ## 5. The `pairSet` algebra of the band-1 identity

For a symmetric pair kernel `w2`, the sum over the ordered pairs of the four
`bandFun`-pair terms equals twice the sum of the `q1word`/`q3word` pair terms. -/

lemma sum_pairSet_four_eq_two {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {w2 : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2sym : ∀ x y : EuclideanSpace ℝ (Fin 3), w2 x y = w2 y x)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ p ∈ pairSet n,
        ((∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aP ℓ p.2 Φ) x)
          + (∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aP ℓ p.1 (aQ ℓ p.2 Φ) x)
          + (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)
          + (∫ x in abox n ℓ, aQ ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)))
      = 2 * (∑ p ∈ pairSet n,
          ((∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aP ℓ p.1 (aP ℓ p.2 Φ) x
              * w2 (x p.1) (x p.2))
            + (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x
              * w2 (x p.1) (x p.2)))) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hper : ∀ p ∈ pairSet n,
      ((∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aP ℓ p.2 Φ) x)
        + (∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aP ℓ p.1 (aQ ℓ p.2 Φ) x)
        + (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)
        + (∫ x in abox n ℓ, aQ ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aQ ℓ p.2 Φ) x))
        = (((∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aP ℓ p.1 (aP ℓ p.2 Φ) x
              * w2 (x p.1) (x p.2))
            + (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x
              * w2 (x p.1) (x p.2)))
          + ((∫ x in abox n ℓ, aP ℓ p.2 (aQ ℓ p.1 Φ) x * aP ℓ p.2 (aP ℓ p.1 Φ) x
              * w2 (x p.2) (x p.1))
            + (∫ x in abox n ℓ, aP ℓ p.2 (aQ ℓ p.1 Φ) x * aQ ℓ p.1 (aQ ℓ p.2 Φ) x
              * w2 (x p.2) (x p.1)))) := by
    intro p hp
    have hpne : p.1 ≠ p.2 := mem_pairSet.mp hp
    have hpne' : p.2 ≠ p.1 := fun h => hpne h.symm
    -- `T2 p = A p`
    have e1 : (∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
          * aP ℓ p.1 (aQ ℓ p.2 Φ) x)
        = (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aP ℓ p.1 (aP ℓ p.2 Φ) x
          * w2 (x p.1) (x p.2)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring
    -- `T3 p = B p`
    have e2 : (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
          * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)
        = (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x
          * w2 (x p.1) (x p.2)) := by
      have hcomm := congrFun (aQ_comm_fun hℓ hpne hΦc)
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [hcomm x]
      ring
    -- `T1 p = A (p.2,p.1)`
    have e3 : (∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
          * aQ ℓ p.1 (aP ℓ p.2 Φ) x)
        = (∫ x in abox n ℓ, aP ℓ p.2 (aQ ℓ p.1 Φ) x * aP ℓ p.2 (aP ℓ p.1 Φ) x
          * w2 (x p.2) (x p.1)) := by
      have h1 := congrFun (aP_comm_fun hℓ p.2 p.1 hΦc)
      have h2 := congrFun (aP_aQ_comm_fun hℓ hpne' hΦc)
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [← h1 x, ← h2 x, hw2sym (x p.2) (x p.1)]
      ring
    -- `T4 p = B (p.2,p.1)`
    have e4 : (∫ x in abox n ℓ, aQ ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
          * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)
        = (∫ x in abox n ℓ, aP ℓ p.2 (aQ ℓ p.1 Φ) x * aQ ℓ p.1 (aQ ℓ p.2 Φ) x
          * w2 (x p.2) (x p.1)) := by
      have h2 := congrFun (aP_aQ_comm_fun hℓ hpne' hΦc)
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [← h2 x, hw2sym (x p.2) (x p.1)]
      ring
    rw [e1, e2, e3, e4]
    ring
  rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib,
    sum_pairSet_swap (n := n) (F := fun p => (∫ x in abox n ℓ,
        aP ℓ p.1 (aQ ℓ p.2 Φ) x * aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2))
      + (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x
        * w2 (x p.1) (x p.2)))]
  ring

/-! ## 6. The band-1 identity for the `qLHSden` weight -/

/-- **The band-1 identity** for the weight `−μΣᵢw₁(xᵢ,·) + (1/2)Σ_{i≠j}w₂(xᵢ,xⱼ)`, in terms
of the corpus words `q1word`/`q3word`.  The pair kernel `w2` is assumed symmetric
(pointwise) — that is exactly the hypothesis `IsRadial v` supplies at the use site. -/
lemma bandFun_qLHSden_eq {ℓ μ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2sym : ∀ x y : EuclideanSpace ℝ (Fin 3), w2 x y = w2 y x)
    (h1int : ∀ i : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      w1Fibre ℓ w1 (x i)) (abox n ℓ) MeasureTheory.volume)
    (h2int : ∀ p ∈ pairSet n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      w2 (x p.1) (x p.2)) (abox n ℓ) MeasureTheory.volume)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    bandFun ℓ n (fun x : Submission.BoseGases.X n => -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))
        + (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) Φ
      = (1/2) * (q1word (N := n) ℓ μ w1 w2 Φ + q3word (N := n) ℓ w2 Φ) := by
  have hΦc : Continuous Φ := hΦ.continuous
  -- the one-slot evaluation
  have hsingle : ∀ i : Fin n, bandFun ℓ n (fun x : Submission.BoseGases.X n =>
        w1Fibre ℓ w1 (x i)) Φ
      = ∫ x in abox n ℓ, aP ℓ i Φ x * w1Fibre ℓ w1 (x i) * aQ ℓ i Φ x := by
    intro i
    refine bandFun_single hℓ i ?_ (h1int i) hΦ
    intro k hk x z
    show w1Fibre ℓ w1 ((Function.update x k z) i) = w1Fibre ℓ w1 (x i)
    rw [Function.update_of_ne (Ne.symm hk)]
  -- the two-slot evaluation
  have hpair : ∀ p ∈ pairSet n, bandFun ℓ n (fun x : Submission.BoseGases.X n =>
        w2 (x p.1) (x p.2)) Φ
      = ((∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aP ℓ p.2 Φ) x)
          + (∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aP ℓ p.1 (aQ ℓ p.2 Φ) x)
          + (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)
          + (∫ x in abox n ℓ, aQ ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
              * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)) := by
    intro p hp
    have hpne : p.1 ≠ p.2 := mem_pairSet.mp hp
    refine bandFun_pair hℓ p.1 p.2 hpne ?_ (h2int p hp) hΦ
    intro k hk1 hk2 x z
    show w2 ((Function.update x k z) p.1) ((Function.update x k z) p.2) = w2 (x p.1) (x p.2)
    rw [Function.update_of_ne (Ne.symm hk1), Function.update_of_ne (Ne.symm hk2)]
  -- integrability of the two parts
  have hW1int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))) (abox n ℓ) MeasureTheory.volume :=
    (integrable_finsetSum (Finset.univ : Finset (Fin n))
      (f := fun i (x : Submission.BoseGases.X n) => w1Fibre ℓ w1 (x i))
      (fun i _ => h1int i)).const_mul (-μ)
  have hW2int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) (abox n ℓ) MeasureTheory.volume :=
    (integrable_finsetSum (pairSet n)
      (f := fun p (x : Submission.BoseGases.X n) => w2 (x p.1) (x p.2))
      (fun p hp => h2int p hp)).const_mul (1/2)
  -- the two halves
  have hS1 : bandFun ℓ n (fun x : Submission.BoseGases.X n =>
        ∑ i : Fin n, w1Fibre ℓ w1 (x i)) Φ
      = ∑ i : Fin n, bandFun ℓ n (fun x : Submission.BoseGases.X n =>
          w1Fibre ℓ w1 (x i)) Φ :=
    bandFun_finsetSum hℓ Finset.univ hΦc
      (T := fun i (x : Submission.BoseGases.X n) => w1Fibre ℓ w1 (x i))
      (fun i _ => h1int i)
  have hS2 : bandFun ℓ n (fun x : Submission.BoseGases.X n =>
        ∑ p ∈ pairSet n, w2 (x p.1) (x p.2)) Φ
      = ∑ p ∈ pairSet n, bandFun ℓ n (fun x : Submission.BoseGases.X n =>
          w2 (x p.1) (x p.2)) Φ :=
    bandFun_finsetSum hℓ (pairSet n) hΦc
      (T := fun p (x : Submission.BoseGases.X n) => w2 (x p.1) (x p.2))
      (fun p hp => h2int p hp)
  have hW1 : bandFun ℓ n (fun x : Submission.BoseGases.X n =>
        -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))) Φ
      = -μ * bandFun ℓ n (fun x : Submission.BoseGases.X n =>
          ∑ i : Fin n, w1Fibre ℓ w1 (x i)) Φ :=
    bandFun_const_mul (-μ) (fun x : Submission.BoseGases.X n =>
      ∑ i : Fin n, w1Fibre ℓ w1 (x i)) Φ
  have hW2 : bandFun ℓ n (fun x : Submission.BoseGases.X n =>
        (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) Φ
      = (1/2) * bandFun ℓ n (fun x : Submission.BoseGases.X n =>
          ∑ p ∈ pairSet n, w2 (x p.1) (x p.2)) Φ :=
    bandFun_const_mul (1/2) (fun x : Submission.BoseGases.X n =>
      ∑ p ∈ pairSet n, w2 (x p.1) (x p.2)) Φ
  have hA : bandFun ℓ n (fun x : Submission.BoseGases.X n => -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))
        + (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) Φ
      = -μ * (∑ i : Fin n, ∫ x in abox n ℓ, aP ℓ i Φ x * w1Fibre ℓ w1 (x i) * aQ ℓ i Φ x)
        + (1/2) * (∑ p ∈ pairSet n,
            ((∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
                  * aQ ℓ p.1 (aP ℓ p.2 Φ) x)
              + (∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
                  * aP ℓ p.1 (aQ ℓ p.2 Φ) x)
              + (∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
                  * aQ ℓ p.1 (aQ ℓ p.2 Φ) x)
              + (∫ x in abox n ℓ, aQ ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
                  * aQ ℓ p.1 (aQ ℓ p.2 Φ) x))) := by
    rw [bandFun_add (W₁ := fun x : Submission.BoseGases.X n =>
            -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i)))
          (W₂ := fun x : Submission.BoseGases.X n =>
            (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) hℓ hΦc hW1int hW2int]
    rw [hW1, hW2, hS1, hS2]
    rw [Finset.sum_congr rfl (fun i _ => hsingle i),
      Finset.sum_congr rfl (fun p hp => hpair p hp)]
  -- the right-hand side
  have hR : (1/2) * (q1word (N := n) ℓ μ w1 w2 Φ + q3word (N := n) ℓ w2 Φ)
      = (∑ p ∈ pairSet n, ∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aP ℓ p.1 (aP ℓ p.2 Φ) x
            * w2 (x p.1) (x p.2))
        - μ * (∑ i : Fin n, ∫ x in abox n ℓ, aQ ℓ i Φ x * aP ℓ i Φ x * w1Fibre ℓ w1 (x i))
        + (∑ p ∈ pairSet n, ∫ x in abox n ℓ, aP ℓ p.1 (aQ ℓ p.2 Φ) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x
            * w2 (x p.1) (x p.2)) := by
    simp only [q1word, q3word]
    ring
  -- the `μ`-parts agree
  have hMU : (∑ i : Fin n, ∫ x in abox n ℓ, aP ℓ i Φ x * w1Fibre ℓ w1 (x i) * aQ ℓ i Φ x)
      = ∑ i : Fin n, ∫ x in abox n ℓ, aQ ℓ i Φ x * aP ℓ i Φ x * w1Fibre ℓ w1 (x i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  rw [hA, hR, hMU, sum_pairSet_four_eq_two hℓ hw2sym hΦ, Finset.sum_add_distrib]
  ring

/-! ## 7. The band-2 identity for the `qLHSden` weight -/

/-- **The band-2 identity** for the `qLHSden` weight: the one-body part contributes nothing
(a single slot cannot supply two level jumps) and the pair part contributes the single
`∅ → {p₁,p₂}` transition. -/
lemma bandFunTwo_qLHSden_eq {ℓ μ : ℝ} (hℓ : 0 < ℓ) {n : ℕ}
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (h1int : ∀ i : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      w1Fibre ℓ w1 (x i)) (abox n ℓ) MeasureTheory.volume)
    (h2int : ∀ p ∈ pairSet n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      w2 (x p.1) (x p.2)) (abox n ℓ) MeasureTheory.volume)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    bandFunTwo ℓ n (fun x : Submission.BoseGases.X n => -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))
        + (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) Φ
      = (1/2) * (∑ p ∈ pairSet n, ∫ x in abox n ℓ,
          aP ℓ p.1 (aP ℓ p.2 Φ) x * aQ ℓ p.2 (aQ ℓ p.1 Φ) x * w2 (x p.1) (x p.2)) := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hsingle : ∀ i : Fin n, bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
        w1Fibre ℓ w1 (x i)) Φ = 0 := by
    intro i
    refine bandFunTwo_single hℓ i ?_ (h1int i) hΦ
    intro k hk x z
    show w1Fibre ℓ w1 ((Function.update x k z) i) = w1Fibre ℓ w1 (x i)
    rw [Function.update_of_ne (Ne.symm hk)]
  have hpair : ∀ p ∈ pairSet n, bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
        w2 (x p.1) (x p.2)) Φ
      = ∫ x in abox n ℓ, aP ℓ p.1 (aP ℓ p.2 Φ) x * w2 (x p.1) (x p.2)
          * aQ ℓ p.1 (aQ ℓ p.2 Φ) x := by
    intro p hp
    have hpne : p.1 ≠ p.2 := mem_pairSet.mp hp
    refine bandFunTwo_pair hℓ p.1 p.2 hpne ?_ (h2int p hp) hΦ
    intro k hk1 hk2 x z
    show w2 ((Function.update x k z) p.1) ((Function.update x k z) p.2) = w2 (x p.1) (x p.2)
    rw [Function.update_of_ne (Ne.symm hk1), Function.update_of_ne (Ne.symm hk2)]
  have hW1int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))) (abox n ℓ) MeasureTheory.volume :=
    (integrable_finsetSum (Finset.univ : Finset (Fin n))
      (f := fun i (x : Submission.BoseGases.X n) => w1Fibre ℓ w1 (x i))
      (fun i _ => h1int i)).const_mul (-μ)
  have hW2int : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) (abox n ℓ) MeasureTheory.volume :=
    (integrable_finsetSum (pairSet n)
      (f := fun p (x : Submission.BoseGases.X n) => w2 (x p.1) (x p.2))
      (fun p hp => h2int p hp)).const_mul (1/2)
  have hS1 : bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
        ∑ i : Fin n, w1Fibre ℓ w1 (x i)) Φ
      = ∑ i : Fin n, bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
          w1Fibre ℓ w1 (x i)) Φ :=
    bandFunTwo_finsetSum hℓ Finset.univ hΦc
      (T := fun i (x : Submission.BoseGases.X n) => w1Fibre ℓ w1 (x i))
      (fun i _ => h1int i)
  have hS2 : bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
        ∑ p ∈ pairSet n, w2 (x p.1) (x p.2)) Φ
      = ∑ p ∈ pairSet n, bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
          w2 (x p.1) (x p.2)) Φ :=
    bandFunTwo_finsetSum hℓ (pairSet n) hΦc
      (T := fun p (x : Submission.BoseGases.X n) => w2 (x p.1) (x p.2))
      (fun p hp => h2int p hp)
  have hW1 : bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
        -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))) Φ
      = -μ * bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
          ∑ i : Fin n, w1Fibre ℓ w1 (x i)) Φ :=
    bandFunTwo_const_mul (n := n) hℓ (-μ)
      (fun x : Submission.BoseGases.X n => ∑ i : Fin n, w1Fibre ℓ w1 (x i)) Φ
  have hW2 : bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
        (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) Φ
      = (1/2) * bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
          ∑ p ∈ pairSet n, w2 (x p.1) (x p.2)) Φ :=
    bandFunTwo_const_mul (n := n) hℓ (1/2)
      (fun x : Submission.BoseGases.X n => ∑ p ∈ pairSet n, w2 (x p.1) (x p.2)) Φ
  have hA : bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
        -μ * (∑ i : Fin n, w1Fibre ℓ w1 (x i))
        + (1/2) * (∑ p ∈ pairSet n, w2 (x p.1) (x p.2))) Φ
      = -μ * (∑ i : Fin n, bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
            w1Fibre ℓ w1 (x i)) Φ)
        + (1/2) * (∑ p ∈ pairSet n, bandFunTwo ℓ n (fun x : Submission.BoseGases.X n =>
            w2 (x p.1) (x p.2)) Φ) := by
    rw [bandFunTwo_add hℓ hΦc hW1int hW2int, hW1, hW2, hS1, hS2]
  rw [hA, Finset.sum_eq_zero (fun i _ => hsingle i), mul_zero, zero_add]
  congr 1
  rw [Finset.sum_congr rfl (fun p hp => hpair p hp)]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hpne : p.1 ≠ p.2 := mem_pairSet.mp hp
  have hcomm := congrFun (aQ_comm_fun hℓ hpne hΦc)
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [hcomm x]
  ring
/-- **The band-1 and band-2 identities of FS §6** for `potWordU`. -/
theorem potBand_secProj_v4 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {ℓ : ℝ} {R : ℝ} (hℓ : 0 < ℓ) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hv1 : MeasureTheory.MemLp v 1)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∑ i ∈ Finset.range n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * Work.BoseFixB2.secProj ℓ (i+1) Φ x
          * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
      = (1/2) * (Submission.BoseGases.q1word (N := n) ℓ μ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h))
            (Submission.BoseGases.wPairC ℓ v) Φ
          + Submission.BoseGases.q3word (N := n) ℓ (Submission.BoseGases.wPairC ℓ v) Φ)
    ∧ (∑ i ∈ Finset.range (n-1), ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * Work.BoseFixB2.secProj ℓ (i+2) Φ x
          * Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
      = (1/2) * (∑ p ∈ Submission.BoseGases.pairSet n,
          ∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
            * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            * Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2)) := by
  have hvin : MeasureTheory.Integrable v := v_integrable hv1
  have hvsup : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 :=
    fun z hz => v_eq_zero_of_norm_ge hv_supp hz
  have hgin : MeasureTheory.Integrable (g0 v h) := g0_integrable hR hv_supp h
  have hgsup : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → g0 v h z = 0 :=
    fun z hz => g0_zero_of_norm_ge hv_supp hz h
  have h1int : ∀ i : Fin n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) (abox n ℓ) MeasureTheory.volume :=
    fun i => integrableOn_w1Fibre_coord hℓ hgin hgsup hR.le hRℓ i
  have h2int : ∀ p ∈ pairSet n, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      wPairC ℓ v (x p.1) (x p.2)) (abox n ℓ) MeasureTheory.volume :=
    fun p hp => integrableOn_wPairC_pair hℓ hvin hvsup hRℓ (mem_pairSet.mp hp)
  have hW : ∀ x : Submission.BoseGases.X n,
      Work.BoseKinLoc.potWordU n v (g0 v h) ℓ μ 0 x
        = -μ * (∑ i : Fin n, w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
          + (1/2) * (∑ p ∈ pairSet n, wPairC ℓ v (x p.1) (x p.2)) := by
    intro x
    rw [← qLHSden_wPairC_eq_potWordU (v := v) (h := h) hvrad hℓ x]
    rfl
  constructor
  · rw [show (∑ i ∈ Finset.range n, ∫ x in abox n ℓ, Work.BoseFixB2.secProj ℓ i Φ x
          * Work.BoseFixB2.secProj ℓ (i+1) Φ x
          * Work.BoseKinLoc.potWordU n v (g0 v h) ℓ μ 0 x)
        = bandFun ℓ n (Work.BoseKinLoc.potWordU n v (g0 v h) ℓ μ 0) Φ from by
      unfold bandFun
      refine Finset.sum_congr rfl (fun i _ => ?_)
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring]
    rw [bandFun_congr_pt hW Φ]
    exact bandFun_qLHSden_eq hℓ (wPairC_v_sym hvrad ℓ) h1int h2int hΦ
  · rw [show (∑ i ∈ Finset.range (n-1), ∫ x in abox n ℓ, Work.BoseFixB2.secProj ℓ i Φ x
          * Work.BoseFixB2.secProj ℓ (i+2) Φ x
          * Work.BoseKinLoc.potWordU n v (g0 v h) ℓ μ 0 x)
        = bandFunTwo ℓ n (Work.BoseKinLoc.potWordU n v (g0 v h) ℓ μ 0) Φ from by
      unfold bandFunTwo
      refine Finset.sum_congr rfl (fun i _ => ?_)
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring]
    rw [bandFunTwo_congr_pt hW Φ]
    exact bandFunTwo_qLHSden_eq hℓ h1int h2int hΦ

end

end Work.BoseFixB2.DvApriori
