import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.B3.fourierExp_shift_iVec
import Submission.Work.Diff.STE.B3.boxIdx_iUnion
import Submission.Work.Diff.STE.B3.boxIdx_pairwiseDisjoint
import Submission.Work.Diff.STE.B3.integrable_fourierExp_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Work.Diff.STE.B3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## Translation invariance of Lebesgue measure on `ι → ℝ` -/

/-- Translation is measure preserving for the Lebesgue measure on `ι → ℝ`. -/
lemma fcp_measurePreserving_add (c : ι → ℝ) :
    MeasurePreserving (fun y : ι → ℝ => y + c) (volume : Measure (ι → ℝ))
      (volume : Measure (ι → ℝ)) := by
  haveI : (MeasureSpace.volume : Measure (ι → ℝ)).IsAddHaarMeasure :=
    isAddHaarMeasure_volume_pi ι
  exact measurePreserving_add_right (MeasureSpace.volume : Measure (ι → ℝ)) c

/-- Change of variables `y ↦ y + c` in a set integral over `ι → ℝ`. -/
lemma fcp_setIntegral_comp_add (c : ι → ℝ) (s : Set (ι → ℝ)) (G : (ι → ℝ) → ℂ) :
    ∫ y in s, G (y + c) = ∫ z in (fun y : ι → ℝ => y + c) '' s, G z := by
  haveI : (MeasureSpace.volume : Measure (ι → ℝ)).IsAddHaarMeasure :=
    isAddHaarMeasure_volume_pi ι
  exact ((measurePreserving_add_right (MeasureSpace.volume : Measure (ι → ℝ)) c).setIntegral_image_emb
    (MeasurableEquiv.addRight c).measurableEmbedding G s).symm

/-- Integrability on the unit cube is preserved by translating the argument. -/
lemma fcp_integrableOn_comp_add {G : (ι → ℝ) → ℂ} (hG : Integrable G (volume : Measure (ι → ℝ)))
    (c : ι → ℝ) :
    IntegrableOn (fun y : ι → ℝ => G (y + c)) (Work.Diff.STE.unitCube (ι := ι))
      (volume : Measure (ι → ℝ)) := by
  haveI : (MeasureSpace.volume : Measure (ι → ℝ)).IsAddHaarMeasure :=
    isAddHaarMeasure_volume_pi ι
  have h := (MeasurePreserving.integrableOn_image
    (measurePreserving_add_right (MeasureSpace.volume : Measure (ι → ℝ)) c)
    (MeasurableEquiv.addRight c).measurableEmbedding
    (f := G) (s := Work.Diff.STE.unitCube (ι := ι))).mp hG.integrableOn
  exact h

/-- A translate of the unit cube is measurable. -/
lemma fcp_measurableSet_shift_unitCube (c : ι → ℝ) :
    MeasurableSet ((fun y : ι → ℝ => y + c) '' Work.Diff.STE.unitCube (ι := ι)) := by
  classical
  exact ((MeasurableEquiv.addRight c).measurableEmbedding.measurableSet_image).mpr
    BesselCont.measSet_unitCube

/-- **The Fourier coefficients of a periodisation.**  For `f` supported in the open cube
`(-1/2,1/2)^ι` and integrable, the `m`-th Fourier coefficient of the periodisation
`per f = Σ_k f (· + k)` is the integral of `f` against the character `e_{-m}` over the *centred*
cube:

  `fourierCoeff (per f) m = ∫_{(-1/2,1/2]^ι} e_{-m}(z) f(z) dz`.

Proof route: on the unit cube `(0,1]^ι` one has `per f = Σ_{k ∈ {-1,0}^ι} f (· + k)` (a finite
sum: if `xᵢ ∈ (0,1]` and `f (x + k) ≠ 0` then `xᵢ + kᵢ ∈ (-1/2,1/2)`, so `kᵢ ∈ {-1,0}`); integrate
term by term, substitute `y = x + k` in each term (the character is `1`-periodic, `k` is an integer
vector), and observe that the boxes `(0,1]^ι + k`, `k ∈ {-1,0}^ι`, are disjoint with union
`(-1,1]^ι ⊇ supp f`.  Hence the whole thing equals `∫_{ℝ^ι} e_{-m} f`, and since `f` is supported
in the open cube this is `∫_{(-1/2,1/2]^ι} e_{-m} f`. -/
theorem fourierCoeff_periodization
    {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℂ) (m : ι → ℤ)
    (hsupp : Function.support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (hf : MeasureTheory.Integrable f MeasureTheory.volume) :
    Work.Diff.STE.fourierCoeff (fun y => ∑' k : ι → ℤ, f (y + Work.Diff.STE.iVec k)) m
      = ∫ z in (Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1/2:ℝ)) (1/2))),
          Work.Diff.STE.fourierExp (-m) z * f z := by
  classical
  have hGint : Integrable (fun z : ι → ℝ => Work.Diff.STE.fourierExp (-m) z * f z)
      (volume : Measure (ι → ℝ)) := integrable_fourierExp_mul (-m) hf
  -- 1. the periodisation is a finite sum on the unit cube
  have hsplit : ∀ y ∈ Work.Diff.STE.unitCube (ι := ι),
      (∑' k : ι → ℤ, f (y + Work.Diff.STE.iVec k))
        = ∑ k ∈ Work.Diff.STE.csqp_boxIdx ι, f (y + Work.Diff.STE.iVec k) := by
    intro y hy
    refine Work.Diff.STE.csqp_periodization_eq_sum_boxIdx hsupp (fun i => ?_)
    have hi := Set.mem_pi.mp hy i (Set.mem_univ i)
    rw [Set.mem_Ioc] at hi
    rw [Set.mem_Ioo]
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  -- 2. rewrite the Fourier coefficient using that finite sum
  have h2 : Work.Diff.STE.fourierCoeff (fun y => ∑' k : ι → ℤ, f (y + Work.Diff.STE.iVec k)) m
      = ∫ y in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.fourierExp (-m) y *
          (∑ k ∈ Work.Diff.STE.csqp_boxIdx ι, f (y + Work.Diff.STE.iVec k)) := by
    rw [Work.Diff.STE.fourierCoeff]
    refine setIntegral_congr_fun BesselCont.measSet_unitCube (fun y hy => ?_)
    rw [hsplit y hy]
  -- 3. the heart: fold the lattice sum onto the big half-open box
  have h3 : ∫ y in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.fourierExp (-m) y *
        (∑ k ∈ Work.Diff.STE.csqp_boxIdx ι, f (y + Work.Diff.STE.iVec k))
      = ∫ z in Set.pi Set.univ (fun _ : ι => Set.Ioc (-1 : ℝ) 1),
          Work.Diff.STE.fourierExp (-m) z * f z := by
    -- the substitution `y ↦ y + k` in a single term
    have h3b : ∀ k ∈ Work.Diff.STE.csqp_boxIdx ι,
        ∫ y in Work.Diff.STE.unitCube (ι := ι),
            Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k)
          = ∫ z in (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube (ι := ι),
              Work.Diff.STE.fourierExp (-m) z * f z := by
      intro k _
      rw [show ∫ y in Work.Diff.STE.unitCube (ι := ι),
              Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k)
            = ∫ y in Work.Diff.STE.unitCube (ι := ι),
                (fun z : ι → ℝ => Work.Diff.STE.fourierExp (-m) z * f z)
                  (y + Work.Diff.STE.iVec k) from
          setIntegral_congr_fun BesselCont.measSet_unitCube (fun y _ => by
            show Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k)
              = Work.Diff.STE.fourierExp (-m) (y + Work.Diff.STE.iVec k) * f (y + Work.Diff.STE.iVec k)
            rw [fourierExp_shift_iVec (-m) k y])]
      exact fcp_setIntegral_comp_add (Work.Diff.STE.iVec k) (Work.Diff.STE.unitCube (ι := ι))
        (fun z : ι → ℝ => Work.Diff.STE.fourierExp (-m) z * f z)
    -- the translates form a disjoint union
    have h3c : ∑ k ∈ Work.Diff.STE.csqp_boxIdx ι,
        ∫ z in (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube (ι := ι),
            Work.Diff.STE.fourierExp (-m) z * f z
      = ∫ z in ⋃ k ∈ Work.Diff.STE.csqp_boxIdx ι,
            (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube (ι := ι),
            Work.Diff.STE.fourierExp (-m) z * f z := by
      refine (integral_biUnion_finset (Work.Diff.STE.csqp_boxIdx ι)
        (s := fun k : ι → ℤ =>
          (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube (ι := ι))
        (fun k _ => fcp_measurableSet_shift_unitCube (Work.Diff.STE.iVec k))
        (boxIdx_pairwiseDisjoint (ι := ι))
        (fun k _ => hGint.integrableOn)).symm
    calc ∫ y in Work.Diff.STE.unitCube (ι := ι), Work.Diff.STE.fourierExp (-m) y *
          (∑ k ∈ Work.Diff.STE.csqp_boxIdx ι, f (y + Work.Diff.STE.iVec k))
        = ∫ y in Work.Diff.STE.unitCube (ι := ι), ∑ k ∈ Work.Diff.STE.csqp_boxIdx ι,
            Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k) := by
          refine setIntegral_congr_fun BesselCont.measSet_unitCube (fun y _ => ?_)
          exact (Finset.mul_sum (Work.Diff.STE.csqp_boxIdx ι)
            (fun k => f (y + Work.Diff.STE.iVec k)) (Work.Diff.STE.fourierExp (-m) y))
      _ = ∑ k ∈ Work.Diff.STE.csqp_boxIdx ι, ∫ y in Work.Diff.STE.unitCube (ι := ι),
            Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k) := by
          refine integral_finsetSum (Work.Diff.STE.csqp_boxIdx ι)
            (f := fun k (y : ι → ℝ) => Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k))
            (fun k _ => ?_)
          have hcongr : (fun y : ι → ℝ => Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k))
              = fun y : ι → ℝ => (fun z : ι → ℝ => Work.Diff.STE.fourierExp (-m) z * f z)
                  (y + Work.Diff.STE.iVec k) := by
            funext y
            show Work.Diff.STE.fourierExp (-m) y * f (y + Work.Diff.STE.iVec k)
              = Work.Diff.STE.fourierExp (-m) (y + Work.Diff.STE.iVec k) * f (y + Work.Diff.STE.iVec k)
            rw [fourierExp_shift_iVec (-m) k y]
          rw [hcongr]
          exact fcp_integrableOn_comp_add hGint (Work.Diff.STE.iVec k)
      _ = ∑ k ∈ Work.Diff.STE.csqp_boxIdx ι,
            ∫ z in (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube (ι := ι),
              Work.Diff.STE.fourierExp (-m) z * f z :=
          Finset.sum_congr rfl (fun k hk => h3b k hk)
      _ = ∫ z in ⋃ k ∈ Work.Diff.STE.csqp_boxIdx ι,
            (fun y : ι → ℝ => y + Work.Diff.STE.iVec k) '' Work.Diff.STE.unitCube (ι := ι),
            Work.Diff.STE.fourierExp (-m) z * f z := h3c
      _ = ∫ z in Set.pi Set.univ (fun _ : ι => Set.Ioc (-1 : ℝ) 1),
            Work.Diff.STE.fourierExp (-m) z * f z := by rw [boxIdx_iUnion (ι := ι)]
  -- 4. the integrand vanishes off the support of `f`
  have hvan : ∀ (s : Set (ι → ℝ)), (∀ z, f z ≠ 0 → z ∈ s) →
      ∀ z ∉ s, Work.Diff.STE.fourierExp (-m) z * f z = 0 := by
    intro s hs z hz
    have hfz : f z = 0 := by
      by_contra hne
      exact hz (hs z hne)
    rw [hfz, mul_zero]
  have hbig : ∀ z ∉ Set.pi Set.univ (fun _ : ι => Set.Ioc (-1 : ℝ) 1),
      Work.Diff.STE.fourierExp (-m) z * f z = 0 :=
    hvan _ (fun z hz => fun i _ => by
      have hi := Set.mem_pi.mp (hsupp hz) i (Set.mem_univ i)
      rw [Set.mem_Ioo] at hi
      rw [Set.mem_Ioc]
      exact ⟨by linarith [hi.1], by linarith [hi.2]⟩)
  have hsmall : ∀ z ∉ Set.pi Set.univ (fun _ : ι => Set.Ioc (-(1/2:ℝ)) (1/2)),
      Work.Diff.STE.fourierExp (-m) z * f z = 0 :=
    hvan _ (fun z hz => fun i _ => by
      have hi := Set.mem_pi.mp (hsupp hz) i (Set.mem_univ i)
      rw [Set.mem_Ioo] at hi
      rw [Set.mem_Ioc]
      exact ⟨hi.1, le_of_lt hi.2⟩)
  rw [h2, h3]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hbig,
    setIntegral_eq_integral_of_forall_compl_eq_zero hsmall]

end Work.Diff.STE.B3
