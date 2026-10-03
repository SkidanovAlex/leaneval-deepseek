import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs

namespace Work.KMTAreas.A4

open MeasureTheory

/-- **Covering pigeonhole for interval masses.**  Let `f ≥ 0` be integrable on `(0,1]`, let
`P : Set ℝ` be such that `P.indicator f` is integrable on `(0,1]`, and let `(b p)_{p ∈ pf}` be a
finite family of measurable subsets of the frequency circle `ℝ/ℤ` which *covers* `P` on `(0,1]` in
the sense that every `t ∈ (0,1] ∩ P` has `↑t ∈ b p` for some `p ∈ pf`.  If the mass of `P` is at
least `B`, then some member of the family carries at least the average mass `B / #pf`. -/
theorem coverMassLe {ι : Type*} [DecidableEq ι] {f : ℝ → ℝ} {B : ℝ} {P : Set ℝ}
    (pf : Finset ι) (hne : pf.Nonempty)
    {b : ι → Set Work.Analysis.InverseTheory.FreqCircle}
    (hb : ∀ p ∈ pf, MeasurableSet (b p))
    (hf0 : ∀ t : ℝ, 0 ≤ f t)
    (hfi : MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hPi : MeasureTheory.Integrable (Set.indicator P f) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (hB : 0 < B)
    (hcover : ∀ t ∈ Set.Ioc (0 : ℝ) 1, t ∈ P → ∃ p ∈ pf, ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p)
    (hint : B ≤ ∫ t in (0 : ℝ)..1, Set.indicator P f t) :
    ∃ p ∈ pf, B / (pf.card : ℝ) ≤ ∫ t in (0 : ℝ)..1,
      (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) t := by
  have hBpos : 0 < B := hB
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  -- pass from interval integrals to integrals over `Ioc 0 1`
  simp only [intervalIntegral.integral_of_le h01] at hint ⊢
  -- measurability of the pieces, hence integrability of each `𝕓 p`-mass
  have hmeas : ∀ p ∈ pf,
      MeasurableSet {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} :=
    fun p hp => (hb p hp).preimage QuotientAddGroup.measurable_coe
  have hInt : ∀ p ∈ pf, Integrable
      (fun t => (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) t)
      (volume.restrict (Set.Ioc 0 1)) :=
    fun p hp => hfi.indicator (hmeas p hp)
  have hsumInt : Integrable
      (fun t => ∑ p ∈ pf, (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) t)
      (volume.restrict (Set.Ioc 0 1)) :=
    integrable_finsetSum pf (fun p hp => hInt p hp)
  -- the pointwise covering inequality on `(0,1]`
  have hle_pt : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Set.indicator P f t ≤
        ∑ p ∈ pf, (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) t := by
    intro t ht
    have hnn : ∀ p ∈ pf, 0 ≤ (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) t :=
      fun p _ => Set.indicator_nonneg (fun s _ => hf0 s) t
    by_cases htP : t ∈ P
    · rw [Set.indicator_of_mem htP]
      obtain ⟨p, hp, hpb⟩ := hcover t ht htP
      have hpv : (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) t = f t :=
        Set.indicator_of_mem (s := {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p}) hpb f
      have hsingle : (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) t ≤
          ∑ i ∈ pf, (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b i} f) t :=
        Finset.single_le_sum (fun i hi => hnn i hi) hp
      rw [hpv] at hsingle
      exact hsingle
    · rw [Set.indicator_of_notMem htP]
      exact Finset.sum_nonneg (fun i hi => hnn i hi)
  have hle_int : ∫ x in Set.Ioc (0 : ℝ) 1, Set.indicator P f x ≤
      ∫ x in Set.Ioc (0 : ℝ) 1,
        ∑ p ∈ pf, (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) x :=
    setIntegral_mono_on hPi hsumInt measurableSet_Ioc hle_pt
  have hsplit : ∫ x in Set.Ioc (0 : ℝ) 1,
        (∑ p ∈ pf, (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) x)
      = ∑ p ∈ pf, ∫ x in Set.Ioc (0 : ℝ) 1,
          (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) x :=
    integral_finsetSum pf (fun p hp => hInt p hp)
  have hB_le_sum : B ≤ ∑ p ∈ pf, ∫ x in Set.Ioc (0 : ℝ) 1,
      (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) x :=
    calc B ≤ ∫ x in Set.Ioc (0 : ℝ) 1, Set.indicator P f x := hint
      _ ≤ _ := hle_int
      _ = _ := hsplit
  -- the pigeonhole step
  by_contra hcon
  push Not at hcon
  have hcard : (0 : ℝ) < (pf.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  have hlt : ∑ p ∈ pf, ∫ x in Set.Ioc (0 : ℝ) 1,
      (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) x < B := by
    have h2 := Finset.sum_lt_sum (s := pf)
      (f := fun p => ∫ x in Set.Ioc (0 : ℝ) 1,
        (Set.indicator {t : ℝ | ((t : ℝ) : Work.Analysis.InverseTheory.FreqCircle) ∈ b p} f) x)
      (g := fun _ => B / (pf.card : ℝ))
      (fun p hp => le_of_lt (hcon p hp))
      ⟨hne.choose, hne.choose_spec, hcon _ hne.choose_spec⟩
    rwa [Finset.sum_const, nsmul_eq_mul, mul_comm, div_mul_cancel₀ B (ne_of_gt hcard)] at h2
  linarith [hB_le_sum, hlt]

end Work.KMTAreas.A4
