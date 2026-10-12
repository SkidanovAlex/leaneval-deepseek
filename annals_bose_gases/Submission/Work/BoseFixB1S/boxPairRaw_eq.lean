import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.integrableOn_boxFragments
import Submission.Work.BoseFixB1S.pairRaw_eq_sumPairInts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The indicator collapse -/

/-- If the kernel `w` vanishes off `A × A`, the two box indicators of the `fgsum` identity can
be dropped from the pair integrand. -/
theorem Aind_pair_mul_eq {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hsuppA : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y ≠ 0 → x ∈ A ∧ y ∈ A) (c : ℝ)
    (y z : EuclideanSpace ℝ (Fin 3)) :
    Aind A y * Aind A z * c * w y z = c * w y z := by
  by_cases h : w y z = 0
  · rw [h]; ring
  · obtain ⟨hy, hz⟩ := hsuppA y z h
    unfold Aind
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hz]
    ring

/-! ## The seven fragments at one orientation, summed -/

/-- The seven box-pair fragments at the orientation `(i,j)`, summed as a function of the
configuration. -/
def pairFrags {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : X N → ℝ) (i j : Fin N) (x : X N) : ℝ :=
  fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x + fg2a volA A w2 Φ i j x
    + fg2b volA A w2 Φ i j x + fg2c volA A w1 Φ i j x + fg3 volA A w1 Φ i j x
    + fg4 volA A w om Φ i j x

/-- `fgsum` is the sum of the two orientations of the seven fragments. -/
theorem fgsum_eq_pairFrags {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : X N → ℝ) (i j : Fin N) (x : X N) :
    fgsum volA A w w1 w2 om Φ i j x
      = pairFrags volA A w w1 w2 om Φ i j x
        + pairFrags volA A w w1 w2 om Φ j i x := by
  simp only [fgsum, pairFrags]
  ring

/-! ## The per-pair identity -/

/-- **The pair identity at the box projections**: for distinct slots `i ≠ j`, the two
orientations of the fourteen word fragments integrate to the flat two-body expectation
`∫ Φ²·w(xᵢ,xⱼ)`. -/
theorem pairInts_add_swap_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w p.1 p.2))
    (homc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => om p.1 p.2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    (hw1rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w2 x y = w x y * (1 - om x y ^ 2))
    (hsuppA : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) {i j : Fin N} (hij : i ≠ j) :
    Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ i j
        + Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ j i
      = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x i) (x j) := by
  obtain ⟨I0, I1, I2a, I2b, I2c, I3, I4⟩ :=
    integrableOn_boxFragments hℓ hvol hA hvolA hAc hwc homc hw1rel hw2rel hΦc i j
  obtain ⟨J0, J1, J2a, J2b, J2c, J3, J4⟩ :=
    integrableOn_boxFragments hℓ hvol hA hvolA hAc hwc homc hw1rel hw2rel hΦc j i
  -- partial sums, first orientation
  have P1 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x) (abox N ℓ) volume := I0.add I1
  have P2 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x + fg2a volA A w2 Φ i j x)
      (abox N ℓ) volume := P1.add I2a
  have P3 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x + fg2a volA A w2 Φ i j x
        + fg2b volA A w2 Φ i j x) (abox N ℓ) volume := P2.add I2b
  have P4 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x + fg2a volA A w2 Φ i j x
        + fg2b volA A w2 Φ i j x + fg2c volA A w1 Φ i j x) (abox N ℓ) volume := P3.add I2c
  have P5 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x + fg2a volA A w2 Φ i j x
        + fg2b volA A w2 Φ i j x + fg2c volA A w1 Φ i j x + fg3 volA A w1 Φ i j x)
      (abox N ℓ) volume := P4.add I3
  have P6 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ i j x + fg1 volA A w2 Φ i j x + fg2a volA A w2 Φ i j x
        + fg2b volA A w2 Φ i j x + fg2c volA A w1 Φ i j x + fg3 volA A w1 Φ i j x
        + fg4 volA A w om Φ i j x) (abox N ℓ) volume := P5.add I4
  -- partial sums, second orientation
  have Q1 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ j i x + fg1 volA A w2 Φ j i x) (abox N ℓ) volume := J0.add J1
  have Q2 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ j i x + fg1 volA A w2 Φ j i x + fg2a volA A w2 Φ j i x)
      (abox N ℓ) volume := Q1.add J2a
  have Q3 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ j i x + fg1 volA A w2 Φ j i x + fg2a volA A w2 Φ j i x
        + fg2b volA A w2 Φ j i x) (abox N ℓ) volume := Q2.add J2b
  have Q4 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ j i x + fg1 volA A w2 Φ j i x + fg2a volA A w2 Φ j i x
        + fg2b volA A w2 Φ j i x + fg2c volA A w1 Φ j i x) (abox N ℓ) volume := Q3.add J2c
  have Q5 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ j i x + fg1 volA A w2 Φ j i x + fg2a volA A w2 Φ j i x
        + fg2b volA A w2 Φ j i x + fg2c volA A w1 Φ j i x + fg3 volA A w1 Φ j i x)
      (abox N ℓ) volume := Q4.add J3
  have Q6 : IntegrableOn (fun x : X N =>
      fg0 volA A w2 Φ j i x + fg1 volA A w2 Φ j i x + fg2a volA A w2 Φ j i x
        + fg2b volA A w2 Φ j i x + fg2c volA A w1 Φ j i x + fg3 volA A w1 Φ j i x
        + fg4 volA A w om Φ j i x) (abox N ℓ) volume := Q5.add J4
  -- collapse each `pairInts` into a single integral
  have hPGi : Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ i j
      = ∫ x in abox N ℓ, pairFrags volA A w w1 w2 om Φ i j x := by
    unfold pairInts pairFrags
    rw [← integral_add I0 I1]
    rw [← integral_add P1 I2a]
    rw [← integral_add P2 I2b]
    rw [← integral_add P3 I2c]
    rw [← integral_add P4 I3]
    rw [← integral_add P5 I4]
  have hPGj : Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ j i
      = ∫ x in abox N ℓ, pairFrags volA A w w1 w2 om Φ j i x := by
    unfold pairInts pairFrags
    rw [← integral_add J0 J1]
    rw [← integral_add Q1 J2a]
    rw [← integral_add Q2 J2b]
    rw [← integral_add Q3 J2c]
    rw [← integral_add Q4 J3]
    rw [← integral_add Q5 J4]
  have hPGi' : IntegrableOn (fun x : X N => pairFrags volA A w w1 w2 om Φ i j x)
      (abox N ℓ) volume := by
    unfold pairFrags
    exact P6
  have hPGj' : IntegrableOn (fun x : X N => pairFrags volA A w w1 w2 om Φ j i x)
      (abox N ℓ) volume := by
    unfold pairFrags
    exact Q6
  calc Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ i j
        + Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ j i
      = (∫ x in abox N ℓ, pairFrags volA A w w1 w2 om Φ i j x)
        + (∫ x in abox N ℓ, pairFrags volA A w w1 w2 om Φ j i x) := by rw [hPGi, hPGj]
    _ = ∫ x in abox N ℓ,
          (pairFrags volA A w w1 w2 om Φ i j x
            + pairFrags volA A w w1 w2 om Φ j i x) := by rw [integral_add hPGi' hPGj']
    _ = ∫ x in abox N ℓ, fgsum volA A w w1 w2 om Φ i j x := by
      apply MeasureTheory.setIntegral_congr_fun (abox_measurable N ℓ)
      intro x hx
      exact (fgsum_eq_pairFrags volA A w w1 w2 om Φ i j x).symm
    _ = ∫ x in abox N ℓ,
          Aind A (x i) * Aind A (x j) * (Φ x) ^ 2 * w (x i) (x j) := by
      apply MeasureTheory.setIntegral_congr_fun (abox_measurable N ℓ)
      intro x hx
      exact boxPairPointwise hℓ hvol hA hvolA hAc hwsym homsym hw1rel hw2rel hij hΦc x hx
    _ = ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x i) (x j) := by
      apply MeasureTheory.setIntegral_congr_fun (abox_measurable N ℓ)
      intro x hx
      exact Aind_pair_mul_eq hsuppA ((Φ x) ^ 2) (x i) (x j)

/-! ## The main theorem -/

theorem boxPairRaw_eq {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => w p.1 p.2))
    (homc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => om p.1 p.2))
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    (hw1rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w2 x y = w x y * (1 - om x y ^ 2))
    (hsuppA : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.pairRaw volA ℓ A w w1 w2 om Φ
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
          ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
  have hswap : (∑ p ∈ pairSet N, Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.2 p.1)
      = ∑ p ∈ pairSet N, Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.1 p.2 :=
    pairSet_swap_sum (N := N) (fun p : Fin N × Fin N =>
      Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.1 p.2)
  calc Work.BoseFixB1S.pairRaw volA ℓ A w w1 w2 om Φ
      = ∑ p ∈ pairSet N, Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.1 p.2 :=
        pairRaw_eq_sumPairInts volA ℓ A w w1 w2 om Φ
    _ = (1 / 2) * (∑ p ∈ pairSet N,
          (Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.1 p.2
            + Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ p.2 p.1)) := by
        rw [Finset.sum_add_distrib, hswap]
        ring
    _ = (1 / 2) * (∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        have hpne : p.1 ≠ p.2 := by simpa [pairSet] using hp
        exact pairInts_add_swap_eq hℓ hvol hA hvolA hAc hwc homc hwsym homsym hw1rel hw2rel
          hsuppA hΦc hpne

end Work.BoseFixB1S
