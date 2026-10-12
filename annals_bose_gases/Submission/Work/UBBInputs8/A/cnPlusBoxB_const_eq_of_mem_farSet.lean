import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The far set empties the box.**  FS's sliding boxes are
`B(u) = acube ℓ ∩ ((ℓd)•u + acube(ℓd))` (`Submission.BoseGases.dlBox`).  If some coordinate of
`w = (ℓd)•u` exceeds the outer half-side `½ℓ(1+d)` — membership in `farSet` — then the two cubes
do not meet, so `B(u) = ∅`.  (Same triangle-inequality computation as the corpus's
`Work.SmallBoxSliding.farSet_chiSmallB_zero`.) -/
theorem dlBox_eq_empty_of_mem_farSet_aux {ℓ d μ : ℝ} (_hℓ : 0 < ℓ) (_hd : 0 < d)
    {u : ℝ³} (hu : u ∈ Work.SmallBoxSliding.farSet ℓ d μ) :
    Submission.BoseGases.dlBox ℓ d u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [Submission.BoseGases.mem_dlBox_iff] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [Submission.BoseGases.mem_acube_iff] at hx1 hx2
  obtain ⟨j, hj⟩ := hu
  have h1 : |x j| ≤ ℓ / 2 := by
    have h := hx1 j; rw [Set.mem_Icc] at h
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have h2 : |(x - (ℓ * d) • u) j| ≤ (ℓ * d) / 2 := by
    have h := hx2 j; rw [Set.mem_Icc] at h
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have htri : |((ℓ * d) • u) j| ≤ |x j| + |(x - (ℓ * d) • u) j| := by
    have hsplit : ((ℓ * d) • u) j = x j - (x - (ℓ * d) • u) j := by simp
    rw [hsplit, sub_eq_add_neg]
    calc |x j + -(x - (ℓ * d) • u) j| ≤ |x j| + |-(x - (ℓ * d) • u) j| := abs_add_le _ _
      _ = |x j| + |(x - (ℓ * d) • u) j| := by rw [abs_neg]
  nlinarith [hj, h1, h2, htri]

/-- The Bochner integral of the constant `1` over the ambient box is the (real) volume of
that box. -/
theorem integral_one_abox {N : ℕ} (a : ℝ) :
    (∫ _ in Submission.BoseGases.abox N a, (1 : ℝ))
      = ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))
          (Submission.BoseGases.abox N a)).toReal := by
  rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def]
  simp

/-- The mean-free projection `boxQ` over the empty box is the identity: `boxP` vanishes on
`∅` (its defining integral is `0`), so `boxQ volA ∅ i Φ = Φ`. -/
theorem boxQ_empty_aux (volA : ℝ) {N : ℕ} (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.SmallBoxTBWord.boxQ volA (∅ : Set ℝ³) i Φ = Φ := by
  funext x
  simp [Work.SmallBoxTBWord.boxQ, Work.SmallBoxTBWord.boxP]

/-! Round 8, strand A (the kinetic clause audit).

The corpus's mean-free projection `Work.SmallBoxTBWord.boxQ volA A i Φ = Φ − boxP` carries *no*
box indicator (`boxP volA A i Φ x = (1/volA) ∫_{z ∈ A} Φ (x_{i←z}) dz`), unlike FS's
`Q_B = 1_B − P_B` (`final_v2.tex` §5).  Consequently, on the far set (`dlBox ℓ d u = ∅`, so the
box mean is `0`) the corpus's projection acts as the identity:
`boxQ volA ∅ i Φ = Φ`.  This statement records the resulting value of the corpus's excited count
`cnPlusBoxB N ℓ d u` at the constant state: `n₊(B) = N · |abox N ℓ|`, the quantity that is *not*
`0` although the box is empty. -/
theorem cnPlusBoxB_const_eq_of_mem_farSet {N : ℕ} {ℓ d μ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.farSet ℓ d μ) :
    Work.SmallBoxTBWord.cnPlusBoxB N ℓ d u (fun _ : Submission.BoseGases.X N => (1 : ℝ))
      = (N : ℝ) * ((MeasureTheory.volume : MeasureTheory.Measure
          (Submission.BoseGases.X N)) (Submission.BoseGases.abox N ℓ)).toReal := by
  have hbox : Submission.BoseGases.dlBox ℓ d u = ∅ :=
    dlBox_eq_empty_of_mem_farSet_aux hℓ hd hu
  rw [Work.SmallBoxTBWord.cnPlusBoxB, Work.SmallBoxTBWord.cnPlusBox, hbox]
  have hmain : ∀ i : Fin N, (∫ x in Submission.BoseGases.abox N ℓ,
      (Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u) ∅ i
        (fun _ : Submission.BoseGases.X N => (1 : ℝ)) x) ^ 2)
      = ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N))
          (Submission.BoseGases.abox N ℓ)).toReal := by
    intro i
    rw [boxQ_empty_aux]
    simpa using integral_one_abox ℓ
  rw [Finset.sum_congr rfl (fun i _ => hmain i)]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Work.UBBInputs8.A
