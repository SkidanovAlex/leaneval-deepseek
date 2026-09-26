import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.TorusCover.ParamTorus_exists_liftOf

/-!
# The pieces of the preimage of a union of inessential simple curves

Let `γ i` (`i : Fin n`) be pairwise disjoint *simple* closed curves of the torus
`F = P.carrier` which are *inessential*, i.e. whose winding vector vanishes.  Such a curve
`γ i` lifts to a `2π`-periodic map `liftMap (L i) : ℝ → ℂ` of the parameter plane, whose
image over one period is a compact connected "piece" `curveSet (L i)`; the preimage of the
whole curve is the disjoint union of the translates of this piece by the lattice
`2π(ℤ + iℤ)`.

This is the geometric skeleton of the dichotomy for the winding span of a region bounded by
inessential curves: the preimage of the union of the curves is a *locally finite disjoint
union of compact connected pieces*.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- Every real number can be shifted by an integer multiple of `2π` into `[0, 2π)`. -/
theorem exists_int_shift_mem_Ico (x : ℝ) :
    ∃ k : ℤ, x + (k : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨-⌊x / (2 * Real.pi)⌋, ?_⟩
  have hx : x + ((-⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) =
      (2 * Real.pi) * Int.fract (x / (2 * Real.pi)) := by
    rw [Int.fract]; push_cast; field_simp; ring
  rw [Set.mem_Ico, hx]
  constructor
  · exact mul_nonneg (le_of_lt hπ) (Int.fract_nonneg _)
  · have h1 := Int.fract_lt_one (x / (2 * Real.pi))
    nlinarith [Real.pi_pos]

/-! ## Lifts of a closed curve to the parameter plane -/

/-- The lift of a closed curve of a parametrised torus, read as a curve of the parameter plane
`ℂ`. -/
def liftMap {P : Work.CoreTopology.ParamTorus} {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) : ℝ → ℂ :=
  fun t => ((L.Θ t : ℝ) : ℂ) + ((L.Φ t : ℝ) : ℂ) * Complex.I

@[simp] theorem liftMap_re {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) (t : ℝ) :
    (liftMap L t).re = L.Θ t := by
  simp [liftMap]

@[simp] theorem liftMap_im {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) (t : ℝ) :
    (liftMap L t).im = L.Φ t := by
  simp [liftMap]

theorem continuous_liftMap {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) :
    Continuous (liftMap L) :=
  (Complex.continuous_ofReal.comp L.contΘ).add
    ((Complex.continuous_ofReal.comp L.contΦ).mul continuous_const)

theorem planePsi_liftMap {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) (t : ℝ) :
    planePsi P (liftMap L t) = γ.γ t := by
  rw [planePsi_apply, liftMap_re, liftMap_im, L.lifts]

theorem liftMap_add_two_pi {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ)
    (hL : L.winding = 0) (t : ℝ) : liftMap L (t + 2 * Real.pi) = liftMap L t := by
  have h1 := L.period_shift_winding t
  rw [hL] at h1
  simp only [Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_mul, add_zero] at h1
  exact Complex.ext (by simp [h1.1]) (by simp [h1.2])

theorem liftMap_periodic {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ)
    (hL : L.winding = 0) : Function.Periodic (liftMap L) (2 * Real.pi) :=
  liftMap_add_two_pi L hL

/-- Shifting a lift by an integer number of periods does not change it. -/
theorem liftMap_int_mul {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ)
    (hL : L.winding = 0) (k : ℤ) (t : ℝ) :
    liftMap L (t + (k : ℝ) * (2 * Real.pi)) = liftMap L t :=
  (liftMap_periodic L hL).int_mul k t

/-! ## The piece cut out by one curve, and its translates -/

/-- The compact connected piece of the parameter plane cut out by one lift over one period. -/
def curveSet {P : Work.CoreTopology.ParamTorus} {γ : Work.CoreTopology.ClosedCurve P}
    (L : Work.CoreTopology.LiftOf P γ) : Set ℂ :=
  liftMap L '' Set.Icc (0 : ℝ) (2 * Real.pi)

theorem curveSet_compact {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) :
    IsCompact (curveSet L) :=
  isCompact_Icc.image_of_continuousOn (continuous_liftMap L).continuousOn

theorem curveSet_preconnected {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) :
    IsPreconnected (curveSet L) :=
  isPreconnected_Icc.image _ (continuous_liftMap L).continuousOn

/-- The translate of a subset of the plane by a vector. -/
def translate (ν : ℂ) (S : Set ℂ) : Set ℂ := (fun z => z + ν) '' S

@[simp] theorem mem_translate (ν : ℂ) (S : Set ℂ) (z : ℂ) :
    z ∈ translate ν S ↔ z - ν ∈ S := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨z - ν, hz, by ring⟩

theorem translate_compact (ν : ℂ) {S : Set ℂ} (hS : IsCompact S) :
    IsCompact (translate ν S) :=
  hS.image (continuous_id.add continuous_const)

theorem translate_preconnected (ν : ℂ) {S : Set ℂ} (hS : IsPreconnected S) :
    IsPreconnected (translate ν S) :=
  hS.image _ (continuous_id.add continuous_const).continuousOn

theorem translate_mono (ν : ℂ) {S T : Set ℂ} (h : S ⊆ T) : translate ν S ⊆ translate ν T :=
  Set.image_mono h

/-! ## The chosen lifts of the curves -/

/-- A chosen lift of a closed curve to the parameter plane. -/
def chosenLift (P : Work.CoreTopology.ParamTorus) (γ : Work.CoreTopology.ClosedCurve P) :
    Work.CoreTopology.LiftOf P γ :=
  Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ)

theorem chosenLift_winding {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (h : ¬ Work.CoreTopology.IsEssential P γ) :
    (chosenLift P γ).winding = (0, 0) := by
  by_contra hne
  exact h ⟨chosenLift P γ, hne⟩

/-! ## The preimage of a union of curves as a union of pieces -/

/-- The translate of the piece of `γ` by a lattice vector lies in the preimage of the curve. -/
theorem translate_curveSet_subset_Xtilde {P : Work.CoreTopology.ParamTorus}
    {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ)
    {ν : ℂ} (hν : ν ∈ periodLattice) :
    translate ν (curveSet L) ⊆ Xtilde P (Set.range γ.γ) := by
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨t, -, rfl⟩ := hw
  show planePsi P (liftMap L t + ν) ∈ Set.range γ.γ
  rw [planePsi_add_periodLattice P (liftMap L t) ν hν, planePsi_liftMap]
  exact ⟨t, rfl⟩

/-- **The preimage of a union of inessential simple curves is the union of the translates of
the pieces cut out by the chosen lifts.** -/
theorem Xtilde_iUnion_eq {P : Work.CoreTopology.ParamTorus} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (L : ∀ i, Work.CoreTopology.LiftOf P (γ i)) (hL : ∀ i, (L i).winding = 0) :
    Xtilde P (⋃ i, Set.range (γ i).γ) =
      ⋃ i, ⋃ ν ∈ periodLattice, translate ν (curveSet (L i)) := by
  ext z
  constructor
  · intro hz
    have hz' : planePsi P z ∈ ⋃ i, Set.range (γ i).γ := hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz'
    obtain ⟨t, ht⟩ := Set.mem_range.mp hi
    -- reduce `t` into the fundamental period
    obtain ⟨k, hk⟩ := exists_int_shift_mem_Ico t
    set t₀ : ℝ := t + (k : ℝ) * (2 * Real.pi) with ht₀
    have ht₀mem : t₀ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := hk
    have ht_eq : t = t₀ - (k : ℝ) * (2 * Real.pi) := by rw [ht₀]; ring
    have hlift : liftMap (L i) t = liftMap (L i) t₀ := by
      rw [ht_eq]
      rw [show t₀ - (k : ℝ) * (2 * Real.pi) = t₀ + (-k : ℤ) * (2 * Real.pi) by
        push_cast; ring]
      exact liftMap_int_mul (L i) (hL i) (-k) t₀
    -- the two parameter points have the same image under the parametrisation
    have hsame : planePsi P (liftMap (L i) t₀) = planePsi P z := by
      rw [← hlift, planePsi_liftMap]
      exact ht
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (P.psi_eq_iff _ _ _ _).mp hsame
    have hz_eq : z = liftMap (L i) t₀ + periodPt (-a) (-b) := by
      have h3 : z.re = (liftMap (L i) t₀).re - (a : ℝ) * (2 * Real.pi) := by
        have h1 : (liftMap (L i) t₀).re = z.re + (a : ℝ) * (2 * Real.pi) := by simpa using ha
        linarith
      have h4 : z.im = (liftMap (L i) t₀).im - (b : ℝ) * (2 * Real.pi) := by
        have h1 : (liftMap (L i) t₀).im = z.im + (b : ℝ) * (2 * Real.pi) := by simpa using hb
        linarith
      apply Complex.ext
      · rw [h3, liftMap_re, Complex.add_re, liftMap_re, periodPt_re]
        push_cast; ring
      · rw [h4, liftMap_im, Complex.add_im, liftMap_im, periodPt_im]
        push_cast; ring
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine Set.mem_iUnion.mpr ⟨periodPt (-a) (-b), ?_⟩
    refine Set.mem_iUnion.mpr ⟨Set.mem_range.mpr ⟨(-a, -b), rfl⟩, ?_⟩
    rw [mem_translate]
    exact ⟨t₀, ⟨⟨ht₀mem.1, ht₀mem.2.le⟩, by rw [hz_eq]; simp⟩⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨ν, hν⟩ := Set.mem_iUnion.mp hi
    obtain ⟨hνmem, hmem⟩ := Set.mem_iUnion.mp hν
    exact Xtilde_mono P (Set.subset_iUnion (fun i => Set.range (γ i).γ) i)
      (translate_curveSet_subset_Xtilde (L i) hνmem hmem)

/-- Every point of the preimage of the union of the curves lies in one of the pieces. -/
theorem exists_piece_of_mem {P : Work.CoreTopology.ParamTorus} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (L : ∀ i, Work.CoreTopology.LiftOf P (γ i)) (hL : ∀ i, (L i).winding = 0)
    {z : ℂ} (hz : z ∈ Xtilde P (⋃ i, Set.range (γ i).γ)) :
    ∃ i : Fin n, ∃ ν ∈ periodLattice, z ∈ translate ν (curveSet (L i)) := by
  rw [Xtilde_iUnion_eq L hL] at hz
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
  obtain ⟨ν, hν⟩ := Set.mem_iUnion.mp hi
  obtain ⟨hνmem, hmem⟩ := Set.mem_iUnion.mp hν
  exact ⟨i, ν, hνmem, hmem⟩

/-! ## Distinct pieces are disjoint -/

theorem planePsi_eq_of_mem_periodLattice {P : Work.CoreTopology.ParamTorus} {z w : ℂ}
    (h : w - z ∈ periodLattice) : planePsi P w = planePsi P z := by
  obtain ⟨a, b, hab⟩ := (mem_periodLattice _).mp h
  have h2 : w - z = periodPt a b := hab.symm
  have h1 : w = z + periodPt a b := by rw [← h2]; ring
  rw [h1, planePsi_add_periodPt]

/-- **Two distinct pieces are disjoint.**  This uses that the curves are simple (so that the
translates of one lift are disjoint) and pairwise disjoint (so that different curves give
disjoint pieces). -/
theorem translate_curveSet_disjoint {P : Work.CoreTopology.ParamTorus} {n : ℕ}
    {γ : Fin n → Work.CoreTopology.ClosedCurve P}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (γ i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ))
    (L : ∀ i, Work.CoreTopology.LiftOf P (γ i)) (hL : ∀ i, (L i).winding = 0)
    {i j : Fin n} {ν ν' : ℂ} (hν : ν ∈ periodLattice) (hν' : ν' ∈ periodLattice)
    (h : (i, ν) ≠ (j, ν')) :
    Disjoint (translate ν (curveSet (L i))) (translate ν' (curveSet (L j))) := by
  rw [Set.disjoint_left]
  rintro z ⟨w, hw, hzw⟩ ⟨w', hw', hzw'⟩
  obtain ⟨s, hs, rfl⟩ := hw
  obtain ⟨t, ht, rfl⟩ := hw'
  have hzi : z = liftMap (L i) s + ν := by rw [← hzw]
  have hzj : z = liftMap (L j) t + ν' := by rw [← hzw']
  have hsame : planePsi P (liftMap (L i) s) = planePsi P (liftMap (L j) t) := by
    have h1 : planePsi P (liftMap (L i) s + ν) = planePsi P (liftMap (L j) t + ν') := by
      rw [← hzi, ← hzj]
    rw [planePsi_add_periodLattice P (liftMap (L i) s) ν hν,
      planePsi_add_periodLattice P (liftMap (L j) t) ν' hν'] at h1
    exact h1
  by_cases hij : i = j
  · -- the same curve: the translate vectors differ
    have hsame_i : planePsi P (liftMap (L i) s) = planePsi P (liftMap (L i) t) := by
      rw [← hij] at hsame
      exact hsame
    have hzj_i : z = liftMap (L i) t + ν' := by
      rw [← hij] at hzj
      exact hzj
    have hνne : ν ≠ ν' := by
      intro hνν
      exact h (by rw [hij, hνν])
    have hne0 : liftMap (L i) s ≠ liftMap (L i) t := by
      intro heq
      apply hνne
      have h1 : liftMap (L i) s + ν = liftMap (L i) t + ν' := by rw [← hzi, ← hzj_i]
      rw [heq] at h1
      exact add_left_cancel h1
    obtain ⟨ks, hks⟩ := exists_int_shift_mem_Ico s
    obtain ⟨kt, hkt⟩ := exists_int_shift_mem_Ico t
    set s₀ : ℝ := s + (ks : ℝ) * (2 * Real.pi) with hs₀
    set t₀ : ℝ := t + (kt : ℝ) * (2 * Real.pi) with ht₀
    have hs_eq : liftMap (L i) s = liftMap (L i) s₀ := by
      rw [hs₀]; exact (liftMap_int_mul (L i) (hL i) ks s).symm
    have ht_eq : liftMap (L i) t = liftMap (L i) t₀ := by
      rw [ht₀]; exact (liftMap_int_mul (L i) (hL i) kt t).symm
    have hsame' : planePsi P (liftMap (L i) s₀) = planePsi P (liftMap (L i) t₀) := by
      rw [← hs_eq, ← ht_eq]
      exact hsame_i
    have hγ : γ i s₀ = γ i t₀ := by
      have h1 := hsame'
      rwa [planePsi_liftMap, planePsi_liftMap] at h1
    have hinj : s₀ = t₀ := hsimple i hks hkt hγ
    exact hne0 (by rw [hs_eq, ht_eq, hinj])
  · -- different curves
    have h1 : planePsi P (liftMap (L i) s) ∈ Set.range (γ i).γ := by
      rw [planePsi_liftMap]; exact ⟨s, rfl⟩
    have h2 : planePsi P (liftMap (L j) t) ∈ Set.range (γ j).γ := by
      rw [planePsi_liftMap]; exact ⟨t, rfl⟩
    rw [hsame] at h1
    exact (Set.disjoint_left.mp (hdisj i j hij) h1) h2

end

end Work.BoxShrink.PinchOff
