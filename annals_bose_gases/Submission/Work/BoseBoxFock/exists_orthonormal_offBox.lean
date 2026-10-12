import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.exists_orthonormal_offBox`

For every `ℓ > 0` and every `m : ℕ` there is a family `b : Fin m → ℝ³ → ℂ` of
`L²`-functions which

* are orthonormal for the (conjugate-linear-in-the-first-argument) inner product
  `⟪f, g⟫ = ∫ star (f x) * g x`,
* and **vanish identically on the box** `Λ(ℓ) = boxL corpusBox ℓ = ℓ • cell`.

This is the "orthonormal family supported off the box" that the second-quantisation
dictionary of FS §8 needs (test vectors for the excitations outside the condensate).

## The construction

`cell` is compact, hence bounded: `cell ⊆ closedBall 0 R`.  Then
`Λ(ℓ) ⊆ closedBall 0 (|ℓ| R)`, so every point of the box has first coordinate
`< K := |ℓ| R + 1` (a coordinate of a vector is bounded by its norm,
`PiLp.norm_apply_le`).

For `i : ℕ` let

`E_i = ([K+i, K+i+1) × [0,1) × [0,1)) ⊂ ℝ³`

in coordinates, transported to `EuclideanSpace ℝ (Fin 3)` along `WithLp.ofLp`
(which preserves Lebesgue measure).  Volume `1`, and `E_i ∩ E_j = ∅` for `i ≠ j`
because the first-coordinate intervals are shifted by distinct integers.
Every `E_i` is disjoint from `Λ(ℓ)` because all its points have first coordinate
`≥ K+i ≥ K`, while the box has first coordinate `< K`.

Take `b t = 1_{E_{(t:ℕ)}}`.  Then

* `MemLp (b t) 2 volume` (indicator of a set of measure `1`);
* `b t x = 0` for `x ∈ Λ(ℓ)`;
* `star (b t x) * b t' x = 1_{E_{(t:ℕ)} ∩ E_{(t':ℕ)}}(x)` pointwise, so the integral is
  `volume (E_t ∩ E_{t'})`, which is `1` for `t = t'` and `0` otherwise.
-/

namespace Work.BoseBoxFock

open MeasureTheory Set

noncomputable section

/-- Lower corner of the `i`-th shifted unit cube: `(K + i, 0, 0)`. -/
private def cLo (K : ℝ) (i : ℕ) (j : Fin 3) : ℝ := if j = 0 then K + (i : ℝ) else 0

/-- The `i`-th shifted half-open unit cube `[K+i,K+i+1) × [0,1) × [0,1)`, in coordinates. -/
private def piBox (K : ℝ) (i : ℕ) : Set (Fin 3 → ℝ) :=
  Set.univ.pi fun j => Set.Ico (cLo K i j) (cLo K i j + 1)

/-- The same cube inside `EuclideanSpace ℝ (Fin 3)`. -/
private def eBox (K : ℝ) (i : ℕ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ⁻¹' piBox K i

private lemma measurableSet_piBox (K : ℝ) (i : ℕ) : MeasurableSet (piBox K i) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico

private lemma measurableSet_eBox (K : ℝ) (i : ℕ) : MeasurableSet (eBox K i) := by
  simp only [eBox]
  exact (measurableSet_piBox K i).preimage (PiLp.volume_preserving_ofLp (Fin 3)).measurable

/-- Each shifted unit cube has Lebesgue measure `1`. -/
private lemma volume_eBox (K : ℝ) (i : ℕ) : volume (eBox K i) = 1 := by
  simp only [eBox, piBox]
  rw [MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    ((MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico :
      MeasurableSet (Set.univ.pi fun j : Fin 3 => Set.Ico (cLo K i j) (cLo K i j + 1)))).nullMeasurableSet]
  rw [Real.volume_pi_Ico]
  simp

private lemma piBox_not_both {K : ℝ} {i j : ℕ} (h : i ≠ j) {w : Fin 3 → ℝ}
    (h1 : w ∈ piBox K i) (h2 : w ∈ piBox K j) : False := by
  have h10 : cLo K i 0 ≤ w 0 ∧ w 0 < cLo K i 0 + 1 := by
    simpa using (Set.mem_univ_pi.mp h1) 0
  have h20 : cLo K j 0 ≤ w 0 ∧ w 0 < cLo K j 0 + 1 := by
    simpa using (Set.mem_univ_pi.mp h2) 0
  simp only [cLo, Fin.isValue, if_true] at h10 h20
  rcases lt_or_gt_of_ne h with hij | hji
  · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    linarith [h10.2, h20.1]
  · have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hji
    linarith [h20.2, h10.1]

/-- Distinct shifted unit cubes are disjoint. -/
private lemma eBox_inter_eq_empty {K : ℝ} {i j : ℕ} (h : i ≠ j) :
    eBox K i ∩ eBox K j = ∅ := by
  simp only [eBox]
  rw [← Set.preimage_inter]
  have hempty : piBox K i ∩ piBox K j = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨w, hw1, hw2⟩
    exact piBox_not_both h hw1 hw2
  rw [hempty, Set.preimage_empty]

/-- A point whose first coordinate is `< K` does not lie in a cube shifted by `K`
(whose points all have first coordinate `≥ K`). -/
private lemma not_mem_eBox (K : ℝ) (i : ℕ) {x : EuclideanSpace ℝ (Fin 3)}
    (h : (WithLp.ofLp x : Fin 3 → ℝ) 0 < K) : x ∉ eBox K i := by
  intro hx
  have h1 : (WithLp.ofLp x : Fin 3 → ℝ) ∈ piBox K i := hx
  have h2 : cLo K i 0 ≤ (WithLp.ofLp x : Fin 3 → ℝ) 0 := (Set.mem_univ_pi.mp h1) 0 |>.1
  have h3 : K ≤ cLo K i 0 := by
    simp only [cLo, Fin.isValue, if_true]
    exact le_add_of_nonneg_right (Nat.cast_nonneg i)
  linarith

/-- Pointwise identity behind the orthonormality of the indicator functions. -/
private lemma star_indicator_mul (s s' : Set (EuclideanSpace ℝ (Fin 3)))
    (x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) ((s.indicator (fun _ => (1 : ℂ))) x)
      * (s'.indicator (fun _ => (1 : ℂ))) x
    = ((s ∩ s').indicator (fun _ => (1 : ℂ))) x := by
  by_cases hx : x ∈ s <;> by_cases hx' : x ∈ s' <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hx']

theorem exists_orthonormal_offBox (ℓ : ℝ) (hℓ : 0 < ℓ) (m : ℕ) :
    ∃ b : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ,
      (∀ t, MeasureTheory.MemLp (b t) 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ t, ∀ x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ, b t x = 0) ∧
      (∀ t t', (∫ x, (starRingEnd ℂ) (b t x) * b t' x) = if t = t' then 1 else 0) := by
  classical
  -- the box `Λ(ℓ) = ℓ • cell` is bounded, hence contained in a closed ball
  obtain ⟨R, hbox⟩ : ∃ R : ℝ, ∀ x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ,
      ‖x‖ ≤ |ℓ| * R := by
    obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall
      (0 : EuclideanSpace ℝ (Fin 3))).mp
      Work.BoseK15.corpusBox.cell_compact.isBounded
    refine ⟨R₀, ?_⟩
    intro x hx
    rw [Work.BoseB4.BoxData.boxL, Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)] at hx
    have h1 : ‖ℓ⁻¹ • x‖ ≤ R₀ := by
      have h2 := hR₀ hx
      rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
    rw [norm_smul, Real.norm_eq_abs, abs_inv] at h1
    have hpos : 0 < |ℓ| := abs_pos.mpr (ne_of_gt hℓ)
    have hmul : |ℓ| * (|ℓ|⁻¹ * ‖x‖) ≤ |ℓ| * R₀ := mul_le_mul_of_nonneg_left h1 hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hmul
    exact hmul
  set K : ℝ := |ℓ| * R + 1 with hK
  have hlt : |ℓ| * R < K := by rw [hK]; linarith
  refine ⟨fun t => (eBox K (t : ℕ)).indicator (fun _ => (1 : ℂ)), ?_, ?_, ?_⟩
  · -- `MemLp` of the indicator of a set of measure `1`
    intro t
    refine memLp_indicator_const 2 (measurableSet_eBox K (t : ℕ)) (1 : ℂ) (Or.inr ?_)
    rw [volume_eBox K (t : ℕ)]
    exact ENNReal.one_ne_top
  · -- vanishing on the box
    intro t x hx
    have hxK : ‖x‖ < K := lt_of_le_of_lt (hbox x hx) hlt
    have hcoord : (WithLp.ofLp x : Fin 3 → ℝ) 0 < K := by
      have h3 : ‖(WithLp.ofLp x : Fin 3 → ℝ) 0‖ ≤ ‖x‖ := PiLp.norm_apply_le (p := 2) x 0
      rw [Real.norm_eq_abs] at h3
      exact lt_of_le_of_lt (le_trans (le_abs_self _) h3) hxK
    exact Set.indicator_of_notMem (not_mem_eBox K (t : ℕ) hcoord) _
  · -- orthonormality
    intro t t'
    have hfun : (fun x => (starRingEnd ℂ) ((eBox K (t : ℕ)).indicator (fun _ => (1 : ℂ)) x)
          * (eBox K (t' : ℕ)).indicator (fun _ => (1 : ℂ)) x)
        = (eBox K (t : ℕ) ∩ eBox K (t' : ℕ)).indicator (fun _ => (1 : ℂ)) := by
      funext x
      exact star_indicator_mul _ _ x
    rw [hfun, integral_indicator_const (1 : ℂ)
      ((measurableSet_eBox K (t : ℕ)).inter (measurableSet_eBox K (t' : ℕ)))]
    have hvol : volume (eBox K (t : ℕ) ∩ eBox K (t' : ℕ)) =
        (if t = t' then 1 else 0 : ENNReal) := by
      by_cases h : t = t'
      · subst h
        rw [Set.inter_self, volume_eBox K (t : ℕ)]
        simp
      · rw [eBox_inter_eq_empty (show (t : ℕ) ≠ (t' : ℕ) from fun hh => h (Fin.ext hh)),
          measure_empty]
        simp [h]
    rw [Measure.real_def, hvol]
    split_ifs with h <;> simp

end

end Work.BoseBoxFock
