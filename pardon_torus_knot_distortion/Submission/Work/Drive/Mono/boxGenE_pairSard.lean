import Mathlib
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.ae_ae_cornerLocus_finite
import Submission.Work.Drive.Mono.finite_zeroSet_of_isInvertible_fderiv
import Submission.Work.Drive.Mono.ae_diag_vertEdgeFinite

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem diagVec_apply (j : Fin 3) : diagVec j = 1 := by
  simp [diagVec]

/-- The box norm is continuous in the point. -/
theorem continuous_boxNorm' (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Continuous (fun y : R3 => Submission.boxNorm c σ y) := by
  change Continuous (fun y : R3 => max (max (|y (σ 0) - c (σ 0)| / Submission.boxSide 0)
    (|y (σ 1) - c (σ 1)| / Submission.boxSide 1))
    (|y (σ 2) - c (σ 2)| / Submission.boxSide 2))
  fun_prop

/-- Each face norm is bounded by the box norm. -/
theorem faceNorm_le_boxNorm' (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) (i : Fin 3) :
    |y (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ y := by
  change |y (σ i) - c (σ i)| / Submission.boxSide i ≤
    max (max (|y (σ 0) - c (σ 0)| / Submission.boxSide 0)
      (|y (σ 1) - c (σ 1)| / Submission.boxSide 1))
      (|y (σ 2) - c (σ 2)| / Submission.boxSide 2)
  fin_cases i <;>
    first
      | exact le_trans (le_max_left _ _) (le_max_left _ _)
      | exact le_trans (le_max_right _ _) (le_max_left _ _)
      | exact le_max_right _ _

/-- The coordinates of the diagonal vector are all `1`. -/
theorem add_smul_diagVec_apply (c : R3) (τ : ℝ) (i : Fin 3) :
    (c + τ • diagVec) i = c i + τ := by
  simp [PiLp.add_apply, PiLp.smul_apply, diagVec_apply]

/-- **The shift bound**: moving the centre along the diagonal changes the box norm by at most
`|τ|`, because every side length of Pardon's box is at least `1`. -/
theorem boxNorm_shift_le (c : R3) (τ : ℝ) (σ : Equiv.Perm (Fin 3)) (y : R3) :
    Submission.boxNorm (c + τ • diagVec) σ y ≤ Submission.boxNorm c σ y + |τ| := by
  have key : ∀ i : Fin 3,
      |y (σ i) - (c + τ • diagVec) (σ i)| / Submission.boxSide i ≤
        Submission.boxNorm c σ y + |τ| := by
    intro i
    rw [add_smul_diagVec_apply]
    rw [show y (σ i) - (c (σ i) + τ) = y (σ i) - c (σ i) - τ from by ring]
    have hbs : (0:ℝ) < Submission.boxSide i := Submission.boxSide_pos i
    have hle : |y (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ y :=
      faceNorm_le_boxNorm' c σ y i
    have htri : |y (σ i) - c (σ i) - τ| ≤ |y (σ i) - c (σ i)| + |τ| := by
      calc |y (σ i) - c (σ i) - τ| = |(y (σ i) - c (σ i)) + (-τ)| := by ring_nf
        _ ≤ |y (σ i) - c (σ i)| + |-τ| := abs_add_le _ _
        _ = |y (σ i) - c (σ i)| + |τ| := by rw [abs_neg]
    have hdiv : |y (σ i) - c (σ i) - τ| / Submission.boxSide i ≤
        (|y (σ i) - c (σ i)| + |τ|) / Submission.boxSide i :=
      div_le_div_of_nonneg_right htri hbs.le
    have hsplit : (|y (σ i) - c (σ i)| + |τ|) / Submission.boxSide i =
        |y (σ i) - c (σ i)| / Submission.boxSide i + |τ| / Submission.boxSide i := by
      rw [add_div]
    have hτle : |τ| / Submission.boxSide i ≤ |τ| := by
      rw [div_le_iff₀ hbs]; nlinarith [abs_nonneg τ, Submission.one_le_boxSide i]
    linarith
  change max (max (|y (σ 0) - (c + τ • diagVec) (σ 0)| / Submission.boxSide 0)
      (|y (σ 1) - (c + τ • diagVec) (σ 1)| / Submission.boxSide 1))
      (|y (σ 2) - (c + τ • diagVec) (σ 2)| / Submission.boxSide 2) ≤
    Submission.boxNorm c σ y + |τ|
  exact max_le (max_le (key 0) (key 1)) (key 2)

/-- **G4**: `HasEssBox` survives a small shift of the centre along the diagonal.  The essential
curve witnessing `HasEssBox P r c σ` has compact range inside the open box `PBox r c σ`, so the
maximum `m` of `boxNorm c σ` on it is `< r`; during the shift by `τ` the box norm grows by at most
`|τ|`, so `τ₀ = r - m` is the required radius. -/
theorem hasEssBox_diag_shift (P : Work.CoreTopology.ParamTorus) (r : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (h : Submission.HasEssBox P r c σ) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, |τ| < τ₀ →
      Submission.HasEssBox P r (c + τ • diagVec) σ := by
  obtain ⟨γ, hess, hmem⟩ := h
  have hcomp : IsCompact (Set.range γ) := by
    have hper : Function.Periodic γ (2 * Real.pi) := γ.periodic
    have himg := hper.image_Icc (by positivity : (0:ℝ) < 2 * Real.pi) 0
    rw [zero_add] at himg
    rw [← himg]
    exact isCompact_Icc.image γ.cont
  have hne : (Set.range γ).Nonempty := ⟨γ 0, ⟨0, rfl⟩⟩
  obtain ⟨y₀, hy₀, hmax⟩ := hcomp.exists_isMaxOn hne (continuous_boxNorm' c σ).continuousOn
  set m : ℝ := Submission.boxNorm c σ y₀ with hm
  have hmr : m < r := by
    have hy₀P : y₀ ∈ Submission.PBox r c σ := by
      obtain ⟨t, ht⟩ := hy₀
      rw [← ht]
      exact hmem t
    rw [Submission.mem_PBox_iff] at hy₀P
    exact hy₀P
  refine ⟨r - m, by linarith, ?_⟩
  intro τ hτ
  refine ⟨γ, hess, fun t => ?_⟩
  rw [Submission.mem_PBox_iff]
  have h1 : Submission.boxNorm c σ (γ t) ≤ m := (isMaxOn_iff.mp hmax) (γ t) ⟨t, rfl⟩
  have h2 : Submission.boxNorm (c + τ • diagVec) σ (γ t) ≤
      Submission.boxNorm c σ (γ t) + |τ| := boxNorm_shift_le c τ σ (γ t)
  linarith [abs_nonneg τ]

/-- The linear part of the affine map `(s, u) ↦ (c (σ i) + ε boxSide i * s, c (σ 2) + u)`. -/
def faceCrossLin (i : Fin 3) (ε : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun w := (ε * Submission.boxSide i * w.1, w.2)
  map_add' w w' := by
    apply Prod.ext <;> simp <;> ring
  map_smul' r w := by
    apply Prod.ext <;> simp <;> ring

theorem faceCrossLin_surjective (i : Fin 3) {ε : ℝ} (hε : ε ≠ 0) :
    Function.Surjective (faceCrossLin i ε) := by
  intro v
  refine ⟨(v.1 / (ε * Submission.boxSide i), v.2), ?_⟩
  have hb : ε * Submission.boxSide i ≠ 0 :=
    mul_ne_zero hε (ne_of_gt (Submission.boxSide_pos i))
  apply Prod.ext <;> simp [faceCrossLin]
  exact mul_div_cancel₀ v.1 hb

/-- **G1 for one `(i, ε)`**: for almost every `(s, u)` the value
`(c (σ i) + ε boxSide i * s, c (σ 2) + u)` is not a critical value of the pair map
`cornerProj ψ σ i 2`.  The map `(s, u) ↦` that value is affine with invertible linear part
`faceCrossLin i ε`, and the critical values of the (smooth, `2π`-periodic) pair map are null by
equal-dimension Sard (`cornerCritVals_null`). -/
theorem ae_faceCrossShift (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    {ε : ℝ} (hε : ε ≠ 0) :
    ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      (c (σ i) + ε * Submission.boxSide i * w.1, c (σ 2) + w.2) ∉
        cornerCritVals ψ σ i 2 := by
  haveI : Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod ℝ ℝ]
    exact Measure.prod.instIsAddHaarMeasure _ _
  set a : ℝ × ℝ := (c (σ i), c (σ 2)) with ha
  set S : Set (ℝ × ℝ) := cornerCritVals ψ σ i 2 with hS
  have hSmeas : MeasurableSet S := hS ▸ cornerCritVals_measurable ψ σ i 2
  have hSnull : MeasureTheory.volume S = 0 := hS ▸ cornerCritVals_null ψ σ i 2
  have hSanull : MeasureTheory.volume {y : ℝ × ℝ | y + a ∈ S} = 0 := by
    have hset : {y : ℝ × ℝ | y + a ∈ S} = (fun y : ℝ × ℝ => a + y) ⁻¹' S := by
      ext y; simp [add_comm]
    rw [hset, MeasureTheory.measure_preimage_add
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) a S, hSnull]
  have hSameas : MeasurableSet {y : ℝ × ℝ | y + a ∈ S} :=
    hSmeas.preimage (measurable_add_const a)
  have hLsurj : Function.Surjective (faceCrossLin i ε) := faceCrossLin_surjective i hε
  have hmain : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      (faceCrossLin i ε w + a) ∉ S := by
    have hiff := MeasureTheory.ae_comp_linearMap_mem_iff (faceCrossLin i ε)
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) hLsurj hSameas.compl
    refine hiff.mpr ?_
    rw [MeasureTheory.ae_iff]
    simpa using hSanull
  filter_upwards [hmain] with w hw
  intro hmem
  exact hw (by
    have heq : (c (σ i) + ε * Submission.boxSide i * w.1, c (σ 2) + w.2) =
        faceCrossLin i ε w + a := by
      apply Prod.ext <;> simp [faceCrossLin, ha] <;> ring
    rw [← heq]; exact hmem)

/-- **G1**: for every centre `c`, almost every level `s` and almost every cutting level `u`, the
face planes `i = 0, 1` cross the flat plane `{y (σ 2) = c (σ 2) + u}` transversally on the
surface. -/
theorem ae_ae_faceCrossReg (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        FaceCrossReg ψ c σ s u := by
  have hprod : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
      FaceCrossReg ψ c σ w.1 w.2 := by
    have hgood : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)),
        ∀ ib : {p : Fin 3 × Bool // p.1 ≠ 2},
          (c (σ ib.1.1) + (if ib.1.2 then (1:ℝ) else -1) * Submission.boxSide ib.1.1 * w.1,
            c (σ 2) + w.2) ∉ cornerCritVals ψ σ ib.1.1 2 := by
      refine MeasureTheory.ae_all_iff.mpr (fun ib => ?_)
      rcases ib with ⟨⟨i, b⟩, hi⟩
      rcases b with _ | _
      · simpa using ae_faceCrossShift ψ c σ i (show (-1:ℝ) ≠ 0 by norm_num)
      · simpa using ae_faceCrossShift ψ c σ i (show (1:ℝ) ≠ 0 by norm_num)
    filter_upwards [hgood] with w hw
    intro i hi ε hε p hp1 hp2
    show (fderiv ℝ (cornerProj ψ σ i 2) p).IsInvertible
    have hval : cornerProj ψ σ i 2 p =
        (c (σ i) + ε * Submission.boxSide i * w.1, c (σ 2) + w.2) := by
      have e1 : Work.Smooth.Morse.param ψ p (σ i) =
          c (σ i) + ε * Submission.boxSide i * w.1 := hp1
      have e2 : Work.Smooth.Morse.param ψ p (σ 2) = c (σ 2) + w.2 := hp2
      exact Prod.ext e1 e2
    have hdet : (fderiv ℝ (cornerProj ψ σ i 2) p).det ≠ 0 := by
      intro hd
      have hmem2 : (c (σ i) + ε * Submission.boxSide i * w.1, c (σ 2) + w.2) ∈
          cornerCritVals ψ σ i 2 := ⟨p, hd, hval⟩
      rcases hε with h | h
      · subst h
        exact hw ⟨(i, true), hi⟩ (by simpa using hmem2)
      · subst h
        exact hw ⟨(i, false), hi⟩ (by simpa using hmem2)
    exact ⟨(fderiv ℝ (cornerProj ψ σ i 2) p).toContinuousLinearEquivOfDetNeZero hdet, rfl⟩
  rw [Measure.volume_eq_prod ℝ ℝ] at hprod
  exact Measure.ae_ae_of_ae_prod hprod

/-- **The pair-Sard inputs of `BoxGenE`, and the generic centre shift** (project lead,
`Mono/NOTES_LEAD_junctionGen.md` §2, G1/G3/G4).

* **G1**: for every centre `c`, for almost every level `s` and almost every cutting level `u`, the
  face planes `i = 0, 1` cross the flat plane `{y (σ 2) = c (σ 2) + u}` transversally on the surface
  (`Work.Drive.Mono.FaceCrossReg`).  Proof: the pair `Φᵢ = (y (σ i), y (σ 2)) ∘ par` is `C^∞` and
  `2π`-periodic, its critical values are null (equal-dimension Sard), and the map
  `(s, u) ↦ (c (σ i) + ε boxSide i · s, c (σ 2) + u)` is affine with determinant `ε boxSide i ≠ 0`,
  so the bad set of `(s, u)` is null; `Measure.ae_prod_mem_iff_ae_ae_mem` finishes.
* **G3**: for every centre `c`, for almost every shift `τ` and almost every level `s`, the vertical
  edge locus of the shifted centre `c + τ • diagVec` is finite
  (`Work.Drive.Mono.VertEdgeFinite`, i.e. `Φ₀₁ = (y (σ 0), y (σ 1)) ∘ par` misses the four pinned
  points, hence has finite fibres).  The pinned point `q (τ, s)` is affine in `(τ, s)` with
  determinant `ε₁ boxSide 1 − ε₀ boxSide 0 ≠ 0` because `boxSide 0 = 1` and `boxSide 1 = 2^{1/3}`;
  finiteness of the fibre then follows from
  `Work.Drive.Mono.finite_zeroSet_of_isInvertible_fderiv` on `[0, 2π]²`.
* **G4**: `HasEssBox` survives a small diagonal shift of the centre: if `m < r` is the maximum of
  `boxNorm c σ` on the range of the loop, then `τ₀ = r − m` works, because `boxSide ≥ 1` gives
  `boxNorm (c + τ • diagVec) σ y ≤ boxNorm c σ y + |τ|`. -/
theorem boxGenE_pairSard (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3))
    (P : Work.CoreTopology.ParamTorus) (r : ℝ) :
    (∀ c : R3, ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          Work.Drive.Mono.FaceCrossReg ψ c σ s u) ∧
    (∀ c : R3, ∀ᵐ τ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ᵐ s ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          Work.Drive.Mono.VertEdgeFinite ψ (c + τ • Work.Drive.Mono.diagVec) σ s) ∧
    (∀ c : R3, Submission.HasEssBox P r c σ →
        ∃ τ₀ : ℝ, 0 < τ₀ ∧
          ∀ τ : ℝ, |τ| < τ₀ → Submission.HasEssBox P r (c + τ • Work.Drive.Mono.diagVec) σ) := by
  exact ⟨fun c => ae_ae_faceCrossReg ψ c σ, fun c => ae_diag_vertEdgeFinite ψ c σ,
    fun c h => hasEssBox_diag_shift P r c σ h⟩

end

end Work.Drive.Mono
