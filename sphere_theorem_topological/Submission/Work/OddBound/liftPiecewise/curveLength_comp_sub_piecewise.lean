import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.liftPiecewise.exists_lift_of_piecewise_short
import Submission.Work.OddBound.longHomotopy.curveLength_comp_sub

namespace Work.OddBound.liftPiecewise

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-!
# Reversing a piecewise `C¹` curve preserves its Riemannian length

This file proves `curveLength_comp_sub_piecewise`: if `c : ℝ → M` is piecewise `C¹` on the
partition `a = p 0 < p 1 < ⋯ < p k = b` (the hypothesis `hpiece`), then the length of the
time-reversed curve `s ↦ c (b - s)` over `[0, b - a]` equals the length of `c` over `[a, b]`.

The proof is *not* by summing over the pieces (which would require the interval-integrability of
the speed on each piece), but directly: the speeds of `c ∘ (b - ·)` and of `c` at `b - ·` agree
whenever `c` is differentiable at `b - ·`, i.e. off the finite set of breakpoints `p i`, hence
almost everywhere; the substitution `s ↦ b - s` in the interval integral is Mathlib's
`intervalIntegral.integral_comp_sub_mul`, which needs no integrability hypothesis.
-/

/-- **Covering by the pieces.**  Every point of the open interval `(p 0, p (last k))` lies in one
of the consecutive closed intervals `[p j.castSucc, p j.succ]`, `j : Fin k`.

(No monotonicity of `p` is needed: take the *last* index `i` with `p i ≤ t`; then `i` is not the
last index, since `p (last k) > t`, and `p i.succ ≤ t` would give the larger index `i.succ`.) -/
private lemma exists_piece_mem_Icc_of_mem_Ioo
    {k : ℕ} {p : Fin (k + 1) → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo (p 0) (p (Fin.last k))) :
    ∃ j : Fin k, t ∈ Set.Icc (p j.castSucc) (p j.succ) := by
  classical
  set S : Finset (Fin (k + 1)) := Finset.univ.filter (fun i => p i ≤ t) with hS
  have h0 : (0 : Fin (k + 1)) ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, le_of_lt ht.1⟩
  have hne : S.Nonempty := ⟨0, h0⟩
  set i₀ : Fin (k + 1) := S.max' hne with hi₀
  have hi₀mem : i₀ ∈ S := by rw [hi₀]; exact Finset.max'_mem S hne
  have hle : p i₀ ≤ t := (Finset.mem_filter.mp hi₀mem).2
  have hmax : ∀ i ∈ S, i ≤ i₀ := by
    intro i hi
    rw [hi₀]
    exact Finset.le_max' S i hi
  have hval : i₀.val < k := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i₀.isLt) with h | h
    · exact h
    · exfalso
      have hlast : i₀ = Fin.last k := Fin.ext h
      rw [hlast] at hle
      exact absurd hle (not_le.mpr ht.2)
  refine ⟨⟨i₀.val, hval⟩, ?_, ?_⟩
  · have hcast : (⟨i₀.val, hval⟩ : Fin k).castSucc = i₀ := Fin.ext rfl
    rw [hcast]
    exact hle
  · by_contra hcon
    push_neg at hcon
    have hmem : ((⟨i₀.val, hval⟩ : Fin k).succ) ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, le_of_lt hcon⟩
    have h2 : ((⟨i₀.val, hval⟩ : Fin k).succ : Fin (k + 1)) ≤ i₀ := hmax _ hmem
    have h2' : i₀.val + 1 ≤ i₀.val := by
      have h3 : ((⟨i₀.val, hval⟩ : Fin k).succ : Fin (k + 1)).val ≤ i₀.val :=
        Fin.le_iff_val_le_val.mp h2
      simpa using h3
    omega

/-- **Differentiability away from the breakpoints.**  If `c` is `C¹` on each of the closed pieces
`[p j.castSucc, p j.succ]` and `a = p 0`, `b = p (last k)`, then `c` is differentiable at every
point of `[a,b]` which is not one of the breakpoints. -/
private lemma mdifferentiableAt_of_notMem_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {c : ℝ → M} {a b : ℝ} {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hp0 : p 0 = a) (hp1 : p (Fin.last k) = b)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 c (Set.Icc (p j.castSucc) (p j.succ)))
    {t : ℝ} (ht : t ∈ Set.Icc a b) (htp : t ∉ Set.range p) :
    MDifferentiableAt 𝓘(ℝ) I c t := by
  have hat : a < t := by
    rcases lt_or_eq_of_le ht.1 with h | h
    · exact h
    · exact absurd ⟨0, by rw [hp0, h]⟩ htp
  have hbt : t < b := by
    rcases lt_or_eq_of_le ht.2 with h | h
    · exact h
    · exact absurd ⟨Fin.last k, by rw [hp1, h]⟩ htp
  obtain ⟨j, hj⟩ :=
    exists_piece_mem_Icc_of_mem_Ioo (p := p) (t := t) (by rw [hp0, hp1]; exact ⟨hat, hbt⟩)
  have hne1 : p j.castSucc ≠ t := fun h => htp ⟨j.castSucc, h⟩
  have hne2 : t ≠ p j.succ := fun h => htp ⟨j.succ, h.symm⟩
  have htIoo : t ∈ Set.Ioo (p j.castSucc) (p j.succ) :=
    ⟨lt_of_le_of_ne hj.1 hne1, lt_of_le_of_ne hj.2 hne2⟩
  have hmem : Set.Icc (p j.castSucc) (p j.succ) ∈ 𝓝 t :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds htIoo) Set.Ioo_subset_Icc_self
  exact ((hpiece j).contMDiffAt hmem).mdifferentiableAt one_ne_zero

theorem curveLength_comp_sub_piecewise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b) {k : ℕ} {p : Fin (k + 1) → ℝ}
    (hmono : StrictMono p) (hp0 : p 0 = a) (hp1 : p (Fin.last k) = b)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 c (Set.Icc (p j.castSucc) (p j.succ))) :
    Submission.Length.curveLength (I := I) (fun s : ℝ => c (b - s)) 0 (b - a)
      = Submission.Length.curveLength (I := I) c a b := by
  rw [Submission.Length.curveLength_def, Submission.Length.curveLength_def]
  -- The two speeds agree almost everywhere on `[0, b - a]`.
  have hcongr : (∫ s in (0 : ℝ)..(b - a),
        Submission.Length.curveSpeed (I := I) (fun s : ℝ => c (b - s)) s)
      = ∫ s in (0 : ℝ)..(b - a), Submission.Length.curveSpeed (I := I) c (b - s) := by
    refine intervalIntegral.integral_congr_ae ?_
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null
      (t := (fun s : ℝ => b - s) ⁻¹' Set.range p) ?_ ?_
    · rintro s hs
      rw [Set.mem_ofPred_eq] at hs
      push_neg at hs
      obtain ⟨hs1, hs2⟩ := hs
      show b - s ∈ Set.range p
      by_contra hcon
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ b - a by linarith)] at hs1
      obtain ⟨hs1a, hs1b⟩ := hs1
      have htIcc : b - s ∈ Set.Icc a b := ⟨by linarith, by linarith⟩
      have hmd : MDifferentiableAt 𝓘(ℝ) I c (b - s) :=
        mdifferentiableAt_of_notMem_range (I := I) (c := c) hp0 hp1 hpiece htIcc hcon
      exact hs2 (Work.OddBound.longHomotopy.curveSpeed_comp_sub_eq (I := I) hmd)
    · exact Set.Finite.measure_zero
        ((Set.finite_range p).preimage (Set.injOn_of_injective (sub_right_injective (b := b))))
        MeasureTheory.volume
  rw [hcongr]
  -- Substitution `t = b - s` in the interval integral.
  have hb1 : (∫ s in (0 : ℝ)..(b - a), Submission.Length.curveSpeed (I := I) c (b - s))
      = ∫ s in (0 : ℝ)..(b - a), Submission.Length.curveSpeed (I := I) c (b - 1 * s) := by
    simp only [one_mul]
  rw [hb1]
  rw [intervalIntegral.integral_comp_sub_mul (f := Submission.Length.curveSpeed (I := I) c)
    (a := (0 : ℝ)) (b := b - a) (c := (1 : ℝ)) (d := b) one_ne_zero]
  simp only [one_mul, inv_one, one_smul, sub_sub_cancel, sub_zero]

end Work.OddBound.liftPiecewise
