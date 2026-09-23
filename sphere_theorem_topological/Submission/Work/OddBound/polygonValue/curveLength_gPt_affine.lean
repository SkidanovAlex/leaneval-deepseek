import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Defs

namespace Work.OddBound.polygonValue

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-- **The pointwise speed of the arclength-parametrised broken geodesic away from the
breakpoints.**  If `s` is not one of the breakpoint parameters `cumLen τ k / totLen τ`
(`k ≤ N`), the composite `s' ↦ gPt τ (totLen τ * s')` agrees near `s` with the affine
reparametrisation `s' ↦ S i ((totLen τ * s' - cumLen τ i) / sideLen τ i) τ` of the side `i`
carrying the arclength `totLen τ * s` (`i = gIdx τ (totLen τ * s)`), so its speed is
`(totLen τ / sideLen τ i) * sideLen τ i = totLen τ`. -/
lemma curveSpeed_gPt_eq_totLen_of_not_breakpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {N : ℕ} (hN : 0 < N) {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    {τ : ℝ}
    (hSsm : ∀ i : Fin N, ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0:ℝ) 1))
    (hK : ∀ i : Fin N, ∀ y ∈ Set.Icc (cumLen (I := I) p w τ (i : ℕ)) (cumLen (I := I) p w τ ((i : ℕ) + 1)),
      gPt (I := I) p hN w S τ y = S i ((y - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ)) τ)
    (hsp : ∀ i : Fin N, ∀ r : ℝ, r ∈ Set.Ioo (0:ℝ) 1 →
      Submission.Length.curveSpeed (I := I) (fun r : ℝ => S i r τ) r = sideLen (I := I) p w τ (i : ℕ))
    (hℓpos : 0 < totLen (I := I) p w τ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hs : ∀ k : ℕ, k ≤ N → cumLen (I := I) p w τ k ≠ totLen (I := I) p w τ * s) :
    Submission.Length.curveSpeed (I := I)
      (fun s' : ℝ => gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s')) s
      = totLen (I := I) p w τ := by
  set i : ℕ := gIdx (I := I) p w τ (totLen (I := I) p w τ * s) with hix
  have hiN : i < N := by rw [hix]; exact gIdx_lt (I := I) p hN w τ _
  have hi1 : i + 1 ≤ N := by omega
  have hlow : cumLen (I := I) p w τ i ≤ totLen (I := I) p w τ * s := by
    have h := cumLen_gIdx_le (I := I) p hN w τ (totLen (I := I) p w τ * s)
      (mul_nonneg hℓpos.le hs0)
    rw [← hix] at h
    exact h
  have hup : totLen (I := I) p w τ * s ≤ cumLen (I := I) p w τ (i + 1) := by
    have h := le_cumLen_gIdx_succ (I := I) p hN w τ (totLen (I := I) p w τ * s)
      (by simpa using mul_le_mul_of_nonneg_left hs1 hℓpos.le)
    rw [← hix] at h
    exact h
  have hlow' : cumLen (I := I) p w τ i < totLen (I := I) p w τ * s :=
    lt_of_le_of_ne hlow (hs i (le_of_lt hiN))
  have hup' : totLen (I := I) p w τ * s < cumLen (I := I) p w τ (i + 1) :=
    lt_of_le_of_ne hup (Ne.symm (hs (i + 1) hi1))
  have hsl : 0 < sideLen (I := I) p w τ i := by
    rw [sideLen_eq_sub (I := I) p w τ i]
    linarith
  have hev : (fun s' : ℝ => gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s'))
      =ᶠ[𝓝 s] (fun s' : ℝ => (fun r : ℝ => S ⟨i, hiN⟩ r τ)
        ((totLen (I := I) p w τ / sideLen (I := I) p w τ i) * s'
          + (-(cumLen (I := I) p w τ i) / sideLen (I := I) p w τ i))) := by
    have hcont : Continuous fun s' : ℝ => totLen (I := I) p w τ * s' :=
      continuous_const.mul continuous_id
    have hopen : IsOpen ((fun s' : ℝ => totLen (I := I) p w τ * s') ⁻¹'
        Set.Ioo (cumLen (I := I) p w τ i) (cumLen (I := I) p w τ (i + 1))) :=
      isOpen_Ioo.preimage hcont
    filter_upwards [hopen.mem_nhds ⟨hlow', hup'⟩] with s' hs'
    rw [hK ⟨i, hiN⟩ (totLen (I := I) p w τ * s') ⟨le_of_lt hs'.1, le_of_lt hs'.2⟩]
    refine congrArg (fun v : ℝ => S ⟨i, hiN⟩ v τ) ?_
    field_simp
    ring
  rw [Submission.GeodesicSpeed.curveSpeed_congr_of_eventuallyEq (I := I) hev]
  have hmem : (totLen (I := I) p w τ / sideLen (I := I) p w τ i) * s
        + (-(cumLen (I := I) p w τ i) / sideLen (I := I) p w τ i) ∈ Set.Ioo (0 : ℝ) 1 := by
    have hval : (totLen (I := I) p w τ / sideLen (I := I) p w τ i) * s
        + (-(cumLen (I := I) p w τ i) / sideLen (I := I) p w τ i)
        = (totLen (I := I) p w τ * s - cumLen (I := I) p w τ i)
            / sideLen (I := I) p w τ i := by
      field_simp
      ring
    rw [hval]
    refine ⟨div_pos (by linarith) hsl, ?_⟩
    rw [div_lt_one hsl]
    have hsub := sideLen_eq_sub (I := I) p w τ i
    linarith
  have hMd : MDifferentiableAt 𝓘(ℝ) I (fun r : ℝ => S ⟨i, hiN⟩ r τ)
      ((totLen (I := I) p w τ / sideLen (I := I) p w τ i) * s
        + (-(cumLen (I := I) p w τ i) / sideLen (I := I) p w τ i)) :=
    ((hSsm ⟨i, hiN⟩).contMDiffAt (Icc_mem_nhds hmem.1 hmem.2)).mdifferentiableAt one_ne_zero
  rw [Submission.Length.curveSpeed_comp_mul_add (I := I) (γ := fun r : ℝ => S ⟨i, hiN⟩ r τ)
    (c := totLen (I := I) p w τ / sideLen (I := I) p w τ i)
    (d := -(cumLen (I := I) p w τ i) / sideLen (I := I) p w τ i) (t := s)
    (div_pos hℓpos hsl) hMd]
  rw [hsp ⟨i, hiN⟩ _ hmem]
  exact div_mul_cancel₀ _ hsl.ne'

/-- **The arclength-parametrised broken geodesic is traversed at constant speed
`totLen τ = gonLength p (w τ)`.**

Hypotheses: `hK` identifies `gPt τ ·` on each side's arclength interval
`[cumLen τ i, cumLen τ (i+1)]` with the side curve `S i · τ` (affinely reparametrised by arclength),
`hSsm` says the side curves are `C¹` in the side parameter, and `hsp` says their speed is the
constant `sideLen τ i`.

Proof plan (for `ℓ := totLen τ > 0`; for `ℓ = 0` the composite is constant and both sides vanish):
off the finite set of `s ∈ [a,b]` with `ℓ * s` one of the breakpoints `cumLen τ j`, the composite
`s ↦ gPt τ (ℓ * s)` agrees near `s` with `s ↦ S i ((ℓ * s - cumLen τ i)/sideLen τ i) τ` for a fixed
side `i` (by `hK`), so by the chain rule (`Submission.Length.curveSpeed_comp_mul_add`) its speed is
`(ℓ / sideLen τ i) * sideLen τ i = ℓ` (using `hsp`); hence the speed equals the constant `ℓ` almost
everywhere on `[a,b]` and `curveLength = ∫_a^b ℓ = ℓ * (b - a)`
(`intervalIntegral.integral_congr_ae`). -/
theorem curveLength_gPt_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {N : ℕ} (hN : 0 < N) {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) 1)
    (hSsm : ∀ i : Fin N, ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0:ℝ) 1))
    (hK : ∀ i : Fin N, ∀ y ∈ Set.Icc (cumLen (I := I) p w τ (i : ℕ)) (cumLen (I := I) p w τ ((i : ℕ) + 1)),
      gPt (I := I) p hN w S τ y = S i ((y - cumLen (I := I) p w τ (i : ℕ)) / sideLen (I := I) p w τ (i : ℕ)) τ)
    (hsp : ∀ i : Fin N, ∀ r : ℝ, r ∈ Set.Ioo (0:ℝ) 1 →
      Submission.Length.curveSpeed (I := I) (fun r : ℝ => S i r τ) r = sideLen (I := I) p w τ (i : ℕ))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Submission.Length.curveLength (I := I)
      (fun s : ℝ => gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s)) a b
      = totLen (I := I) p w τ * (b - a) := by
  rcases eq_or_lt_of_le (totLen_nonneg (I := I) p w τ) with hℓ0 | hℓpos
  · -- Degenerate case: the total length vanishes, so the composite is constant.
    have hfun : (fun s : ℝ => gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s))
        = fun _ => gPt (I := I) p hN w S τ 0 := by
      funext s
      rw [← hℓ0, zero_mul]
    rw [hfun, Submission.Length.curveLength_const, ← hℓ0, zero_mul]
  · -- Main case: the speed is `totLen τ` off the finitely many breakpoint parameters.
    set BadF : Finset ℝ := (Finset.range (N + 1)).image
      (fun k => cumLen (I := I) p w τ k / totLen (I := I) p w τ) with hBadF
    have hae : (fun s : ℝ => Submission.Length.curveSpeed (I := I)
        (fun s' : ℝ => gPt (I := I) p hN w S τ (totLen (I := I) p w τ * s')) s)
        =ᵐ[volume.restrict (Set.uIoc a b)] (fun _ : ℝ => totLen (I := I) p w τ) := by
      rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_uIoc,
        MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null (t := (BadF : Set ℝ) ∪ {b}) ?_ ?_
      · intro x hx
        rw [Set.mem_ofPred_eq, Classical.not_imp] at hx
        by_contra hxb
        rw [Set.mem_union, not_or] at hxb
        obtain ⟨hxBad, hxneqb⟩ := hxb
        rw [Set.mem_singleton_iff] at hxneqb
        have hxIoc : x ∈ Set.Ioc a b := by
          have h := hx.1
          rwa [Set.uIoc_of_le hab] at h
        have hxIoo : x ∈ Set.Ioo a b := ⟨hxIoc.1, lt_of_le_of_ne hxIoc.2 hxneqb⟩
        have hxnot : ∀ k : ℕ, k ≤ N → cumLen (I := I) p w τ k ≠ totLen (I := I) p w τ * x := by
          intro k hk hck
          apply hxBad
          rw [hBadF]
          refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), ?_⟩
          rw [hck, mul_div_cancel_left₀ x (ne_of_gt hℓpos)]
        exact hx.2 (curveSpeed_gPt_eq_totLen_of_not_breakpoint (I := I) hN hSsm hK hsp hℓpos
          (le_trans ha hxIoo.1.le) (le_trans hxIoo.2.le hb) hxnot)
      · rw [MeasureTheory.measure_union_null_iff]
        exact ⟨Set.Finite.measure_zero BadF.finite_toSet volume,
          Set.Finite.measure_zero (Set.finite_singleton b) volume⟩
    rw [Submission.Length.curveLength_def, intervalIntegral.integral_congr_ae_restrict hae,
      intervalIntegral.integral_const, smul_eq_mul, mul_comm]

end Work.OddBound.polygonValue
