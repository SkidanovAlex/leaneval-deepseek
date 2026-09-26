import Mathlib
import Submission.Work.Drive.Mono.NoGrazeDefs
import Submission.Work.Topology.SphereSlicing.boxNorm_continuous

/-!
# Finiteness of the tilted face parameters

The parameters of one period at which the knot lies in the closed Pardon box and on one of the two
faces `{⟪v, y⟫ = ⟪v,c⟫ + u ± h}` of the tilted slab are finite, provided the derivative of the
tilted height `⟪v,·⟫ ∘ K` does not vanish at any such parameter.

The proof is the one-dimensional argument already used for the flat crossing set
(`Work.Drive.Mono.finite_flatCrossings`): the set is closed (a preimage of the closed box under the
box norm and of `{±h}` under the continuous tilted height) and bounded, hence compact; every point is
isolated, because the tilted height has nonzero derivative there and the derivative is continuous, so
the height is injective on a neighbourhood and only one of the two levels `h`, `-h` can be met there.
A compact set whose points are all isolated is finite.

The two levels are handled by the auxiliary lemma `finite_zeroLevel_of_deriv_ne_zero` (one level,
level `0`), applied to `g - h` and `g + h`, where `g = slabHeight K c u v` is the tilted height.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal _root_.Topology RealInnerProductSpace

noncomputable section

/-! ## The level set at a single level -/

/-- **A compact isolated level set is finite.**  If a function `f` is continuous, its derivative is
continuous, and the derivative of `f` does not vanish at any point of the closed Pardon box at which
`f` vanishes, then `f` vanishes at only finitely many parameters of one period inside the closed box.

This is the one-level form of the counting argument; it is `finite_flatCrossings` with the flat
height replaced by an arbitrary `f`. -/
theorem finite_zeroLevel_of_deriv_ne_zero (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (f : ℝ → ℝ) (hfcont : Continuous f)
    (hdfcont : Continuous (deriv f))
    (hfderiv : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) ≤ s → f t = 0 →
      deriv f t ≠ 0) :
    ({t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) ≤ s ∧ f t = 0}).Finite := by
  classical
  set S : Set ℝ := {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) ≤ s ∧ f t = 0} with hSdef
  have hSmem : ∀ t : ℝ, t ∈ S ↔ t ∈ Set.Icc 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) ≤ s ∧ f t = 0 := by
    intro t; simp only [hSdef, Set.mem_ofPred_eq]
  have hKc : Continuous K.curve := K.smooth.continuous
  -- Every point of `S` is isolated in `S`.
  have hloc : ∀ x ∈ S, ∃ U : Set ℝ, U ∈ nhds x ∧ S ∩ U ⊆ {x} := by
    intro x hx
    obtain ⟨-, hxbox, hxzero⟩ := (hSmem x).mp hx
    have hdfx : deriv f x ≠ 0 := hfderiv x hxbox hxzero
    have hopen : IsOpen {y : ℝ | deriv f y ≠ 0} :=
      isOpen_compl_singleton.preimage hdfcont
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hdfx)
    refine ⟨Set.Ioo (x - ε) (x + ε), isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩, ?_⟩
    rintro y ⟨hyS, hyU⟩
    have hfy : f y = 0 := ((hSmem y).mp hyS).2.2
    have hsub : Set.Ioo (x - ε) (x + ε) ⊆ {y : ℝ | deriv f y ≠ 0} := by
      intro z hz
      exact hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        exact abs_sub_lt_iff.mpr ⟨by linarith [hz.2], by linarith [hz.1]⟩)
    have hInj : Set.InjOn f (Set.Ioo (x - ε) (x + ε)) :=
      intervalZeros.injOn_of_deriv_ne_zero (by linarith) (fun z hz => hsub hz)
    have hyx : y = x := hInj hyU ⟨by linarith, by linarith⟩ (by rw [hfy, hxzero])
    simpa only [Set.mem_singleton_iff] using hyx
  -- `S` is closed and lies in the compact interval `[0, 2π]`.
  have hSsub : S ⊆ Set.Icc (0 : ℝ) (2 * Real.pi) := fun t ht => ((hSmem t).mp ht).1
  have hSclosed : IsClosed S := by
    rw [hSdef]
    have h1 : IsClosed (Set.Icc (0 : ℝ) (2 * Real.pi)) := isClosed_Icc
    have h2 : IsClosed (K.curve ⁻¹' {y : R3 | Submission.boxNorm c σ y ≤ s}) :=
      (isClosed_le (Work.Topology.SphereSlicing.boxNorm_continuous c σ)
        continuous_const).preimage hKc
    have h3 : IsClosed (f ⁻¹' ({0} : Set ℝ)) := isClosed_singleton.preimage hfcont
    have heq : {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) ≤ s ∧ f t = 0}
        = Set.Icc (0 : ℝ) (2 * Real.pi) ∩
          (K.curve ⁻¹' {y : R3 | Submission.boxNorm c σ y ≤ s}) ∩
          (f ⁻¹' ({0} : Set ℝ)) := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      tauto
    rw [heq]
    exact (h1.inter h2).inter h3
  have hScomp : IsCompact S := IsCompact.of_isClosed_subset isCompact_Icc hSclosed hSsub
  -- A compact set all of whose points are isolated is finite.
  obtain ⟨F, hFsub, hFcover⟩ := hScomp.elim_nhds_subcover
    (fun x => if hx : x ∈ S then Classical.choose (hloc x hx) else Set.univ)
    (fun x hx => by
      rw [dif_pos hx]
      exact (Classical.choose_spec (hloc x hx)).1)
  refine Set.Finite.subset (s := (↑F : Set ℝ)) (t := S) (Finset.finite_toSet F) ?_
  intro y hy
  obtain ⟨x, hxF, hyU⟩ := by simpa only [Set.mem_iUnion] using hFcover hy
  have hxS : x ∈ S := hFsub x hxF
  have hsub := (Classical.choose_spec (hloc x hxS)).2
  have hyU' : y ∈ Classical.choose (hloc x hxS) := by simpa only [dif_pos hxS] using hyU
  have hyx : y = x := Set.mem_singleton_iff.mp (hsub ⟨hy, hyU'⟩)
  rw [hyx]
  simpa using hxF

/-! ## The face parameters -/

/-- **The parameters at which the knot lies on a face of the tilted slab inside the box are finite.**  If the derivative of the tilted height `⟪v,·⟫ ∘ K` does not vanish at any parameter of the closed box at which the tilted height equals `±h` (measured from the level `⟪v,c⟫ + u`), then in one period there are only finitely many such parameters.  Please put the result in namespace `Work.Drive.Mono`, in a new file `Submission/Work/Drive/Mono/finite_facePts_tilted.lean`.

Proof.  The set `F := {t ∈ Icc 0 (2π) | boxNorm c σ (K.curve t) ≤ s ∧ |⟪v, K.curve t⟫ - (⟪v,c⟫ + u)| = h}` is closed and bounded, hence compact.  At every point `t₀ ∈ F` the function `t ↦ ⟪v, K.curve t⟫` has nonzero derivative and continuous derivative (the knot is smooth), so it is strictly monotone — hence injective — on a neighbourhood; consequently `t₀` is isolated in `F` (and if `h ≠ 0`, a neighbourhood meets `F` in at most two points).  A compact set all of whose points are isolated is finite (`IsCompact.elim_nhds_subcover` / `IsCompact.elim_finite_subcover`), and the `Ico 0 (2π)`-subtrace in the conclusion is contained in the `Icc 0 (2π)` set, hence finite. -/
theorem finite_facePts_tilted (K : LeanEval.KnotTheory.PardonDistortion.Knot) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) (v : LeanEval.KnotTheory.PardonDistortion.R3) (h : ℝ)
    (hderiv : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) ≤ s →
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) :
    {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
      Submission.boxNorm c σ (K.curve t) ≤ s ∧
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h}.Finite := by
  classical
  by_cases hh : 0 ≤ h
  · -- The two levels `h` and `-h` are the zero levels of `g - h` and `g + h`.
    set g : ℝ → ℝ := slabHeight K c u v with hgdef
    have hgapply : ∀ t : ℝ, g t = inner ℝ v (K.curve t) - (inner ℝ v c + u) :=
      fun t => by rw [hgdef]; exact slabHeight_apply K c u v t
    have hgcont : Continuous g := by
      rw [hgdef]
      exact (continuous_const.inner K.smooth.continuous).sub continuous_const
    have hdg : ∀ t : ℝ, deriv g t = deriv (fun r : ℝ => inner ℝ v (K.curve r)) t := by
      intro t
      rw [hgdef, deriv_slabHeight, deriv_inner_curve_const]
    have hdgcont : Continuous (deriv g) := by
      have heq : deriv g = fun t : ℝ => inner ℝ v (deriv K.curve t) :=
        funext (fun t => by rw [hdg t, deriv_inner_curve_const])
      rw [heq]
      exact continuous_const.inner (contDiff_deriv_curve K).continuous
    -- The level set of `g - h`.
    have hf1cont : Continuous (fun y : ℝ => g y - h) := hgcont.sub continuous_const
    have hdf1 : Continuous (deriv (fun y : ℝ => g y - h)) := by
      have heq : deriv (fun y : ℝ => g y - h) = deriv g :=
        funext (fun t => deriv_sub_const (f := g) h)
      rw [heq]; exact hdgcont
    have hf1deriv : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) ≤ s →
        (fun y : ℝ => g y - h) t = 0 → deriv (fun y : ℝ => g y - h) t ≠ 0 := by
      intro t hbox hzero
      have hgt : g t = h := sub_eq_zero.mp hzero
      have habs : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h := by
        rw [← hgapply t, hgt, abs_of_nonneg hh]
      rw [deriv_sub_const (f := g) h, hdg t]
      exact hderiv t hbox habs
    have hfin1 := finite_zeroLevel_of_deriv_ne_zero K s c σ (fun y : ℝ => g y - h)
      hf1cont hdf1 hf1deriv
    -- The level set of `g + h`.
    have hf2cont : Continuous (fun y : ℝ => g y + h) := hgcont.add continuous_const
    have hdf2 : Continuous (deriv (fun y : ℝ => g y + h)) := by
      have heq : deriv (fun y : ℝ => g y + h) = deriv g :=
        funext (fun t => deriv_add_const (f := g) h)
      rw [heq]; exact hdgcont
    have hf2deriv : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) ≤ s →
        (fun y : ℝ => g y + h) t = 0 → deriv (fun y : ℝ => g y + h) t ≠ 0 := by
      intro t hbox hzero
      have hgt : g t = -h := add_eq_zero_iff_eq_neg.mp hzero
      have habs : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h := by
        rw [← hgapply t, hgt, abs_neg, abs_of_nonneg hh]
      rw [deriv_add_const (f := g) h, hdg t]
      exact hderiv t hbox habs
    have hfin2 := finite_zeroLevel_of_deriv_ne_zero K s c σ (fun y : ℝ => g y + h)
      hf2cont hdf2 hf2deriv
    -- The face set is the union of the two level sets.
    refine (hfin1.union hfin2).subset ?_
    intro t ht
    obtain ⟨htI, htbox, htab⟩ := ht
    have htI' : t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨htI.1, le_of_lt htI.2⟩
    rcases (abs_eq hh).mp htab with hgt | hgt
    · exact Or.inl ⟨htI', htbox, sub_eq_zero.mpr hgt⟩
    · exact Or.inr ⟨htI', htbox, add_eq_zero_iff_eq_neg.mpr hgt⟩
  · -- For `h < 0` no parameter survives (`|·| = h` is impossible), so the set is empty.
    have hlt : h < 0 := not_le.mp hh
    refine Set.Finite.subset (s := (∅ : Set ℝ)) Set.finite_empty ?_
    intro t ht
    obtain ⟨-, -, habs⟩ := ht
    have h1 : (0 : ℝ) ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)| := abs_nonneg _
    rw [habs] at h1
    exact absurd h1 (not_le.mpr hlt)

end

end Work.Drive.Mono
