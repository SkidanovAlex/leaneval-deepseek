import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.annulusCuts
import Submission.Work.Smooth.SphereJordan.PCopy.tgtSpansClean

/-!
# The two halves of the target pcannulus (Pardon's cut-and-paste, block `pcannulusTargetSpans`)

This module proves `Work.SphereJordan.pcannulusTargetSpans`: for a simple closed plane curve `γ` in the
open unit disc with Schoenflies datum `S`, there are parameters `t₁ < s₁`, `t₂ < s₂` on the two rays
of the diameter through the pcbase point, and two injective continuous maps `Φ_up`, `Φ_dn` of the model
disc whose boundary parametrisations are the two `4`-arc curves `pctgtUpB`, `pctgtDnB` of
`Submission/Work/Smooth/SphereJordan/pcannulusInjectionTwoCutsAlt.lean`, whose images cover the pcannulus
`pcannulus S = 𝔻 ∖ S.V` and meet exactly in the two crosscuts `pccut₁`, `pccut₂`.

The file is organised in two layers:

* `pcexists_targetData` (proved here) constructs the *configuration*: the two crosscuts of
  `Work.Smooth.SphereJordan.pccrosscut_mem_annulus` in the two directions `±pccutDir S`, together with
  the parameters `θ₁`, `θ₂` of their inner endpoints on `γ`, and the two facts that make the crosscuts
  *proper* arcs of the pcannulus (beyond the inner endpoint the ray misses the closed disc `closure S.V`,
  so the crosscuts meet the curve `γ` exactly in their inner endpoints);
* `Work.SphereJordan.pctgtSpansCore` (`Submission/Work/SphereJordan/tgtSpansClean.lean`) turns that
  configuration into the two spanning discs.

## The two halves of the final step

* the *configuration-dependent* algebra (simplicity of the two four-arc curves, and the flag `b` for
  which `S.V` lies on the unbounded side of both) is in
  `Submission/Work/SphereJordan/tgtSpansClean.lean`, on top of the cycle-free pairing machinery
  (`pcwindIdentitiesProof`, `pcspan_pairing`, `prelim`, `pctgtUpPC_isSimple`) and
  `Work.SphereJordan.pcdnPCIsSimple` (`pcdnPCIsSimple.lean`, the `pcdnPC` mirror of `pctgtUpPC_isSimple`);
* the *topology* — two pccuts cut the pcannulus into two discs — is `Work.SphereJordan.pctgtT_tilingOfPairing`
  in `Submission/Work/SphereJordan/tgtSpansTiling.lean`.

## Why `tgtSpansTiling.lean` is a copy

The tiling of the pcannulus by the two pieces of the pairing is proved in
`Submission/Work/SphereJordan/tilingOfPairing.lean`, which imports
`Submission/Work/Smooth/SphereJordan/pccoreAuxTwoCuts.lean`.  That module cannot be used underneath
`pcannulusTargetSpans`, because `annulusSchoenfliesCore.lean` — which imports `pcannulusTargetSpans` —
declares the same names as `pccoreAuxTwoCuts` (`pccuts_subset_trace_up`, `pcsegPt`, `pcnorm_base_add`, ...),
so no module may import both families.  The module `tgtSpansTiling.lean` is therefore a verbatim
copy of `tilingOfPairing` (and of the twelve declarations of `pccoreAuxTwoCuts` on which it depends),
with every declaration renamed with the prefix `tgtT_`; that removes the clash while keeping the same
proof.

## The shape of the configuration

Write `u = pccutDir S`, `p = pcbase S`; then `p = ‖p‖·u` with `‖p‖ < 1` and `‖u‖ = 1`, so the line
`ℝu` through the origin is the line of the two crosscuts.  With `t₁`, `t₂` the *last* exits of the
ray from `p` in the directions `u` and `-u`, and `s₁ = 1 - ‖p‖`, `s₂ = 1 + ‖p‖` the exits from the
closed unit disc, the crosscuts are

  `pccut₁ = {λ•u : λ ∈ [λ₁, 1]}`  and  `pccut₂ = {λ•u : λ ∈ [-1, λ₂]}`,

where `λ₁ = ‖p‖ + t₁` and `λ₂ = ‖p‖ - t₂` are the parameters of the inner endpoints `a₁ = γ θ₁`,
`a₂ = γ θ₂`.  The two curves `pctgtUpB`, `pctgtDnB` are the boundaries of the two "halves" of the cut
pcannulus: `pctgtUpB` runs along the upper outer arc from `u` to `-u`, inward along `pccut₂` to `a₂`,
along the inner arc of `γ` from `a₂` to `a₁`, and outward along `pccut₁` back to `u`; `pctgtDnB` is the
same with the roles of the upper and lower arcs interchanged.
-/

namespace Work.SphereJordan

open Set

/-- **The configuration of the two crosscuts of the target pcannulus.**

There are parameters `0 < t₁ < s₁`, `0 < t₂ < s₂` with the inner endpoints `p + t₁•u`, `p - t₂•u` on
the curve, the outer endpoints equal to `u` and `-u`, the open segments inside the pcannulus, and the
rays beyond the inner endpoints disjoint from the closed disc `closure S.V`; moreover the inner
endpoints are `γ θ₁`, `γ θ₂` for parameters `θ₂ < θ₁ < θ₂ + 2π`. -/
theorem pcexists_targetData (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ (t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ),
      0 < t₁ ∧ t₁ < s₁ ∧ 0 < t₂ ∧ t₂ < s₂ ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) +
          (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace ∧
      (∀ σ : ℝ, t₁ < σ → σ < s₁ →
        (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
          Metric.ball (0 : ℂ) 1 \ S.V) ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
        Work.Smooth.SphereJordan.pccutDir S ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) -
          (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace ∧
      (∀ σ : ℝ, t₂ < σ → σ < s₂ →
        (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
          Metric.ball (0 : ℂ) 1 \ S.V) ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
        -Work.Smooth.SphereJordan.pccutDir S ∧
      γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
        (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∧
      γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
        (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∧
      θ₂ < θ₁ ∧ θ₁ < θ₂ + 2 * Real.pi ∧
      (∀ σ : ℝ, t₁ < σ →
        (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
          closure S.V) ∧
      (∀ σ : ℝ, t₂ < σ →
        (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
          closure S.V) := by
  have hu : Work.Smooth.SphereJordan.pccutDir S ≠ 0 :=
    Work.Smooth.SphereJordan.pccutDir_ne_zero S
  have hsmul : ∀ (a : ℂ) (t : ℝ), a + t • Work.Smooth.SphereJordan.pccutDir S =
      a + (t : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    intro a t; rw [Complex.real_smul]
  have hsmul' : ∀ (a : ℂ) (t : ℝ), a + t • (-Work.Smooth.SphereJordan.pccutDir S) =
      a - (t : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    intro a t; rw [smul_neg, Complex.real_smul]; ring
  obtain ⟨t₁, ht₁pos, ha₁, ht₁max⟩ :=
    Work.Smooth.SphereJordan.pcexists_crosscut_inner S hball (Work.Smooth.SphereJordan.pccutDir S) hu
  have ha₁K : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      t₁ • Work.Smooth.SphereJordan.pccutDir S ∈ closure S.V := by
    rw [Work.Smooth.SphereJordan.pcclosure_V_eq S]; exact Or.inr ha₁
  obtain ⟨s₁, hts₁, hb₁, hseg₁⟩ :=
    Work.Smooth.SphereJordan.pcexists_crosscut_outer S hball (Work.Smooth.SphereJordan.pccutDir S) hu
      ht₁pos.le ha₁K
  have ht₁lt : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ) +
      t₁ • Work.Smooth.SphereJordan.pccutDir S‖ < 1 :=
    Work.Smooth.SphereJordan.pcclosure_V_subset_openBall S hball ha₁K
  have ht₁s₁ : t₁ < s₁ := by
    rcases lt_or_eq_of_le hts₁ with hlt | heq
    · exact hlt
    · exfalso
      have h1 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ) +
          s₁ • Work.Smooth.SphereJordan.pccutDir S‖ = 1 :=
        Work.Smooth.SphereJordan.pcmem_sphere_one_iff _ |>.mp hb₁
      rw [← heq] at h1
      rw [h1] at ht₁lt
      exact lt_irrefl 1 ht₁lt
  have hs₁pos : 0 < s₁ := lt_trans ht₁pos ht₁s₁
  obtain ⟨t₂, ht₂pos, ha₂, ht₂max⟩ :=
    Work.Smooth.SphereJordan.pcexists_crosscut_inner S hball
      (-Work.Smooth.SphereJordan.pccutDir S) (neg_ne_zero.mpr hu)
  have ha₂K : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      t₂ • (-Work.Smooth.SphereJordan.pccutDir S) ∈ closure S.V := by
    rw [Work.Smooth.SphereJordan.pcclosure_V_eq S]; exact Or.inr ha₂
  obtain ⟨s₂, hts₂, hb₂, hseg₂⟩ :=
    Work.Smooth.SphereJordan.pcexists_crosscut_outer S hball
      (-Work.Smooth.SphereJordan.pccutDir S) (neg_ne_zero.mpr hu) ht₂pos.le ha₂K
  have ht₂lt : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ) +
      t₂ • (-Work.Smooth.SphereJordan.pccutDir S)‖ < 1 :=
    Work.Smooth.SphereJordan.pcclosure_V_subset_openBall S hball ha₂K
  have ht₂s₂ : t₂ < s₂ := by
    rcases lt_or_eq_of_le hts₂ with hlt | heq
    · exact hlt
    · exfalso
      have h1 : ‖(Work.Smooth.SphereJordan.pcbase S : ℂ) +
          s₂ • (-Work.Smooth.SphereJordan.pccutDir S)‖ = 1 :=
        Work.Smooth.SphereJordan.pcmem_sphere_one_iff _ |>.mp hb₂
      rw [← heq] at h1
      rw [h1] at ht₂lt
      exact lt_irrefl 1 ht₂lt
  have hs₂pos : 0 < s₂ := lt_trans ht₂pos ht₂s₂
  have hsurf₁ : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [← hsmul _ s₁]; exact hb₁
  have hsurf₂ : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [← hsmul' _ s₂]; exact hb₂
  obtain ⟨hout₁, hout₂⟩ :=
    Work.Smooth.SphereJordan.pccut_outer_eq S hball hs₁pos hs₂pos hsurf₁ hsurf₂
  have ha1c : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace := by rw [← hsmul _ t₁]; exact ha₁
  have ha2c : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace := by rw [← hsmul' _ t₂]; exact ha₂
  obtain ⟨θ₁', hθ₁'⟩ := ha1c
  obtain ⟨θ₂', hθ₂'⟩ := ha2c
  set n₁ : ℤ := ⌊θ₁' / (2 * Real.pi)⌋ with hn₁
  set n₂ : ℤ := ⌊θ₂' / (2 * Real.pi)⌋ with hn₂
  have hred₁ : γ.γ (θ₁' - (n₁ : ℝ) * (2 * Real.pi)) = γ.γ θ₁' := by
    have hper := γ.apply_add_int_mul (θ₁' - (n₁ : ℝ) * (2 * Real.pi)) n₁
    rw [show θ₁' - (n₁ : ℝ) * (2 * Real.pi) + (n₁ : ℝ) * (2 * Real.pi) = θ₁' from by ring] at hper
    exact hper.symm
  have hred₂ : γ.γ (θ₂' - (n₂ : ℝ) * (2 * Real.pi)) = γ.γ θ₂' := by
    have hper := γ.apply_add_int_mul (θ₂' - (n₂ : ℝ) * (2 * Real.pi)) n₂
    rw [show θ₂' - (n₂ : ℝ) * (2 * Real.pi) + (n₂ : ℝ) * (2 * Real.pi) = θ₂' from by ring] at hper
    exact hper.symm
  have hmem₁ : θ₁' - (n₁ : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    have hpos : (0 : ℝ) < 2 * Real.pi := Work.Smooth.Jordan.two_pi_pos
    refine ⟨?_, ?_⟩
    · have := (le_div_iff₀ hpos).mp (Int.floor_le (θ₁' / (2 * Real.pi)))
      linarith
    · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (θ₁' / (2 * Real.pi)))
      linarith
  have hmem₂ : θ₂' - (n₂ : ℝ) * (2 * Real.pi) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    have hpos : (0 : ℝ) < 2 * Real.pi := Work.Smooth.Jordan.two_pi_pos
    refine ⟨?_, ?_⟩
    · have := (le_div_iff₀ hpos).mp (Int.floor_le (θ₂' / (2 * Real.pi)))
      linarith
    · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (θ₂' / (2 * Real.pi)))
      linarith
  have hne : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ≠
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
    intro hcon
    have h2 : (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
        -((t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S) := by
      have h3 : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
            (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
          (Work.Smooth.SphereJordan.pcbase S : ℂ) +
            (-((t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S)) := by
        rw [← sub_eq_add_neg]; exact hcon
      exact add_left_cancel h3
    have hzero : ((t₁ + t₂ : ℝ) : ℂ) * Work.Smooth.SphereJordan.pccutDir S = 0 := by
      have hce : ((t₁ + t₂ : ℝ) : ℂ) = (t₁ : ℂ) + (t₂ : ℂ) := by push_cast; ring
      rw [hce, add_mul, h2]
      ring
    have hsum : ((t₁ + t₂ : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp hzero with hh | hh
      · exact hh
      · exact absurd hh hu
    have : t₁ + t₂ = 0 := by exact_mod_cast hsum
    linarith
  have hne_par : θ₁' - (n₁ : ℝ) * (2 * Real.pi) ≠ θ₂' - (n₂ : ℝ) * (2 * Real.pi) := by
    intro hcon
    have h1 : γ.γ (θ₁' - (n₁ : ℝ) * (2 * Real.pi)) = γ.γ θ₁' := hred₁
    have h2 : γ.γ (θ₂' - (n₂ : ℝ) * (2 * Real.pi)) = γ.γ θ₂' := hred₂
    have h3 : γ.γ (θ₁' - (n₁ : ℝ) * (2 * Real.pi)) =
        γ.γ (θ₂' - (n₂ : ℝ) * (2 * Real.pi)) := congrArg (fun x : ℝ => γ.γ x) hcon
    rw [h1, h2, hθ₁', hθ₂'] at h3
    exact hne h3
  -- the branch independent facts
  have f1 : 0 < t₁ := ht₁pos
  have f2 : t₁ < s₁ := ht₁s₁
  have f3 : 0 < t₂ := ht₂pos
  have f4 : t₂ < s₂ := ht₂s₂
  have f5 : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace := by
    rw [← hsmul _ t₁]; exact ha₁
  have f6 : ∀ σ : ℝ, t₁ < σ → σ < s₁ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V := by
    intro σ h1 h2
    refine ⟨?_, ?_⟩
    · rw [← hsmul _ σ]; exact hseg₁ σ h1.le h2
    · intro hV; rw [← hsmul _ σ] at hV; exact ht₁max σ h1 (subset_closure hV)
  have f7 : (Work.Smooth.SphereJordan.pcbase S : ℂ) +
      (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = Work.Smooth.SphereJordan.pccutDir S := hout₁
  have f8 : (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace := by
    rw [← hsmul' _ t₂]; exact ha₂
  have f9 : ∀ σ : ℝ, t₂ < σ → σ < s₂ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
        Metric.ball (0 : ℂ) 1 \ S.V := by
    intro σ h1 h2
    refine ⟨?_, ?_⟩
    · rw [← hsmul' _ σ]; exact hseg₂ σ h1.le h2
    · intro hV; rw [← hsmul' _ σ] at hV; exact ht₂max σ h1 (subset_closure hV)
  have f10 : (Work.Smooth.SphereJordan.pcbase S : ℂ) -
      (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S = -Work.Smooth.SphereJordan.pccutDir S := hout₂
  have f15 : ∀ σ : ℝ, t₁ < σ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
        closure S.V := by
    intro σ hσ; rw [← hsmul _ σ]; exact ht₁max σ hσ
  have f16 : ∀ σ : ℝ, t₂ < σ →
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∉
        closure S.V := by
    intro σ hσ; rw [← hsmul' _ σ]; exact ht₂max σ hσ
  rcases lt_or_gt_of_ne hne_par with hlt | hgt
  · -- `θ₁'' < θ₂''`: shift the first parameter by a full turn
    have f11 : γ.γ (θ₁' - (n₁ : ℝ) * (2 * Real.pi) + 2 * Real.pi) =
        (Work.Smooth.SphereJordan.pcbase S : ℂ) +
          (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      rw [show γ.γ (θ₁' - (n₁ : ℝ) * (2 * Real.pi) + 2 * Real.pi) =
          γ.γ (θ₁' - (n₁ : ℝ) * (2 * Real.pi)) from γ.periodic _]
      rw [hred₁]; exact hθ₁'
    have f12 : γ.γ (θ₂' - (n₂ : ℝ) * (2 * Real.pi)) =
        (Work.Smooth.SphereJordan.pcbase S : ℂ) -
          (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      rw [hred₂]; exact hθ₂'
    have f13 : θ₂' - (n₂ : ℝ) * (2 * Real.pi) <
        θ₁' - (n₁ : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      linarith [hmem₂.2, hmem₁.1]
    have f14 : θ₁' - (n₁ : ℝ) * (2 * Real.pi) + 2 * Real.pi <
        θ₂' - (n₂ : ℝ) * (2 * Real.pi) + 2 * Real.pi := by linarith [hlt]
    exact ⟨t₁, s₁, t₂, s₂, θ₁' - (n₁ : ℝ) * (2 * Real.pi) + 2 * Real.pi,
      θ₂' - (n₂ : ℝ) * (2 * Real.pi), f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14,
      f15, f16⟩
  · -- `θ₂'' < θ₁''`: keep both parameters
    have f11 : γ.γ (θ₁' - (n₁ : ℝ) * (2 * Real.pi)) =
        (Work.Smooth.SphereJordan.pcbase S : ℂ) +
          (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      rw [hred₁]; exact hθ₁'
    have f12 : γ.γ (θ₂' - (n₂ : ℝ) * (2 * Real.pi)) =
        (Work.Smooth.SphereJordan.pcbase S : ℂ) -
          (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      rw [hred₂]; exact hθ₂'
    have f13 : θ₂' - (n₂ : ℝ) * (2 * Real.pi) < θ₁' - (n₁ : ℝ) * (2 * Real.pi) := by
      linarith [hgt]
    have f14 : θ₁' - (n₁ : ℝ) * (2 * Real.pi) <
        θ₂' - (n₂ : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
      linarith [hmem₁.2, hmem₂.1]
    exact ⟨t₁, s₁, t₂, s₂, θ₁' - (n₁ : ℝ) * (2 * Real.pi),
      θ₂' - (n₂ : ℝ) * (2 * Real.pi), f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14,
      f15, f16⟩

/-! ## The target statement -/

theorem pcannulusTargetSpans (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {γ : Work.Smooth.Jordan.PlaneCurve} (hs : γ.IsSimple) (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1)
    (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    ∃ (t₁ s₁ t₂ s₂ θ₁ θ₂ : ℝ) (b : Bool),
      0 < t₁ ∧ t₁ < s₁ ∧ 0 < t₂ ∧ t₂ < s₂ ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) +
          (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace ∧
      (∀ σ : ℝ, t₁ < σ → σ < s₁ →
        (Work.Smooth.SphereJordan.pcbase S : ℂ) + (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
          Metric.ball (0 : ℂ) 1 \ S.V) ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
        Work.Smooth.SphereJordan.pccutDir S ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) -
          (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈ γ.trace ∧
      (∀ σ : ℝ, t₂ < σ → σ < s₂ →
        (Work.Smooth.SphereJordan.pcbase S : ℂ) - (σ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∈
          Metric.ball (0 : ℂ) 1 \ S.V) ∧
      (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
        -Work.Smooth.SphereJordan.pccutDir S ∧
      γ.γ θ₁ = (Work.Smooth.SphereJordan.pcbase S : ℂ) +
        (t₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∧
      γ.γ θ₂ = (Work.Smooth.SphereJordan.pcbase S : ℂ) -
        (t₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S ∧
      ∃ Φ_up Φ_dn : C(Work.Smooth.SphereJordan.Disc, ℂ),
        Function.Injective Φ_up ∧ Function.Injective Φ_dn ∧
        (∀ τ : ℝ, Φ_up (Work.Smooth.SphereJordan.circlePoint τ) =
          Work.Smooth.SphereJordan.pctgtUpB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ) ∧
        (∀ τ : ℝ, Φ_dn (Work.Smooth.SphereJordan.circlePoint τ) =
          Work.Smooth.SphereJordan.pctgtDnB S t₁ s₁ t₂ s₂ b θ₁ θ₂ τ) ∧
        Set.range Φ_up ⊆ Work.Smooth.SphereJordan.pcannulus S ∧
        Set.range Φ_dn ⊆ Work.Smooth.SphereJordan.pcannulus S ∧
        Set.range Φ_up ∪ Set.range Φ_dn = Work.Smooth.SphereJordan.pcannulus S ∧
        Set.range Φ_up ∩ Set.range Φ_dn =
          Work.Smooth.SphereJordan.pccut₁ S t₁ s₁ ∪ Work.Smooth.SphereJordan.pccut₂ S t₂ s₂ := by
  obtain ⟨t₁, s₁, t₂, s₂, θ₁, θ₂, ht₁, ht₁s₁, ht₂, ht₂s₂, ha₁, hseg₁, hout₁, ha₂, hseg₂,
    hout₂, hθ₁, hθ₂, hθ, hθ', hmax₁, hmax₂⟩ := pcexists_targetData h hs hball S
  obtain ⟨b, Φ_up, Φ_dn, hinj₁, hinj₂, hbd₁, hbd₂, hsub₁, hsub₂, hun, hint⟩ :=
    pctgtSpansCore h hs hball S t₁ s₁ t₂ s₂ θ₁ θ₂ ht₁ ht₁s₁ ht₂ ht₂s₂ ha₁ hseg₁ hout₁
      ha₂ hseg₂ hout₂ hθ₁ hθ₂ hθ hθ' hmax₁ hmax₂
  exact ⟨t₁, s₁, t₂, s₂, θ₁, θ₂, b, ht₁, ht₁s₁, ht₂, ht₂s₂, ha₁, hseg₁, hout₁, ha₂, hseg₂,
    hout₂, hθ₁, hθ₂, Φ_up, Φ_dn, hinj₁, hinj₂, hbd₁, hbd₂, hsub₁, hsub₂, hun, hint⟩

end Work.SphereJordan
