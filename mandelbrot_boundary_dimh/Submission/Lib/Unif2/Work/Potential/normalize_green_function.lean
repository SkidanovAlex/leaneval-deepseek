import Mathlib
import Submission.Lib.Unif2.Work.Potential.Defs

/-!
# Normalising the logarithmic pole of a weak Green function

A *weak* Green function `E` at `z₀` (positive and harmonic off `z₀`, with compact superlevel sets)
has, by Bôcher's theorem (`LogCoefficientInput`), a logarithmic singularity of some coefficient
`c ≥ 0` at `z₀`:

`|E x + c · log ‖ξ x - ξ z₀‖| ≤ C` near `z₀`,  where `ξ = chartAt ℂ z₀`.

The main point of this file is that `c` cannot vanish: if it did, `E` would be bounded near `z₀`,
so by the removable-singularity input (`RemovableInput`) it would extend to a harmonic function `U`
on all of `X`; the compactness of the superlevel sets of `E` is inherited by `U`, so `U` attains a
global maximum — and a harmonic function attaining its maximum on a connected space is constant,
which is impossible for a non-compact space with compact superlevel sets.  Hence `c > 0`, and
`E' = c⁻¹ • E` is a *strong* Green function: its pole has coefficient exactly one.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open Set Filter
open Classical

namespace Work.Potential

theorem normalize_green_function
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) {z₀ : X} {E : X → ℝ}
    (hlog : Submission.LogCoefficientInput (X := X) z₀)
    (hrem : Submission.RemovableInput (X := X) z₀)
    (hE : Submission.HasGreenFunctionWeak z₀ E) :
    ∃ E' : X → ℝ, Submission.HasGreenFunctionE z₀ E' := by
  obtain ⟨c, hc_nonneg, C, V, hV, hbnd⟩ := hlog (u := E) hE.2.1 hE.1
  by_cases hc0 : c = 0
  · -- Case `c = 0`: `E` is bounded near `z₀`, hence extends to a harmonic function on `X`.
    exfalso
    have hbounded : ∃ M : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ → |E x| ≤ M :=
      ⟨C, V, hV, fun x hx hne => by simpa [hc0] using hbnd x hx hne⟩
    obtain ⟨U, hUharm, hUeq⟩ := hrem (u := E) hE.2.1 hbounded
    have hUcont : Continuous U := Submission.HarmonicOnX_continuous hUharm
    have hUpos : ∀ x, x ≠ z₀ → 0 < U x := fun x hx => by rw [hUeq x hx]; exact hE.1 x hx
    -- The superlevel sets of the extension are still compact.
    have hUcompact : ∀ ε : ℝ, 0 < ε → IsCompact {x : X | ε ≤ U x} := by
      intro ε hε
      refine IsCompact.of_isClosed_subset ((hE.2.2 ε hε).insert z₀) ?_ ?_
      · exact isClosed_le continuous_const hUcont
      · intro x hx
        by_cases hxz : x = z₀
        · exact mem_insert_iff.mpr (Or.inl hxz)
        · refine mem_insert_iff.mpr (Or.inr ?_)
          show ε ≤ E x
          rw [← hUeq x hxz]
          exact hx
    -- `X` is not a single point, because it is not compact.
    have hex : ∃ x : X, x ≠ z₀ := by
      by_contra h
      have h' : ∀ x : X, x = z₀ := by
        intro x
        by_contra hx
        exact h ⟨x, hx⟩
      refine hX (isCompact_univ_iff.mp ?_)
      rw [show (univ : Set X) = {z₀} from by ext x; simp [h' x]]
      exact isCompact_singleton
    obtain ⟨p, hp⟩ := hex
    have hpU : 0 < U p := hUpos p hp
    -- `U` attains its global maximum.
    have hK : IsCompact {x : X | U p / 2 ≤ U x} := hUcompact _ (by linarith)
    have hKne : ({x : X | U p / 2 ≤ U x} : Set X).Nonempty :=
      ⟨p, by show U p / 2 ≤ U p; linarith⟩
    obtain ⟨q, hqK, hqmax⟩ := hK.exists_isMaxOn hKne hUcont.continuousOn
    have hglobal : ∀ x, U x ≤ U q := by
      intro x
      by_cases hx : x ∈ {x : X | U p / 2 ≤ U x}
      · exact hqmax hx
      · have hx' : U x < U p / 2 := lt_of_not_ge (by simpa using hx)
        have : U p / 2 ≤ U q := hqK
        linarith
    -- A harmonic function attaining its maximum on a preconnected space is constant.
    have hconst : ∀ x : X, U x = U q :=
      Submission.SubharmonicOnX.eq_of_isMaxOn (hUharm.subharmonic hUcont.continuousOn) hglobal
    have hqpos : 0 < U q := lt_of_lt_of_le hpU (hglobal p)
    have huniv : (univ : Set X) = {x : X | U q / 2 ≤ U x} := by
      ext x
      show True ↔ (U q / 2 ≤ U x)
      constructor
      · intro _; rw [hconst x]; linarith
      · intro _; trivial
    -- But then `univ` is compact, contradicting `hX`.
    refine hX (isCompact_univ_iff.mp ?_)
    rw [huniv]
    exact hUcompact (U q / 2) (by linarith)
  · -- Case `c > 0`: rescale `E` to make the pole coefficient one.
    have hcpos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hc0)
    refine ⟨fun x => c⁻¹ * E x, ⟨?_, ?_, ?_⟩, ⟨c⁻¹ * C, V, hV, ?_⟩, fun A => ?_⟩
    · -- positivity
      intro x hx
      exact mul_pos (inv_pos.mpr hcpos) (hE.1 x hx)
    · -- harmonicity
      have h := hE.2.1.const_smul c⁻¹
      have hfun : (c⁻¹ • E : X → ℝ) = fun x => c⁻¹ * E x := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rwa [hfun] at h
    · -- compactness of the superlevel sets (rescaling by a positive constant)
      intro ε hε
      have hset : {x : X | ε ≤ c⁻¹ * E x} = {x : X | ε * c ≤ E x} := by
        ext x
        show (ε ≤ c⁻¹ * E x) ↔ (ε * c ≤ E x)
        have h1 : c⁻¹ * E x = E x / c := by rw [div_eq_mul_inv, mul_comm]
        rw [h1, le_div_iff₀ hcpos]
      rw [hset]
      exact hE.2.2 (ε * c) (mul_pos hε hcpos)
    · -- the boundedness of the logarithmic singularity, rescaled
      refine fun x hx hne => ?_
      have hb := hbnd x hx hne
      have heq : c⁻¹ * (E x + c * Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖)
          = c⁻¹ * E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
      rw [← heq, abs_mul, abs_of_pos (inv_pos.mpr hcpos)]
      exact mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr hcpos))
    · -- `c⁻¹ • E → +∞` at `z₀`, since `E x ≥ -c log ‖ξ x - ξ z₀‖ - C` there
      have hchart : ContinuousAt (fun x : X => (chartAt ℂ z₀) x) z₀ :=
        (chartAt ℂ z₀).continuousAt (mem_chart_source ℂ z₀)
      have hnormct : ContinuousAt
          (fun x : X => ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖) z₀ :=
        (hchart.sub continuousAt_const).norm
      have hVr : {x : X | ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖
            < Real.exp (-(A + C / c))} ∈ nhds z₀ :=
        hnormct (isOpen_Iio.mem_nhds (by simpa using Real.exp_pos (-(A + C / c))))
      refine ⟨V ∩ (chartAt ℂ z₀).source ∩ {x : X | ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖
          < Real.exp (-(A + C / c))}, ?_, ?_⟩
      · refine inter_mem (inter_mem hV ?_) hVr
        exact (chartAt ℂ z₀).open_source.mem_nhds (mem_chart_source ℂ z₀)
      · intro x hx hne
        obtain ⟨⟨hxV, hxsrc⟩, hxr⟩ := hx
        have hne_chart : (chartAt ℂ z₀) x ≠ (chartAt ℂ z₀) z₀ := fun h =>
          hne ((chartAt ℂ z₀).injOn hxsrc (mem_chart_source ℂ z₀) h)
        have hposn : 0 < ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          exact hne_chart
        have hloglt : Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ < -(A + C / c) :=
          (Real.log_lt_iff_lt_exp hposn).mpr hxr
        have hb := hbnd x hxV hne
        have hsum : -C ≤ E x + c * Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ :=
          (abs_le.mp hb).1
        have hcC : c * (C / c) = C := by field_simp
        have hstep : c * Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖ < -(c * A + C) := by
          have h := mul_lt_mul_of_pos_left hloglt hcpos
          have hcA : c * (-(A + C / c)) = -(c * A + C) := by rw [mul_neg, mul_add, hcC]
          rwa [hcA] at h
        have h3 : c * A < E x := by linarith
        have h4 : c⁻¹ * (c * A) < c⁻¹ * E x := mul_lt_mul_of_pos_left h3 (inv_pos.mpr hcpos)
        have h5 : c⁻¹ * (c * A) = A := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
        rwa [h5] at h4

end Work.Potential
