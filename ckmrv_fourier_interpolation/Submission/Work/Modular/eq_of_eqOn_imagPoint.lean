import Mathlib
import Submission.Work.Modular.ThetaImagAxis

namespace Work.Modular

open Work.Modular
open scoped Manifold Real MatrixGroups
open UpperHalfPlane

open Filter
open scoped Topology

/-- **Identity principle on the imaginary axis.**  Two holomorphic functions on the upper half
plane which agree on the imaginary axis `{i t | t > 0}` are equal.  (The imaginary axis
accumulates at `i`; `t ↦ i t` is continuous and injective for `t > 0`, so the agreement holds
frequently in every punctured neighbourhood of `i`, and `UpperHalfPlane.eq_zero_of_frequently`
applies.) -/
lemma eq_of_eqOn_imagPoint {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g)
    (h : ∀ t : ℝ, 0 < t → f (imagPoint t) = g (imagPoint t)) : f = g := by
  let φ : ℍ → ℂ := f - g
  have hφ : MDiff φ := hf.sub hg
  have hzero : ∀ t : ℝ, 0 < t → φ (imagPoint t) = 0 := by
    intro t ht
    simp only [φ, Pi.sub_apply, h t ht, sub_self]
  -- `imagPoint 1 = I`
  have hI : imagPoint 1 = (I : ℍ) := by
    rw [imagPoint,
      show ((1 : ℝ) : ℂ) * Complex.I = ((I : ℍ) : ℂ) by rw [UpperHalfPlane.coe_I]; norm_num]
    exact UpperHalfPlane.ofComplex_apply UpperHalfPlane.I
  -- continuity of `imagPoint` at `1`
  have hca : ContinuousAt imagPoint (1 : ℝ) := by
    have h1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
    have hc := UpperHalfPlane.continuousOn_ofComplex_I_mul.continuousAt (isOpen_Ioi.mem_nhds h1)
    convert hc using 1
    ext t
    simp only [imagPoint]
    rw [UpperHalfPlane.coe_I, mul_comm]
  have hpos : ∀ᶠ t in 𝓝[≠] (1 : ℝ), 0 < t :=
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hne : ∀ᶠ t in 𝓝[≠] (1 : ℝ), t ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := ({1}ᶜ : Set ℝ))] with t ht
    simpa using ht
  -- `imagPoint` maps punctured neighbourhoods of `1` into punctured neighbourhoods of `I`
  have hev : ∀ᶠ t in 𝓝[≠] (1 : ℝ), imagPoint t ≠ (I : ℍ) := by
    filter_upwards [hpos, hne] with t ht ht1 hEq
    exact ht1 (imagPoint_injOn ht (by norm_num) (by rw [← hI] at hEq; exact hEq))
  have hcont : Tendsto imagPoint (𝓝[≠] (1 : ℝ)) (𝓝[≠] (I : ℍ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, hev⟩
    have := hca.tendsto.mono_left (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := ({1}ᶜ : Set ℝ)))
    rwa [hI] at this
  have hfreq : ∃ᶠ t in 𝓝[≠] (1 : ℝ), φ (imagPoint t) = 0 :=
    (hpos.mono (fun t ht => hzero t ht)).frequently
  have hzero' : φ = 0 :=
    UpperHalfPlane.eq_zero_of_frequently hφ (hcont.frequently hfreq)
  exact sub_eq_zero.mp hzero'

end Work.Modular
