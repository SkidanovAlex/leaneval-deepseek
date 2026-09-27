import Mathlib

namespace Work.Engulf.E4Aux

open Set Metric Filter Topology

/-- A function defined by `if χ x = 0 then f x else G x` is continuous on a set `S` as soon as
`χ` is continuous, `f` and `G` are continuous on `S`, and the two branches agree at every point of
`S ∩ {χ = 0}` that is a limit point of `S ∩ {χ ≠ 0}`. -/
theorem continuousOn_ite_of_closure {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {χ : X → ℝ} (hχ : Continuous χ) {f G : X → Y} {S : Set X}
    (hf : ContinuousOn f S) (hG : ContinuousOn G S)
    (hagree : ∀ x ∈ S, χ x = 0 → x ∈ closure (S ∩ {y | χ y ≠ 0}) → G x = f x) :
    ContinuousOn (fun x => if χ x = 0 then f x else G x) S := by
  intro x hx
  set A : Set X := S ∩ {y | χ y = 0} with hAdef
  set B : Set X := S ∩ {y | χ y ≠ 0} with hBdef
  have hA_sub : A ⊆ S := inter_subset_left
  have hB_sub : B ⊆ S := inter_subset_left
  have hAB : A ∪ B = S := by
    rw [hAdef, hBdef, ← inter_union_distrib_left]
    have hun : ({y : X | χ y = 0} : Set X) ∪ {y : X | χ y ≠ 0} = univ := by
      ext y; by_cases h : χ y = 0 <;> simp [h]
    rw [hun, Set.inter_univ]
  have heqA : (fun y => if χ y = 0 then f y else G y) =ᶠ[𝓝[A] x] f := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy2 : χ y = 0 := by rw [hAdef] at hy; exact hy.2
    simp [hy2]
  have heqB : (fun y => if χ y = 0 then f y else G y) =ᶠ[𝓝[B] x] G := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy2 : χ y ≠ 0 := by rw [hBdef] at hy; exact hy.2
    simp [hy2]
  show Tendsto (fun y => if χ y = 0 then f y else G y) (𝓝[S] x)
    (𝓝 (if χ x = 0 then f x else G x))
  rw [show 𝓝[S] x = 𝓝[A] x ⊔ 𝓝[B] x by rw [← hAB, nhdsWithin_union]]
  rw [tendsto_sup]
  constructor
  · by_cases hxA : x ∈ closure A
    · have hx0 : χ x = 0 :=
        closure_minimal (by rw [hAdef]; exact inter_subset_right)
          (isClosed_eq hχ continuous_const) hxA
      rw [ite_eq_left hx0]
      have htA : Tendsto f (𝓝[A] x) (𝓝 (f x)) :=
        (hf x hx).mono_left (nhdsWithin_mono x hA_sub)
      exact (tendsto_congr' heqA).mpr htA
    · rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hxA]
      exact tendsto_bot
  · by_cases hxB : x ∈ closure B
    · have htB : Tendsto G (𝓝[B] x) (𝓝 (G x)) :=
        (hG x hx).mono_left (nhdsWithin_mono x hB_sub)
      by_cases hx0 : χ x = 0
      · rw [ite_eq_left hx0]
        have hGf : G x = f x := hagree x hx hx0 hxB
        rw [hGf] at htB
        exact (tendsto_congr' heqB).mpr htB
      · rw [ite_eq_right hx0]
        exact (tendsto_congr' heqB).mpr htB
    · rw [notMem_closure_iff_nhdsWithin_eq_bot.mp hxB]
      exact tendsto_bot

end Work.Engulf.E4Aux
