import Mathlib
import Submission.Lib.Unif2.Work.Modulus.puncturedConnected
import Submission.Work.BasinSC.StepOneCrit.isOpen_infinite

namespace Work.BasinSC.StepOneCrit

/-! If `U ⊆ ℂ` is open and connected and `F` is finite then `U ∖ F` is connected.
Helpful workspace results: `Work.Modulus.isPreconnected_compl_singleton_of_isOpen_nhds`
(module `Submission.Lib.Unif2.Work.Modulus.puncturedConnected`) and
`Work.Modulus.isPreconnected_ball_diff_center` (same module); the one-point case can be iterated
inside the subtype `↥(U ∖ F')`, whose points still have punctured balls as neighbourhoods
(`Work.Modulus.exists_isOpen_nhds_isPreconnected_diff_singleton`).  Nonemptiness of `U ∖ F`
comes from `U` being open nonempty hence infinite. -/

open Set Metric

/-- **Removing one point from a preconnected open subset of `ℂ`.**  If `W ⊆ ℂ` is open and
preconnected and `z : ℂ`, then `W ∖ {z}` is preconnected.

The proof works in the subtype `↥W`, which is a connected space: the punctured ball
`V ∖ {⟨z, _⟩} = (ball z ρ) ∖ {z}` is a preconnected open neighbourhood of `⟨z, _⟩`, so
`isPreconnected_compl_singleton_of_isOpen_nhds` applies.  Both directions of the translation
between subsets of `↥W` and subsets of `ℂ` go through `IsInducing.subtypeVal.isPreconnected_image`
together with `Subtype.val '' S`. -/
theorem isPreconnected_diff_singleton {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    (z : ℂ) : IsPreconnected (W \ {z}) := by
  by_cases hz : z ∈ W
  · haveI : ConnectedSpace ↥W := Subtype.connectedSpace ⟨⟨z, hz⟩, hWc⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hWo z hz
    have hVo : IsOpen (Subtype.val ⁻¹' Metric.ball z ρ : Set ↥W) :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    have hpV : (⟨z, hz⟩ : ↥W) ∈ (Subtype.val ⁻¹' Metric.ball z ρ : Set ↥W) := by
      simp [Metric.mem_ball, hρ]
    have hVpc : IsPreconnected ((Subtype.val ⁻¹' Metric.ball z ρ : Set ↥W) \ {⟨z, hz⟩}) := by
      rw [← Topology.IsInducing.isPreconnected_image
        (f := (Subtype.val : ↥W → ℂ)) Topology.IsInducing.subtypeVal]
      have himg : Subtype.val '' ((Subtype.val ⁻¹' Metric.ball z ρ : Set ↥W) \ {⟨z, hz⟩})
          = Metric.ball z ρ \ {z} := by
        ext y
        constructor
        · rintro ⟨w, ⟨hwV, hwp⟩, rfl⟩
          exact ⟨hwV, fun hy => hwp (Subtype.ext hy)⟩
        · rintro ⟨hy1, hy2⟩
          exact ⟨⟨y, hball hy1⟩, ⟨hy1, fun h => hy2 (congrArg Subtype.val h)⟩, rfl⟩
      rw [himg]
      exact Work.Modulus.isPreconnected_ball_diff_center hρ
    have hcompl : IsPreconnected ({⟨z, hz⟩}ᶜ : Set ↥W) :=
      Work.Modulus.isPreconnected_compl_singleton_of_isOpen_nhds hVo hpV hVpc
    have himg2 : Subtype.val '' ({⟨z, hz⟩}ᶜ : Set ↥W) = W \ {z} := by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w.2, fun hy => hw (Subtype.ext hy)⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨⟨y, hy1⟩, fun h => hy2 (congrArg Subtype.val h), rfl⟩
    have h := (Topology.IsInducing.isPreconnected_image
      (f := (Subtype.val : ↥W → ℂ)) Topology.IsInducing.subtypeVal
      (s := ({⟨z, hz⟩}ᶜ : Set ↥W))).mpr hcompl
    rwa [himg2] at h
  · rwa [Set.sdiff_singleton_eq_self hz]

theorem isConnected_diff_finite {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U)
    {F : Set ℂ} (hF : F.Finite) : IsConnected (U \ F) := by
  have hpre : IsPreconnected (U \ F) := by
    refine Set.Finite.induction_on F hF ?_ ?_
    · simpa using hUc.isPreconnected
    · intro a s has hs ih
      have hOpen : IsOpen (U \ s) := hUo.sdiff hs.isClosed
      have hstep : IsPreconnected ((U \ s) \ {a}) := isPreconnected_diff_singleton hOpen ih a
      have hEq : (U \ s) \ {a} = U \ insert a s := by
        ext x
        simp only [mem_sdiff, mem_singleton_iff, mem_insert_iff]
        tauto
      rwa [hEq] at hstep
  have hUinf : U.Infinite := isOpen_infinite hUo hUc.nonempty
  refine ⟨?_, hpre⟩
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : U ⊆ F := fun x hx => by
    by_contra hxF
    exact (Set.eq_empty_iff_forall_notMem.mp h) x ⟨hx, hxF⟩
  exact hUinf (hF.subset hsub)

end Work.BasinSC.StepOneCrit
