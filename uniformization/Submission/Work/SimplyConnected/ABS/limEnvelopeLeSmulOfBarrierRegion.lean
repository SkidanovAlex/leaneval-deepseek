import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg
import Submission.Work.SimplyConnected.ABS.le_of_frontier_limsup_preconnected_region

/-!
# The barrier comparison for the limsup Perron envelope, region form

`Submission.limEnvelope_le_smul_of_barrier` states the comparison
`limEnvelope U f M ≤ (M/m) · β` under the hypothesis `[PreconnectedSpace X]`.  Here is the same
statement with that global instance replaced by the *local* hypothesis `IsPreconnected U` (plus
compact closure and nonempty frontier), which is what the globalized-barrier construction needs: a
Riemann surface need not be connected, and the comparison is applied to the components of
`Ω ∩ chartBall …`.

The proof is the same maximum-principle argument as in
`Submission.Work.SimplyConnected.ABS.limEnvelope_le_smul_of_barrier`; the only change is that the
maximum principle `Submission.SubharmonicOnX.le_of_frontier_limsup` is replaced by the region
version `le_of_frontier_limsup_preconnected_region`.
-/

open Filter Set
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.SimplyConnected.ABS

theorem limEnvelopeLeSmulOfBarrierRegion {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hU : IsOpen U) (hUpc : IsPreconnected U) (hcomp : IsCompact (closure U))
    (hne : (frontier U).Nonempty) {f : X → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hneF : (Submission.limFamily U f M).Nonempty)
    {β : X → ℝ} (hβ : Submission.SuperharmonicOnX β U) (hβ0 : ∀ x ∈ U, 0 ≤ β x)
    {K : Set X} (hKfr : K ⊆ frontier U) (hKcont : ∀ ζ ∈ K, ContinuousAt β ζ)
    {m : ℝ} (hm : 0 < m) (hmβ : ∀ ζ ∈ K, m ≤ β ζ)
    (hf : ∀ ζ ∈ frontier U, ζ ∉ K → f ζ ≤ 0) :
    ∀ x ∈ U, Submission.limEnvelope U f M x ≤ (M / m) * β x := by
  have hMm : 0 ≤ M / m := div_nonneg hM hm.le
  -- scaling by a nonnegative constant preserves superharmonicity; the library lemma
  -- `SuperharmonicOnX.const_mul` carries a spurious `[PreconnectedSpace X]`, so we inline it.
  have hsmul : Submission.SuperharmonicOnX (fun x => (M / m) * β x) U := by
    refine ⟨hβ.1.const_mul (M / m), fun x hx => ?_⟩
    obtain ⟨hxsrc, ρh, hρh, htgt, hch, hmvh⟩ := hβ.2 x hx
    have hfun : (fun y => (M / m) * β y) ∘ (chartAt ℂ x).symm
        = fun w => (M / m) * (β ∘ (chartAt ℂ x).symm) w := by
      funext w; rfl
    refine ⟨hxsrc, ρh, hρh, htgt, ?_, ?_⟩
    · rw [hfun]
      exact hch.const_mul (M / m)
    · intro p hp r hr hrsub
      have hca : Real.circleAverage (fun w => (M / m) * (β ∘ (chartAt ℂ x).symm) w) p r
          = (M / m) * Real.circleAverage (β ∘ (chartAt ℂ x).symm) p r := by
        simpa using Real.circleAverage_fun_smul (f := β ∘ (chartAt ℂ x).symm) (a := M / m)
          (c := p) (R := r)
      rw [hfun, hca]
      exact mul_le_mul_of_nonneg_left (hmvh p hp r hr hrsub) hMm
  -- Every member of the Perron family is dominated by the rescaled barrier.
  have hmem : ∀ v ∈ Submission.limFamily U f M, ∀ x ∈ U, v x ≤ (M / m) * β x := by
    intro v hv
    have hsub : Submission.SubharmonicOnX (fun x => v x - (M / m) * β x) U :=
      Submission.SubharmonicOnX.sub_superharmonicOnX (Submission.limFamily_subharmonic hv) hsmul
    have hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ z in 𝓝[U] ξ, (v z - (M / m) * β z) ≤ 0 + ε := by
      intro ζ hζ ε hε
      by_cases hζK : ζ ∈ K
      · set δ : ℝ := ε * m / (M + 1) with hδdef
        have hM1 : (0 : ℝ) < M + 1 := by linarith
        have hδpos : 0 < δ := by rw [hδdef]; positivity
        have hδle : (M / m) * δ ≤ ε := by
          rw [hδdef]
          have heq : (M / m) * (ε * m / (M + 1)) = M * ε / (M + 1) := by
            field_simp
          rw [heq, div_le_iff₀ hM1]
          nlinarith
        have hcont : ContinuousAt β ζ := hKcont ζ hζK
        have hmem' : Set.Ioi (β ζ - δ) ∈ 𝓝 (β ζ) :=
          isOpen_Ioi.mem_nhds (by show β ζ - δ < β ζ; linarith)
        have hev : ∀ᶠ z in 𝓝 ζ, β ζ - δ < β z := hcont.eventually hmem'
        have hevU : ∀ᶠ z in 𝓝[U] ζ, β ζ - δ < β z :=
          hev.filter_mono nhdsWithin_le_nhds
        filter_upwards [hevU] with z hzβ
        have hzβ' : m - δ ≤ β z := by linarith [hmβ ζ hζK]
        have hvz : v z ≤ M := Submission.limFamily_bound hv z
        have hgmul : (M / m) * (m - δ) ≤ (M / m) * β z :=
          mul_le_mul_of_nonneg_left hzβ' hMm
        have hid : M - (M / m) * (m - δ) = (M / m) * δ := by
          rw [mul_sub, div_mul_cancel₀ M (ne_of_gt hm)]
          ring
        linarith
      · have hfζ : f ζ ≤ 0 := hf ζ hζ hζK
        have hlimv : ∀ᶠ z in 𝓝[U] ζ, v z ≤ f ζ + ε := Submission.limFamily_limsup hv hζ hε
        filter_upwards [hlimv, self_mem_nhdsWithin] with z hz hzU
        have hβz : 0 ≤ β z := hβ0 z hzU
        have hWz : 0 ≤ (M / m) * β z := mul_nonneg hMm hβz
        linarith
    have hle := le_of_frontier_limsup_preconnected_region hU hUpc hsub hcomp hne (a := 0) hlim
    intro x hx
    have hx' := hle x hx
    linarith
  intro x hx
  rw [Submission.limEnvelope, Submission.upperEnvelope]
  refine csSup_le ((Submission.limFamily_isPerronOn hU hneF).nonempty.image _) ?_
  rintro y ⟨v, hv, rfl⟩
  exact hmem v hv x hx

end Work.SimplyConnected.ABS
