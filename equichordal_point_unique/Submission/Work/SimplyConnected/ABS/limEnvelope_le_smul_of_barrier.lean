import Mathlib
import Submission.Work.SimplyConnected.ABS.GreenSetupReg

/-!
# The barrier comparison for the limsup Perron envelope with a partial boundary set

`Submission.limEnvelope_le_of_superharmonic_bound` compares the Perron envelope
`Submission.limEnvelope U f M` with a nonnegative superharmonic function `W` when the boundary data
`f` is `≤ 0` on the *whole* frontier of `U`.  The present lemma is the form needed when the
boundary data is only controlled **off** a closed set `K ⊆ frontier U`: one is given a nonnegative
superharmonic *barrier* `β` on `U` with `β ≥ m > 0` on `K` (and `β` continuous at the points of
`K`), and concludes the comparison against the rescaled barrier `(M / m) · β`.

The proof is the same maximum-principle argument: for a member `v` of the Perron family the
function `v - (M / m) · β` is subharmonic on `U`, and its limsup at a frontier point is `≤ 0`:

* at a point off `K`, the boundary datum gives `v ≤ f ζ + ε ≤ ε` and `(M / m) · β ≥ 0` on `U`;
* at a point of `K`, the barrier dominates the global bound `v ≤ M`, since `β ≥ m` there and `β`
  is continuous: near `ζ` inside `U` we have `(M / m) · β ≥ M - ε`.
-/

open Filter Set
open scoped Topology

namespace Work.SimplyConnected.ABS

theorem limEnvelope_le_smul_of_barrier {X : Type*} [TopologicalSpace X] [T2Space X]
    [PreconnectedSpace X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {U : Set X} (hU : IsOpen U) (hcomp : IsCompact (closure U)) (hne : (frontier U).Nonempty)
    {f : X → ℝ} {M : ℝ} (hM : 0 ≤ M) (hneF : (Submission.limFamily U f M).Nonempty)
    {β : X → ℝ} (hβ : Submission.SuperharmonicOnX β U) (hβ0 : ∀ x ∈ U, 0 ≤ β x)
    {K : Set X} (hKfr : K ⊆ frontier U) (hKcont : ∀ ζ ∈ K, ContinuousAt β ζ)
    {m : ℝ} (hm : 0 < m) (hmβ : ∀ ζ ∈ K, m ≤ β ζ)
    (hf : ∀ ζ ∈ frontier U, ζ ∉ K → f ζ ≤ 0) :
    ∀ x ∈ U, Submission.limEnvelope U f M x ≤ (M / m) * β x := by
  have hMm : 0 ≤ M / m := div_nonneg hM hm.le
  have hsmul : Submission.SuperharmonicOnX (fun x => (M / m) * β x) U :=
    Submission.SuperharmonicOnX.const_mul hMm hβ
  -- Every member of the Perron family is dominated by the rescaled barrier.
  have hmem : ∀ v ∈ Submission.limFamily U f M, ∀ x ∈ U, v x ≤ (M / m) * β x := by
    intro v hv
    have hsub : Submission.SubharmonicOnX (fun x => v x - (M / m) * β x) U :=
      Submission.SubharmonicOnX.sub_superharmonicOnX (Submission.limFamily_subharmonic hv) hsmul
    -- the limsup condition at the frontier
    have hlim : ∀ ξ ∈ frontier U, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ z in 𝓝[U] ξ, (v z - (M / m) * β z) ≤ 0 + ε := by
      intro ζ hζ ε hε
      by_cases hζK : ζ ∈ K
      · -- at a barrier point: `β ≥ m` near `ζ`, so the global bound `v ≤ M` wins
        set δ : ℝ := ε * m / (M + 1) with hδdef
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
      · -- away from the barrier set: the boundary datum applies and the barrier is nonnegative
        have hfζ : f ζ ≤ 0 := hf ζ hζ hζK
        have hlimv : ∀ᶠ z in 𝓝[U] ζ, v z ≤ f ζ + ε := Submission.limFamily_limsup hv hζ hε
        filter_upwards [hlimv, self_mem_nhdsWithin] with z hz hzU
        have hβz : 0 ≤ β z := hβ0 z hzU
        have hWz : 0 ≤ (M / m) * β z := mul_nonneg hMm hβz
        linarith
    have hle := Submission.SubharmonicOnX.le_of_frontier_limsup hU hsub hcomp hne (a := 0) hlim
    intro x hx
    have hx' := hle x hx
    linarith
  -- the envelope is the supremum of the family
  intro x hx
  rw [Submission.limEnvelope, Submission.upperEnvelope]
  refine csSup_le ((Submission.limFamily_isPerronOn hU hneF).nonempty.image _) ?_
  rintro y ⟨v, hv, rfl⟩
  exact hmem v hv x hx

end Work.SimplyConnected.ABS
