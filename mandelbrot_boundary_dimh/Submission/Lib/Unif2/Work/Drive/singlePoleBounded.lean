import Mathlib
import Submission.Lib.Unif2.Work.Drive.Interfaces
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.Defs
import Submission.Lib.Unif2.Work.Drive.greenExhaustion_locallyBounded
import Submission.Lib.Unif2.Work.Drive.greenExhaustionParabolicBounded
import Submission.Lib.Unif2.Work.Drive.harmonicMontelEventually
import Submission.Lib.Unif2.Work.Drive.hasLogPoleOn_of_isGreenOn_limit
import Submission.Lib.Unif2.Work.Drive.bddAbove_off_compact_of_isGreenOn_limit

namespace Work.Drive

open Filter Set
open scoped Topology Manifold ContDiff

section Helpers

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- A compact set contained in the union of a monotone sequence of open sets lies in one member. -/
theorem exists_subset_iUnion_of_isCompact_spb {Ω : ℕ → Set X} (hΩo : ∀ n, IsOpen (Ω n))
    (hmono : ∀ n, Ω n ⊆ Ω (n + 1)) {K : Set X} (hK : IsCompact K)
    (hcov : (⋃ n, Ω n) = Set.univ) : ∃ N : ℕ, K ⊆ Ω N := by
  classical
  have hcov' : K ⊆ ⋃ n, Ω n := by rw [hcov]; exact Set.subset_univ K
  obtain ⟨t, hKt⟩ := hK.elim_finite_subcover Ω hΩo hcov'
  obtain ⟨N, hN⟩ := t.exists_nat_subset_range
  have hmono' : ∀ {m n : ℕ}, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  refine ⟨N, fun x hx => ?_⟩
  obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp (hKt hx)
  exact hmono' (le_of_lt (Finset.mem_range.mp (hN hit))) hxi

/-- **The hyperbolic case.**  A *unit* Green function at `a`
(`Work.UnitGreen.IsUnitGreenFunctionAt`: positive, harmonic, unit logarithmic pole, superlevel sets
with compact closure) has all three properties required by `Work.Drive.singlePoleBounded`. -/
theorem singlePoleBounded_of_isUnitGreen_spb {a : X}
    (h : ∃ E : X → ℝ, Work.UnitGreen.IsUnitGreenFunctionAt (X := X) a E) :
    ∃ E : X → ℝ, Submission.HarmonicOnX E (Set.univ \ {a}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, E x ≤ 1 := by
  obtain ⟨E, hE⟩ := h
  obtain ⟨K, hK, hKle⟩ := hE.1.exists_isCompact_subset (show (0 : ℝ) < 1 by norm_num)
  have hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E := by
    obtain ⟨C, V, hV, hCV⟩ := hE.2
    exact ⟨C, V, hV, fun x hxV _ hxne => hCV x hxV hxne⟩
  exact ⟨E, hE.1.harmonic, hpole, K, hK, fun x hx => le_of_lt (hKle x hx)⟩

end Helpers

section Main

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **The assembly.**  From an exhaustion with Green functions whose normalisations are locally
bounded off the pole one obtains a harmonic function on `X ∖ {a}` with a unit logarithmic pole at `a`
that is bounded above off a compact set.  Montel's theorem
(`Work.Drive.harmonicMontelEventually`) gives the locally uniform limit `E`, the unit pole passes to
the limit (`Work.Drive.hasLogPoleOn_of_isGreenOn_limit`), the maximum principle bounds the limit by
a constant `c` off a compact set (`Work.Drive.bddAbove_off_compact_of_isGreenOn_limit`) — this is
the part contributed by this file — and shifting by `c - 1` turns `≤ c` into `≤ 1`. -/
theorem singlePoleBounded_of_greenExhaustion_spb {a x₁ : X} {Ω : ℕ → Set X} {G : ℕ → X → ℝ}
    (hΩo : ∀ n, IsOpen (Ω n)) (hΩc : ∀ n, IsCompact (closure (Ω n)))
    (hmono : ∀ n, Ω n ⊆ Ω (n + 1)) (hcov : (⋃ n, Ω n) = Set.univ)
    (haΩ : ∀ n, a ∈ Ω n) (hG : ∀ n, Work.SimplyConnected.ABS.IsGreenOn (Ω n) a (G n))
    (hbdd : ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} → ∃ C : ℝ, ∀ n, ∀ x ∈ K,
      |G n x - G n x₁| ≤ C) :
    ∃ E : X → ℝ, Submission.HarmonicOnX E (Set.univ \ {a}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, E x ≤ 1 := by
  classical
  haveI : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  have hmono' : ∀ m n : ℕ, m ≤ n → Ω m ⊆ Ω n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  have hYopen : IsOpen (Set.univ \ {a} : Set X) := by
    rw [← Set.compl_eq_univ_sdiff]
    exact isOpen_compl_singleton
  have hev : ∀ K : Set X, K ⊆ Set.univ \ {a} → IsCompact K →
      ∃ O : Set X, IsOpen O ∧ K ⊆ O ∧ O ⊆ Set.univ \ {a} ∧
        ∃ N : ℕ, ∀ n ≥ N, Submission.HarmonicOnX (fun x => G n x - G n x₁) O := by
    intro K hKsub hK
    obtain ⟨N, hN⟩ := exists_subset_iUnion_of_isCompact_spb hΩo hmono hK hcov
    refine ⟨Ω N \ {a}, (hΩo N).sdiff isClosed_singleton, fun x hx => ⟨hN hx, (hKsub hx).2⟩,
      fun x hx => ⟨mem_univ x, hx.2⟩, N, fun n hn x hx => ?_⟩
    exact ((hG n).2.1 x ⟨hmono' N n hn hx.1, by simpa using hx.2⟩).sub
      (Submission.harmonicOnXAt_const (G n x₁))
  have hbdd' : ∀ K : Set X, K ⊆ Set.univ \ {a} → IsCompact K →
      ∃ C : ℝ, ∀ n : ℕ, ∀ x ∈ K, |G n x - G n x₁| ≤ C :=
    fun K hKsub hK => hbdd K hK hKsub
  have hbdd'' : ∀ K : Set X, IsCompact K → K ⊆ Set.univ \ {a} →
      ∃ C : ℝ, ∀ n : ℕ, ∀ x ∈ K, |G n x - G n x₁| ≤ C :=
    fun K hK hKsub => hbdd K hK hKsub
  obtain ⟨φ, E, hφ, hEharm, hconv⟩ := harmonicMontelEventually hYopen hev hbdd'
  have hpole : Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E :=
    hasLogPoleOn_of_isGreenOn_limit haΩ hΩo hmono hG hconv hbdd''
  obtain ⟨K, c, hKcomp, hKle⟩ :=
    bddAbove_off_compact_of_isGreenOn_limit haΩ hΩo hΩc hmono hcov hφ.tendsto_atTop hG hconv
  refine ⟨fun x => E x - (c - 1), ?_, ?_, K, hKcomp, ?_⟩
  · intro x hx
    exact (hEharm x hx).sub
      (show Submission.HarmonicOnXAt (fun _ : X => c - 1) x from
        Submission.harmonicOnXAt_const (c - 1))
  · obtain ⟨C, V, hV, hCV⟩ := hpole
    refine ⟨C + |c - 1|, V, hV, fun x hxV hxΩ hxne => ?_⟩
    have h1 : |E x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖| ≤ C := hCV x hxV hxΩ hxne
    have h2 : (E x - (c - 1)) + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖ =
        (E x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖) - (c - 1) := by ring
    rw [h2, sub_eq_add_neg]
    calc |(E x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖) + -(c - 1)|
        ≤ |E x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖| + |-(c - 1)| :=
          abs_add_le _ _
      _ = |E x + Real.log ‖(chartAt ℂ a) x - (chartAt ℂ a) a‖| + |c - 1| := by rw [abs_neg]
      _ ≤ C + |c - 1| := by linarith
  · intro x hxK
    have h1 : E x ≤ c := hKle x hxK
    linarith

/-- **A unit-log-pole harmonic function which is bounded above off a compact set.**
Careful with the sign convention: `HasLogPoleOn (univ \ {a}) a E` means `E + log‖ζ_a - ζ_a a‖`
is bounded near `a`, i.e. `E ≈ -log‖ζ_a - ζ_a a‖ → +∞` at `a`. So on `X = ℂ`, `a = 0` the model
example is `E = -log‖z‖` (NOT `+log‖z‖`): it is harmonic on `ℂ ∖ {0}`, has the unit pole, and
`E ≤ 0` for `‖z‖ ≥ 1`. (An entire-function argument shows that *every* such `E` on `ℂ` is
`-log‖z-a‖ + const`, hence bounded above off a compact set — so the claim is true there.)

Route: for a relatively compact exhaustion `Ω_n` and a chart ball `D` around `a` with `D̄ ⊆ Ω_1`,
solve the Dirichlet problem on `Ω_n ∖ D̄` with fixed boundary datum `ψ` on `∂D` (the local model
`-log‖ζ-ζ_a‖ + c`) and datum `0` on `∂Ω_n`; glue with the local model inside `D`. The maximum
principle gives `E_n ≤ max (0, sup_∂D ψ)` for every `n`, so the sequence is uniformly bounded above
on compacts, and a locally uniformly convergent subsequence (compactness of locally bounded
harmonic functions) has the required unit pole and bound. -/
theorem singlePoleBounded {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (a : X) :
    ∃ E : X → ℝ, Submission.HarmonicOnX E (Set.univ \ {a}) ∧
      Work.SimplyConnected.ABS.HasLogPoleOn (Set.univ \ {a}) a E ∧
      ∃ K : Set X, IsCompact K ∧ ∀ x ∉ K, E x ≤ 1 := by
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : X, x₁ ≠ a := by
    by_contra h
    push_neg at h
    have huniv : (Set.univ : Set X) = {a} :=
      (Set.eq_univ_of_forall fun x => by rw [Set.mem_singleton_iff]; exact h x).symm
    exact hX (isCompact_univ_iff.mp (by rw [huniv]; exact isCompact_singleton))
  by_cases hW : Work.Drive.WeakGreenAt X a
  · obtain ⟨Ω, G, hΩo, hΩc, hmono, hcov, haΩ, -, hG, -, hbdd⟩ :=
      greenExhaustion_locallyBounded_of_weakGreen (X := X) hX a x₁ hx₁ hW
    exact singlePoleBounded_of_greenExhaustion_spb hΩo hΩc hmono hcov haΩ hG hbdd
  · obtain ⟨Ω, G, hΩo, hΩc, hmono, hcov, haΩ, -, hG, -, hbdd⟩ :=
      greenExhaustionParabolicBounded (X := X) hX a x₁ hx₁ hW
    exact singlePoleBounded_of_greenExhaustion_spb hΩo hΩc hmono hcov haΩ hG hbdd

end Main

end Work.Drive
