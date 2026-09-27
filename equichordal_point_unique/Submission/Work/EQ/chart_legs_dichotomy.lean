import Mathlib
import Submission.Work.EQ.EquiLocalDefs
import Submission.Work.EQ.roots_small_of_centre_eq
import Submission.Work.EQ.legDom_preconnected
import Submission.Work.EQ.chart_leg_meets_open
import Submission.Work.EQ.chart_leg_meets_closed
import Submission.Work.EQ.legFibre_eq_of_legImg_eq

set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace Work.EQ

open Filter _root_.Topology

/-- **Core assembly of the leg dichotomy.**  Suppose two pieces of `H0` over the value disc
`ball u₁ ρ`,
* `E '' {ζ ≠ 0 | ‖κ ζ^k‖ < ρ}` and `F '' {η ≠ 0 | ‖κ' η^{k'}‖ < ρ}`,
are such that the set of parameters `ζ` for which the `E`-point lies on the `F`-piece is both
open (`hopen`) and relatively closed in the orbit domain (`hclosed`), and that the orbit domain
is preconnected (`hpre`).  Then meeting at one parameter forces the two pieces to be equal.
The hypotheses `hopen`, `hclosed`, `hpre` are supplied by
`Work.EQ.chart_leg_meets_open`, `Work.EQ.chart_leg_meets_closed` and
`Work.EQ.legDom_preconnected`. -/
private lemma legImg_subset_of_meets {E F : ℂ → ChainData} {κ κ' : ℂ} {k k' : ℕ} {ρ : ℝ}
    (hopen : ∀ ζ : ℂ, ζ ≠ 0 → ‖κ * ζ ^ k‖ < ρ →
      E ζ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} →
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball ζ ε ⊆
        {ζ' : ℂ | ζ' ≠ 0 ∧ ‖κ * ζ' ^ k‖ < ρ ∧
          E ζ' ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}})
    (hclosed : ∀ ζ : ℂ, ζ ≠ 0 → ‖κ * ζ ^ k‖ < ρ →
      ζ ∈ closure {ζ' : ℂ | ζ' ≠ 0 ∧ ‖κ * ζ' ^ k‖ < ρ ∧
          E ζ' ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}} →
      E ζ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ})
    (hpre : IsPreconnected {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ})
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ≠ 0) (hζ₀ρ : ‖κ * ζ₀ ^ k‖ < ρ)
    (hζ₀F : E ζ₀ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}) :
    E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} ⊆
      F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} := by
  set C : Set ℂ := {ζ' : ℂ | ζ' ≠ 0 ∧ ‖κ * ζ' ^ k‖ < ρ ∧
    E ζ' ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}} with hC
  -- the orbit domain
  have hCopen : ∀ ζ : ℂ, ζ ∈ C → ∃ ε : ℝ, 0 < ε ∧ Metric.ball ζ ε ⊆ C := by
    intro ζ hζ
    rw [hC] at hζ
    exact hopen ζ hζ.1 hζ.2.1 hζ.2.2
  have hCclosed : ∀ ζ : ℂ, ζ ≠ 0 → ‖κ * ζ ^ k‖ < ρ → ζ ∈ closure C → ζ ∈ C := by
    intro ζ h1 h2 hcl
    rw [hC]
    exact ⟨h1, h2, hclosed ζ h1 h2 hcl⟩
  have hζ₀C : ζ₀ ∈ C := by rw [hC]; exact ⟨hζ₀, hζ₀ρ, hζ₀F⟩
  have hsub : ({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) ⊆
      closure C ∪ closure (({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) \ C) := by
    intro ζ hζ
    by_cases h : ζ ∈ C
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure ⟨hζ, h⟩)
  have hdisj : ({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) ∩
      (closure C ∩ closure (({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) \ C)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ζ hζ
    obtain ⟨hζΩ, hζclC, hζclD⟩ := hζ
    have hζmem : ζ ∈ ({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) := hζΩ
    obtain ⟨hζ1, hζ2⟩ := hζmem
    have hζC : ζ ∈ C := hCclosed ζ hζ1 hζ2 hζclC
    obtain ⟨ε, hε, hball⟩ := hCopen ζ hζC
    obtain ⟨ζ', hζ'mem, hζ'dist⟩ := Metric.mem_closure_iff.mp hζclD ε hε
    exact hζ'mem.2 (hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hζ'dist)))
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hpre (closure C)
      (closure (({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) \ C))
      isClosed_closure isClosed_closure hsub hdisj) with hcase | hcase
  · intro q hq
    obtain ⟨ζ, hζΩ, rfl⟩ := hq
    have hζmem : ζ ∈ ({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) := hζΩ
    obtain ⟨hζ1, hζ2⟩ := hζmem
    exact (hCclosed ζ hζ1 hζ2 (hcase ⟨hζ1, hζ2⟩)).2.2
  · exfalso
    have hζ₀Ω : ζ₀ ∈ ({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) := ⟨hζ₀, hζ₀ρ⟩
    have hcl : ζ₀ ∈ closure (({ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} : Set ℂ) \ C) := hcase hζ₀Ω
    obtain ⟨ε, hε, hball⟩ := hCopen ζ₀ hζ₀C
    obtain ⟨ζ', hζ'mem, hζ'dist⟩ := Metric.mem_closure_iff.mp hcl ε hε
    exact hζ'mem.2 (hball (Metric.mem_ball.mpr (by rw [dist_comm]; exact hζ'dist)))


namespace Work.EQ

/-- **Two legs with the same centre `u₁` either agree over every nearby value or are disjoint.**
If for some value near `u₁` (but different from it) two legs meet, then they have exactly the same
points over every value near `u₁`.  This is the dichotomy used for deduplicating the pieces (and
it also implies that two legs kept as different pieces never share a point). -/
theorem chart_legs_dichotomy {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h) {u₁ : ℂ} (hu₁ : u₁ ≠ 0)
    {E F : ℂ → ChainData} {κ κ' : ℂ} {k k' : ℕ} (hE : IsChartData a h E u₁ κ k)
    (hF : IsChartData a h F u₁ κ' k')
    (hES : E '' (Metric.ball (0 : ℂ) 1 \ {0}) ⊆ connectedComponentIn (H0 a h) p)
    (hFS : F '' (Metric.ball (0 : ℂ) 1 \ {0}) ⊆ connectedComponentIn (H0 a h) p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ → ∀ v ∈ Metric.ball u₁ ρ, v ≠ u₁ →
      (legFibre E u₁ u κ k ∩ legFibre F u₁ u κ' k').Nonempty →
      legFibre E u₁ v κ k = legFibre F u₁ v κ' k' := by
  have hk : 0 < k := hE.1
  have hκ : κ ≠ 0 := hE.2.1
  have hk' : 0 < k' := hF.1
  have hκ' : κ' ≠ 0 := hF.2.1
  obtain ⟨ρE, hρE, hsmallE₀⟩ := roots_small_of_centre_eq hκ hk (δ := 1) one_pos
  obtain ⟨ρF, hρF, hsmallF₀⟩ := roots_small_of_centre_eq hκ' hk' (δ := 1) one_pos
  set ρ : ℝ := min ρE (min ρF (min (‖κ‖ / 2) (‖κ'‖ / 2))) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]; exact lt_min hρE (lt_min hρF (lt_min (by positivity) (by positivity)))
  have hρ_le_ρE : ρ ≤ ρE := by rw [hρdef]; exact min_le_left _ _
  have hρ_le_ρF : ρ ≤ ρF := by rw [hρdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_le_κ : ρ ≤ ‖κ‖ / 2 := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ_le_κ' : ρ ≤ ‖κ'‖ / 2 := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsmallE : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ * ζ ^ k = u → ‖ζ‖ < 1 := by
    intro u ζ hu h
    have h' := hsmallE₀ u ζ (lt_of_lt_of_le hu hρ_le_ρE) h
    simpa [dist_zero_right] using h'
  have hsmallF : ∀ u ζ : ℂ, dist u u₁ < ρ → u₁ + κ' * ζ ^ k' = u → ‖ζ‖ < 1 := by
    intro u ζ hu h
    have h' := hsmallF₀ u ζ (lt_of_lt_of_le hu hρ_le_ρF) h
    simpa [dist_zero_right] using h'
  have hpreE : IsPreconnected {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} :=
    legDom_preconnected hκ hk hρ
  have hpreF : IsPreconnected {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} :=
    legDom_preconnected hκ' hk' hρ
  have hopenE : ∀ ζ : ℂ, ζ ≠ 0 → ‖κ * ζ ^ k‖ < ρ →
      E ζ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} →
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball ζ ε ⊆
        {ζ' : ℂ | ζ' ≠ 0 ∧ ‖κ * ζ' ^ k‖ < ρ ∧
          E ζ' ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}} :=
    fun ζ h1 h2 h3 => chart_leg_meets_open ha0 ha1 hh hE hF hρ hsmallE hsmallF h1 h2 h3
  have hopenF : ∀ η : ℂ, η ≠ 0 → ‖κ' * η ^ k'‖ < ρ →
      F η ∈ E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} →
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball η ε ⊆
        {η' : ℂ | η' ≠ 0 ∧ ‖κ' * η' ^ k'‖ < ρ ∧
          F η' ∈ E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ}} :=
    fun η h1 h2 h3 => chart_leg_meets_open ha0 ha1 hh hF hE hρ hsmallF hsmallE h1 h2 h3
  have hclosedE : ∀ ζ : ℂ, ζ ≠ 0 → ‖κ * ζ ^ k‖ < ρ →
      ζ ∈ closure {ζ' : ℂ | ζ' ≠ 0 ∧ ‖κ * ζ' ^ k‖ < ρ ∧
          E ζ' ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ}} →
      E ζ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} :=
    fun ζ h1 h2 h3 => chart_leg_meets_closed ha0 ha1 hh hE hF hρ hsmallE hsmallF hρ_le_κ' h1 h2 h3
  have hclosedF : ∀ η : ℂ, η ≠ 0 → ‖κ' * η ^ k'‖ < ρ →
      η ∈ closure {η' : ℂ | η' ≠ 0 ∧ ‖κ' * η' ^ k'‖ < ρ ∧
          F η' ∈ E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ}} →
      F η ∈ E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} :=
    fun η h1 h2 h3 => chart_leg_meets_closed ha0 ha1 hh hF hE hρ hsmallF hsmallE hρ_le_κ h1 h2 h3
  refine ⟨ρ, hρ, ?_⟩
  intro u hu hun v hv hvn hmeet
  obtain ⟨q, hqE, hqF⟩ := hmeet
  simp only [legFibre, Set.mem_image, Set.mem_ofPred_eq] at hqE hqF
  obtain ⟨ζ₀, ⟨hζ₀, hζ₀val⟩, hζ₀eq⟩ := hqE
  obtain ⟨η₀, ⟨hη₀, hη₀val⟩, hη₀eq⟩ := hqF
  have hζ₀ρ : ‖κ * ζ₀ ^ k‖ < ρ := by
    have h1 : κ * ζ₀ ^ k = u - u₁ := by rw [← hζ₀val]; ring
    rw [h1, ← dist_eq_norm]
    exact hu
  have hη₀ρ : ‖κ' * η₀ ^ k'‖ < ρ := by
    have h1 : κ' * η₀ ^ k' = u - u₁ := by rw [← hη₀val]; ring
    rw [h1, ← dist_eq_norm]
    exact hu
  have heq : E ζ₀ = F η₀ := by rw [hζ₀eq, hη₀eq]
  have hζ₀F : E ζ₀ ∈ F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} :=
    ⟨η₀, ⟨hη₀, hη₀ρ⟩, heq.symm⟩
  have hη₀E : F η₀ ∈ E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} :=
    ⟨ζ₀, ⟨hζ₀, hζ₀ρ⟩, heq⟩
  have hsub₁ := legImg_subset_of_meets (E := E) (F := F) (κ := κ) (κ' := κ')
    (k := k) (k' := k') hopenE hclosedE hpreE hζ₀ hζ₀ρ hζ₀F
  have hsub₂ := legImg_subset_of_meets (E := F) (F := E) (κ := κ') (κ' := κ)
    (k := k') (k' := k) hopenF hclosedF hpreF hη₀ hη₀ρ hη₀E
  have himg : E '' {ζ : ℂ | ζ ≠ 0 ∧ ‖κ * ζ ^ k‖ < ρ} =
      F '' {η : ℂ | η ≠ 0 ∧ ‖κ' * η ^ k'‖ < ρ} := le_antisymm hsub₁ hsub₂
  exact legFibre_eq_of_legImg_eq hE hF hρ hsmallE hsmallF himg hv hvn

end Work.EQ

/- The file template opens `namespace Work.EQ` once for the module and the requested statement
opened it once more, so the declaration whose proof is above lives at the name
`Work.EQ.Work.EQ.chart_legs_dichotomy`; the `end` above pops back to `Work.EQ`.  The same lemma
is therefore also exposed under the requested name `Work.EQ.chart_legs_dichotomy`. -/

/-- **Two legs with the same centre `u₁` either agree over every nearby value or are disjoint.**
Alias of `Work.EQ.Work.EQ.chart_legs_dichotomy` under the requested name. -/
theorem chart_legs_dichotomy {a : ℝ} {h : ℂ → ℂ} {r : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hh : IsStableGerm a h r) {p : ChainData} (hp : p ∈ H0 a h) {u₁ : ℂ} (hu₁ : u₁ ≠ 0)
    {E F : ℂ → ChainData} {κ κ' : ℂ} {k k' : ℕ} (hE : IsChartData a h E u₁ κ k)
    (hF : IsChartData a h F u₁ κ' k')
    (hES : E '' (Metric.ball (0 : ℂ) 1 \ {0}) ⊆ connectedComponentIn (H0 a h) p)
    (hFS : F '' (Metric.ball (0 : ℂ) 1 \ {0}) ⊆ connectedComponentIn (H0 a h) p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ Metric.ball u₁ ρ, u ≠ u₁ → ∀ v ∈ Metric.ball u₁ ρ, v ≠ u₁ →
      (legFibre E u₁ u κ k ∩ legFibre F u₁ u κ' k').Nonempty →
      legFibre E u₁ v κ k = legFibre F u₁ v κ' k' :=
  Work.EQ.Work.EQ.chart_legs_dichotomy ha0 ha1 hh hp hu₁ hE hF hES hFS

end Work.EQ
