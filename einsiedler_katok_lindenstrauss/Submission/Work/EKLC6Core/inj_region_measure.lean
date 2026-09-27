import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLNonExc.DinjFacts

/-!
# `Work.EKLC6Core.inj_region_measure`

The "injectivity region" of the frozen component `P_X3` has measure tending to `0`:

`∀ ε > 0, ∃ η > 0, μ (mkX '' {g : SL₃(ℝ) | ∃ γ ∈ Γ₃, γ ≠ 1, g γ g⁻¹ ∈ V η}) < ε`

for **every finite** measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` (no invariance of `μ` is needed).

## The argument

Write `badRegion η` for the set in question.  A point `x = mkX g` lies in `badRegion η` iff its
stabiliser contains a nontrivial element `h = g γ g⁻¹ ∈ V η`:

* `badRegion` is **open**: the underlying set of `g` is the union, over `γ ∈ Γ₃ \ {1}`, of the
  preimages of the open set `V η` under the continuous maps `g ↦ g γ g⁻¹`, hence open; and the
  quotient map `mkX` is open (`QuotientGroup.isOpenMap_coe`).
* `badRegion` is **antitone** in `η` (larger `η` means a larger set of permitted displacements).
* For every `x ∈ X₃` there is `δ > 0` with `x ∉ badRegion δ`: this is the discreteness of the
  stabiliser of `x`, i.e. the statement that `x ∈ Dinj δ` for some `δ > 0` (EKL's `D_ℓ`; proved in
  `Work.EKLNonExc.DinjFacts`).  Indeed if `x = mkX g ∈ badRegion δ` with witness `γ ≠ 1`, then
  `h = g γ g⁻¹ ∈ V δ` is a nontrivial element of `V δ` fixing `x` (because `mkX (g γ) = mkX g`),
  contradicting `x ∈ Dinj δ` (in which the action of `V δ` on `x` is injective).

Hence `⋂ n, badRegion (1/(n+1)) = ∅`: given `x`, choose `δ > 0` with `x ∈ Dinj δ` and `n` with
`1/(n+1) < δ`; then `x ∉ badRegion δ`, and `badRegion (1/(n+1)) ⊆ badRegion δ`.  Since `μ` is a
finite measure and the sets decrease, continuity from above
(`MeasureTheory.tendsto_measure_iInter_atTop`) gives `μ (badRegion (1/(n+1))) → μ ∅ = 0`, and
the definition of convergence gives the required `η`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLC6Core

open MeasureTheory Filter Topology
open Work.EKLContract

noncomputable section

/-- **The bad region.**  The image in `X₃` of the set of `g ∈ SL₃(ℝ)` for which some nontrivial
`γ ∈ Γ₃ = SL₃(ℤ)` becomes an element of the displacement neighbourhood `V η` after conjugation by
`g`.  Equivalently (`not_mem_badRegion_of_mem_Dinj`) the set of `x` whose stabiliser meets
`V η \ {1}`. -/
def badRegion (η : ℝ) : Set X3 :=
  mkX '' {g : SL3 | ∃ γ ∈ Γ3, γ ≠ 1 ∧ g * γ * g⁻¹ ∈ V η}

/-- The defining set of `badRegion`, written as a union over `γ ∈ Γ₃ \ {1}`. -/
lemma badRegion_pre_eq_iUnion (η : ℝ) :
    {g : SL3 | ∃ γ ∈ Γ3, γ ≠ 1 ∧ g * γ * g⁻¹ ∈ V η}
      = ⋃ (γ : Γ3) (_ : (γ : SL3) ≠ 1), {g : SL3 | g * (γ : SL3) * g⁻¹ ∈ V η} := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨γ, hγ, hγne, hV⟩
    exact ⟨⟨γ, hγ⟩, hγne, hV⟩
  · rintro ⟨⟨γ, hγ⟩, hγne, hV⟩
    exact ⟨γ, hγ, hγne, hV⟩

/-- The domain of `badRegion` is open: a union of preimages of the open set `V η` under the
continuous conjugation maps `g ↦ g γ g⁻¹`, and `mkX` is an open map. -/
lemma isOpen_badRegion {η : ℝ} (hη : 0 < η) : IsOpen (badRegion η) := by
  unfold badRegion
  rw [badRegion_pre_eq_iUnion]
  refine QuotientGroup.isOpenMap_coe _ ?_
  refine isOpen_iUnion (fun γ => isOpen_iUnion (fun _ : (γ : SL3) ≠ 1 => ?_))
  exact (Work.EKLContract.Lemmas.V_open_one η hη).1.preimage (by fun_prop)

/-- `badRegion` is monotone: a larger displacement radius only enlarges the set. -/
lemma monotone_badRegion : Monotone badRegion := by
  intro η η' h x hx
  obtain ⟨g, ⟨γ, hγ, hγne, hγV⟩, hgx⟩ := hx
  exact ⟨g, ⟨γ, hγ, hγne, fun i j => lt_of_lt_of_le (hγV i j) h⟩, hgx⟩

/-- **Key point.**  If the action of `V δ` on `x` is injective (`x ∈ Dinj δ`, `δ > 0`), then no
nontrivial conjugate `g γ g⁻¹ ∈ V δ` can fix `x = mkX g`; i.e. `x ∉ badRegion δ`.

Indeed `h = g γ g⁻¹ ∈ V δ` fixes `x` because `mkX (h g) = mkX (g γ) = mkX g` (as `mkX γ = mkX 1`),
and `h ≠ 1` since `γ ≠ 1`; both `h` and `1` lie in `V δ`, so injectivity forces `h = 1`. -/
lemma not_mem_badRegion_of_mem_Dinj {δ : ℝ} (hδ : 0 < δ) {x : X3}
    (hx : x ∈ Work.EKLNonExc.Dinj δ) : x ∉ badRegion δ := by
  rintro ⟨g, ⟨γ, hγ, hγne, hγV⟩, rfl⟩
  have hne : g * γ * g⁻¹ ≠ 1 := by
    intro h1
    refine hγne ?_
    calc γ = g⁻¹ * (g * γ * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h1]
      _ = 1 := by group
  have h2 : mkX (g * γ) = mkX g := by
    refine QuotientGroup.eq.mpr ?_
    have hc : (g * γ)⁻¹ * g = γ⁻¹ := by group
    rw [hc]
    exact Γ3.inv_mem hγ
  have hfix : (g * γ * g⁻¹) • mkX g = (1 : SL3) • mkX g := by
    calc (g * γ * g⁻¹) • mkX g = mkX ((g * γ * g⁻¹) * g) :=
          (Work.EKLContract.Lemmas.mkX_mul _ _).symm
      _ = mkX (g * γ) := by rw [show (g * γ * g⁻¹) * g = g * γ by group]
      _ = mkX g := h2
      _ = (1 : SL3) • mkX g := by rw [← Work.EKLContract.Lemmas.mkX_mul, one_mul]
  have h1V : (1 : SL3) ∈ V δ := (Work.EKLContract.Lemmas.V_open_one δ hδ).2
  exact hne (Work.EKLNonExc.mem_Dinj.mp hx _ _ hγV h1V hfix)

/-- The bad regions shrink to the empty set as `η → 0⁺`. -/
lemma iInter_badRegion_eq_empty :
    (⋂ n : ℕ, badRegion (1 / ((n : ℝ) + 1))) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨δ, hδ, hxD⟩ := Work.EKLNonExc.DinjFacts.2.1 x
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hsub : badRegion (1 / ((n : ℝ) + 1)) ⊆ badRegion δ :=
    monotone_badRegion (le_of_lt hn)
  exact not_mem_badRegion_of_mem_Dinj hδ hxD (hsub (Set.mem_iInter.mp hx n))

theorem inj_region_measure {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsFiniteMeasure μ] :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      μ (Work.EKLContract.mkX '' {g : Work.EKLContract.SL3 |
            ∃ γ ∈ Work.EKLContract.Γ3, γ ≠ 1 ∧
              g * γ * g⁻¹ ∈ Work.EKLContract.V η}) < ENNReal.ofReal ε := by
  intro ε hε
  -- the sets `badRegion (1/(n+1))` decrease
  have hanti : Antitone (fun n : ℕ => badRegion (1 / ((n : ℝ) + 1))) := by
    intro m n hmn
    refine monotone_badRegion ?_
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    exact one_div_le_one_div_of_le (by positivity) hmn'
  -- they are measurable (indeed open)
  have hnull : ∀ n : ℕ, NullMeasurableSet (badRegion (1 / ((n : ℝ) + 1))) μ :=
    fun n => (isOpen_badRegion (by positivity)).measurableSet.nullMeasurableSet
  -- and one of them has finite measure, since `μ` is finite
  have hfin : ∃ n : ℕ, μ (badRegion (1 / ((n : ℝ) + 1))) ≠ ⊤ :=
    ⟨0, ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ _))
      MeasureTheory.IsFiniteMeasure.measure_univ_lt_top)⟩
  -- continuity from above, and the intersection is empty
  have htend : Tendsto (fun n : ℕ => μ (badRegion (1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (μ (⋂ n : ℕ, badRegion (1 / ((n : ℝ) + 1))))) :=
    MeasureTheory.tendsto_measure_iInter_atTop hnull hanti hfin
  have hlim : μ (⋂ n : ℕ, badRegion (1 / ((n : ℝ) + 1))) = 0 := by
    rw [iInter_badRegion_eq_empty, MeasureTheory.measure_empty]
  rw [hlim] at htend
  have hev : ∀ᶠ n : ℕ in atTop, μ (badRegion (1 / ((n : ℝ) + 1))) < ENNReal.ofReal ε := by
    have h1 := htend.eventually (isOpen_Iio.mem_nhds (ENNReal.ofReal_pos.mpr hε))
    simpa [Function.comp_def] using h1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨1 / ((N : ℝ) + 1), by positivity, ?_⟩
  exact hN N le_rfl

end

end Work.EKLC6Core
