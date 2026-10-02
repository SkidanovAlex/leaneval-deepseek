import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.montel_omits_three
import Submission.Work.Normal.JuliaBasics
import Submission.Work.Normal.JuliaIterate
import Submission.Work.Normal.unique_preimage_mem_fatou
import Submission.Work.Normal.poly_eval_surjective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Forward images and iterated preimages of the Julia set

* `exists_compl_iUnion_iterate_image_subset_singleton`: if a domain `U` meets the Julia set of a
  polynomial map of degree `≥ 2`, then `⋃ₙ f^n(U)` misses at most one point of the plane.  If it
  missed two distinct points `a`, `b`, every iterate would omit `a`, `b` and `∞`, so the omitted
  values principle (`montel_two_omitted`) would make the iterates normal on `U`.
* `subset_closure_iUnion_preimage`: consequently the iterated preimages of any point of the Julia
  set are dense in the Julia set.
-/

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology Polynomial

/-- **A domain meeting the Julia set has forward images missing at most one point.** -/
theorem exists_compl_iUnion_iterate_image_subset_singleton {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hJU : (JuliaSet f ∩ U).Nonempty) :
    ∃ a : ℂ, (⋃ n : ℕ, f^[n] '' U)ᶜ ⊆ {a} := by
  obtain ⟨P, -, hPf⟩ := hf
  have hfdiff : Differentiable ℂ f := by
    rw [show f = fun z => P.eval z from funext fun z => hPf z]
    exact Polynomial.differentiable P
  by_contra h
  have hex : ∀ a : ℂ, ∃ b ∈ (⋃ n : ℕ, f^[n] '' U)ᶜ, b ≠ a := by
    intro a
    have hnot : ¬ ((⋃ n : ℕ, f^[n] '' U)ᶜ ⊆ {a}) := fun hc => h ⟨a, hc⟩
    obtain ⟨b, hb, hbne⟩ := Set.not_subset.mp hnot
    exact ⟨b, hb, by simpa using hbne⟩
  obtain ⟨b₀, hb₀, -⟩ := hex 0
  obtain ⟨b, hb, hne⟩ := hex b₀
  have homit : ∀ n : ℕ, ∀ z ∈ U, f^[n] z ≠ b₀ ∧ f^[n] z ≠ b := by
    intro n z hz
    constructor
    · intro hc
      exact hb₀ (mem_iUnion.mpr ⟨n, show b₀ ∈ f^[n] '' U from ⟨z, hz, hc⟩⟩)
    · intro hc
      exact hb (mem_iUnion.mpr ⟨n, show b ∈ f^[n] '' U from ⟨z, hz, hc⟩⟩)
  have hhol : ∀ g ∈ iterateFamily f, DifferentiableOn ℂ g U := by
    rintro g ⟨n, rfl⟩
    exact (hfdiff.iterate n).differentiableOn
  have hnorm : IsNormalFamily (iterateFamily f) U :=
    montel_two_omitted (a := b₀) (b := b) hne.symm hU hUc hhol fun g hg z hz => by
      obtain ⟨n, rfl⟩ := hg
      exact homit n z hz
  obtain ⟨z, hzJ, hzU⟩ := hJU
  exact hzJ (fatouSet_of_mem_nhds (hU.mem_nhds hzU) hU hnorm)

/-- **Density of iterated preimages in the Julia set.** For `y` in the Julia set of a polynomial
map of degree at least two, every point of the Julia set is a limit point of the set of iterated
preimages of `y`. -/
theorem subset_closure_iUnion_preimage {d : ℕ} {f : ℂ → ℂ} (hd : 2 ≤ d)
    (hf : IsPolynomialMapOfDegree d f) {y : ℂ} (hy : y ∈ JuliaSet f) :
    JuliaSet f ⊆ closure (⋃ n : ℕ, f^[n] ⁻¹' {y}) := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro V hV
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  have hJdot : (JuliaSet f ∩ Metric.ball z r).Nonempty :=
    ⟨z, hz, Metric.mem_ball_self hr⟩
  obtain ⟨a, ha⟩ := exists_compl_iUnion_iterate_image_subset_singleton hd hf
    Metric.isOpen_ball (convex_ball z r).isPreconnected hJdot
  by_contra hcon
  have hnotmem : ∀ n : ℕ, ∀ w ∈ Metric.ball z r, f^[n] w ≠ y := by
    intro n w hw hc
    have hmem : w ∈ V ∩ ⋃ n : ℕ, f^[n] ⁻¹' {y} := by
      refine ⟨hrV hw, ?_⟩
      simp only [mem_iUnion, mem_preimage, mem_singleton_iff]
      exact ⟨n, hc⟩
    exact hcon ⟨w, hmem⟩
  have hyE : y ∉ (⋃ n : ℕ, f^[n] '' Metric.ball z r) := by
    intro hc
    obtain ⟨n, hc⟩ := mem_iUnion.mp hc
    obtain ⟨w, hw, hw'⟩ := hc
    exact hnotmem n w hw hw'
  have hpre : ∃ b : ℂ, f b = y ∧ b ≠ y := by
    by_contra h'
    push_neg at h'
    have hfy : f y = y := by
      obtain ⟨w, hw⟩ := poly_eval_surjective (by omega : 1 ≤ d) hf y
      have hwy : w = y := h' w hw
      calc f y = f w := by rw [hwy]
        _ = y := hw
    exact hy (unique_preimage_mem_fatou hd hf
      fun z => ⟨fun hz => h' z hz, fun hz => by rw [hz]; exact hfy⟩)
  obtain ⟨b, hb, hbne⟩ := hpre
  have hbE : b ∉ (⋃ n : ℕ, f^[n] '' Metric.ball z r) := by
    intro hc
    obtain ⟨n, hc⟩ := mem_iUnion.mp hc
    obtain ⟨w, hw, hw'⟩ := hc
    exact hyE (mem_iUnion.mpr ⟨n + 1, w, hw,
      by rw [Function.iterate_succ_apply', hw', hb]⟩)
  have hba : b = a := by simpa using ha hbE
  have hya : y = a := by simpa using ha hyE
  exact hbne (hba.trans hya.symm)

end Work.Normal
