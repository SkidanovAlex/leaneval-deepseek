import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law

/-!
# The joint law of the head and the tail of the canonical exponential product

`canonM = ⊗_{n} Exp(1)` is the law of an iid sequence of standard exponentials on `ℕ → ℝ`.
The map `x ↦ (x 0, cshift x)` splits off the first coordinate; its pushforward is the product
of the law of `x 0` (which is `expLaw`) with the law of the tail (`cshift x`), which is again
`canonM`.  This is the (head, tail) independence statement for the infinite product measure.

The proof goes through the inverse map `ccons : ℝ × (ℕ → ℝ) → (ℕ → ℝ)` and the
characterisation `Measure.eq_infinitePi` of the product measure by its values on finite
product ("box") sets.
-/

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open MeasureTheory
open scoped ENNReal

noncomputable section

lemma ccons_zero (p : ℝ × (ℕ → ℝ)) : ccons p 0 = p.1 := rfl

lemma ccons_succ (p : ℝ × (ℕ → ℝ)) (i : ℕ) : ccons p (i + 1) = p.2 i := rfl

lemma ccons_eq_of_ne_zero (p : ℝ × (ℕ → ℝ)) {i : ℕ} (hi : i ≠ 0) : ccons p i = p.2 (i - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  rfl

/-- The preimage under `ccons` of a finite product set is a rectangle: the first coordinate
is constrained (only) when `0 ∈ s`, and the tail is constrained along the shifted index set
`(s.erase 0).image (· - 1)`. -/
lemma ccons_preimage_pi (s : Finset ℕ) (t : ℕ → Set ℝ) :
    ccons ⁻¹' (Set.pi (s : Set ℕ) t)
      = (if 0 ∈ s then t 0 else Set.univ) ×ˢ
        Set.pi (((s.erase 0).image (fun i => i - 1) : Finset ℕ) : Set ℕ) (fun j => t (j + 1)) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe]
  constructor
  · intro h
    constructor
    · by_cases h0 : 0 ∈ s
      · rw [if_pos h0]
        have := h 0 h0
        rwa [ccons_zero] at this
      · rw [if_neg h0]; exact trivial
    · intro j hj
      rw [Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [Finset.mem_erase] at hi
      obtain ⟨hine, his⟩ := hi
      rw [← ccons_eq_of_ne_zero p hine]
      have heq : i - 1 + 1 = i := by omega
      rw [heq]
      exact h i his
  · rintro ⟨h1, h2⟩ i hi
    by_cases hi0 : i = 0
    · subst hi0
      by_cases h0 : 0 ∈ s
      · rw [if_pos h0] at h1; rw [ccons_zero]; exact h1
      · exact absurd hi h0
    · rw [ccons_eq_of_ne_zero p hi0]
      have hmem : i - 1 ∈ (s.erase 0).image (fun i => i - 1) :=
        Finset.mem_image.mpr ⟨i, by rw [Finset.mem_erase]; exact ⟨hi0, hi⟩, rfl⟩
      have := h2 (i - 1) hmem
      have heq : i - 1 + 1 = i := by omega
      rw [heq] at this
      exact this

/-- Reindexing a product along the bijection `i ↦ i + 1` between `s.erase 0` and
`(s.erase 0).image (· - 1)`. -/
lemma prod_image_sub_one (s : Finset ℕ) (g : ℕ → ℝ≥0∞) :
    ∏ j ∈ (s.erase 0).image (fun i => i - 1), g (j + 1) = ∏ i ∈ s.erase 0, g i := by
  have hinj : Set.InjOn (fun i => i - 1) ↑(s.erase 0) := by
    intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_erase] at ha hb
    change a - 1 = b - 1 at hab
    omega
  have h1 := Finset.prod_image (s := s.erase 0) (g := fun i => i - 1)
    (f := fun j => g (j + 1)) hinj
  rw [h1]
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.mem_erase] at hx
  rw [show x - 1 + 1 = x by omega]

/-- The box identity: `expLaw.prod canonM` gives a finite product set in `ℕ → ℝ` the mass
`∏ i ∈ s, expLaw (t i)`. -/
lemma map_ccons_prod_apply (s : Finset ℕ) (t : ℕ → Set ℝ) (ht : ∀ i, MeasurableSet (t i)) :
    (expLaw.prod canonM) (ccons ⁻¹' (Set.pi (s : Set ℕ) t)) = ∏ i ∈ s, expLaw (t i) := by
  rw [ccons_preimage_pi, Measure.prod_prod]
  have htail : canonM (Set.pi (((s.erase 0).image (fun i => i - 1) : Finset ℕ) : Set ℕ)
        (fun j => t (j+1)))
      = ∏ j ∈ (s.erase 0).image (fun i => i - 1), expLaw (t (j+1)) := by
    rw [canonM]
    exact Measure.infinitePi_pi _ (fun j _ => ht (j+1))
  have hprod : ∏ j ∈ (s.erase 0).image (fun i => i - 1), expLaw (t (j+1))
      = ∏ i ∈ s.erase 0, expLaw (t i) := prod_image_sub_one s (fun i => expLaw (t i))
  rw [htail, hprod]
  by_cases h0 : 0 ∈ s
  · rw [if_pos h0, Finset.mul_prod_erase s (fun i => expLaw (t i)) h0]
  · rw [if_neg h0, measure_univ, one_mul, Finset.erase_eq_of_notMem h0]

/-- The pushforward of `expLaw.prod canonM` under `ccons` is `canonM`. -/
lemma map_ccons_eq_canonM : (expLaw.prod canonM).map ccons = canonM := by
  rw [canonM]
  refine Measure.eq_infinitePi (fun _ : ℕ => expLaw) ?_
  intro s t ht
  rw [Measure.map_apply measurable_ccons (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
  exact map_ccons_prod_apply s t ht

theorem joint_law_head_tail : canonM.map (fun x : ℕ → ℝ => (x 0, cshift x)) = expLaw.prod canonM := by
  have hccons := map_ccons_eq_canonM
  have hcomp : (fun x : ℕ → ℝ => (x 0, cshift x)) ∘ ccons
      = (id : ℝ × (ℕ → ℝ) → ℝ × (ℕ → ℝ)) := rfl
  have hT : Measurable (fun x : ℕ → ℝ => (x 0, cshift x)) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_apply 0
    · exact measurable_cshift
  calc canonM.map (fun x : ℕ → ℝ => (x 0, cshift x))
      = ((expLaw.prod canonM).map ccons).map (fun x : ℕ → ℝ => (x 0, cshift x)) := by rw [hccons]
    _ = (expLaw.prod canonM).map ((fun x : ℕ → ℝ => (x 0, cshift x)) ∘ ccons) := by
          rw [Measure.map_map hT measurable_ccons]
    _ = (expLaw.prod canonM).map id := by rw [hcomp]
    _ = expLaw.prod canonM := Measure.map_id

end

end Work.ChenPlan.LinearSieve.Selberg.Alt
