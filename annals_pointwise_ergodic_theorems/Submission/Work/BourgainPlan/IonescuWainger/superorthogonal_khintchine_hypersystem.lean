import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.decouple
import Submission.Work.BourgainPlan.IonescuWainger.averaged_bound
import Submission.Work.BourgainPlan.IonescuWainger.cardLe_bound

/-!
# The hypersystem Khintchine inequality (Tao, `sys-ortho`(ii))

This file assembles the target theorem `superorthogonal_khintchine_hypersystem` from
the system form (`khintchine_hilbert`), the level-by-level decoupling (`decouple`),
the averaging over colourings (`averaged_bound`, Keller–Jiang-style probabilistic decoupling) and
the reduction to exact cardinalities (`cardLe_bound`).
-/

set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset Filter
open scoped ENNReal BigOperators

/-- **Superorthogonal Khintchine inequality, hypersystem form** (Tao, arXiv:2008.05066, Theorem `sys-ortho`(ii)). The same conclusion as the system form, for a family indexed by the subsets `A ⊆ S` with `|A| ≤ k`, whose Type II `2r`-superorthogonality hypothesis is the vanishing of `∫ ∏_{j<r}⟨f_{A_j}, f_{A_{r+j}}⟩` for every `2r`-tuple of admissible sets carrying a *nonce* (an element belonging to exactly one of the sets). The constant `C` is uniform in the index set `S` (it depends only on `k` and `r`), which is the essential content: the trivial Cauchy–Schwarz bound would only give a constant depending on `|C(S,≤k)|`. Proof (Tao §2): probabilistic decoupling — average over random partitions `S = S_1 ⊔ ⋯ ⊔ S_k` (a finite average over the `k^{|S|}` colourings `i : S → Fin k`) and iterate the system form `superorthogonal_khintchine` (import it from `Submission.Work.BourgainPlan.IonescuWainger.superorthogonal_khintchine`), applied to the Hilbert space `EuclideanSpace ℂ (Fin m)` of functions on `S_1 × ⋯ × S_{i-1}`; a nonce of the system tuple is a nonce of the corresponding `k`-sets, so the given hypothesis applies. -/
theorem superorthogonal_khintchine_hypersystem {X : Type*} [MeasurableSpace X]
    {α : Type*} [DecidableEq α] (k r : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : MeasureTheory.Measure X) (S : Finset α) (f : Finset α → X → ℂ),
      (∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ) →
      (∀ A : Fin r ⊕ Fin r → Finset α, (∀ i, A i ⊆ S ∧ (A i).card ≤ k) →
        MeasureTheory.Integrable (fun x => ∏ i : Fin r, ‖f (A (Sum.inl i)) x‖ * ‖f (A (Sum.inr i)) x‖) μ) →
      (∀ A : Fin r ⊕ Fin r → Finset α, (∀ i, A i ⊆ S ∧ (A i).card ≤ k) →
        Work.BourgainPlan.IonescuWainger.HasNonce A →
        ∫ x, (∏ i : Fin r, star (f (A (Sum.inl i)) x) * f (A (Sum.inr i)) x) ∂μ = 0) →
      ∫⁻ x, ‖∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), f A x‖ₑ ^ (2 * (r : ℝ)) ∂μ
        ≤ ENNReal.ofReal (C ^ (k * r)) *
          ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), ‖f A x‖ₑ ^ (2 : ℝ)) ^ r ∂μ := by
  set Css : ℝ := max 1 (Real.exp 1 * (r : ℝ) ^ (2 * r)) with hCss
  have hCsspos : 0 < Css := by rw [hCss]; exact lt_max_of_lt_left one_pos
  set G : ℝ := max 1 Css + ((k : ℝ) + 1) + ((k : ℝ) ^ k + 1) + 1 with hG
  have hG1 : (1 : ℝ) ≤ G := by
    rw [hG]
    have h1 : (1 : ℝ) ≤ max 1 Css := le_max_left _ _
    have h2 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
    linarith
  have hGCss : Css ≤ G := by
    rw [hG]
    have h1 : Css ≤ max 1 Css := le_max_right _ _
    have h2 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
    linarith
  have hGk1 : (k : ℝ) + 1 ≤ G := by
    rw [hG]
    have h1 : (1 : ℝ) ≤ max 1 Css := le_max_left _ _
    have h3 : (0 : ℝ) ≤ (k : ℝ) ^ k := by positivity
    linarith
  have hGkk : (k : ℝ) ^ k + 1 ≤ G := by
    rw [hG]
    have h1 : (1 : ℝ) ≤ max 1 Css := le_max_left _ _
    have h2 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    linarith
  refine ⟨G ^ 12, by positivity, ?_⟩
  intro μ S f hm hint horth
  have hsys : ∀ (i : ℕ) (hi : i ≤ k) (hi' : i + 1 ≤ k)
      (ν : Measure X) (g : S → X → EuclideanSpace ℂ (Fin i → S)),
      (∀ a, AEMeasurable (g a) ν) →
      (Integrable (fun x => (∑ a, ‖g a x‖ ^ 2) ^ r) ν) →
      (∀ s : Fin r ⊕ Fin r → S, HasNonceTuple s →
        ∫ x, (∏ m : Fin r, inner ℂ (g (s (Sum.inl m)) x) (g (s (Sum.inr m)) x)) ∂ν = 0) →
      ∫⁻ x, ‖∑ a, g a x‖ₑ ^ (2 * (r : ℝ)) ∂ν
        ≤ ENNReal.ofReal (Css ^ r) * ∫⁻ x, (∑ a, ‖g a x‖ₑ ^ (2 : ℝ)) ^ r ∂ν := by
    intro i hi hi' ν g
    rw [hCss]
    exact khintchine_hilbert_sq (X := X) r hr ν g
  have hfix : ∀ j, j ≤ k →
      MeasureTheory.lintegral μ (fun x => enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2 * (r : ℝ)))
        ≤ ENNReal.ofReal (G ^ (r * k + 2 * r)) *
          MeasureTheory.lintegral μ (fun x => (∑ A ∈ S.powerset.filter (fun A => A.card = j), enorm (f A x) ^ (2 : ℝ)) ^ r) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      have hone : S.powerset.filter (fun A => A.card = 0) = {∅} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.empty_subset S, by simp⟩
        · intro b hb
          simp only [Finset.mem_filter] at hb
          exact Finset.card_eq_zero.mp hb.2
      rw [hone]
      simp only [Finset.sum_singleton]
      have hpt : ∀ x : X, ‖f ∅ x‖ₑ ^ (2 * (r : ℝ)) = (‖f ∅ x‖ₑ ^ (2 : ℝ)) ^ r := by
        intro x
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      rw [show (fun x : X => ‖f ∅ x‖ₑ ^ (2 * (r : ℝ))) =
          (fun x : X => (‖f ∅ x‖ₑ ^ (2 : ℝ)) ^ r) from funext hpt]
      refine le_mul_of_one_le_left
        (b := MeasureTheory.lintegral μ (fun x : X => (‖f ∅ x‖ₑ ^ (2 : ℝ)) ^ r)) zero_le ?_
      exact ENNReal.one_le_ofReal.mpr (one_le_pow₀ hG1)
    · have hmj : ∀ A, A ⊆ S → A.card ≤ j → AEMeasurable (f A) μ :=
        fun A h1 h2 => hm A h1 (by omega)
      have hintj : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ i, A i ⊆ S ∧ (A i).card ≤ j) →
          Integrable (fun x => ∏ i : Fin r, ‖f (A (Sum.inl i)) x‖ * ‖f (A (Sum.inr i)) x‖) μ :=
        fun A hA => hint A (fun i => ⟨(hA i).1, by have := (hA i).2; omega⟩)
      have horthj : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ i, A i ⊆ S ∧ (A i).card ≤ j) →
          HasNonce A →
          ∫ x, (∏ i : Fin r, star (f (A (Sum.inl i)) x) * f (A (Sum.inr i)) x) ∂μ = 0 :=
        fun A hA => horth A (fun i => ⟨(hA i).1, by have := (hA i).2; omega⟩)
      have hdec : ∀ c : S → Fin j,
          MeasureTheory.lintegral μ (fun x => enorm (∑ σ ∈ transversalTuples S j c, f (tupleSet S σ) x) ^ (2 * (r : ℝ)))
            ≤ ENNReal.ofReal (Css ^ (r * j)) *
              MeasureTheory.lintegral μ (fun x => (∑ σ ∈ transversalTuples S j c, enorm (f (tupleSet S σ) x) ^ (2 : ℝ)) ^ r) :=
        fun c => decoupled_colouring S j r hr c f μ hmj hintj horthj hCsspos
          (fun i hi hi' ν g => hsys i (by omega) (by omega) ν g)
      have havg := averaged_bound S j r hr hpos f μ hCsspos hmj hdec
      refine havg.trans ?_
      have hconst : Css ^ (r * j) * ((j : ℝ) ^ j / (j.factorial : ℝ)) ^ (2 * r)
          ≤ G ^ (r * k + 2 * r) := by
        have h1 : Css ^ (r * j) ≤ G ^ (r * k) := by
          calc Css ^ (r * j) ≤ G ^ (r * j) := pow_le_pow_left₀ (le_of_lt hCsspos) hGCss _
            _ ≤ G ^ (r * k) := pow_le_pow_right₀ hG1 (Nat.mul_le_mul_left _ hj)
        have h2 : ((j : ℝ) ^ j / (j.factorial : ℝ)) ≤ G := by
          have hjk : j ^ j ≤ k ^ k :=
            (Nat.pow_le_pow_left (by omega : j ≤ k) j).trans
              (Nat.pow_le_pow_right (by omega : 0 < k) hj)
          have hcast : (j : ℝ) ^ j ≤ (k : ℝ) ^ k := by
            rw [← Nat.cast_pow, ← Nat.cast_pow]
            exact Nat.cast_le.mpr hjk
          refine (div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos j)).trans ?_
          linarith [hGkk]
        have h3 : ((j : ℝ) ^ j / (j.factorial : ℝ)) ^ (2 * r) ≤ G ^ (2 * r) :=
          pow_le_pow_left₀ (by positivity) h2 _
        calc Css ^ (r * j) * ((j : ℝ) ^ j / (j.factorial : ℝ)) ^ (2 * r)
            ≤ G ^ (r * k) * G ^ (2 * r) :=
              mul_le_mul h1 h3 (by positivity) (by positivity)
          _ = G ^ (r * k + 2 * r) := by rw [← pow_add]
      refine mul_le_mul_of_nonneg_right ?_ (zero_le)
      rw [ENNReal.ofReal_le_ofReal_iff (by positivity)]
      exact hconst
  have hcard := cardLe_bound S k r hr f μ (by positivity) (fun A h1 h2 => hm A h1 h2) hfix
  refine hcard.trans ?_
  gcongr
  have hexp : 2 * r + (r * k + 2 * r) ≤ 12 * (k * r) := by
    have h4 : k + 4 ≤ 12 * k := by omega
    calc 2 * r + (r * k + 2 * r) = r * (k + 4) := by ring
      _ ≤ r * (12 * k) := Nat.mul_le_mul_left _ h4
      _ = 12 * (k * r) := by ring
  calc ((k : ℝ) + 1) ^ (2 * r) * G ^ (r * k + 2 * r)
      ≤ G ^ (2 * r) * G ^ (r * k + 2 * r) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hGk1 _) (by positivity)
    _ = G ^ (2 * r + (r * k + 2 * r)) := by rw [← pow_add]
    _ ≤ G ^ (12 * (k * r)) := pow_le_pow_right₀ hG1 hexp
    _ = (G ^ 12) ^ (k * r) := by rw [pow_mul]

end Work.BourgainPlan.IonescuWainger
