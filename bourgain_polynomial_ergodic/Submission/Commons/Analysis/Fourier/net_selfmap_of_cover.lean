import Mathlib

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped ENNReal

/-- Elementary ℓ²-triangle bound: if `x` and `y` both have squared `ℓ²`-norm at most `c`, then
so does `x + y` up to a factor `4`. -/
private lemma sum_normSq_add_le (K : ℕ) (x y : Fin K → ℂ) {c : ℝ}
    (hx : (∑ k, ‖x k‖^2) ≤ c) (hy : (∑ k, ‖y k‖^2) ≤ c) :
    (∑ k, ‖x k + y k‖^2) ≤ 4 * c := by
  have hterm : ∀ k : Fin K, ‖x k + y k‖^2 ≤ 2 * (‖x k‖^2 + ‖y k‖^2) := by
    intro k
    have h1 : ‖x k + y k‖ ≤ ‖x k‖ + ‖y k‖ := norm_add_le _ _
    have h4 : (0:ℝ) ≤ ‖x k + y k‖ := norm_nonneg _
    have hsq : ‖x k + y k‖ * ‖x k + y k‖
        ≤ (‖x k‖ + ‖y k‖) * (‖x k‖ + ‖y k‖) :=
      mul_self_le_mul_self h4 h1
    nlinarith [hsq, sq_nonneg (‖x k‖ - ‖y k‖)]
  calc ∑ k, ‖x k + y k‖^2
      ≤ ∑ k, 2 * (‖x k‖^2 + ‖y k‖^2) := Finset.sum_le_sum (fun k _ => hterm k)
    _ = 2 * ((∑ k, ‖x k‖^2) + (∑ k, ‖y k‖^2)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * (c + c) := by linarith
    _ = 4 * c := by ring

/-- **Curve-point nets from an arbitrary cover.**  Let `a : Fin N → (Fin K → ℂ)` be a finite family
and let `S : Finset (Fin K → ℂ)` cover the range of `a` by `ℓ²`-balls of radius `r/2`.  Then there
is a self-map `σ : Fin N → Fin N` whose range has at most `S.card` elements and which is a *net map
of radius `r`*: `∑ k, ‖a i k - a (σ i) k‖ ^ 2 ≤ r ^ 2` for every `i`. -/
theorem net_selfmap_of_cover {N K : ℕ} (a : Fin N → Fin K → ℂ) (S : Finset (Fin K → ℂ)) {r : ℝ}
    (hcover : ∀ i : Fin N, ∃ s ∈ S, ∑ k : Fin K, ‖a i k - s k‖ ^ 2 ≤ (r / 2) ^ 2) :
    ∃ σ : Fin N → Fin N, (Finset.univ.image σ).card ≤ S.card ∧
      ∀ i : Fin N, ∑ k : Fin K, ‖a i k - a (σ i) k‖ ^ 2 ≤ r ^ 2 := by
  by_cases hN : N = 0
  · subst hN
    refine ⟨fun i => i.elim0, by simp, ?_⟩
    intro i; exact i.elim0
  · -- Choice of a covering element `s i ∈ S` for every point `a i`.
    let s : Fin N → Fin K → ℂ := fun i => Classical.choose (hcover i)
    have hs_mem : ∀ i, s i ∈ S := fun i => (Classical.choose_spec (hcover i)).1
    have hs_le : ∀ i, ∑ k, ‖a i k - s i k‖^2 ≤ (r/2)^2 :=
      fun i => (Classical.choose_spec (hcover i)).2
    -- A default index, and the representative map: `rep x` is an index `j` with `s j = x`
    -- whenever such an index exists.
    let d : Fin N := ⟨0, Nat.pos_of_ne_zero hN⟩
    let rep : (Fin K → ℂ) → Fin N :=
      fun x => if h : ∃ i, s i = x then Classical.choose h else d
    have hrep : ∀ x (h : ∃ i, s i = x), s (rep x) = x := by
      intro x h
      have hchoose : rep x = Classical.choose h := by
        simp only [rep]
        exact dif_pos h
      rw [hchoose]
      exact Classical.choose_spec h
    let σ : Fin N → Fin N := fun i => rep (s i)
    have hσs : ∀ i, s (σ i) = s i := by
      intro i
      show s (rep (s i)) = s i
      exact hrep (s i) ⟨i, rfl⟩
    refine ⟨σ, ?_, ?_⟩
    · -- The range of `σ` is contained in the image of `S` under `rep`.
      calc (Finset.univ.image σ).card
          = (Finset.univ.image (fun i => rep (s i))).card := rfl
        _ ≤ (S.image rep).card := by
            apply Finset.card_le_card
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
            exact Finset.mem_image.mpr ⟨s i, hs_mem i, rfl⟩
        _ ≤ S.card := Finset.card_image_le
    · intro i
      have h1 : ∑ k, ‖a i k - s i k‖^2 ≤ (r/2)^2 := hs_le i
      have h2 : ∑ k, ‖a (σ i) k - s i k‖^2 ≤ (r/2)^2 := by
        have := hs_le (σ i)
        rwa [hσs i] at this
      have hy : ∑ k, ‖s i k - a (σ i) k‖^2 ≤ (r/2)^2 := by
        simpa only [norm_sub_rev] using h2
      have h3 : ∑ k, ‖(a i k - s i k) + (s i k - a (σ i) k)‖^2 ≤ 4 * (r/2)^2 :=
        sum_normSq_add_le K (fun k => a i k - s i k) (fun k => s i k - a (σ i) k) h1 hy
      have h3' : (∑ k, ‖(a i k - s i k) + (s i k - a (σ i) k)‖^2)
          = ∑ k, ‖a i k - a (σ i) k‖^2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [show (a i k - s i k) + (s i k - a (σ i) k) = a i k - a (σ i) k from by ring]
      calc ∑ k, ‖a i k - a (σ i) k‖^2
          = ∑ k, ‖(a i k - s i k) + (s i k - a (σ i) k)‖^2 := h3'.symm
        _ ≤ 4 * (r/2)^2 := h3
        _ = r^2 := by ring

end Commons.Analysis.Fourier
