import Mathlib
import Submission.Work.DSEQ0.SurjBasic

/-!
# `Work.DSEQ0.GrAcyclic_self`

The graded pieces `F m / F (m+1)` of the image-size filtration of the full complex
`D k = (Fin (k+1) → ι) → M` are acyclic above degree `m`, given the acyclicity of the
surjection complex `F m` for every type of cardinality `m`.

Concretely, `F m / F (m+1)` is the direct sum, over the `m`-element subsets `T ⊆ ι`, of the
surjection complex of `T`.  A representative `f ∈ F m` with `cob f ∈ F (m+1)` restricts to a
cocycle `f_T` on each `T`; the induction hypothesis produces a primitive `ψ_T`, and
`h := ∑_T (ψ_T extended by zero outside the tuples with image `T`)` is a primitive of `f`
modulo `F (m+1)`.
-/

open Classical Finset

namespace Work.DSEQ0

universe u

variable {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M]

/-- Coercing a tuple into a subtype does not change the cardinality of its image. -/
theorem imgCard_coe {T : Finset ι} {j : ℕ} (h : Fin (j + 1) → ↥T) :
    imgCard (fun i => (h i : ι)) = imgCard h := by
  rw [imgCard, imgCard, imgFinset, imgFinset]
  symm
  refine Finset.card_nbij (fun x : ↥T => (x : ι)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact ⟨i, rfl⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨i, rfl⟩ := hy
    refine ⟨h i, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨i, rfl⟩

/-- The image of a composite tuple is contained in the image of the outer tuple. -/
theorem imgFinset_comp_subset {k j : ℕ} (x : Fin (k + 1) → ι) (e : Fin (j + 1) → Fin (k + 1)) :
    imgFinset (x ∘ e) ⊆ imgFinset x := by
  intro y hy
  simp only [imgFinset, Finset.mem_image, Finset.mem_univ, true_and] at hy ⊢
  obtain ⟨i, rfl⟩ := hy
  exact ⟨e i, rfl⟩

theorem imgFinset_eq_of_imgCard {k : ℕ} {x : Fin (k + 1) → ι} {T : Finset ι}
    (hsub : imgFinset x ⊆ T) (hx : imgCard x = T.card) : imgFinset x = T :=
  Finset.eq_of_subset_of_card_le hsub (le_of_eq hx.symm)

theorem GrAcyclic_self {ι : Type u} [Fintype ι] {M : Type u} [AddCommGroup M] (m : ℕ) (hm : 1 ≤ m)
    (hIH : ∀ (X : Type u) [Fintype X], Fintype.card X = m → @FAcyclic X M _ m m) :
    @GrAcyclic ι M _ m m := by
  intro k hk f hf hc
  -- the restricted cocycles `f_T` are exact by the induction hypothesis
  have hψ : ∀ (T : Finset ι), T.card = m →
      ∃ ψ : (Fin (k + 1) → ↥T) → M, inF m ψ ∧ cob k ψ =
        (fun g : Fin (k + 2) → ↥T => f (fun i => (g i : ι))) := by
    intro T hT
    refine hIH ↥T ?_ k hk (fun g : Fin (k + 2) → ↥T => f (fun i => (g i : ι))) ?_ ?_
    · rw [Fintype.card_coe]; exact hT
    · intro g hg
      exact hf (fun i => (g i : ι)) ((imgCard_coe (j := k + 1) g).trans_lt hg)
    · funext x
      change (∑ j : Fin (k + 1 + 2),
        (-1 : ℤ) ^ (j : ℕ) • f (fun i => ((x ∘ Fin.succAbove j) i : ι))) = 0
      have hx' : imgCard (fun i => (x i : ι)) < m + 1 := by
        rw [imgCard_coe x]
        have h1 : imgCard x ≤ Fintype.card ↥T := imgCard_le x
        rw [Fintype.card_coe, hT] at h1
        omega
      have h0 := hc (fun i => (x i : ι)) hx'
      simp only [cob] at h0
      exact h0
  let ψ : (T : Finset ι) → T.card = m → (Fin (k + 1) → ↥T) → M :=
    fun T hT => Classical.choose (hψ T hT)
  have hψ_inf : ∀ (T : Finset ι) (hT : T.card = m), inF m (ψ T hT) :=
    fun T hT => (Classical.choose_spec (hψ T hT)).1
  have hψ_cob : ∀ (T : Finset ι) (hT : T.card = m), cob k (ψ T hT) =
      (fun g : Fin (k + 2) → ↥T => f (fun i => (g i : ι))) :=
    fun T hT => (Classical.choose_spec (hψ T hT)).2
  -- extension by zero of `ψ T` to the tuples missing `T`
  let L : (T : Finset ι) → T.card = m → (Fin (k + 1) → ι) → M := fun T hT g =>
    if h : imgFinset g = T then
      ψ T hT (fun i => ⟨g i, by
        rw [← h, imgFinset]; exact Finset.mem_image_of_mem g (Finset.mem_univ i)⟩)
    else 0
  let h : (Fin (k + 1) → ι) → M := fun g =>
    ∑ T : {T : Finset ι // T.card = m}, L T.1 T.2 g
  refine ⟨h, ?_, ?_⟩
  · -- support of `h`
    intro g hg
    dsimp only [h]
    apply Finset.sum_eq_zero
    intro T _
    dsimp only [L]
    exact dif_neg (fun hc2 => by
      have : imgCard g = m := by rw [imgCard, hc2]; exact T.2
      omega)
  · -- `cob k h - f` vanishes on tuples of image size `≤ m`
    intro x hxlt
    dsimp only
    rcases lt_or_eq_of_le (show imgCard x ≤ m by omega) with hxlt' | hxeq
    · have h0 : cob k h x = 0 := by
        dsimp only [cob]
        apply Finset.sum_eq_zero
        intro j _
        have hz : h (x ∘ Fin.succAbove j) = 0 := by
          dsimp only [h]
          apply Finset.sum_eq_zero
          intro T _
          dsimp only [L]
          exact dif_neg (fun hc2 => by
            have hle : imgCard (x ∘ Fin.succAbove j) ≤ imgCard x := imgCard_comp_le x (Fin.succAbove j)
            have : imgCard (x ∘ Fin.succAbove j) = m := by rw [imgCard, hc2]; exact T.2
            omega)
        rw [hz, smul_zero]
      have hfx : f x = 0 := hf x hxlt'
      rw [h0, hfx, sub_self]
    · -- the interesting case: `imgCard x = m`
      have hT0 : (imgFinset x).card = m := by rw [← hxeq]; rfl
      -- the term of the sum over `T` corresponding to `T = imgFinset x` is `f x`
      have hkey : cob k (L (imgFinset x) hT0) x = f x := by
        let xc : Fin (k + 2) → ↥(imgFinset x) :=
          fun i => ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩
        have hstep : ∀ j : Fin (k + 2),
            L (imgFinset x) hT0 (x ∘ Fin.succAbove j) = ψ (imgFinset x) hT0 (xc ∘ Fin.succAbove j) := by
          intro j
          dsimp only [L]
          by_cases hfij : imgFinset (x ∘ Fin.succAbove j) = imgFinset x
          · rw [dif_pos hfij]
            exact congrArg (ψ (imgFinset x) hT0) (by
              funext i
              exact Subtype.ext (by dsimp only [xc]; rfl))
          · rw [dif_neg hfij]
            symm
            apply hψ_inf (imgFinset x) hT0
            rw [← imgCard_coe (xc ∘ Fin.succAbove j)]
            change imgCard (x ∘ Fin.succAbove j) < m
            have hle : imgCard (x ∘ Fin.succAbove j) ≤ m := by
              calc imgCard (x ∘ Fin.succAbove j) ≤ imgCard x := imgCard_comp_le x (Fin.succAbove j)
                _ = m := hxeq
            have hne : imgCard (x ∘ Fin.succAbove j) ≠ m := by
              intro he
              exact hfij (imgFinset_eq_of_imgCard (imgFinset_comp_subset x (Fin.succAbove j))
                (by rw [he, ← hxeq]; rfl))
            omega
        have h2 : cob k (L (imgFinset x) hT0) x = cob k (ψ (imgFinset x) hT0) xc := by
          dsimp only [cob]
          apply Finset.sum_congr rfl
          intro j _
          rw [hstep j]
        rw [h2, hψ_cob (imgFinset x) hT0]
      -- all other terms vanish
      have hother : ∀ T : {T : Finset ι // T.card = m}, T ≠ ⟨imgFinset x, hT0⟩ →
          cob k (L T.1 T.2) x = 0 := by
        intro T hTne
        dsimp only [cob]
        apply Finset.sum_eq_zero
        intro j _
        have hz : L T.1 T.2 (x ∘ Fin.succAbove j) = 0 := by
          dsimp only [L]
          exact dif_neg (fun hc2 => by
            have hEq : imgFinset (x ∘ Fin.succAbove j) = imgFinset x :=
              imgFinset_eq_of_imgCard (imgFinset_comp_subset x (Fin.succAbove j))
                (by rw [imgCard, hc2, T.2, ← hxeq]; rfl)
            exact hTne (Subtype.ext (hc2.symm.trans hEq)))
        rw [hz, smul_zero]
      have hsplit : cob k h x =
          ∑ T : {T : Finset ι // T.card = m}, cob k (L T.1 T.2) x := by
        have e1 : cob k h x = ∑ j : Fin (k + 2),
            ∑ T : {T : Finset ι // T.card = m},
              (-1 : ℤ) ^ (j : ℕ) • L T.1 T.2 (x ∘ Fin.succAbove j) := by
          dsimp only [cob, h]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.smul_sum]
        rw [e1, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro T _
        rw [cob]
      rw [hsplit,
        Finset.sum_eq_single ⟨imgFinset x, hT0⟩ (fun T _ hne => hother T hne)
          (fun hc2 => absurd (Finset.mem_univ _) hc2)]
      rw [hkey, sub_self]

end Work.DSEQ0
