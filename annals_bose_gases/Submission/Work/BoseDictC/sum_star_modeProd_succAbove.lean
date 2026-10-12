import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseDictC.sum_star_modeProd_succAbove`

The mode-wise creation identity for the symmetric mode products of `Work.BoseDict`:

`Σ_j e_l(x_j) · modeProd e d β (x ∖ j) = (β_l + 1) · modeProd e (d+1) (β + e_l) x`,

i.e. the box creation `boxCre e l d` (see `Work.BoseDict.boxCreOf`) raises the occupation
number of the mode `l` by one, with the combinatorial factor `β_l + 1` counting the
placements of the new particle.

## Proof

Every labelling `σ : Fin d → Fin m` together with a slot `j : Fin (d+1)` determines the
labelling `insNth j l σ` of `Fin (d+1)`, and conversely.  Hence the double sum over `(j, σ)`
is the sum over `τ : Fin (d+1) → Fin m` of the weight
`[modeMult τ = β + e_l] · ∏_k e_{τ_k}(x_k)`, counted with multiplicity the number
`#{j | τ_j = l}` of slots carrying the label `l` — which is `(β + e_l)_l = β_l + 1` on the
support of the weight, and irrelevant off it.  The factor `β_l + 1` is exactly the
multiplicity of the labelling `τ` in this fibre decomposition.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseDictC

/-- The labelling obtained by inserting the label `a` in the slot `j`
(`insNth j a σ = Fin.insertNth j a σ`, written with an explicit type so that it can be
used in term position without type inference problems). -/
def insNth {n : ℕ} {α : Type*} (j : Fin (n + 1)) (a : α) (σ : Fin n → α) :
    Fin (n + 1) → α :=
  Fin.insertNth j a σ

/-! ## 1. Counting lemmas for the occupation multi-index -/

/-- The `k`-component of the occupation multi-index of a labelling is the number of
coordinates carrying the label `k`. -/
lemma modeMult_apply {m n : ℕ} (σ : Fin n → Fin m) (k : Fin m) :
    Work.BoseDict.modeMult σ k = (Finset.univ.filter fun i => σ i = k).card := by
  rw [Work.BoseDict.modeMult, Finsupp.finsetSum_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    exact Finsupp.single_eq_of_ne (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Adding `single l 1` on the right is injective for `Fin m →₀ ℕ`. -/
lemma add_single_one_right_inj {m : ℕ} {a b : Fin m →₀ ℕ} {l : Fin m} :
    a + Finsupp.single l 1 = b + Finsupp.single l 1 ↔ a = b := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun f : Fin m →₀ ℕ => f i) h
    rw [Finsupp.add_apply, Finsupp.add_apply] at hi
    exact Nat.add_right_cancel hi
  · intro h
    rw [h]

/-- Inserting the label `l` into the slot `j` of a labelling increases the occupation
number of `l` by one and leaves every other occupation number unchanged. -/
lemma modeMult_insertNth {m d : ℕ} (l : Fin m) (j : Fin (d + 1)) (σ : Fin d → Fin m) :
    Work.BoseDict.modeMult (insNth j l σ)
      = Work.BoseDict.modeMult σ + Finsupp.single l 1 := by
  ext k
  rw [Finsupp.add_apply, modeMult_apply (insNth j l σ) k, modeMult_apply σ k,
    Finsupp.single_apply]
  rw [Finset.card_filter, Finset.card_filter]
  change (∑ i : Fin (d + 1), (fun i : Fin (d + 1) =>
        if insNth j l σ i = k then (1 : ℕ) else 0) i)
      = (∑ i : Fin d, (fun i : Fin d => if σ i = k then (1 : ℕ) else 0) i)
        + (if l = k then (1 : ℕ) else 0)
  rw [Fin.sum_univ_succAbove (fun i : Fin (d + 1) =>
    if insNth j l σ i = k then (1 : ℕ) else 0) j]
  simp only [insNth, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  exact Nat.add_comm _ _

/-- The product of a labelling with an inserted slot splits off the inserted factor. -/
lemma prod_insertNth {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (l : Fin m)
    (j : Fin (d + 1)) (σ : Fin d → Fin m) (x : Work.BoseDict.Xn (d + 1)) :
    (∏ k : Fin (d + 1), e (insNth j l σ k) (x k))
      = e l (x j) * ∏ i : Fin d, e (σ i) (x (Fin.succAbove j i)) := by
  rw [Fin.prod_univ_succAbove (fun k : Fin (d + 1) => e (insNth j l σ k) (x k)) j]
  simp only [insNth, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-! ## 2. Reindexing a sum of labellings by an inserted slot -/

/-- Reindexing a sum over the labellings of `Fin n` by insertion of the label `a` in the
slot `j` (the fibre form, over the filter of those `τ` with `τ j = a`). -/
lemma sum_insertNth_fibre {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*}
    [AddCommMonoid M] (j : Fin (n + 1)) (a : α) (F : (Fin (n + 1) → α) → M) :
    (∑ σ : Fin n → α, F (insNth j a σ))
      = ∑ τ ∈ Finset.univ.filter (fun τ : Fin (n + 1) → α => τ j = a), F τ := by
  refine Finset.sum_nbij' (fun σ : Fin n → α => insNth j a σ)
    (fun τ : Fin (n + 1) → α => fun i : Fin n => τ (j.succAbove i)) ?_ ?_ ?_ ?_ ?_
  · intro σ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, insNth, Fin.insertNth_apply_same]
  · intro τ _
    exact Finset.mem_univ _
  · intro σ _
    funext i
    simp only [insNth, Fin.insertNth_apply_succAbove]
  · intro τ hτ
    have h : τ j = a := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hτ
    rw [insNth]
    exact (Fin.insertNth_eq_iff (α := fun _ : Fin (n + 1) => α)).mpr ⟨h.symm, rfl⟩
  · intro σ _
    rfl

/-- Reindexing a sum over the labellings of `Fin n` by insertion of the label `a` in the
slot `j` (the indicator form: the sum over all `τ` of `F τ` weighted by `[τ j = a]`). -/
lemma sum_insertNth_fibre_ite {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*}
    [AddCommMonoid M] (j : Fin (n + 1)) (a : α) (F : (Fin (n + 1) → α) → M) :
    (∑ σ : Fin n → α, F (insNth j a σ))
      = ∑ τ : Fin (n + 1) → α, if τ j = a then F τ else 0 := by
  rw [sum_insertNth_fibre j a F, ← Finset.sum_filter]

/-! ## 3. The creation identity -/

theorem sum_star_modeProd_succAbove {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (l : Fin m)
    (β : Fin m →₀ ℕ) (x : Work.BoseDict.Xn (d + 1)) :
    (∑ j : Fin (d + 1), e l (x j)
        * Work.BoseDict.modeProd e d β (fun i : Fin d => x (Fin.succAbove j i)))
      = (((β l : ℝ) + 1 : ℂ)) * Work.BoseDict.modeProd e (d + 1) (β + Work.BoseB4.e m l) x := by
  classical
  have hsingle : Work.BoseB4.e m l = Finsupp.single l 1 := rfl
  rw [hsingle]
  -- the weight of a labelling `τ` on `Fin (d+1)`
  set W : (Fin (d + 1) → Fin m) → ℂ := fun τ =>
    (if Work.BoseDict.modeMult τ = β + Finsupp.single l 1 then (1 : ℂ) else 0)
      * ∏ k : Fin (d + 1), e (τ k) (x k) with hW
  -- **(1)** the summand attached to `(j, σ)` is the weight of the inserted labelling `τ`
  have hpt : ∀ (j : Fin (d + 1)) (σ : Fin d → Fin m),
      (if Work.BoseDict.modeMult σ = β then (1 : ℂ) else 0)
          * (e l (x j) * ∏ i : Fin d, e (σ i) (x (Fin.succAbove j i)))
        = W (insNth j l σ) := by
    intro j σ
    rw [hW]
    change (if Work.BoseDict.modeMult σ = β then (1 : ℂ) else 0)
          * (e l (x j) * ∏ i : Fin d, e (σ i) (x (Fin.succAbove j i)))
        = (if Work.BoseDict.modeMult (insNth j l σ) = β + Finsupp.single l 1
              then (1 : ℂ) else 0)
          * ∏ k : Fin (d + 1), e (insNth j l σ k) (x k)
    rw [modeMult_insertNth l j σ, prod_insertNth l j σ x]
    by_cases h : Work.BoseDict.modeMult σ = β
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hh => h (add_single_one_right_inj.mp hh))]
  -- **(2)** reindex each inner sum by the inserted labelling
  have hL2 : (∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, W (insNth j l σ))
      = ∑ j : Fin (d + 1), ∑ τ : Fin (d + 1) → Fin m, (if τ j = l then W τ else 0) :=
    Finset.sum_congr rfl fun j _ => sum_insertNth_fibre_ite j l W
  -- **(3)** the number of slots carrying the label `l` is the `l`-occupation number
  have hL4 : ∀ τ : Fin (d + 1) → Fin m,
      (∑ j : Fin (d + 1), (if τ j = l then W τ else 0))
        = ((Finset.univ.filter (fun j => τ j = l)).card : ℂ) * W τ := by
    intro τ
    have h1 : (∑ j : Fin (d + 1), (if τ j = l then W τ else 0))
        = (∑ j : Fin (d + 1), (if τ j = l then (1 : ℂ) else 0)) * W τ := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : τ j = l <;> simp [h]
    rw [h1, Finset.sum_boole]
  -- **(4)** on the support of the weight that number is `β_l + 1`, off it the weight vanishes
  have hscal : ∀ τ : Fin (d + 1) → Fin m,
      ((Finset.univ.filter (fun j => τ j = l)).card : ℂ) * W τ
        = (((β l : ℝ) + 1 : ℂ)) * W τ := by
    intro τ
    have hcard : ((Finset.univ.filter (fun j => τ j = l)).card : ℂ)
        = ((Work.BoseDict.modeMult τ l : ℕ) : ℂ) := by
      rw [modeMult_apply τ l]
    have hc : (((β l : ℝ) + 1 : ℂ)) = ((β l + 1 : ℕ) : ℂ) := by
      push_cast
      ring
    rw [hcard]
    by_cases h : Work.BoseDict.modeMult τ = β + Finsupp.single l 1
    · have hl : Work.BoseDict.modeMult τ l = β l + 1 := by
        rw [h, Finsupp.add_apply, Finsupp.single_eq_same]
      rw [hl, hc]
    · have hWτ : W τ = 0 := by
        rw [hW]
        change (if Work.BoseDict.modeMult τ = β + Finsupp.single l 1 then (1 : ℂ) else 0)
            * ∏ k : Fin (d + 1), e (τ k) (x k) = 0
        rw [if_neg h, zero_mul]
      rw [hWτ, mul_zero, mul_zero]
  -- **(5)** the weighted sum of the labellings is the mode product
  have hWsum : (∑ τ : Fin (d + 1) → Fin m, W τ)
      = Work.BoseDict.modeProd e (d + 1) (β + Finsupp.single l 1) x := by
    simp only [hW, Work.BoseDict.modeProd]
  have hmain : (∑ j : Fin (d + 1), e l (x j)
        * Work.BoseDict.modeProd e d β (fun i : Fin d => x (Fin.succAbove j i)))
      = (((β l : ℝ) + 1 : ℂ))
        * Work.BoseDict.modeProd e (d + 1) (β + Finsupp.single l 1) x := by
    calc (∑ j : Fin (d + 1), e l (x j)
          * Work.BoseDict.modeProd e d β (fun i : Fin d => x (Fin.succAbove j i)))
        = ∑ j : Fin (d + 1), ∑ σ : Fin d → Fin m, W (insNth j l σ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Work.BoseDict.modeProd, Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [← hpt j σ]
          ring
      _ = ∑ j : Fin (d + 1), ∑ τ : Fin (d + 1) → Fin m, (if τ j = l then W τ else 0) :=
          hL2
      _ = ∑ τ : Fin (d + 1) → Fin m, ∑ j : Fin (d + 1), (if τ j = l then W τ else 0) :=
          Finset.sum_comm
      _ = ∑ τ : Fin (d + 1) → Fin m,
            ((Finset.univ.filter (fun j => τ j = l)).card : ℂ) * W τ :=
          Finset.sum_congr rfl fun τ _ => hL4 τ
      _ = ∑ τ : Fin (d + 1) → Fin m, (((β l : ℝ) + 1 : ℂ)) * W τ :=
          Finset.sum_congr rfl fun τ _ => hscal τ
      _ = (((β l : ℝ) + 1 : ℂ)) * ∑ τ : Fin (d + 1) → Fin m, W τ := by
          rw [Finset.mul_sum]
      _ = (((β l : ℝ) + 1 : ℂ))
            * Work.BoseDict.modeProd e (d + 1) (β + Finsupp.single l 1) x := by
          rw [hWsum]
  exact hmain

end Work.BoseDictC
