import Mathlib
import Submission.Work.Peluse.SwapC.pbox_le_one

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## Auxiliary lemmas

`pboxSum` sees its normalisation set `S` only through the factor `|S|⁻¹` (the `x`-sum is over all
of `ℤ`), so `pbox` is unchanged when `S` is replaced by a set of the same cardinality; and the
translate `symIcc N + x₀` has the cardinality of `symIcc N`. -/

/-- `pbox` depends on the normalisation set `S` only through its cardinality. -/
lemma pbox_card_congr (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) {S T : Finset ℤ}
    (h : S.card = T.card) (f : ℤ → ℂ) :
    pbox d q₁ q₂ M S f = pbox d q₁ q₂ M T f := by
  simp [pbox, pboxSum, h]

/-- Membership in the translate `symIcc N + x₀`. -/
lemma mem_symIcc_translate (N : ℕ) (x₀ x : ℤ) :
    x ∈ (symIcc N).image (fun t => t + x₀) ↔ x - x₀ ∈ symIcc N := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · intro hx
    exact ⟨x - x₀, hx, by ring⟩

/-- The translate `symIcc N + x₀` has the cardinality of `symIcc N`. -/
lemma card_symIcc_translate (N : ℕ) (x₀ : ℤ) :
    ((symIcc N).image (fun t : ℤ => t + x₀)).card = (symIcc N).card :=
  Finset.card_image_of_injective _ (add_left_injective x₀)

/-- **The `pbox ≤ 1` bound with translated support.**  `concatStep`'s hypothesis supports `f` in
a *translate* `x₀ + symIcc N` while `pbox` normalises by `symIcc N`; the two cardinalities agree, so
the bound of `pbox_le_one` still holds.  (The prover should also record the `avg` corollary
`avg (fun i : I => pbox d (q₁ i) (q₂ i) M (symIcc N) f) ≤ 1` in the same file, since it is what
gives `δ ≤ 1` from the hypothesis of `concatStep`.) -/
theorem pbox_le_one_translate (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M N : ℕ) (x₀ : ℤ) (f : ℤ → ℂ)
    (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    Work.Peluse.LadderP.Swap.pbox d q₁ q₂ M (Work.Peluse.symIcc N) f ≤ 1 := by
  have hcard : ((symIcc N).image (fun t : ℤ => t + x₀)).card = (symIcc N).card :=
    card_symIcc_translate N x₀
  have hsupS : ∀ x : ℤ, x ∉ (symIcc N).image (fun t : ℤ => t + x₀) → f x = 0 := by
    intro x hx
    refine hsup x (lt_of_not_ge fun hle => hx ?_)
    rw [mem_symIcc_translate]
    rw [Work.Peluse.symIcc, Finset.mem_Icc]
    exact abs_le.mp hle
  have h1 : pbox d q₁ q₂ M ((symIcc N).image (fun t : ℤ => t + x₀)) f ≤ 1 :=
    pbox_le_one d q₁ q₂ M ((symIcc N).image (fun t : ℤ => t + x₀)) f hsupS hbd
  rw [pbox_card_congr d q₁ q₂ M hcard f] at h1
  exact h1

/-- The `avg` corollary of `pbox_le_one_translate`: averaging the bound over any nonempty family of
slot pairs keeps it `≤ 1` (this is the form in which it gives `δ ≤ 1` from `concatStep`'s
hypothesis, since `δ ≤ avg … ≤ 1`). -/
theorem avg_pbox_le_one_translate {I : Type} [Fintype I] [Nonempty I]
    (d : ℕ) (q₁ q₂ : I → Fin d → ℤ) (M N : ℕ) (x₀ : ℤ) (f : ℤ → ℂ)
    (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) (hbd : ∀ x : ℤ, ‖f x‖ ≤ 1) :
    avg (fun i : I => pbox d (q₁ i) (q₂ i) M (symIcc N) f) ≤ 1 :=
  avg_le_of_forall_le fun i => pbox_le_one_translate d (q₁ i) (q₂ i) M N x₀ f hsup hbd

end

end Work.Peluse.SwapC
