import Mathlib
import Submission.Work.PTCert.RedWDefs

namespace Work.PTCert

open Submission.PTCert

set_option autoImplicit false

/-!
# Decoding the PTCert word model is reduced and injective

`decP r hr` decodes a word-model letter `c < 2r` as the Mathlib free-group letter
`(⟨c / 2, _⟩, c % 2 == 0)`.  We show that it preserves reducedness (`RedP` ↦
`FreeGroup.IsReduced`) and is injective on letters `< 2r`.
-/

/-- Division by two strictly decreases the bound `2 * r` to `r`. -/
lemma div2lt {r c : ℕ} (hc : c < 2 * r) : c / 2 < r := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)]
  omega

/-- For a letter `c < 2r` the decoder is in its "in range" branch. -/
lemma decP_eq {r : ℕ} (hr : 0 < r) {c : ℕ} (hc : c < 2 * r) :
    decP r hr c = (⟨c / 2, div2lt hc⟩, c % 2 == 0) := by
  rw [decP, dif_pos (div2lt hc)]

/-- Parity is determined by the quotient by two together with the reducedness relation:
if `a` and `b` have the same integer part `a/2 = b/2` and `b` is not the bit-flip of `a`,
then `a` and `b` have the same parity. -/
lemma xor_key {a b : ℕ} (h : a / 2 = b / 2) (hb : b ≠ a ^^^ 1) : a % 2 = b % 2 := by
  rcases Nat.even_or_odd a with ha | ha
  · rw [Nat.xor_one_of_even ha] at hb
    have : a % 2 = 0 := Nat.even_iff.mp ha
    have hb' : b % 2 ≠ 1 := by intro hc; apply hb; omega
    omega
  · rw [Nat.xor_one_of_odd ha] at hb
    have : a % 2 = 1 := Nat.odd_iff.mp ha
    have hb' : b % 2 ≠ 0 := by intro hc; apply hb; omega
    omega

/-- `decP r hr` is injective on the letters `< 2r`. -/
lemma decP_inj {r : ℕ} (hr : 0 < r) {a b : ℕ} (ha : a < 2 * r) (hb : b < 2 * r)
    (h : decP r hr a = decP r hr b) : a = b := by
  rw [decP_eq hr ha, decP_eq hr hb] at h
  have h1 : a / 2 = b / 2 := by
    have := congrArg (fun x : Fin r × Bool => (x.1 : ℕ)) h
    simpa using this
  have h2 : (a % 2 == 0) = (b % 2 == 0) := by
    have := congrArg (fun x : Fin r × Bool => x.2) h
    simpa using this
  have h3 : a % 2 = b % 2 := by
    rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with h0 | h0 <;>
      rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with h1' | h1' <;> simp_all
  omega

/-- If `f` is injective on the elements of `l₁` against the elements of `l₂`, then `l₁` is
recovered from `l₁.map f`. -/
lemma map_eq_of_inj_on {α β : Type*} {f : α → β} {l₁ l₂ : List α}
    (H : ∀ a ∈ l₁, ∀ b ∈ l₂, f a = f b → a = b)
    (hm : l₁.map f = l₂.map f) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => cases l₂ <;> simp_all
  | cons a t ih =>
    cases l₂ with
    | nil => simp at hm
    | cons b t' =>
      simp only [List.map_cons, List.cons.injEq] at hm
      obtain ⟨hf, hm'⟩ := hm
      have hab : a = b := H a (by simp) b (by simp) hf
      rw [hab]
      exact congrArg (List.cons b) (ih (fun x hx y hy => H x (by simp [hx]) y (by simp [hy])) hm')

theorem decPMap : ∀ (r : ℕ) (hr : 0 < r),
    (∀ {l : List ℕ}, (∀ c ∈ l, c < 2 * r) → RedP l →
      FreeGroup.IsReduced (l.map (decP r hr))) ∧
    (∀ {l₁ l₂ : List ℕ}, (∀ c ∈ l₁, c < 2 * r) → (∀ c ∈ l₂, c < 2 * r) →
      l₁.map (decP r hr) = l₂.map (decP r hr) → l₁ = l₂) := by
  intro r hr
  refine ⟨?_, ?_⟩
  · intro l hbound hred
    have hS : List.IsChain (fun a b : ℕ => (decP r hr a).1 = (decP r hr b).1 →
        (decP r hr a).2 = (decP r hr b).2) l := by
      apply List.IsChain.imp_of_mem_imp _ hred
      intro a b ha hb hR hfst
      rw [decP_eq hr (hbound a ha), decP_eq hr (hbound b hb)] at hfst ⊢
      have hq : a / 2 = b / 2 := by
        have := congrArg (fun x : Fin r => (x : ℕ)) hfst
        simpa using this
      rw [xor_key hq hR]
    exact List.isChain_map_of_isChain (decP r hr) (fun _ _ h => h) hS
  · intro l₁ l₂ hb₁ hb₂ hm
    exact map_eq_of_inj_on (fun a ha b hb h => decP_inj hr (hb₁ a ha) (hb₂ b hb) h) hm

end Work.PTCert
