import ChallengeDeps
import Submission.Vinogradov.Core

open LeanEval.NumberTheory.VinogradovMeanValue
open scoped BigOperators

set_option autoImplicit false

namespace Submission.Vinogradov

noncomputable section
open Classical

/-- A tuple of length `m+1` of naturals is determined by its first `m` entries and its sum. -/
lemma eq_of_prefix_eq_of_eq_sum {m : ℕ} {a b : Fin (m+1) → ℕ}
    (hpre : ∀ i : Fin m, a (i.castSucc) = b (i.castSucc))
    (hsum : (∑ j : Fin (m+1), a j) = (∑ j : Fin (m+1), b j)) : a = b := by
  apply funext
  intro i
  by_cases hi : i.val = m
  · have hlast_eq : i = Fin.last m := by
      ext; simp [hi]
    rw [hlast_eq]
    have h1 := Fin.sum_univ_castSucc a
    have h2 := Fin.sum_univ_castSucc b
    have hpre_sum : (∑ j : Fin m, a (j.castSucc)) = (∑ j : Fin m, b (j.castSucc)) := by
      exact Finset.sum_congr rfl (fun j _ => hpre j)
    rw [h1, h2] at hsum
    nlinarith
  · have hv : i.val < m := by omega
    have hcast : i = (⟨i.val, hv⟩ : Fin m).castSucc := by
      ext; simp [Fin.castSucc_mk]
    rw [hcast]
    exact hpre ⟨i.val, hv⟩

/-- Given one more variable than equations, dropping the last `y`-entry is
injective on pairs with equal first moments (`k = 1`). -/
lemma inj_dropLast_eqSum (m X : ℕ) :
    Set.InjOn (fun xy : PairSpace (m+1) X => (xy.1, fun i : Fin m => xy.2 (i.castSucc)))
      ↑(Finset.univ.filter (fun xy : PairSpace (m+1) X =>
        (∑ i, (xy.1 i).1) = (∑ i, (xy.2 i).1))) := by
  let f : PairSpace (m+1) X → (Fin (m+1) → Finset.Icc 1 X) × (Fin m → Finset.Icc 1 X) :=
    fun xy => (xy.1, fun i : Fin m => xy.2 (i.castSucc))
  change Set.InjOn f ↑(Finset.univ.filter (fun xy : PairSpace (m+1) X =>
        (∑ i, (xy.1 i).1) = (∑ i, (xy.2 i).1)))
  intro a ha b hb h
  apply Prod.ext
  · -- first components equal
    have h1' : (f a).1 = (f b).1 := congrArg Prod.fst h
    simpa [f] using h1'
  · -- second components equal
    have hpre : ∀ i : Fin m, (a.2 (i.castSucc)).1 = (b.2 (i.castSucc)).1 := by
      intro i
      have := congrArg (fun z : (Fin (m+1) → Finset.Icc 1 X) × (Fin m → Finset.Icc 1 X) => (z.2 i).1) h
      simpa [f] using this
    have hsumY : (∑ j : Fin (m+1), (a.2 j).1) = (∑ j : Fin (m+1), (b.2 j).1) := by
      have hfa : (∑ j : Fin (m+1), (a.1 j).1) = (∑ j : Fin (m+1), (a.2 j).1) := by simpa using ha
      have hfb : (∑ j : Fin (m+1), (b.1 j).1) = (∑ j : Fin (m+1), (b.2 j).1) := by simpa using hb
      have hfst_eq : (∑ j : Fin (m+1), (a.1 j).1) = (∑ j : Fin (m+1), (b.1 j).1) := by
        have hf1 : a.1 = b.1 := by
          have h1' : (f a).1 = (f b).1 := congrArg Prod.fst h
          simpa [f] using h1'
        rw [hf1]
      linarith
    have hval : (fun j : Fin (m+1) => (a.2 j).1) = (fun j : Fin (m+1) => (b.2 j).1) := by
      exact eq_of_prefix_eq_of_eq_sum hpre hsumY
    apply funext
    intro j
    apply Subtype.ext
    exact congrFun hval j

/-- For `k = 1` the number of solutions with `m + 1` variables is at most
`X^(2m+1)`: the linear equation leaves one variable determined. -/
lemma J_le_pow_k1 (m X : ℕ) : J (m + 1) 1 X ≤ (X ^ (2 * m + 1) : ℕ) := by
  rw [J_eq_filter_card]
  -- relate Matches (m+1) 1 to plain sum equality
  have hfilter :
      (Finset.univ.filter (Matches (m + 1) 1 X)) =
        (Finset.univ.filter (fun xy : PairSpace (m + 1) X =>
          (∑ i, (xy.1 i).1) = (∑ i, (xy.2 i).1))) := by
    ext xy
    simp [Matches]
    constructor
    · intro h
      simpa using (h 1 (by omega))
    · intro hsum j hj
      have hj01 : j = 0 ∨ j = 1 := by omega
      rcases hj01 with rfl | rfl
      · simp
      · simpa using hsum
  rw [hfilter]
  -- bound by the image cardinality
  let A := (Finset.univ.filter (fun xy : PairSpace (m+1) X =>
        (∑ i, (xy.1 i).1) = (∑ i, (xy.2 i).1)))
  let f := fun xy : PairSpace (m+1) X => (xy.1, fun i : Fin m => xy.2 (i.castSucc))
  have hcard_img : (A.image f).card = A.card := Finset.card_image_of_injOn (inj_dropLast_eqSum m X)
  have hsub : A.image f ⊆ (Finset.univ : Finset ((Fin (m+1) → Finset.Icc 1 X) × (Fin m → Finset.Icc 1 X))) := by
    intro z hz
    simp
  have hle : A.card ≤ (Finset.univ : Finset ((Fin (m+1) → Finset.Icc 1 X) × (Fin m → Finset.Icc 1 X))).card := by
    rw [← hcard_img]
    exact Finset.card_le_card hsub
  have hcard : (Finset.univ : Finset ((Fin (m+1) → Finset.Icc 1 X) × (Fin m → Finset.Icc 1 X))).card
      = X ^ (2 * m + 1) := by
    rw [Finset.card_univ, Fintype.card_prod]
    have h1 : Fintype.card (Fin (m+1) → Finset.Icc 1 X) = X ^ (m+1) := by simp [Nat.card_Icc]
    have h2 : Fintype.card (Fin m → Finset.Icc 1 X) = X ^ m := by simp [Nat.card_Icc]
    rw [h1, h2]
    rw [← pow_add]
    congr 1
    omega
  rw [hcard] at hle
  exact_mod_cast hle

end
end Submission.Vinogradov
