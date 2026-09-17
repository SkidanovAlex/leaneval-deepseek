import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan
namespace E8denomRefl

/-!
# The reflection identity for the coefficient form of the Weyl denominator of `E₈`

Let `s` be the finset of the `120` positive roots of `E₈` (the nonzero lattice vectors of squared
length `2` whose simple-root coordinates are nonnegative) and let

  `C(δ) = ∑_{T ⊆ s, ∑_{α∈T} α = δ} (-1)^{|T|}`

be the coefficient of `e^{-δ}` in the Weyl denominator `∏_{α>0}(1 - e^{-α})`.  This file proves the
**reflection identity**

  `C(αᵢ + sᵢδ) = - C(δ)`  for every `i` and `δ`,

the only nontrivial combinatorial input of the Weyl denominator formula for `E₈`.  The proof is the
explicit fixed-point-free, sign-reversing involution `T ↦ sᵢ(T ∖ {αᵢ})` of the power set of `s`
(add/remove `αᵢ` according to whether it is present), which maps
`{T : ∑_{α∈T} α = αᵢ + sᵢδ}` bijectively onto `{T : ∑_{α∈T} α = δ}` while flipping `(-1)^{|T|}`.

Everything is proved for an arbitrary `s` satisfying the characterising property of the positive
roots, so the result is stated exactly in the form needed downstream.
-/

/-! ## Elementary facts about `sref` -/

private lemma sref_neg (i : Fin 8) (a : Fin 8 → ℤ) : sref i (-a) = - sref i a := by
  funext j
  simp only [sref_apply, Pi.neg_apply]
  ring

private lemma sref_sub (i : Fin 8) (a b : Fin 8 → ℤ) :
    sref i (a - b) = sref i a - sref i b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sref_add, sref_neg]

private lemma sref_sum (i : Fin 8) (T : Finset (Fin 8 → ℤ)) :
    sref i (∑ v ∈ T, v) = ∑ v ∈ T, sref i v := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [sref_zero]
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sref_add, ih]

private lemma sref_invol_fun (i : Fin 8) : Function.Involutive (sref i) := sref_invol i

private lemma sref_alpha (i : Fin 8) : sref i (alpha i) = - alpha i := by
  funext j
  simp only [sref_apply, Pi.neg_apply, alpha_apply, E8m_diag]
  ring

/-- `(-1)^{n-1} = -(-1)^n` for `n ≥ 1`. -/
private lemma neg_one_pow_pred (n : ℕ) (hn : 1 ≤ n) : (-1 : ℤ) ^ (n - 1) = - (-1) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add, pow_one]
  ring

/-! ## Bridging the two copies of the `E₈` lattice data

The commons development `E8posRoots` and the "outer" namespace carry two definitionally equal
copies of `coords`, `sref` (and an `alpha` which is equal, but not definitionally).  The next three
lemmas identify them. -/

private lemma alpha_eq (i : Fin 8) : E8posRoots.alpha i = alpha i := by
  have hα : (fun j => CartanMatrix.E₈ i j) = CartanMatrix.E₈.mulVec (Pi.single i 1) := by
    rw [Matrix.mulVec_single_one]
    funext j
    simp only [Matrix.col_apply]
    exact E8posRoots.E8_symm i j
  exact hα

private lemma coords_eq : (E8posRoots.coords : (Fin 8 → ℤ) → Fin 8 → ℤ) = coords := rfl

private lemma sref_eq_fun : (E8posRoots.sref : Fin 8 → (Fin 8 → ℤ) → (Fin 8 → ℤ)) = sref := rfl

/-! ## Membership in `s` and the three facts about positive roots -/

private lemma mem_iff_isPosRoot (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (v : Fin 8 → ℤ) : v ∈ s ↔ E8posRoots.IsPosRoot v := by
  rw [hs v]
  simp only [E8posRoots.IsPosRoot, coords_eq]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

private lemma alpha_mem (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) : alpha i ∈ s := by
  have h := E8posRoots.alpha_isPosRoot i
  rw [alpha_eq i] at h
  exact (mem_iff_isPosRoot s hs (alpha i)).mpr h

private lemma sref_mem (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    {i : Fin 8} {β : Fin 8 → ℤ} (hβ : β ∈ s) (hne : β ≠ alpha i) : sref i β ∈ s := by
  have hroot : E8posRoots.IsPosRoot β := (mem_iff_isPosRoot s hs β).mp hβ
  have hne' : β ≠ E8posRoots.alpha i := by rw [alpha_eq i]; exact hne
  have h := E8posRoots.sref_mem_posRoot i β hroot hne'
  rw [sref_eq_fun] at h
  exact (mem_iff_isPosRoot s hs (sref i β)).mpr h

private lemma neg_alpha_not_mem (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) : -alpha i ∉ s := by
  intro h
  have hroot : E8posRoots.IsPosRoot (-alpha i) := (mem_iff_isPosRoot s hs (-alpha i)).mp h
  have h' : (-alpha i : Fin 8 → ℤ) = -(E8posRoots.alpha i) := by rw [alpha_eq i]
  rw [h'] at hroot
  exact E8posRoots.neg_alpha_not_memP i ((E8posRoots.memP _).mpr hroot)

/-! ## The sign-reversing involution of the power set of `s` -/

private def Psi (i : Fin 8) (T : Finset (Fin 8 → ℤ)) : Finset (Fin 8 → ℤ) :=
  if alpha i ∈ T then (T.erase (alpha i)).image (sref i)
  else insert (alpha i) (T.image (sref i))

private lemma alpha_not_mem_image_sref (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) {U : Finset (Fin 8 → ℤ)} (hU : U ⊆ s) (_hne : ∀ β ∈ U, β ≠ alpha i) :
    alpha i ∉ U.image (sref i) := by
  intro h
  obtain ⟨β, hβ, hb⟩ := Finset.mem_image.mp h
  have hβ' : β = -alpha i := by
    have hh : β = sref i (alpha i) := by
      have hcong := congrArg (sref i) hb
      rwa [sref_invol] at hcong
    rw [sref_alpha] at hh
    exact hh
  exact neg_alpha_not_mem s hs i (hβ' ▸ hU hβ)

private lemma Psi_subset (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ s) : Psi i T ⊆ s := by
  intro β hβ
  by_cases h : alpha i ∈ T
  · rw [Psi, if_pos h] at hβ
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hβ
    rw [Finset.mem_erase] at hγ
    exact sref_mem s hs (hT hγ.2) hγ.1
  · rw [Psi, if_neg h, Finset.mem_insert, Finset.mem_image] at hβ
    rcases hβ with rfl | ⟨γ, hγ, rfl⟩
    · exact alpha_mem s hs i
    · exact sref_mem s hs (hT hγ) (fun heq => h (heq ▸ hγ))

private lemma Psi_invol (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ s) : Psi i (Psi i T) = T := by
  by_cases h : alpha i ∈ T
  · have hsub : T.erase (alpha i) ⊆ s := fun β hβ => hT (Finset.mem_erase.mp hβ).2
    have hne : ∀ β ∈ T.erase (alpha i), β ≠ alpha i :=
      fun β hβ => (Finset.mem_erase.mp hβ).1
    have hnot : alpha i ∉ (T.erase (alpha i)).image (sref i) :=
      alpha_not_mem_image_sref s hs i hsub hne
    have hPsiT : Psi i T = (T.erase (alpha i)).image (sref i) := by rw [Psi, if_pos h]
    rw [hPsiT, Psi, if_neg hnot, Finset.image_image]
    rw [show (sref i ∘ sref i) = id from funext (sref_invol_fun i), Finset.image_id]
    exact Finset.insert_erase h
  · have hne : ∀ β ∈ T, β ≠ alpha i := fun β hβ heq => h (heq ▸ hβ)
    have hnot : alpha i ∉ T.image (sref i) := alpha_not_mem_image_sref s hs i hT hne
    have hPsiT : Psi i T = insert (alpha i) (T.image (sref i)) := by rw [Psi, if_neg h]
    rw [hPsiT, Psi, if_pos (Finset.mem_insert_self _ _), Finset.erase_insert hnot,
        Finset.image_image]
    rw [show (sref i ∘ sref i) = id from funext (sref_invol_fun i), Finset.image_id]

private lemma sum_Psi (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ s) :
    (∑ β ∈ Psi i T, β) = alpha i + sref i (∑ β ∈ T, β) := by
  have hinj : Set.InjOn (sref i) ↑T := fun a _ b _ hab => (sref_invol_fun i).injective hab
  by_cases h : alpha i ∈ T
  · have hinj' : Set.InjOn (sref i) ↑(T.erase (alpha i)) :=
      fun a _ b _ hab => (sref_invol_fun i).injective hab
    have hPsiT : Psi i T = (T.erase (alpha i)).image (sref i) := by rw [Psi, if_pos h]
    have hss : (∑ β ∈ T.erase (alpha i), β) = (∑ β ∈ T, β) - alpha i := by
      have hins : insert (alpha i) (T.erase (alpha i)) = T := Finset.insert_erase h
      have hone : (∑ β ∈ T, β) = alpha i + ∑ β ∈ T.erase (alpha i), β := by
        conv_lhs => rw [← hins]
        rw [Finset.sum_insert (Finset.notMem_erase (alpha i) T)]
      rw [hone]; abel
    rw [hPsiT, Finset.sum_image hinj', ← sref_sum, hss, sref_sub, sref_alpha]
    abel
  · have hne : ∀ β ∈ T, β ≠ alpha i := fun β hβ heq => h (heq ▸ hβ)
    have hnot : alpha i ∉ T.image (sref i) := alpha_not_mem_image_sref s hs i hT hne
    have hPsiT : Psi i T = insert (alpha i) (T.image (sref i)) := by rw [Psi, if_neg h]
    rw [hPsiT, Finset.sum_insert hnot, Finset.sum_image hinj, ← sref_sum]

private lemma card_Psi (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ s) :
    (-1 : ℤ) ^ (Psi i T).card = - (-1 : ℤ) ^ T.card := by
  by_cases h : alpha i ∈ T
  · have hPsiT : Psi i T = (T.erase (alpha i)).image (sref i) := by rw [Psi, if_pos h]
    rw [hPsiT, Finset.card_image_of_injective _ (sref_invol_fun i).injective,
        Finset.card_erase_of_mem h]
    exact neg_one_pow_pred T.card (Finset.card_pos.mpr ⟨alpha i, h⟩)
  · have hne : ∀ β ∈ T, β ≠ alpha i := fun β hβ heq => h (heq ▸ hβ)
    have hnot : alpha i ∉ T.image (sref i) := alpha_not_mem_image_sref s hs i hT hne
    have hPsiT : Psi i T = insert (alpha i) (T.image (sref i)) := by rw [Psi, if_neg h]
    rw [hPsiT, Finset.card_insert_of_notMem hnot,
        Finset.card_image_of_injective _ (sref_invol_fun i).injective, pow_succ]
    ring

/-! ## The reflection identity -/

private lemma refl_identity (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) (δ : Fin 8 → ℤ) :
    (∑ T ∈ s.powerset,
        (if (∑ α ∈ T, α) = alpha i + sref i δ then (-1 : ℤ) ^ T.card else 0))
      = - (∑ T ∈ s.powerset,
        (if (∑ α ∈ T, α) = δ then (-1 : ℤ) ^ T.card else 0)) := by
  have hmem : ∀ T ∈ s.powerset, Psi i T ∈ s.powerset :=
    fun T hT => Finset.mem_powerset.mpr (Psi_subset s hs i (Finset.mem_powerset.mp hT))
  have hinj : ∀ T1 ∈ s.powerset, ∀ T2 ∈ s.powerset, Psi i T1 = Psi i T2 → T1 = T2 := by
    intro T1 h1 T2 h2 heq
    calc T1 = Psi i (Psi i T1) := (Psi_invol s hs i (Finset.mem_powerset.mp h1)).symm
      _ = Psi i (Psi i T2) := by rw [heq]
      _ = T2 := Psi_invol s hs i (Finset.mem_powerset.mp h2)
  have hsurj : ∀ U ∈ s.powerset, ∃ T, ∃ _ : T ∈ s.powerset, Psi i T = U := by
    intro U hU
    exact ⟨Psi i U, hmem U hU, Psi_invol s hs i (Finset.mem_powerset.mp hU)⟩
  have hfg : ∀ T ∈ s.powerset,
      (if (∑ β ∈ T, β) = alpha i + sref i δ then (-1 : ℤ) ^ T.card else 0)
        = -(if (∑ β ∈ Psi i T, β) = δ then (-1 : ℤ) ^ (Psi i T).card else 0) := by
    intro T hT
    have hT' : T ⊆ s := Finset.mem_powerset.mp hT
    have hss := sum_Psi s hs i hT'
    have hc := card_Psi s hs i hT'
    by_cases hcond : (∑ β ∈ T, β) = alpha i + sref i δ
    · have hcond' : (∑ β ∈ Psi i T, β) = δ := by
        rw [hss, hcond, sref_add, sref_alpha, sref_invol]; abel
      rw [if_pos hcond, if_pos hcond', hc]; ring
    · have hcond' : (∑ β ∈ Psi i T, β) ≠ δ := by
        intro hc2
        apply hcond
        have h2 := (hss.symm.trans hc2)
        have h3 := congrArg (sref i) h2
        rw [sref_add, sref_alpha, sref_invol] at h3
        rw [← h3]; abel
      rw [if_neg hcond, if_neg hcond']; ring
  calc (∑ T ∈ s.powerset,
        (if (∑ α ∈ T, α) = alpha i + sref i δ then (-1 : ℤ) ^ T.card else 0))
      = ∑ T ∈ s.powerset,
          -(if (∑ β ∈ Psi i T, β) = δ then (-1 : ℤ) ^ (Psi i T).card else 0) :=
        Finset.sum_congr rfl (fun T hT => hfg T hT)
    _ = -(∑ T ∈ s.powerset,
          (if (∑ β ∈ Psi i T, β) = δ then (-1 : ℤ) ^ (Psi i T).card else 0)) :=
        Finset.sum_neg_distrib _
    _ = -(∑ T ∈ s.powerset, (if (∑ β ∈ T, β) = δ then (-1 : ℤ) ^ T.card else 0)) := by
        congr 1
        exact Finset.sum_bij (fun T _ => Psi i T) hmem hinj hsurj (fun T hT => rfl)

end E8denomRefl

theorem E8_weyl_denom_refl (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ,
      v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (i : Fin 8) (δ : Fin 8 → ℤ) :
    (∑ T ∈ s.powerset,
        (if (∑ α ∈ T, α) = alpha i + sref i δ then (-1 : ℤ) ^ T.card else 0))
      = - (∑ T ∈ s.powerset,
        (if (∑ α ∈ T, α) = δ then (-1 : ℤ) ^ T.card else 0)) :=
  E8denomRefl.refl_identity s hs i δ

end Commons.LinearAlgebra.Matrix.Cartan
