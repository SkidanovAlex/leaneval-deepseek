import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan
namespace E8posRoots

/-!
# The coefficient form of the Weyl denominator formula for `E₈`

Let `s` be the set of the `120` positive roots of `E₈` (written in the `ω`-basis) and let
`wact L` be the Weyl-group element defined by a word `L` of simple reflections.  The main theorem
of this file states that the coefficient of `e^{-(ρ - wρ)}` in the Weyl denominator
`∏_{α>0}(1 - e^{-α}) = ∑_{T ⊆ Φ⁺} (-1)^{|T|} e^{-∑_{α∈T}α}` equals the sign `ε(w) = (-1)^{|L|}`.

Everything is proved for the concrete finset `P` of positive roots; the theorem at the bottom
transfers to any `s` satisfying the characterising property of the positive roots.

The proof strategy is a direct induction on the word `L`, using the two facts

* `C 0 = 1` (the empty subset is the only one whose root-sum vanishes), and
* `C (α_i + s_i δ) = - C δ`, where `C δ` denotes the coefficient of `e^{-δ}`;

the second is proved by an explicit fixed-point-free, sign-reversing involution `Psi i` of the
power set of `P`, given by `T ↦ s_i (T ∖ {α_i})` (adding/removing `α_i` according to whether it
is present), which sends `{T : ∑_{α∈T} α = α_i + s_i δ}` bijectively onto `{T : ∑_{α∈T} α = δ}`.
-/

private lemma coords_sum {ι : Type*} (T : Finset ι) (g : ι → Fin 8 → ℤ) :
    coords (∑ i ∈ T, g i) = ∑ i ∈ T, coords (g i) := by
  change E8NormTwo.E8inv.mulVec (∑ i ∈ T, g i) = ∑ i ∈ T, E8NormTwo.E8inv.mulVec (g i)
  rw [Matrix.mulVec_sum]

private lemma sref_neg (i : Fin 8) (a : Fin 8 → ℤ) : sref i (-a) = - sref i a := by
  rw [← neg_one_smul ℤ a, sref_smul, neg_one_smul]

private lemma sref_sub (i : Fin 8) (a b : Fin 8 → ℤ) : sref i (a - b) = sref i a - sref i b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, sref_add, sref_neg]

private lemma wact_neg (L : List (Fin 8)) (a : Fin 8 → ℤ) : wact L (-a) = - wact L a := by
  rw [← neg_one_smul ℤ a, wact_smul, neg_one_smul]

private lemma wact_sub (L : List (Fin 8)) (a b : Fin 8 → ℤ) :
    wact L (a - b) = wact L a - wact L b := by
  rw [sub_eq_add_neg, sub_eq_add_neg, wact_add, wact_neg]

/-- `(-1)^{n-1} = -(-1)^n` for `n ≥ 1`. -/
private lemma neg_one_pow_pred (n : ℕ) (hn : 1 ≤ n) : (-1 : ℤ) ^ (n - 1) = - (-1) ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add, pow_one]
  ring

/-- The coefficient of `e^{-δ}` in the Weyl denominator `∏_{α>0}(1 - e^{-α})`. -/
private noncomputable def C (δ : Fin 8 → ℤ) : ℤ :=
  ∑ T ∈ P.powerset, (if (∑ β ∈ T, β) = δ then (-1 : ℤ) ^ T.card else 0)

/-- A nonempty subset of positive roots has a nonvanishing sum. -/
private lemma sum_ne_zero {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ P) (hne : T ≠ ∅) :
    (∑ β ∈ T, β) ≠ 0 := by
  intro h0
  obtain ⟨β, hβ⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hβP : β ∈ P := hT hβ
  obtain ⟨hq, hβ0, hc⟩ := (memP β).mp hβP
  have hcoord : coords (∑ γ ∈ T, γ) = ∑ γ ∈ T, coords γ := coords_sum T id
  have hzero : (∑ γ ∈ T, coords γ) = 0 := by rw [← hcoord, h0]; simp [coords]
  have hcnz : coords β ≠ 0 := by
    intro hc0
    exact hβ0 (by rw [← mulVec_coords β, hc0, Matrix.mulVec_zero])
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hcnz
  have hk' : coords β k ≠ 0 := by simpa using hk
  have hpos : 0 < coords β k := by have := hc k; omega
  have hle : coords β k ≤ (∑ γ ∈ T, coords γ) k := by
    rw [Finset.sum_apply]
    exact Finset.single_le_sum (fun γ hγ => (memP γ).mp (hT hγ) |>.2.2 k) hβ
  rw [hzero] at hle
  simp only [Pi.zero_apply] at hle
  omega

/-- The constant coefficient of the Weyl denominator is `1`. -/
private lemma C_zero : C 0 = 1 := by
  have hmain : C 0 = (if (∑ β ∈ (∅ : Finset (Fin 8 → ℤ)), β) = (0 : Fin 8 → ℤ)
      then (-1 : ℤ) ^ (∅ : Finset (Fin 8 → ℤ)).card else 0) := by
    unfold C
    exact Finset.sum_eq_single (∅ : Finset (Fin 8 → ℤ))
      (fun T hT hne => if_neg (sum_ne_zero (Finset.mem_powerset.mp hT) hne))
      (fun h => absurd (Finset.empty_mem_powerset P) h)
  rw [hmain]; simp

/-- The sign-reversing involution of the power set of `P` underlying the reflection identity:
`T ↦ s_i (T ∖ {α_i})`, where `α_i` is added back when it was absent. -/
private def Psi (i : Fin 8) (T : Finset (Fin 8 → ℤ)) : Finset (Fin 8 → ℤ) :=
  if alpha i ∈ T then (T.erase (alpha i)).image (sref i)
  else insert (alpha i) (T.image (sref i))

private lemma sref_mem_of_mem {i : Fin 8} {β : Fin 8 → ℤ} (hβ : β ∈ P) (hne : β ≠ alpha i) :
    sref i β ∈ P :=
  (memP _).mpr (sref_mem_posRoot i β ((memP β).mp hβ) hne)

private lemma alpha_mem_P (i : Fin 8) : alpha i ∈ P := (memP _).mpr (alpha_isPosRoot i)

private lemma alpha_not_mem_image_sref (i : Fin 8) {U : Finset (Fin 8 → ℤ)} (hU : U ⊆ P)
    (_hne : ∀ β ∈ U, β ≠ alpha i) : alpha i ∉ U.image (sref i) := by
  intro h
  obtain ⟨β, hβ, hb⟩ := Finset.mem_image.mp h
  have hβ' : β = -alpha i := by
    have hh : β = sref i (alpha i) := by
      have := congrArg (sref i) hb
      rwa [sref_invol] at this
    rw [sref_alpha] at hh
    exact hh
  exact neg_alpha_not_memP i (hβ' ▸ hU hβ)

private lemma Psi_subset (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ P) : Psi i T ⊆ P := by
  intro β hβ
  by_cases h : alpha i ∈ T
  · rw [Psi, if_pos h] at hβ
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hβ
    rw [Finset.mem_erase] at hγ
    exact sref_mem_of_mem (hT hγ.2) hγ.1
  · rw [Psi, if_neg h, Finset.mem_insert, Finset.mem_image] at hβ
    rcases hβ with rfl | ⟨γ, hγ, rfl⟩
    · exact alpha_mem_P i
    · exact sref_mem_of_mem (hT hγ) (fun heq => h (heq ▸ hγ))

private lemma Psi_invol (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ P) :
    Psi i (Psi i T) = T := by
  by_cases h : alpha i ∈ T
  · have hsub : T.erase (alpha i) ⊆ P := fun β hβ => hT (Finset.mem_erase.mp hβ).2
    have hne : ∀ β ∈ T.erase (alpha i), β ≠ alpha i :=
      fun β hβ => (Finset.mem_erase.mp hβ).1
    have hnot : alpha i ∉ (T.erase (alpha i)).image (sref i) :=
      alpha_not_mem_image_sref i hsub hne
    have hPsiT : Psi i T = (T.erase (alpha i)).image (sref i) := by rw [Psi, if_pos h]
    rw [hPsiT, Psi, if_neg hnot, Finset.image_image]
    rw [show (sref i ∘ sref i) = id from funext (sref_invol i), Finset.image_id]
    exact Finset.insert_erase h
  · have hne : ∀ β ∈ T, β ≠ alpha i := fun β hβ heq => h (heq ▸ hβ)
    have hnot : alpha i ∉ T.image (sref i) := alpha_not_mem_image_sref i hT hne
    have hPsiT : Psi i T = insert (alpha i) (T.image (sref i)) := by rw [Psi, if_neg h]
    rw [hPsiT, Psi, if_pos (Finset.mem_insert_self _ _), Finset.erase_insert hnot,
        Finset.image_image]
    rw [show (sref i ∘ sref i) = id from funext (sref_invol i), Finset.image_id]

private lemma sum_Psi (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ P) :
    (∑ β ∈ Psi i T, β) = alpha i + sref i (∑ β ∈ T, β) := by
  have hinj : Set.InjOn (sref i) ↑T := fun a _ b _ hab => (sref_invol i).injective hab
  by_cases h : alpha i ∈ T
  · have hinj' : Set.InjOn (sref i) ↑(T.erase (alpha i)) :=
      fun a _ b _ hab => (sref_invol i).injective hab
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
    have hnot : alpha i ∉ T.image (sref i) := alpha_not_mem_image_sref i hT hne
    have hPsiT : Psi i T = insert (alpha i) (T.image (sref i)) := by rw [Psi, if_neg h]
    rw [hPsiT, Finset.sum_insert hnot, Finset.sum_image hinj, ← sref_sum]

private lemma card_Psi (i : Fin 8) {T : Finset (Fin 8 → ℤ)} (hT : T ⊆ P) :
    (-1 : ℤ) ^ (Psi i T).card = - (-1 : ℤ) ^ T.card := by
  by_cases h : alpha i ∈ T
  · have hPsiT : Psi i T = (T.erase (alpha i)).image (sref i) := by rw [Psi, if_pos h]
    rw [hPsiT, Finset.card_image_of_injective _ (sref_invol i).injective,
        Finset.card_erase_of_mem h]
    exact neg_one_pow_pred T.card (Finset.card_pos.mpr ⟨alpha i, h⟩)
  · have hne : ∀ β ∈ T, β ≠ alpha i := fun β hβ heq => h (heq ▸ hβ)
    have hnot : alpha i ∉ T.image (sref i) := alpha_not_mem_image_sref i hT hne
    have hPsiT : Psi i T = insert (alpha i) (T.image (sref i)) := by rw [Psi, if_neg h]
    rw [hPsiT, Finset.card_insert_of_notMem hnot,
        Finset.card_image_of_injective _ (sref_invol i).injective, pow_succ]
    ring

/-- The reflection identity `C (α_i + s_i δ) = - C δ`: the coefficient of `e^{-(α_i + s_iδ)}` in
the Weyl denominator is the negative of the coefficient of `e^{-δ}`. -/
private lemma C_sref (i : Fin 8) (δ : Fin 8 → ℤ) : C (alpha i + sref i δ) = - C δ := by
  have hmem : ∀ T ∈ P.powerset, Psi i T ∈ P.powerset :=
    fun T hT => Finset.mem_powerset.mpr (Psi_subset i (Finset.mem_powerset.mp hT))
  have hinj : ∀ T1 ∈ P.powerset, ∀ T2 ∈ P.powerset, Psi i T1 = Psi i T2 → T1 = T2 := by
    intro T1 h1 T2 h2 heq
    calc T1 = Psi i (Psi i T1) := (Psi_invol i (Finset.mem_powerset.mp h1)).symm
      _ = Psi i (Psi i T2) := by rw [heq]
      _ = T2 := Psi_invol i (Finset.mem_powerset.mp h2)
  have hsurj : ∀ U ∈ P.powerset, ∃ T, ∃ _ : T ∈ P.powerset, Psi i T = U := by
    intro U hU
    exact ⟨Psi i U, hmem U hU, Psi_invol i (Finset.mem_powerset.mp hU)⟩
  have hfg : ∀ T ∈ P.powerset,
      (if (∑ β ∈ T, β) = alpha i + sref i δ then (-1 : ℤ) ^ T.card else 0)
        = -(if (∑ β ∈ Psi i T, β) = δ then (-1 : ℤ) ^ (Psi i T).card else 0) := by
    intro T hT
    have hT' : T ⊆ P := Finset.mem_powerset.mp hT
    have hss := sum_Psi i hT'
    have hc := card_Psi i hT'
    by_cases hcond : (∑ β ∈ T, β) = alpha i + sref i δ
    · have hcond' : (∑ β ∈ Psi i T, β) = δ := by
        rw [hss, hcond, sref_add, sref_alpha, sref_invol]; abel
      rw [if_pos hcond, if_pos hcond', hc]; ring
    · have hcond' : (∑ β ∈ Psi i T, β) ≠ δ := by
        intro hc2
        apply hcond
        have hthis : (∑ β ∈ Psi i T, β) = alpha i + sref i (∑ β ∈ T, β) := hss
        have h2 := (hthis.symm.trans hc2)
        have h3 := congrArg (sref i) h2
        rw [sref_add, sref_alpha, sref_invol] at h3
        rw [← h3]; abel
      rw [if_neg hcond, if_neg hcond']; ring
  calc C (alpha i + sref i δ)
      = ∑ T ∈ P.powerset, (if (∑ β ∈ T, β) = alpha i + sref i δ then (-1 : ℤ) ^ T.card else 0) := rfl
    _ = ∑ T ∈ P.powerset, -(if (∑ β ∈ Psi i T, β) = δ then (-1 : ℤ) ^ (Psi i T).card else 0) :=
          Finset.sum_congr rfl (fun T hT => hfg T hT)
    _ = -(∑ T ∈ P.powerset, (if (∑ β ∈ Psi i T, β) = δ then (-1 : ℤ) ^ (Psi i T).card else 0)) :=
          Finset.sum_neg_distrib _
    _ = -(∑ T ∈ P.powerset, (if (∑ β ∈ T, β) = δ then (-1 : ℤ) ^ T.card else 0)) := by
          congr 1
          exact Finset.sum_bij (fun T _ => Psi i T) hmem hinj hsurj (fun T hT => rfl)
    _ = - C δ := rfl

/-- The Weyl-denominator coefficient identity along a word of simple reflections. -/
private lemma key (L : List (Fin 8)) (γ : Fin 8 → ℤ) :
    C (wact L γ + (rhoZ - wact L rhoZ)) = (-1 : ℤ) ^ L.length * C γ := by
  induction L generalizing γ with
  | nil =>
      rw [List.length_nil, pow_zero, one_mul]
      congr 1
      simp [wact]
  | cons i L ih =>
      have hsrefrho : sref i rhoZ = rhoZ - alpha i := by
        funext j; simp only [sref, rhoZ, Pi.sub_apply, alpha]; ring
      have hwv : wact (i :: L) γ = wact L (sref i γ) := rfl
      have h1 : wact (i :: L) rhoZ = wact L (rhoZ - alpha i) := by
        rw [show wact (i :: L) rhoZ = wact L (sref i rhoZ) from rfl, hsrefrho]
      have hht : rhoZ - wact (i :: L) rhoZ = (rhoZ - wact L rhoZ) + wact L (alpha i) := by
        rw [h1, wact_sub]; abel
      rw [hwv, hht, List.length_cons]
      have hlin : wact L (sref i γ) + ((rhoZ - wact L rhoZ) + wact L (alpha i))
          = wact L (sref i γ + alpha i) + (rhoZ - wact L rhoZ) := by
        rw [wact_add]; abel
      rw [hlin, ih (sref i γ + alpha i), pow_succ]
      rw [add_comm (sref i γ) (alpha i), C_sref]
      ring

end E8posRoots

theorem E8_weyl_denom (s : Finset (Fin 8 → ℤ)) (hs : ∀ v : Fin 8 → ℤ, v ∈ s ↔ v ≠ 0 ∧ Commons.LinearAlgebra.Matrix.Cartan.E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ Commons.LinearAlgebra.Matrix.Cartan.coords v i) (L : List (Fin 8)) : (∑ T ∈ s.powerset, (if (∑ α ∈ T, α) = Commons.LinearAlgebra.Matrix.Cartan.rhoZ - Commons.LinearAlgebra.Matrix.Cartan.wact L Commons.LinearAlgebra.Matrix.Cartan.rhoZ then (-1 : ℤ) ^ T.card else 0)) = (-1 : ℤ) ^ L.length := by
  have hPs : s = E8posRoots.P := by
    apply Finset.ext
    intro v
    rw [hs v, E8posRoots.memP, E8posRoots.IsPosRoot]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3⟩
  rw [hPs]
  have := E8posRoots.key L 0
  rw [E8posRoots.wact_zero, zero_add, E8posRoots.C_zero, mul_one] at this
  exact this

end Commons.LinearAlgebra.Matrix.Cartan
