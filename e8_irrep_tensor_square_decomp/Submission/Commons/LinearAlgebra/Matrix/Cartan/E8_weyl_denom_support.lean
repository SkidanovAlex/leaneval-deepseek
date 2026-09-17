import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_denom

/-!
# The support of the Weyl denominator of `E₈`

Let `s` be the set of the `120` positive roots of `E₈` and let

  `C γ = ∑ T ∈ s.powerset, (if ∑_{α∈T} α = γ then (-1)^{T.card} else 0)`

be the coefficient of `e^{-γ}` in the Weyl denominator `∏_{α>0}(1 - e^{-α})`.

The main theorem `E8_weyl_denom_support` states that **every nonzero coefficient occurs at an
exponent `-γ` with `γ = ρ - wρ`** for some element `w = wact L` of the Weyl group.  (The companion
statement, giving the *values* `C (ρ - wρ) = ε(w)`, is the commons theorem `E8_weyl_denom`; the two
together say that the support of the Weyl denominator is exactly the Weyl orbit of `ρ`.)

The proof is the classical descent on the height.  The reflection identity
`C (sᵢ γ + αᵢ) = - C γ` (proved here by copying the sign-reversing involution argument of
`E8_weyl_denom`, which is private there) shows that `C γ` is controlled by its value at the
reflected weight `sᵢ γ + αᵢ` of strictly smaller height whenever `γᵢ ≥ 2`, while `γᵢ = 1` forces
`C γ = 0`.  A strong induction on the height finishes the proof; the remaining case of a weight
with all `γᵢ ≤ 0` inside the positive cone is `γ = 0 = ρ - wact [] ρ`.
-/

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan
namespace E8posRoots

/-! ## Coefficients of the Weyl denominator (copied from `E8_weyl_denom`, where they are private) -/

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
/-! ## Reduction of the support problem to the concrete positive roots `P` -/


/-! ## The support of the Weyl denominator -/

/-- The reflection identity in the form used by the support induction: `C (sᵢ γ + αᵢ) = - C γ`. -/
private lemma C_refl (i : Fin 8) (γ : Fin 8 → ℤ) : C (sref i γ + alpha i) = - C γ := by
  have h := C_sref i γ
  rwa [add_comm (alpha i) (sref i γ)] at h

/-- `sref i v = v - vᵢ αᵢ`. -/
private lemma sref_eq' (i : Fin 8) (v : Fin 8 → ℤ) : sref i v = v - v i • alpha i := by
  funext j
  simp only [sref, alpha, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-- `sref i ρ = ρ - αᵢ`. -/
private lemma sref_rhoZ (i : Fin 8) : sref i rhoZ = rhoZ - alpha i := by
  funext j
  simp only [sref, rhoZ, alpha, Pi.sub_apply]
  ring

/-- The height `∑ᵢ (coords γ)ᵢ` of a weight `γ`. -/
private def ht (γ : Fin 8 → ℤ) : ℤ := ∑ i, coords γ i

private lemma ht_add (a b : Fin 8 → ℤ) : ht (a + b) = ht a + ht b := by
  simp only [ht, coords_add, Pi.add_apply, Finset.sum_add_distrib]

private lemma ht_alpha (i : Fin 8) : ht (alpha i) = 1 := by
  unfold ht
  rw [coords_alpha]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma ht_sref (i : Fin 8) (γ : Fin 8 → ℤ) : ht (sref i γ) = ht γ - γ i := by
  unfold ht
  rw [coords_sref]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The height of the reflected weight: `ht (sᵢ γ + αᵢ) = ht γ + 1 - γᵢ`. -/
private lemma ht_sref_add_alpha (i : Fin 8) (γ : Fin 8 → ℤ) :
    ht (sref i γ + alpha i) = ht γ + 1 - γ i := by
  rw [ht_add, ht_sref, ht_alpha]; ring

/-- If some `α`-coordinate of `γ` is negative then the coefficient of `e^{-γ}` vanishes: no subset
of positive roots sums to a vector outside the cone `Q⁺`. -/
private lemma C_eq_zero_of_not_posCon (γ : Fin 8 → ℤ) (h : ∃ i, coords γ i < 0) : C γ = 0 := by
  obtain ⟨i, hi⟩ := h
  unfold C
  apply Finset.sum_eq_zero
  intro T hT
  by_cases hsum : (∑ β ∈ T, β) = γ
  · exfalso
    have hTsub : T ⊆ P := Finset.mem_powerset.mp hT
    have hc : coords γ i = ∑ β ∈ T, coords β i := by
      rw [← hsum]
      have h2 := congrFun (coords_sum T id) i
      simpa [Finset.sum_apply] using h2
    have hnn : 0 ≤ ∑ β ∈ T, coords β i :=
      Finset.sum_nonneg (fun β hβ => ((memP β).mp (hTsub hβ)).2.2 i)
    omega
  · rw [if_neg hsum]

/-- A nonvanishing coefficient of `e^{-γ}` forces `γ` into the positive cone `Q⁺`. -/
private lemma posCon_of_C_ne_zero (γ : Fin 8 → ℤ) (h : C γ ≠ 0) :
    ∀ i, 0 ≤ coords γ i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i, hi⟩ := hcon
  exact h (C_eq_zero_of_not_posCon γ ⟨i, hi⟩)

/-- The squared length `qZ` is nonnegative. -/
private lemma qZ_nonneg (v : Fin 8 → ℤ) : 0 ≤ E8NormTwo.qZ v := by
  have h := E8NormTwo.form2_nonneg (E8NormTwo.xc v)
  rw [E8NormTwo.form2_xc_self] at h
  exact_mod_cast h

private lemma int_toNat_lt {a b : ℤ} (ha : 0 ≤ a) (h : a < b) : a.toNat < b.toNat := by
  have hb : 0 ≤ b := le_of_lt (lt_of_le_of_lt ha h)
  have h1 : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha
  have h2 : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb
  omega

/-- **The support of the Weyl denominator, for the concrete positive roots `P`**: if the
coefficient of `e^{-γ}` is nonzero then `γ = ρ - wρ` for some word `L` of simple reflections. -/
private lemma exists_wact_of_C_ne_zero (γ : Fin 8 → ℤ) (h : C γ ≠ 0) :
    ∃ L : List (Fin 8), wact L rhoZ = rhoZ - γ := by
  suffices H : ∀ n : ℕ, ∀ γ : Fin 8 → ℤ, (ht γ).toNat = n → C γ ≠ 0 →
      ∃ L : List (Fin 8), wact L rhoZ = rhoZ - γ by
    exact H _ γ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hμ hC
    have hpos : ∀ i, 0 ≤ coords γ i := posCon_of_C_ne_zero γ hC
    by_cases hbig : ∃ i : Fin 8, 2 ≤ γ i
    · -- descent: reflect at a coordinate `γᵢ ≥ 2`
      obtain ⟨i, hi⟩ := hbig
      have hC' : C (sref i γ + alpha i) ≠ 0 := by
        rw [C_refl]; exact neg_ne_zero.mpr hC
      have hpos' : ∀ j, 0 ≤ coords (sref i γ + alpha i) j := posCon_of_C_ne_zero _ hC'
      have hlt : (ht (sref i γ + alpha i)).toNat < n := by
        rw [← hμ]
        refine int_toNat_lt (Finset.sum_nonneg (fun j _ => hpos' j)) ?_
        rw [ht_sref_add_alpha]
        omega
      obtain ⟨L, hL⟩ := ih _ hlt (sref i γ + alpha i) rfl hC'
      refine ⟨L ++ [i], ?_⟩
      rw [wact_append, hL]
      have hstep : sref i (rhoZ - (sref i γ + alpha i)) = rhoZ - γ := by
        rw [sref_sub, sref_rhoZ, sref_add, sref_alpha, sref_invol]
        abel
      simpa only [wact, List.foldl_cons, List.foldl_nil] using hstep
    · push_neg at hbig
      by_cases h1 : ∃ i : Fin 8, γ i = 1
      · -- `γᵢ = 1` forces `C γ = -C γ = 0`
        obtain ⟨i, hi⟩ := h1
        have hfix : sref i γ + alpha i = γ := by
          rw [sref_eq', hi, one_smul]
          abel
        have hCeq : C γ = - C γ := by
          have hh := C_refl i γ
          rwa [hfix] at hh
        exact absurd (by omega : C γ = 0) hC
      · -- all coordinates are `≤ 0`: then `γ = 0`
        push_neg at h1
        have hle : ∀ i, γ i ≤ 0 := fun i => by
          have h2 := hbig i; have h3 := h1 i; omega
        have hqZle : E8NormTwo.qZ γ ≤ 0 := by
          rw [qz_eq_dot]
          exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hpos j) (hle j))
        have hγ0 : γ = 0 := qz_eq_zero γ (le_antisymm hqZle (qZ_nonneg γ))
        refine ⟨[], ?_⟩
        rw [hγ0]
        simp [wact]


end E8posRoots

/-- The support half of the Weyl denominator formula: every nonzero coefficient of the Weyl
denominator `∏_{α>0}(1-e^{-α}) = ∑ T ∈ s.powerset, (-1)^T.card e^{-∑_{α∈T}α}` occurs at an exponent
`-γ` with `γ = ρ - wρ` for some Weyl group element `w`. The companion direction (the *values*,
`C (ρ - wρ) = ε(w)`) is already the commons theorem `E8_weyl_denom`.

PROOF STRATEGY (strong induction on `htOf γ`, using `C γ = ∑ T, if ∑ α ∈ T, α = γ then (-1)^T.card`):
* `C γ = 0` unless `posCon γ` (no subset of positive roots sums to a vector outside the cone `Q⁺`).
* Reflection identity (prove it here; the commons file `E8_weyl_denom` proves it as the *private*
  lemma `C_sref` by the sign-reversing involution `T ↦ sᵢ(T∖{αᵢ})` of `s.powerset`):
  `C (alpha i + sref i δ) = - C δ` for all `δ`, hence `C γ = - C (sref i γ + alpha i)`.
* ω-coordinates: `htOf (sref i γ + alpha i) = htOf γ - γ i + 1`.
* If `γ i = 1`: `sref i γ + alpha i = γ`, so `C γ = -C γ`, hence `C γ = 0`, contradiction with `h`.
* If `γ i ≥ 2` for some `i`: put `γ' = sref i γ + alpha i`; then `htOf γ' < htOf γ` and
  `C γ = -C γ'`. If `¬ posCon γ'` then `C γ' = 0` and hence `C γ = 0`, contradiction. Otherwise
  apply the induction hypothesis to `γ'`: `γ' = rhoZ - wact L rhoZ`, and then
  `γ = rhoZ - wact (i :: L) rhoZ` (using `sref`-linearity: `sref i (rhoZ - x) = rhoZ - alpha i - sref i x`).
* If `γ i ≤ 0` for all `i`: then `⟨γ, αᵢ⟩ ≤ 0` and `posCon γ`, so `qZ γ = ∑ j (coords γ) j * ⟨γ,αⱼ⟩ ≤ 0`,
  forcing `γ = 0 = rhoZ - wact [] rhoZ`. -/
theorem E8_weyl_denom_support (s : Finset (Fin 8 → ℤ))
    (hs : ∀ v : Fin 8 → ℤ,
      v ∈ s ↔ v ≠ 0 ∧ E8NormTwo.qZ v = 2 ∧ ∀ i, 0 ≤ coords v i)
    (γ : Fin 8 → ℤ)
    (h : (∑ T ∈ s.powerset,
        (if (∑ α ∈ T, α) = γ then (-1 : ℤ) ^ T.card else 0)) ≠ 0) :
    ∃ L : List (Fin 8), wact L rhoZ = rhoZ - γ := by
  have hPs : s = E8posRoots.P := by
    apply Finset.ext
    intro v
    rw [hs v, E8posRoots.memP, E8posRoots.IsPosRoot]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3⟩
  rw [hPs] at h
  exact E8posRoots.exists_wact_of_C_ne_zero γ h

end Commons.LinearAlgebra.Matrix.Cartan
