import Mathlib
import Submission.Work.PTCert.LetterCore

/-!
# Injectivity of the Nielsen letters `Xtr`

`Xtr i j hij kind` is one of the eight Nielsen transvections attached to the ordered pair
`(i,j)` of distinct generators (`kind = 0,1,2,3` for `ρᵢⱼ, ρᵢⱼ⁻¹, λᵢⱼ, λᵢⱼ⁻¹`).

The map `(i, j, kind) ↦ Xtr i j hij kind` is injective on the domain `i ≠ j`, `kind < 4`.
The proof reads the pair and the kind off the *reduced word* of the image of the generator
`aᵢ`: the automorphism moves exactly one generator (`aᵢ`), and

  `ρᵢⱼ (aᵢ) = aᵢ aⱼ`,  `ρᵢⱼ⁻¹ (aᵢ) = aᵢ aⱼ⁻¹`,  `λᵢⱼ (aᵢ) = aⱼ aᵢ`,  `λᵢⱼ⁻¹ (aᵢ) = aⱼ⁻¹ aᵢ`,

whose reduced words are pairwise distinct (as `i ≠ j`).
-/

set_option autoImplicit false

namespace Work.PTCert

open Submission.PTCert Submission.FreeGroupAut

namespace XtrAux

/-- The reduced word of `Xtr i j hij kind (aᵢ)` depends only on `(i, j, kind)`, `kind < 4`. -/
def Xw {r : ℕ} (i j : Fin r) (kind : ℕ) : List (Fin r × Bool) :=
  if kind = 0 then [(i, true), (j, true)] else if kind = 1 then [(i, true), (j, false)]
    else if kind = 2 then [(j, true), (i, true)] else [(j, false), (i, true)]

/-- The reduced normal form `toWord` of `Xtr i j hij kind (aᵢ)`. -/
theorem Xtr_toWord_self {r : ℕ} (i j : Fin r) (hij : i ≠ j) (kind : ℕ) (hk : kind < 4) :
    (Submission.PTCert.Xtr i j hij kind (FreeGroup.of i)).toWord = Xw i j kind := by
  interval_cases kind <;>
    simp [Xw, FreeGroup.toWord_mul, rho_apply_self, rhoNeg_apply_self, lam_apply_self,
      lamNeg_apply_self, hij, Ne.symm hij]

/-- `Xtr i j hij kind` with `kind < 4` moves the generator `aᵢ`. -/
theorem Xtr_self_ne {r : ℕ} (i j : Fin r) (hij : i ≠ j) (kind : ℕ) (hk : kind < 4) :
    Submission.PTCert.Xtr i j hij kind (FreeGroup.of i) ≠ FreeGroup.of i := by
  intro h
  have h' := congrArg FreeGroup.toWord h
  rw [Xtr_toWord_self i j hij kind hk, FreeGroup.toWord_of] at h'
  interval_cases kind <;> simp [Xw] at h'

/-- `Xtr i j hij kind` fixes every generator other than `aᵢ`, whatever the kind. -/
theorem Xtr_apply_of_ne {r : ℕ} (i j : Fin r) (hij : i ≠ j) (kind : ℕ) {k : Fin r}
    (hk : k ≠ i) :
    Submission.PTCert.Xtr i j hij kind (FreeGroup.of k) = FreeGroup.of k := by
  unfold Submission.PTCert.Xtr
  split_ifs
  · exact rho_apply_other hij hk
  · exact rhoNeg_apply_other hij hk
  · exact lam_apply_other hij hk
  · exact lamNeg_apply_other hij hk

/-- The four words `Xw i j k` (`k < 4`) determine both `j` and `k`. -/
theorem Xw_inj {r : ℕ} (i j j' : Fin r) (hij : i ≠ j) (hij' : i ≠ j')
    (k k' : ℕ) (hk : k < 4) (hk' : k' < 4)
    (h : Xw i j k = Xw i j' k') : j = j' ∧ k = k' := by
  interval_cases k <;> interval_cases k' <;> simp [Xw] at h ⊢
  · exact h
  · exact absurd h.1 hij'
  · exact h
  · exact absurd h.1.symm hij
  · exact h
  · exact h

end XtrAux

/-- The Nielsen letters are injective: `Xtr i j hij k = Xtr i' j' hij' k'` with `k, k' < 4`
forces `i = i'`, `j = j'` and `k = k'`. -/
theorem XtrInjective {r : ℕ} (i j i' j' : Fin r) (hij : i ≠ j) (hij' : i' ≠ j')
    (k k' : ℕ) (hk : k < 4) (hk' : k' < 4)
    (h : Submission.PTCert.Xtr i j hij k = Submission.PTCert.Xtr i' j' hij' k') :
    i = i' ∧ j = j' ∧ k = k' := by
  -- the automorphism moves exactly the generators indexed by `i`, so `i = i'`
  have hii : i = i' := by
    by_contra hne
    have h1 : Submission.PTCert.Xtr i' j' hij' k' (FreeGroup.of i) = FreeGroup.of i :=
      XtrAux.Xtr_apply_of_ne i' j' hij' k' (k := i) (fun e => hne e)
    have h2 : Submission.PTCert.Xtr i j hij k (FreeGroup.of i) = FreeGroup.of i := by
      rw [h]; exact h1
    exact XtrAux.Xtr_self_ne i j hij k hk h2
  subst hii
  -- the reduced word of the image of `aᵢ` determines `j` and `k`
  have hw : XtrAux.Xw i j k = XtrAux.Xw i j' k' := by
    have h2 : (Submission.PTCert.Xtr i j hij k) (FreeGroup.of i)
        = (Submission.PTCert.Xtr i j' hij' k') (FreeGroup.of i) := by rw [h]
    have h3 := congrArg FreeGroup.toWord h2
    rwa [XtrAux.Xtr_toWord_self i j hij k hk,
      XtrAux.Xtr_toWord_self i j' hij' k' hk'] at h3
  obtain ⟨hj, hk2⟩ := XtrAux.Xw_inj i j j' hij hij' k k' hk hk' hw
  exact ⟨rfl, hj, hk2⟩

end Work.PTCert
