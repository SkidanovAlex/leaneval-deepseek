import Mathlib
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.egSigTKey

/-!
# Index facts for the key word `Work.Resample.buLamWord`

The facts about the two index maps `egRho s t ℓ = ⌊(2tℓ+s)/(2s)⌋` (the row index of `C̃`),
`egSigT s t k = (-s·k) mod t` (the index map of `P̃_t`) and `egLam` (the destination key of the
fused `C̃ ∘ P̃_t` step).

NOTE: these are the facts of `Work.Resample.buQWkey`, restated here because `buQWkey` imports
`Work.Resample.buQWdefs`, which re-declares `buTabList_eq` (already in `Work.Resample.buKit`), so
that `buQWdefs` and `buKit` cannot be imported into the same environment.  The word
`Work.Resample.buLamWord` needs `buKit` (for `buCB`/`buL7`), hence this restatement.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

private lemma div_add_div_le (A B c : ℕ) (hc : 0 < c) : A / c + B / c ≤ (A + B) / c := by
  rw [Nat.le_div_iff_mul_le hc, Nat.add_mul]
  exact Nat.add_le_add (Nat.div_mul_le_self A c) (Nat.div_mul_le_self B c)

private lemma egRho_lt_add (s t a c : ℕ) (hs : 0 < s) (hst : s < t) (hc : 0 < c) :
    egRho s t a < egRho s t (a + c) := by
  have h2s : 0 < 2 * s := by omega
  have hP : 2 * t * (a + c) + s = (2 * t * a + s) + 2 * t * c := by ring
  have hQ : 1 ≤ (2 * t * c) / (2 * s) := by
    rw [Nat.le_div_iff_mul_le h2s]
    have h2 : 2 * t ≤ 2 * t * c := by
      calc 2 * t = 2 * t * 1 := by ring
        _ ≤ 2 * t * c := Nat.mul_le_mul_left (2 * t) hc
    have h3 : 2 * s ≤ 2 * t := by omega
    simpa using le_trans h3 h2
  have hmain := div_add_div_le (2 * t * a + s) (2 * t * c) (2 * s) h2s
  rw [egRho, egRho, hP]
  omega

private lemma egRho_strictMono (s t : ℕ) (hs : 0 < s) (hst : s < t) : StrictMono (egRho s t) := by
  intro a b hab
  obtain ⟨c, hc⟩ : ∃ c, b = a + c := ⟨b - a, (Nat.add_sub_of_le (le_of_lt hab)).symm⟩
  have hc0 : 0 < c := by omega
  subst hc
  exact egRho_lt_add s t a c hs hst hc0

private lemma egRho_self (s t : ℕ) (hs : 0 < s) : egRho s t s = t := by
  have h2s : 0 < 2 * s := by omega
  rw [egRho]
  refine le_antisymm ?_ ?_
  · have h : (2 * t * s + s) / (2 * s) < t + 1 := by
      rw [Nat.div_lt_iff_lt_mul h2s]
      have hcast : (t + 1) * (2 * s) = 2 * t * s + 2 * s := by ring
      rw [hcast]
      omega
    omega
  · rw [Nat.le_div_iff_mul_le h2s]
    have hcast : t * (2 * s) = 2 * t * s := by ring
    rw [hcast]
    omega

lemma egRho_lt (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ : ℕ) (hℓ : ℓ < s) :
    egRho s t ℓ < t := by
  have h := egRho_strictMono s t hs hst hℓ
  rwa [egRho_self s t hs] at h

private lemma egNu_lt (s t : ℕ) (ht : 0 < t) (ℓ : Fin s) : egNu s t (ℓ : ℕ) < t := by
  simp only [egNu, egSigT]
  exact Nat.mod_lt _ ht

lemma egNu_inj (s t : ℕ) (hs : 0 < s) (hst : s < t) (hcop : Nat.Coprime s t) :
    Function.Injective (fun ℓ : Fin s => egNu s t (ℓ : ℕ)) := by
  have ht : 0 < t := lt_of_lt_of_le hs (le_of_lt hst)
  intro ℓ ℓ' h
  have h1 : egRho s t (ℓ : ℕ) = egRho s t (ℓ' : ℕ) :=
    (egSigTKey s t hcop ht).2 _ _
      (egRho_lt s t hs hst _ ℓ.isLt) (egRho_lt s t hs hst _ ℓ'.isLt) h
  exact Fin.ext ((egRho_strictMono s t hs hst).injective h1)

lemma egLam_of_mem (s t i : ℕ) (h : ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i) :
    egLam s t i = ((Classical.choose h : Fin s) : ℕ) :=
  dite_eq_left h

lemma egLam_of_not (s t i : ℕ) (h : ¬ ∃ ℓ : Fin s, egNu s t (ℓ : ℕ) = i) :
    egLam s t i = s + i :=
  dite_eq_right h

end Work.Resample
