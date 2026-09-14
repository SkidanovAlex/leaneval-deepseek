import Mathlib
import Submission.Vdw.ResidueIndex
import Submission.Commons.FieldTheory.Polynomial.discr_constCoeff_rootCard_le

/-!
# Case III stone (A)(ii): root count of `Disc` in the constant coefficient

**Goal of the chapter.**  Bhargava's Case III needs, per prime `p` with `p ∤ n`, the
bound `#{c ∈ 𝔽_p : Disc(f_c) = 0} ≤ n − 1` where `f_c` is a monic degree-`n` polynomial
with all coefficients fixed except the constant one (`c`).  Equivalently, varying only
`coeff 0` of `monicOfTrail n v` over `𝔽_p`, at most `n − 1` choices make the
discriminant vanish.  (These are the paper's "at most `deg_{a_n}(Disc) = n − 1` solutions
for `a_n` (mod `p`) to `Disc(f) ≡ 0`".)

The field-theoretic proof is the fleet commons lemma
`Commons.FieldTheory.Polynomial.discr_constCoeff_rootCard_le`: `Disc(f_c) = 0`
iff `f_c` is inseparable (commons `discr_eq_zero_iff_not_separable`), iff `f_c` and the
`c`-independent derivative `f'` have a common root in the algebraic closure; each such
root is a root of the fixed `f'` (at most `n − 1` of them) and determines `c` back, so
at most `n − 1` values of `c` are counted.  This module glues that lemma to the corpus's
`monicOfTrail` language over `𝔽_p`.
-/

set_option linter.unusedSectionVars false

namespace Submission.Vdw

noncomputable section

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [DecidableEq F]

/-- Changing the constant coefficient of `monicOfTrail n v` from `v 0` to `c` is the
same as changing the trailing-coefficient vector: `monicOfTrail` is linear in its
trailing vector `v`. -/
theorem monicOfTrail_update_zero (n : ℕ) (v : Fin n → F) (hn0 : 0 < n) (c : F) :
    monicOfTrail n (Function.update v ⟨0, hn0⟩ c) =
      monicOfTrail n v - Polynomial.C (v ⟨0, hn0⟩) + Polynomial.C c := by
  ext i
  by_cases hin : i = n
  · subst i
    simp [monicOfTrail, Polynomial.ofFn_coeff_eq_zero_of_ge (v := Function.update v ⟨0, hn0⟩ c) (by omega : n ≤ n),
          Polynomial.ofFn_coeff_eq_zero_of_ge (v := v) (by omega : n ≤ n)]
    have hnn : n ≠ 0 := by omega
    simp [Polynomial.coeff_C, hnn]
  · rcases lt_or_ge i n with hilt | hge
    · by_cases hi0 : i = 0
      · subst i
        have hcoefL : (Polynomial.ofFn n (Function.update v ⟨0, hn0⟩ c)).coeff 0 = c := by
          rw [Polynomial.ofFn_coeff_eq_val_of_lt (v := Function.update v ⟨0, hn0⟩ c) hn0]
          simp [Function.update]
        have hcoefR1 : (Polynomial.ofFn n v).coeff 0 = v ⟨0, hn0⟩ := by
          rw [Polynomial.ofFn_coeff_eq_val_of_lt (v := v) hn0]
        simp [monicOfTrail, hcoefL, hcoefR1]
      · have hcoefX : (X ^ n : F[X]).coeff i = 0 := by
          rw [Polynomial.coeff_X_pow]; simp [hin]
        have hcoefL : (Polynomial.ofFn n (Function.update v ⟨0, hn0⟩ c)).coeff i = v ⟨i, hilt⟩ := by
          rw [Polynomial.ofFn_coeff_eq_val_of_lt (v := Function.update v ⟨0, hn0⟩ c) hilt]
          have hne : (⟨i, hilt⟩ : Fin n) ≠ ⟨0, hn0⟩ := by
            intro h; exact hi0 (Fin.ext_iff.mp h)
          simp [Function.update, hne]
        have hcoefR1 : (Polynomial.ofFn n v).coeff i = v ⟨i, hilt⟩ := by
          rw [Polynomial.ofFn_coeff_eq_val_of_lt (v := v) hilt]
        have hC (a : F) : (Polynomial.C a : F[X]).coeff i = 0 := by
          simp [Polynomial.coeff_C, hi0]
        simp [monicOfTrail, hcoefX, hcoefL, hcoefR1, hC]
    · -- n ≤ i and i ≠ n
      have hgt : n < i := lt_of_le_of_ne hge (by intro h; exact hin h.symm)
      have hin' : ¬ i = n := by omega
      have hcoefL : (Polynomial.ofFn n (Function.update v ⟨0, hn0⟩ c)).coeff i = 0 := by
        rw [Polynomial.ofFn_coeff_eq_zero_of_ge (v := Function.update v ⟨0, hn0⟩ c) hge]
      have hcoefR : (Polynomial.ofFn n v).coeff i = 0 := by
        rw [Polynomial.ofFn_coeff_eq_zero_of_ge (v := v) hge]
      have hX0 : (X ^ n : F[X]).coeff i = 0 := by
        rw [Polynomial.coeff_X_pow]; simp [hin']
      have hi0' : i ≠ 0 := by omega
      have hC (a : F) : (Polynomial.C a : F[X]).coeff i = 0 := by
        simp [Polynomial.coeff_C, hi0']
      simp [monicOfTrail, hcoefL, hcoefR, hX0, hC]

/-- **Corollary for the corpus (Case III / geometric sieve):** over `𝔽_p` with `p ∤ n`
(`2 ≤ n`), fixing the trailing coefficients `v` of a monic degree-`n` polynomial, at most
`n − 1` choices of the *constant* coefficient make the discriminant vanish:
`#{c ∈ 𝔽_p : Disc(monicOfTrail n (update v 0 c)) = 0} ≤ n − 1`. -/
theorem monicOfTrail_constCoeff_rootCard_le (p n : ℕ) [Fact (Nat.Prime p)] (hn : 2 ≤ n)
    (hpn : ¬ p ∣ n) (v : Fin n → ZMod p) :
    ({c : ZMod p |
        Polynomial.discr (monicOfTrail n (Function.update v ⟨0, (by omega : 0 < n)⟩ c)) = 0} :
      Set (ZMod p)).ncard ≤ n - 1 := by
  have hn0 : 0 < n := by omega
  let f : (ZMod p)[X] := monicOfTrail n v
  have hfmon : f.Monic := by simpa [f] using (monicOfTrail_monic n v)
  have hfdeg : f.natDegree = n := by simpa [f] using (monicOfTrail_natDegree n v)
  have hfam : ∀ c : ZMod p,
      f - Polynomial.C (f.coeff 0) + Polynomial.C c =
        monicOfTrail n (Function.update v ⟨0, hn0⟩ c) := by
    intro c
    dsimp [f]
    rw [monicOfTrail_coeff n v (i := 0) hn0]
    exact (monicOfTrail_update_zero (F := ZMod p) n v hn0 c).symm
  have hchar : (n : ZMod p) ≠ 0 := by
    exact (not_iff_not.mpr (CharP.cast_eq_zero_iff (ZMod p) p n)).mpr hpn
  -- apply the commons lemma to f and translate the counted set
  have hmain : ({c : ZMod p |
      Polynomial.discr (f - Polynomial.C (f.coeff 0) + Polynomial.C c) = 0} : Set (ZMod p)).ncard ≤
        f.natDegree - 1 :=
    Commons.FieldTheory.Polynomial.discr_constCoeff_rootCard_le (F := ZMod p) (f := f) hfmon
      (by simpa [hfdeg] using hn) (by simpa [hfdeg] using hchar)
  calc
    ({c : ZMod p |
        Polynomial.discr (monicOfTrail n (Function.update v ⟨0, hn0⟩ c)) = 0} : Set (ZMod p)).ncard
        = ({c : ZMod p |
            Polynomial.discr (f - Polynomial.C (f.coeff 0) + Polynomial.C c) = 0} : Set (ZMod p)).ncard := by
            apply congrArg Set.ncard
            ext c
            simp [hfam c]
    _ ≤ f.natDegree - 1 := hmain
    _ = n - 1 := by rw [hfdeg]
