import Mathlib
import Submission.Work.PTCert.EntryDefs
import Submission.Work.PTCert.sigmaGroupFacts

open Submission.PTCert Submission.PTCert.G Submission.PTCert.D
open Submission.FreeGroupAut Submission.RouteB

namespace Work.PTCert

variable {k : ℕ}

/-- The `a`-th table of the Klein data of the base character `k` (`a < 4`, `efKl k a = (klTs.getD k (NT.leaf 0)).get a`)
is the letter table of the permutation automorphism `permAut (kleinPerm k a)`: `TabOf σ tab` means
`σ * b1 5 j * σ⁻¹ = b1 5 (lk tab j)` for all `j < 81` (GlueDefs).  KleinSem's first clause gives
`lk (efKl k a) j = actL 5 (pcOf (kleinPerm k a)) 0 j`; `CodeFacts` gives
`codeElt (32 * pcOf p + scOf s) = sigAut p s = signAut s * permAut p` (with `s` constantly false and
`scOf s = 0` this is `codeElt (32 * pcOf p) = permAut p`), and its first clause applied to
`c = 32 * pcOf p` gives both the conjugation identity (with `actL 5 (pcOf p) 0 j`) and the bound `lk < 81`. -/
theorem tabOf_kleinPerm (hCF : CodeFacts) (hK : KleinSem k) (a : ℕ) (ha : a < 4) :
    TabOf (permAut (kleinPerm k a)) (efKl k a) ∧ (∀ j < 81, lk (efKl k a) j < 81) := by
  classical
  set p := kleinPerm k a with hp
  -- `pcOf p` is a valid permutation code (CodeFacts, clause 3).
  have hvalid : validPC 5 (pcOf p) = true := (hCF.2.2.1 p (fun _ : Fin 5 => false)).1
  -- `codeElt (32 * pcOf p) = permAut p` (CodeFacts, clause 3 with the constant-false sign function).
  have hsc : scOf (fun _ : Fin 5 => false) = 0 := by simp [scOf]
  have hsig : sigAut p (fun _ : Fin 5 => false) = permAut p := by
    rw [sigAut, SigmaFacts.signAut_one, one_mul]
  have hcode : codeElt (32 * pcOf p) = permAut p := by
    have h2 := (hCF.2.2.1 p (fun _ : Fin 5 => false)).2.2
    have harg : 32 * pcOf p + scOf (fun _ : Fin 5 => false) = 32 * pcOf p := by rw [hsc, add_zero]
    calc codeElt (32 * pcOf p)
        = codeElt (32 * pcOf p + scOf (fun _ : Fin 5 => false)) := by rw [harg]
      _ = sigAut p (fun _ : Fin 5 => false) := h2
      _ = permAut p := hsig
  have hdiv : (32 * pcOf p) / 32 = pcOf p := Nat.mul_div_cancel_left (pcOf p) (by norm_num)
  have hmod : (32 * pcOf p) % 32 = 0 := Nat.mul_mod_right 32 (pcOf p)
  have hvalid' : validPC 5 ((32 * pcOf p) / 32) = true := by rw [hdiv]; exact hvalid
  -- CodeFacts, clause 1 at `c = 32 * pcOf p`.
  have hact : ∀ j < 81, codeElt (32 * pcOf p) * b1 5 j * (codeElt (32 * pcOf p))⁻¹
      = b1 5 (actL 5 (pcOf p) 0 j) := by
    intro j hj
    have h := (hCF.1 (32 * pcOf p) hvalid').2 j hj
    rw [hdiv, hmod] at h
    exact h.2
  have hactb : ∀ j < 81, actL 5 (pcOf p) 0 j < 81 := by
    intro j hj
    have h := (hCF.1 (32 * pcOf p) hvalid').2 j hj
    rw [hdiv, hmod] at h
    exact h.1
  -- KleinSem, first clause.
  have hL : ∀ j < 81, lk (efKl k a) j = actL 5 (pcOf p) 0 j := by
    intro j hj
    have h := hK.1 a ha j hj
    rw [← hp] at h
    simpa only [efKl] using h
  refine ⟨?_, ?_⟩
  · intro j hj
    rw [hL j hj, ← hact j hj, ← hcode]
  · intro j hj
    rw [hL j hj]
    exact hactb j hj

end Work.PTCert
