import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample
open HvdH

/-- Stripping the keys off the first `s` sorted records gives exactly `buPermL s t _ hcop.symm d`
(the final permutation `P̃_sᵀ`).  Use `egGam_spec` and `egKeyS_inj` to identify `i` with `egGam`. -/
theorem buScOut (s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hcop : Nat.Coprime s t)
    (d : List (ℤ × ℤ)) (hd : d.length = s) (ys : List Val) (hylen : ys.length = s)
    (hget : ∀ ℓ < s, ∃ i < s, egKeyS s t i = ℓ ∧
      ys.getD ℓ Val.nil = Val.cons (Val.int (ℓ : ℤ)) (cfxVal (d.getD i (0, 0)))) :
    (ys.take s).map buScStrip = (buPermL s t (by omega) hcop.symm d).map cfxVal := by
  -- The two proof arguments of `buPermL` are propositional, so fix them as variables: the `egGam`
  -- occurring in the unfolded right-hand side is then the very `egGam` of `egGam_spec`.
  have main : ∀ (hs0 : 0 < s) (hc0 : Nat.Coprime t s),
      (ys.take s).map buScStrip = (buPermL s t hs0 hc0 d).map cfxVal := by
    intro hs0 hc0
    -- `ys` is the `ofFn` of its own entries, of which there are exactly `s`.
    have hA : ys = List.ofFn (fun k : Fin s => ys.getD (k : ℕ) Val.nil) := by
      apply List.ext_getElem
      · simp [hylen]
      · intro i h1 h2
        rw [List.getElem_ofFn]
        exact (List.getD_eq_getElem ys Val.nil h1).symm
    rw [buPermL, List.take_of_length_le (le_of_eq hylen), hA, List.map_ofFn, List.map_ofFn,
      List.ofFn_inj]
    funext k
    show buScStrip (ys.getD (k : ℕ) Val.nil) =
      cfxVal (d.getD ((egGam s t hs0 hc0 k : Fin s) : ℕ) (0, 0))
    -- the `k`-th record has key `(k : ℕ)` and holds the `i`-th entry of `d`
    obtain ⟨i, hi, hkey, hval⟩ := hget (k : ℕ) k.isLt
    rw [hval, buScStrip_apply]
    -- and `i` is the source index of the final permutation, since `i ↦ (t·i) % s` is injective
    have hii : i = ((egGam s t hs0 hc0 k : Fin s) : ℕ) :=
      egKeyS_inj s t hs0 hc0 hi (egGam s t hs0 hc0 k).isLt
        (hkey.trans (egGam_spec s t hs0 hc0 k).symm)
    rw [hii]
  exact main (by omega) hcop.symm

end Work.Resample
