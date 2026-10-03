import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- `(u² + v²).natAbs = u.natAbs² + v.natAbs²`: the norm is the sum of the squares of the
absolute values. -/
lemma natAbs_sq_add_sq (u v : ℤ) :
    (u ^ 2 + v ^ 2).natAbs = u.natAbs ^ 2 + v.natAbs ^ 2 := by
  have h : ((u ^ 2 + v ^ 2).natAbs : ℤ) = (u.natAbs : ℤ) ^ 2 + (v.natAbs : ℤ) ^ 2 := by
    rw [Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ u ^ 2 + v ^ 2)]
    rw [Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
  exact_mod_cast h

/-- For `u` odd and `v` even the norm `u² + v²` is `≡ 1 (mod 4)`. -/
lemma sq_add_sq_mod_four {u v : ℤ} (hu : Odd u) (hv : Even v) :
    (u ^ 2 + v ^ 2).natAbs % 4 = 1 := by
  have hU2 : u.natAbs ^ 2 % 4 = 1 := by
    rw [Nat.pow_mod]
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hu.natAbs) with h | h <;> rw [h]
  have hV2 : v.natAbs ^ 2 % 4 = 0 := by
    obtain ⟨l, hl⟩ := hv.natAbs
    rw [hl]
    have : (l + l) ^ 2 = 4 * l ^ 2 := by ring
    rw [this]
    exact Nat.mul_mod_right 4 (l ^ 2)
  simp only [natAbs_sq_add_sq, Nat.add_mod, hU2, hV2, Nat.reduceMod]

/-- *FI* (19.8): for `u` odd, `v` even and `(u,v) = 1`, the Jacobi symbol of `u` against the norm
`q = u² + v²` equals `1` (`(u/q) = (|u|/q) = (q/|u|) = (v²/|u|) = 1`, the middle step being
quadratic reciprocity (17.6) with `q ≡ v² (mod |u|)` and `q ≡ 1 (mod 4)`).

This is the normalisation that identifies the Dirichlet symbol `ξ_w(z)` of §19 with the Jacobi
symbol `(Re(wz) | |w|²)` (19.10): it is the missing ingredient of `dirichletSym_mul`, and it is
also the reason `(z/w)(w/z) = (Re wz | |wz|²) = 1` for primary primitive `w,z` ((19.12)). -/
theorem jacobiSym_sq_add_sq {u v : ℤ} (hu : Odd u) (hv : Even v) (hcop : IsCoprime u v) :
    jacobiSym u ((u ^ 2 + v ^ 2).natAbs) = 1 := by
  have hqmod4 : (u ^ 2 + v ^ 2).natAbs % 4 = 1 := sq_add_sq_mod_four hu hv
  have hqodd : Odd ((u ^ 2 + v ^ 2).natAbs) := by
    rw [natAbs_sq_add_sq]
    exact (hu.natAbs.pow).add_even (Nat.even_pow.mpr ⟨hv.natAbs, by norm_num⟩)
  have hUodd : Odd u.natAbs := hu.natAbs
  -- The reciprocity chain `(|u|/q) = (q/|u|) = (v²/|u|) = 1`.
  have hchain : jacobiSym (u.natAbs : ℤ) ((u ^ 2 + v ^ 2).natAbs) = 1 := by
    have hrec := (jacobiSym.quadratic_reciprocity_one_mod_four
      (a := (u ^ 2 + v ^ 2).natAbs) (b := u.natAbs) hqmod4 hUodd).symm
    rw [hrec, jacobiSym.mod_left]
    have hcong : (((u ^ 2 + v ^ 2).natAbs : ℤ)) % (u.natAbs : ℤ)
        = ((v.natAbs : ℤ)) ^ 2 % (u.natAbs : ℤ) := by
      rw [natAbs_sq_add_sq]; push_cast
      rw [Int.add_emod]
      have h1 : (|u|) ^ 2 % |u| = 0 := by rw [sq]; exact Int.mul_emod_right _ _
      rw [h1, Int.zero_add, Int.emod_emod]
    rw [hcong, ← jacobiSym.mod_left]
    apply jacobiSym.sq_one'
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    have hgcd : Int.gcd u v = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    rw [Int.gcd_eq_natAbs] at hgcd
    rw [Nat.gcd_comm]; exact hgcd
  rcases Int.natAbs_eq u with h | h
  · nth_rewrite 1 [h]; exact hchain
  · nth_rewrite 1 [h]
    rw [jacobiSym.neg (u.natAbs) hqodd, ZMod.χ₄_nat_one_mod_four hqmod4, one_mul]
    exact hchain

end Work.FIArea7
