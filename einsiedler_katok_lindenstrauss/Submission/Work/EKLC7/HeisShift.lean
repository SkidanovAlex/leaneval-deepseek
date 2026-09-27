import Mathlib
import Submission.Work.EKLC7.HeisMul

/-!
# C7: the action of the root groups on the Heisenberg parametrisation

The element `heis hij hjk hik p q r = u_ij(p) u_jk(r) u_ik(q - pr) = 1 + p E_ij + q E_ik + r E_jk`
is written in the "first" Heisenberg coordinate system.  Multiplying it on the left or on the
right by one of the three root groups `u_ij(s)`, `u_jk(s)`, `u_ik(s)` amounts -- by the
multiplication law `Work.EKLC7.heis_mul` and the identifications
`u_ij(s) = heis s 0 0`, `u_jk(s) = heis 0 0 s`, `u_ik(s) = heis 0 s 0` (`heis_uij`,
`heis_ujk`, `heis_uik`) -- to a *linear* change of the coordinates, with the `E_ij` and `E_jk`
directions acting as unipotent shears on the central coordinate `q`.

This is the group-level input of the "two orders" comparison of the leafwise product formulae
`TripleA`/`TripleB` (Pisa 9.11): the two product formulas differ by a central translation, and
the translation is read off from the shifts recorded here.
-/

set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-- **The shifts of the Heisenberg parametrisation by the three root groups.**  Left and right
multiplication of `heis p q r` by `u_ij(s)`, `u_jk(s)`, `u_ik(s)`:

* `u_ij(s) · (p,q,r) = (s + p, q + s r, r)` and `(p,q,r) · u_ij(s) = (p + s, q, r)`;
* `u_jk(s) · (p,q,r) = (p, q, r + s)` and `(p,q,r) · u_jk(s) = (p, q + p s, r + s)`;
* `u_ik(s) · (p,q,r) = (p, q + s, r) = (p,q,r) · u_ik(s)` (centrality of `U_ik`).

The last two components say exactly that `U_ik` is central in `Heis3` while `U_ij` and `U_jk`
shear the centre: right multiplying by `u_jk(s)` adds `p s` to `q`, and left multiplying by
`u_ij(s)` adds `s r` to `q`. -/
theorem HeisShift : ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r s : ℝ),
    (Work.EKLContract.uij hij s * Work.EKLC7.heis hij hjk hik p q r
        = Work.EKLC7.heis hij hjk hik (s + p) (q + s * r) r)
      ∧ (Work.EKLC7.heis hij hjk hik p q r * Work.EKLContract.uij hij s
        = Work.EKLC7.heis hij hjk hik (p + s) q r)
      ∧ (Work.EKLContract.uij hjk s * Work.EKLC7.heis hij hjk hik p q r
        = Work.EKLC7.heis hij hjk hik p q (r + s))
      ∧ (Work.EKLC7.heis hij hjk hik p q r * Work.EKLContract.uij hjk s
        = Work.EKLC7.heis hij hjk hik p (q + p * s) (r + s))
      ∧ (Work.EKLContract.uij hik s * Work.EKLC7.heis hij hjk hik p q r
        = Work.EKLC7.heis hij hjk hik p (q + s) r)
      ∧ (Work.EKLC7.heis hij hjk hik p q r * Work.EKLContract.uij hik s
        = Work.EKLC7.heis hij hjk hik p (q + s) r) := by
  intro i j k hij hjk hik p q r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `u_ij(s) · (p,q,r) = (s+p, q+sr, r)`
    rw [← heis_uij hij hjk hik s, heis_mul hij hjk hik s 0 0 p q r]
    congr 1 <;> ring
  · -- `(p,q,r) · u_ij(s) = (p+s, q, r)`
    rw [← heis_uij hij hjk hik s, heis_mul hij hjk hik p q r s 0 0]
    congr 1 <;> ring
  · -- `u_jk(s) · (p,q,r) = (p, q, r+s)`
    rw [← heis_ujk hij hjk hik s, heis_mul hij hjk hik 0 0 s p q r]
    congr 1 <;> ring
  · -- `(p,q,r) · u_jk(s) = (p, q+ps, r+s)`
    rw [← heis_ujk hij hjk hik s, heis_mul hij hjk hik p q r 0 0 s]
    congr 1 <;> ring
  · -- centrality of `U_ik` on the left: `u_ik(s) · (p,q,r) = (p, q+s, r)`
    rw [← heis_uik hij hjk hik s, heis_mul hij hjk hik 0 s 0 p q r]
    congr 1 <;> ring
  · -- centrality of `U_ik` on the right: `(p,q,r) · u_ik(s) = (p, q+s, r)`
    rw [← heis_uik hij hjk hik s, heis_mul hij hjk hik p q r 0 s 0]
    congr 1 <;> ring

end Work.EKLC7
