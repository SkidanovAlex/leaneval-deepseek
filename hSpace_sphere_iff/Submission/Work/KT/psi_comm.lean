import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.KT.Psi.Basic
import Submission.Work.KT.Psi.cubePart_idem
import Submission.Work.KT.Psi.sq2Part_isIdem
import Submission.Work.KT.PsiC.FramePerm2
import Submission.Work.PsiC.PB_comm_frame
import Submission.Work.PsiC.bridge_sq2_cube
import Submission.Work.PsiC.bridge_cube_sq2
import Submission.Work.PsiC.gamB_decomp
import Submission.Work.PsiC.cycProj_diag
import Submission.Work.PsiC.Deps_idem
import Submission.Work.PsiC.step_psi2psi3
import Submission.Work.PsiC.step_psi3psi2
import Submission.Work.PsiC.rest_cancel
import Submission.Work.PsiC.inv_gamB

/-! # `Work.KT.psi_comm` — `ψ² ψ³ = ψ³ ψ²` on `K₀` of a commutative `ℂ`-algebra

Both sides are computed on the six-fold tensor power `P = p^{⊗6}` in the frame
`IB n = (I2 n × I2 n) × I2 n` (six tensor positions grouped into three pairs), where the relevant
position permutations are the three pair swaps `sg0,sg1,sg2`, their product `sB`, the pair cycle
`cB`, the transported block cycles `uB,vB` (with `cB = uB * vB`) and the six-cycle
`gamB = cB⁻¹ * sB` with `gamB² = cB`, `gamB³ = sB`.

With `C_μ = cycProj6 γ μ` the `μ`-eigenspace projector of `gamB`:

* `ψ²ψ³` on the generator `cls p` equals `Σ_{(ε,λ)} εχ(λ) ( Tcls p (λε) - Q2cls p ε λ )`,
* `ψ³ψ²` equals `Σ_{(ε,λ)} εχ(λ) ( Tcls p (λ²ε) - Dcls p ε )`,

the `Q2`-rest terms cancel in the `λ`-pairs (conjugation by `sB`), the `D`-rest terms cancel in the
`ε`-pairs (the free `cB`-orbit), and the two leading sums agree because inverting `gamB` swaps the
`μ`-projectors for `μ = ±ω`, `μ = ±ω²`.
-/

namespace Work.KT

open Matrix

noncomputable section

open Work.KT.Psi



open Work.KT.Psi

lemma omega_pow_six : (omega : ℂ) ^ 6 = 1 := by
  rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, omega_pow_three, one_pow]

lemma neg_omega_pow_six : ((-omega : ℂ)) ^ 6 = 1 := by
  rw [neg_pow, omega_pow_six]; norm_num

lemma neg_omega_inv : ((-omega : ℂ))⁻¹ = -(omega ^ 2) := by
  rw [inv_neg, omega_inv]

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem core (hA : ∀ x y : A, x * y = y * x) (p : Mat A) (hp : p.IsIdem)
    (ψ2 ψ3 : K0 A →+ K0 A) (h2 : IsPsi2 ψ2) (h3 : IsPsi3 ψ3) :
    ψ2 (ψ3 (cls p)) = ψ3 (ψ2 (cls p)) := by
  classical
  have h1 : (cubePart (1 : ℂ) p).IsIdem := Psi.cubePart_idem hA 1 (by norm_num) hp
  have hω : (cubePart omega p).IsIdem := Psi.cubePart_idem hA omega omega_pow_three hp
  have hs1 : (sq2Part (1 : ℂ) p).IsIdem := Psi.sq2Part_isIdem A hA p hp 1 (by norm_num)
  have hsm : (sq2Part (-1 : ℂ) p).IsIdem := Psi.sq2Part_isIdem A hA p hp (-1) (by norm_num)
  have e2 : ∀ q : Mat A, q.IsIdem → psi2Cls q = cls (sq2Part 1 q) - cls (sq2Part (-1) q) := by
    intro q hq; rw [psi2Cls, if_pos hq]
  have e3 : ∀ q : Mat A, q.IsIdem → psi3Cls q = cls (cubePart 1 q) - cls (cubePart omega q) := by
    intro q hq; rw [psi3Cls, if_pos hq]
  -- the two unfolded sides
  have hL : ψ2 (ψ3 (cls p)) =
      PsiC.Tcls (A := A) p 1 - PsiC.Tcls (A := A) p (-1)
        - PsiC.Tcls (A := A) p omega + PsiC.Tcls (A := A) p (-omega) := by
    have u : ψ2 (ψ3 (cls p)) = cls (sq2Part 1 (cubePart 1 p)) - cls (sq2Part (-1) (cubePart 1 p))
        - cls (sq2Part 1 (cubePart omega p)) + cls (sq2Part (-1) (cubePart omega p)) := by
      rw [h3 p, e3 p hp, map_sub, h2 (cubePart 1 p), h2 (cubePart omega p),
        e2 (cubePart 1 p) h1, e2 (cubePart omega p) hω]
      abel
    rw [u,
      _root_.Work.PsiC.step_psi2psi3 A hA p hp 1 1 (by norm_num) (by norm_num),
      _root_.Work.PsiC.step_psi2psi3 A hA p hp (-1) 1 (by norm_num) (by norm_num),
      _root_.Work.PsiC.step_psi2psi3 A hA p hp 1 omega (by norm_num) omega_pow_three,
      _root_.Work.PsiC.step_psi2psi3 A hA p hp (-1) omega (by norm_num) omega_pow_three]
    simp only [PsiC.Q2cls, PsiC.Q2m]
    rw [_root_.Work.PsiC.rest_cancel A hA p hp 1 (by norm_num),
      _root_.Work.PsiC.rest_cancel A hA p hp omega omega_pow_three]
    simp only [mul_one, one_mul, mul_neg, neg_mul]
    abel
  have hR : ψ3 (ψ2 (cls p)) =
      PsiC.Tcls (A := A) p 1 - PsiC.Tcls (A := A) p (-1)
        - PsiC.Tcls (A := A) p (omega ^ 2) + PsiC.Tcls (A := A) p (-(omega ^ 2)) := by
    have u : ψ3 (ψ2 (cls p)) = cls (cubePart 1 (sq2Part 1 p)) - cls (cubePart 1 (sq2Part (-1) p))
        - cls (cubePart omega (sq2Part 1 p)) + cls (cubePart omega (sq2Part (-1) p)) := by
      rw [h2 p, e2 p hp, map_sub, h3 (sq2Part 1 p), h3 (sq2Part (-1) p),
        e3 (sq2Part 1 p) hs1, e3 (sq2Part (-1) p) hsm]
      abel
    rw [u,
      _root_.Work.PsiC.step_psi3psi2 A hA p hp 1 1 (by norm_num) (by norm_num),
      _root_.Work.PsiC.step_psi3psi2 A hA p hp (-1) 1 (by norm_num) (by norm_num),
      _root_.Work.PsiC.step_psi3psi2 A hA p hp 1 omega (by norm_num) omega_pow_three,
      _root_.Work.PsiC.step_psi3psi2 A hA p hp (-1) omega (by norm_num) omega_pow_three]
    simp only [PsiC.Dcls, one_pow, one_mul, mul_one, mul_neg, neg_mul]
    abel
  -- the matching of the two leading sums
  have hidem : PsiC.PB p * PsiC.PB p = PsiC.PB p := PsiC.PB_idem p hA hp
  have hPi : PsiC.PB p * (PsiC.invB p.1).permMatrix A
      = (PsiC.invB p.1).permMatrix A * PsiC.PB p := (_root_.Work.PsiC.PB_comm_frame A hA p hp).2.2.1
  have hω' : PsiC.Tcls (A := A) p omega = PsiC.Tcls (A := A) p (omega ^ 2) := by
    have h := _root_.Work.PsiC.inv_gamB A p.1 (PsiC.PB p) hidem hPi omega omega_pow_six
    rw [omega_inv] at h
    exact h
  have hmω' : PsiC.Tcls (A := A) p (-omega) = PsiC.Tcls (A := A) p (-(omega ^ 2)) := by
    have h := _root_.Work.PsiC.inv_gamB A p.1 (PsiC.PB p) hidem hPi (-omega) neg_omega_pow_six
    rw [neg_omega_inv] at h
    exact h
  rw [hL, hR, hω', hmω']

theorem psi_comm (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (ψ2 ψ3 : K0 A →+ K0 A) (h2 : IsPsi2 ψ2) (h3 : IsPsi3 ψ3) :
    ∀ x, ψ2 (ψ3 x) = ψ3 (ψ2 x) := by
  have key : ∀ p : Mat A, ψ2 (ψ3 (cls p)) = ψ3 (ψ2 (cls p)) := by
    intro p
    by_cases hp : p.IsIdem
    · exact core hA p hp ψ2 ψ3 h2 h3
    · simp [cls_zero_of_not_idem hp]
  intro x
  have hh : ψ2.comp ψ3 = ψ3.comp ψ2 := addHom_ext_cls key
  simpa using congrArg (fun f : K0 A →+ K0 A => f x) hh

end

end Work.KT
