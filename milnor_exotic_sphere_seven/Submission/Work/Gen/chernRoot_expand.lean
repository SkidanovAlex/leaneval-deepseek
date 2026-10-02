import Mathlib
import Submission.Work.Gen.crx.Core

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The Chern-root expansion `∏_i (t_i + x) = Σ_k e_k(t) x^{n-k}`

For a family `t : Fin n → H²(P;ℤ)` of degree-`2` cohomology classes and a class `x`, the top
elementary symmetric class of the family `i ↦ t i + x` expands as the convolution of the
elementary symmetric classes of `t` with the powers of `x`:

  `eSymC n (fun i => t i + x) n = convSeries (fun k => eSymC n t k) (zPow x) n`.

The proof is an induction on `n` which uses, at each step, the recursion of `eSymC`
(`Work.Gen.eSymC_succ_top`, mirrored by `Work.Gen.eSymC_eq_shiftSeries`), the recursion of the
convolution with `zPow x` (`Work.Gen.convSeries_zPow_succ`) and the shift rule
(`Work.Gen.convSeries_shiftSeries`), together with the commutativity of the graded product.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The Chern-root expansion**, auxiliary form: the statement with `x` fixed, by induction on the
number of variables. -/
theorem chernRoot_expand_aux {P : Type} [TopologicalSpace P] (x : Coh ℤ 2 P) :
    ∀ (n : ℕ) (t : Fin n → Coh ℤ 2 P),
      Work.Gen.eSymC (P := P) n (fun i => t i + x) n
        = Work.LerayHirsch.convSeries (fun k => Work.Gen.eSymC (P := P) n t k)
            (Work.Whitney.ChernRel.zPow x) n := by
  intro n
  induction n with
  | zero =>
      intro t
      rw [Work.Gen.eSymC_zero_index (P := P) (fun i => t i + x),
        Work.Gen.convSeries_zero (fun k => Work.Gen.eSymC (P := P) 0 t k)
          (Work.Whitney.ChernRel.zPow x) (Work.Whitney.ChernRel.zPow_zero x),
        Work.Gen.eSymC_zero_index (P := P) t]
  | succ n ih =>
      intro t
      rw [Work.Gen.eSymC_succ_top]
      rw [Work.Gen.eSymC_above (k := n + 1) (fun i => t (Fin.castSucc i) + x)
        (by omega : n < n + 1), zero_add]
      rw [ih (fun i => t (Fin.castSucc i))]
      rw [Work.Gen.eSymC_eq_shiftSeries t,
        Work.Gen.convSeries_shiftSeries
          (fun k => Work.Gen.eSymC (P := P) n (fun i => t (Fin.castSucc i)) k)
          (t (Fin.last n)) x n,
        Work.Gen.convSeries_zPow_succ
          (fun k => Work.Gen.eSymC (P := P) n (fun i => t (Fin.castSucc i)) k) x n,
        Work.Gen.eSymC_above (k := n + 1) (fun i => t (Fin.castSucc i)) (by omega : n < n + 1)]
      rw [Work.Whitney.ChernRel.cupChern_add_left, Work.Whitney.ChernRel.cohTransport_add]
      rw [← Work.Whitney.ChernRel.cupChern_comm n 1
        (Work.LerayHirsch.convSeries
          (fun k => Work.Gen.eSymC (P := P) n (fun i => t (Fin.castSucc i)) k)
          (Work.Whitney.ChernRel.zPow x) n) x]
      abel

theorem chernRoot_expand {P : Type} [TopologicalSpace P] {n : ℕ}
    (t : Fin n → Work.Thom.Coh ℤ 2 P) (x : Work.Thom.Coh ℤ 2 P) :
    Work.Gen.eSymC (P := P) n (fun i => t i + x) n
      = Work.LerayHirsch.convSeries (fun k => Work.Gen.eSymC (P := P) n t k)
          (Work.Whitney.ChernRel.zPow x) n :=
  chernRoot_expand_aux x n t

end

end Work.Gen
