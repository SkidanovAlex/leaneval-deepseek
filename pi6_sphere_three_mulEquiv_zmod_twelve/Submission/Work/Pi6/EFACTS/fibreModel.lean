import Mathlib
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration
import Submission.Work.Stems.subsingleton_of_contractible
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `fib g3 = S³⟨3⟩`'s fibre is a model of `K(ℤ,2)`

`Work.Pi6.EFACTS.fibreModel`: if `P3` is a range model of `K(ℤ,3)` through degree `12`, then the
fibre `fib g3` of the projection `proj g3 : hofib(g3) → SphModel 3` over `∞` is a range model of
`K(ℤ,2)` through degree `11`.

The fibre is the space of paths of `P3` from `g3 s3` to `g3 (sHomeo ∞)` (`fibHomeo`), which is the
strict fibre of the path–loop fibration `evalOne P3 (g3 s3) : PathSpace P3 (g3 s3) → P3` over that
path (`fibPt g3`).  The long exact homotopy sequence of that fibration
(`Work.StemsB.fibrationLES_of_isSerreFibration`), whose total space is contractible, identifies
`π_i` of the fibre with `π_{i+1}(P3)` (`fibreLESIso`).
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.Pi6.EFACTS

open scoped Topology

/-- The `S³`-coordinate of a point of `fib g3` is `sHomeo ∞`. -/
theorem fib_coord {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3))
    (q : Work.Pi6.EFACTS.fib g3) :
    q.1.1.1 = Work.Pi6.EFACTS.sHomeo OnePoint.infty :=
  Work.Pi6.EFACTS.sHomeo.symm.injective (by
    have hp : Work.Pi6.EFACTS.sHomeo.symm q.1.1.1 = OnePoint.infty := q.2
    rw [hp, Homeomorph.symm_apply_apply])

/-- **The fibre of `proj g3` over `∞` is the strict fibre of the path–loop fibration of `P3`.**
Both are the space of paths in `P3` from `g3 s3` to `g3 (sHomeo ∞)`; the homeomorphism forgets the
`S³`-coordinate (forced to be `sHomeo ∞`) of the homotopy-fibre model. -/
noncomputable def fibHomeo {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) :
    Work.Pi6.EFACTS.fib g3 ≃ₜ
      Work.StemsB.fibre (Work.StemsB.evalOne P3 (g3 Work.Pi6.s3))
        (Work.StemsB.evalOne P3 (g3 Work.Pi6.s3) (Work.Pi6.EFACTS.fibPt g3).1.1.2) where
  toFun q := ⟨q.1.1.2, by
    have h1 : (Work.StemsB.evalOne P3 (g3 Work.Pi6.s3)) q.1.1.2 = g3 q.1.1.1 := q.1.2
    have h2 : (Work.StemsB.evalOne P3 (g3 Work.Pi6.s3)) (Work.Pi6.EFACTS.fibPt g3).1.1.2
        = g3 (Work.Pi6.EFACTS.fibPt g3).1.1.1 := (Work.Pi6.EFACTS.fibPt g3).1.2
    rw [h1, h2, fib_coord g3 q, fib_coord g3 (Work.Pi6.EFACTS.fibPt g3)]⟩
  invFun γ := ⟨⟨⟨Work.Pi6.EFACTS.sHomeo OnePoint.infty, γ.1⟩, by
    have h2 : (Work.StemsB.evalOne P3 (g3 Work.Pi6.s3)) (Work.Pi6.EFACTS.fibPt g3).1.1.2
        = g3 (Work.Pi6.EFACTS.fibPt g3).1.1.1 := (Work.Pi6.EFACTS.fibPt g3).1.2
    exact γ.2.trans (h2.trans (congrArg g3 (fib_coord g3 (Work.Pi6.EFACTS.fibPt g3))))⟩, by
    exact Homeomorph.symm_apply_apply _ _⟩
  left_inv q := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    exact (fib_coord g3 q).symm
  right_inv γ := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  continuous_invFun := Continuous.subtype_mk (by fun_prop) _

/-- **The connecting isomorphism of the path–loop fibration with contractible total space.**  For a
Serre fibration `p : E → B` with `E` contractible, the connecting map
`π_{k+2}(B, p e₀) → π_{k+1}(F, fibrePoint p e₀)` (`F = p ⁻¹' {p e₀}`) is an isomorphism, since the
two neighbouring groups `π_{k+2}(E)` and `π_{k+1}(E)` of the long exact sequence vanish. -/
theorem fibreLESIso {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) [ContractibleSpace E] (k : ℕ) :
    Nonempty (HomotopyGroup (Fin (k + 2)) B (p e₀) ≃*
      HomotopyGroup (Fin (k + 1)) (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀)) := by
  obtain ⟨d, -, hex2, hex3⟩ := Work.StemsB.fibrationLES_of_isSerreFibration p hp e₀ k
  haveI hs1 : Subsingleton (HomotopyGroup (Fin (k + 2)) E e₀) :=
    Work.Stems.subsingleton_of_contractible e₀
  haveI hs2 : Subsingleton (HomotopyGroup (Fin (k + 1)) E
      ((Work.StemsB.fibreIncl p (p e₀)) (Work.StemsB.fibrePoint p e₀))) :=
    Work.Stems.subsingleton_of_contractible _
  refine ⟨MulEquiv.ofBijective d ⟨?_, ?_⟩⟩
  · intro a b hab
    have h1 : d (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : a * b⁻¹ ∈ Set.range (Work.StemsB.πmap p (k + 1) e₀) := (hex2 (a * b⁻¹)).mp h1
    obtain ⟨z, hz⟩ := h2
    exact mul_inv_eq_one.mp (by rw [← hz, Subsingleton.elim z 1, map_one])
  · intro y
    have h1 : y ∈ Set.range d := (hex3 y).mp (Subsingleton.elim _ _)
    obtain ⟨x, hx⟩ := h1
    exact ⟨x, hx⟩

/-- The connecting isomorphism in the degree shape `π_{i+1}(B) ≃* π_i(F)` (`i ≥ 1`). -/
theorem fibreLESIso' {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) [ContractibleSpace E]
    (i : ℕ) [Nonempty (Fin i)] :
    Nonempty (HomotopyGroup (Fin (i + 1)) B (p e₀) ≃*
      HomotopyGroup (Fin i) (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀)) := by
  have hi : 1 ≤ i := by
    obtain ⟨j⟩ := (inferInstance : Nonempty (Fin i))
    have hj : (j : ℕ) < i := j.2
    omega
  obtain ⟨d⟩ := fibreLESIso p hp e₀ (i - 1)
  haveI : Nonempty (Fin (i + 1)) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin ((i - 1) + 2)) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin ((i - 1) + 1)) := ⟨⟨0, by omega⟩⟩
  refine ⟨(Work.Stems.piMulEquivOfIndexEq (X := B) (x := p e₀)
      (show i + 1 = (i - 1) + 2 by omega)).trans
    (d.trans (Work.Stems.piMulEquivOfIndexEq (X := Work.StemsB.fibre p (p e₀))
      (x := Work.StemsB.fibrePoint p e₀) (show (i - 1) + 1 = i by omega)))⟩

theorem fibreModel {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hP3 : Work.Serre.IsEMSpaceUpTo ℤ 3 (by norm_num) 12 P3 (g3 Work.Pi6.s3)) : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (Work.Pi6.EFACTS.fib g3) (Work.Pi6.EFACTS.fibPt g3) := by
  classical
  haveI : Nonempty (Fin 2) := ⟨⟨0, by norm_num⟩⟩
  let e₀ : Work.StemsB.PathSpace P3 (g3 Work.Pi6.s3) := (Work.Pi6.EFACTS.fibPt g3).1.1.2
  let p : C(Work.StemsB.PathSpace P3 (g3 Work.Pi6.s3), P3) :=
    Work.StemsB.evalOne P3 (g3 Work.Pi6.s3)
  have hp : Work.StemsB.IsSerreFibration p :=
    Work.StemsB.isSerreFibration_evalOne P3 (g3 Work.Pi6.s3)
  haveI hcontr : ContractibleSpace (Work.StemsB.PathSpace P3 (g3 Work.Pi6.s3)) :=
    Work.StemsB.contractible_pathSpace P3 (g3 Work.Pi6.s3)
  have hpcP3 : PathConnectedSpace P3 :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero (g3 Work.Pi6.s3)
      (hP3.2 0 (by norm_num) (Or.inl (by norm_num)))
  obtain ⟨γ₀⟩ : Nonempty (Path (g3 Work.Pi6.s3) (p e₀)) := hpcP3.joined _ _
  have hP3' : Work.Serre.IsEMSpaceUpTo ℤ 3 (by norm_num) 12 P3 (p e₀) :=
    Work.Stems.isEMSpaceUpTo_change_basepoint (A := ℤ) (m := 3) (N := 12) (by norm_num) γ₀ hP3
  haveI hpcF : PathConnectedSpace (Work.StemsB.fibre p (p e₀)) :=
    Work.Serre.pathConnectedSpace_fibre_of_isSerreFibration p hp (p e₀) inferInstance hpcP3
      (hP3'.2 1 (by norm_num) (Or.inr (by norm_num)))
  have hF : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11
      (Work.StemsB.fibre p (p e₀)) (Work.StemsB.fibrePoint p e₀) := by
    constructor
    · obtain ⟨d1⟩ := fibreLESIso' p hp e₀ 2
      exact ⟨d1.symm.trans hP3'.1.some⟩
    · intro i hi hc
      rcases lt_or_ge i 2 with h2 | h2
      · interval_cases i
        · exact Work.Serre.subsingleton_pi0_of_pathConnectedSpace _ _
        · obtain ⟨d⟩ := fibreLESIso' p hp e₀ 1
          haveI : Subsingleton (HomotopyGroup (Fin 2) P3 (p e₀)) :=
            hP3'.2 2 (by norm_num) (Or.inr (by norm_num))
          exact ⟨fun a b => d.symm.injective (Subsingleton.elim (d.symm a) (d.symm b))⟩
      · haveI : Nonempty (Fin i) := ⟨⟨0, by omega⟩⟩
        obtain ⟨d⟩ := fibreLESIso' p hp e₀ i
        haveI : Subsingleton (HomotopyGroup (Fin (i + 1)) P3 (p e₀)) :=
          hP3'.2 (i + 1) (by omega) (Or.inr (by omega))
        exact ⟨fun a b => d.symm.injective (Subsingleton.elim (d.symm a) (d.symm b))⟩
  have hφ : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11
      (Work.StemsB.fibre p (p e₀)) (fibHomeo g3 (Work.Pi6.EFACTS.fibPt g3)) := by
    rw [show fibHomeo g3 (Work.Pi6.EFACTS.fibPt g3)
        = Work.StemsB.fibrePoint p e₀ from Subtype.ext rfl]
    exact hF
  have hfin := Work.RatHurewicz.isEMSpaceUpTo_of_homeomorph (A := ℤ) (k := 2) (N := 11)
    (by norm_num) (fibHomeo g3).symm (fibHomeo g3 (Work.Pi6.EFACTS.fibPt g3)) hφ
  simpa only [Homeomorph.symm_apply_apply] using hfin

end Work.Pi6.EFACTS
