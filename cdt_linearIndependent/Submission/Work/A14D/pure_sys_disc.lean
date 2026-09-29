import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.ppc_aux
import Submission.Work.Pure.pure_facts
import Submission.Work.A14D.PureSysDefs
import Submission.Work.A14D.PolyGrowth
import Submission.Work.C17I.evp_sum
import Submission.Work.CPull.evp_sympPhi
import Submission.Work.A14D.pure_dclosed_spec
import Submission.Work.A14D.evp_poly_subst_sympY
import Submission.Work.A14D.evp_deriv_sympY

/-!
# Area A14D — the pure system on the disc

`pure_sys_disc` is the substitution-evaluated form of the `D`-closure
`dq · B_k' = Σ_m dA k m · B_m` of the seven pure functions `B₁,…,B₇` along the symmetrisation
coordinate `y = x²/(x−1) = Submission.CDT.sympY`.

Writing `S_k = B_k ∘ y` and recalling `(B_k ∘ y)' = (B_k' ∘ y) · y'`, the formal identity
`dq(y) · (B_k' ∘ y) = Σ_m dA_{km}(y) · (B_m ∘ y)` becomes, after multiplication by `y'`,

`dq(y) · (B_k ∘ y)' = y' · Σ_m dA_{km}(y) · (B_m ∘ y)`,

which is the statement below: `evp` sends the polynomials `dq, dA k m ∈ ℚ[X]` to
`pAtY dq = dq(y(z))`, `pAtY (dA k m) = dA_{km}(y(z))`, sends substitution along `y` and `d/dX`,
and is multiplicative.
-/

open scoped BigOperators

namespace Work.A14D

open PowerSeries

/-- Polynomial growth of the substituted pure series `B_k ∘ y`. -/
theorem polyGrowth_Sk (k : Fin 7) : PolyGrowth (Sk k) := by
  obtain ⟨C, hC, kk, hb⟩ := pureB_subst_poly_growth k
  exact ⟨C, hC, kk, hb⟩

/-- Polynomial growth of `dq ∘ y`. -/
theorem polyGrowth_DQ : PolyGrowth DQ :=
  polyGrowth_poly_subst_sympY Work.Pure.dq

/-- Polynomial growth of `dA k m ∘ y`. -/
theorem polyGrowth_DA (k m : Fin 7) : PolyGrowth (DA k m) :=
  polyGrowth_poly_subst_sympY (Work.Pure.dA k m)

/-- Polynomial growth of `y' = d/dX (x²/(x−1))`. -/
theorem polyGrowth_SYd : PolyGrowth SYd :=
  polyGrowth_derivative polyGrowth_sympY

/-- The chain rule for the substituted pure series: `(B_k ∘ y)' = (B_k' ∘ y) · y'`. -/
theorem derivative_Sk (k : Fin 7) :
    PowerSeries.derivative (R := ℚ) ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY)
      = ((PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.pureB k)).subst Submission.CDT.sympY)
          * (PowerSeries.derivative (R := ℚ) Submission.CDT.sympY) :=
  PowerSeries.derivative_subst (R := ℚ) (f := Submission.CDTPlan.pureB k)
    (g := Submission.CDT.sympY) Submission.CDT.sympY_hasSubst

/-- The substituted `D`-closure: applying `X ↦ y` to `dq · B_k' = Σ_m dA k m · B_m`. -/
theorem dclosed_sympY (k : Fin 7) :
    ((Work.Pure.dq : PowerSeries ℚ).subst Submission.CDT.sympY)
        * ((PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.pureB k)).subst Submission.CDT.sympY)
      = ∑ m : Fin 7, ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
          * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) := by
  have h := Work.A14D.pure_dclosed_spec k
  have h2 := congrArg (PowerSeries.subst Submission.CDT.sympY) h
  simpa only [PowerSeries.subst_mul Submission.CDT.sympY_hasSubst, subst_finset_sum] using h2

/-- The series-level identity `dq(y) · (B_k ∘ y)' = y' · Σ_m dA_{km}(y) · (B_m ∘ y)`. -/
theorem system_series (k : Fin 7) :
    ((Work.Pure.dq : PowerSeries ℚ).subst Submission.CDT.sympY)
        * PowerSeries.derivative (R := ℚ) ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY)
      = (PowerSeries.derivative (R := ℚ) Submission.CDT.sympY)
        * ∑ m : Fin 7, ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
            * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) := by
  rw [derivative_Sk k, ← mul_assoc, dclosed_sympY k]
  exact mul_comm _ _

theorem pure_sys_disc (k : Fin 7) {z : ℂ} (hz : ‖z‖ < 1) :
    Work.A14D.pAtY Work.Pure.dq z * deriv (fun w => Work.CPull.evp
        ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY) w) z
      = Work.A14D.dyC z * ∑ m : Fin 7, Work.A14D.pAtY (Work.Pure.dA k m) z * Work.CPull.evp
          ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) z := by
  -- left-hand side, evaluated
  have hL : Work.A14D.pAtY Work.Pure.dq z * deriv (fun w => Work.CPull.evp
        ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY) w) z
      = Work.CPull.evp (((Work.Pure.dq : PowerSeries ℚ).subst Submission.CDT.sympY)
          * PowerSeries.derivative (R := ℚ)
              ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY)) z := by
    have h1 : Work.A14D.pAtY Work.Pure.dq z
        = Work.CPull.evp ((Work.Pure.dq : PowerSeries ℚ).subst Submission.CDT.sympY) z :=
      (Work.A14D.evp_poly_subst_sympY Work.Pure.dq hz).symm
    have h2 : deriv (fun w => Work.CPull.evp
          ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY) w) z
        = Work.CPull.evp (PowerSeries.derivative (R := ℚ)
            ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY)) z := by
      obtain ⟨C, hC, kk, hb⟩ := pureB_subst_poly_growth k
      exact (evp_deriv hC hb hz).symm
    have h3 : Work.CPull.evp (((Work.Pure.dq : PowerSeries ℚ).subst Submission.CDT.sympY)
          * PowerSeries.derivative (R := ℚ)
              ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY)) z
        = Work.CPull.evp ((Work.Pure.dq : PowerSeries ℚ).subst Submission.CDT.sympY) z
          * Work.CPull.evp (PowerSeries.derivative (R := ℚ)
              ((Submission.CDTPlan.pureB k).subst Submission.CDT.sympY)) z :=
      (Work.CPull.evpMul _ _ z
        (summable_norm_of_polyGrowth (polyGrowth_poly_subst_sympY Work.Pure.dq) hz)
        (summable_norm_of_polyGrowth (polyGrowth_derivative (polyGrowth_Sk k)) hz)).2.2.2
    rw [h1, h2, ← h3]
  -- right-hand side, evaluated
  have hR : Work.A14D.dyC z * ∑ m : Fin 7, Work.A14D.pAtY (Work.Pure.dA k m) z * Work.CPull.evp
          ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) z
      = Work.CPull.evp ((PowerSeries.derivative (R := ℚ) Submission.CDT.sympY)
          * ∑ m : Fin 7, ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
              * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z := by
    have hdy : Work.A14D.dyC z = Work.CPull.evp (PowerSeries.derivative (R := ℚ) Submission.CDT.sympY) z :=
      (Work.A14D.evp_deriv_sympY hz).symm
    have hterm : ∀ m : Fin 7, Work.A14D.pAtY (Work.Pure.dA k m) z * Work.CPull.evp
          ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) z
        = Work.CPull.evp (((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
            * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z := by
      intro m
      have hp : Work.A14D.pAtY (Work.Pure.dA k m) z
          = Work.CPull.evp ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY) z :=
        (Work.A14D.evp_poly_subst_sympY (Work.Pure.dA k m) hz).symm
      have he : Work.CPull.evp (((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
            * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z
          = Work.CPull.evp ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY) z
            * Work.CPull.evp ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) z :=
        (Work.CPull.evpMul _ _ z
          (summable_norm_of_polyGrowth (polyGrowth_poly_subst_sympY (Work.Pure.dA k m)) hz)
          (summable_norm_of_polyGrowth (polyGrowth_Sk m) hz)).2.2.2
      rw [hp, ← he]
    have hsum2 : (∑ m : Fin 7, Work.A14D.pAtY (Work.Pure.dA k m) z * Work.CPull.evp
            ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY) z)
        = ∑ m : Fin 7, Work.CPull.evp
            (((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
              * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z :=
      Finset.sum_congr rfl (fun m _ => hterm m)
    have hsum : Work.CPull.evp (∑ m : Fin 7,
            ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
              * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z
        = ∑ m : Fin 7, Work.CPull.evp
            (((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
              * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z :=
      Work.C17I.evp_sum Finset.univ (fun m : Fin 7 =>
          ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
            * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z
        (fun m _ => summable_of_polyGrowth
          (polyGrowth_mul (polyGrowth_poly_subst_sympY (Work.Pure.dA k m)) (polyGrowth_Sk m)) hz)
    have hsv : Work.CPull.evp ((PowerSeries.derivative (R := ℚ) Submission.CDT.sympY)
          * ∑ m : Fin 7, ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
              * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z
        = Work.CPull.evp (PowerSeries.derivative (R := ℚ) Submission.CDT.sympY) z
          * Work.CPull.evp (∑ m : Fin 7,
              ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
                * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY)) z :=
      (Work.CPull.evpMul _ _ z
        (summable_norm_of_polyGrowth polyGrowth_SYd hz)
        (summable_norm_of_polyGrowth (polyGrowth_finset_sum Finset.univ
          (fun m : Fin 7 => ((Work.Pure.dA k m : PowerSeries ℚ).subst Submission.CDT.sympY)
            * ((Submission.CDTPlan.pureB m).subst Submission.CDT.sympY))
          (fun m _ => polyGrowth_mul (polyGrowth_poly_subst_sympY (Work.Pure.dA k m))
            (polyGrowth_Sk m))) hz)).2.2.2
    rw [hdy, hsum2, ← hsum, ← hsv]
  rw [hL, hR, system_series k]

end Work.A14D
