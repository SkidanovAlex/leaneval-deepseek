import Mathlib
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst.mderiv_defs

/-!
# `Work.ZeroEstB.psi_ode`

If a matrix `Phi` of power series satisfies the first order system `qs • Phi' = As • Phi`
(entrywise), and the "coefficient vectors" `Ps k` satisfy `s • Λ(Ps k) = N • Ps k`, where `Λ` is
the coefficient-level operator of `Work.ZeroEst.Lam` (`θ = qs·d/dx` on coefficient vectors),
then the `r × m` matrix `Psi = Ps · Phi` satisfies

  `(s·qs) • Psi' = N · Psi`.

Indeed, `θ` is a derivation and `θ(Psi k j) = Σ_l ∂(Ps k l) · qs · Phi l j + Σ_l Ps k l · (qs·∂Phi l j)`,
which by `hN` (using `Λ(Ps k)_l = qs·∂(Ps k l) + Σ_i Ps k i · As i l`) and by `hPhi`
(`qs·∂Phi l j = Σ_i As l i · Phi i j`) collapses to `Σ_l N k l · Psi l j`.
-/

namespace Work.ZeroEstB

open Polynomial PowerSeries Matrix

/-- Leibniz rule for a "dot product": the derivative of `∑ l, Q l * f l`, in the form in which it
is applied to the `s`-multiple of `⟨Λ Q, f⟩`. -/
lemma deriv_dot {m : ℕ} (q : PowerSeries ℚ) (F : Fin m → Fin m → PowerSeries ℚ)
    (Q f : Fin m → PowerSeries ℚ)
    (hf : ∀ l, q * PowerSeries.derivative (R := ℚ) (f l) = ∑ i, F l i * f i) :
    q * PowerSeries.derivative (R := ℚ) (∑ l, Q l * f l)
      = ∑ l, (q * PowerSeries.derivative (R := ℚ) (Q l)) * f l
        + ∑ l, Q l * (∑ i, F l i * f i) := by
  have hterm : ∀ l, q * PowerSeries.derivative (R := ℚ) (Q l * f l)
      = (q * PowerSeries.derivative (R := ℚ) (Q l)) * f l + Q l * (∑ i, F l i * f i) := by
    intro l
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
    rw [show q * (Q l * PowerSeries.derivative (R := ℚ) (f l))
          = Q l * (q * PowerSeries.derivative (R := ℚ) (f l)) from by ring, hf l]
    ring
  rw [map_sum, Finset.mul_sum, Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_add_distrib]

/-- Exchanging the two summation indices in `∑ l, Q l * (∑ i, F l i * f i)`. -/
lemma sum_swap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ι → PowerSeries ℚ) (F : ι → κ → PowerSeries ℚ) (f : κ → PowerSeries ℚ) :
    (∑ l, Q l * (∑ i, F l i * f i)) = ∑ i, (∑ l, Q l * F l i) * f i := by
  rw [Finset.sum_congr rfl (fun l _ => Finset.mul_sum _ _ (Q l))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : (∑ x, Q x * (F x i * f i)) = ∑ x, (Q x * F x i) * f i :=
    Finset.sum_congr rfl (fun x _ => by ring)
  rw [h, ← Finset.sum_mul]

/-- The `c`-scaled version of `sum_swap`, with the factors kept in the bracketing produced by
`Finset.mul_sum`. -/
lemma sum_c_mul_swap {ι κ : Type*} [Fintype ι] [Fintype κ] (c : PowerSeries ℚ)
    (Q : ι → PowerSeries ℚ) (F : ι → κ → PowerSeries ℚ) (f : κ → PowerSeries ℚ) :
    (∑ l, c * (Q l * (∑ i, F l i * f i))) = ∑ i, (∑ l, c * (Q l * F l i)) * f i := by
  rw [Finset.sum_congr rfl (fun l _ => by rw [Finset.mul_sum, Finset.mul_sum])]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h : (∑ x, c * (Q x * (F x i * f i))) = ∑ x, (c * (Q x * F x i)) * f i :=
    Finset.sum_congr rfl (fun x _ => by ring)
  rw [h, ← Finset.sum_mul]

/-- Entrywise expansion of the coefficient-level operator `Λ` of `Work.ZeroEst.Lam`, obtained from
the definitional identity `Work.ZeroEst.Lam_coe`. -/
lemma Lam_coe_apply {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (Q : Fin m → Polynomial ℚ) (l : Fin m) :
    ((Work.ZeroEst.Lam q A Q l : Polynomial ℚ) : PowerSeries ℚ)
      = (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) ((Q l : Polynomial ℚ) : PowerSeries ℚ)
        + ∑ i, ((Q i : Polynomial ℚ) : PowerSeries ℚ) * ((A i l : Polynomial ℚ) : PowerSeries ℚ) := by
  have h := congrFun (Work.ZeroEst.Lam_coe q A Q) l
  simp only [Work.ZeroEst.LamPS] at h
  exact h.symm

theorem psi_ode {m r : ℕ} (qs : Polynomial ℚ) (As : Fin m → Fin m → Polynomial ℚ)
    (Ps : Fin r → Fin m → Polynomial ℚ) (Phi : Matrix (Fin m) (Fin m) (PowerSeries ℚ))
    (s : Polynomial ℚ) (N : Fin r → Fin r → Polynomial ℚ)
    (hPhi : ∀ i j, (qs : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (Phi i j)
      = ∑ k, ((As i k : Polynomial ℚ) : PowerSeries ℚ) * Phi k j)
    (hN : ∀ k j, (s : PowerSeries ℚ)
        * (((Work.ZeroEst.Lam qs As (Ps k)) j : Polynomial ℚ) : PowerSeries ℚ)
      = ∑ l, (((N k l : Polynomial ℚ)) : PowerSeries ℚ) * (((Ps l j : Polynomial ℚ)) : PowerSeries ℚ)) :
    ((s : PowerSeries ℚ) * (qs : PowerSeries ℚ))
        • Work.ZeroEst.mderiv (Matrix.of (fun k j => ((Ps k j : Polynomial ℚ) : PowerSeries ℚ)) * Phi)
      = Matrix.of (fun k l => ((N k l : Polynomial ℚ) : PowerSeries ℚ))
        * (Matrix.of (fun k j => ((Ps k j : Polynomial ℚ) : PowerSeries ℚ)) * Phi) := by
  have hLam : ∀ k l, (((Work.ZeroEst.Lam qs As (Ps k)) l : Polynomial ℚ) : PowerSeries ℚ)
      = (qs : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (((Ps k l : Polynomial ℚ) : PowerSeries ℚ))
        + ∑ i, (((Ps k i : Polynomial ℚ) : PowerSeries ℚ))
            * (((As i l : Polynomial ℚ) : PowerSeries ℚ)) := fun k l => Lam_coe_apply qs As (Ps k) l
  funext k j
  simp only [Work.ZeroEst.mderiv_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply,
    smul_eq_mul]
  -- Step 1: `(s·qs)·∂⟨Ps_k, Phi_·j⟩ = ⟨(s·qs)·∂Ps_k + s·Ps_k·As, Phi_·j⟩`.
  have hL : (s : PowerSeries ℚ) * (qs : PowerSeries ℚ)
        * PowerSeries.derivative (R := ℚ)
            (∑ l, (((Ps k l : Polynomial ℚ) : PowerSeries ℚ)) * Phi l j)
      = ∑ l, (s : PowerSeries ℚ)
          * ((((Work.ZeroEst.Lam qs As (Ps k)) l : Polynomial ℚ) : PowerSeries ℚ)) * Phi l j := by
    have hdd := deriv_dot (qs : PowerSeries ℚ)
      (fun l i => ((As l i : Polynomial ℚ) : PowerSeries ℚ))
      (fun l => ((Ps k l : Polynomial ℚ) : PowerSeries ℚ)) (fun l => Phi l j) (fun l => hPhi l j)
    have hsw := sum_c_mul_swap (s : PowerSeries ℚ)
      (fun l => ((Ps k l : Polynomial ℚ) : PowerSeries ℚ))
      (fun l i => ((As l i : Polynomial ℚ) : PowerSeries ℚ)) (fun l => Phi l j)
    rw [mul_assoc, hdd, mul_add, Finset.mul_sum, Finset.mul_sum, hsw, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hLam k l]
    have hcombine : (s : PowerSeries ℚ)
          * ((qs : PowerSeries ℚ)
              * PowerSeries.derivative (R := ℚ) (((Ps k l : Polynomial ℚ) : PowerSeries ℚ))
              + ∑ i, (((Ps k i : Polynomial ℚ) : PowerSeries ℚ))
                  * (((As i l : Polynomial ℚ) : PowerSeries ℚ))) * Phi l j
        = (s : PowerSeries ℚ)
            * (((qs : PowerSeries ℚ)
                * PowerSeries.derivative (R := ℚ) (((Ps k l : Polynomial ℚ) : PowerSeries ℚ)))
                * Phi l j)
          + (∑ i, (s : PowerSeries ℚ)
                * ((((Ps k i : Polynomial ℚ) : PowerSeries ℚ))
                    * (((As i l : Polynomial ℚ) : PowerSeries ℚ)))) * Phi l j := by
      have e : (s : PowerSeries ℚ)
            * (((qs : PowerSeries ℚ)
                * PowerSeries.derivative (R := ℚ) (((Ps k l : Polynomial ℚ) : PowerSeries ℚ))))
            * Phi l j
          = (s : PowerSeries ℚ)
            * (((qs : PowerSeries ℚ)
                * PowerSeries.derivative (R := ℚ) (((Ps k l : Polynomial ℚ) : PowerSeries ℚ)))
                * Phi l j) := by ring
      rw [mul_add, add_mul, Finset.mul_sum, e]
    rw [hcombine]
  -- Step 2: the right-hand side, rewritten as a sum against the same coefficient vector.
  have hR : (∑ l, (((N k l : Polynomial ℚ) : PowerSeries ℚ))
        * ∑ i, (((Ps l i : Polynomial ℚ) : PowerSeries ℚ)) * Phi i j)
      = ∑ l, (s : PowerSeries ℚ)
          * ((((Work.ZeroEst.Lam qs As (Ps k)) l : Polynomial ℚ) : PowerSeries ℚ)) * Phi l j := by
    have hsw := sum_swap (fun l => ((N k l : Polynomial ℚ) : PowerSeries ℚ))
      (fun l i => ((Ps l i : Polynomial ℚ) : PowerSeries ℚ)) (fun i => Phi i j)
    rw [hsw]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hN k i]
  rw [hL, hR]

end Work.ZeroEstB
