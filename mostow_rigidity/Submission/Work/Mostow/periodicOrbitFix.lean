import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.BaryBase

/-!
# `periodicOrbitFix`: a periodic orbit of an isometry of `ℍⁿ` forces a fixed point

If `g ^ m` (`m > 0`) fixes a point `u` of `ℍⁿ`, then `g` itself fixes a point of `ℍⁿ`.

The argument is elementary and lives entirely in the linear model `u ↦ hlift u = (u, √(1+‖u‖²))`
of the hyperboloid.  Let `G = poEffMat g = tsign (rep g) • mat (rep g)`, the representative of
the class of `Quotient.out g` acting on the hyperboloid the way `g` does:
`G *ᵥ hlift w = hlift (g • w)` (`poEffMat_mulVec_hlift`).  Because `(g ^ m) • u = u`, the finite
orbit sum `z = Σ_{k<m} hlift ((g ^ k) • u)` satisfies `G *ᵥ z = z` -- the sum telescopes, the
first and last term coinciding.  Now each term `hlift w = (w, √(1+‖w‖²))` is a *future-directed*
unit timelike vector (`‖w‖ < tpart w`), and the future light cone is convex, so `z` is future
timelike: writing `z = (W, T)` with `W = Σ_k (g ^ k) • u` and `T = Σ_k tpart ((g ^ k) • u)` we
have `‖W‖ ≤ Σ_k ‖(g ^ k) • u‖ < Σ_k tpart ((g ^ k) • u) = T`.  Normalising,
`c⁻¹ • z` (with `c = √(T² - ‖W‖²) > 0`) is again the lift of a point of `ℍⁿ`,
`b = spat (c⁻¹ • z)`, and since `G *ᵥ z = z` we get
`hlift (g • b) = G *ᵥ hlift b = c⁻¹ • (G *ᵥ z) = c⁻¹ • z = hlift b`, whence `g • b = b`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-- The *effective matrix* of `g ∈ PO(n,1)`:
`tsign (rep g) • mat (rep g)`, the representative of the class of `rep g` whose time–time entry
is positive, i.e. the one that acts on the hyperboloid lift of `ℍⁿ` as `g` acts. -/
def poEffMat (g : PO n 1) : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  tsign (rep g) • mat (rep g)

/-- The effective matrix moves the hyperboloid lift of `w` to the lift of `g • w`. -/
lemma poEffMat_mulVec_hlift (g : PO n 1) (w : E n) :
    (poEffMat g).mulVec (hlift w) = hlift (g • w) := by
  rw [poEffMat, Matrix.smul_mulVec]
  exact (Hyper.hlift_actO (rep g) w).symm

/-- A point of the hyperboloid is future timelike: `‖w‖ < tpart w = √(1+‖w‖²)`. -/
lemma norm_lt_tpart_of_chart (w : E n) : ‖w‖ < tpart w := by
  rw [tpart, Real.lt_sqrt (norm_nonneg w)]
  nlinarith

/-- A one-term shift of an `m`-periodic sum leaves the sum unchanged. -/
lemma sum_range_shift_of_periodic {M : Type*} [AddCommGroup M] {m : ℕ} {a : ℕ → M}
    (h : a m = a 0) : (∑ k ∈ Finset.range m, a (k + 1)) = ∑ k ∈ Finset.range m, a k := by
  have h1 := Finset.sum_range_succ' a m
  have h2 := Finset.sum_range_succ a m
  rw [h] at h2
  exact add_right_cancel (h1.symm.trans h2)

theorem periodicOrbitFix (n : ℕ) (hA : Submission.Mostow.POActionProp n) (g : LeanEval.Geometry.MostowRigidity.PO n 1) (m : ℕ) (hm : 0 < m) (u : Submission.Mostow.E n) (hfix : (g ^ m) • u = u) : ∃ b : Submission.Mostow.E n, g • b = b := by
  have hmul : ∀ (a b : PO n 1) (x : E n), (a * b) • x = a • (b • x) := hA.2.2.2.2.1
  have hone : ∀ x : E n, (1 : PO n 1) • x = x := hA.2.2.2.1
  -- the lifted orbit sum is fixed by the effective matrix
  set z : Fin n ⊕ Fin 1 → ℝ := ∑ k ∈ Finset.range m, hlift ((g ^ k) • u) with hz
  have hzfix : (poEffMat g).mulVec z = z := by
    rw [hz, Matrix.mulVec_sum]
    rw [show (∑ k ∈ Finset.range m, (poEffMat g).mulVec (hlift ((g ^ k) • u)))
        = ∑ k ∈ Finset.range m, hlift ((g ^ (k + 1)) • u) from
      Finset.sum_congr rfl (fun k _ => by rw [poEffMat_mulVec_hlift, pow_succ', hmul])]
    exact sum_range_shift_of_periodic (a := fun k => hlift ((g ^ k) • u))
      (by rw [pow_zero, hone, hfix])
  -- its spatial and time coordinates
  set W : E n := ∑ k ∈ Finset.range m, ((g ^ k) • u) with hW
  set T : ℝ := ∑ k ∈ Finset.range m, tpart ((g ^ k) • u) with hT
  have hzW : ∀ i : Fin n, z (Sum.inl i) = W i := by
    intro i
    rw [hz, hW]
    simp [Finset.sum_apply, hlift_inl]
  have hzT : z (Sum.inr 0) = T := by
    rw [hz, hT]
    simp [Finset.sum_apply, hlift_inr]
  have hTpos : 0 < T := by
    rw [hT]
    exact Finset.sum_pos' (fun k _ => (tpart_pos _).le)
      ⟨0, Finset.mem_range.mpr hm, tpart_pos _⟩
  -- the sum is future timelike
  have hWT : ‖W‖ < T := by
    rw [hW, hT]
    calc ‖∑ k ∈ Finset.range m, ((g ^ k) • u)‖
        ≤ ∑ k ∈ Finset.range m, ‖((g ^ k) • u)‖ := norm_sum_le _ _
      _ < ∑ k ∈ Finset.range m, tpart ((g ^ k) • u) :=
          Finset.sum_lt_sum (fun k _ => (norm_lt_tpart_of_chart _).le)
            ⟨0, Finset.mem_range.mpr hm, norm_lt_tpart_of_chart _⟩
  have hz_mink : Hyper.mink z z = ‖W‖ ^ 2 - T ^ 2 := by
    rw [Hyper.mink_apply, Hyper.norm_sq_eq_sum W]
    simp only [hzW, hzT, pow_two]
  -- normalise to a unit timelike vector
  set c : ℝ := Real.sqrt (T ^ 2 - ‖W‖ ^ 2) with hc
  have hcsq : c ^ 2 = T ^ 2 - ‖W‖ ^ 2 := by
    rw [hc, Real.sq_sqrt (by nlinarith [norm_nonneg W, hWT])]
  have hcpos : 0 < c := by
    rw [hc, Real.sqrt_pos]
    nlinarith [norm_nonneg W, hWT]
  have hzc : Hyper.mink (c⁻¹ • z) (c⁻¹ • z) = -1 := by
    rw [Hyper.mink_smul, hz_mink]
    have hne : T ^ 2 - ‖W‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg W, hWT]
    rw [← _root_.mul_inv_rev, ← pow_two, hcsq,
      show ‖W‖ ^ 2 - T ^ 2 = -(T ^ 2 - ‖W‖ ^ 2) by ring, mul_neg, inv_mul_cancel₀ hne]
  have hzpos : 0 < (c⁻¹ • z) (Sum.inr 0) := by
    rw [Pi.smul_apply, smul_eq_mul, hzT]
    exact mul_pos (inv_pos.mpr hcpos) hTpos
  have hblift : hlift (Hyper.spat (c⁻¹ • z)) = c⁻¹ • z :=
    Hyper.hlift_spat_of_mink (c⁻¹ • z) hzc hzpos
  refine ⟨Hyper.spat (c⁻¹ • z), ?_⟩
  apply hlift_injective
  calc hlift (g • Hyper.spat (c⁻¹ • z))
      = (poEffMat g).mulVec (hlift (Hyper.spat (c⁻¹ • z))) :=
        (poEffMat_mulVec_hlift g _).symm
    _ = (poEffMat g).mulVec (c⁻¹ • z) := by rw [hblift]
    _ = c⁻¹ • ((poEffMat g).mulVec z) := by rw [Matrix.mulVec_smul]
    _ = c⁻¹ • z := by rw [hzfix]
    _ = hlift (Hyper.spat (c⁻¹ • z)) := hblift.symm

end

end Work.Mostow
