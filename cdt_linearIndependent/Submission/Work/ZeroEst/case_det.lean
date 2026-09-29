import Mathlib
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst.case_det_cramer
import Submission.Work.ZeroEst.case_det_detdeg
import Submission.Work.ZeroEst.case_det_detne
import Submission.Work.ZeroEst.case_det_order_iter
import Submission.Work.ZeroEst.case_det_order_sum
import Submission.Work.ZeroEst.case_det_orbit_dot

/-!
# Area Z, case `det`: Shidlovsky's lemma when the `θ`-orbit of `P` is independent

This file proves `Work.ZeroEst.case_det`, the determinant case of the one-variable Shidlovsky
bound of area Z (see `Submission/Work/ZeroEst/defs.lean` and `one_var.lean`).

Setting: `f₁,…,f_m ∈ ℚ⟦x⟧` is `ℚ(x)`-independent, closed under `θ = q·d/dx`
(`q fᵢ' = Σⱼ Aᵢⱼ fⱼ`), `P = (P₁,…,P_m)` is a vector of polynomials with `deg Pᵢ < D`, and
`R = Σᵢ Pᵢ fᵢ ≠ 0`.  Write `Λ Q = q·Q' + Q·Aᵗ` for the coefficient-level operator realising `θ`
on combinations (`Lam`), `Q_k = Λᵏ P` (`orbit`) and `F_k = ⟨Q_k, f⟩ = θᵏ R`.

The hypothesis `hind` says that `Q_0,…,Q_{m-1}` are linearly independent over `ℚ(x)`.  Under this
hypothesis `Δ := det(Q_k j)` is a *nonzero* polynomial (`case_det_detne`), Cramer's rule
(`case_det_cramer`) writes `Δ·f_j = Σ_k c_{k,j} F_k` with polynomial cofactors `c_{k,j}`, and
`ord F_k ≥ ord R - k` (`case_det_order_iter`), so for any `j`

`ord R ≤ ord(Δ·f_j) + (m-1) = ord Δ + ord f_j + (m-1) ≤ deg Δ + ord f_j + (m-1)`.

The degree of `Δ` is bounded by `m·(D + m·dlt q A)` (`case_det_detdeg`, with `dlt q A` the
per-step degree growth of `Λ`), and `ord f_j ≤ supᵢ ord fᵢ`, which is the claimed bound.
-/

namespace Work.ZeroEst

open Polynomial PowerSeries

/-- The order of a nonzero polynomial, viewed as a power series, is at most its `natDegree`. -/
lemma order_coe_toNat_le (p : Polynomial ℚ) (hp : p ≠ 0) :
    (p : PowerSeries ℚ).order ≤ (p.natDegree : ℕ∞) := by
  refine PowerSeries.order_le p.natDegree ?_
  rw [Polynomial.coeff_coe, Polynomial.coeff_natDegree]
  exact Polynomial.leadingCoeff_ne_zero.mpr hp

theorem case_det (m : ℕ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (f : Fin m → PowerSeries ℚ) (hpi : Submission.CDTPlan.PolyIndependent f)
    (hrel : ∀ i, (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) (f i)
      = ∑ j, (A i j : PowerSeries ℚ) * f j)
    (P : Fin m → Polynomial ℚ) (D : ℕ) (hP : Work.ZeroEst.DegLT P D)
    (hR : (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0)
    (hind : LinearIndependent (RatFunc ℚ)
      (fun k : Fin m => (fun i => ((Work.ZeroEst.orbit q A P k) i : RatFunc ℚ)))) :
    (∑ i, (P i : PowerSeries ℚ) * f i).order ≤
      ((m * D + (m * Work.ZeroEst.dlt q A * m + m
        + Finset.univ.sup (fun i => (f i).order.toNat)) : ℕ) : ℕ∞) := by
  classical
  set R : PowerSeries ℚ := ∑ i, (P i : PowerSeries ℚ) * f i with hRdef
  have hRne : R ≠ 0 := hR
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: the sum `R` is empty, contradicting `hR`
    subst hm
    exact absurd (by rw [hRdef]; simp) hRne
  · -- `D = 0` would force `P = 0` and hence `R = 0`
    have hD1 : 1 ≤ D := by
      by_contra hlt
      have hD0 : D = 0 := by omega
      subst hD0
      have hPz : ∀ i, P i = 0 := fun i => Polynomial.ext fun k => hP i k (Nat.zero_le k)
      exact hRne (by rw [hRdef]; simp [hPz])
    let j₀ : Fin m := ⟨0, hm⟩
    -- the matrix of `Λ`-orbits, whose determinant is the common denominator
    set M : Matrix (Fin m) (Fin m) (Polynomial ℚ) := fun k j => Work.ZeroEst.orbit q A P k j
      with hM
    have hdet_ne : M.det ≠ 0 := case_det_detne M (by simpa [hM] using hind)
    -- degree bookkeeping: every entry of `M` has `natDegree ≤ D + m * dlt q A`
    have hN : ∀ k j, (M k j).natDegree ≤ D + m * Work.ZeroEst.dlt q A := by
      intro k j
      have hk : Work.ZeroEst.DegLT (Work.ZeroEst.orbit q A P k)
          (D + k * Work.ZeroEst.dlt q A) := Work.ZeroEst.orbit_DegLT q A P D hD1 hP k
      have hdeg := (Work.ZeroEst.DegLT_iff_degree _ _).mp hk j
      have hle : D + k * Work.ZeroEst.dlt q A ≤ D + m * Work.ZeroEst.dlt q A := by
        have hkm : (k : ℕ) ≤ m := le_of_lt k.isLt
        have := Nat.mul_le_mul_right (Work.ZeroEst.dlt q A) hkm
        omega
      simp only [hM]
      exact Polynomial.natDegree_le_iff_degree_le.mpr
        (le_of_lt (lt_of_lt_of_le hdeg (by exact_mod_cast hle)))
    have hdetsz : M.det.natDegree ≤ m * (D + m * Work.ZeroEst.dlt q A) :=
      case_det_detdeg M (D + m * Work.ZeroEst.dlt q A) hN
    have hordΔ : (M.det : PowerSeries ℚ).order ≤ ((M.det.natDegree : ℕ) : ℕ∞) :=
      order_coe_toNat_le M.det hdet_ne
    -- `f j₀ ≠ 0`, and its order is bounded by the sup of the orders of the `f i`
    have hfj : f j₀ ≠ 0 := by
      intro hz
      let P' : Fin m → Polynomial ℚ := fun i => if i = j₀ then 1 else 0
      have hcomb : (∑ i, (P' i : PowerSeries ℚ) * f i) = 0 := by
        rw [Finset.sum_eq_single j₀]
        · simp [P', hz]
        · intro b _ hb
          simp [P', hb]
        · intro hmem
          exact absurd (Finset.mem_univ j₀) hmem
      have hthis := hpi P' hcomb j₀
      simp [P'] at hthis
    have hfjsup : (f j₀).order ≤ ((Finset.univ.sup (fun i => (f i).order.toNat) : ℕ) : ℕ∞) := by
      rw [← PowerSeries.coe_toNat_order hfj]
      exact_mod_cast Finset.le_sup (s := Finset.univ) (f := fun i => (f i).order.toNat)
        (Finset.mem_univ j₀)
    have hcramer := case_det_cramer M f j₀
    -- `F k = ⟨Q k, f⟩ = θᵏ R`
    have hFtheta : ∀ k : Fin m, (∑ j', (M k j' : PowerSeries ℚ) * f j')
        = ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k : ℕ)]) R := by
      intro k
      have h := case_det_orbit_dot m q A f hrel P (k : ℕ)
      rw [hRdef]
      simpa [hM] using h
    -- Cramer + `ord F k ≥ ord R - k`: `ord R - (m-1) ≤ ord (Δ * f j₀)`
    have hkey : ((R.order.toNat - (m - 1) : ℕ) : ℕ∞) ≤ ((M.det : PowerSeries ℚ) * f j₀).order := by
      rw [hcramer]
      refine case_det_order_sum Finset.univ
        (fun k : Fin m => (M.adjugate j₀ k : PowerSeries ℚ)
          * (∑ j', (M k j' : PowerSeries ℚ) * f j'))
        (((R.order.toNat - (m - 1) : ℕ)) : ℕ∞) ?_
      intro k _
      have h1 : ((R.order.toNat - (m - 1) : ℕ) : ℕ∞) ≤ ((R.order.toNat - (k : ℕ) : ℕ) : ℕ∞) :=
        ENat.natCast_le_natCast.mpr (Nat.sub_le_sub_left (by omega : (k : ℕ) ≤ m - 1) _)
      have h2 := case_det_order_iter q R (k : ℕ)
      have h3 : ((fun S => (q : PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) S)^[(k : ℕ)] R).order
          = (∑ j', (M k j' : PowerSeries ℚ) * f j').order := by rw [hFtheta k]
      have h4 : (∑ j', (M k j' : PowerSeries ℚ) * f j').order
          ≤ ((M.adjugate j₀ k : PowerSeries ℚ)
              * (∑ j', (M k j' : PowerSeries ℚ) * f j')).order := by
        refine le_trans (le_add_left (b := (M.adjugate j₀ k : PowerSeries ℚ).order) le_rfl) ?_
        exact PowerSeries.le_order_mul _ _
      exact le_trans (le_trans h1 (le_trans h2 (le_of_eq h3))) h4
    -- `ord (Δ * f j₀) = ord Δ + ord f j₀` and `ord Δ ≤ natDegree Δ`
    have hstep2 : ((R.order.toNat - (m - 1) : ℕ) : ℕ∞) ≤
        ((M.det.natDegree + Finset.univ.sup (fun i => (f i).order.toNat) : ℕ) : ℕ∞) := by
      refine hkey.trans ?_
      rw [PowerSeries.order_mul]
      calc (M.det : PowerSeries ℚ).order + (f j₀).order
          ≤ ((M.det.natDegree : ℕ) : ℕ∞)
              + ((Finset.univ.sup (fun i => (f i).order.toNat) : ℕ) : ℕ∞) :=
            add_le_add hordΔ hfjsup
        _ = ((M.det.natDegree + Finset.univ.sup (fun i => (f i).order.toNat) : ℕ) : ℕ∞) := by
            push_cast; ring
    have hnat : R.order.toNat - (m - 1) ≤
        M.det.natDegree + Finset.univ.sup (fun i => (f i).order.toNat) :=
      ENat.natCast_le_natCast.mp hstep2
    have harith : m * (D + m * Work.ZeroEst.dlt q A)
          + Finset.univ.sup (fun i => (f i).order.toNat) + (m - 1)
        ≤ m * D + (m * Work.ZeroEst.dlt q A * m + m
            + Finset.univ.sup (fun i => (f i).order.toNat)) := by
      have h1 : m * (D + m * Work.ZeroEst.dlt q A)
          = m * D + m * (m * Work.ZeroEst.dlt q A) := Nat.mul_add m D (m * Work.ZeroEst.dlt q A)
      have h2 : m * (m * Work.ZeroEst.dlt q A) = m * Work.ZeroEst.dlt q A * m := by ring
      rw [h1, h2]
      omega
    rw [← PowerSeries.coe_toNat_order hRne]
    refine ENat.natCast_le_natCast.mpr ?_
    omega

end Work.ZeroEst
