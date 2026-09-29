import Submission.CDT.FinalLinear

/-!
# From the paper's relation `(todiff)` to the paper's system

In the proof of Lemma `14functions` of Calegari–Dimitrov–Tang (arXiv:2408.15403) one is
led, for `Δ` a solution of the order-`4` ODE
`Σ_{i≤4} cᵢ Δ^{(i)} = 0` of the paper's display `(explicitode)`, to a relation
`(todiff)`

`a₀ ∫Δ + a₋₁ ∫Δ/y + a₋₂ ∫Δ/y² = b₀Δ + b₁Δ' + b₂Δ'' + b₃Δ'''`

with `a₀,a₋₁,a₋₂ ∈ ℂ` constants, and the claim is that this forces the rational functions
`b₀,…,b₃` to satisfy the paper's *system*

`b₃' + b₂ − (c₃/c₄)b₃ = 0`, `b₂' + b₁ − (c₂/c₄)b₃ = 0`, `b₁' + b₀ − (c₁/c₄)b₃ = 0`,
`b₀' − (c₀/c₄)b₃ = a₀ + a₋₁/y + a₋₂/y²`

of four first-order equations.  This module formalizes that step in the abstract setting of a
*module with a derivation* over `𝔽 = ℂ(y)`:  `M` is an `𝔽`-module, `δ : M → M` satisfies
`δ (r • m) = r' • m + r • δ m` (`r' = dRat r`) and `δ (x + y) = δ x + δ y`, and the
`u i = Δ^{(i)}` (`i ≤ 3`), `v j = ∫Δ/y^j` are elements of `M` with

* `δ (u 0) = u 1`, `δ (u 1) = u 2`, `δ (u 2) = u 3`,
  `δ (u 3) = −(Zz • u₀ + Uu • u₁ + Vv • u₂ + Ww • u₃)` (the ODE, with `Uu,Vv,Ww,Zz` the
  `c₁/c₄,…,c₀/c₄` of the paper),
* `δ (v 0) = u 0`, `δ (v 1) = y⁻¹ • u 0`, `δ (v 2) = y⁻² • u 0`.

`hindep` is the statement that `Δ,Δ',Δ'',Δ'''` are `𝔽`-linearly independent, which in the
paper comes from the irreducibility of the order-`4` operator (the monodromy argument).

The main results of this module are `system_of_relation` (the paper's step) and, in the
sequel, the reduction of a general relation to constant coefficients and the final
contradiction via `no_solution`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open Classical

noncomputable section

namespace Submission.CDT
namespace RelSystem

open Polynomial
open Submission.CDT.Elim14C
open Submission.CDT.ElimOpC

/-! ## The differential-field infrastructure -/

/-- The element `y` of `ℂ(y)`. -/
abbrev yR : RF := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X : Polynomial ℂ)

lemma am_C (c : ℂ) : am (Polynomial.C c) = algebraMap ℂ RF c := by
  rw [Polynomial.C_eq_algebraMap]
  exact IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) RF c

lemma dRat_am_C (c : ℂ) : dRat (algebraMap ℂ RF c) = 0 := by
  rw [← am_C c]
  exact dRat_C c

lemma yR_eq : yR = am (Polynomial.X : Polynomial ℂ) := rfl

lemma dRat_yR : dRat yR = 1 := by
  rw [yR_eq, dRat_algebraMap]
  simp

lemma yR_ne_zero : yR ≠ 0 := by
  have h : yR = am (Polynomial.X : Polynomial ℂ) := rfl
  rw [h]
  exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero

/-- `δ` is additive over finite sums. -/
lemma deriv_sum {M : Type*} [AddCommGroup M] (δ : M → M)
    (hadd : ∀ x y : M, δ (x + y) = δ x + δ y) {ι : Type*} (s : Finset ι) (f : ι → M) :
    δ (∑ i ∈ s, f i) = ∑ i ∈ s, δ (f i) := by
  classical
  have hzero : δ 0 = 0 := by
    have h : δ 0 = δ 0 + δ 0 := by simpa using hadd 0 0
    have h2 : δ 0 + 0 = δ 0 + δ 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  induction s using Finset.induction_on with
  | empty => simp [hzero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

/-- Constants are killed by the Leibniz rule. -/
lemma deriv_smul_const {M : Type*} [AddCommGroup M] [Module RF M] (δ : M → M)
    (hsmul : ∀ (r : RF) (m : M), δ (r • m) = dRat r • m + r • δ m)
    (c : ℂ) (m : M) : δ ((algebraMap ℂ RF c) • m) = (algebraMap ℂ RF c) • δ m := by
  rw [hsmul, dRat_am_C c, zero_smul, zero_add]

/-! ## The explicit data of the paper's system -/

/-- The matrix of the derivation on `Δ, Δ', Δ'', Δ'''`: `δ (u i) = Σ k, Du i k • u k`. -/
def Du : Fin 4 → Fin 4 → RF :=
  ![
    ![(0 : RF), 1, 0, 0],
    ![0, 0, 1, 0],
    ![0, 0, 0, 1],
    ![-Zz, -Uu, -Vv, -Ww]
  ]

/-- The top row of `Du`, i.e. the coefficients of `δ (u 3)` in the basis `u k`. -/
def cU : Fin 4 → RF := ![Zz, Uu, Vv, Ww]

/-- The scalars `e j` with `δ (v j) = e j • u 0`. -/
def Ev : Fin 3 → RF := ![(1 : RF), yR⁻¹, (yR ^ 2)⁻¹]

/-- The coefficients `q k` of the derivative of `Σ b k • u k`. -/
def qv (b : Fin 4 → RF) : Fin 4 → RF :=
  ![dRat (b 0) - Zz * b 3, dRat (b 1) + b 0 - Uu * b 3,
    dRat (b 2) + b 1 - Vv * b 3, dRat (b 3) + b 2 - Ww * b 3]

variable {M : Type*} [AddCommGroup M] [Module RF M]

lemma cU_sum (u : Fin 4 → M) :
    (∑ k : Fin 4, cU k • u k) = Zz • u 0 + Uu • u 1 + Vv • u 2 + Ww • u 3 := by
  rw [Fin.sum_univ_four]; simp [cU]

/-- The `u 3`-row of the derivation matrix, in the form in which the ODE provides it. -/
lemma Du_three (u : Fin 4 → M) :
    (∑ k : Fin 4, Du 3 k • u k) = -(∑ k : Fin 4, cU k • u k) := by
  trans ∑ k : Fin 4, (-(cU k)) • u k
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    fin_cases k <;> simp [Du, cU]
  · rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun k _ => neg_smul (cU k) (u k))

/-- The coefficient identity `dRat (b k) + Σ i, b i * Du i k = qv b k`. -/
lemma qv_eq (b : Fin 4 → RF) (k : Fin 4) :
    dRat (b k) + (∑ i : Fin 4, b i * Du i k) = qv b k := by
  fin_cases k
  · show dRat (b 0) + (∑ i : Fin 4, b i * Du i 0) = qv b 0
    rw [Fin.sum_univ_four]; simp [Du, qv]; ring
  · show dRat (b 1) + (∑ i : Fin 4, b i * Du i 1) = qv b 1
    rw [Fin.sum_univ_four]; simp [Du, qv]; ring
  · show dRat (b 2) + (∑ i : Fin 4, b i * Du i 2) = qv b 2
    rw [Fin.sum_univ_four]; simp [Du, qv]; ring
  · show dRat (b 3) + (∑ i : Fin 4, b i * Du i 3) = qv b 3
    rw [Fin.sum_univ_four]; simp [Du, qv]; ring

lemma Ev_sum : (∑ j : Fin 3, Ev j) = 1 + yR⁻¹ + (yR ^ 2)⁻¹ := by
  rw [Fin.sum_univ_three]; simp [Ev]

/-! ## The differentiated relation -/

/-- **The differentiated relation.**  Differentiating a relation
`Σ_j A_j • v_j = Σ_i b_i • u_i` (with `A_j ∈ ℂ[y]` arbitrary, no constancy needed) replaces the
`v`-coefficients `A_j` by their derivatives, at the cost of an explicit inhomogeneous
`u`-coefficient:  this is the identity `(remaining)` of the paper. -/
theorem deriv_relation (δ : M → M) (hadd : ∀ x y : M, δ (x + y) = δ x + δ y)
    (hsmul : ∀ (r : RF) (m : M), δ (r • m) = dRat r • m + r • δ m)
    (u : Fin 4 → M) (v : Fin 3 → M)
    (hu0 : δ (u 0) = u 1) (hu1 : δ (u 1) = u 2) (hu2 : δ (u 2) = u 3)
    (hu3 : δ (u 3) = -(Zz • u 0 + Uu • u 1 + Vv • u 2 + Ww • u 3))
    (hv0 : δ (v 0) = u 0) (hv1 : δ (v 1) = yR⁻¹ • u 0)
    (hv2 : δ (v 2) = (yR ^ 2)⁻¹ • u 0)
    (A : Fin 3 → Polynomial ℂ) (b : Fin 4 → RF)
    (hrel : ∑ j : Fin 3, am (A j) • v j = ∑ i : Fin 4, b i • u i) :
    ∑ j : Fin 3, am ((A j).derivative) • v j
      = ∑ k : Fin 4, (qv b k - ![∑ j : Fin 3, am (A j) * Ev j, 0, 0, 0] k) • u k := by
  have hvV : ∀ j : Fin 3, δ (v j) = Ev j • u 0 := by
    intro j
    fin_cases j
    · show δ (v 0) = Ev 0 • u 0
      rw [hv0]; simp [Ev]
    · show δ (v 1) = Ev 1 • u 0
      rw [hv1]; simp [Ev]
    · show δ (v 2) = Ev 2 • u 0
      rw [hv2]; simp [Ev]
  have huMat : ∀ i : Fin 4, δ (u i) = ∑ k : Fin 4, Du i k • u k := by
    intro i
    fin_cases i
    · show δ (u 0) = ∑ k : Fin 4, Du 0 k • u k
      rw [hu0, Fin.sum_univ_four]; simp [Du]
    · show δ (u 1) = ∑ k : Fin 4, Du 1 k • u k
      rw [hu1, Fin.sum_univ_four]; simp [Du]
    · show δ (u 2) = ∑ k : Fin 4, Du 2 k • u k
      rw [hu2, Fin.sum_univ_four]; simp [Du]
    · show δ (u 3) = ∑ k : Fin 4, Du 3 k • u k
      rw [hu3, ← cU_sum u, Du_three u]
  have hL : δ (∑ j : Fin 3, am (A j) • v j)
      = ∑ j : Fin 3, am ((A j).derivative) • v j
        + (∑ j : Fin 3, am (A j) * Ev j) • u 0 := by
    rw [deriv_sum δ hadd]
    calc ∑ j : Fin 3, δ (am (A j) • v j)
        = ∑ j : Fin 3, (am ((A j).derivative) • v j + (am (A j) * Ev j) • u 0) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hsmul, dRat_algebraMap, hvV j, smul_smul]
      _ = ∑ j : Fin 3, am ((A j).derivative) • v j + ∑ j : Fin 3, (am (A j) * Ev j) • u 0 :=
          Finset.sum_add_distrib
      _ = ∑ j : Fin 3, am ((A j).derivative) • v j + (∑ j : Fin 3, am (A j) * Ev j) • u 0 := by
          rw [Finset.sum_smul]
  have hR : δ (∑ i : Fin 4, b i • u i) = ∑ k : Fin 4, qv b k • u k := by
    rw [deriv_sum δ hadd]
    calc ∑ i : Fin 4, δ (b i • u i)
        = ∑ i : Fin 4, (dRat (b i) • u i + b i • δ (u i)) :=
          Finset.sum_congr rfl (fun i _ => hsmul (b i) (u i))
      _ = ∑ i : Fin 4, dRat (b i) • u i + ∑ i : Fin 4, b i • δ (u i) :=
          Finset.sum_add_distrib
      _ = ∑ k : Fin 4, dRat (b k) • u k + ∑ k : Fin 4, (∑ i : Fin 4, b i * Du i k) • u k := by
          congr 1
          calc ∑ i : Fin 4, b i • δ (u i)
              = ∑ i : Fin 4, ∑ k : Fin 4, (b i * Du i k) • u k := by
                refine Finset.sum_congr rfl (fun i _ => ?_)
                rw [huMat i, Finset.smul_sum]
                exact Finset.sum_congr rfl (fun k _ => smul_smul (b i) (Du i k) (u k))
            _ = ∑ k : Fin 4, ∑ i : Fin 4, (b i * Du i k) • u k := Finset.sum_comm
            _ = ∑ k : Fin 4, (∑ i : Fin 4, b i * Du i k) • u k :=
                Finset.sum_congr rfl (fun k _ => Finset.sum_smul.symm)
      _ = ∑ k : Fin 4, (dRat (b k) + ∑ i : Fin 4, b i * Du i k) • u k := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun k _ => (add_smul _ _ _).symm)
      _ = ∑ k : Fin 4, qv b k • u k :=
          Finset.sum_congr rfl (fun k _ => by rw [qv_eq b k])
  have hkey : (∑ j : Fin 3, am ((A j).derivative) • v j) + (∑ j : Fin 3, am (A j) * Ev j) • u 0
      = ∑ k : Fin 4, qv b k • u k :=
    hL.symm.trans ((congrArg δ hrel).trans hR)
  have hAtm0 : (∑ j : Fin 3, am (A j) * Ev j) • u 0
      = ∑ k : Fin 4, ![∑ j : Fin 3, am (A j) * Ev j, 0, 0, 0] k • u k := by
    rw [Fin.sum_univ_four]; simp
  calc ∑ j : Fin 3, am ((A j).derivative) • v j
      = ∑ k : Fin 4, qv b k • u k - (∑ j : Fin 3, am (A j) * Ev j) • u 0 :=
        eq_sub_iff_add_eq.mpr hkey
    _ = ∑ k : Fin 4, qv b k • u k
          - ∑ k : Fin 4, ![∑ j : Fin 3, am (A j) * Ev j, 0, 0, 0] k • u k := by rw [hAtm0]
    _ = ∑ k : Fin 4, (qv b k - ![∑ j : Fin 3, am (A j) * Ev j, 0, 0, 0] k) • u k := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun k _ => (sub_smul _ _ _).symm)

/-! ## The paper's step `(todiff) ⟹ system` -/

/-- **The paper's step, in the form used in the proof of Lemma `14functions`.**  A relation
`(todiff)` with *constant* coefficients on the three integrals forces the paper's system of
four equations on `b₀,…,b₃`. -/
theorem system_of_relation (δ : M → M) (hadd : ∀ x y : M, δ (x + y) = δ x + δ y)
    (hsmul : ∀ (r : RF) (m : M), δ (r • m) = dRat r • m + r • δ m)
    (u : Fin 4 → M) (v : Fin 3 → M)
    (hu0 : δ (u 0) = u 1) (hu1 : δ (u 1) = u 2) (hu2 : δ (u 2) = u 3)
    (hu3 : δ (u 3) = -(Zz • u 0 + Uu • u 1 + Vv • u 2 + Ww • u 3))
    (hv0 : δ (v 0) = u 0) (hv1 : δ (v 1) = yR⁻¹ • u 0)
    (hv2 : δ (v 2) = (yR ^ 2)⁻¹ • u 0)
    (hindep : ∀ p : Fin 4 → RF, (∑ i, p i • u i) = 0 → p = 0)
    (A : Fin 3 → Polynomial ℂ) (b : Fin 4 → RF)
    (hA : ∀ j, (A j).natDegree = 0)
    (hrel : ∑ j : Fin 3, am (A j) • v j = ∑ i : Fin 4, b i • u i) :
    (dRat (b 3) + b 2 - Ww * b 3 = 0) ∧ (dRat (b 2) + b 1 - Vv * b 3 = 0) ∧
    (dRat (b 1) + b 0 - Uu * b 3 = 0) ∧
    (dRat (b 0) - Zz * b 3 = am (A 0) + am (A 1) * yR⁻¹ + am (A 2) * (yR ^ 2)⁻¹) := by
  have hder := deriv_relation δ hadd hsmul u v hu0 hu1 hu2 hu3 hv0 hv1 hv2 A b hrel
  have hz : (∑ j : Fin 3, am ((A j).derivative) • v j) = 0 := by
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [Polynomial.derivative_eq_zero.mpr (hA j)]
    simp
  have h0 : (∑ k : Fin 4, (qv b k - ![∑ j : Fin 3, am (A j) * Ev j, 0, 0, 0] k) • u k) = 0 := by
    rw [← hder, hz]
  have hp := hindep (fun k => qv b k - ![∑ j : Fin 3, am (A j) * Ev j, 0, 0, 0] k) h0
  have e0 : qv b 0 - (∑ j : Fin 3, am (A j) * Ev j) = 0 := by
    simpa using congrFun hp 0
  have e1 : qv b 1 = 0 := by simpa using congrFun hp 1
  have e2 : qv b 2 = 0 := by simpa using congrFun hp 2
  have e3 : qv b 3 = 0 := by simpa using congrFun hp 3
  have hEvsum : (∑ j : Fin 3, am (A j) * Ev j)
      = am (A 0) + am (A 1) * yR⁻¹ + am (A 2) * (yR ^ 2)⁻¹ := by
    rw [Fin.sum_univ_three]; simp [Ev]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [qv] using e3
  · simpa [qv] using e2
  · simpa [qv] using e1
  · have hlast : dRat (b 0) - Zz * b 3
        - (am (A 0) + am (A 1) * yR⁻¹ + am (A 2) * (yR ^ 2)⁻¹) = 0 := by
      simpa [qv, hEvsum] using e0
    exact sub_eq_zero.mp hlast

/-! ## Reduction of an arbitrary relation to constant coefficients -/

/-- **Clearing denominators.**  A relation `Σ_j A_j • v_j = Σ_i B_i • u_i` with coefficients in
`ℂ(y)` can be scaled by the common denominator of the `A_j` to one with coefficients in `ℂ[y]`. -/
lemma exists_poly_relation (u : Fin 4 → M) (v : Fin 3 → M) (A : Fin 3 → RF) (B : Fin 4 → RF)
    (hA : A ≠ 0) (hrel : ∑ j : Fin 3, A j • v j = ∑ i : Fin 4, B i • u i) :
    ∃ (A' : Fin 3 → Polynomial ℂ) (B' : Fin 4 → RF), A' ≠ 0 ∧
      ∑ j : Fin 3, am (A' j) • v j = ∑ i : Fin 4, B' i • u i := by
  classical
  refine ⟨fun j => (∏ k ∈ Finset.univ.erase j, (A k).denom) * (A j).num,
    fun i => am (∏ j : Fin 3, (A j).denom) * B i, ?_, ?_⟩
  · intro hA'
    apply hA
    funext j
    have h := congrFun hA' j
    simp only [Pi.zero_apply] at h
    have hprod : (∏ k ∈ Finset.univ.erase j, (A k).denom) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun k _ => RatFunc.denom_ne_zero (A k))
    have hnum : (A j).num = 0 := (mul_eq_zero.mp h).resolve_left hprod
    rw [← RatFunc.num_div_denom (A j), hnum]
    simp
  · have hfactor : ∀ j : Fin 3, am ((∏ k ∈ Finset.univ.erase j, (A k).denom) * (A j).num)
        = am (∏ k : Fin 3, (A k).denom) * A j := by
      intro j
      have hsplit : (∏ k : Fin 3, (A k).denom)
          = (∏ k ∈ Finset.univ.erase j, (A k).denom) * (A j).denom :=
        (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
      have hmul : am ((∏ k ∈ Finset.univ.erase j, (A k).denom) * (A j).num)
          = am (∏ k ∈ Finset.univ.erase j, (A k).denom) * am (A j).num :=
        map_mul (algebraMap (Polynomial ℂ) (RatFunc ℂ)) _ _
      have hnd : A j = am (A j).num / am (A j).denom := (RatFunc.num_div_denom (A j)).symm
      have hmul2 : am ((∏ k ∈ Finset.univ.erase j, (A k).denom) * (A j).denom)
          = am (∏ k ∈ Finset.univ.erase j, (A k).denom) * am (A j).denom :=
        map_mul (algebraMap (Polynomial ℂ) (RatFunc ℂ)) _ _
      rw [hmul]
      conv_rhs => rw [hnd]
      rw [hsplit, hmul2]
      have hd : am (A j).denom ≠ 0 := RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero (A j))
      field_simp
    calc ∑ j : Fin 3, am ((∏ k ∈ Finset.univ.erase j, (A k).denom) * (A j).num) • v j
        = ∑ j : Fin 3, (am (∏ k : Fin 3, (A k).denom) * A j) • v j :=
          Finset.sum_congr rfl (fun j _ => by rw [hfactor j])
      _ = ∑ j : Fin 3, am (∏ k : Fin 3, (A k).denom) • (A j • v j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [smul_smul]
      _ = am (∏ k : Fin 3, (A k).denom) • ∑ j : Fin 3, A j • v j := (Finset.smul_sum).symm
      _ = am (∏ k : Fin 3, (A k).denom) • ∑ i : Fin 4, B i • u i := by rw [hrel]
      _ = ∑ i : Fin 4, am (∏ k : Fin 3, (A k).denom) • (B i • u i) := Finset.smul_sum
      _ = ∑ i : Fin 4, (am (∏ k : Fin 3, (A k).denom) * B i) • u i := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [smul_smul]

/-- **Expansion of a `Fin 7`-sum.**  Splits a sum over the seven functions
`(v₀,v₁,v₂,u₀,u₁,u₂,u₃)` into a `Fin 3`-sum and a `Fin 4`-sum. -/
lemma sum_fin_seven_split {N : Type*} [AddCommMonoid N] [SMul RF N] (h : Fin 7 → RF)
    (v0 v1 v2 u0 u1 u2 u3 : N) :
    (∑ i : Fin 7, h i • ![v0, v1, v2, u0, u1, u2, u3] i)
      = (∑ j : Fin 3, h (Fin.castLE (by norm_num : 3 ≤ 7) j) • ![v0, v1, v2] j)
        + ∑ i : Fin 4, h (Fin.natAdd 3 i) • ![u0, u1, u2, u3] i := by
  simp [Fin.sum_univ_succ, Fin.sum_univ_three, Fin.sum_univ_four]
  abel

/-- **Descent to constant coefficients.**  From a relation with polynomial coefficients one can
differentiate down to a relation whose `v`-coefficients are constants, the degree
`Σ_j deg (A j)` being the termination measure. -/
lemma exists_degree_zero_relation (δ : M → M) (hadd : ∀ x y : M, δ (x + y) = δ x + δ y)
    (hsmul : ∀ (r : RF) (m : M), δ (r • m) = dRat r • m + r • δ m)
    (u : Fin 4 → M) (v : Fin 3 → M)
    (hu0 : δ (u 0) = u 1) (hu1 : δ (u 1) = u 2) (hu2 : δ (u 2) = u 3)
    (hu3 : δ (u 3) = -(Zz • u 0 + Uu • u 1 + Vv • u 2 + Ww • u 3))
    (hv0 : δ (v 0) = u 0) (hv1 : δ (v 1) = yR⁻¹ • u 0)
    (hv2 : δ (v 2) = (yR ^ 2)⁻¹ • u 0)
    (A : Fin 3 → Polynomial ℂ) (B : Fin 4 → RF) (hA : A ≠ 0)
    (hrel : ∑ j : Fin 3, am (A j) • v j = ∑ i : Fin 4, B i • u i) :
    ∃ (A' : Fin 3 → Polynomial ℂ) (B' : Fin 4 → RF),
      (∀ j, (A' j).natDegree = 0) ∧ A' ≠ 0 ∧
      ∑ j : Fin 3, am (A' j) • v j = ∑ i : Fin 4, B' i • u i := by
  suffices key : ∀ n : ℕ, ∀ (A : Fin 3 → Polynomial ℂ) (B : Fin 4 → RF),
      (∑ j : Fin 3, (A j).natDegree) ≤ n → A ≠ 0 →
      (∑ j : Fin 3, am (A j) • v j = ∑ i : Fin 4, B i • u i) →
      ∃ (A' : Fin 3 → Polynomial ℂ) (B' : Fin 4 → RF),
        (∀ j, (A' j).natDegree = 0) ∧ A' ≠ 0 ∧
        ∑ j : Fin 3, am (A' j) • v j = ∑ i : Fin 4, B' i • u i from
    key _ A B le_rfl hA hrel
  intro n
  induction n with
  | zero =>
    intro A B hsum hA hrel
    refine ⟨A, B, fun j => ?_, hA, hrel⟩
    exact Nat.le_zero.mp (le_trans (Finset.single_le_sum
      (f := fun j : Fin 3 => (A j).natDegree) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)) hsum)
  | succ n ih =>
    intro A B hsum hA hrel
    by_cases hdeg : ∀ j : Fin 3, (A j).natDegree = 0
    · exact ⟨A, B, hdeg, hA, hrel⟩
    · push Not at hdeg
      obtain ⟨j0, hj0⟩ := hdeg
      have hlt : (∑ j : Fin 3, ((A j).derivative).natDegree) ≤ n := by
        have h2 : (∑ j : Fin 3, ((A j).derivative).natDegree)
            < ∑ j : Fin 3, (A j).natDegree := by
          refine Finset.sum_lt_sum (fun j _ => ?_) ⟨j0, Finset.mem_univ j0, ?_⟩
          · rw [Polynomial.natDegree_derivative]; exact Nat.sub_le _ _
          · rw [Polynomial.natDegree_derivative]
            exact Nat.sub_lt (Nat.pos_of_ne_zero hj0) Nat.one_pos
        omega
      have hne : (fun j => (A j).derivative) ≠ 0 := by
        intro h
        have h1 := congrFun h j0
        simp only [Pi.zero_apply] at h1
        exact hj0 (Polynomial.derivative_eq_zero.mp h1)
      have hder := deriv_relation δ hadd hsmul u v hu0 hu1 hu2 hu3 hv0 hv1 hv2 A B hrel
      exact ih (fun j => (A j).derivative)
        (fun i => qv B i - ![∑ j : Fin 3, am (A j) * Ev j, 0, 0, 0] i) hlt hne hder

/-! ## The main theorem: no relation at all -/

/-- **Lemma `14functions`, second half (algebraic part), in its cleanest form.**  In the
abstract differential-module setting of this file (a solution `u 0,…,u 3` of the order-`4`
operator with independent derivatives, and its three integrals `v 0,v 1,v 2`), the seven
elements `v₀,v₁,v₂,u₀,u₁,u₂,u₃` are `ℂ(y)`-linearly independent: a relation
`Σ_j A_j • v_j = Σ_i B_i • u_i` forces `A = 0` and `B = 0`. -/
theorem relation_trivial (δ : M → M) (hadd : ∀ x y : M, δ (x + y) = δ x + δ y)
    (hsmul : ∀ (r : RF) (m : M), δ (r • m) = dRat r • m + r • δ m)
    (u : Fin 4 → M) (v : Fin 3 → M)
    (hu0 : δ (u 0) = u 1) (hu1 : δ (u 1) = u 2) (hu2 : δ (u 2) = u 3)
    (hu3 : δ (u 3) = -(Zz • u 0 + Uu • u 1 + Vv • u 2 + Ww • u 3))
    (hv0 : δ (v 0) = u 0) (hv1 : δ (v 1) = yR⁻¹ • u 0)
    (hv2 : δ (v 2) = (yR ^ 2)⁻¹ • u 0)
    (hindep : ∀ p : Fin 4 → RF, (∑ i, p i • u i) = 0 → p = 0)
    (A : Fin 3 → RF) (B : Fin 4 → RF)
    (hrel : ∑ j : Fin 3, A j • v j = ∑ i : Fin 4, B i • u i) : A = 0 ∧ B = 0 := by
  by_cases hA0 : A = 0
  · refine ⟨hA0, ?_⟩
    have hz : (∑ i : Fin 4, B i • u i) = 0 := by
      rw [← hrel, Finset.sum_eq_zero (fun j _ => by rw [hA0, Pi.zero_apply, zero_smul])]
    exact hindep B hz
  obtain ⟨A₁, B₁, hA₁, hrel₁⟩ := exists_poly_relation u v A B hA0 hrel
  obtain ⟨A₂, B₂, hdeg, hA₂, hrel₂⟩ :=
    exists_degree_zero_relation δ hadd hsmul u v hu0 hu1 hu2 hu3 hv0 hv1 hv2 A₁ B₁ hA₁ hrel₁
  obtain ⟨h1, h2, h3, h4⟩ :=
    system_of_relation δ hadd hsmul u v hu0 hu1 hu2 hu3 hv0 hv1 hv2 hindep A₂ B₂ hdeg hrel₂
  classical
  set R : RF := am (A₂ 0) + am (A₂ 1) * yR⁻¹ + am (A₂ 2) * (yR ^ 2)⁻¹ with hRdef
  set Rnum : Polynomial ℂ := A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X + A₂ 2 with hRnumdef
  have hA₂C : ∀ i : Fin 3, A₂ i = Polynomial.C ((A₂ i).coeff 0) :=
    fun i => Polynomial.eq_C_of_natDegree_eq_zero (hdeg i)
  have hRdeg : Rnum.natDegree ≤ 2 := by
    rw [hRnumdef]
    have h0 : (A₂ 0 * Polynomial.X ^ 2).natDegree ≤ 2 := by
      calc (A₂ 0 * Polynomial.X ^ 2).natDegree
          ≤ (A₂ 0).natDegree + (Polynomial.X ^ 2).natDegree := Polynomial.natDegree_mul_le
        _ = 0 + 2 := by rw [hdeg 0, Polynomial.natDegree_X_pow]
        _ ≤ 2 := le_rfl
    have h1 : (A₂ 1 * Polynomial.X).natDegree ≤ 2 := by
      calc (A₂ 1 * Polynomial.X).natDegree
          ≤ (A₂ 1).natDegree + (Polynomial.X).natDegree := Polynomial.natDegree_mul_le
        _ = 0 + 1 := by rw [hdeg 1, Polynomial.natDegree_X]
        _ ≤ 2 := by norm_num
    have h2 : (A₂ 2).natDegree ≤ 2 := by rw [hdeg 2]; norm_num
    have h12 : (A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X).natDegree ≤ 2 := by
      calc (A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X).natDegree
          ≤ max (A₂ 0 * Polynomial.X ^ 2).natDegree (A₂ 1 * Polynomial.X).natDegree :=
            (Polynomial.natDegree_add_le (p := A₂ 0 * Polynomial.X ^ 2)
              (q := A₂ 1 * Polynomial.X))
        _ ≤ 2 := max_le h0 h1
    calc (A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X + A₂ 2).natDegree
        ≤ max (A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X).natDegree (A₂ 2).natDegree :=
          (Polynomial.natDegree_add_le (p := A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X)
            (q := A₂ 2))
      _ ≤ 2 := max_le h12 h2
  have hRnum : Rnum ≠ 0 := by
    intro hzero
    apply hA₂
    funext i
    have hc : (A₂ i).coeff 0 = 0 := by
      fin_cases i
      · have h := congrArg (fun p : Polynomial ℂ => p.coeff 2) hzero
        rw [hRnumdef, hA₂C 0, hA₂C 1, hA₂C 2] at h
        simpa [Polynomial.coeff_C_mul_X_pow] using h
      · have h := congrArg (fun p : Polynomial ℂ => p.coeff 1) hzero
        rw [hRnumdef, hA₂C 0, hA₂C 1, hA₂C 2] at h
        simpa [Polynomial.coeff_C_mul_X_pow] using h
      · have h := congrArg (fun p : Polynomial ℂ => p.coeff 0) hzero
        rw [hRnumdef, hA₂C 0, hA₂C 1, hA₂C 2] at h
        simpa [Polynomial.coeff_C_mul_X_pow] using h
    rw [hA₂C i, hc]
    simp
  have hamX : am (Polynomial.X : Polynomial ℂ) = yR := rfl
  have hamX2 : am (Polynomial.X ^ 2 : Polynomial ℂ) = yR ^ 2 := by
    have hmm : am ((Polynomial.X : Polynomial ℂ) * Polynomial.X) = am Polynomial.X * am Polynomial.X :=
      map_mul (algebraMap (Polynomial ℂ) (RatFunc ℂ)) _ _
    rw [pow_two, hmm, pow_two]
  have hRnumam : am Rnum = am (A₂ 0) * yR ^ 2 + am (A₂ 1) * yR + am (A₂ 2) := by
    have ha0 : am (A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X + A₂ 2)
        = am (A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X) + am (A₂ 2) :=
      map_add (algebraMap (Polynomial ℂ) (RatFunc ℂ)) _ _
    have ha1 : am (A₂ 0 * Polynomial.X ^ 2 + A₂ 1 * Polynomial.X)
        = am (A₂ 0 * Polynomial.X ^ 2) + am (A₂ 1 * Polynomial.X) :=
      map_add (algebraMap (Polynomial ℂ) (RatFunc ℂ)) _ _
    have hm0 : am (A₂ 0 * Polynomial.X ^ 2) = am (A₂ 0) * yR ^ 2 := by
      have hmm : am (A₂ 0 * Polynomial.X ^ 2) = am (A₂ 0) * am (Polynomial.X ^ 2) :=
        map_mul (algebraMap (Polynomial ℂ) (RatFunc ℂ)) _ _
      rw [hmm, hamX2]
    have hm1 : am (A₂ 1 * Polynomial.X) = am (A₂ 1) * yR := by
      have hmm : am (A₂ 1 * Polynomial.X) = am (A₂ 1) * am (Polynomial.X) :=
        map_mul (algebraMap (Polynomial ℂ) (RatFunc ℂ)) _ _
      rw [hmm, hamX]
    rw [hRnumdef, ha0, ha1, hm0, hm1]
  have hR : R = am Rnum / am (Polynomial.X ^ 2) := by
    rw [hRdef, hRnumam, hamX2]
    have hy : yR ≠ 0 := yR_ne_zero
    field_simp
  have hRne : R ≠ 0 := by
    rw [hR]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hRnum)
      (RatFunc.algebraMap_ne_zero (pow_ne_zero 2 Polynomial.X_ne_zero))
  have hb3 : B₂ 3 ≠ 0 := by
    intro hb
    have h220 : B₂ 2 = 0 := by rw [hb] at h1; simpa using h1
    have h210 : B₂ 1 = 0 := by rw [hb, h220] at h2; simpa using h2
    have h200 : B₂ 0 = 0 := by rw [hb, h210] at h3; simpa using h3
    rw [hb, h200] at h4
    have hz : R = 0 := by
      rw [hRdef] at h4 ⊢
      simpa using h4.symm
    exact hRne hz
  have hcontra : False :=
    FrobeniusApply.no_solution (B₂ 0) (B₂ 1) (B₂ 2) (B₂ 3) R Rnum hb3 hRnum hRdeg hR h1 h2 h3 h4
  exact absurd hcontra not_false

/-- **The seven-element statement in the form of the paper.**  The seven elements
`v₀,v₁,v₂,u₀,u₁,u₂,u₃` (the three integrals `∫Δ, ∫Δ/y, ∫Δ/y²` together with the solution
`Δ, Δ', Δ'', Δ'''` of the order-`4` operator) are `ℂ(y)`-linearly independent. -/
theorem linearIndependent_seven (δ : M → M) (hadd : ∀ x y : M, δ (x + y) = δ x + δ y)
    (hsmul : ∀ (r : RF) (m : M), δ (r • m) = dRat r • m + r • δ m)
    (u : Fin 4 → M) (v : Fin 3 → M)
    (hu0 : δ (u 0) = u 1) (hu1 : δ (u 1) = u 2) (hu2 : δ (u 2) = u 3)
    (hu3 : δ (u 3) = -(Zz • u 0 + Uu • u 1 + Vv • u 2 + Ww • u 3))
    (hv0 : δ (v 0) = u 0) (hv1 : δ (v 1) = yR⁻¹ • u 0)
    (hv2 : δ (v 2) = (yR ^ 2)⁻¹ • u 0)
    (hindep : ∀ p : Fin 4 → RF, (∑ i, p i • u i) = 0 → p = 0) :
    LinearIndependent RF ![v 0, v 1, v 2, u 0, u 1, u 2, u 3] := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g hfg
  have hf : (∑ i : Fin 7, f i • ![v 0, v 1, v 2, u 0, u 1, u 2, u 3] i)
      = f 0 • v 0 + f 1 • v 1 + f 2 • v 2 + f 3 • u 0 + f 4 • u 1 + f 5 • u 2 + f 6 • u 3 := by
    simp [Fin.sum_univ_succ]
    abel
  have hg : (∑ i : Fin 7, g i • ![v 0, v 1, v 2, u 0, u 1, u 2, u 3] i)
      = g 0 • v 0 + g 1 • v 1 + g 2 • v 2 + g 3 • u 0 + g 4 • u 1 + g 5 • u 2 + g 6 • u 3 := by
    simp [Fin.sum_univ_succ]
    abel
  have h7 : f 0 • v 0 + f 1 • v 1 + f 2 • v 2 + f 3 • u 0 + f 4 • u 1 + f 5 • u 2 + f 6 • u 3
      = g 0 • v 0 + g 1 • v 1 + g 2 • v 2 + g 3 • u 0 + g 4 • u 1 + g 5 • u 2 + g 6 • u 3 := by
    rw [← hf, ← hg]
    exact hfg
  have hsub : (f 0 - g 0) • v 0 + (f 1 - g 1) • v 1 + (f 2 - g 2) • v 2
        + (f 3 - g 3) • u 0 + (f 4 - g 4) • u 1 + (f 5 - g 5) • u 2 + (f 6 - g 6) • u 3
      = (f 0 • v 0 + f 1 • v 1 + f 2 • v 2 + f 3 • u 0 + f 4 • u 1 + f 5 • u 2 + f 6 • u 3)
        - (g 0 • v 0 + g 1 • v 1 + g 2 • v 2 + g 3 • u 0 + g 4 • u 1 + g 5 • u 2 + g 6 • u 3) := by
    simp only [sub_smul]
    abel
  have hmid : (f 0 - g 0) • v 0 + (f 1 - g 1) • v 1 + (f 2 - g 2) • v 2
        + (f 3 - g 3) • u 0 + (f 4 - g 4) • u 1 + (f 5 - g 5) • u 2 + (f 6 - g 6) • u 3 = 0 :=
    hsub.trans (by rw [h7, sub_self])
  set A : Fin 3 → RF := ![f 0 - g 0, f 1 - g 1, f 2 - g 2] with hAdef
  set B : Fin 4 → RF := ![f 3 - g 3, f 4 - g 4, f 5 - g 5, f 6 - g 6] with hBdef
  have hrel : ∑ j : Fin 3, A j • v j = ∑ i : Fin 4, (-(B i)) • u i := by
    have hL : (∑ j : Fin 3, A j • v j)
        = (f 0 - g 0) • v 0 + (f 1 - g 1) • v 1 + (f 2 - g 2) • v 2 := by
      rw [Fin.sum_univ_three]
      simp [A]
    have hR : (∑ i : Fin 4, (-(B i)) • u i)
        = -((f 3 - g 3) • u 0 + (f 4 - g 4) • u 1 + (f 5 - g 5) • u 2 + (f 6 - g 6) • u 3) := by
      rw [Fin.sum_univ_four]
      simp only [B, Matrix.cons_val_zero, Matrix.cons_val_succ, neg_smul]
      abel
    rw [hL, hR, eq_neg_iff_add_eq_zero]
    have hsplit : (f 0 - g 0) • v 0 + (f 1 - g 1) • v 1 + (f 2 - g 2) • v 2
        + ((f 3 - g 3) • u 0 + (f 4 - g 4) • u 1 + (f 5 - g 5) • u 2 + (f 6 - g 6) • u 3)
        = (f 0 - g 0) • v 0 + (f 1 - g 1) • v 1 + (f 2 - g 2) • v 2 + (f 3 - g 3) • u 0
          + (f 4 - g 4) • u 1 + (f 5 - g 5) • u 2 + (f 6 - g 6) • u 3 := by abel
    rw [hsplit]
    exact hmid
  obtain ⟨hAz, hBz⟩ :=
    relation_trivial δ hadd hsmul u v hu0 hu1 hu2 hu3 hv0 hv1 hv2 hindep A (fun i => -(B i)) hrel
  have hBz' : B = 0 := by
    funext i
    have h := congrFun hBz i
    simpa using neg_eq_zero.mp h
  intro i
  fin_cases i
  · show f 0 = g 0
    have h := congrFun hAz (0 : Fin 3)
    rw [hAdef] at h
    exact sub_eq_zero.mp (by simpa using h)
  · show f 1 = g 1
    have h := congrFun hAz (1 : Fin 3)
    rw [hAdef] at h
    exact sub_eq_zero.mp (by simpa using h)
  · show f 2 = g 2
    have h := congrFun hAz (2 : Fin 3)
    rw [hAdef] at h
    exact sub_eq_zero.mp (by simpa using h)
  · show f 3 = g 3
    have h := congrFun hBz' (0 : Fin 4)
    rw [hBdef] at h
    exact sub_eq_zero.mp (by simpa using h)
  · show f 4 = g 4
    have h := congrFun hBz' (1 : Fin 4)
    rw [hBdef] at h
    exact sub_eq_zero.mp (by simpa using h)
  · show f 5 = g 5
    have h := congrFun hBz' (2 : Fin 4)
    rw [hBdef] at h
    exact sub_eq_zero.mp (by simpa using h)
  · show f 6 = g 6
    have h := congrFun hBz' (3 : Fin 4)
    rw [hBdef] at h
    exact sub_eq_zero.mp (by simpa using h)

/-- **The paper's `(todiff)` in the form in which it arises.**  If the coefficients of the three
integrals are *complex* constants then the relation is trivial: `a = 0` and `B = 0`. -/
theorem no_relation_const (δ : M → M) (hadd : ∀ x y : M, δ (x + y) = δ x + δ y)
    (hsmul : ∀ (r : RF) (m : M), δ (r • m) = dRat r • m + r • δ m)
    (u : Fin 4 → M) (v : Fin 3 → M)
    (hu0 : δ (u 0) = u 1) (hu1 : δ (u 1) = u 2) (hu2 : δ (u 2) = u 3)
    (hu3 : δ (u 3) = -(Zz • u 0 + Uu • u 1 + Vv • u 2 + Ww • u 3))
    (hv0 : δ (v 0) = u 0) (hv1 : δ (v 1) = yR⁻¹ • u 0)
    (hv2 : δ (v 2) = (yR ^ 2)⁻¹ • u 0)
    (hindep : ∀ p : Fin 4 → RF, (∑ i, p i • u i) = 0 → p = 0)
    (a : Fin 3 → ℂ) (B : Fin 4 → RF)
    (hrel : ∑ j : Fin 3, (algebraMap ℂ RF (a j)) • v j = ∑ i : Fin 4, B i • u i) :
    a = 0 ∧ B = 0 := by
  have h := relation_trivial δ hadd hsmul u v hu0 hu1 hu2 hu3 hv0 hv1 hv2 hindep
    (fun j => algebraMap ℂ RF (a j)) B hrel
  refine ⟨?_, h.2⟩
  funext j
  have h1 := congrFun h.1 j
  simpa using h1

end RelSystem
end Submission.CDT
