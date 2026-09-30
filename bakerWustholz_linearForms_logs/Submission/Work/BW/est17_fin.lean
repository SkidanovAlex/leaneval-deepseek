import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.est17_gexp
import Submission.Work.BW.tijdeman_rat
import Submission.Work.BW.ap_factorial_dvd
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.est15defs
import Submission.Work.BW.acH_lower
import Submission.Work.BW.deltaRat_int
import Submission.Work.BW.est17_rat_fin_le
import Submission.Work.BW.est17_mon_fin_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex NumberField

/-! ### Generic non-archimedean tools at a finite place -/

/-- At a finite place `w` of a number field, a finite sum is bounded by any upper bound of the
summands: `w (∑_{i∈s} f i) ≤ B` whenever `0 ≤ B` and `w (f i) ≤ B` for `i ∈ s`.  This is the
ultrametric (`max`) inequality iterated over the finset. -/
theorem finplace_sum_le {L : Type*} [Field L] [NumberField L] (w : NumberField.FinitePlace L)
    {ι : Type*} (s : Finset ι) (f : ι → L) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ s, w (f i) ≤ B) : w (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (FinitePlace.add_le w _ _).trans
        (max_le (h a (Finset.mem_insert_self a s))
          (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

/-- A finite place of a number field is `≤ 1` on the integers. -/
theorem finplace_intCast_le_one {L : Type*} [Field L] [NumberField L]
    (w : NumberField.FinitePlace L) (z : ℤ) : w (z : L) ≤ 1 := by
  have hv : IsNonarchimedean (fun x : L => w x) := FinitePlace.add_le w
  exact IsNonarchimedean.apply_intCast_le_one (map_zero_le w 1) (map_one w) (map_neg_eq_map w) hv

/-- A finite place of a number field is `≤ 1` on the naturals. -/
theorem finplace_natCast_le_one {L : Type*} [Field L] [NumberField L]
    (w : NumberField.FinitePlace L) (n : ℕ) : w (n : L) ≤ 1 := by
  have hv : IsNonarchimedean (fun x : L => w x) := FinitePlace.add_le w
  exact IsNonarchimedean.apply_natCast_le_one (map_zero_le w 1) (map_one w) hv

/-- Non-archimedean upper bound for `g(s/2)` at a place `w` of the Kummer extension:
`w g(s/2) ≤ (max_λ w(φ(p λ))) · exp(|z|·Ω_w + 2(J+1)h(D₀+1)|log w(2)|)`, `z = |s|/2^{J+1}`,
with the sign-aware `Ω_w = Σ_j D_j log⁺ w(α'_j^{sign s})` (as in `est17_arch`).
Uses non-archimedean maximality (`|Σ|_w ≤ max_lm |·|_w`), the integrality of the `Δ`-factors
and `ulcm`, and `tijdeman_rat` for `2^{(J+1)2h(λ₋₁+1)}Θ ∈ ℤ`, so that the only place-dependent
factors besides `w(φ(pλ))` and `Ω_w` are `|log w(2)|`. -/
theorem est17_fin {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {Lm : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v Lm α' σl ι p) (J : ℕ) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σl) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    [inst : NumberField (EL φ (rhoC φ α v Lm))]
    (hmem : acg φ α b k Lm ι v σl p J μ t0 t ((s : ℂ) / 2) ∈ (EL φ (rhoC φ α v Lm) : Set ℂ))
    (w : NumberField.FinitePlace (EL φ (rhoC φ α v Lm))) :
    w (gamE α v Lm φ b k p J μ t0 t s hmem) ≤
      (⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm))) * Real.exp (
        (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σl j : ℝ)
            * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
               else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog
        + 2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * |Real.log (w (inclE φ (rhoC φ α v Lm) (2 : K)))|) := by
  classical
  set SUP : ℝ := ⨆ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl),
      w (inclE φ (rhoC φ α v Lm) (p lm)) with hSUPdef
  set MON : ℝ := (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σl j : ℝ)
            * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
               else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog with hMONdef
  set CF : ℝ := 2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * |Real.log (w (inclE φ (rhoC φ α v Lm) (2 : K)))| with hCFdef
  have hBdd : BddAbove (Set.range (fun lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl)
      (pDj r (dK K) σl) => w (inclE φ (rhoC φ α v Lm) (p lm)))) :=
    (Set.finite_range _).bddAbove
  have hSUPnn : 0 ≤ SUP := by
    have hh : 0 < acH K b v := by have := (acH_lower H).1; omega
    let lm0 : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) :=
      ⟨⟨0, hh⟩, ⟨0, Nat.succ_pos _⟩, fun _ => ⟨0, Nat.succ_pos _⟩⟩
    rw [hSUPdef]
    exact (apply_nonneg w _).trans (le_ciSup hBdd lm0)
  rw [est17_gexp H J μ t0 t s hmem]
  refine finplace_sum_le w Finset.univ _ (mul_nonneg hSUPnn (Real.exp_pos _).le)
    (fun lm _ => ?_)
  by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
  · rw [if_pos hc]
    set A : EL φ (rhoC φ α v Lm) := inclE φ (rhoC φ α v Lm) (p lm) with hAdef
    set Bq : EL φ (rhoC φ α v Lm) := algebraMap ℚ (EL φ (rhoC φ α v Lm))
        ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ)
              (deltaPoly (t m)))
          * (ulcm (acH K b v) : ℚ) ^ t0
          * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ))
              (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))) with hBqdef
    set Crho : EL φ (rhoC φ α v Lm) :=
      ∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)) with hCrhodef
    have hA : w A ≤ SUP := by rw [hAdef, hSUPdef]; exact le_ciSup hBdd lm
    have hBq : w Bq ≤ Real.exp CF := by
      rw [hBqdef, hCFdef]; exact est17_rat_fin_le H J t0 t s w lm
    have hCrho : w Crho ≤ Real.exp MON := by
      rw [hCrhodef, hMONdef]; exact est17_mon_fin_le H J s w lm
    have hBqnn : 0 ≤ w Bq := apply_nonneg w _
    have hCrhonn : 0 ≤ w Crho := apply_nonneg w _
    have hAnnn : 0 ≤ w A := apply_nonneg w _
    calc w (A * Bq * Crho)
        = w (A * Bq) * w Crho := by rw [map_mul]
      _ = w A * w Bq * w Crho := by rw [map_mul]
      _ ≤ (SUP * Real.exp CF) * Real.exp MON := by
            apply mul_le_mul
            · exact mul_le_mul hA hBq hBqnn hSUPnn
            · exact hCrho
            · exact hCrhonn
            · exact mul_nonneg hSUPnn (Real.exp_pos CF).le
      _ = SUP * Real.exp (MON + CF) := by rw [mul_assoc, ← Real.exp_add, add_comm]
  · rw [if_neg hc, map_zero]
    exact mul_nonneg hSUPnn (Real.exp_pos _).le

end Work.BW
