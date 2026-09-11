import Submission.UpperFinal
import Submission.UpperB3
import Submission.UpperB1
import Submission.Switch
import Submission.UpperConfig
import Submission.NBridge

open EquiangularLinesFixedAngle
open Matrix
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! # Eventual upper bounds for `N α d` (used by the main theorem)

Prove the two eventual upper bounds.  Available machinery:

  * Submission.UpperFinal: `upperVal k0 d` (= ⌊k0(d−1)/(k0−1)⌋₊, the same expression used in
    Submission.LowerFinal.eventually_lower_bound), `ratioVal`, `nat_le_floor_of_real_le`,
    `eventually_ratioVal_ge_add`, `ratioVal_ge_bound`, `eventually_upperVal_ge`, `ratioVal_eq`.
  * Submission.UpperB1.b1_bound: case B1: (n : ℝ) ≤ ratioVal k0 d.
  * Submission.UpperB3.b2_bound: case B2.
  * Submission.Switch.switch_bounded.
  * Submission.UpperConfig: `ConfigBounds`, `upper_bound_caseA`.
  * Submission.NBridge: `N_le_of_card_le`, `exists_enumerate`.
  * Submission.Perron / UpperB2 etc.

PLAN (both theorems): first prove the per-family (indexed) version:
  for all sufficiently large d, EVERY indexed family `v : Fin n → EuclideanSpace ℝ (Fin d)`
  satisfying the config properties satisfies `n ≤ X d` (X := upperVal k0 d in the finite case;
  `(n : ℝ) ≤ (1+ε) (d : ℝ)` in the infinite case).  Then use `N_le_of_card_le` and convert the
  ∃D statements into `∀ᶠ d in atTop` via `eventually_atTop`.

For the per-family proof fix `d`, an indexed family v with n ≥ 1 (n = 0 is trivial), and:
  1. (switch) pick `v'` with the same config properties and bounded degree `≤ Δ` where
     Δ := the bound returned by `switch_bounded α hα0 hα1` (pick it once outside the family).
  2. Let G := assocGraph α v', hA := adjMatrix_isHermitian G.
  3. Case A: `∀ j : Fin n, hA.eigenvalues j ≠ lam α` ⇒ `n ≤ d + 1`
     (build `C : ConfigBounds α d := ⟨n, v', norm, angle⟩` and use
     `upper_bound_caseA C hα0`; note C.N = n).
     Then in the finite case use `eventually_upperVal_ge` (d+1 ≤ upperVal k0 d for d ≥ 2k0);
     in the infinite case `d + 1 ≤ (1+ε)(d:ℝ)` for d large.
  4. Case B1: `spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal (lam α)` ⇒
     `(n : ℝ) ≤ ratioVal k0 d` by `b1_bound` (needs `hk` in the finite case; in the infinite
     case B1 is IMPOSSIBLE: `spectralRadiusOrder (lam α) = ⊤` contradicts
     the membership of the graph `G` in the defining set of `spectralRadiusOrder (lam α)`).
  5. Otherwise (B2): `∃ j, hA.eigenvalues j = lam α` and `ρ ≠ ofReal λ`:
     obtain an eigenvector x with value λ (eigenvectorBasis j), and a real ρ0 > λ with
     ρ(A_G) = ofReal ρ0 (the spectral radius of a non-negative symmetric matrix is its largest
     eigenvalue value: `spectralRadius_eq_ofReal_top`).  Then use `b2_bound`:
       - FINITE case, ε0 := 1/(2·(k0:ℝ)): it yields n₀ such that for our family
         `∃ m, n ≤ d + 1 + m ∧ (m ≤ n₀ ∨ (m : ℝ) ≤ ε0 * (n : ℝ))`.
           if `m ≤ n₀`: `n ≤ d + 1 + n₀ ≤ ratioVal k0 d` (for d ≥ D₁ from
             `eventually_ratioVal_ge_add`), hence `n ≤ upperVal k0 d`.
           if `m ≤ ε0·n`: `n(1−ε0) ≤ d+1`, so `n ≤ (d+1)/(1−ε0) ≤ ratioVal k0 d`
             (second ≤ by `ratioVal_ge_bound` for d ≥ 4k0).
       - INFINITE case, ε' := ε/(2(1+ε)) < 1: if `m ≤ n₀` then `n ≤ d+1+n₀ ≤ (1+ε)d`
         eventually; if `m ≤ ε'·n` then `n ≤ (d+1)/(1−ε') ≤ (1+ε)d` eventually
         (since (1−ε')(1+ε) > 1).
  Conclude with `N_le_of_card_le` (finite case) and, in the infinite case, first pass through
  the natural bound `n ≤ ⌊(1+ε)·d⌋₊` and use `Nat.floor_le`.
-/

/-- an eigenvector with a given eigenvalue value, obtained from the eigenvector basis. -/
lemma eigenvector_of_eigenvalue_value {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {lam : ℝ} (h : ∃ j : Fin n, hA.eigenvalues j = lam) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ A *ᵥ x = lam • x := by
  classical
  rcases h with ⟨j, hj⟩
  let x : Fin n → ℝ := (hA.eigenvectorBasis j).ofLp
  refine ⟨x, ?_, ?_⟩
  · intro hx0
    have hd := EigenMult.bfun_unit A hA j
    change (hA.eigenvectorBasis j).ofLp = 0 at hx0
    rw [hx0] at hd
    simp at hd
  · have hb := EigenMult.bfun_eigen A hA j
    simpa [x, hj] using hb

/-- the spectral radius of a non-negative symmetric matrix equals its largest eigenvalue value. -/
lemma spectralRadius_eq_ofReal_top {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (hnonneg : ∀ i j : Fin n, 0 ≤ A i j) :
    ∃ i : Fin n, spectralRadius ℝ A = ENNReal.ofReal (hA.eigenvalues i) ∧
      ∀ j : Fin n, hA.eigenvalues j ≤ hA.eigenvalues i := by
  classical
  rcases exists_top_eigenvalue_index A hA hn with ⟨i, hi⟩
  have htop : ∀ j : Fin n, |hA.eigenvalues j| ≤ hA.eigenvalues i :=
    fun j => top_eigenvalue_ge_abs A hA hnonneg hn i hi j
  have hσi_nonneg : 0 ≤ hA.eigenvalues i := by
    have habs : |hA.eigenvalues i| ≤ hA.eigenvalues i := htop i
    have h1 := (abs_le (a := hA.eigenvalues i) (b := hA.eigenvalues i)).mp habs
    linarith
  have hρ_le : spectralRadius ℝ A ≤ ENNReal.ofReal (hA.eigenvalues i) := by
    rw [spectralRadius]
    refine iSup_le (fun μ => ?_)
    refine iSup_le (fun hμ => ?_)
    rcases exists_eigenvalue_of_mem_spectrum A hA hμ with ⟨j, hj⟩
    have hjμ : |μ| = |hA.eigenvalues j| := by rw [hj]
    have hleabs : |μ| ≤ hA.eigenvalues i := by
      rw [hjμ]
      exact htop j
    have hnn : (‖μ‖₊ : NNReal) = ⟨|μ|, abs_nonneg μ⟩ := by
      apply Subtype.ext
      simp [Real.norm_eq_abs]
    have hco : ((‖μ‖₊ : NNReal) : ENNReal) = ENNReal.ofReal |μ| := by
      rw [hnn]
      exact (ENNReal.ofReal_eq_coe_nnreal (abs_nonneg μ)).symm
    rw [hco]
    exact (ENNReal.ofReal_le_ofReal_iff hσi_nonneg).mpr hleabs
  have hρ_ge : ENNReal.ofReal (hA.eigenvalues i) ≤ spectralRadius ℝ A := by
    have hge := spectralRadius_ge_eigenvalue A hA i
    simpa [abs_of_nonneg hσi_nonneg] using hge
  refine ⟨i, ?_, hi⟩
  exact le_antisymm hρ_le hρ_ge

/-- for any fixed real `c`, eventually `d + c ≤ (1+ε)·d`. -/
lemma eventually_d_add_c_le_mul (c ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → (d : ℝ) + c ≤ (1 + ε) * (d : ℝ) := by
  classical
  rcases exists_nat_ge (c / ε) with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro d hd
  have hdR : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hc : c ≤ ε * (d : ℝ) := by
    have h1 : c / ε ≤ (d : ℝ) := le_trans hD hdR
    have h2 : c ≤ (d : ℝ) * ε := (div_le_iff₀ hε).mp h1
    nlinarith
  nlinarith

/-- if `c0 > 1`, eventually `d + 1 ≤ c0·d`. -/
lemma eventually_d_add_one_le_mul_c0 (c0 : ℝ) (hc0 : 1 < c0) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → (d : ℝ) + 1 ≤ c0 * (d : ℝ) := by
  classical
  rcases exists_nat_ge (1 / (c0 - 1)) with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro d hd
  have hdR : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hpos : 0 < c0 - 1 := by linarith
  have hmain : 1 ≤ (c0 - 1) * (d : ℝ) := by
    have h1 : 1 / (c0 - 1) ≤ (d : ℝ) := le_trans hD hdR
    have h2 : 1 ≤ (d : ℝ) * (c0 - 1) := (div_le_iff₀ hpos).mp h1
    nlinarith
  nlinarith

/-- when the spectral radius order is finite: eventually `N α d ≤ upperVal k0 d`. -/
theorem eventually_upper_finite (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hk : spectralRadiusOrder (lam α) < (⊤ : ℕ∞)) :
    ∀ᶠ d : ℕ in atTop,
      N α d ≤ upperVal (spectralRadiusOrder (lam α)).toNat d := by
  classical
  let k0 : ℕ := (spectralRadiusOrder (lam α)).toNat
  have hlam : 0 < lam α := lam_pos hα0 hα1
  have hk2 : 2 ≤ k0 := by
    simpa [k0] using (spectralRadiusOrder_toNat_ge_two hlam hk)
  rcases switch_bounded α hα0 hα1 with ⟨Δ, hswitch⟩
  let eps : ℝ := 1 / (2 * (k0 : ℝ))
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  rcases b2_bound (α := α) (Δ := Δ) hα0 hα1 eps heps with ⟨n0, hb2⟩
  rcases eventually_upperVal_ge k0 hk2 with ⟨DA, hDA⟩
  rcases eventually_ratioVal_ge_add k0 hk2 (n0 : ℝ) with ⟨D1, hD1⟩
  let D : ℕ := max DA (max (4 * k0) D1)
  rw [eventually_atTop]
  refine ⟨D, ?_⟩
  intro d hd
  have hdA : DA ≤ d := by omega
  have hd4 : 4 * k0 ≤ d := by omega
  have hdD1 : D1 ≤ d := by omega
  have huA : d + 1 ≤ upperVal k0 d := hDA d hdA
  have huR : ((d : ℝ) + 1) / (1 - (1 / (2 * (k0 : ℝ)))) ≤ ratioVal k0 d :=
    ratioVal_ge_bound hk2 hd4
  have hu1 : (d : ℝ) + 1 + (n0 : ℝ) ≤ ratioVal k0 d := hD1 d hdD1
  apply N_le_of_card_le hα0 hα1 (X := upperVal k0 d)
  intro n v hvnorm hvangle
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rcases hswitch (v := v) hvnorm hvangle with ⟨v', hvs, hdeg⟩
    have hv'norm : ∀ i : Fin n, ‖v' i‖ = 1 := by
      intro i
      rcases hvs i with hi | hi
      · rw [hi]
        exact hvnorm i
      · rw [hi]
        simpa using hvnorm i
    have hv'angle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v' i, v' j⟫| = α := by
      intro i j hij
      rcases hvs i with hi | hi <;> rcases hvs j with hj | hj
      · rw [hi, hj]
        exact hvangle hij
      · rw [hi, hj]
        simpa [inner_neg_right_eq, abs_neg] using hvangle hij
      · rw [hi, hj]
        simpa [inner_neg_left_eq, abs_neg] using hvangle hij
      · rw [hi, hj]
        simpa [inner_neg_left_eq, inner_neg_right_eq, abs_neg] using hvangle hij
    let G : SimpleGraph (Fin n) := assocGraph α v'
    have hA : (G.adjMatrix ℝ).IsHermitian := adjMatrix_isHermitian G
    by_cases hlamEig : ∃ j : Fin n, hA.eigenvalues j = lam α
    · by_cases hB1 : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal (lam α)
      · have hb := b1_bound (v := v') hα0 hα1 hn hv'norm hv'angle hk hB1
        have hnfl : n ≤ ⌊ratioVal k0 d⌋₊ := by
          apply nat_le_floor_of_real_le
          change (n : ℝ) ≤ ratioVal (spectralRadiusOrder (lam α)).toNat d
          exact hb
        exact hnfl
      · have hx : ∃ x : Fin n → ℝ, x ≠ 0 ∧ G.adjMatrix ℝ *ᵥ x = (lam α) • x :=
          eigenvector_of_eigenvalue_value hA hlamEig
        have htop := spectralRadius_eq_ofReal_top hn (G.adjMatrix ℝ) hA (adjMatrix_nonneg G)
        rcases htop with ⟨i, hρi, htopi⟩
        let ρ0 : ℝ := hA.eigenvalues i
        have hρ0 : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal ρ0 := by
          simpa [ρ0] using hρi
        have hlamLe : lam α ≤ ρ0 := by
          rcases hlamEig with ⟨j, hj⟩
          dsimp [ρ0]
          rw [← hj]
          exact htopi j
        have hne : lam α ≠ ρ0 := by
          intro heq
          apply hB1
          rw [hρ0, heq]
        have hlamRho : lam α < ρ0 := lt_of_le_of_ne hlamLe hne
        have hb2' := hb2 (v := v') (hn := hn) hv'norm hv'angle hdeg hx ⟨ρ0, hlamRho, hρ0⟩
        rcases hb2' with ⟨m, hnmd, hmcase⟩
        rcases hmcase with hmn0 | hmeps
        · have hnle : n ≤ d + 1 + n0 := by omega
          have hcr : (n : ℝ) ≤ (d : ℝ) + 1 + (n0 : ℝ) := by exact_mod_cast hnle
          have hleR : (n : ℝ) ≤ ratioVal k0 d := le_trans hcr hu1
          exact (nat_le_floor_of_real_le hleR)
        · have hcr : (n : ℝ) ≤ (d : ℝ) + 1 + (m : ℝ) := by exact_mod_cast hnmd
          have hle1 : (n : ℝ) * (1 - eps) ≤ (d : ℝ) + 1 := by
            nlinarith
          have hepslt : eps < 1 := by
            have hk0r : (2 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk2
            have hbig : (1 : ℝ) < 2 * (k0 : ℝ) := by nlinarith
            have hpos : 0 < 2 * (k0 : ℝ) := by positivity
            dsimp [eps]
            rwa [div_lt_one hpos]
          have h1e : 0 < 1 - eps := by linarith
          have hdiv : (n : ℝ) ≤ ((d : ℝ) + 1) / (1 - eps) := (le_div_iff₀ h1e).mpr hle1
          have huR' : ((d : ℝ) + 1) / (1 - eps) ≤ ratioVal k0 d := by
            simpa [eps] using huR
          have hleR : (n : ℝ) ≤ ratioVal k0 d := le_trans hdiv huR'
          exact (nat_le_floor_of_real_le hleR)
    · push Not at hlamEig
      let C : ConfigBounds α d := { N := n, v := v', norm := hv'norm, angle := hv'angle }
      have hcA : C.N ≤ d + 1 := ConfigBounds.upper_bound_caseA C hα0 hlamEig
      have hnle : n ≤ d + 1 := by simpa [C] using hcA
      exact le_trans hnle huA

/-- when the spectral radius order is infinite: eventually `N α d ≤ (1+ε)·d`. -/
theorem eventually_upper_infinite (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hk : spectralRadiusOrder (lam α) = (⊤ : ℕ∞)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop, (N α d : ℝ) ≤ (1 + ε) * (d : ℝ) := by
  classical
  intro ε hε
  let eps : ℝ := ε / (2 * (1 + ε))
  have h1pe : (0 : ℝ) < 1 + ε := by linarith
  have hpos2 : (0 : ℝ) < 2 * (1 + ε) := by positivity
  have hepspos : 0 < eps := by
    dsimp [eps]
    positivity
  have hepslt1 : eps < 1 := by
    dsimp [eps]
    rw [div_lt_iff₀ hpos2]
    nlinarith
  have h1e : 0 < 1 - eps := by linarith
  have hcoef : 1 < (1 - eps) * (1 + ε) := by
    dsimp [eps]
    field_simp [h1pe.ne']
    nlinarith
  rcases switch_bounded α hα0 hα1 with ⟨Δ, hswitch⟩
  rcases b2_bound (α := α) (Δ := Δ) hα0 hα1 eps hepspos with ⟨n0, hb2⟩
  rcases eventually_d_add_c_le_mul (1 : ℝ) ε hε with ⟨DA, hDA⟩
  rcases eventually_d_add_c_le_mul (1 + (n0 : ℝ)) ε hε with ⟨Dc1, hDc1⟩
  rcases eventually_d_add_one_le_mul_c0 ((1 - eps) * (1 + ε)) hcoef with ⟨Ddv, hDdv⟩
  let D : ℕ := max (max DA Dc1) Ddv
  rw [eventually_atTop]
  refine ⟨D, ?_⟩
  intro d hd
  have hdA : DA ≤ d := by omega
  have hd1 : Dc1 ≤ d := by omega
  have hddv : Ddv ≤ d := by omega
  have hcA : (d : ℝ) + 1 ≤ (1 + ε) * (d : ℝ) := hDA d hdA
  have hc1 : (d : ℝ) + 1 + (n0 : ℝ) ≤ (1 + ε) * (d : ℝ) := by
    have hh := hDc1 d hd1
    nlinarith
  have hdv : (d : ℝ) + 1 ≤ ((1 - eps) * (1 + ε)) * (d : ℝ) := hDdv d hddv
  have hnonneg : 0 ≤ (1 + ε) * (d : ℝ) := by positivity
  have hfam : ∀ {n : ℕ} (v : Fin n → Euc d), (∀ i, ‖v i‖ = 1) →
      (∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) → n ≤ ⌊(1 + ε) * (d : ℝ)⌋₊ := by
    intro n v hvnorm hvangle
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hn : 0 < n := Nat.pos_of_ne_zero hn0
      rcases hswitch (v := v) hvnorm hvangle with ⟨v', hvs, hdeg⟩
      have hv'norm : ∀ i : Fin n, ‖v' i‖ = 1 := by
        intro i
        rcases hvs i with hi | hi
        · rw [hi]
          exact hvnorm i
        · rw [hi]
          simpa using hvnorm i
      have hv'angle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v' i, v' j⟫| = α := by
        intro i j hij
        rcases hvs i with hi | hi <;> rcases hvs j with hj | hj
        · rw [hi, hj]
          exact hvangle hij
        · rw [hi, hj]
          simpa [inner_neg_right_eq, abs_neg] using hvangle hij
        · rw [hi, hj]
          simpa [inner_neg_left_eq, abs_neg] using hvangle hij
        · rw [hi, hj]
          simpa [inner_neg_left_eq, inner_neg_right_eq, abs_neg] using hvangle hij
      let G : SimpleGraph (Fin n) := assocGraph α v'
      have hA : (G.adjMatrix ℝ).IsHermitian := adjMatrix_isHermitian G
      by_cases hlamEig : ∃ j : Fin n, hA.eigenvalues j = lam α
      · by_cases hB1 : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal (lam α)
        · exfalso
          have hmem : n ∈ {k : ℕ | ∃ G0 : SimpleGraph (Fin k),
              spectralRadius ℝ (G0.adjMatrix ℝ) = ENNReal.ofReal (lam α)} := by
            exact ⟨G, hB1⟩
          have hnle : (spectralRadiusOrder (lam α) : ℕ∞) ≤ (n : ℕ∞) := by
            rw [spectralRadiusOrder]
            exact iInf₂_le (f := fun k : ℕ => fun _ : k ∈ {k : ℕ | ∃ G0 : SimpleGraph (Fin k),
              spectralRadius ℝ (G0.adjMatrix ℝ) = ENNReal.ofReal (lam α)} => (k : ℕ∞)) n hmem
          have htop : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by
            rwa [hk] at hnle
          exact (not_le_of_gt (WithTop.coe_lt_top n)) htop
        · have hx : ∃ x : Fin n → ℝ, x ≠ 0 ∧ G.adjMatrix ℝ *ᵥ x = (lam α) • x :=
            eigenvector_of_eigenvalue_value hA hlamEig
          have htop := spectralRadius_eq_ofReal_top hn (G.adjMatrix ℝ) hA (adjMatrix_nonneg G)
          rcases htop with ⟨i, hρi, htopi⟩
          let ρ0 : ℝ := hA.eigenvalues i
          have hρ0 : spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal ρ0 := by
            simpa [ρ0] using hρi
          have hlamLe : lam α ≤ ρ0 := by
            rcases hlamEig with ⟨j, hj⟩
            dsimp [ρ0]
            rw [← hj]
            exact htopi j
          have hne : lam α ≠ ρ0 := by
            intro heq
            apply hB1
            rw [hρ0, heq]
          have hlamRho : lam α < ρ0 := lt_of_le_of_ne hlamLe hne
          have hb2' := hb2 (v := v') (hn := hn) hv'norm hv'angle hdeg hx ⟨ρ0, hlamRho, hρ0⟩
          rcases hb2' with ⟨m, hnmd, hmcase⟩
          rcases hmcase with hmn0 | hmeps
          · have hnle : n ≤ d + 1 + n0 := by omega
            have hcr : (n : ℝ) ≤ (d : ℝ) + 1 + (n0 : ℝ) := by exact_mod_cast hnle
            have hreal : (n : ℝ) ≤ (1 + ε) * (d : ℝ) := le_trans hcr hc1
            exact (nat_le_floor_of_real_le hreal)
          · have hcr : (n : ℝ) ≤ (d : ℝ) + 1 + (m : ℝ) := by exact_mod_cast hnmd
            have hle1 : (n : ℝ) * (1 - eps) ≤ (d : ℝ) + 1 := by
              nlinarith
            have hdiv : (n : ℝ) ≤ ((d : ℝ) + 1) / (1 - eps) := (le_div_iff₀ h1e).mpr hle1
            have hdivmul : ((d : ℝ) + 1) / (1 - eps) ≤ (1 + ε) * (d : ℝ) := by
              rw [div_le_iff₀ h1e]
              nlinarith [hdv]
            have hreal : (n : ℝ) ≤ (1 + ε) * (d : ℝ) := le_trans hdiv hdivmul
            exact (nat_le_floor_of_real_le hreal)
      · push Not at hlamEig
        let C : ConfigBounds α d := { N := n, v := v', norm := hv'norm, angle := hv'angle }
        have hcA' : C.N ≤ d + 1 := ConfigBounds.upper_bound_caseA C hα0 hlamEig
        have hnle : n ≤ d + 1 := by simpa [C] using hcA'
        have hcr : (n : ℝ) ≤ (d : ℝ) + 1 := by exact_mod_cast hnle
        have hreal : (n : ℝ) ≤ (1 + ε) * (d : ℝ) := le_trans hcr hcA
        exact (nat_le_floor_of_real_le hreal)
  have hNle : N α d ≤ ⌊(1 + ε) * (d : ℝ)⌋₊ := N_le_of_card_le hα0 hα1 hfam
  have h1 : (N α d : ℝ) ≤ (⌊(1 + ε) * (d : ℝ)⌋₊ : ℝ) := by exact_mod_cast hNle
  have h2 : (⌊(1 + ε) * (d : ℝ)⌋₊ : ℝ) ≤ (1 + ε) * (d : ℝ) := Nat.floor_le hnonneg
  exact le_trans h1 h2

end
end Submission
