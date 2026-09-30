import Mathlib
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.est17_gexp
import Submission.Work.BW.est13p
import Submission.Work.BW.est14
import Submission.Work.BW.est_Pi
import Submission.Work.BW.num_13
import Submission.Work.BW.num_T
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.ulcm_le_three_pow
import Submission.Work.BW.acH_lower
import Submission.Work.BW.sigma_ge
import Submission.Work.BW.est17_arch_rat_le
import Submission.Work.BW.est17_arch_num
import Submission.Work.BW.rhoE_zpow_w_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField





/-- Triangle inequality for a finite sum and an infinite place. -/
lemma w_sum_le {K : Type*} [Field K] [NumberField K] (w : NumberField.InfinitePlace K)
    {ι : Type*} [Fintype ι] (f : ι → K) : w (∑ i, f i) ≤ ∑ i, w (f i) := by
  classical
  have key : ∀ s : Finset ι, w.1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, w.1 (f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        calc w.1 (f a + ∑ i ∈ s, f i) ≤ w.1 (f a) + w.1 (∑ i ∈ s, f i) := w.1.add_le _ _
          _ ≤ w.1 (f a) + ∑ i ∈ s, w.1 (f i) := add_le_add le_rfl ih
  exact key Finset.univ

/-- An infinite place takes the canonical archimedean value on `ℚ`: `w (algebraMap ℚ K q) = ‖q‖`. -/
lemma w_algebraMap_rat {K : Type*} [Field K] [NumberField K] (w : NumberField.InfinitePlace K)
    (q : ℚ) : w (algebraMap ℚ K q) = ‖(q : ℂ)‖ := by
  rw [← NumberField.InfinitePlace.norm_embedding_eq w (algebraMap ℚ K q)]
  have h : w.embedding ((algebraMap ℚ K) q) = ((algebraMap ℚ ℂ) q) := by
    have h2 : w.embedding.comp (algebraMap ℚ K) = (algebraMap ℚ ℂ) := Subsingleton.elim _ _
    exact congr_fun (congrArg DFunLike.coe h2) q
  rw [h]
  rfl

/-- Archimedean upper bound for `g(s/2)` at a place `w ≠ w₀` of the Kummer extension
`L = ℚ(φ(K), ρ)`: `w g(s/2) ≤ (max_λ w(φ(p λ))) · exp(hT* + (0.203 + 0.007|z|/S)SD/d + log N + |z|·Ω_w)`,
where `z = |s|/2^{J+1}`, `N = h(D₀+1)∏(D_j+1)` is the number of summands and
`Ω_w = Σ_j D_j log⁺ w(α'_j^{sign s})` (sign-aware: `w(α'_j)` for `s ≥ 0`, `w(α'_j)⁻¹` for `s ≤ 0`;
both have the same total height `logHeight₁ (α'_j)`). The rational factors `Δ(γ;t)`, `ulcm^{t₀}`,
`Θ` are bounded by `est_Pi`/`est_Theta_yu`/`num_13`; they are independent of the place, so only
`max_λ w(φ(p λ))` and `Ω_w` are place-dependent. -/
theorem est17_arch {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {Lm : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σl : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) → K}
    (H : ACHyp φ α b k c v Lm α' σl ι p) (J : ℕ) (μ : Fin r → ℕ) (Tst : ℝ)
    (hTst : Tst ≤ acT K σl) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    [inst : NumberField (EL φ (rhoC φ α v Lm))]
    (hmem : acg φ α b k Lm ι v σl p J μ t0 t ((s : ℂ) / 2) ∈ (EL φ (rhoC φ α v Lm) : Set ℂ))
    (w : NumberField.InfinitePlace (EL φ (rhoC φ α v Lm))) (hw : w ≠ w0 φ (rhoC φ α v Lm)) :
    w (gamE α v Lm φ b k p J μ t0 t s hmem) ≤
      (⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm))) * Real.exp (
        (acH K b v : ℝ) * Tst
        + (0.203 + 0.007 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / acS K r b v))
            * acS K r b v * acD K σl / (dK K : ℝ)
        + Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * ∏ j, ((pDj r (dK K) σl j : ℝ) + 1))
        + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σl j : ℝ)
            * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
               else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)  := by
  classical
  have hr2 : 2 ≤ r := H.hr
  have hd1 : 1 ≤ dK K := one_le_dK
  have hσ : ∀ j : Fin r, 1 / (dK K : ℝ) ≤ σl j := fun j => sigma_ge H j
  have hh19 : 19 ≤ acH K b v := (acH_lower H).1
  have hznn : 0 ≤ (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) := by positivity
  have hSpos : (0:ℝ) < acS K r b v := by
    show (0:ℝ) < (pS r (dK K) (acH K b v) : ℝ)
    have h : (0:ℕ) < pS r (dK K) (acH K b v) := by
      show (0:ℕ) < 16 * r * dK K * acH K b v
      positivity
    exact_mod_cast h
  have hexp : ∀ j : Fin r, Complex.exp (lamP φ α v Lm j) = φ (α' j) :=
    fun j => (H.hBH.2.2.1 j).2
  -- the numerical comparison of the exponent increments
  have hnum : 0.1 * (acH K b v : ℝ) * acT K σl + Real.log 1.7 * acT K σl
      + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ)))
            * (acH K b v : ℝ)
          + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ)))
          * ((pD0 r (dK K) σl : ℝ) + 1)
      ≤ 0.203 * acS K r b v * acD K σl / (dK K : ℝ)
        + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) :=
    est17_arch_num hr2 (dK K) (acH K b v) hd1 hh19 σl hσ (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) hznn
  -- the place-dependent maximum is attained (AuxIdx is nonempty)
  have hsup_bdd : BddAbove (Set.range fun lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl) =>
      w (inclE φ (rhoC φ α v Lm) (p lm))) := (Set.finite_range _).bddAbove
  have hsup_nn : 0 ≤ ⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm)) := by
    have hmem : w (inclE φ (rhoC φ α v Lm) (p ⟨⟨0, by omega⟩, ⟨0, Nat.succ_pos _⟩, fun j => ⟨0, Nat.succ_pos _⟩⟩))
        ≤ ⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm)) := le_ciSup hsup_bdd _
    exact le_trans (w.1.nonneg _) hmem
  -- ### per-summand estimate
  have hterm : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl),
      w (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
          inclE φ (rhoC φ α v Lm) (p lm)
            * algebraMap ℚ (EL φ (rhoC φ α v Lm)) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))
            * ∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J))
        else 0)
      ≤ (⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm))) * Real.exp ((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) := by
    intro lm
    by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
    · rw [if_pos hc]
      have hq : w (algebraMap ℚ (EL φ (rhoC φ α v Lm)) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))) ≤ Real.exp ((acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * acT K σl + Real.log 1.7 * acT K σl + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ))) * ((pD0 r (dK K) σl : ℝ) + 1)) := by
        rw [w_algebraMap_rat]
        change ‖(algebraMap ℚ ℂ) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))‖ ≤ Real.exp ((acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * acT K σl + Real.log 1.7 * acT K σl + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ))) * ((pD0 r (dK K) σl : ℝ) + 1))
        rw [est17_rat_map J t0 t s lm]
        exact est17_arch_rat_le H J Tst hTst t0 t ht s lm
      have hρ : w (∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
          ≤ Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) := by
        have hstep : ∀ j : Fin r,
            w (rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
              ≤ Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) := by
          intro j
          have he : (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * (2 : ℝ) ^ J
              ≤ (pDj r (dK K) σl j : ℝ) := by
            have h1 : ((lm.2.2 j : ℕ) / 2 ^ J) * 2 ^ J ≤ (lm.2.2 j : ℕ) :=
              Nat.div_mul_le_self _ _
            have h2 : (lm.2.2 j : ℕ) ≤ pDj r (dK K) σl j :=
              Nat.lt_succ_iff.mp (lm.2.2 j).isLt
            calc (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℝ) * (2 : ℝ) ^ J
                = ((((lm.2.2 j : ℕ) / 2 ^ J) * 2 ^ J : ℕ) : ℝ) := by push_cast; ring
              _ ≤ ((lm.2.2 j : ℕ) : ℝ) := by exact_mod_cast h1
              _ ≤ (pDj r (dK K) σl j : ℝ) := by exact_mod_cast h2
          have hmain := rhoE_zpow_w_le hexp w J j s ((lm.2.2 j : ℕ) / 2 ^ J)
            ((pDj r (dK K) σl j : ℝ)) (by positivity) he
          rw [map_zpow₀]
          exact hmain
        rw [map_prod]
        calc ∏ j, w (rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
            ≤ ∏ j, Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) :=
              Finset.prod_le_prod₀ (fun j _ => (w.1.nonneg _)) (fun j _ => hstep j)
          _ = Real.exp (∑ j, (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) := by
              rw [← Real.exp_sum Finset.univ]
          _ = Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) := by
              congr 1
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring)
      have hwT : w (inclE φ (rhoC φ α v Lm) (p lm)
            * algebraMap ℚ (EL φ (rhoC φ α v Lm)) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))
            * ∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
          = w (inclE φ (rhoC φ α v Lm) (p lm))
            * w (algebraMap ℚ (EL φ (rhoC φ α v Lm)) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))))
            * w (∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J))) := by
        rw [map_mul, map_mul]
      rw [hwT]
      calc w (inclE φ (rhoC φ α v Lm) (p lm))
              * w (algebraMap ℚ (EL φ (rhoC φ α v Lm)) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1)))))
              * w (∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J)))
          ≤ w (inclE φ (rhoC φ α v Lm) (p lm)) * Real.exp ((acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * acT K σl + Real.log 1.7 * acT K σl + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ))) * ((pD0 r (dK K) σl : ℝ) + 1))
              * Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hq (w.1.nonneg _)
            · exact hρ
            · positivity
            · exact mul_nonneg (w.1.nonneg _) (Real.exp_pos _).le
        _ = w (inclE φ (rhoC φ α v Lm) (p lm))
              * Real.exp (((acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * acT K σl + Real.log 1.7 * acT K σl + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ))) * ((pD0 r (dK K) σl : ℝ) + 1)) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) := by
            rw [show Real.exp (((acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * acT K σl + Real.log 1.7 * acT K σl + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ))) * ((pD0 r (dK K) σl : ℝ) + 1)) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog))
                = Real.exp (((acH K b v : ℝ) * Tst + 0.1 * (acH K b v : ℝ) * acT K σl + Real.log 1.7 * acT K σl + ((Real.log (57 * (r : ℝ) * (dK K : ℝ)) + 3 / (57 * (r : ℝ) * (dK K : ℝ))) * (acH K b v : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / (57 * (r : ℝ) * (dK K : ℝ))) * ((pD0 r (dK K) σl : ℝ) + 1))) * Real.exp ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) from Real.exp_add _ _]
            ring
        _ ≤ w (inclE φ (rhoC φ α v Lm) (p lm)) * Real.exp ((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (w.1.nonneg _)
            linarith [hnum]
        _ ≤ (⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm))) * Real.exp ((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) := by
            have hle : w (inclE φ (rhoC φ α v Lm) (p lm))
                ≤ ⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm)) := le_ciSup hsup_bdd lm
            exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    · rw [if_neg hc, map_zero]
      exact mul_nonneg hsup_nn (Real.exp_pos _).le
  -- ### assembly
  have hcard : ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) : ℕ) : ℝ)
      = (acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
        * ∏ j, ((pDj r (dK K) σl j : ℝ) + 1) := by
    simp only [AuxIdx, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, Nat.cast_prod]
    try ring
  have hcardpos : (0:ℝ) < ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) : ℕ) : ℝ) := by
    rw [hcard]
    have h2 : (0:ℝ) < ((pD0 r (dK K) σl : ℝ) + 1) := by positivity
    have h3 : (0:ℝ) < ∏ j, ((pDj r (dK K) σl j : ℝ) + 1) :=
      Finset.prod_pos (fun j _ => by positivity)
    have h1 : (0:ℝ) < (acH K b v : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hh19)
    positivity
  have hgap : (0.203 + 0.007 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / acS K r b v)) * acS K r b v * acD K σl / (dK K : ℝ)
      = 0.203 * acS K r b v * acD K σl / (dK K : ℝ)
        + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) := by
    have hS : acS K r b v ≠ 0 := ne_of_gt hSpos
    field_simp
    try ring
  have hfinal : ((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) + Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) : ℕ) : ℝ) = 
        (acH K b v : ℝ) * Tst
        + (0.203 + 0.007 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / acS K r b v))
            * acS K r b v * acD K σl / (dK K : ℝ)
        + Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * ∏ j, ((pDj r (dK K) σl j : ℝ) + 1))
        + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σl j : ℝ)
            * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
               else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog := by
    rw [hcard, hgap]
    ring
  rw [est17_gexp H J μ t0 t s hmem]
  calc w (∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl),
          if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
            inclE φ (rhoC φ α v Lm) (p lm)
              * algebraMap ℚ (EL φ (rhoC φ α v Lm)) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))
              * ∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J))
          else 0)
      ≤ ∑ lm, w (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
            inclE φ (rhoC φ α v Lm) (p lm)
              * algebraMap ℚ (EL φ (rhoC φ α v Lm)) ((∏ m, Polynomial.aeval (((∑ i, derVec b k Lm (ι m) i * (lm.2.2 i : ℤ)) : ℤ) : ℚ) (deltaPoly (t m))) * (ulcm (acH K b v) : ℚ) ^ t0 * Polynomial.aeval ((s : ℚ) / 2 / 2 ^ J + (lm.1 : ℕ)) (Polynomial.hasseDeriv t0 (deltaPoly (acH K b v) ^ ((lm.2.1 : ℕ) + 1))))
              * ∏ j, rhoE φ (rhoC φ α v Lm) j ^ (s * ((lm.2.2 j : ℕ) / 2 ^ J))
          else 0) := w_sum_le w _
    _ ≤ ∑ lm, (⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm))) * Real.exp ((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) :=
        Finset.sum_le_sum (fun lm _ => hterm lm)
    _ = ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) : ℕ) : ℝ) * ((⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm))) * Real.exp ((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm)))
          * Real.exp (((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) + Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) : ℕ) : ℝ)) := by
        rw [show Real.exp (((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog)) + Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) : ℕ) : ℝ))
              = Real.exp (((acH K b v : ℝ) * Tst + 0.203 * acS K r b v * acD K σl / (dK K : ℝ) + 0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σl / (dK K : ℝ) + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * (∑ j, (pDj r (dK K) σl j : ℝ) * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j)) else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog))) * Real.exp (Real.log ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σl) (pDj r (dK K) σl)) : ℕ) : ℝ)) from Real.exp_add _ _,
            Real.exp_log hcardpos]
        ring
    _ = (⨆ lm, w (inclE φ (rhoC φ α v Lm) (p lm))) * Real.exp (
        (acH K b v : ℝ) * Tst
        + (0.203 + 0.007 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / acS K r b v))
            * acS K r b v * acD K σl / (dK K : ℝ)
        + Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σl : ℝ) + 1)
            * ∏ j, ((pDj r (dK K) σl j : ℝ) + 1))
        + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σl j : ℝ)
            * (if 0 ≤ s then w (inclE φ (rhoC φ α v Lm) (α' j))
               else (w (inclE φ (rhoC φ α v Lm) (α' j)))⁻¹).posLog) := by rw [hfinal]


end Work.BW
