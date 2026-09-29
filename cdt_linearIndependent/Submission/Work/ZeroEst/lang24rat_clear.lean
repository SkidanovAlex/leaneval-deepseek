import Mathlib
import Submission.Work.ZeroEst.one_var_defs
import Submission.Work.ZeroEst.lang24_rank
import Submission.Work.ZeroEst.lang24_cramer
import Submission.Work.ZeroEst.lamdeg

/-!
# `Work.ZeroEst.lang24rat_clear` — Lang's Lemma 2.4 (cleared form) from `lamdeg`

`lamdeg` gives bounded rational dependence coefficients of the `Λ`-orbit matrix; clearing the
denominators (multiplying by the product `G` of all the `denom`'s) gives the polynomial form with
degrees bounded independently of `P`.
-/

namespace Work.ZeroEst

open Polynomial Matrix

theorem lang24rat_clear (m : ℕ) (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ) (hq : q ≠ 0) :
    ∃ N : ℕ, ∀ (P : Fin m → Polynomial ℚ),
      ¬ LinearIndependent (RatFunc ℚ)
        (fun k : Fin m => (fun i => ((orbit q A P k) i : RatFunc ℚ))) →
      ∃ (r : ℕ) (_ : r < m) (V k0 : Fin r → Fin m) (G : Polynomial ℚ)
        (B : Fin r → Fin m → Polynomial ℚ),
        Function.Injective V ∧
        (Matrix.of (fun a b : Fin r => orbit q A P (k0 a) (V b))).det ≠ 0 ∧
        G ≠ 0 ∧ G.degree ≤ (N : WithBot ℕ) ∧
        (∀ l j, (B l j).degree ≤ (N : WithBot ℕ)) ∧
        (∀ k, k < m → ∀ j, (∀ l, V l ≠ j) →
          G * orbit q A P k j = ∑ l, B l j * orbit q A P k (V l)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := lamdeg m q A hq
  refine ⟨4 * (m * (m * N₀)) + 2 * N₀ + 4, ?_⟩
  intro P hdep
  set Mp : Matrix (Fin m) (Fin m) (Polynomial ℚ) := Matrix.of (fun k j => orbit q A P k j) with hMp
  set f' : Polynomial ℚ →+* RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ) with hf'
  have hdep' : ¬ LinearIndependent (RatFunc ℚ) (Mp.map f').row := hdep
  obtain ⟨r, hr, V, k0, hVinj, hkinj, hdetR, hspan⟩ := lang24_rank (Mp.map f') hdep'
  obtain ⟨lam, hcol, _hcramer⟩ := lang24_cramer (Mp.map f') V k0 hdetR hspan
  have hdetP : (Matrix.of (fun a b : Fin r => orbit q A P (k0 a) (V b))).det ≠ 0 := by
    intro hz
    have hsub : (Matrix.of (fun a b : Fin r => orbit q A P (k0 a) (V b))) = Mp.submatrix k0 V := by
      ext a b; simp [hMp, Matrix.submatrix_apply]
    have hdetcoe : ((Mp.submatrix k0 V).det : RatFunc ℚ)
        = ((Mp.map f').submatrix k0 V).det := by
      rw [Matrix.submatrix_map]
      exact RingHom.map_det f' (Mp.submatrix k0 V)
    rw [hsub] at hz
    exact hdetR (by rw [← hdetcoe, hz]; simp)
  have hrel : ∀ k, k < m → ∀ j, ((orbit q A P k j : Polynomial ℚ) : RatFunc ℚ)
      = ∑ l, lam l j * ((orbit q A P k (V l) : Polynomial ℚ) : RatFunc ℚ) := by
    intro k hk j
    have h := hcol j ⟨k, hk⟩
    simpa [hMp, hf', Matrix.map_apply, Matrix.of_apply] using h
  have hnum : ∀ l j, ((lam l j).num).degree ≤ (N₀ : WithBot ℕ) :=
    fun l j => (hN₀ P r V k0 lam hdetP hrel l j).1
  have hden : ∀ l j, ((lam l j).denom).degree ≤ (N₀ : WithBot ℕ) :=
    fun l j => (hN₀ P r V k0 lam hdetP hrel l j).2
  let G : Polynomial ℚ := ∏ p : Fin r × Fin m, (lam p.1 p.2).denom
  let B : Fin r → Fin m → Polynomial ℚ := fun l j =>
    (lam l j).num * ∏ p ∈ (Finset.univ.erase (l, j)), (lam p.1 p.2).denom
  have hclear : ∀ l j, (G : RatFunc ℚ) * lam l j = (B l j : RatFunc ℚ) := by
    intro l j
    let D : Polynomial ℚ := (lam l j).denom
    let N : Polynomial ℚ := (lam l j).num
    let C : Polynomial ℚ := ∏ p ∈ (Finset.univ.erase (l, j)), (lam p.1 p.2).denom
    have hD : D = (lam l j).denom := rfl
    have hN : N = (lam l j).num := rfl
    have hC : C = ∏ p ∈ (Finset.univ.erase (l, j)), (lam p.1 p.2).denom := rfl
    have hGpoly : G = C * D := by
      rw [show G = ∏ p : Fin r × Fin m, (lam p.1 p.2).denom from rfl, hC, hD]
      exact (Finset.prod_erase_mul Finset.univ
        (fun p : Fin r × Fin m => (lam p.1 p.2).denom) (Finset.mem_univ (l, j))).symm
    have hBpoly : B l j = N * C := by
      rw [show B l j = (lam l j).num
        * ∏ p ∈ (Finset.univ.erase (l, j)), (lam p.1 p.2).denom from rfl, hN, hC]
    have hne : (D : RatFunc ℚ) ≠ 0 := by
      rw [hD]
      intro h
      exact RatFunc.denom_ne_zero (lam l j)
        (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) (by simpa using h))
    have hnumden : (D : RatFunc ℚ) * lam l j = (N : RatFunc ℚ) := by
      rw [← RatFunc.num_div_denom (lam l j)]
      exact mul_div_cancel₀ _ hne
    rw [show ∀ r₀ : Polynomial ℚ, (r₀ : RatFunc ℚ)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) r₀ from fun r₀ => rfl]
    simp only [hGpoly, hBpoly, map_mul]
    rw [show algebraMap (Polynomial ℚ) (RatFunc ℚ) C * algebraMap (Polynomial ℚ) (RatFunc ℚ) D * lam l j
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) C
          * (algebraMap (Polynomial ℚ) (RatFunc ℚ) D * lam l j) from by ring]
    rw [show algebraMap (Polynomial ℚ) (RatFunc ℚ) D * lam l j = (D : RatFunc ℚ) * lam l j from rfl,
      hnumden,
      show ((N * C : Polynomial ℚ) : RatFunc ℚ)
        = (N : RatFunc ℚ) * (C : RatFunc ℚ) from
        map_mul (algebraMap (Polynomial ℚ) (RatFunc ℚ)) N C]
    rw [show algebraMap (Polynomial ℚ) (RatFunc ℚ) C = (C : RatFunc ℚ) from rfl]
    exact mul_comm _ _
  refine ⟨r, hr, V, k0, G, B, hVinj, hdetP, ?_, ?_, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (fun p _ => RatFunc.denom_ne_zero _)
  · -- degree of `G`
    have h1 : G.natDegree ≤ (r * m) * N₀ := by
      rw [show G = ∏ p : Fin r × Fin m, (lam p.1 p.2).denom from rfl]
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      calc ∑ p : Fin r × Fin m, ((lam p.1 p.2).denom).natDegree
          ≤ ∑ _p : Fin r × Fin m, N₀ :=
            Finset.sum_le_sum (fun p _ => Polynomial.natDegree_le_iff_degree_le.mpr (hden p.1 p.2))
        _ = (r * m) * N₀ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
            simp
    refine (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr h1)).trans ?_
    refine WithBot.coe_le_coe.mpr ?_
    calc (r * m) * N₀ ≤ (m * m) * N₀ :=
          Nat.mul_le_mul_right N₀ (Nat.mul_le_mul_right m (by omega))
      _ ≤ 4 * (m * (m * N₀)) + 2 * N₀ + 4 := by
          have : (m * m) * N₀ = m * (m * N₀) := by ring
          omega
  · -- degrees of `B`
    intro l j
    have hnum4 : ((lam l j).num).natDegree ≤ N₀ :=
      Polynomial.natDegree_le_iff_degree_le.mpr (hnum l j)
    have h3 : (∏ p ∈ (Finset.univ.erase (l, j)), (lam p.1 p.2).denom).natDegree
        ≤ (r * m) * N₀ := by
      calc (∏ p ∈ (Finset.univ.erase (l, j)), (lam p.1 p.2).denom).natDegree
          ≤ ∑ p ∈ (Finset.univ.erase (l, j)), ((lam p.1 p.2).denom).natDegree :=
            Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ _p ∈ (Finset.univ.erase (l, j)), N₀ :=
            Finset.sum_le_sum (fun p _ => Polynomial.natDegree_le_iff_degree_le.mpr (hden p.1 p.2))
        _ ≤ ∑ _p : Fin r × Fin m, N₀ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) ?_
            intro p _ _; exact Nat.zero_le _
        _ = (r * m) * N₀ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul]
            simp
    have h1 : (B l j).natDegree ≤ N₀ + (r * m) * N₀ := by
      rw [show B l j = (lam l j).num * ∏ p ∈ (Finset.univ.erase (l, j)), (lam p.1 p.2).denom
        from rfl]
      exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add hnum4 h3)
    refine (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr h1)).trans ?_
    refine WithBot.coe_le_coe.mpr ?_
    calc N₀ + (r * m) * N₀ ≤ N₀ + (m * m) * N₀ :=
          Nat.add_le_add_left (Nat.mul_le_mul_right N₀ (Nat.mul_le_mul_right m (by omega))) N₀
      _ ≤ 4 * (m * (m * N₀)) + 2 * N₀ + 4 := by
          have : (m * m) * N₀ = m * (m * N₀) := by ring
          omega
  · -- the relation
    intro k hk j hj
    apply RatFunc.algebraMap_injective ℚ
    have h1 := hrel k hk j
    rw [show ∀ r₀ : Polynomial ℚ, (r₀ : RatFunc ℚ)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) r₀ from fun r₀ => rfl] at h1
    simp only [map_mul, map_sum] at h1 ⊢
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show ∀ r₀ : Polynomial ℚ, algebraMap (Polynomial ℚ) (RatFunc ℚ) r₀ = (r₀ : RatFunc ℚ)
        from fun r₀ => rfl]
    rw [← mul_assoc, hclear l j]
    simp only [show ∀ r₀ : Polynomial ℚ, algebraMap (Polynomial ℚ) (RatFunc ℚ) r₀
        = (r₀ : RatFunc ℚ) from fun r₀ => rfl]

end Work.ZeroEst
