import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.DefsMP
import Submission.Work.BW.zeroDeg_reduce
import Submission.Work.BW.zero_estimate_stepwise
import Submission.Work.BW.ker_c_eq_span_B
import Submission.Work.BW.quotient_reduction
import Submission.Work.BW.finrank_lieSub
import Submission.Work.BW.transversal_exclusion_spec
import Submission.Work.BW.cardMod_true_of_linearIndependent
import Submission.Work.BW.multiplicity_engine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem B_eq_zero_of_deg_lt_one {r : ℕ} (hr : 2 ≤ r) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : P ≠ 0) (𝒟 : Fin (r + 1) → ℝ) (hdeg : ∀ j, (P.degreeOf j : ℝ) ≤ 𝒟 j)
    (h𝒟0 : 1 ≤ 𝒟 0) (𝒮 𝒯 : ℝ) (Sq Tq : ℕ → ℕ)
    (hSa : ∀ m, m < r → Sq (m + 1) ≤ Sq m) (hTa : ∀ m, m < r → Tq (m + 1) ≤ Tq m)
    (hSsum : ((∑ m ∈ Finset.range (r + 1), Sq m : ℕ) : ℝ) ≤ 𝒮)
    (hTsum : ((∑ m ∈ Finset.range (r + 1), Tq m : ℕ) : ℝ) ≤ 𝒯)
    (hE0 : ∀ j : Fin r, ((r : ℝ) + 1) * 𝒟 j.succ < (Tq 0 : ℝ) + 1)
    (hE1 : ∀ m, m < r → ∀ e : Fin (r + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, 𝒟 i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ))
    (hE2 : ((r + 1).factorial : ℝ) * ∏ i, 𝒟 i < ((Sq r : ℝ) + 1) * ((Tq r + r).choose r : ℝ))
    (hE3 : ((r + 1).factorial : ℝ) * ∏ i : Fin r, 𝒟 i.succ <
      ((Sq (r - 1) : ℝ) + 1) * ((Tq (r - 1) + (r - 1)).choose (r - 1) : ℝ))
    (B : Fin r → ℤ) (hB : B ≠ 0) (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0) (ℓ : Fin r → ℂ) (hℓ : LinearIndependent ℚ ℓ)
    (hΛ : ‖∑ i, (B i : ℂ) * ℓ i‖ < Real.pi / 𝒮)
    (hvan : ∀ s : ℕ, (s : ℝ) ≤ 𝒮 → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ 𝒯 →
      MvPolynomial.eval (ptS ℓ s) (applyDer c t0 t P) = 0)
    (i : Fin r) (hi : 𝒟 i.succ < 1) :
    B i = 0 := by
  classical
  by_contra hBi
  -- linear algebra: the kernel of `c` is spanned by `B`
  have hker := ker_c_eq_span_B c hc B hB hcB
  -- reduce to the quotient polytope
  obtain ⟨N', σ, P', δ, w, hN'lt, hσinj, hi_range, hP'ne, hδnn, hδ0, hδ1, hdeg',
      hspan, hδeq, hw1, hw0, hvan'⟩ :=
    quotient_reduction P hP 𝒟 hdeg h𝒟0 Sq Tq 𝒮 𝒯 hSsum hTsum c B hB hker ℓ hvan i hi hBi
  have hSa' : ∀ m, m < N' → Sq (m + 1) ≤ Sq m := fun m hm => hSa m (by omega)
  have hTa' : ∀ m, m < N' → Tq (m + 1) ≤ Tq m := fun m hm => hTa m (by omega)
  -- the exclusions (E0), (E1) in the quotient
  have hE0δ : ∀ j : Fin N', ((r : ℝ) + 1) * δ j.succ < (Tq 0 : ℝ) + 1 := by
    intro j
    rw [hδeq j.succ, zeroDeg_liftIdx_succ]
    exact hE0 (σ j)
  have hE1δ : ∀ m, m < r → ∀ e : Fin (N' + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ) := by
    intro m hm e he hsum
    have hInj : Function.Injective (liftIdx σ) := zeroDeg_liftIdx_injective hσinj
    let e' : Fin (r + 1) → ℕ := Function.extend (liftIdx σ) e (fun _ => 0)
    have happ : ∀ j : Fin (N' + 1), e' (liftIdx σ j) = e j :=
      fun j => Function.Injective.extend_apply hInj e (fun _ => 0) j
    have hzero : ∀ i : Fin (r + 1), i ∉ Set.range (liftIdx σ) → e' i = 0 :=
      fun i hi => Function.extend_apply' e (fun _ => 0) i hi
    have he'1 : ∀ i, e' i ≤ 1 := by
      intro i
      by_cases h : ∃ j, liftIdx σ j = i
      · obtain ⟨j, rfl⟩ := h; rw [happ j]; exact he j
      · rw [hzero i (by rintro ⟨j, hj⟩; exact h ⟨j, hj⟩)]; omega
    have he'sum : ∑ i, e' i = m + 1 := by
      rw [show (∑ i : Fin (r + 1), e' i) = ∑ j : Fin (N' + 1), e' (liftIdx σ j) from
        zeroDeg_sum_range_eq (liftIdx σ) hInj e' hzero]
      rw [Finset.sum_congr rfl (fun j _ => happ j), hsum]
    have hprod : ∏ i : Fin (r + 1), 𝒟 i ^ e' i = ∏ i : Fin (N' + 1), δ i ^ e i := by
      have h1 : ∏ i : Fin (r + 1), 𝒟 i ^ e' i =
          ∏ i ∈ (Finset.univ.filter (fun i : Fin (r + 1) => i ∈ Set.range (liftIdx σ))),
            𝒟 i ^ e' i :=
        (Finset.prod_subset (Finset.filter_subset _ _) (fun i _ hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [hzero i hi, pow_zero])).symm
      have h2 : (Finset.univ.filter (fun i : Fin (r + 1) => i ∈ Set.range (liftIdx σ))) =
          (Finset.univ : Finset (Fin (N' + 1))).map ⟨liftIdx σ, hInj⟩ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Function.Embedding.coeFn_mk, Set.mem_range]
      rw [h1, h2, Finset.prod_map]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Function.Embedding.coeFn_mk, happ j, hδeq j]
    rw [← hprod]
    exact hE1 m hm e' he'1 he'sum
  -- the operator family does not depend on the reduced coordinates' multipliers
  obtain ⟨ε, ρ, M', hρN, hM'prim, hε, m, hm, hineq0⟩ :=
    zero_estimate_stepwise (N := N') (q := r - 1 + 1) P' hP'ne (fun j => ⌊δ j⌋₊) hδ1 hdeg'
      w (fun j => Complex.exp (ℓ (σ j))) (fun j => Complex.exp_ne_zero _) Sq Tq hvan'
  -- the transversality: `ellW = k`
  have hLk : ellW w ε M' = (if ε then 0 else 1) + ρ := by
    have h1 : (Submodule.span ℂ (Set.range w) : Submodule ℂ (Fin (N' + 1) → ℂ)) = ⊤ := hspan
    rw [ellW, h1, top_inf_eq, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
      finrank_lieSub hρN M' hM'prim.1 ε]
    rcases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hineq : ∀ (J : Finset (Fin N')) (hJ : J.card = ρ), minorJ M' J hJ ≠ 0 →
      (((Tq m + ((if ε then 0 else 1) + ρ)).choose ((if ε then 0 else 1) + ρ) : ℕ) : ℝ) *
          (cardMod ε M' (fun j => Complex.exp (ℓ (σ j))) (Sq m) : ℝ) *
        ((N' + 1 - ((if ε then 0 else 1) + ρ)).factorial : ℝ) * |(minorJ M' J hJ : ℝ)| *
        (if ε then ((⌊δ 0⌋₊ : ℕ) : ℝ) else 1) *
          ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N' + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ) := by
    intro J hJ hΔ
    have h := hineq0 J hJ hΔ
    rwa [hLk] at h
  -- the cardinality bounds on `cardMod`
  have hℓσ : LinearIndependent ℚ (fun j : Fin N' => ℓ (σ j)) := hℓ.comp σ hσinj
  have hcard : (ε = false → Sq m + 1 ≤ cardMod false M' (fun j => Complex.exp (ℓ (σ j))) (Sq m)) ∧
      (2 ≤ ρ → Sq m + 1 ≤ cardMod true M' (fun j => Complex.exp (ℓ (σ j))) (Sq m)) ∧
      (1 ≤ cardMod true M' (fun j => Complex.exp (ℓ (σ j))) (Sq m)) := by
    refine ⟨fun _ => ?_, fun hρ2 => ?_, ?_⟩
    · rw [cardMod_false]
    · rw [cardMod_true_of_linearIndependent hρ2 M' hM'prim.1 (fun j => ℓ (σ j)) hℓσ]
    · exact one_le_cardMod true M' (fun j => Complex.exp (ℓ (σ j))) (Sq m)
  exact (transversal_exclusion_spec hr hN'lt δ hδnn hδ0 hδ1 Sq Tq hSa' hTa' hE0δ hE1δ
    (fun j => Complex.exp (ℓ (σ j))) ε ρ M' m hρN hM'prim hε hm hcard hineq).elim

end Work.BW
