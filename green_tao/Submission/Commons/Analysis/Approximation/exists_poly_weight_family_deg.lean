import Mathlib
import Submission.Commons.Analysis.Approximation.exists_poly_weight_family

noncomputable section
open Finset
open scoped BigOperators

namespace Commons.Analysis.Approximation

/-! ## Degree bounds for the shifted one-variable polynomials

The main theorem `exists_poly_weight_family` already builds
`P c = ∏ j, shiftPoly Q j (c j)` from a *fixed* bivariate polynomial `Q`.
Here we record that this construction has a **uniform total degree bound**:
each factor `shiftPoly Q j u` has total degree at most `Q.totalDegree`, and a
product of `K` such factors has total degree at most `K * Q.totalDegree`. -/

lemma totalDegree_shiftPoly_le {K : ℕ} (Q : MvPolynomial (Fin 2) ℝ) (j : Fin K) (u : ℝ) :
    (shiftPoly Q j u).totalDegree ≤ Q.totalDegree := by
  rw [shiftPoly]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  refine le_trans (MvPolynomial.totalDegree_monomial_le (Finsupp.single j (m (1 : Fin 2))) _) ?_
  have h1 : (Finsupp.single j (m (1 : Fin 2))).sum (fun x => id) = m (1 : Fin 2) :=
    Finsupp.sum_single_index (h := fun x => id) rfl
  have h2 : m (1 : Fin 2) ≤ Q.totalDegree := by
    have hd := Finsupp.le_degree (1 : Fin 2) m
    have hdeg : m.degree = m.sum (fun _ e => e) := Finsupp.degree_apply m
    rw [hdeg] at hd
    exact le_trans hd (MvPolynomial.le_totalDegree hm)
  rw [h1]; exact h2

lemma totalDegree_prod_shiftPoly_le {K : ℕ} (Q : MvPolynomial (Fin 2) ℝ) (c : Fin K → ℝ) :
    (∏ j : Fin K, shiftPoly Q j (c j)).totalDegree ≤ K * Q.totalDegree := by
  refine le_trans (MvPolynomial.totalDegree_finsetProd Finset.univ
    (fun j => shiftPoly Q j (c j))) ?_
  calc (∑ j : Fin K, (shiftPoly Q j (c j)).totalDegree) ≤ ∑ _j : Fin K, Q.totalDegree :=
        Finset.sum_le_sum (fun j _ => totalDegree_shiftPoly_le Q j (c j))
    _ = K * Q.totalDegree := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem exists_poly_weight_family_deg {K : ℕ} {M ε C η' : ℝ} (hM : 0 ≤ M) (hε : 0 < ε)
    (hC : 0 ≤ C) (hη' : 0 < η') {ψ : ℝ → ℝ}
    (hψ : ContinuousOn ψ (Set.Icc (-((C + M) / ε)) ((C + M) / ε)))
    (hψ01 : ∀ u ∈ Set.Icc (-((C + M) / ε)) ((C + M) / ε), 0 ≤ ψ u ∧ ψ u ≤ 1) :
    ∃ (E : ℝ) (D : ℕ), 0 ≤ E ∧ ∀ c : Fin K → ℝ, (∀ j, |c j| ≤ C) →
      ∃ P : MvPolynomial (Fin K) ℝ,
        (∀ t ∈ Set.pi Set.univ (fun _ : Fin K => Set.Icc (-M) M),
          |∏ j, ψ ((t j - c j) / ε) - MvPolynomial.eval t P| ≤ η') ∧
        (∑ m ∈ P.support, |P.coeff m|) ≤ E ∧
        P.totalDegree ≤ D := by
  have hψe : Continuous (fun y : ℝ => ψ (max (-((C + M) / ε)) (min ((C + M) / ε) y))) :=
    continuous_clamp_comp hM hε hC hψ
  set I : ℝ := max C M with hIdef
  have hI : 0 ≤ I := by rw [hIdef]; exact le_trans hC (le_max_left C M)
  have hCI : C ≤ I := by rw [hIdef]; exact le_max_left C M
  have hMI : M ≤ I := by rw [hIdef]; exact le_max_right C M
  have hlin : Continuous (fun x : Fin 2 → ℝ => (x (1 : Fin 2) - x (0 : Fin 2)) / ε) := by
    apply Continuous.div_const
    apply Continuous.sub
    · exact continuous_apply (1 : Fin 2)
    · exact continuous_apply (0 : Fin 2)
  have hcont : Continuous
      (fun x : Fin 2 → ℝ => ψ (max (-((C + M) / ε)) (min ((C + M) / ε)
        ((x (1 : Fin 2) - x (0 : Fin 2)) / ε)))) :=
    hψe.comp hlin
  set T : ℝ := (2 : ℝ) ^ K * (K : ℝ) with hTdef
  have hTnn : 0 ≤ T := by rw [hTdef]; positivity
  set δ : ℝ := min 1 (η' / (T + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min one_pos (div_pos hη' (by linarith))
  have hδle1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδle : δ ≤ η' / (T + 1) := by rw [hδdef]; exact min_le_right _ _
  obtain ⟨Q, hQ⟩ := exists_mvpolynomial_near_of_continuousOn I hI
    (fun x : Fin 2 → ℝ => ψ (max (-((C + M) / ε)) (min ((C + M) / ε)
      ((x (1 : Fin 2) - x (0 : Fin 2)) / ε)))) hcont.continuousOn hδpos
  set B : ℝ := ∑ m ∈ Q.support, |Q.coeff m| * C ^ (m (0 : Fin 2)) with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (abs_nonneg _) (pow_nonneg hC _))
  refine ⟨B ^ K, K * Q.totalDegree, pow_nonneg hBnn K, ?_⟩
  intro c hc
  refine ⟨∏ j : Fin K, shiftPoly Q j (c j), ?_, ?_, ?_⟩
  · intro t ht
    have ht' : ∀ j, t j ∈ Set.Icc (-M) M := fun j =>
      (Set.mem_pi.mp ht) j (Set.mem_univ j)
    have harg : ∀ j, (t j - c j) / ε ∈ Set.Icc (-((C + M) / ε)) ((C + M) / ε) := by
      intro j
      have ht1 : -M ≤ t j := (ht' j).1
      have ht2 : t j ≤ M := (ht' j).2
      have hc1 : -C ≤ c j := (abs_le.mp (hc j)).1
      have hc2 : c j ≤ C := (abs_le.mp (hc j)).2
      constructor
      · have h : -((C + M) / ε) = (-(C + M)) / ε := by rw [neg_div]
        rw [h]
        exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)
      · exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)
    have habs : ∀ j, |ψ ((t j - c j) / ε)
        - MvPolynomial.eval t (shiftPoly Q j (c j))| ≤ δ := by
      intro j
      set x : Fin 2 → ℝ := fun i => if i = (0 : Fin 2) then c j else t j with hxdef
      have hx0 : x (0 : Fin 2) = c j := by simp [hxdef]
      have hx1 : x (1 : Fin 2) = t j := by simp [hxdef]
      have hxl : x ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-I) I) := by
        rw [Set.mem_pi]
        intro i _
        fin_cases i
        · change x (0 : Fin 2) ∈ Set.Icc (-I) I
          have h := abs_le.mp (hc j)
          rw [Set.mem_Icc, hx0]
          exact ⟨by linarith [h.1, hCI], le_trans h.2 hCI⟩
        · change x (1 : Fin 2) ∈ Set.Icc (-I) I
          have h := ht' j
          rw [Set.mem_Icc, hx1]
          exact ⟨by linarith [h.1, hMI], le_trans h.2 hMI⟩
      have hQx := hQ x hxl
      have hPhi : ψ (max (-((C + M) / ε)) (min ((C + M) / ε) ((x (1 : Fin 2) - x (0 : Fin 2)) / ε)))
          = ψ ((t j - c j) / ε) := by
        rw [hx1, hx0]
        exact clamp_eq_of_mem (harg j)
      have hbx : MvPolynomial.eval x Q = MvPolynomial.eval t (shiftPoly Q j (c j)) := by
        rw [hxdef]
        exact (eval_shiftPoly_eq Q j (c j) t).symm
      rw [hPhi, hbx] at hQx
      exact hQx
    have ha1 : ∀ j, |ψ ((t j - c j) / ε)| ≤ 1 := by
      intro j
      have h01 := hψ01 _ (harg j)
      rw [abs_le]
      exact ⟨by linarith [h01.1], h01.2⟩
    have hbD : ∀ j, |MvPolynomial.eval t (shiftPoly Q j (c j))| ≤ 1 + δ := by
      intro j
      have h := habs j
      have h1 := ha1 j
      calc |MvPolynomial.eval t (shiftPoly Q j (c j))|
          = |(MvPolynomial.eval t (shiftPoly Q j (c j)) - ψ ((t j - c j) / ε))
              + ψ ((t j - c j) / ε)| := by ring_nf
        _ ≤ |MvPolynomial.eval t (shiftPoly Q j (c j)) - ψ ((t j - c j) / ε)|
              + |ψ ((t j - c j) / ε)| := abs_add_le _ _
        _ ≤ δ + 1 := by
              apply add_le_add
              · rw [abs_sub_comm]; exact h
              · exact h1
        _ = 1 + δ := by ring
    rw [MvPolynomial.eval_prod]
    have hkey := abs_prod_sub_prod_le (Finset.univ : Finset (Fin K))
      (fun j => ψ ((t j - c j) / ε))
      (fun j => MvPolynomial.eval t (shiftPoly Q j (c j)))
      (M := 1 + δ) (by linarith)
      (fun j _ => le_trans (ha1 j) (by linarith))
      (fun j _ => hbD j)
    have hkey' : |∏ j : Fin K, ψ ((t j - c j) / ε)
        - ∏ j : Fin K, MvPolynomial.eval t (shiftPoly Q j (c j))|
        ≤ (1 + δ) ^ K * ∑ j : Fin K, |ψ ((t j - c j) / ε)
          - MvPolynomial.eval t (shiftPoly Q j (c j))| := by
      simpa [Finset.card_univ, Fintype.card_fin] using hkey
    have hsum : ∑ j : Fin K, |ψ ((t j - c j) / ε)
        - MvPolynomial.eval t (shiftPoly Q j (c j))| ≤ (K : ℝ) * δ := by
      calc ∑ j : Fin K, |ψ ((t j - c j) / ε)
              - MvPolynomial.eval t (shiftPoly Q j (c j))|
          ≤ ∑ _j : Fin K, δ := Finset.sum_le_sum (fun j _ => habs j)
        _ = (K : ℝ) * δ := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpow : (1 + δ) ^ K ≤ (2 : ℝ) ^ K :=
      pow_le_pow_left₀ (by linarith) (by linarith) K
    calc |∏ j : Fin K, ψ ((t j - c j) / ε)
            - ∏ j : Fin K, MvPolynomial.eval t (shiftPoly Q j (c j))|
        ≤ (1 + δ) ^ K * ∑ j : Fin K, |ψ ((t j - c j) / ε)
            - MvPolynomial.eval t (shiftPoly Q j (c j))| := hkey'
      _ ≤ (2 : ℝ) ^ K * ((K : ℝ) * δ) := by
            apply mul_le_mul hpow hsum (by positivity) (by positivity)
      _ = T * δ := by rw [hTdef]; ring
      _ ≤ η' := by
            calc T * δ ≤ T * (η' / (T + 1)) := mul_le_mul_of_nonneg_left hδle hTnn
              _ = T * η' / (T + 1) := by ring
              _ ≤ η' := by
                  rw [div_le_iff₀ (by linarith)]
                  nlinarith [hη']
  · change coeffMass (∏ j : Fin K, shiftPoly Q j (c j)) ≤ B ^ K
    calc coeffMass (∏ j : Fin K, shiftPoly Q j (c j))
        ≤ ∏ j : Fin K, coeffMass (shiftPoly Q j (c j)) := coeffMass_prod_le _ _
      _ ≤ ∏ _j : Fin K, B :=
            Finset.prod_le_prod (fun j _ => coeffMass_nonneg _)
              (fun j _ => by rw [hBdef]; exact coeffMass_shiftPoly_le Q j hC (hc j))
      _ = B ^ K := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · exact totalDegree_prod_shiftPoly_le Q c

end Commons.Analysis.Approximation
