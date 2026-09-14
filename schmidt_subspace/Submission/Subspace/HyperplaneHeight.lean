import Submission.Subspace.HeightAux
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Submission.Subspace

open Finset

theorem hyperplane_height_dichotomy {n : ℕ} (hn : 1 ≤ n)
    (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hL : L.det ≠ 0)
    (hLa : ∀ i j, IsAlgebraic ℚ (L i j))
    (γ : Fin (n + 1) → ℝ) (hsum : ∑ i, γ i < 0) :
    ∃ (Q₀ θ M : ℝ), 1 ≤ Q₀ ∧ 0 < θ ∧ 0 < M ∧
      ∀ (Q : ℝ) (b : Fin (n + 1) → ℤ), Q₀ ≤ Q → b ≠ 0 →
        Module.finrank ℚ (approxSpace L γ Q) = n →
        (∀ x : Fin (n + 1) → ℚ, x ∈ approxSpace L γ Q ↔ ∑ j, (b j : ℚ) * x j = 0) →
        (∃ a j : Fin (n + 1), a ≠ j ∧ b a ≠ 0 ∧
          θ * Real.log Q ≤ Height.logHeight₁ (((b j : ℤ) : ℚ) / ((b a : ℤ) : ℚ))) ∨
        ∃ c : Fin (n + 1) → ℤ, c ≠ 0 ∧ ‖c‖ ≤ M ∧
          ∀ x : Fin (n + 1) → ℚ, x ∈ approxSpace L γ Q ↔ ∑ j, (c j : ℚ) * x j = 0 := by
  classical
  obtain ⟨K, hKfin, hLK⟩ := exists_numberField_of_algebraic_coefficients L hLa
  haveI hKfd : FiniteDimensional ℚ ↥K := hKfin
  haveI hKnf : NumberField ↥K := NumberField.of_module_finite ℚ ↥K
  set dK : ℕ := Module.finrank ℚ ↥K with hdKdef
  have hdKpos : 0 < dK := by rw [hdKdef]; exact Module.finrank_pos
  set ε : ℝ := -∑ i, γ i with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  -- the coefficient matrix over K and the adjugate forms
  set LK : Matrix (Fin (n+1)) (Fin (n+1)) ↥K := (fun i j => (⟨L i j, hLK i j⟩ : ↥K)) with hLKdef
  set Af : Fin (n+1) → Fin (n+1) → ↥K := fun k j => LK.adjugate j k with hAfdef
  set Call : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun k : Fin (n+1) => ∏ j, Height.mulHeight₁ (Af k j)) with hCalldef
  have hCall1 : 1 ≤ Call := by
    rw [hCalldef]
    refine le_trans ?_ (Finset.le_sup' (fun k : Fin (n+1) => ∏ j, Height.mulHeight₁ (Af k j))
      (Finset.mem_univ (0 : Fin (n+1))))
    exact Finset.one_le_prod (fun j _ => Height.one_le_mulHeight₁ _)
  set C1 : ℝ := (((n+1 : ℕ)) : ℝ) ^ dK * Call with hC1def
  have hC1pos : 0 < C1 := by
    rw [hC1def]
    have h1 : (0:ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    exact mul_pos (pow_pos h1 _) (lt_of_lt_of_le one_pos hCall1)
  set theta : ℝ := ε / (4 * (dK : ℝ) * ((n+1 : ℕ) : ℝ) * (n : ℝ)) with hthetadef
  have hthetapos : 0 < theta := by
    rw [hthetadef]
    apply div_pos hεpos
    have h1 : (0:ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h3 : (0:ℝ) < (dK : ℝ) := by exact_mod_cast hdKpos
    positivity
  -- ### the fixed linear forms and the finite family of candidate normals
  set phi : Fin (n+1) → ((Fin (n+1) → ℚ) →ₗ[ℚ] ↥K) :=
    fun k => ∑ j : Fin (n+1), (LinearMap.proj j).smulRight (Af k j) with hphidef
  have hphi_apply : ∀ (k : Fin (n+1)) (y : Fin (n+1) → ℚ),
      phi k y = ∑ j, (y j : ↥K) * Af k j := by
    intro k y
    rw [hphidef]
    simp [LinearMap.proj_apply, Algebra.smul_def]
  set Lam : Finset (Fin (n+1)) → Submodule ℚ (Fin (n+1) → ℚ) :=
    fun J => ⨅ k ∈ J, LinearMap.ker (phi k) with hLamdef
  have hLam_mem : ∀ (J : Finset (Fin (n+1))) (y : Fin (n+1) → ℚ),
      y ∈ Lam J ↔ ∀ k ∈ J, phi k y = 0 := by
    intro J y
    rw [hLamdef]
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  have hchoose : ∀ J : Finset (Fin (n+1)), Lam J ≠ ⊥ →
      ∃ y : Fin (n+1) → ℤ, y ≠ 0 ∧ (fun j => ((y j : ℤ) : ℚ)) ∈ Lam J := by
    intro J hJ
    obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff (Lam J)).mp hJ
    obtain ⟨D, hDpos, hD⟩ := Commons.Data.Rat.exists_common_denominator (Fin (n+1)) y
    choose n hn using hD
    refine ⟨fun j => n j, ?_, ?_⟩
    · intro h0
      apply hy0
      funext j
      have := congrFun h0 j
      simp only [Pi.zero_apply] at this
      have h1 : (y j : ℚ) = 0 := by rw [hn j, this]; simp
      exact_mod_cast h1
    · have hscale : (D : ℚ) • y ∈ Lam J := Submodule.smul_mem _ _ hy
      have hEq : (D : ℚ) • y = fun j => ((n j : ℤ) : ℚ) := by
        funext j
        rw [Pi.smul_apply, smul_eq_mul, hn j]
        field_simp
      rwa [hEq] at hscale
  let cy : Finset (Fin (n+1)) → (Fin (n+1) → ℤ) :=
    fun J => if h : Lam J ≠ ⊥ then Classical.choose (hchoose J h) else 0
  have hcy : ∀ (J : Finset (Fin (n+1))) (h : Lam J ≠ ⊥),
      cy J ≠ 0 ∧ (fun j => ((cy J j : ℤ) : ℚ)) ∈ Lam J := by
    intro J h
    have : cy J = Classical.choose (hchoose J h) := dif_pos h
    rw [this]
    exact Classical.choose_spec (hchoose J h)
  set M : ℝ := 1 + (Finset.univ.powerset).sup' ⟨Finset.univ, by simp⟩ (fun J => ‖cy J‖)
    with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have h1 : (0:ℝ) ≤ (Finset.univ.powerset).sup' ⟨Finset.univ, by simp⟩ (fun J => ‖cy J‖) :=
      le_trans (norm_nonneg (cy Finset.univ))
        (Finset.le_sup' (fun J : Finset (Fin (n+1)) => ‖cy J‖)
          (show Finset.univ ∈ Finset.univ.powerset from by simp))
    linarith
  have hMbound : ∀ J : Finset (Fin (n+1)), ‖cy J‖ ≤ M := by
    intro J
    rw [hMdef]
    have h1 : ‖cy J‖ ≤ (Finset.univ.powerset).sup' ⟨Finset.univ, by simp⟩ (fun J => ‖cy J‖) :=
      Finset.le_sup' (fun J : Finset (Fin (n+1)) => ‖cy J‖)
        (show J ∈ Finset.univ.powerset from by simp)
    linarith
  set Cadj : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := Fin (n+1) × Fin (n+1)))
    (fun p : Fin (n+1) × Fin (n+1) => ‖(Matrix.of L).adjugate p.1 p.2‖) with hCadjdef
  have hCadj_nn : 0 ≤ Cadj := by
    rw [hCadjdef]
    exact le_trans (norm_nonneg ((Matrix.of L).adjugate 0 0)) (Finset.le_sup'
      (fun p : Fin (n+1) × Fin (n+1) => ‖(Matrix.of L).adjugate p.1 p.2‖) (Finset.mem_univ (0,0)))
  set Q₀ : ℝ := max 1 (max (max ((((n.factorial : ℝ) * C1) + 1) ^ (4 / ε))
      ((((n.factorial : ℝ)) + 1) ^ (2 / ε)))
      ((((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ + 1) ^ (2 / ε))) with hQ₀def
  have hQ₀1 : 1 ≤ Q₀ := by rw [hQ₀def]; exact le_max_left _ _
  have hQ₀A : ((((n.factorial : ℝ) * C1) + 1) ^ (4 / ε)) ≤ Q₀ := by
    rw [hQ₀def]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hQ₀B : ((((n.factorial : ℝ)) + 1) ^ (2 / ε)) ≤ Q₀ := by
    rw [hQ₀def]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hQ₀C : ((((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ + 1) ^ (2 / ε)) ≤ Q₀ := by
    rw [hQ₀def]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have keypow : ∀ (x : ℝ) (c : ℝ), 1 ≤ x → 0 < c → x ≤ ((x ^ c) ^ (1 / c)) := by
    intro x c hx hc
    rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ x), one_div, mul_inv_cancel₀ (ne_of_gt hc),
      Real.rpow_one]
  have hQε4 : ∀ Q : ℝ, Q₀ ≤ Q → (n.factorial : ℝ) * C1 ≤ Q ^ (ε/4) := by
    intro Q hQ
    have h2 : (((n.factorial : ℝ) * C1) + 1) ^ (4/ε) ≤ Q := le_trans hQ₀A hQ
    have h5 : ((((n.factorial : ℝ) * C1) + 1) ^ (4/ε)) ^ (ε/4) ≤ Q ^ (ε/4) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h2
        (div_nonneg (le_of_lt hεpos) (by norm_num))
    rw [← Real.rpow_mul (show (0:ℝ) ≤ ((n.factorial : ℝ) * C1) + 1 from by positivity),
      show (4/ε) * (ε/4) = 1 from by field_simp, Real.rpow_one] at h5
    linarith
  have hQε2 : ∀ Q : ℝ, Q₀ ≤ Q → (n.factorial : ℝ) ≤ Q ^ (ε/2) := by
    intro Q hQ
    have h2 : (((n.factorial : ℝ)) + 1) ^ (2/ε) ≤ Q := le_trans hQ₀B hQ
    have h5 : ((((n.factorial : ℝ)) + 1) ^ (2/ε)) ^ (ε/2) ≤ Q ^ (ε/2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h2
        (div_nonneg (le_of_lt hεpos) (by norm_num))
    rw [← Real.rpow_mul (show (0:ℝ) ≤ ((n.factorial : ℝ)) + 1 from by positivity),
      show (2/ε) * (ε/2) = 1 from by field_simp, Real.rpow_one] at h5
    linarith
  have hQcase2 : ∀ Q : ℝ, Q₀ ≤ Q →
      ((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ + 1 ≤ Q ^ (ε/2) := by
    intro Q hQ
    have h2 : ((((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ + 1) ^ (2/ε)) ≤ Q :=
      le_trans hQ₀C hQ
    have hx : (1:ℝ) ≤ ((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ + 1 := by
      have h1 : (0:ℝ) < ‖(Matrix.of L).det‖ := norm_pos_iff.mpr hL
      have h2 : (0:ℝ) ≤ ((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ := by positivity
      linarith [h2]
    have h5 : ((((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ + 1) ^ (2/ε)) ^ (ε/2)
        ≤ Q ^ (ε/2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) h2
        (div_nonneg (le_of_lt hεpos) (by norm_num))
    rw [← Real.rpow_mul (show (0:ℝ) ≤ ((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ + 1
        from by positivity),
      show (2/ε) * (ε/2) = 1 from by field_simp, Real.rpow_one] at h5
    exact h5
  refine ⟨Q₀, theta, M, hQ₀1, hthetapos, hMpos, ?_⟩
  intro Q b hQ hb hfr hker
  have hQ1 : 1 ≤ Q := le_trans hQ₀1 hQ
  have hQpos : 0 < Q := lt_of_lt_of_le one_pos hQ1
  -- ### the box basis and the cofactor vector
  obtain ⟨g, hgbox, hgli⟩ := exists_fin_box_independent n (approxBox L γ Q) (approxSpace L γ Q)
    (by rintro v ⟨y, hy, rfl⟩; exact mem_approxSpace_of_mem_box hy) rfl hfr
  set G : Matrix (Fin (n+1)) (Fin n) ℤ := fun i j => g j i with hGdef
  have hGcol : LinearIndependent ℚ (fun j : Fin n => fun i : Fin (n+1) => ((G i j : ℤ) : ℚ)) :=
    hgli
  have hspan : Submodule.span ℚ (Set.range (fun j : Fin n => fun i : Fin (n+1) =>
      ((G i j : ℤ) : ℚ))) = approxSpace L γ Q := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro v ⟨j, rfl⟩
      exact mem_approxSpace_of_mem_box (hgbox j)
    · rw [finrank_span_eq_card hGcol, Fintype.card_fin, hfr]
  have hstar_orth : ∀ x ∈ approxSpace L γ Q, ∑ i, (starVecZ G i : ℚ) * x i = 0 := by
    intro x hx
    have hx' : x ∈ Submodule.span ℚ (Set.range (fun j : Fin n => fun i : Fin (n+1) =>
        ((G i j : ℤ) : ℚ))) := by rw [hspan]; exact hx
    have key : dotLin (fun i => (starVecZ G i : ℚ)) x = 0 := by
      refine Submodule.span_induction (p := fun y _ => dotLin (fun i => (starVecZ G i : ℚ)) y = 0)
        ?_ ?_ ?_ ?_ hx'
      · rintro v ⟨j, rfl⟩
        simp only [dotLin_apply]
        exact starVecZ_dotProduct G j
      · simp
      · intro p q hp hq hpp hqq
        rw [map_add, hpp, hqq, add_zero]
      · intro c p hp hpp
        rw [map_smul, hpp, smul_zero]
    simpa only [dotLin_apply] using key
  -- ### the primitive normal
  obtain ⟨d, hd1, b₀, hgcd, hstar_eq, -, -⟩ :=
    Commons.Data.IntVec.primitive_factor (starVecZ G) (starVecZ_ne_zero G hGcol)
  have hb₀_ne : b₀ ≠ 0 := by
    intro h0
    refine starVecZ_ne_zero G hGcol ?_
    rw [hstar_eq, h0, smul_zero]
  have hd0q : (d : ℚ) ≠ 0 := by
    have h : (0:ℤ) < d := lt_of_lt_of_le Int.zero_lt_one hd1
    exact_mod_cast (ne_of_gt h)
  have hb₀_orth : ∀ x ∈ approxSpace L γ Q, ∑ i, (b₀ i : ℚ) * x i = 0 := by
    intro x hx
    have h1 := hstar_orth x hx
    have h2 : ∀ i, (starVecZ G i : ℚ) = (d : ℚ) * (b₀ i : ℚ) := by
      intro i
      rw [hstar_eq]
      simp [Pi.smul_apply]
    have h3 : ∑ i, ((d : ℚ) * (b₀ i : ℚ)) * x i
        = (d : ℚ) * ∑ i, (b₀ i : ℚ) * x i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have h1' : ∑ i, ((d : ℚ) * (b₀ i : ℚ)) * x i = 0 := by
      have : ∑ i, ((d : ℚ) * (b₀ i : ℚ)) * x i = ∑ i, (starVecZ G i : ℚ) * x i :=
        Finset.sum_congr rfl (fun i _ => by rw [h2 i])
      rw [this]; exact h1
    rw [h3] at h1'
    exact (mul_eq_zero.mp h1').resolve_left hd0q
  have hb₀q_ne : (fun j => (b₀ j : ℚ)) ≠ 0 := by
    intro hh
    apply hb₀_ne
    funext j
    have h := congrFun hh j
    simp only [Pi.zero_apply] at h
    exact_mod_cast h
  have hb₀_ker : ∀ x : Fin (n+1) → ℚ, x ∈ approxSpace L γ Q ↔ ∑ j, (b₀ j : ℚ) * x j = 0 := by
    intro x
    constructor
    · exact hb₀_orth x
    · intro hx
      set φ : (Fin (n+1) → ℚ) →ₗ[ℚ] ℚ := dotLin (fun j => (b₀ j : ℚ)) with hφdef
      have hφne : φ ≠ 0 := by
        rw [hφdef]; exact dotLin_ne_zero hb₀q_ne
      have hkerfin : Module.finrank ℚ (LinearMap.ker φ) = n := by
        have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφne
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
        omega
      have heq : LinearMap.ker φ = approxSpace L γ Q :=
        (Submodule.eq_of_le_of_finrank_eq (fun y hy => hb₀_orth y hy)
          (by rw [hkerfin, hfr])).symm
      have : x ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker]
        simpa [hφdef] using hx
      rwa [heq] at this
  -- ### `b` is a rational multiple of `b₀`
  have hbq_ne : (fun j => (b j : ℚ)) ≠ 0 := by
    intro hh
    apply hb
    funext j
    have h := congrFun hh j
    simp only [Pi.zero_apply] at h
    exact_mod_cast h
  obtain ⟨cc, hcc_eq⟩ :=
    Commons.LinearAlgebra.LinearForm.exists_smul_of_forall_sum_eq_zero_iff
      (fun j => (b₀ j : ℚ)) (fun j => (b j : ℚ)) hbq_ne
      (fun x => by rw [← hb₀_ker x, ← hker x])
  have hcc_ne : cc ≠ 0 := by
    intro h0
    apply hb₀q_ne
    rw [hcc_eq, h0, zero_smul]
  have hcc_apply : ∀ j : Fin (n+1), (b₀ j : ℚ) = cc * (b j : ℚ) := by
    intro j
    have h1 := congrFun hcc_eq j
    simpa [Pi.smul_apply, smul_eq_mul] using h1
  have hratio : ∀ a j : Fin (n+1), ((b₀ j : ℤ) : ℚ) / ((b₀ a : ℤ) : ℚ)
      = ((b j : ℤ) : ℚ) / ((b a : ℤ) : ℚ) := by
    intro a j
    rw [hcc_apply j, hcc_apply a, mul_div_mul_left _ _ hcc_ne]
  -- ### the adjugate forms over the coefficient field
  set Gk : Matrix (Fin (n+1)) (Fin n) ↥K := G.map (fun x : ℤ => (x : ↥K)) with hGkdef
  have hGkdet : ∀ j : Fin (n+1), (Gk.submatrix (Fin.succAbove j) id).det
      = ((-1 : ↥K)^(j:ℕ)) * ((d : ↥K) * (b₀ j : ↥K)) := by
    intro j
    have h2 := starVecZ_cast (R := ↥K) G j
    rw [← hGkdef] at h2
    have h3 : (starVecZ G j : ↥K) = (d : ↥K) * (b₀ j : ↥K) := by
      rw [hstar_eq]
      simp [Pi.smul_apply]
    rw [h3] at h2
    calc (Gk.submatrix (Fin.succAbove j) id).det
        = 1 * (Gk.submatrix (Fin.succAbove j) id).det := (one_mul _).symm
      _ = ((-1 : ↥K)^(j:ℕ) * (-1 : ↥K)^(j:ℕ)) * (Gk.submatrix (Fin.succAbove j) id).det := by
          rw [neg_one_pow_mul_self]
      _ = (-1 : ↥K)^(j:ℕ)
            * (((-1 : ↥K)^(j:ℕ)) * (Gk.submatrix (Fin.succAbove j) id).det) := by ring
      _ = (-1 : ↥K)^(j:ℕ) * ((d : ↥K) * (b₀ j : ↥K)) := by rw [← h2]
  have hdet_id : ∀ k : Fin (n+1),
      (IntermediateField.val K) (((LK * Gk).submatrix (Fin.succAbove k) id).det)
        = ((Matrix.of L * G.map (fun x : ℤ => (x : ℂ))).submatrix
            (Fin.succAbove k) id).det := by
    intro k
    have hmat : ((LK * Gk).map (fun x : ↥K => (x : ℂ)))
        = (Matrix.of L * G.map (fun x : ℤ => (x : ℂ))) := by
      have hmap : ((LK * Gk).map (fun x : ↥K => (x : ℂ)))
          = ((LK.map (fun x : ↥K => (x : ℂ))) * (Gk.map (fun x : ↥K => (x : ℂ)))) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.mul_apply]
        push_cast
        rfl
      have hL : LK.map (fun x : ↥K => (x : ℂ)) = Matrix.of L := by ext i j; rfl
      have hG : Gk.map (fun x : ↥K => (x : ℂ)) = G.map (fun x : ℤ => (x : ℂ)) := by
        ext i j; rfl
      rw [hmap, hL, hG]
    have h0 := RingHom.map_det (IntermediateField.val K).toRingHom
      ((LK * Gk).submatrix (Fin.succAbove k) id)
    rw [RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
      show (⇑(IntermediateField.val K).toRingHom) = (fun x : ↥K => (x : ℂ)) from rfl,
      hmat] at h0
    exact h0
  by_cases hcase : ∃ k : Fin (n+1),
      ((LK * Gk).submatrix (Fin.succAbove k) id).det ≠ 0 ∧ -(ε/2) ≤ γ k
  · left
    obtain ⟨k, hDk_ne, hγk⟩ := hcase
    set lB0 : ↥K := ∑ j, LK.adjugate j k * (b₀ j : ↥K) with hlB0def
    have hDceq : ((LK * Gk).submatrix (Fin.succAbove k) id).det
        = (d : ↥K) * (-1 : ↥K) ^ (k : ℕ) * lB0 := by
      rw [Commons.LinearAlgebra.Matrix.det_succAbove_mul_eq_sum_adjugate n LK Gk k, hlB0def]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hGkdet j]
      have hfac : (-1 : ↥K) ^ ((j:ℕ) + (k:ℕ)) * (-1 : ↥K) ^ (j:ℕ) = (-1 : ↥K)^(k:ℕ) := by
        rw [← pow_add, show (j:ℕ)+(k:ℕ)+(j:ℕ) = (k:ℕ) + 2*(j:ℕ) from by ring, pow_add, pow_mul]
        norm_num
      calc (-1 : ↥K)^((j:ℕ)+(k:ℕ)) * LK.adjugate j k
              * ((-1 : ↥K)^(j:ℕ) * ((d : ↥K) * (b₀ j : ↥K)))
          = ((-1 : ↥K)^((j:ℕ)+(k:ℕ)) * (-1 : ↥K)^(j:ℕ))
              * (LK.adjugate j k * ((d : ↥K) * (b₀ j : ↥K))) := by ring
        _ = (-1 : ↥K)^(k:ℕ) * (LK.adjugate j k * ((d : ↥K) * (b₀ j : ↥K))) := by rw [hfac]
        _ = (d : ↥K) * (-1 : ↥K)^(k:ℕ) * (LK.adjugate j k * (b₀ j : ↥K)) := by ring
    have hlB0_ne : lB0 ≠ 0 := by
      intro h0
      refine hDk_ne ?_
      rw [hDceq, h0]; ring
    -- the archimedean bound on `D k`
    have hDkC : ‖(IntermediateField.val K) (((LK * Gk).submatrix (Fin.succAbove k) id).det)‖
        ≤ (n.factorial : ℝ) * Q ^ (-(ε/2)) := by
      have hmat : ((LK * Gk).map (fun x : ↥K => (x : ℂ)))
          = (Matrix.of L * G.map (fun x : ℤ => (x : ℂ))) := by
        have hmap : ((LK * Gk).map (fun x : ↥K => (x : ℂ)))
            = ((LK.map (fun x : ↥K => (x : ℂ))) * (Gk.map (fun x : ↥K => (x : ℂ)))) := by
          ext i j
          simp only [Matrix.map_apply, Matrix.mul_apply]
          push_cast
          rfl
        have hL : LK.map (fun x : ↥K => (x : ℂ)) = Matrix.of L := by ext i j; rfl
        have hG : Gk.map (fun x : ↥K => (x : ℂ)) = G.map (fun x : ℤ => (x : ℂ)) := by
          ext i j; rfl
        rw [hmap, hL, hG]
      have hid : (IntermediateField.val K) (((LK * Gk).submatrix (Fin.succAbove k) id).det)
          = ((Matrix.of L * G.map (fun x : ℤ => (x : ℂ))).submatrix
              (Fin.succAbove k) id).det := by
        have h0 := RingHom.map_det (IntermediateField.val K).toRingHom
          ((LK * Gk).submatrix (Fin.succAbove k) id)
        rw [RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
          show (⇑(IntermediateField.val K).toRingHom) = (fun x : ↥K => (x : ℂ)) from rfl,
          hmat] at h0
        exact h0
      rw [hid]
      have hb : ∀ i j, ‖((Matrix.of L * G.map (fun x : ℤ => (x : ℂ))).submatrix
          (Fin.succAbove k) id) i j‖ ≤ Q ^ (γ (Fin.succAbove k i)) := by
        intro i j
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.map_apply]
        exact hgbox j (Fin.succAbove k i)
      calc ‖((Matrix.of L * G.map (fun x : ℤ => (x : ℂ))).submatrix (Fin.succAbove k) id).det‖
          ≤ (n.factorial : ℝ) * ∏ i : Fin n, Q ^ (γ (Fin.succAbove k i)) :=
            Commons.LinearAlgebra.Matrix.norm_det_le_prod _ _ hb
        _ = (n.factorial : ℝ) * Q ^ (∑ i : Fin n, γ (Fin.succAbove k i)) := by
            rw [Real.rpow_sum_of_pos hQpos]
        _ ≤ (n.factorial : ℝ) * Q ^ (-(ε/2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            apply Real.rpow_le_rpow_of_exponent_le hQ1
            have hsum' : ∑ i : Fin n, γ (Fin.succAbove k i) = (∑ i, γ i) - γ k := by
              have h := Fin.sum_univ_succAbove γ k
              linarith [h]
            rw [hsum']
            have hε : ∑ i, γ i = -ε := by rw [hεdef]; ring
            rw [hε]
            linarith
    have hQDk : ‖(IntermediateField.val K) lB0‖ ≤ (n.factorial : ℝ) * Q ^ (-(ε/2)) := by
      have h1 : (IntermediateField.val K) (((LK * Gk).submatrix (Fin.succAbove k) id).det)
          = (d : ℂ) * (-1 : ℂ)^(k:ℕ) * (IntermediateField.val K) lB0 := by
        rw [hDceq]
        simp only [map_mul, map_pow, map_neg, map_one, map_intCast]
      have h2 : ‖(IntermediateField.val K) lB0‖
          ≤ ‖(IntermediateField.val K) (((LK * Gk).submatrix (Fin.succAbove k) id).det)‖ := by
        rw [h1, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
        have hd : (1:ℝ) ≤ ‖(d : ℂ)‖ := by
          rw [Complex.norm_intCast,
            abs_of_nonneg (show (0:ℝ) ≤ (d:ℝ) from by
              exact_mod_cast (show (0:ℤ) ≤ d from by omega))]
          exact_mod_cast hd1
        nlinarith [norm_nonneg ((IntermediateField.val K) lB0)]
      linarith [hDkC]
    -- the height lower bound
    set w : NumberField.InfinitePlace ↥K :=
      NumberField.InfinitePlace.mk (IntermediateField.val K) with hwdef
    have hwval : w lB0 = ‖(IntermediateField.val K) lB0‖ := rfl
    have hwpos : 0 < w lB0 := by
      rw [hwval]
      exact norm_pos_iff.mpr (fun h0 => hlB0_ne (ZeroMemClass.coe_eq_zero.mp h0))
    have hHlow : Q ^ (ε/2) / (n.factorial : ℝ) ≤ Height.mulHeight₁ lB0 := by
      have h1 : (w lB0)⁻¹ ≤ Height.mulHeight₁ lB0 := by
        have h := Commons.NumberTheory.Height.NumberField.infinitePlace_val_le_mulHeight w (lB0⁻¹)
        rw [map_inv₀, Height.mulHeight₁_inv] at h
        exact h
      have h2 : (Q ^ (ε/2) / (n.factorial : ℝ)) ≤ (w lB0)⁻¹ := by
        have hle : w lB0 ≤ (n.factorial : ℝ) * Q ^ (-(ε/2)) := by rw [hwval]; exact hQDk
        have hA : (0:ℝ) < Q ^ (ε/2) / (n.factorial : ℝ) := by positivity
        have h1 : (Q ^ (ε/2) / (n.factorial : ℝ)) * w lB0 ≤ 1 := by
          calc (Q ^ (ε/2) / (n.factorial : ℝ)) * w lB0
              ≤ (Q ^ (ε/2) / (n.factorial : ℝ)) * ((n.factorial : ℝ) * Q ^ (-(ε/2))) :=
                mul_le_mul_of_nonneg_left hle hA.le
            _ = 1 := by
                rw [div_mul_eq_mul_div, mul_comm ((n.factorial : ℝ)) (Q ^ (-(ε/2))),
                  ← mul_assoc, ← Real.rpow_add hQpos,
                  show ε/2 + -(ε/2) = 0 from by ring, Real.rpow_zero, one_mul,
                  div_self (by positivity : ((n.factorial : ℝ)) ≠ 0)]
        rw [inv_eq_one_div, le_div_iff₀ hwpos]
        exact h1
      exact le_trans h2 h1
    have hHup : Height.mulHeight₁ lB0 ≤ C1 * ‖b₀‖ ^ (dK * (n+1)) := by
      have h1 := Commons.NumberTheory.Height.NumberField.mulHeight_sum_mul_int_le_of_nonempty
        (K := ↥K) (Af k) b₀
      have h2 : (∑ j : Fin (n+1), Af k j * (b₀ j : ↥K)) = lB0 := by
        rw [hlB0def, hAfdef]
      rw [h2] at h1
      rw [show Fintype.card (Fin (n+1)) = n + 1 from Fintype.card_fin _,
        show (Module.finrank ℚ ↥K) = dK from hdKdef.symm] at h1
      rw [show max 1 ‖b₀‖ = ‖b₀‖ from
        max_eq_right (Commons.Analysis.Normed.intVec_norm_ge_one b₀ hb₀_ne)] at h1
      have h6 : (∏ j, Height.mulHeight₁ (Af k j)) ≤ Call := by
        rw [hCalldef]
        exact Finset.le_sup' (fun k : Fin (n+1) => ∏ j, Height.mulHeight₁ (Af k j))
          (Finset.mem_univ k)
      calc Height.mulHeight₁ lB0
          ≤ (((n+1 : ℕ) : ℝ) ^ dK * (∏ j, Height.mulHeight₁ (Af k j)))
              * ‖b₀‖ ^ (dK * (n+1)) := h1
        _ ≤ (((n+1 : ℕ) : ℝ) ^ dK * Call) * ‖b₀‖ ^ (dK * (n+1)) := by
            have hnn : (0:ℝ) ≤ ‖b₀‖ ^ (dK * (n+1)) := by positivity
            apply mul_le_mul_of_nonneg_right _ hnn
            exact mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = C1 * ‖b₀‖ ^ (dK * (n+1)) := by rw [hC1def]
    have hkey : Q ^ (ε/2) / ((n.factorial : ℝ) * C1) ≤ ‖b₀‖ ^ (dK * (n+1)) := by
      have h1 : Q ^ (ε/2) / (n.factorial : ℝ) ≤ C1 * ‖b₀‖ ^ (dK * (n+1)) :=
        le_trans hHlow hHup
      have h2 : Q ^ (ε/2) ≤ ((n.factorial : ℝ) * C1) * ‖b₀‖ ^ (dK * (n+1)) := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < (n.factorial : ℝ))] at h1
        linarith [h1]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (n.factorial : ℝ) * C1)]
      linarith [h2]
    have hb₀_large : Q ^ (ε / (4 * ((dK * (n+1)) : ℝ))) ≤ ‖b₀‖ := by
      have hs : dK * (n+1) ≠ 0 := by positivity
      have hQ4 := hQε4 Q hQ
      have h2 : Q ^ (ε/4) ≤ Q ^ (ε/2) / ((n.factorial : ℝ) * C1) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < (n.factorial : ℝ) * C1)]
        calc Q ^ (ε/4) * ((n.factorial : ℝ) * C1) ≤ Q ^ (ε/4) * Q ^ (ε/4) :=
              mul_le_mul_of_nonneg_left hQ4 (Real.rpow_nonneg hQpos.le _)
          _ = Q ^ (ε/4 + ε/4) := (Real.rpow_add hQpos _ _).symm
          _ = Q ^ (ε/2) := by ring_nf
      have h1 : (Q ^ (ε / (4 * ((dK * (n+1)) : ℝ)))) ^ (dK * (n+1)) = Q ^ (ε/4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
        congr 1
        push_cast
        field_simp
      have h3 : (Q ^ (ε / (4 * ((dK * (n+1)) : ℝ)))) ^ (dK * (n+1))
          ≤ (‖b₀‖) ^ (dK * (n+1)) := by
        rw [h1]; exact le_trans h2 hkey
      exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hQpos.le _) (norm_nonneg _) hs).mp h3
    have hlogb0 : (ε / (4 * ((dK * (n+1)) : ℝ))) * Real.log Q ≤ Real.log ‖b₀‖ := by
      have h1 : (0:ℝ) < Q ^ (ε / (4 * ((dK * (n+1)) : ℝ))) := Real.rpow_pos_of_pos hQpos _
      have h := Real.log_le_log h1 hb₀_large
      rwa [Real.log_rpow hQpos] at h
    -- the ratio
    obtain ⟨a, j, haj, hba, hpr⟩ :=
      Commons.NumberTheory.Height.Vector.pair_ratio_logHeight_ge (N := n+1) (by omega) b₀ hb₀_ne
    have hlogH : Height.logHeight (fun i => ((b₀ i : ℤ) : ℚ)) = Real.log ‖b₀‖ := by
      rw [Height.logHeight_eq_log_mulHeight,
        Commons.NumberTheory.Height.Vector.mulHeight_intVec_ne_zero b₀ hb₀_ne, hgcd]
      simp
    refine ⟨a, j, haj, ?_, ?_⟩
    · intro h0
      apply hba
      have h1 : (b₀ a : ℚ) = 0 := by rw [hcc_apply a, h0]; ring
      exact_mod_cast h1
    · have h1 : Height.logHeight₁ (((b₀ j : ℤ) : ℚ) / ((b₀ a : ℤ) : ℚ))
          = Height.logHeight₁ (((b j : ℤ) : ℚ) / ((b a : ℤ) : ℚ)) := by rw [hratio a j]
      rw [← h1]
      rw [show ((n + 1 - 1 : ℕ) : ℝ) = (n : ℝ) from by simp] at hpr
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have hstep : (Real.log ‖b₀‖) / (n:ℝ)
          ≤ Height.logHeight₁ (((b₀ j : ℤ) : ℚ) / ((b₀ a : ℤ) : ℚ)) := by
        rw [← hlogH, div_le_iff₀ hnpos]
        linarith [hpr]
      have hstep2 : theta * Real.log Q ≤ (Real.log ‖b₀‖) / (n:ℝ) := by
        rw [hthetadef]
        have heq : ε / (4 * (dK:ℝ) * ((n+1:ℕ):ℝ) * (n:ℝ)) * Real.log Q
            = (ε / (4 * ((dK * (n+1)) : ℝ)) * Real.log Q) / (n:ℝ) := by
          field_simp
          push_cast
          ring
        rw [heq]
        exact div_le_div_of_nonneg_right hlogb0 hnpos.le
      linarith [hstep, hstep2]
  · -- Case 2: the hyperplane is one of finitely many
    right
    set J : Finset (Fin (n+1)) :=
      Finset.univ.filter (fun k => ((LK * Gk).submatrix (Fin.succAbove k) id).det = 0) with hJdef
    have hJk : ∀ k : Fin (n+1), k ∈ J ↔ ((LK * Gk).submatrix (Fin.succAbove k) id).det = 0 := by
      intro k; rw [hJdef]; simp
    have hγsmall : ∀ k : Fin (n+1), k ∉ J → γ k < -(ε/2) := by
      intro k hk
      by_contra hcon
      rw [not_lt] at hcon
      refine hcase ⟨k, ?_, hcon⟩
      intro h0
      exact hk ((hJk k).mpr h0)
    -- the adjugate entries over `ℂ`
    have hAf : ∀ (k j : Fin (n+1)),
        (IntermediateField.val K) (Af k j) = (Matrix.of L).adjugate j k := by
      intro k j
      have hmap : ((IntermediateField.val K).toRingHom).mapMatrix LK = Matrix.of L := by
        rw [RingHom.mapMatrix_apply]
        ext i j; rfl
      have h := RingHom.map_adjugate (IntermediateField.val K).toRingHom LK
      rw [hmap] at h
      have h1 := congrFun (congrFun h j) k
      rw [hAfdef]
      simpa [Matrix.map_apply] using h1
    -- the value of `phi k` at an integer vector, over `ℂ`
    have hphiC : ∀ (k : Fin (n+1)) (y : Fin (n+1) → ℤ),
        (IntermediateField.val K) (phi k (fun j => ((y j : ℤ) : ℚ)))
          = ∑ j, (Matrix.of L).adjugate j k * ((y j : ℤ) : ℂ) := by
      intro k y
      rw [hphi_apply, map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_mul]
      have hc : (IntermediateField.val K) ((((y j : ℤ) : ℚ) : ↥K)) = ((y j : ℤ) : ℂ) := by
        rw [map_ratCast]; push_cast; ring
      rw [hc, hAf k j]
      ring
    -- `star` lies in `Lam J`
    have hstar_in : (fun j => ((starVecZ G j : ℤ) : ℚ)) ∈ Lam J := by
      rw [hLam_mem]
      intro k hk
      have hDk0 : ((LK * Gk).submatrix (Fin.succAbove k) id).det = 0 := (hJk k).mp hk
      refine (ZeroMemClass.coe_eq_zero).mp ?_
      change (IntermediateField.val K) (phi k (fun j => ((starVecZ G j : ℤ) : ℚ))) = 0
      rw [hphiC k (starVecZ G)]
      have hcomm := Commons.LinearAlgebra.Matrix.det_succAbove_mul_eq_sum_adjugate n
        (Matrix.of L) (G.map (fun x : ℤ => (x : ℂ))) k
      have h0 : ((Matrix.of L * G.map (fun x : ℤ => (x : ℂ))).submatrix
          (Fin.succAbove k) id).det = 0 := by
        rw [← hdet_id k, hDk0]; simp
      rw [h0] at hcomm
      have hstep : (-1 : ℂ) ^ (k : ℕ) *
            (∑ j : Fin (n+1), (Matrix.of L).adjugate j k * ((starVecZ G j : ℤ) : ℂ))
          = ∑ j : Fin (n+1), (-1 : ℂ) ^ ((j : ℕ) + (k : ℕ)) * (Matrix.of L).adjugate j k *
              ((G.map (fun x : ℤ => (x : ℂ))).submatrix (Fin.succAbove j) id).det := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [starVecZ_cast (R := ℂ) G j, pow_add]
        ring
      have hfin : (-1 : ℂ) ^ (k : ℕ) *
            (∑ j : Fin (n+1), (Matrix.of L).adjugate j k * ((starVecZ G j : ℤ) : ℂ)) = 0 := by
        rw [hstep, ← hcomm]
      exact (mul_eq_zero.mp hfin).resolve_left (pow_ne_zero _ (by norm_num))
    have hΛne : Lam J ≠ ⊥ := by
      intro hbot
      rw [hbot] at hstar_in
      have h1 : (fun j => ((starVecZ G j : ℤ) : ℚ)) = 0 := hstar_in
      have h2 : starVecZ G = 0 := by
        funext j
        have := congrFun h1 j
        simp only [Pi.zero_apply] at this
        exact_mod_cast this
      exact starVecZ_ne_zero G hGcol h2
    have hy0 : cy J ≠ 0 := (hcy J hΛne).1
    have hyin : ∀ k ∈ J, phi k (fun j => ((cy J j : ℤ) : ℚ)) = 0 := by
      intro k hk
      exact (hLam_mem J _).mp (hcy J hΛne).2 k hk
    -- the forward direction: box points are orthogonal to `cy J`
    have hybound : ‖cy J‖ ≤ M := hMbound J
    have hli : ∀ i : Fin (n+1),
        ‖∑ j, (Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ)‖
          ≤ ((n+1 : ℕ) : ℝ) * Cadj * M := by
      intro i
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ j, ‖(Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ)‖
          ≤ ∑ j : Fin (n+1), (Cadj * M) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            rw [norm_mul, Complex.norm_intCast]
            have h1 : ‖(Matrix.of L).adjugate j i‖ ≤ Cadj :=
              Finset.le_sup'
                (f := fun p : Fin (n+1) × Fin (n+1) => ‖(Matrix.of L).adjugate p.1 p.2‖)
                (Finset.mem_univ (j, i))
            have h2 : |(((cy J j : ℤ)) : ℝ)| ≤ M := by
              rw [← Int.norm_eq_abs]
              exact le_trans (norm_le_pi_norm (cy J) j) (hMbound J)
            exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = ((n+1 : ℕ) : ℝ) * (Cadj * M) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = ((n+1 : ℕ) : ℝ) * Cadj * M := by ring
    have hle : approxSpace L γ Q ≤ LinearMap.ker (dotLin (fun j => (cy J j : ℚ))) := by
      intro x hx
      have key : dotLin (fun j => ((cy J j : ℤ) : ℚ)) x = 0 := by
        refine Submodule.span_induction
          (p := fun y _ => dotLin (fun j => ((cy J j : ℤ) : ℚ)) y = 0) ?_ ?_ ?_ ?_ hx
        · rintro v ⟨z, hz, rfl⟩
          simp only [dotLin_apply]
          have hZ : (∑ j, z j * cy J j : ℤ) = 0 := by
            by_contra hne
            have h1 : (1:ℝ) ≤ |(((∑ j, z j * cy J j : ℤ)) : ℝ)| := by
              rw [← Int.cast_abs]
              exact_mod_cast Int.one_le_abs hne
            have h2 : |(((∑ j, z j * cy J j : ℤ)) : ℝ)| < 1 := by
              have hcomm := Commons.LinearAlgebra.Matrix.sum_mul_adjugate_eq (Matrix.of L)
                (fun j => ((z j : ℤ) : ℂ)) (fun j => ((cy J j : ℤ) : ℂ))
              have hZcast : (((∑ j, z j * cy J j : ℤ)) : ℂ)
                  = ∑ j, ((z j : ℤ) : ℂ) * ((cy J j : ℤ) : ℂ) := by
                rw [Int.cast_sum]
                exact Finset.sum_congr rfl (fun j _ => by rw [Int.cast_mul])
              have hsum : (Matrix.of L).det * (((∑ j, z j * cy J j : ℤ)) : ℂ)
                  = ∑ i, (∑ j, (Matrix.of L) i j * ((z j : ℤ) : ℂ)) *
                      (∑ j, (Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ)) := by
                rw [hZcast]
                exact hcomm.symm
              have hzJ : ∀ i ∈ J,
                  (∑ j, (Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ)) = 0 := by
                intro i hi
                have h1 : (IntermediateField.val K)
                    (phi i (fun j => ((cy J j : ℤ) : ℚ))) = 0 := by
                  rw [hyin i hi]; simp
                rwa [hphiC i (cy J)] at h1
              have hbd : ‖∑ i : Fin (n+1), (∑ j, L i j * ((z j : ℤ) : ℂ)) *
                    (∑ j, (Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ))‖
                  < ‖(Matrix.of L).det‖ := by
                have h1 : ‖∑ i : Fin (n+1), (∑ j, L i j * ((z j : ℤ) : ℂ)) *
                      (∑ j, (Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ))‖
                    ≤ ((n+1 : ℕ) : ℝ) *
                        (Q ^ (-(ε/2)) * (((n+1 : ℕ) : ℝ) * Cadj * M)) := by
                  refine le_trans (norm_sum_le _ _) ?_
                  calc ∑ i : Fin (n+1), ‖(∑ j, L i j * ((z j : ℤ) : ℂ)) *
                        (∑ j, (Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ))‖
                      ≤ ∑ i : Fin (n+1), (if i ∉ J then
                          Q ^ (-(ε/2)) * (((n+1 : ℕ) : ℝ) * Cadj * M) else 0) := by
                        refine Finset.sum_le_sum (fun i _ => ?_)
                        by_cases hi : i ∉ J
                        · rw [if_pos hi, norm_mul]
                          refine mul_le_mul ?_ (hli i) (norm_nonneg _) (by positivity)
                          exact le_trans (hz i)
                            (Real.rpow_le_rpow_of_exponent_le hQ1 (le_of_lt (hγsmall i hi)))
                        · rw [if_neg hi, hzJ i (by simpa using hi), mul_zero, norm_zero]
                    _ ≤ ∑ i : Fin (n+1),
                          (Q ^ (-(ε/2)) * (((n+1 : ℕ) : ℝ) * Cadj * M)) := by
                        refine Finset.sum_le_sum (fun i _ => ?_)
                        by_cases hi : i ∉ J
                        · rw [if_pos hi]
                        · rw [if_neg hi]; positivity
                    _ = ((n+1 : ℕ) : ℝ) *
                        (Q ^ (-(ε/2)) * (((n+1 : ℕ) : ℝ) * Cadj * M)) := by
                        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                refine lt_of_le_of_lt h1 ?_
                have hdetpos : (0:ℝ) < ‖(Matrix.of L).det‖ := norm_pos_iff.mpr hL
                have hQ2 := hQcase2 Q hQ
                have hQp : (0:ℝ) < Q ^ (ε/2) := Real.rpow_pos_of_pos hQpos _
                have h6 : ((n+1 : ℕ) : ℝ) * (Q ^ (-(ε/2)) * (((n+1 : ℕ) : ℝ) * Cadj * M))
                    = (((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M) * (Q ^ (ε/2))⁻¹ := by
                  rw [← Real.rpow_neg (le_of_lt hQpos)]
                  ring
                rw [h6]
                have hlt : ((n+1 : ℕ) : ℝ) ^ 2 * Cadj * M / ‖(Matrix.of L).det‖ < Q ^ (ε/2) := by
                  linarith [hQ2]
                rw [div_lt_iff₀ hdetpos] at hlt
                rw [mul_inv_lt_iff₀ hQp]
                linarith [hlt]
              have hZdot : ((Matrix.of L).det * (((∑ j, z j * cy J j : ℤ)) : ℂ))
                  = ∑ i : Fin (n+1), (∑ j, (Matrix.of L) i j * ((z j : ℤ) : ℂ)) *
                      (∑ j, (Matrix.of L).adjugate j i * ((cy J j : ℤ) : ℂ)) := hsum
              have hfin : ‖(Matrix.of L).det‖ *
                    ‖(((∑ j, z j * cy J j : ℤ)) : ℂ)‖ < ‖(Matrix.of L).det‖ := by
                rw [← norm_mul, hZdot]
                exact hbd
              have hdetpos : (0:ℝ) < ‖(Matrix.of L).det‖ := norm_pos_iff.mpr hL
              have h4 : ‖(((∑ j, z j * cy J j : ℤ)) : ℂ)‖
                  = |(((∑ j, z j * cy J j : ℤ)) : ℝ)| := by
                rw [Complex.norm_intCast]
              rw [h4] at hfin
              have hfin' : ‖(Matrix.of L).det‖ * |(((∑ j, z j * cy J j : ℤ)) : ℝ)|
                  < ‖(Matrix.of L).det‖ * 1 := by linarith [hfin]
              exact lt_of_mul_lt_mul_left hfin' hdetpos.le
            linarith [h1, h2]
          have hcast : (∑ j : Fin (n+1), ((cy J j : ℤ) : ℚ) * ((z j : ℤ) : ℚ))
              = ((∑ j, z j * cy J j : ℤ) : ℚ) := by
            push_cast
            exact Finset.sum_congr rfl (fun j _ => by ring)
          rw [hcast, hZ]
          simp
        · simp
        · intro p q hp hq hpp hqq
          rw [map_add, hpp, hqq, add_zero]
        · intro c p hp hpp
          rw [map_smul, hpp, smul_zero]
      exact (LinearMap.mem_ker).mpr (by simpa only [dotLin_apply] using key)
    refine ⟨cy J, hy0, hybound, ?_⟩
    intro x
    constructor
    · intro hx
      have key := (LinearMap.mem_ker).mp (hle hx)
      simpa only [dotLin_apply] using key
    · intro hx
      have hyq_ne : (fun j => (cy J j : ℚ)) ≠ 0 := by
        intro hh
        apply hy0
        funext j
        have := congrFun hh j
        simp only [Pi.zero_apply] at this
        exact_mod_cast this
      have hφne : dotLin (fun j => (cy J j : ℚ)) ≠ 0 := dotLin_ne_zero hyq_ne
      have hkerfin : Module.finrank ℚ (LinearMap.ker (dotLin (fun j => (cy J j : ℚ)))) = n := by
        have h := Module.Dual.finrank_ker_add_one_of_ne_zero hφne
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
        omega
      have heq : LinearMap.ker (dotLin (fun j => (cy J j : ℚ))) = approxSpace L γ Q :=
        (Submodule.eq_of_le_of_finrank_eq hle (by rw [hkerfin, hfr])).symm
      have hx' : x ∈ LinearMap.ker (dotLin (fun j => (cy J j : ℚ))) :=
        (LinearMap.mem_ker).mpr (by simpa only [dotLin_apply] using hx)
      rwa [heq] at hx'

end Submission.Subspace
