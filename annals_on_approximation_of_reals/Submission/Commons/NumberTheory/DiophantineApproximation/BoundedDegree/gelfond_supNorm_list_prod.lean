import Mathlib.Analysis.Polynomial.MahlerMeasure

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

/-!
# Gelfond's sup-norm product lemma

If `P₁,…,P_k ∈ ℤ[X]` are non-zero polynomials of degree `≤ n` with `k ≤ n`, then the
product of their sup-norms is bounded above by a constant `C(n)` times the sup-norm of
their product.  This is the classical *Gelfond lemma* (it is usually stated with the
naive height `H(P) = supNorm (P.map (Int.castRingHom ℝ))`).

Proof strategy (Mahler measure): for complex polynomials the sup norm `H(p)` and the
Mahler measure `M(p)` satisfy `H(p) ≤ (deg p choose (deg p / 2)) · M(p)` and
`M(p) ≤ √(deg p + 1) · H(p)`, while `M` is multiplicative.  Mapping the integer
polynomials into `ℂ[X]` and chaining these inequalities with the degree bounds
`deg p ≤ n` and `k ≤ n` yields the constant `C = (n+1) · 2^(n²)`.
-/

private lemma supNorm_map_eq {A B : Type*} [NormedRing A] [NormedRing B] (p : Polynomial A)
    (f : A →+* B) (h_norm : ∀ a, ‖f a‖ = ‖a‖) : (p.map f).supNorm = p.supNorm := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := (p.map f).exists_eq_supNorm
    rw [hi]
    calc
      ‖(p.map f).coeff i‖ = ‖f (p.coeff i)‖ := by rw [Polynomial.coeff_map]
      _ = ‖p.coeff i‖ := h_norm (p.coeff i)
      _ ≤ p.supNorm := p.le_supNorm i
  · obtain ⟨i, hi⟩ := p.exists_eq_supNorm
    rw [hi]
    calc
      ‖p.coeff i‖ = ‖f (p.coeff i)‖ := (h_norm (p.coeff i)).symm
      _ = ‖(p.map f).coeff i‖ := by rw [Polynomial.coeff_map]
      _ ≤ (p.map f).supNorm := (p.map f).le_supNorm i

private lemma norm_int_real (z : ℤ) : ‖(z : ℝ)‖ = ‖z‖ := by
  rw [Real.norm_eq_abs, Int.norm_eq_abs, ← Int.cast_abs]

private lemma norm_int_complex (z : ℤ) : ‖(z : ℂ)‖ = ‖z‖ := by
  exact Complex.isometry_intCast.norm_map_of_map_zero (by simp) z

private lemma mahlerMeasure_list_prod (ps : List (Polynomial ℂ)) :
    (ps.map fun p : Polynomial ℂ => p.mahlerMeasure).prod = ps.prod.mahlerMeasure := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.map_cons, List.prod_cons, ih]
      exact (Polynomial.mahlerMeasure_mul p ps.prod).symm

private lemma natDegree_list_prod_le_sum (ps : List (Polynomial ℂ)) :
    ps.prod.natDegree ≤ (ps.map (fun p : Polynomial ℂ => p.natDegree)).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.prod_cons, List.map_cons, List.sum_cons]
      exact (Polynomial.natDegree_mul_le.trans (Nat.add_le_add_left ih _))

private lemma list_sum_natDegree_le (ps : List (Polynomial ℂ)) {n : ℕ}
    (hdeg : ∀ p ∈ ps, p.natDegree ≤ n) :
    (ps.map (fun p : Polynomial ℂ => p.natDegree)).sum ≤ ps.length * n := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have hhead : p.natDegree ≤ n := hdeg p List.mem_cons_self
      have ih' := ih (fun q hq => hdeg q (List.mem_cons_of_mem p hq))
      have hm : p.natDegree + (ps.map (fun q : Polynomial ℂ => q.natDegree)).sum ≤ n + ps.length * n :=
        Nat.add_le_add hhead ih'
      exact hm.trans (by rw [Nat.succ_mul, add_comm])

private lemma prod_natDegree_le_sq (n : ℕ) (ps : List (Polynomial ℂ))
    (hlen : ps.length ≤ n) (hdeg : ∀ p ∈ ps, p.natDegree ≤ n) :
    ps.prod.natDegree ≤ n * n := by
  exact (natDegree_list_prod_le_sum ps).trans
    ((list_sum_natDegree_le ps hdeg).trans (Nat.mul_le_mul_right n hlen))

private lemma sqrt_natDegree_le (n D : ℕ) (hD : D ≤ n * n) :
    Real.sqrt ((D : ℝ) + 1) ≤ (n : ℝ) + 1 := by
  have hc : (D : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (by simpa [pow_two] using hD)
  have hpos : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
  have h1 : (D : ℝ) + 1 ≤ (n : ℝ) ^ 2 + 1 := by nlinarith
  have h2 : (n : ℝ) ^ 2 + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith [hpos]
  have hle : (D : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := le_trans h1 h2
  have hsqrt' : Real.sqrt ((D : ℝ) + 1) ≤ Real.sqrt (((n : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (by positivity : 0 ≤ (n : ℝ) + 1)] at hsqrt'

private lemma binom_prod_le (n : ℕ) (ps : List (Polynomial ℂ))
    (hlen : ps.length ≤ n) (hdeg : ∀ p ∈ ps, p.natDegree ≤ n) :
    (ps.map (fun p : Polynomial ℂ => (p.natDegree.choose (p.natDegree / 2) : ℝ))).prod ≤
      (2 : ℝ) ^ (n * n) := by
  have h0 : ∀ p ∈ ps, (0 : ℝ) ≤ (p.natDegree.choose (p.natDegree / 2) : ℝ) := by
    intro p hp; exact_mod_cast Nat.zero_le _
  have hle : ∀ p ∈ ps, (p.natDegree.choose (p.natDegree / 2) : ℝ) ≤ (2 : ℝ) ^ n := by
    intro p hp
    have hd : p.natDegree ≤ n := hdeg p hp
    have hn : p.natDegree.choose (p.natDegree / 2) ≤ 2 ^ n := by
      exact (Nat.choose_le_two_pow p.natDegree (p.natDegree / 2)).trans
        (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hd)
    exact_mod_cast hn
  calc
    (ps.map (fun p : Polynomial ℂ => (p.natDegree.choose (p.natDegree / 2) : ℝ))).prod
        ≤ (ps.map (fun _ : Polynomial ℂ => (2 : ℝ) ^ n)).prod := by
            exact List.prod_map_le_prod_map₀
              (fun p : Polynomial ℂ => (p.natDegree.choose (p.natDegree / 2) : ℝ))
              (fun _ : Polynomial ℂ => (2 : ℝ) ^ n) h0 hle
    _ = ((2 : ℝ) ^ n) ^ ps.length := by simp
    _ ≤ ((2 : ℝ) ^ n) ^ n := pow_le_pow_right₀ (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hlen
    _ = (2 : ℝ) ^ (n * n) := by rw [← pow_mul]

/-- Gelfond's lemma for complex polynomials: the product of the sup-norms of a short
list of bounded-degree polynomials is controlled by the sup-norm of their product. -/
private lemma complex_supNorm_list_prod (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (ps : List (Polynomial ℂ)), ps.length ≤ n →
        (∀ p ∈ ps, p.natDegree ≤ n) →
          (ps.map (fun p : Polynomial ℂ => p.supNorm)).prod ≤ C * ps.prod.supNorm := by
  refine ⟨((n : ℝ) + 1) * (2 : ℝ) ^ (n * n), ?one, ?main⟩
  · have hn : (1 : ℕ) ≤ n + 1 := by omega
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hn
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (n * n) := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact one_le_mul_of_one_le_of_one_le h1 hpow
  · intro ps hlen hdeg
    calc
      (ps.map fun p : Polynomial ℂ => p.supNorm).prod
          ≤ (ps.map (fun p : Polynomial ℂ => (p.natDegree.choose (p.natDegree / 2) : ℝ) * p.mahlerMeasure)).prod := by
            refine List.prod_map_le_prod_map₀ (fun p : Polynomial ℂ => p.supNorm)
                (fun p : Polynomial ℂ => (p.natDegree.choose (p.natDegree / 2) : ℝ) * p.mahlerMeasure) ?h0 ?hle
            · intro p hp; exact p.supNorm_nonneg
            · intro p hp; exact Polynomial.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure p
      _ = (ps.map (fun p : Polynomial ℂ => (p.natDegree.choose (p.natDegree / 2) : ℝ))).prod
          * (ps.map (fun p : Polynomial ℂ => p.mahlerMeasure)).prod := by
            rw [List.prod_map_mul]
      _ = (ps.map (fun p : Polynomial ℂ => (p.natDegree.choose (p.natDegree / 2) : ℝ))).prod
          * ps.prod.mahlerMeasure := by rw [mahlerMeasure_list_prod]
      _ ≤ (2 : ℝ) ^ (n * n) * ps.prod.mahlerMeasure := by
            exact mul_le_mul_of_nonneg_right
              (binom_prod_le n ps hlen hdeg)
              (Polynomial.mahlerMeasure_nonneg _)
      _ ≤ (2 : ℝ) ^ (n * n) *
            (Real.sqrt ((ps.prod.natDegree : ℝ) + 1) * ps.prod.supNorm) := by
            exact mul_le_mul_of_nonneg_left
              (Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm ps.prod)
              (by positivity : 0 ≤ (2 : ℝ) ^ (n * n))
      _ ≤ (2 : ℝ) ^ (n * n) * (((n : ℝ) + 1) * ps.prod.supNorm) := by
            have hD : ps.prod.natDegree ≤ n * n := prod_natDegree_le_sq n ps hlen hdeg
            have hsqrt : Real.sqrt ((ps.prod.natDegree : ℝ) + 1) ≤ (n : ℝ) + 1 :=
              sqrt_natDegree_le n ps.prod.natDegree hD
            have hH : (0 : ℝ) ≤ ps.prod.supNorm := ps.prod.supNorm_nonneg
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt hH)
              (by positivity : 0 ≤ (2 : ℝ) ^ (n * n))
      _ = ((n : ℝ) + 1) * (2 : ℝ) ^ (n * n) * ps.prod.supNorm := by ring

/-- **Gelfond's lemma**: for non-zero integer polynomials of degree at most `n`, of which
there are at most `n`, the product of the sup-norms is bounded by a constant times the
sup-norm of the product (the constant depends only on `n`). -/
theorem gelfond_supNorm_list_prod (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (ws : List (Polynomial ℤ)), ws.length ≤ n →
        (∀ w ∈ ws, w ≠ 0) → (∀ w ∈ ws, w.natDegree ≤ n) →
          (ws.map (fun w ↦ (w.map (Int.castRingHom ℝ)).supNorm)).prod ≤
            C * ((ws.prod.map (Int.castRingHom ℝ)).supNorm) := by
  rcases complex_supNorm_list_prod n with ⟨C, hC1, hCmain⟩
  refine ⟨C, hC1, ?_⟩
  intro ws hlen hne0 hdeg
  let ps : List (Polynomial ℂ) := ws.map (fun w => (w.map (Int.castRingHom ℂ)))
  have hpslen : ps.length ≤ n := by
    simpa [ps] using hlen
  have hpsdeg : ∀ p ∈ ps, p.natDegree ≤ n := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨w, hw, rfl⟩
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective]
    exact hdeg w hw
  calc
    (ws.map (fun w ↦ (w.map (Int.castRingHom ℝ)).supNorm)).prod
        = (ws.map (fun w ↦ (w.map (Int.castRingHom ℂ)).supNorm)).prod := by
            apply congrArg List.prod
            apply List.map_congr_left
            intro w hw
            calc
              (w.map (Int.castRingHom ℝ)).supNorm = w.supNorm :=
                supNorm_map_eq w (Int.castRingHom ℝ) norm_int_real
              _ = (w.map (Int.castRingHom ℂ)).supNorm :=
                (supNorm_map_eq w (Int.castRingHom ℂ) norm_int_complex).symm
    _ = (ps.map (fun p : Polynomial ℂ => p.supNorm)).prod := by
            apply congrArg List.prod
            rw [List.map_map]
            exact List.map_congr_left (by intro w hw; rfl)
    _ ≤ C * ps.prod.supNorm := hCmain ps hpslen hpsdeg
    _ = C * ((ws.prod.map (Int.castRingHom ℝ)).supNorm) := by
            have hpsprod : ps.prod = (ws.prod).map (Int.castRingHom ℂ) := by
              dsimp [ps]
              rw [Polynomial.map_list_prod]
            rw [hpsprod]
            have heq : ((ws.prod.map (Int.castRingHom ℂ)).supNorm) =
                ((ws.prod.map (Int.castRingHom ℝ)).supNorm) := by
              calc
                (ws.prod.map (Int.castRingHom ℂ)).supNorm = ws.prod.supNorm :=
                  supNorm_map_eq ws.prod (Int.castRingHom ℂ) norm_int_complex
                _ = (ws.prod.map (Int.castRingHom ℝ)).supNorm :=
                  (supNorm_map_eq ws.prod (Int.castRingHom ℝ) norm_int_real).symm
            rw [heq]

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree