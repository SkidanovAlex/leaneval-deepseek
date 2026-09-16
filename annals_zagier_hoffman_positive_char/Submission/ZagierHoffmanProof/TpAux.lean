import Submission.ZagierHoffmanProof.BridgeP2
import Submission.ZagierHoffmanProof.AmbTransferVal

/-!
# Auxiliaries for the `𝒯'_w`-route to Theorem D

* the polynomial model `ambGammaPoly` of the `Γ`-factor `ambGammaF`;
* the refined `π̃`-divisibility for elements of the completion `K_∞` (rather than `K`);
* `GSuperEntire` of `tmL` for the Anderson–Thakur datum `(s, H_s)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The polynomial model of `Γ_s` -/

/-- The polynomial (in the `t`-variable) whose value at `θ` is `ambGammaF F s`. -/
noncomputable def ambGammaPoly (s : ℕ) : Polynomial (Ambient F) :=
  if s ≤ Nat.card F then 1 else Polynomial.X ^ Nat.card F - Polynomial.X

lemma ambGammaPoly_of_le {s : ℕ} (hs : s ≤ Nat.card F) : ambGammaPoly F s = 1 := if_pos hs

lemma ambGammaPoly_of_gt {s : ℕ} (hs : Nat.card F < s) :
    ambGammaPoly F s = Polynomial.X ^ Nat.card F - Polynomial.X := if_neg (by omega)

lemma eval_ambGammaPoly (s : ℕ) :
    (ambGammaPoly F s).eval (ambTheta F) = ambGammaF F s := by
  rcases le_or_gt s (Nat.card F) with h | h
  · rw [ambGammaPoly_of_le F h, ambGammaF_of_le F h, Polynomial.eval_one]
  · rw [ambGammaPoly_of_gt F h, ambGammaF_of_gt F h, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X]

lemma ite_one_zero_mem_ambF (P : Prop) [Decidable P] :
    (if P then (1 : Ambient F) else 0) ∈ ambF F := by
  split_ifs with h
  · exact Subfield.one_mem _
  · exact (ambF F).zero_mem

lemma ambGammaPoly_coeff_mem (s n : ℕ) : (ambGammaPoly F s).coeff n ∈ ambF F := by
  rcases le_or_gt s (Nat.card F) with h | h
  · rw [ambGammaPoly_of_le F h]
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Polynomial.coeff_one, if_pos rfl]; exact Subfield.one_mem _
    · rw [Polynomial.coeff_one, if_neg hn]; exact (ambF F).zero_mem
  · rw [ambGammaPoly_of_gt F h, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    exact (ambF F).sub_mem (ite_one_zero_mem_ambF F _) (ite_one_zero_mem_ambF F _)

/-- A polynomial whose coefficients are Frobenius-fixed is fixed by the Frobenius twist. -/
lemma frobTwist_eq_self_of_coeff_mem_ambF (p : Polynomial (Ambient F))
    (hp : ∀ n, p.coeff n ∈ ambF F) :
    frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((p : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((p : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
  ext n
  rw [frobTwist_coeff, pow_one, Polynomial.coeff_coe]
  rw [← mem_ambF_iff]
  exact hp n

lemma frobTwist_ambGammaPoly (s : ℕ) :
    frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((ambGammaPoly F s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((ambGammaPoly F s : Polynomial (Ambient F)) : PowerSeries (Ambient F)) :=
  frobTwist_eq_self_of_coeff_mem_ambF F _ (fun n => ambGammaPoly_coeff_mem F s n)

/-- The product of the `Γ`-factors of a tuple, as a polynomial in `t`. -/
noncomputable def gammaPolyTup {n : ℕ} (𝔰 : Fin n → ℕ+) : Polynomial (Ambient F) :=
  ∏ j : Fin n, ambGammaPoly F (𝔰 j : ℕ)

lemma coe_prod_poly {ι : Type*} (s : Finset ι) (p : ι → Polynomial (Ambient F)) :
    (((∏ i ∈ s, p i) : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ∏ i ∈ s, ((p i : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, Polynomial.coe_mul, ih]

lemma eval_gammaPolyTup {n : ℕ} (𝔰 : Fin n → ℕ+) :
    (gammaPolyTup F 𝔰).eval (ambTheta F) = ∏ j : Fin n, ambGammaF F (𝔰 j : ℕ) := by
  rw [gammaPolyTup, Polynomial.eval_prod]
  exact Finset.prod_congr rfl (fun j _ => eval_ambGammaPoly F (𝔰 j : ℕ))

lemma frobTwist_gammaPolyTup {n : ℕ} (𝔰 : Fin n → ℕ+) :
    frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((gammaPolyTup F 𝔰 : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((gammaPolyTup F 𝔰 : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
  rw [gammaPolyTup, coe_prod_poly, frobTwist_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simpa using frobTwist_ambGammaPoly F (𝔰 j : ℕ)

/-! ## §2. The refined `π̃`-divisibility -/

/-- **Step 3's arithmetic core, in the completion**: if a power `π̃^m` lies in the image of the
completion `K_∞` in the ambient field, then `q - 1` divides `m`.  Indeed the value group of `K_∞`
is `exp ((q-1)ℤ)` (`v_ambInfHom_mem_pred`) while `v (π̃^m) = exp (q m)`. -/
theorem dvd_pred_of_piTilde_pow_mem_range {m : ℕ}
    (h : (ambPiTilde F) ^ m ∈ Set.range (ambInfHom F)) : (Nat.card F - 1) ∣ m := by
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  have hq1 : 1 ≤ Nat.card F := by omega
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm]; exact dvd_zero _
  · obtain ⟨y, hy⟩ := h
    have hne : (ambPiTilde F) ^ m ≠ 0 := pow_ne_zero _ (ambPiTilde_ne_zero F)
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hy
      exact hne hy.symm
    obtain ⟨k, hk⟩ := v_ambInfHom_mem_pred F y hy0
    rw [hy, v_ambPiTilde_pow] at hk
    have hexp : (Nat.card F : ℚ) * (m : ℚ) = ((Nat.card F : ℚ) - 1) * (k : ℚ) :=
      WithZero.exp_injective hk
    have hcast : (((Nat.card F - 1 : ℕ)) : ℚ) = (Nat.card F : ℚ) - 1 := by
      rw [Nat.cast_sub hq1, Nat.cast_one]
    have hZ : (((Nat.card F - 1 : ℕ)) : ℤ) * k = ((Nat.card F : ℕ) : ℤ) * ((m : ℕ) : ℤ) := by
      have h2 : ((((Nat.card F - 1 : ℕ)) : ℤ) * k : ℚ)
          = ((((Nat.card F : ℕ)) : ℤ) * ((m : ℕ) : ℤ) : ℚ) := by
        push_cast
        rw [hcast]
        exact hexp.symm
      exact_mod_cast h2
    have hdivZ : (((Nat.card F - 1 : ℕ)) : ℤ)
        ∣ ((((Nat.card F : ℕ)) : ℤ) * ((m : ℕ) : ℤ)) := ⟨k, hZ.symm⟩
    have hdivN : (Nat.card F - 1) ∣ (Nat.card F) * m := by
      have h3 : (((Nat.card F - 1 : ℕ)) : ℤ) ∣ ((((Nat.card F) * m : ℕ)) : ℤ) := by
        rw [Nat.cast_mul]
        exact hdivZ
      exact_mod_cast h3
    have hcop : Nat.Coprime (Nat.card F - 1) (Nat.card F) :=
      (Nat.coprime_self_sub_left hq1).mpr (Nat.coprime_one_left _)
    exact hcop.dvd_of_dvd_mul_left hdivN

/-! ## §3. `ambK F` sits inside the image of the completion -/

lemma ambK_subset_range_ambInfHom {x : Ambient F} (hx : x ∈ ambK F) :
    x ∈ Set.range (ambInfHom F) := by
  refine ⟨((ambKEquiv F).symm ⟨x, hx⟩ : RatFunc F), ?_⟩
  rw [ambInfHom_coe]
  exact congrArg Subtype.val (RingEquiv.apply_symm_apply (ambKEquiv F) ⟨x, hx⟩)

lemma range_ambInfHom_mul_mem {x y : Ambient F}
    (hx : x ∈ Set.range (ambInfHom F)) (hy : y ∈ Set.range (ambInfHom F)) :
    x * y ∈ Set.range (ambInfHom F) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, map_mul _ _ _⟩

/-! ## §4. The super-entireness of the `L`-series of the `ambH`-datum -/

/-- `GSuperEntire` of `tmL` for lists whose entries carry the Anderson–Thakur polynomials. -/
theorem gSuperEntire_tmL_H (L : List (ℕ × Polynomial (Ambient F)))
    (hH : ∀ x ∈ L, x.2 = ambH F x.1) (hpos : ∀ x ∈ L, 1 ≤ x.1) :
    GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) L) := by
  rw [tmL]
  refine gSuperEntire_atLrPaperGen (γ := ambGamma) (K := Ambient F) (q := Nat.card F)
    (ω := ambOmega F) (L := tmCoe (K := Ambient F) L)
    ambGamma_lt_one gammaArchimedean_rat (two_le_ambCard F)
    (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F) ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hH y hy]
    exact gIsSmall_ambOmega_pow_mul_ambH F (hpos y hy)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [hH y hy]
    exact gSuperEntire_ambH F y.1

end ZagierHoffmanPositiveChar
