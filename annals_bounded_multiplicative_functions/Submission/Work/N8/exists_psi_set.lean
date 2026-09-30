import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.N8.integral_coeff_denom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.N8.exists_psi_set`

Given `k` and `Q₀`, there is `R₀ ≥ k!·Q₀^k` such that for every `1 ≤ q₀ ≤ Q₀` and every finite
family of degree-`≤ k` polynomials `γ` integral on `q₀ℤ`, the functions `e(-γ(·))` all lie in a
single finite set `Ψ` of `(k!·q₀^k)`-periodic bounded functions with `#Ψ ≤ R₀^{R₀}`.

The proof: `M := k!·q₀^k` clears the denominators of `γ` (`int_poly_of_integralOn`), so `M·γ`
is an integer polynomial; hence `γ(n) mod 1` depends only on `n mod M` and takes at most `M`
values per position.  Encoding such a function by `n ↦ g(n mod M)` with `g : ZMod M → ZMod M`
(`exists_psi_repr`) gives a surjection from a set of cardinality `M^M ≤ R₀^{R₀}` with
`R₀ := k!·Q₀^k`.
-/

namespace Work.N8

open Polynomial Finset Real Complex

/-! ## Elementary properties of `eC (t) = e(t) = exp(2πit)` -/

private lemma eC_eq (t : ℝ) : Work.BMF.eC t = Complex.exp (((2 * Real.pi * t : ℝ)) * Complex.I) := by
  rw [Work.BMF.eC]
  congr 1
  push_cast
  ring

private lemma eC_add' (t s : ℝ) : Work.BMF.eC (t + s) = Work.BMF.eC t * Work.BMF.eC s := by
  rw [eC_eq, eC_eq, eC_eq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma eC_int (m : ℤ) : Work.BMF.eC (m : ℝ) = 1 := by
  rw [eC_eq]
  have h : (((2 * Real.pi * (m:ℝ) : ℝ)) : ℂ) * Complex.I
      = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private lemma eC_sub_int (t : ℝ) (m : ℤ) : Work.BMF.eC (t - (m:ℝ)) = Work.BMF.eC t := by
  have h : t - (m:ℝ) = t + ((-m : ℤ) : ℝ) := by push_cast; ring
  rw [h, eC_add', eC_int, mul_one]

private lemma eC_norm (t : ℝ) : ‖Work.BMF.eC t‖ = 1 := by
  rw [eC_eq, Complex.norm_exp_ofReal_mul_I]

/-! ## Clearing denominators of an integral polynomial -/

/-- Evaluating the image in `ℝ[X]` of an integer polynomial at an integer is the image of the
value of the integer polynomial. -/
private lemma eval_map_intCast (P : Polynomial ℤ) (z : ℤ) :
    (P.map (Int.castRingHom ℝ)).eval (z : ℝ) = ((P.eval z : ℤ) : ℝ) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (Int.castRingHom ℝ) z

/-- If `γ : ℝ[X]` has degree `≤ k` and is integral on `qℤ` (`q ≥ 1`), then `k!·q^k·γ` is the
image of an integer polynomial (the denominator clearing of MRTTZ's `int_fine`). -/
theorem int_poly_of_integralOn (k q : ℕ) (hq : 1 ≤ q) {γ : Polynomial ℝ}
    (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn (q : ℝ) γ) :
    ∃ S : Polynomial ℤ, Polynomial.C (((k.factorial * q ^ k : ℕ) : ℝ)) * γ
      = S.map (Int.castRingHom ℝ) := by
  obtain ⟨c, hc⟩ := Work.N8.integral_coeff_denom k q hq hdeg hint
  refine ⟨∑ m ∈ Finset.range (k + 1), Polynomial.C (c m) * Polynomial.X ^ m, ?_⟩
  have hM0 : ((k.factorial * q ^ k : ℕ) : ℝ) ≠ 0 := by
    have h : (0 : ℕ) < k.factorial * q ^ k :=
      Nat.mul_pos (Nat.factorial_pos k) (pow_pos (by omega) k)
    exact_mod_cast (Nat.pos_iff_ne_zero.mp h)
  rw [hc, Finset.mul_sum, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, ← mul_assoc,
    ← Polynomial.C_mul, mul_div_cancel₀ (c m : ℝ) hM0]
  simp only [Int.coe_castRingHom]

/-! ## Evaluation of integer polynomials modulo `m` -/

/-- Evaluation of an integer polynomial preserves congruence of the arguments. -/
theorem eval_modEq_int (S : Polynomial ℤ) {r n m : ℤ} (h : n ≡ m [ZMOD r]) :
    S.eval n ≡ S.eval m [ZMOD r] := by
  rw [Int.modEq_iff_dvd] at h ⊢
  exact dvd_trans h (Polynomial.sub_dvd_eval_sub m n S)

/-! ## Periodicity of the encoded functions -/

private lemma isPeriodicBdd_eC_zmod (M : ℕ) (hM : 0 < M) (g : ZMod M → ZMod M) :
    Work.BMF.IsPeriodicBdd M
      (fun n : ℕ => Work.BMF.eC (-(((g ((n : ℕ) : ZMod M)).val : ℝ) / (M : ℝ)))) := by
  refine ⟨hM, ?_, ?_⟩
  · intro n
    have h : ((n + M : ℕ) : ZMod M) = ((n : ℕ) : ZMod M) := by
      push_cast
      rw [ZMod.natCast_self, add_zero]
    simp only [h]
  · intro n
    rw [eC_norm]

/-! ## The encoding of a single `e(-γ(·))` -/

/-- Every `ψ = e(-γ(·))` with `γ : ℝ[X]` of degree `≤ k` integral on `qℤ` is one of the `M^M`
functions encoded by `g : ZMod M → ZMod M`, `ψ_g(n) = e(-(g(n)).val / M)`, `M = k!·q^k`. -/
theorem exists_psi_repr (k q : ℕ) (hq : 1 ≤ q) {γ : Polynomial ℝ}
    (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn (q : ℝ) γ) :
    ∃ g : ZMod (k.factorial * q ^ k) → ZMod (k.factorial * q ^ k),
      ∀ n : ℕ, Work.BMF.eC (-(γ.eval (n : ℝ))) =
        Work.BMF.eC (-(((g ((n : ℕ) : ZMod (k.factorial * q ^ k))).val : ℝ)
          / ((k.factorial * q ^ k : ℕ) : ℝ))) := by
  set M : ℕ := k.factorial * q ^ k with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; exact Nat.mul_pos (Nat.factorial_pos k) (pow_pos (by omega) k)
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hMpos⟩
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hMpos)
  obtain ⟨S, hS⟩ := int_poly_of_integralOn k q hq hdeg hint
  set g : ZMod M → ZMod M :=
    (fun a => Polynomial.eval₂ (Int.castRingHom (ZMod M)) a S) with hgdef
  refine ⟨g, ?_⟩
  intro n
  set W : ℤ := S.eval ((n : ℕ) : ℤ) with hWdef
  have hMn : (M : ℝ) * γ.eval (n : ℝ) = ((W : ℤ) : ℝ) := by
    have h := congrArg (fun p : Polynomial ℝ => p.eval (n : ℝ)) hS
    simp only [Polynomial.eval_mul, Polynomial.eval_C] at h
    rw [h, hWdef]
    simpa using eval_map_intCast S ((n : ℕ) : ℤ)
  have hg : g ((n : ℕ) : ZMod M) = ((W : ℤ) : ZMod M) := by
    have hcast : (((n : ℕ)) : ZMod M) = (((n : ℕ) : ℤ) : ZMod M) := by push_cast; ring
    change Polynomial.eval₂ (Int.castRingHom (ZMod M)) (((n : ℕ)) : ZMod M) S
      = ((W : ℤ) : ZMod M)
    rw [hcast, hWdef]
    exact Polynomial.eval₂_at_apply (Int.castRingHom (ZMod M)) ((n : ℕ) : ℤ)
  have hmod : (((g ((n : ℕ) : ZMod M)).val : ℕ) : ℤ) ≡ W [ZMOD (M : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ M).mp
    simp only [Int.cast_natCast]
    rw [ZMod.natCast_zmod_val, hg]
  obtain ⟨t, ht⟩ := hmod.dvd
  have hW : W = (((g ((n : ℕ) : ZMod M)).val : ℕ) : ℤ) + (M : ℤ) * t := by omega
  have hγ : γ.eval (n : ℝ) = ((g ((n : ℕ) : ZMod M)).val : ℝ) / (M : ℝ) + (t : ℝ) := by
    have h1 : (M : ℝ) * γ.eval (n : ℝ)
        = ((g ((n : ℕ) : ZMod M)).val : ℝ) + (M : ℝ) * (t : ℝ) := by
      rw [hMn, hW]
      push_cast
      ring
    have h2 : γ.eval (n : ℝ) - (t : ℝ) = ((g ((n : ℕ) : ZMod M)).val : ℝ) / (M : ℝ) := by
      rw [eq_div_iff hM0]
      nlinarith [h1]
    linarith
  have harg : -(γ.eval (n : ℝ))
      = (-(((g ((n : ℕ) : ZMod M)).val : ℝ) / (M : ℝ))) + (((-t : ℤ)) : ℝ) := by
    rw [hγ]
    push_cast
    ring
  rw [harg, eC_add', eC_int, mul_one]

/-! ## The finite set `Ψ` -/

theorem exists_psi_set (k : ℕ) (Q₀ : ℕ) (hQ₀ : 1 ≤ Q₀) :
    ∃ R₀ : ℕ, 1 ≤ R₀ ∧ k.factorial * Q₀ ^ k ≤ R₀ ∧
      ∀ (q₀ : ℕ), 1 ≤ q₀ → q₀ ≤ Q₀ →
      ∀ (V : Finset (ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ))
        (gam : ℝ × ℕ × ℕ × Polynomial ℝ × Finset ℕ → Polynomial ℝ),
        (∀ v ∈ V, (gam v).natDegree ≤ k) →
        (∀ v ∈ V, Work.BMF.IntegralOn (q₀ : ℝ) (gam v)) →
        ∃ Ψ : Finset (ℕ → ℂ),
          (∀ v ∈ V, (fun n : ℕ => Work.BMF.eC (-(gam v).eval (n : ℝ))) ∈ Ψ) ∧
          (∀ ψ ∈ Ψ, Work.BMF.IsPeriodicBdd (k.factorial * q₀ ^ k) ψ) ∧
          (Ψ.card : ℝ) ≤ (R₀ : ℝ) ^ R₀ := by
  classical
  refine ⟨k.factorial * Q₀ ^ k, ?_, le_rfl, ?_⟩
  · rw [Nat.one_le_iff_ne_zero]
    exact Nat.mul_ne_zero (Nat.factorial_ne_zero k) (pow_ne_zero k (by omega))
  · intro q₀ hq₀ hqQ V gam hdeg hint
    set M : ℕ := k.factorial * q₀ ^ k with hMdef
    set R : ℕ := k.factorial * Q₀ ^ k with hRdef
    have hMpos : 0 < M := by
      rw [hMdef]; exact Nat.mul_pos (Nat.factorial_pos k) (pow_pos (by omega) k)
    haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hMpos⟩
    let F : (ZMod M → ZMod M) → (ℕ → ℂ) :=
      fun g n => Work.BMF.eC (-(((g ((n : ℕ) : ZMod M)).val : ℝ) / (M : ℝ)))
    refine ⟨(Finset.univ : Finset (ZMod M → ZMod M)).image F, ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨g, hg⟩ := exists_psi_repr k q₀ hq₀ (hdeg v hv) (hint v hv)
      exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, funext (fun n => (hg n).symm)⟩
    · intro ψ hψ
      obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hψ
      rw [← hg]
      exact isPeriodicBdd_eC_zmod M hMpos g
    · have hcard : ((Finset.univ : Finset (ZMod M → ZMod M)).image F).card ≤ M ^ M := by
        calc ((Finset.univ : Finset (ZMod M → ZMod M)).image F).card
            ≤ (Finset.univ : Finset (ZMod M → ZMod M)).card := Finset.card_image_le
          _ = M ^ M := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
      have hMR : M ≤ R := by
        rw [hMdef, hRdef]
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqQ k)
      have hpow : M ^ M ≤ R ^ R := by
        calc M ^ M ≤ R ^ M := Nat.pow_le_pow_left hMR M
          _ ≤ R ^ R := Nat.pow_le_pow_right (by omega) hMR
      have h1 : (((Finset.univ : Finset (ZMod M → ZMod M)).image F).card : ℝ)
          ≤ ((M ^ M : ℕ) : ℝ) := by exact_mod_cast hcard
      have h2 : ((M ^ M : ℕ) : ℝ) ≤ ((R ^ R : ℕ) : ℝ) := by exact_mod_cast hpow
      have h3 : ((R ^ R : ℕ) : ℝ) = (R : ℝ) ^ R := by push_cast; ring
      linarith

end Work.N8
