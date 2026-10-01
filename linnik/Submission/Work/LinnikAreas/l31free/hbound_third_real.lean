import Mathlib
import Submission.Work.LinnikAreas.l31free.hb_real_charSum
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess

open scoped BigOperators

namespace Work.LinnikAreas.l31free

open Commons.NumberTheory.DirichletCharacter

/-! ## The primitive part of a real character is real -/

/-- A character of order dividing `2` has a primitive part of order dividing `2`: `changeLevel` is
injective and commutes with powers, and `changeLevel χ.conductor_dvd_level χ.primitiveCharacter = χ`. -/
private lemma primitiveCharacter_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (h : χ ^ 2 = 1) :
    χ.primitiveCharacter ^ 2 = 1 := by
  refine DirichletCharacter.changeLevel_injective χ.conductor_dvd_level ?_
  rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, h, DirichletCharacter.changeLevel_one]

/-! ## Assembly

HB Lemma 2.5 with `φ = 1/3` for characters of order dividing `2`:

* `Work.LinnikAreas.l31free.hb_real_charSum` is the `k = 3` Burgess character-sum bound
  `≪ q^{1/9+ε} H^{2/3}` for **primitive real** characters, uniformly in the modulus (HB Lemma 2.1
  for cube-free moduli together with HB Lemmas 2.3/2.4 for the cube-full part, the order factor
  `(orderOf χ)^{1/2}` being at most `√2`);
* `Commons…primitive_LFunction_bound` (HB §2, (2.2)–(2.4), three-range partial summation with
  `q₁ = q^{(k+1)/(4k)}`) turns it into `‖L(σ+it,χ)‖ ≪ q^{(1/3)(1-σ)(1+1/k)+ε-δ}(1+|t|)` for
  primitive `χ`, `1 - 1/k ≤ σ ≤ 1`;
* a non-primitive `χ` is reduced to its primitive part (`LFunction_nonprimitive_le` and
  `prod_primeFactors_one_add_rpow_le'`), its primitive part being real by
  `primitiveCharacter_sq_one`;
* for `σ ≥ 1` the crude bound `LFunction_crude_bound` together with `crude_absorb` gives the same
  shape. -/

/-- **HB Lemma 2.5 with `φ = 1/3` for real characters** (the `hbound` slot of HB Lemma 3.1,
consumed by `Work.LinnikAreas.l31free.lemma3_1_free_gen_real`). -/
theorem hbound_third_real {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ ^ 2 = 1 →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ) * Complex.I)‖
          ≤ C * (N:ℝ) ^ (((1:ℝ)/3) * (1 - σ) * (1 + 1/(k:ℝ)) + ε) * (1 + |t|) := by
  have hkR : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hε2 : (0:ℝ) < ε/2 := by positivity
  have hε4 : (0:ℝ) < ε/4 := by positivity
  -- the `k = 3` Burgess character-sum bound for primitive real characters
  obtain ⟨Cs, hCspos, hCs⟩ := hb_real_charSum (ε := ε/2) hε2
  set δ : ℝ := min (ε/4) (1/(48*(k:ℝ))) with hδdef
  have hδ : 0 < δ := lt_min hε4 (by positivity)
  have hδε : δ ≤ ε/4 := min_le_left _ _
  have hδk : δ ≤ 1/(48*(k:ℝ)) := min_le_right _ _
  -- Heath-Brown's §2 argument for primitive characters
  obtain ⟨Cp, hCppos, hCp⟩ := primitive_LFunction_bound k hk (ε := ε/2) (δ := δ)
    hε2 hδ (by linarith) hδk hCspos
  -- the Euler product of a non-primitive character
  obtain ⟨Cpd, hCpdpos, hCpd⟩ :=
    prod_primeFactors_one_add_rpow_le' (σ := (1:ℝ)/2) (δ := ε/4) (by norm_num) hε4
  -- the crude bound for `σ ≥ 1`
  obtain ⟨Cc, hCcpos, hCc⟩ := LFunction_crude_bound
  obtain ⟨Cf, hCfpos, hCf⟩ := crude_absorb (k := k) hk hε
  refine ⟨max (Cp * Cpd) (Cc * Cf) + 1, by positivity, ?_⟩
  intro N _inst χ hχ hsq σ t hσlo hσhi
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le one_pos hN1
  have hσ12 : (1:ℝ)/2 ≤ σ := by
    have h1k : 1/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) hkR
    linarith
  by_cases hσ1 : σ ≤ 1
  · -- the range `σ ≤ 1`: reduce to the primitive character and apply the Burgess bound
    have hE0 : (0:ℝ) ≤ ((1:ℝ)/3) * (1 - σ) * (1 + 1/(k:ℝ)) + ε/2 - δ := by
      have h3 : (0:ℝ) ≤ ((1:ℝ)/3) * (1 - σ) * (1 + 1/(k:ℝ)) := by
        refine mul_nonneg (mul_nonneg (by norm_num) ?_) (by positivity)
        linarith
      linarith [hδε]
    haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hprimne : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ hχ
    have hreal : (χ.primitiveCharacter : DirichletCharacter ℂ χ.conductor) ^ 2 = 1 :=
      primitiveCharacter_sq_one χ hsq
    have hB' : ∀ {M H : ℕ}, 1 ≤ M → 1 ≤ H → H ≤ χ.conductor →
        ‖∑ n ∈ Finset.Ioc M (M + H), χ.primitiveCharacter n‖ ≤
          Cs * (χ.conductor : ℝ) ^ ((1:ℝ)/9 + ε/2) * (H:ℝ)^((2:ℝ)/3) :=
      fun {M H} h1 h2 h3 => hCs χ.primitiveCharacter hprim hprimne hreal h1 h2 h3
    have hpb := hCp χ.conductor χ.primitiveCharacter hprim hprimne hB' σ t hσlo hσ1
    have hred := LFunction_nonprimitive_le χ hχ (σ := σ) hσ12 (t := t)
    have hprod_le : (∏ p ∈ N.primeFactors, (1 + (p:ℝ)^(-σ))) ≤ Cpd * (N:ℝ)^(ε/4) := by
      refine (Finset.prod_le_prod₀ (fun p hp => by positivity) ?_).trans (hCpd N (NeZero.ne N))
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.one_le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ -(1/2:ℝ) by linarith)
      linarith
    have hcondle : (χ.conductor : ℝ) ≤ (N:ℝ) := by
      exact_mod_cast (Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level)
    have hpowc : (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ)
        ≤ (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ) :=
      Real.rpow_le_rpow (by positivity) hcondle hE0
    have hcomb : (N:ℝ)^(ε/4) * (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ)
        ≤ (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) := by
      have hN4 : (0:ℝ) ≤ (N:ℝ)^(ε/4) := Real.rpow_nonneg (le_of_lt hNpos) _
      have hstep : (N:ℝ)^(ε/4) * (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ)
          ≤ (N:ℝ)^(ε/4) * (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ) :=
        mul_le_mul_of_nonneg_left hpowc hN4
      calc (N:ℝ)^(ε/4) * (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ)
          ≤ (N:ℝ)^(ε/4) * (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ) := hstep
        _ = (N:ℝ)^(ε/4 + (((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ)) :=
            (Real.rpow_add hNpos (ε/4) _).symm
        _ ≤ (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ (∏ p ∈ N.primeFactors, (1 + (p:ℝ)^(-σ)))
            * ‖DirichletCharacter.LFunction χ.primitiveCharacter ((σ:ℂ) + (t:ℂ)*Complex.I)‖ := hred
      _ ≤ (Cpd * (N:ℝ)^(ε/4))
            * (Cp * (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ) * (1 + |t|)) :=
          mul_le_mul hprod_le hpb (norm_nonneg _) (by positivity)
      _ = (Cp * Cpd) * ((N:ℝ)^(ε/4)
            * (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ)) * (1 + |t|) := by ring
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε)
            * (1 + |t|) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hcnonneg : (0:ℝ) ≤ (N:ℝ)^(ε/4)
              * (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε/2 - δ) :=
            mul_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _)
              (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          exact mul_le_mul (by linarith [le_max_left (Cp*Cpd) (Cc*Cf)]) hcomb hcnonneg (by positivity)
  · -- the range `σ ≥ 1`: the crude bound
    have hσge : 1 ≤ σ := le_of_lt (lt_of_not_ge hσ1)
    have hcb := hCc N χ hχ σ t hσge
    have hca := hCf N (Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) σ hσge hσhi
    have hpowT : (0:ℝ) ≤ (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) :=
      Real.rpow_nonneg (by positivity) _
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ Cc * (1 + Real.log (N:ℝ)) * (1 + |t|) := hcb
      _ ≤ Cc * (Cf * (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (1 + |t|) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hca (le_of_lt hCcpos)
      _ = (Cc * Cf) * (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by ring
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (N:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε)
            * (1 + |t|) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (by linarith [le_max_right (Cp*Cpd) (Cc*Cf)]) hpowT

end Work.LinnikAreas.l31free
