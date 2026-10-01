import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_bound_third_of_burgess
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_uniform_of_moment_eps23
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_moment_cubefree_r3
import Submission.Work.LinnikAreas.assembly_own
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_charSum_order_of_cubefree
import Submission.Work.NumberTheory.DirichletCharacter.quarterBurgess
import Submission.Work.LinnikAreas.moment_cubefree_all_r
import Submission.Work.LinnikAreas.charSum_of_moment_all_k
import Submission.Work.LinnikAreas.primitive_LFunction_quarter_order

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN Linnik contract (Submission/Work/LinnikContract/Areas.lean; composition
linnik_of_areas PROVED, so proving all seven areas closes the problem). Read first:
* Submission/Work/LinnikPlan/ROUTE_LEAD.md: §1.2 constants, §3.1 your area with the source and proof sketch, §4 numerics, §5 risks;
* LinnikContract/Defs.lean.
Never use the quarantined lemmas (LinnikContract/Quarantine.lean: q-dependent constants); the build guard will fail. The seeded
Submission/Commons/** is a large sorry-free analytic-number-theory library (ROUTE_LEAD §2.1 inventory); reuse it and do not re-request what
exists. Parallelise: request all independent pieces at once.

Area1 = LBound13 ∧ LBoundSmall: HB Lemma 2.5, the Burgess bound for L(σ+it,χ) near σ=1/2..1 with φ = 1/3 for ALL moduli, and φ = 1/4 for
small-order characters. The chain Burgess → HB Lemmas 3.1/5.2 is complete in the workspace EXCEPT the sixth moment mod p^e (e ≥ 3), which a
sibling lemma agent (LinnikBurgess/burgess_r3_noncubefree) is proving right now. Build everything else and consume that lemma by name.
ROUTE_LEAD notes that φ = 1/4 for small order may be removable; check whether Area7's numerics need it.
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas

open Commons.NumberTheory.DirichletCharacter

/-! ## Part 1: `LBound13` (HB Lemma 2.5 with φ = 1/3)

The chain is

* `burgess_moment_general_r2_eps` (r = 2, all moduli, proved),
* `burgess_moment_cubefree_r3` (r = 3, cube-free moduli, proved) together with
  `Work.LinnikBurgess.burgess_r3_noncubefree` (r = 3, moduli divisible by a cube; the live sibling
  route, statement identical to the stale `burgess_moment_r3_noncubefree_final`),
* `burgess_charSum_uniform_of_moment_eps23` (moments for `r ∈ {2,3}` ⇒ uniform Burgess
  character sum for `k = 3`),
* `LFunction_bound_third_of_burgess` (uniform Burgess ⇒ HB Lemma 2.5 with φ = 1/3).
-/

/-- The sixth moment of Burgess for **every** modulus: cube-free moduli are handled by
`burgess_moment_cubefree_r3`, the others by the `r = 3` non-cube-free moment bound. -/
theorem cubic_moment_all (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ H : ℕ, H ^ 6 ≤ q →
        ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ 6
          ≤ C * (q : ℝ) ^ ε * ((q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := burgess_moment_cubefree_r3 hε
  obtain ⟨C₂, hC₂, h₂⟩ := Work.LinnikAreas.burgess_r3_noncubefree_own2 hε
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro q _inst χ hp hχ H hH
  have hqε : (0 : ℝ) ≤ (q : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hX : (0 : ℝ) ≤ (q : ℝ) * (H : ℝ) ^ 3 + (H : ℝ) ^ 6 * Real.sqrt (q : ℝ) := by positivity
  by_cases hcube : ∃ p : ℕ, p.Prime ∧ p ^ 3 ∣ q
  · refine (h₂ hcube χ hp hχ H hH).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hqε) hX
  · have hcf : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q := fun p hp hp3 => hcube ⟨p, hp, hp3⟩
    refine (h₁ hcf χ hp hχ H hH).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hqε) hX

/-- Uniform Burgess character sum with `k = 3`: from the sixth moment for all moduli. -/
theorem charSum_three_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨C, hC, h⟩ :=
    burgess_charSum_uniform_of_moment_single_eps 3 (Or.inr rfl) (fun ε' hε' => cubic_moment_all ε' hε') hε
  refine ⟨C, hC, ?_⟩
  intro q _inst χ hp hχ N H hN hH hHq
  have hhexp : ((((3 : ℕ) : ℝ) + 1) / (4 * (((3 : ℕ) : ℝ)) ^ 2)) + ε = (1 : ℝ) / 9 + ε := by
    norm_num
  have hhexp2 : (1 : ℝ) - 1 / (((3 : ℕ) : ℝ)) = (2 : ℝ) / 3 := by norm_num
  refine (h χ hp hχ hN hH hHq).trans (le_of_eq ?_)
  rw [hhexp, hhexp2]

/-- **HB Lemma 2.5 with φ = 1/3** (= the first conjunct of Area 1). -/
theorem LBound13_holds : Work.LinnikContract.LBound13 := by
  intro k hk ε' hε'
  have hε4 : (0 : ℝ) < ε' / 4 := by positivity
  have hε2 : (0 : ℝ) < ε' / 2 := by positivity
  obtain ⟨C₃, hC₃, h₃⟩ := charSum_three_uniform (ε' / 4) hε4
  have hB : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖
          ≤ C₃ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 2) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
    intro q _inst χ hp hχ N H hN hH hHq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hstep : (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 4) ≤ (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 2) :=
      Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    refine (h₃ χ hp hχ hN hH hHq).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstep (le_of_lt hC₃)) (by positivity)
  obtain ⟨C, hC, hbound⟩ := LFunction_bound_third_of_burgess (ε := ε' / 2) hε2 k hk hC₃ hB
  refine ⟨C, hC, ?_⟩
  intro N _inst χ hχ σ t hσ hσle
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hstep : (N : ℝ) ^ (((1 : ℝ) / 3) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2)
      ≤ (N : ℝ) ^ (((1 : ℝ) / 3) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  refine (hbound χ hχ σ t hσ hσle).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hstep (le_of_lt hC)) (by positivity)

/-! ## Part 2: `LBoundSmall` (HB Lemma 2.5 with φ = 1/4 for characters of order ≤ log q)

HB's chain is

* Lemma 2.1 for cube-free moduli, **every** `k` (the input `hB` of
  `primitive_LFunction_quarter_order`),
* Lemma 2.3 / 2.4: the `v`-factor `v^{(3k-1)/(4k²)}` of the cubeful part is dominated by
  `(orderOf χ)^{3/(2k)}` (proved in the Commons as `burgess_charSum_order_of_cubefree`),
* the derivation `(2.2)`–`(2.4)` with `q₁ = q^{(k+1)/(4k)}`, which gives the exponent
  `(1/4)(1-σ)(1+1/k)` — this is `primitive_LFunction_quarter_order`,
* the primitive character is then related to the given one by `LFunction_nonprimitive_le`
  and the order factor is absorbed using `(orderOf χ)^{3/(2k)} ≤ C(ε) N^{ε}`.
-/

/-- `2 ≤ orderOf χ` for `χ ≠ 1`. -/
theorem two_le_orderOf {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    2 ≤ orderOf χ := by
  have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
  have h2 : 1 ≤ orderOf χ := orderOf_pos χ
  omega

/-- Every character to modulus `2` is trivial (the unit group is trivial). -/
theorem dirichletCharacter_two_eq_one (χ : DirichletCharacter ℂ 2) : χ = 1 := by
  refine MulChar.ext (fun a => ?_)
  rw [Subsingleton.elim a 1, Units.val_one]
  rw [MulChar.map_one χ, MulChar.one_apply (isUnit_one : IsUnit (1 : ZMod 2))]

/-- If the conductor of `χ` is at most `2` then `χ = 1`. -/
theorem eq_one_of_conductor_le_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (h : χ.conductor ≤ 2) : χ = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hc0 : 1 ≤ χ.conductor := Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero
  have hprim : χ.primitiveCharacter = 1 := by
    rcases (by omega : χ.conductor = 1 ∨ χ.conductor = 2) with h1 | h2
    · have hsub : Subsingleton (ZMod χ.conductor)ˣ :=
        h1 ▸ (inferInstance : Subsingleton (ZMod 1)ˣ)
      refine MulChar.ext (fun a => ?_)
      rw [Subsingleton.elim a 1, Units.val_one]
      rw [MulChar.map_one χ.primitiveCharacter,
        MulChar.one_apply (isUnit_one : IsUnit (1 : ZMod χ.conductor))]
    · have hsub : Subsingleton (ZMod χ.conductor)ˣ :=
        h2 ▸ (inferInstance : Subsingleton (ZMod 2)ˣ)
      refine MulChar.ext (fun a => ?_)
      rw [Subsingleton.elim a 1, Units.val_one]
      rw [MulChar.map_one χ.primitiveCharacter,
        MulChar.one_apply (isUnit_one : IsUnit (1 : ZMod χ.conductor))]
  have hcl : (DirichletCharacter.changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ :=
    DirichletCharacter.changeLevel_primitiveCharacter χ
  rw [hprim, DirichletCharacter.changeLevel_one] at hcl
  exact hcl.symm

/-- The conductor of a non-trivial character is at least `3`. -/
theorem conductor_ge_three {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    3 ≤ χ.conductor := by
  by_contra h
  exact hχ (eq_one_of_conductor_le_two χ (by omega))

/-- **HB Lemma 2.5 with φ = 1/4, non-primitive form.**  From the primitive bound with the
explicit order factor one obtains the same bound for every non-trivial `χ` of order `≤ log N`,
with the order factor absorbed into `N^{ε'}`. -/
theorem quarter_LFunction_nonprimitive {ε' : ℝ} (hε' : 0 < ε') (k : ℕ) (hk : 3 ≤ k)
    {Cp : ℝ} (hCp : 0 < Cp)
    (hprim : ∀ {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
        ‖DirichletCharacter.LFunction ψ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          Cp * (orderOf ψ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * (q : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) * (1 + |t|)) :
    ∃ Cb : ℝ, 0 < Cb ∧ ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      (orderOf χ : ℝ) ≤ Real.log (N : ℝ) →
      ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          Cb * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) := by
  have hε16 : (0 : ℝ) < ε' / 16 := by positivity
  have hε2 : (0 : ℝ) < ε' / 2 := by positivity
  obtain ⟨Cpd, hCpd, hpd⟩ := prod_primeFactors_one_add_rpow_le' (σ := 1 / 2) (by norm_num) hε16
  obtain ⟨C2, hC2, hlog⟩ := Commons.Analysis.Real.log_pow_le_mul_rpow hε16 1
  obtain ⟨Cc, hCc, hcrude⟩ := LFunction_crude_bound
  obtain ⟨Cf, hCf, habs⟩ := Commons.NumberTheory.DirichletCharacter.crude_absorb_quarter hk hε2
  refine ⟨max (Cpd * Cp * C2) (Cc * Cf) + 1, by positivity, ?_⟩
  intro N _inst χ hχ hord σ t hσlo hσhi
  have hN0 : N ≠ 0 := NeZero.ne N
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN0
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hN1
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have horder2 : 2 ≤ orderOf χ := two_le_orderOf χ hχ
  have hlog1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have : (2 : ℝ) ≤ (orderOf χ : ℝ) := by exact_mod_cast horder2
    linarith
  have h3k2le1 : (3 : ℝ) / (2 * (k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 2 * (k : ℝ))]
    linarith
  have h3k2pos : (0 : ℝ) ≤ (3 : ℝ) / (2 * (k : ℝ)) := by positivity
  have horder_le : (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ))) ≤ C2 * (N : ℝ) ^ (ε' / 16) := by
    have h1 : (Real.log (N : ℝ)) ^ ((3 : ℝ) / (2 * (k : ℝ))) ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 h3k2le1
    have h2 : (Real.log (N : ℝ)) ^ (1 : ℝ) = Real.log (N : ℝ) := Real.rpow_one _
    have h3 : Real.log (N : ℝ) ≤ C2 * (N : ℝ) ^ (ε' / 16) := by
      simpa using hlog (N : ℝ) hN1
    calc (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
        ≤ (Real.log (N : ℝ)) ^ ((3 : ℝ) / (2 * (k : ℝ))) :=
          Real.rpow_le_rpow (by positivity) hord h3k2pos
      _ ≤ (Real.log (N : ℝ)) ^ (1 : ℝ) := h1
      _ = Real.log (N : ℝ) := h2
      _ ≤ C2 * (N : ℝ) ^ (ε' / 16) := h3
  have hmax1 : Cpd * Cp * C2 ≤ max (Cpd * Cp * C2) (Cc * Cf) + 1 := by
    have := le_max_left (Cpd * Cp * C2) (Cc * Cf); linarith
  have hmax2 : Cc * Cf ≤ max (Cpd * Cp * C2) (Cc * Cf) + 1 := by
    have := le_max_right (Cpd * Cp * C2) (Cc * Cf); linarith
  by_cases hσ1 : σ ≤ 1
  · -- σ ≤ 1: reduce to the primitive character
    have hσ12 : (1 : ℝ) / 2 ≤ σ := by
      have h1 : 1 / (k : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hkR
      linarith
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hlim := LFunction_nonprimitive_le χ hχ (σ := σ) hσ12 (t := t)
    have hprod : (∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (-σ)))
        ≤ Cpd * (N : ℝ) ^ (ε' / 16) := by
      refine (Finset.prod_le_prod₀ (fun p _ => by positivity) ?_).trans (hpd N hN0)
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.one_le
      have := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ -(1 / 2 : ℝ) by linarith)
      linarith
    have hd3 : 3 ≤ χ.conductor := conductor_ge_three χ hχ
    have hσrange : σ ≤ 1 + Real.log (Real.log (χ.conductor : ℝ)) / Real.log (χ.conductor : ℝ) := by
      have hd1 : (1 : ℝ) < ((χ.conductor : ℕ) : ℝ) := by
        have : (3 : ℝ) ≤ ((χ.conductor : ℕ) : ℝ) := by exact_mod_cast hd3
        linarith
      have h0 : 0 ≤ Real.log (Real.log (χ.conductor : ℝ)) / Real.log (χ.conductor : ℝ) := by
        refine div_nonneg ?_ (le_of_lt (Real.log_pos hd1))
        have hexp : Real.exp 1 < ((χ.conductor : ℕ) : ℝ) :=
          lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast hd3)
        refine Real.log_nonneg ?_
        have hlogd : (1 : ℝ) < Real.log ((χ.conductor : ℕ) : ℝ) := by
          rw [← Real.log_exp 1]
          exact Real.log_lt_log (Real.exp_pos 1) hexp
        exact le_of_lt hlogd
      linarith
    have hpb := hprim χ.primitiveCharacter (DirichletCharacter.primitiveCharacter_isPrimitive χ)
      (primitiveCharacter_ne_one χ hχ) σ t hσlo hσrange
    rw [Commons.NumberTheory.DirichletCharacter.orderOf_primitiveCharacter] at hpb
    have hdN : ((χ.conductor : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (NeZero.pos N) χ.conductor_dvd_level
    have hExpnn : (0 : ℝ) ≤ ((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4 := by
      have : (0 : ℝ) ≤ (1 - σ) * (1 + 1 / (k : ℝ)) :=
        mul_nonneg (by linarith) (by positivity)
      linarith
    have hdpow : ((χ.conductor : ℕ) : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4)
        ≤ (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) :=
      Real.rpow_le_rpow (by positivity) hdN hExpnn
    have hdnn : (0 : ℝ) ≤ ((χ.conductor : ℕ) : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h1nn : (0 : ℝ) ≤ (1 + |t|) := by positivity
    have hBd : ‖DirichletCharacter.LFunction χ.primitiveCharacter ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Cp * (C2 * (N : ℝ) ^ (ε' / 16))
            * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) * (1 + |t|) := by
      have step1 : Cp * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            * ((χ.conductor : ℕ) : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4)
            * (1 + |t|)
          ≤ Cp * (C2 * (N : ℝ) ^ (ε' / 16))
            * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) * (1 + |t|) := by
        have ha : Cp * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
            ≤ Cp * (C2 * (N : ℝ) ^ (ε' / 16)) :=
          mul_le_mul_of_nonneg_left horder_le (le_of_lt hCp)
        have hb : (0 : ℝ) ≤ (1 + |t|) := h1nn
        calc Cp * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ)))
              * ((χ.conductor : ℕ) : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4)
              * (1 + |t|)
            = (Cp * (orderOf χ : ℝ) ^ ((3 : ℝ) / (2 * (k : ℝ))))
              * (((χ.conductor : ℕ) : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4)
                * (1 + |t|)) := by ring
          _ ≤ (Cp * (C2 * (N : ℝ) ^ (ε' / 16)))
              * (((χ.conductor : ℕ) : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4)
                * (1 + |t|)) := mul_le_mul_of_nonneg_right ha (by positivity)
          _ ≤ (Cp * (C2 * (N : ℝ) ^ (ε' / 16)))
              * ((N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4)
                * (1 + |t|)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdpow hb) (by positivity)
          _ = Cp * (C2 * (N : ℝ) ^ (ε' / 16))
              * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) * (1 + |t|) := by ring
      exact hpb.trans step1
    refine hlim.trans ?_
    -- combine the two bounds
    have hstep : (∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (-σ)))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (Cpd * (N : ℝ) ^ (ε' / 16))
          * (Cp * (C2 * (N : ℝ) ^ (ε' / 16))
              * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) * (1 + |t|)) :=
      mul_le_mul hprod hBd (norm_nonneg _) (by positivity)
    refine hstep.trans ?_
    -- rewrite the product of powers of `N`
    have hpow : (N : ℝ) ^ (ε' / 16) * ((N : ℝ) ^ (ε' / 16)
          * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4))
        = (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 16 + ε' / 16 + ε' / 4) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
      congr 1
      ring
    have hfac : (Cpd * (N : ℝ) ^ (ε' / 16))
          * (Cp * (C2 * (N : ℝ) ^ (ε' / 16))
              * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4) * (1 + |t|))
        = (Cpd * Cp * C2)
          * ((N : ℝ) ^ (ε' / 16) * ((N : ℝ) ^ (ε' / 16)
              * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 4)) * (1 + |t|)) := by
      ring
    rw [hfac, hpow]
    have hexple : ((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 16 + ε' / 16 + ε' / 4
        ≤ ((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' := by linarith
    have hpownn : (0 : ℝ) ≤ (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 16 + ε' / 16 + ε' / 4) :=
      Real.rpow_nonneg hNnn _
    have hpowle : (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 16 + ε' / 16 + ε' / 4)
        ≤ (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') :=
      Real.rpow_le_rpow_of_exponent_le hN1 hexple
    have hCbpos : (0 : ℝ) < max (Cpd * Cp * C2) (Cc * Cf) + 1 := by positivity
    calc (Cpd * Cp * C2)
          * ((N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 16 + ε' / 16 + ε' / 4)
              * (1 + |t|))
        ≤ (max (Cpd * Cp * C2) (Cc * Cf) + 1)
          * ((N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 16 + ε' / 16 + ε' / 4)
              * (1 + |t|)) :=
          mul_le_mul_of_nonneg_right hmax1 (by positivity)
      _ ≤ (max (Cpd * Cp * C2) (Cc * Cf) + 1)
          * ((N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpowle h1nn) (le_of_lt hCbpos)
      _ = (max (Cpd * Cp * C2) (Cc * Cf) + 1)
          * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) := by ring
  · -- σ ≥ 1: the crude bound
    have hσge : 1 ≤ σ := le_of_lt (lt_of_not_ge hσ1)
    have hcr := hcrude N χ hχ σ t hσge
    have hab := habs N (Nat.one_le_iff_ne_zero.mpr hN0) σ hσge hσhi
    have hexple' : ((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2
        ≤ ((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' := by linarith
    have hCfpos : (0 : ℝ) < Cf := hCf
    refine hcr.trans ?_
    have hstep : Cc * (1 + Real.log (N : ℝ)) * (1 + |t|)
        ≤ Cc * (Cf * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2))
          * (1 + |t|) := by
      have hCfnn : (0 : ℝ) ≤ Cf := le_of_lt hCf
      calc Cc * (1 + Real.log (N : ℝ)) * (1 + |t|)
          = Cc * ((1 + Real.log (N : ℝ)) * (1 + |t|)) := by ring
        _ ≤ Cc * ((Cf * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2))
              * (1 + |t|)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab (by positivity)) (le_of_lt hCc)
        _ = Cc * (Cf * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2))
              * (1 + |t|) := by ring
    refine hstep.trans ?_
    have hCbpos : (0 : ℝ) < max (Cpd * Cp * C2) (Cc * Cf) + 1 := by positivity
    have hNpow : (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2)
        ≤ (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') :=
      Real.rpow_le_rpow_of_exponent_le hN1 hexple'
    calc Cc * (Cf * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2)) * (1 + |t|)
        = (Cc * Cf) * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2) * (1 + |t|) := by
          ring
      _ ≤ (max (Cpd * Cp * C2) (Cc * Cf) + 1)
            * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε' / 2) * (1 + |t|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax2 (by positivity)) (by positivity)
      _ ≤ (max (Cpd * Cp * C2) (Cc * Cf) + 1)
            * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hNpow (le_of_lt hCbpos)
      _ = (max (Cpd * Cp * C2) (Cc * Cf) + 1)
            * (N : ℝ) ^ (((1 : ℝ) / 4) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε') * (1 + |t|) := by ring



/-- **HB Lemma 2.1, cube-free case, for every `k`**: the cube-free `2r`-th moment bounds for
all `r` (HBB Lemma 2(i)) imply, via the Burgess core argument, the cube-free Burgess character
sum bound for every `k`. -/
theorem cubefree_charSum_all_k (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q], (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ q) →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) :=
  charSum_of_moment_all_k (fun r hr ε' hε' => moment_cubefree_all_r r (by omega) ε' hε') hε k hk

/-- **HB Lemma 2.5 with φ = 1/4** (= the second conjunct of Area 1). -/
theorem LBoundSmall_holds : Work.LinnikContract.LBoundSmall := by
  intro k hk ε' hε'
  have hε16 : (0 : ℝ) < ε' / 16 := by positivity
  have hε4 : (0 : ℝ) < ε' / 4 := by positivity
  obtain ⟨CB, hCB, hB0⟩ := cubefree_charSum_all_k (ε' / 4 / 4) (by positivity) k (by omega)
  have hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖
          ≤ CB * (u : ℝ) ^ ((((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2)) + ε' / 4 / 4)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
    intro u _inst ψ hψ hψ1 hcf N H hN hH hHu
    exact hB0 hcf ψ hψ hψ1 hN hH hHu
  obtain ⟨Cp, hCp, hprim⟩ :=
    primitive_LFunction_quarter_order (ε := ε' / 4) hε4 k hk hCB hB
  obtain ⟨Cb, hCb, hb⟩ := quarter_LFunction_nonprimitive (ε' := ε') hε' k hk hCp hprim
  refine ⟨Cb, hCb, ?_⟩
  intro N _inst χ hχ hord σ t hσ hσle
  exact hb χ hχ hord σ t hσ hσle

theorem area1 : Work.LinnikContract.Area1 := ⟨LBound13_holds, LBoundSmall_holds⟩

end Work.LinnikAreas
