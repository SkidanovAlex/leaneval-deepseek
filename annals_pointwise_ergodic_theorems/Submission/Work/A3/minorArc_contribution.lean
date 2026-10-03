import Mathlib
import Submission.Work.A3.polyEnergyOn_one_le
import Submission.Work.A3.norm_expSum_le_of_not_mem_majorArcSet

/-!
# The minor-arc contribution to the circle method (Area A3)

Given the Weyl-type pointwise bound for the polynomial exponential sum
`S_N(θ) = ∑_{n ≤ N} e(-2πi θ Q(n))` under a Dirichlet approximation `|θ - a/q| ≤ 1/q²`
(the hypothesis `hweyl`, the conclusion of `Work.A3.weyl_poly`), we bound the contribution of
the *minor arcs* — the complement of `Work.A3.majorArcSet Q N η` — to the `2s`-th moment:

  `∫_{minor arcs ∩ [0,1]} ‖S_N(θ)‖^{2s} dθ ≤ C(N) · N^{2s - deg Q}`.

The proof is the classical one:

* Dirichlet's approximation theorem at level `N^{d/2}` produces, for every `θ ∉ majorArcSet Q N η`,
  a reduced `a/q` with `N^η < q ≤ N^{d/2}` and `|θ - a/q| ≤ 1/(q N^{d/2}) ≤ 1/q²`, so that
  `hweyl` applies; all three terms of the Weyl bracket are `≤ N^{-η}`, giving the pointwise
  power saving `‖S_N(θ)‖ ≤ (CW · 3^δ) · N^{1 + ε - η δ}`, `δ = 1/2^{d-1}`
  (`Work.A3.norm_expSum_le_of_not_mem_majorArcSet`);
* interpolation of the `2s`-th moment against the *second* moment:
  `∫_minor ‖S‖^{2s} ≤ (sup_minor ‖S‖)^{2s-2} ∫_0^1 ‖S‖²`, and `∫_0^1 ‖S‖² = polyEnergy Q 1 N`
  is linear in `N` (`O(N) = deg Q · N`), because a nonconstant polynomial of degree `d` has at
  most `d` integral roots (`Work.A3.polyEnergyOn_one_le`);
* the exponent bookkeeping `d - 1 ≤ (2s-2)(ηδ - ε)` (`hsz`) is exactly what is needed to make
  `(2s-2)(1 + ε - ηδ) + 1 ≤ 2s - d`.
-/

set_option autoImplicit false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The major arcs are a countable union of closed intervals, hence measurable. -/
lemma measurableSet_majorArcSet (Q : ℤ[X]) (N : ℕ) (η : ℝ) :
    MeasurableSet (majorArcSet Q N η) := by
  unfold majorArcSet
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => ?_
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (q : ℝ) ≤ (N : ℝ) ^ η
  · convert measurableSet_Icc
        (a := (a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2)))
        (b := (a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * (N : ℝ) ^ ((Q.natDegree : ℝ) / 2))) using 1
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, h, true_and]
    constructor <;> intro hh
    · obtain ⟨h1, h2⟩ := abs_le.mp hh; exact ⟨by linarith, by linarith⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · convert MeasurableSet.empty using 1
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun h1 h2 h3 _ => h ⟨h1, h2, h3⟩

/-- `(x ^ (1/n)) ^ n = x` for `x ≥ 0`, `n > 0`: the round trip through the real power
`x ↦ x^{1/n}`, used to build the constant of the estimate. -/
lemma rpow_div_nat_mul_self {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n) :
    (x ^ ((1 : ℝ) / n)) ^ n = x := by
  rw [← Real.rpow_natCast (x ^ ((1 : ℝ) / n)) n, ← Real.rpow_mul hx]
  have h1 : (1 : ℝ) / (n : ℝ) * (n : ℝ) = 1 := by field_simp
  rw [h1, Real.rpow_one]

/-- **The exponent bookkeeping of the minor arcs.**  In the notation `δ = 2^{1-d}` of Weyl's
inequality, the hypothesis `deg Q - 1 ≤ (2s-2)(ηδ - ε)` is exactly equivalent to
`(2s-2)(1 + ε - ηδ) + 1 ≤ 2s - deg Q`, i.e. to the statement that the product of the pointwise
power saving with the linear bound for the second moment still gains `N^{-d}`. -/
lemma exp_bookkeeping {δ ε η : ℝ} {s d : ℕ} (hs : 2 ≤ s) (hds : d ≤ 2 * s)
    (hsz : ((d : ℝ) - 1) ≤ ((2 * s - 2 : ℕ) : ℝ) * (η * δ - ε)) :
    (1 + ε - η * δ) * ((2 * s - 2 : ℕ) : ℝ) + 1 ≤ ((2 * s - d : ℕ) : ℝ) := by
  have h2s : 2 ≤ 2 * s := by omega
  have h1 : ((2 * s - 2 : ℕ) : ℝ) = (2 * s : ℝ) - 2 := by
    rw [Nat.cast_sub h2s]; norm_num
  have h2 : ((2 * s - d : ℕ) : ℝ) = (2 * s : ℝ) - d := by
    rw [Nat.cast_sub hds]; norm_num
  rw [h1] at hsz ⊢
  rw [h2]
  nlinarith

/-- `(A N^e)^n · c · N = A^n · c · N^{en + 1}`: the product of the pointwise Weyl bound raised to
the power `n = 2s-2` with the linear factor `N` from the second moment. -/
lemma step_identity {A N e c : ℝ} {n : ℕ} (hN : 0 < N) :
    (A * N ^ e) ^ n * c * N = A ^ n * c * N ^ (e * (n : ℝ) + 1) := by
  have h1 : (A * N ^ e) ^ n = A ^ n * (N ^ e) ^ n := mul_pow A (N ^ e) n
  have h2 : (N ^ e) ^ n = N ^ (e * (n : ℝ)) := by
    rw [← Real.rpow_natCast (N ^ e) n, ← Real.rpow_mul hN.le]
  have h3 : N ^ (e * (n : ℝ)) * N = N ^ (e * (n : ℝ) + 1) := by
    rw [Real.rpow_add hN, Real.rpow_one]
  rw [h1, h2, show (A ^ n * N ^ (e * (↑n))) * c * N = (N ^ (e * (↑n)) * N) * (A ^ n * c) by
    ring, h3]
  ring

/-- **The minor-arc integral bound, given the two inputs.**  If

* `hkey` is the pointwise Weyl saving `‖S_N(θ)‖ ≤ (CW · 3^δ) N^{1 + ε - ηδ}` on the complement of
  the major arcs, and
* `henergy` is the linear bound `polyEnergy Q 1 N ≤ deg Q · N` for the second moment,

then the `2s`-th moment over the minor arcs is bounded by `C^{2s} N^{2s - deg Q}`. -/
lemma minorArc_contribution_aux (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {CW ε η δ : ℝ} (hCW : 0 < CW)
    {s : ℕ} (hs : 2 ≤ s) (hds : Polynomial.natDegree Q ≤ 2 * s)
    (hsz : (Polynomial.natDegree Q - 1 : ℝ) ≤ (2 * s - 2 : ℝ) * (η * δ - ε))
    (hkey : ∀ (N : ℕ), 1 ≤ N → ∀ θ : ℝ, θ ∉ majorArcSet Q N η →
      ‖expSum Q N θ‖ ≤ (CW * (3 : ℝ) ^ δ) * (N : ℝ) ^ (1 + ε - η * δ))
    (henergy : ∀ N : ℕ, 1 ≤ N →
      (polyEnergy Q 1 N : ℝ) ≤ (Polynomial.natDegree Q : ℝ) * (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s) ≤
        C ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
  classical
  set A : ℝ := CW * (3 : ℝ) ^ δ with hA
  have hApos : 0 < A := by rw [hA]; positivity
  set d0 : ℝ := (Polynomial.natDegree Q : ℝ) with hd0
  have hd0pos : 0 < d0 := by
    rw [hd0]; exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) hd)
  have h2s : 2 ≤ 2 * s := by omega
  have h2s_sub : ((2 * s - 2 : ℕ) : ℝ) = (2 * s - 2 : ℝ) := by
    rw [Nat.cast_sub h2s]; norm_num
  have hsz' : ((Polynomial.natDegree Q : ℝ) - 1) ≤
      ((2 * s - 2 : ℕ) : ℝ) * (η * δ - ε) := by
    rw [h2s_sub]; exact hsz
  have hexp := exp_bookkeeping (δ := δ) (ε := ε) (η := η) (s := s)
    (d := Polynomial.natDegree Q) hs hds hsz'
  refine ⟨max 1 ((A ^ (2 * s - 2) * d0) ^ ((1 : ℝ) / ((2 * s : ℕ) : ℝ))),
    lt_max_of_lt_left zero_lt_one, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set K : ℝ := (A * (N : ℝ) ^ (1 + ε - η * δ)) ^ (2 * s - 2) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hpt : ∀ θ ∈ (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1,
      ‖expSum Q N θ‖ ^ (2 * s) ≤ K * ‖expSum Q N θ‖ ^ 2 := by
    intro θ hθ
    have hb : ‖expSum Q N θ‖ ≤ A * (N : ℝ) ^ (1 + ε - η * δ) := by
      have h1 := hkey N hN θ hθ.1
      rwa [hA] at h1
    have hsplit : 2 * s = (2 * s - 2) + 2 := by omega
    rw [hsplit, pow_add, hK]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb _) (by positivity)
  have hcont1 : Continuous (fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s)) := by
    unfold expSum; fun_prop
  have hcont2 : Continuous (fun θ : ℝ => K * ‖expSum Q N θ‖ ^ 2) := by
    unfold expSum; fun_prop
  have hcont3 : Continuous (fun θ : ℝ => ‖expSum Q N θ‖ ^ 2) := by
    unfold expSum; fun_prop
  have hint1 : IntegrableOn (fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s))
      ((majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1) volume :=
    (hcont1.integrableOn_Icc).mono_set Set.inter_subset_right
  have hint2 : IntegrableOn (fun θ : ℝ => K * ‖expSum Q N θ‖ ^ 2)
      ((majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1) volume :=
    (hcont2.integrableOn_Icc).mono_set Set.inter_subset_right
  have hint3 : IntegrableOn (fun θ : ℝ => ‖expSum Q N θ‖ ^ 2) (Set.Icc (0 : ℝ) 1) volume :=
    hcont3.integrableOn_Icc
  have step1 : ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
      ≤ ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, K * ‖expSum Q N θ‖ ^ 2 :=
    setIntegral_mono_on hint1 hint2
      ((measurableSet_majorArcSet Q N η).compl.inter measurableSet_Icc) hpt
  have step2 : ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, K * ‖expSum Q N θ‖ ^ 2
      = K * ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 :=
    integral_const_mul K _
  have step3 : ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2
      ≤ ∫ θ in Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 :=
    setIntegral_mono_set hint3 (Filter.Eventually.of_forall (fun θ => by positivity))
      (Filter.Eventually.of_forall (fun θ hθ => hθ.2))
  have step4 : ∫ θ in Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 = (polyEnergy Q 1 N : ℝ) := by
    simpa using integral_norm_expSum_pow Q N 1 hN
  have step5 : (polyEnergy Q 1 N : ℝ) ≤ d0 * (N : ℝ) := by
    rw [hd0]; exact henergy N hN
  calc ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
      ≤ K * ∫ θ in (majorArcSet Q N η)ᶜ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 := by
        rw [← step2]; exact step1
    _ ≤ K * ∫ θ in Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left step3 hKpos.le
    _ = K * (polyEnergy Q 1 N : ℝ) := by rw [step4]
    _ ≤ K * (d0 * (N : ℝ)) := mul_le_mul_of_nonneg_left step5 hKpos.le
    _ = A ^ (2 * s - 2) * d0 * (N : ℝ) ^ ((1 + ε - η * δ) * ((2 * s - 2 : ℕ) : ℝ) + 1) := by
        rw [hK]
        rw [show (A * ↑N ^ (1 + ε - η * δ)) ^ (2 * s - 2) * (d0 * ↑N)
              = (A * ↑N ^ (1 + ε - η * δ)) ^ (2 * s - 2) * d0 * ↑N by ring]
        exact step_identity (A := A) (N := (N : ℝ)) (e := 1 + ε - η * δ) (c := d0) hNpos
    _ ≤ A ^ (2 * s - 2) * d0 * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_natCast (N : ℝ) (2 * s - Polynomial.natDegree Q)]
        exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
    _ ≤ (max 1 ((A ^ (2 * s - 2) * d0) ^ ((1 : ℝ) / ((2 * s : ℕ) : ℝ)))) ^ (2 * s)
          * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        refine (le_of_eq (rpow_div_nat_mul_self (x := A ^ (2 * s - 2) * d0) (by positivity)
          (by omega : 0 < 2 * s)).symm).trans ?_
        exact pow_le_pow_left₀ (by positivity) (le_max_right 1 _) (2 * s)

theorem minorArc_contribution (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {CW ε : ℝ} (hCW : 0 < CW) (hε : 0 < ε)
    (hweyl : ∀ (M : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ M → 1 ≤ q → IsCoprime a q →
      |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
      ‖Work.A3.expSum Q M θ‖ ≤ CW * (M : ℝ) ^ (1 + ε) *
        (((q : ℝ)⁻¹ + (M : ℝ)⁻¹ + (q : ℝ) * (M : ℝ) ^ (-((Polynomial.natDegree Q : ℤ))))
          ^ ((1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1))))
    {s : ℕ} (hs : 2 ≤ s) (hds : Polynomial.natDegree Q ≤ 2 * s)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hsz : (Polynomial.natDegree Q - 1 : ℝ) ≤
      (2 * s - 2 : ℝ) * (η * (1 / (2 : ℝ) ^ (Polynomial.natDegree Q - 1)) - ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ∫ θ in (Work.A3.majorArcSet Q N η)ᶜ ∩ Set.Icc (0:ℝ) 1, ‖Work.A3.expSum Q N θ‖ ^ (2 * s) ≤
        C ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
  refine minorArc_contribution_aux Q hd hCW hs hds hsz ?_ ?_
  · intro N hN θ hθ
    exact norm_expSum_le_of_not_mem_majorArcSet Q hd hCW hε hη hη1 hweyl hN hθ
  · intro N hN
    have h := polyEnergyOn_one_le Q (le_trans (by norm_num : (1 : ℕ) ≤ 2) hd)
      (Finset.Icc (1 : ℤ) (N : ℤ))
    have hcard : (((Finset.Icc (1 : ℤ) (N : ℤ)).card : ℕ) : ℝ) = (N : ℝ) := by
      rw [Int.card_Icc]; simp
    calc (polyEnergy Q 1 N : ℝ)
        = (polyEnergyOn Q 1 (Finset.Icc (1 : ℤ) (N : ℤ)) : ℝ) := by
          rw [polyEnergy_eq_polyEnergyOn]
      _ ≤ ((Polynomial.natDegree Q : ℝ) * ((Finset.Icc (1 : ℤ) (N : ℤ)).card : ℝ)) := by
          exact_mod_cast h
      _ = (Polynomial.natDegree Q : ℝ) * (N : ℝ) := by rw [hcard]

end

end Work.A3
