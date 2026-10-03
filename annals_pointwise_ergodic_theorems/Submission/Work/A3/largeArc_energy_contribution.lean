import Mathlib
import Submission.Work.A3.majorArc_split
import Submission.Work.A3.minorArc_contribution

/-!
# The `L²`-interpolation bound on the large-denominator arcs (Area A3)

For `θ` on the "large denominator" arcs `largeArcSet Q N η γ` — the arcs of radius
`1/(q N^{d/2})` around reduced fractions `a/q` with `N^γ ≤ q ≤ N^η`, `d = deg Q` — Weyl's
inequality gives the pointwise power saving

  `‖expSum Q N θ‖ ≤ C N^{1 + ε - γ/2^{d-1}}`   (`Work.A3.expSum_le_of_largeArc`).

Interpolating this against the *sharp* second moment `∫₀¹‖expSum Q N‖² = E₁(N) ≤ d·N`
(`Work.A3.integral_norm_expSum_pow` + `Work.A3.polyEnergyOn_one_le`, i.e. a nonconstant
polynomial of degree `d` takes each value at most `d` times) yields

  `∫_{largeArcSet ∩ [0,1]} ‖expSum Q N‖^{2s} ≤ C^{2s} N^{2s-d}`

as soon as the exponent bookkeeping `d - 1 ≤ (2s-2)(γ/2^{d-1} - ε)` holds, i.e. exactly when
`(2s-2)(1 + ε - γ/2^{d-1}) + 1 ≤ 2s - d`: the `2s-2` powers of the pointwise saving must pay for
the loss of `d - 1` powers of `N` relative to the trivial `N^{2s-2}·N` bound.  This is the
`q ≥ N^γ` ("large denominator", also called "deep shoulder"-free) part of the major-arc analysis
of the circle method, see `NOTES_A3_deepShoulder_SESSION.md`.

All the analytic ingredients are the same as for the *minor* arcs
(`Work.A3.minorArc_contribution_aux`): only the pointwise input and the set change.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The large-denominator arcs are a countable union of closed intervals, hence measurable. -/
lemma measurableSet_largeArcSet (Q : Polynomial ℤ) (N : ℕ) (η γ : ℝ) :
    MeasurableSet (largeArcSet Q N η γ) := by
  unfold largeArcSet
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => ?_
  rw [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ IsCoprime a (q : ℤ) ∧ (N : ℝ) ^ γ ≤ (q : ℝ) ∧
      (q : ℝ) ≤ (N : ℝ) ^ η
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
    exact fun h1 h2 h3 h4 _ => h ⟨h1, h2, h3, h4⟩

theorem largeArc_energy_contribution (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {ε γ η : ℝ} (hε : 0 < ε) (hη : η ≤ 1) {s : ℕ} (hs : 2 ≤ s)
    (hds : Polynomial.natDegree Q ≤ 2 * s)
    (hcond : (Polynomial.natDegree Q : ℝ) - 1 ≤
      (2 * (s : ℝ) - 2) * (γ / (2 : ℝ) ^ (Polynomial.natDegree Q - 1) - ε)) :
    ∃ C > 0, ∀ N : ℕ, 1 ≤ N →
      ∫ θ in Work.A3.largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1, ‖Work.A3.expSum Q N θ‖ ^ (2 * s)
        ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
  classical
  obtain ⟨CW, hCWpos, hkey⟩ := expSum_le_of_largeArc Q hd hε hη
  set d : ℕ := Polynomial.natDegree Q with hdQ
  have hds' : d ≤ 2 * s := hds
  have h2s : 2 ≤ 2 * s := by omega
  have hcast : ((2 * s - 2 : ℕ) : ℝ) = 2 * (s : ℝ) - 2 := by
    rw [Nat.cast_sub h2s]; norm_num
  set b : ℝ := γ / (2 : ℝ) ^ (d - 1) with hb
  have hexp : (1 + ε - b) * ((2 * s - 2 : ℕ) : ℝ) + 1 ≤ ((2 * s - d : ℕ) : ℝ) := by
    have hsz : (d : ℝ) - 1 ≤ ((2 * s - 2 : ℕ) : ℝ) * (1 * b - ε) := by
      rw [one_mul, hcast, hb]
      exact hcond
    simpa using exp_bookkeeping (δ := b) (ε := ε) (η := 1) (s := s) (d := d) hs hds' hsz
  refine ⟨max 1 ((CW ^ (2 * s - 2) * (d : ℝ)) ^ ((1 : ℝ) / ((2 * s : ℕ) : ℝ))),
    lt_max_of_lt_left zero_lt_one, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hKpos : (0 : ℝ) < (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) := by positivity
  have hpt : ∀ θ ∈ largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1,
      ‖expSum Q N θ‖ ^ (2 * s) ≤
        (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * ‖expSum Q N θ‖ ^ 2 := by
    intro θ hθ
    have hbnd : ‖expSum Q N θ‖ ≤ CW * (N : ℝ) ^ (1 + ε - b) := by
      simpa only [hb] using hkey N θ hN hθ.1
    have hsplit : 2 * s = (2 * s - 2) + 2 := by omega
    rw [hsplit, pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hbnd _) (by positivity)
  have hcont1 : Continuous (fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s)) := by
    unfold expSum; fun_prop
  have hcont2 : Continuous (fun θ : ℝ =>
      (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * ‖expSum Q N θ‖ ^ 2) := by
    unfold expSum; fun_prop
  have hcont3 : Continuous (fun θ : ℝ => ‖expSum Q N θ‖ ^ 2) := by
    unfold expSum; fun_prop
  have hint1 : IntegrableOn (fun θ : ℝ => ‖expSum Q N θ‖ ^ (2 * s))
      (largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1) volume :=
    (hcont1.integrableOn_Icc).mono_set Set.inter_subset_right
  have hint2 : IntegrableOn (fun θ : ℝ =>
      (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * ‖expSum Q N θ‖ ^ 2)
      (largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1) volume :=
    (hcont2.integrableOn_Icc).mono_set Set.inter_subset_right
  have hint3 : IntegrableOn (fun θ : ℝ => ‖expSum Q N θ‖ ^ 2) (Set.Icc (0 : ℝ) 1) volume :=
    hcont3.integrableOn_Icc
  have hmeas : MeasurableSet (largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1) :=
    (measurableSet_largeArcSet Q N η γ).inter measurableSet_Icc
  have step1 : ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
      ≤ ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1,
          (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * ‖expSum Q N θ‖ ^ 2 :=
    setIntegral_mono_on hint1 hint2 hmeas hpt
  have step2 : ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1,
        (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * ‖expSum Q N θ‖ ^ 2
      = (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) *
        ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 :=
    integral_const_mul _ _
  have step3 : ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2
      ≤ ∫ θ in Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 :=
    setIntegral_mono_set hint3 (Filter.Eventually.of_forall (fun θ => by positivity))
      (Filter.Eventually.of_forall (fun θ hθ => hθ.2))
  have step4 : ∫ θ in Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 = (polyEnergy Q 1 N : ℝ) := by
    simpa using integral_norm_expSum_pow Q N 1 hN
  have step5 : (polyEnergy Q 1 N : ℝ) ≤ (d : ℝ) * (N : ℝ) := by
    have h := polyEnergyOn_one_le Q (le_trans (by norm_num : (1 : ℕ) ≤ 2) hd)
      (Finset.Icc (1 : ℤ) (N : ℤ))
    have hcard : (((Finset.Icc (1 : ℤ) (N : ℤ)).card : ℕ) : ℝ) = (N : ℝ) := by
      rw [Int.card_Icc]; simp
    calc (polyEnergy Q 1 N : ℝ)
        = (polyEnergyOn Q 1 (Finset.Icc (1 : ℤ) (N : ℤ)) : ℝ) := by
          rw [polyEnergy_eq_polyEnergyOn]
      _ ≤ ((Polynomial.natDegree Q : ℝ) * ((Finset.Icc (1 : ℤ) (N : ℤ)).card : ℝ)) := by
          exact_mod_cast h
      _ = (d : ℝ) * (N : ℝ) := by rw [← hdQ, hcard]
  calc ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ (2 * s)
      ≤ (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) *
          ∫ θ in largeArcSet Q N η γ ∩ Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 := by
        rw [← step2]; exact step1
    _ ≤ (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) *
          ∫ θ in Set.Icc (0 : ℝ) 1, ‖expSum Q N θ‖ ^ 2 :=
        mul_le_mul_of_nonneg_left step3 hKpos.le
    _ = (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * (polyEnergy Q 1 N : ℝ) := by rw [step4]
    _ ≤ (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * ((d : ℝ) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left step5 hKpos.le
    _ = CW ^ (2 * s - 2) * (d : ℝ) *
          (N : ℝ) ^ ((1 + ε - b) * ((2 * s - 2 : ℕ) : ℝ) + 1) := by
        rw [show (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * ((d : ℝ) * (N : ℝ))
              = (CW * (N : ℝ) ^ (1 + ε - b)) ^ (2 * s - 2) * (d : ℝ) * (N : ℝ) by ring]
        exact step_identity (A := CW) (N := (N : ℝ)) (e := 1 + ε - b) (c := (d : ℝ)) hNpos
    _ ≤ CW ^ (2 * s - 2) * (d : ℝ) * (N : ℝ) ^ (2 * s - d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_natCast (N : ℝ) (2 * s - d)]
        exact Real.rpow_le_rpow_of_exponent_le hN1 hexp
    _ ≤ (max 1 ((CW ^ (2 * s - 2) * (d : ℝ)) ^ ((1 : ℝ) / ((2 * s : ℕ) : ℝ)))) ^ (2 * s) *
          (N : ℝ) ^ (2 * s - d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        refine (le_of_eq (rpow_div_nat_mul_self (x := CW ^ (2 * s - 2) * (d : ℝ))
          (by positivity) (by omega : 0 < 2 * s)).symm).trans ?_
        exact pow_le_pow_left₀ (by positivity) (le_max_right 1 _) (2 * s)

end

end Work.A3
