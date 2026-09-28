import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.Lat.card_Mon
import Submission.Work.HP.MDEstimates.ReducFactor
import Submission.Work.Q44Geom.ReducDefs
import Submission.Work.Q44Geom.ReducAux
import Submission.Work.Q44Geom.formOf_mulVec
import Submission.Work.Q44Geom.mulVec_norm_lower
import Submission.Work.Q44Geom.exists_prim_multiple
import Submission.Work.Q44Geom.ncard_ball_le
import Submission.Work.Q44Geom.ncard_pair_ball_le
import Submission.Work.Q44Geom.integral_cofactor_deg1
import Submission.Work.Q44Geom.integral_cofactor_deg2

/-!
# Counting reducible quartic forms in `5` variables

`Work.HP.MDEstimates.reducible_forms`: the number of nonzero coefficient vectors
`c : Mon 4 4 → ℤ` of Euclidean norm at most `M` whose form `formOf 4 4 c` is reducible over `ℚ`
is `O(M ^ 40)`.

A reducible quartic over `ℚ` has a homogeneous factor of degree `1` or `2`
(`Work.HP.MDEstimates.exists_homogeneous_factor`); clearing denominators (Gauss's lemma,
`integral_cofactor_deg1`, `integral_cofactor_deg2`) produces a *primitive integral* factor `l`
(of degree `1` or `2`) and an integral cofactor, and the multiplicative lower bound
`Work.Q44Geom.mulVec_norm_lower` shows that both factors have norm `≪ M`.  Counting the possible
pairs of integral coefficient vectors of norm `≤ M / c₀` in the two degree patterns gives
`M ^ (5 + 35) + M ^ (15 + 15) = O(M ^ 40)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.MDEstimates

open Work.HP
open Work.HP.Vero
open Work.Q44Geom
open Work.HP.MDEstimates.ReducFactor

/-- The nonzero coefficient vectors of reducible quartic forms of norm at most `M`. -/
def RedSet (M : ℝ) : Set (Mon 4 4 → ℤ) :=
  {c | c ≠ 0 ∧ eNorm c ≤ M ∧ ¬ Irreducible (formOf 4 4 c)}

/-- Pairs of integral coefficient vectors of degrees `d`, `d'` in the product of the two balls. -/
def pairBall (d d' : ℕ) (R : ℝ) : Set ((Mon d 4 → ℤ) × (Mon d' 4 → ℤ)) :=
  {p | eNorm p.1 ≤ R ∧ eNorm p.2 ≤ R}

lemma rNorm_nonneg'' {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ rNorm v := Real.sqrt_nonneg _

/-! ## Extraction of a bounded primitive integral factor -/

/-- Every reducible `c` of norm `≤ M` has, in one of the two shapes `ℓ · h` (degrees 1 and 3) or
`q · q'` (two quadrics), a factorisation into integral coefficient vectors such that the first
factor is primitive and both factors have norm at most `M / c₀`. -/
theorem reduc_witness (c₀ : ℝ) (hc₀ : 0 < c₀)
    (h₁₃ : ∀ (A : Mon 1 4 → ℝ) (B : Mon 3 4 → ℝ),
      c₀ * rNorm A * rNorm B ≤ rNorm (mulVec 1 3 4 A B))
    (h₂₂ : ∀ (A : Mon 2 4 → ℝ) (B : Mon 2 4 → ℝ),
      c₀ * rNorm A * rNorm B ≤ rNorm (mulVec 2 2 4 A B))
    {M : ℝ} (hM : 1 ≤ M) {c : Mon 4 4 → ℤ} (hc0 : c ≠ 0) (hnorm : eNorm c ≤ M)
    (hred : ¬ Irreducible (formOf 4 4 c)) :
    (∃ l : Mon 1 4 → ℤ, ∃ h : Mon 3 4 → ℤ,
        IsPrim l ∧ eNorm l ≤ M / c₀ ∧ eNorm h ≤ M / c₀ ∧ c = mulVec 1 3 4 l h)
    ∨ (∃ q q' : Mon 2 4 → ℤ,
        IsPrim q ∧ eNorm q ≤ M / c₀ ∧ eNorm q' ≤ M / c₀ ∧ c = mulVec 2 2 4 q q') := by
  rcases exists_homogeneous_factor c hc0 hred with
    ⟨A, B, hA1, hB3, hA0, hB0, hAB⟩ | ⟨A, B, hA2, hB2, hA0, hB0, hAB⟩
  · -- a factor of degree 1
    obtain ⟨t, l, ht0, hlprim, hl⟩ :=
      exists_prim_multiple (fun m : Mon 1 4 => A.coeff m.toFinsupp) (by
        intro h0
        apply hA0
        rw [← polyOfR_ofHomog hA1, h0]
        simp)
    have hAeq : A = MvPolynomial.C t⁻¹ * polyOfR (fun m => (l m : ℚ)) := by
      have h1 : polyOfR (fun m : Mon 1 4 => (l m : ℚ)) = MvPolynomial.C t * A := by
        have h2 : (fun m : Mon 1 4 => (l m : ℚ)) = fun m => t * A.coeff m.toFinsupp :=
          funext fun m => hl m
        rw [h2, polyOfR_C_mul, polyOfR_ofHomog hA1]
      rw [h1, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ (ne_of_gt ht0),
        MvPolynomial.C_1, one_mul]
    have hHne : MvPolynomial.C t⁻¹ * B ≠ 0 :=
      mul_ne_zero (MvPolynomial.C_ne_zero.mpr (inv_ne_zero (ne_of_gt ht0))) hB0
    obtain ⟨h, hh⟩ := integral_cofactor_deg1 c (MvPolynomial.C t⁻¹ * B) l hlprim
      (MvPolynomial.IsHomogeneous.C_mul hB3 _) (by rw [hAB, hAeq]; ring)
    have hh0 : h ≠ 0 := fun h0 => hHne (by rw [hh, h0]; simp [polyOfR])
    have key : formOf 4 4 c = formOf 4 4 (mulVec 1 3 4 l h) := by
      have h1 : (MvPolynomial.C t⁻¹ * polyOfR (fun m : Mon 1 4 => (l m : ℚ))) * B
          = polyOfR (fun m : Mon 1 4 => (l m : ℚ)) *
            polyOfR (fun m : Mon 3 4 => (h m : ℚ)) := by
        rw [show (MvPolynomial.C t⁻¹ * polyOfR (fun m : Mon 1 4 => (l m : ℚ))) * B
            = polyOfR (fun m : Mon 1 4 => (l m : ℚ)) * (MvPolynomial.C t⁻¹ * B) from by ring,
          hh]
      rw [hAB, hAeq, h1, ← formOf_eq_polyOfR (d := 1) l, ← formOf_eq_polyOfR (d := 3) h,
        ← formOf_mulVec]
    have hceq : c = mulVec 1 3 4 l h := formOf_injective key
    have hb : c₀ * eNorm l * eNorm h ≤ M := by
      have h3 := h₁₃ (fun m => (l m : ℝ)) (fun m => (h m : ℝ))
      rw [← eNorm_eq_rNorm l, ← eNorm_eq_rNorm h] at h3
      rw [← eNorm_mulVec_intCast (A := l) (B := h), ← hceq] at h3
      exact le_trans h3 hnorm
    have hlge : 1 ≤ eNorm l := one_le_eNorm_of_ne_zero (isPrim_ne_zero' hlprim)
    have hhge : 1 ≤ eNorm h := one_le_eNorm_of_ne_zero hh0
    have hl_le : eNorm l ≤ M / c₀ := by
      have h5 : c₀ * eNorm l ≤ c₀ * eNorm l * eNorm h := by
        calc c₀ * eNorm l = c₀ * eNorm l * 1 := by ring
          _ ≤ c₀ * eNorm l * eNorm h :=
              mul_le_mul_of_nonneg_left hhge (mul_nonneg hc₀.le (eNorm_nonneg' l))
      rw [le_div_iff₀ hc₀, mul_comm (eNorm l) c₀]
      linarith
    have hh_le : eNorm h ≤ M / c₀ := by
      have h5 : c₀ * eNorm h ≤ c₀ * eNorm l * eNorm h := by
        calc c₀ * eNorm h = c₀ * eNorm h * 1 := by ring
          _ ≤ c₀ * eNorm h * eNorm l :=
              mul_le_mul_of_nonneg_left hlge (mul_nonneg hc₀.le (eNorm_nonneg' h))
          _ = c₀ * eNorm l * eNorm h := by ring
      rw [le_div_iff₀ hc₀, mul_comm (eNorm h) c₀]
      linarith
    exact Or.inl ⟨l, h, hlprim, hl_le, hh_le, hceq⟩
  · -- two quadrics
    obtain ⟨t, q, ht0, hqprim, hq⟩ :=
      exists_prim_multiple (fun m : Mon 2 4 => A.coeff m.toFinsupp) (by
        intro h0
        apply hA0
        rw [← polyOfR_ofHomog hA2, h0]
        simp)
    have hAeq : A = MvPolynomial.C t⁻¹ * polyOfR (fun m => (q m : ℚ)) := by
      have h1 : polyOfR (fun m : Mon 2 4 => (q m : ℚ)) = MvPolynomial.C t * A := by
        have h2 : (fun m : Mon 2 4 => (q m : ℚ)) = fun m => t * A.coeff m.toFinsupp :=
          funext fun m => hq m
        rw [h2, polyOfR_C_mul, polyOfR_ofHomog hA2]
      rw [h1, ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ (ne_of_gt ht0),
        MvPolynomial.C_1, one_mul]
    have hHne : MvPolynomial.C t⁻¹ * B ≠ 0 :=
      mul_ne_zero (MvPolynomial.C_ne_zero.mpr (inv_ne_zero (ne_of_gt ht0))) hB0
    obtain ⟨q', hq'⟩ := integral_cofactor_deg2 c (MvPolynomial.C t⁻¹ * B) q hqprim
      (MvPolynomial.IsHomogeneous.C_mul hB2 _) (by rw [hAB, hAeq]; ring)
    have hq'0 : q' ≠ 0 := fun h0 => hHne (by rw [hq', h0]; simp [polyOfR])
    have key : formOf 4 4 c = formOf 4 4 (mulVec 2 2 4 q q') := by
      have h1 : (MvPolynomial.C t⁻¹ * polyOfR (fun m : Mon 2 4 => (q m : ℚ))) * B
          = polyOfR (fun m : Mon 2 4 => (q m : ℚ)) *
            polyOfR (fun m : Mon 2 4 => (q' m : ℚ)) := by
        rw [show (MvPolynomial.C t⁻¹ * polyOfR (fun m : Mon 2 4 => (q m : ℚ))) * B
            = polyOfR (fun m : Mon 2 4 => (q m : ℚ)) * (MvPolynomial.C t⁻¹ * B) from by ring,
          hq']
      rw [hAB, hAeq, h1, ← formOf_eq_polyOfR (d := 2) q, ← formOf_eq_polyOfR (d := 2) q',
        ← formOf_mulVec]
    have hceq : c = mulVec 2 2 4 q q' := formOf_injective key
    have hb : c₀ * eNorm q * eNorm q' ≤ M := by
      have h3 := h₂₂ (fun m => (q m : ℝ)) (fun m => (q' m : ℝ))
      rw [← eNorm_eq_rNorm q, ← eNorm_eq_rNorm q'] at h3
      rw [← eNorm_mulVec_intCast (A := q) (B := q'), ← hceq] at h3
      exact le_trans h3 hnorm
    have hqge : 1 ≤ eNorm q := one_le_eNorm_of_ne_zero (isPrim_ne_zero' hqprim)
    have hq'ge : 1 ≤ eNorm q' := one_le_eNorm_of_ne_zero hq'0
    have hq_le : eNorm q ≤ M / c₀ := by
      have h5 : c₀ * eNorm q ≤ c₀ * eNorm q * eNorm q' := by
        calc c₀ * eNorm q = c₀ * eNorm q * 1 := by ring
          _ ≤ c₀ * eNorm q * eNorm q' :=
              mul_le_mul_of_nonneg_left hq'ge (mul_nonneg hc₀.le (eNorm_nonneg' q))
      rw [le_div_iff₀ hc₀, mul_comm (eNorm q) c₀]
      linarith
    have hq'_le : eNorm q' ≤ M / c₀ := by
      have h5 : c₀ * eNorm q' ≤ c₀ * eNorm q * eNorm q' := by
        calc c₀ * eNorm q' = c₀ * eNorm q' * 1 := by ring
          _ ≤ c₀ * eNorm q' * eNorm q :=
              mul_le_mul_of_nonneg_left hqge (mul_nonneg hc₀.le (eNorm_nonneg' q'))
          _ = c₀ * eNorm q * eNorm q' := by ring
      rw [le_div_iff₀ hc₀, mul_comm (eNorm q') c₀]
      linarith
    exact Or.inr ⟨q, q', hqprim, hq_le, hq'_le, hceq⟩

/-! ## The counting step -/

/-- The number of reducible vectors of norm `≤ M` is bounded by the number of pairs of integral
vectors of norm `≤ M / c₀` in the two possible degrees. -/
theorem ncard_RedSet_le (c₀ : ℝ) (hc₀ : 0 < c₀)
    (h₁₃ : ∀ (A : Mon 1 4 → ℝ) (B : Mon 3 4 → ℝ),
      c₀ * rNorm A * rNorm B ≤ rNorm (mulVec 1 3 4 A B))
    (h₂₂ : ∀ (A : Mon 2 4 → ℝ) (B : Mon 2 4 → ℝ),
      c₀ * rNorm A * rNorm B ≤ rNorm (mulVec 2 2 4 A B))
    (M : ℝ) (hM : 1 ≤ M) :
    (RedSet M).ncard ≤ (pairBall 1 3 (M / c₀)).ncard + (pairBall 2 2 (M / c₀)).ncard := by
  classical
  have hfinRed : (RedSet M).Finite :=
    (finite_ball M).subset fun c hc => hc.2.1
  set S1 : Set (Mon 4 4 → ℤ) := {c | c ∈ RedSet M ∧ ∃ l : Mon 1 4 → ℤ, ∃ h : Mon 3 4 → ℤ,
      IsPrim l ∧ eNorm l ≤ M / c₀ ∧ eNorm h ≤ M / c₀ ∧ c = mulVec 1 3 4 l h} with hS1
  set S2 : Set (Mon 4 4 → ℤ) := {c | c ∈ RedSet M ∧ ∃ q : Mon 2 4 → ℤ, ∃ q' : Mon 2 4 → ℤ,
      IsPrim q ∧ eNorm q ≤ M / c₀ ∧ eNorm q' ≤ M / c₀ ∧ c = mulVec 2 2 4 q q'} with hS2
  have hsub : RedSet M ⊆ S1 ∪ S2 := by
    intro c hc
    have hcmem : c ∈ RedSet M := hc
    obtain ⟨hc0, hnorm, hred⟩ := hc
    rcases reduc_witness c₀ hc₀ h₁₃ h₂₂ hM hc0 hnorm hred with h | h
    · exact Or.inl ⟨hcmem, h⟩
    · exact Or.inr ⟨hcmem, h⟩
  have hfinU : (S1 ∪ S2).Finite :=
    hfinRed.subset fun c hc => hc.elim (fun h => h.1) (fun h => h.1)
  let T1 : Set ((Mon 1 4 → ℤ) × (Mon 3 4 → ℤ)) :=
    {p | IsPrim p.1 ∧ eNorm p.1 ≤ M / c₀ ∧ eNorm p.2 ≤ M / c₀}
  let f1 : (Mon 4 4 → ℤ) → (Mon 1 4 → ℤ) × (Mon 3 4 → ℤ) := fun c =>
    if h : ∃ p : (Mon 1 4 → ℤ) × (Mon 3 4 → ℤ), p ∈ T1 ∧ c = mulVec 1 3 4 p.1 p.2
    then Classical.choose h else (0, 0)
  have hf1_inj : Set.InjOn f1 S1 := by
    intro c1 hc1 c2 hc2 heq
    have h1 : ∃ p : (Mon 1 4 → ℤ) × (Mon 3 4 → ℤ), p ∈ T1 ∧ c1 = mulVec 1 3 4 p.1 p.2 := by
      obtain ⟨l, h, hl, hl1, hl2, hc⟩ := hc1.2
      exact ⟨(l, h), ⟨hl, hl1, hl2⟩, hc⟩
    have h2 : ∃ p : (Mon 1 4 → ℤ) × (Mon 3 4 → ℤ), p ∈ T1 ∧ c2 = mulVec 1 3 4 p.1 p.2 := by
      obtain ⟨l, h, hl, hl1, hl2, hc⟩ := hc2.2
      exact ⟨(l, h), ⟨hl, hl1, hl2⟩, hc⟩
    have e1 : f1 c1 = Classical.choose h1 := by simp only [f1]; exact dif_pos h1
    have e2 : f1 c2 = Classical.choose h2 := by simp only [f1]; exact dif_pos h2
    rw [e1, e2] at heq
    rw [(Classical.choose_spec h1).2, (Classical.choose_spec h2).2, heq]
  have hmap1 : Set.MapsTo f1 S1 (pairBall 1 3 (M / c₀)) := by
    intro c hc
    have h1 : ∃ p : (Mon 1 4 → ℤ) × (Mon 3 4 → ℤ), p ∈ T1 ∧ c = mulVec 1 3 4 p.1 p.2 := by
      obtain ⟨l, h, hl, hl1, hl2, hc'⟩ := hc.2
      exact ⟨(l, h), ⟨hl, hl1, hl2⟩, hc'⟩
    have e1 : f1 c = Classical.choose h1 := by simp only [f1]; exact dif_pos h1
    rw [e1]
    exact ⟨(Classical.choose_spec h1).1.2.1, (Classical.choose_spec h1).1.2.2⟩
  have hcard1 : S1.ncard ≤ (pairBall 1 3 (M / c₀)).ncard := by
    rw [← hf1_inj.ncard_image]
    exact Set.ncard_le_ncard (Set.image_subset_iff.mpr hmap1)
      (finite_pair_ball (d := 1) (d' := 3) (M / c₀) (M / c₀))
  let T2 : Set ((Mon 2 4 → ℤ) × (Mon 2 4 → ℤ)) :=
    {p | IsPrim p.1 ∧ eNorm p.1 ≤ M / c₀ ∧ eNorm p.2 ≤ M / c₀}
  let f2 : (Mon 4 4 → ℤ) → (Mon 2 4 → ℤ) × (Mon 2 4 → ℤ) := fun c =>
    if h : ∃ p : (Mon 2 4 → ℤ) × (Mon 2 4 → ℤ), p ∈ T2 ∧ c = mulVec 2 2 4 p.1 p.2
    then Classical.choose h else (0, 0)
  have hf2_inj : Set.InjOn f2 S2 := by
    intro c1 hc1 c2 hc2 heq
    have h1 : ∃ p : (Mon 2 4 → ℤ) × (Mon 2 4 → ℤ), p ∈ T2 ∧ c1 = mulVec 2 2 4 p.1 p.2 := by
      obtain ⟨q, q', hq, hq1, hq2, hc⟩ := hc1.2
      exact ⟨(q, q'), ⟨hq, hq1, hq2⟩, hc⟩
    have h2 : ∃ p : (Mon 2 4 → ℤ) × (Mon 2 4 → ℤ), p ∈ T2 ∧ c2 = mulVec 2 2 4 p.1 p.2 := by
      obtain ⟨q, q', hq, hq1, hq2, hc⟩ := hc2.2
      exact ⟨(q, q'), ⟨hq, hq1, hq2⟩, hc⟩
    have e1 : f2 c1 = Classical.choose h1 := by simp only [f2]; exact dif_pos h1
    have e2 : f2 c2 = Classical.choose h2 := by simp only [f2]; exact dif_pos h2
    rw [e1, e2] at heq
    rw [(Classical.choose_spec h1).2, (Classical.choose_spec h2).2, heq]
  have hmap2 : Set.MapsTo f2 S2 (pairBall 2 2 (M / c₀)) := by
    intro c hc
    have h1 : ∃ p : (Mon 2 4 → ℤ) × (Mon 2 4 → ℤ), p ∈ T2 ∧ c = mulVec 2 2 4 p.1 p.2 := by
      obtain ⟨q, q', hq, hq1, hq2, hc'⟩ := hc.2
      exact ⟨(q, q'), ⟨hq, hq1, hq2⟩, hc'⟩
    have e1 : f2 c = Classical.choose h1 := by simp only [f2]; exact dif_pos h1
    rw [e1]
    exact ⟨(Classical.choose_spec h1).1.2.1, (Classical.choose_spec h1).1.2.2⟩
  have hcard2 : S2.ncard ≤ (pairBall 2 2 (M / c₀)).ncard := by
    rw [← hf2_inj.ncard_image]
    exact Set.ncard_le_ncard (Set.image_subset_iff.mpr hmap2)
      (finite_pair_ball (d := 2) (d' := 2) (M / c₀) (M / c₀))
  calc (RedSet M).ncard ≤ (S1 ∪ S2).ncard := Set.ncard_le_ncard hsub hfinU
    _ ≤ S1.ncard + S2.ncard := Set.ncard_union_le S1 S2
    _ ≤ (pairBall 1 3 (M / c₀)).ncard + (pairBall 2 2 (M / c₀)).ncard :=
        Nat.add_le_add hcard1 hcard2

/-! ## The final bound -/

theorem reducible_forms :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 1 ≤ M →
      (({c : Mon 4 4 → ℤ | c ≠ 0 ∧ eNorm c ≤ M ∧ ¬ Irreducible (formOf 4 4 c)} :
        Set (Mon 4 4 → ℤ)).ncard : ℝ) ≤ C * M ^ 40 := by
  obtain ⟨c₁, hc₁, h₁₃⟩ := mulVec_norm_lower 1 3 (by norm_num)
  obtain ⟨c₂, hc₂, h₂₂⟩ := mulVec_norm_lower 2 2 (by norm_num)
  let c₀ : ℝ := min c₁ c₂
  have hc₀ : 0 < c₀ := lt_min hc₁ hc₂
  have h₁₃' : ∀ (A : Mon 1 4 → ℝ) (B : Mon 3 4 → ℝ),
      c₀ * rNorm A * rNorm B ≤ rNorm (mulVec 1 3 4 A B) := by
    intro A B
    have hle : c₀ ≤ c₁ := min_le_left _ _
    have h0 : 0 ≤ rNorm A * rNorm B := mul_nonneg (rNorm_nonneg'' A) (rNorm_nonneg'' B)
    calc c₀ * rNorm A * rNorm B = c₀ * (rNorm A * rNorm B) := by ring
      _ ≤ c₁ * (rNorm A * rNorm B) := mul_le_mul_of_nonneg_right hle h0
      _ = c₁ * rNorm A * rNorm B := by ring
      _ ≤ rNorm (mulVec 1 3 4 A B) := h₁₃ A B
  have h₂₂' : ∀ (A : Mon 2 4 → ℝ) (B : Mon 2 4 → ℝ),
      c₀ * rNorm A * rNorm B ≤ rNorm (mulVec 2 2 4 A B) := by
    intro A B
    have hle : c₀ ≤ c₂ := min_le_right _ _
    have h0 : 0 ≤ rNorm A * rNorm B := mul_nonneg (rNorm_nonneg'' A) (rNorm_nonneg'' B)
    calc c₀ * rNorm A * rNorm B = c₀ * (rNorm A * rNorm B) := by ring
      _ ≤ c₂ * (rNorm A * rNorm B) := mul_le_mul_of_nonneg_right hle h0
      _ = c₂ * rNorm A * rNorm B := by ring
      _ ≤ rNorm (mulVec 2 2 4 A B) := h₂₂ A B
  refine ⟨2 * (2 * (1 / c₀ + 1) + 1) ^ 40, by positivity, ?_⟩
  intro M hM
  have hcount := ncard_RedSet_le c₀ hc₀ h₁₃' h₂₂' M hM
  set B : ℝ := 2 * (⌈M / c₀⌉₊ : ℝ) + 1 with hB
  set K : ℝ := 2 * (1 / c₀ + 1) + 1 with hK
  have hB1 : 1 ≤ B := by
    rw [hB]
    have := Nat.cast_nonneg (α := ℝ) ⌈M / c₀⌉₊
    linarith
  have hc1 : ((pairBall 1 3 (M / c₀)).ncard : ℝ) ≤ B ^ 5 * B ^ 35 := by
    have h := ncard_pair_ball_le (d := 1) (d' := 3) (M / c₀) (M / c₀)
    refine le_trans h ?_
    rw [show Fintype.card (Mon 1 4) = 5 from by rw [Work.HP.Lat.card_Mon]; decide,
      show Fintype.card (Mon 3 4) = 35 from by rw [Work.HP.Lat.card_Mon]; decide, hB]
  have hc2 : ((pairBall 2 2 (M / c₀)).ncard : ℝ) ≤ B ^ 15 * B ^ 15 := by
    have h := ncard_pair_ball_le (d := 2) (d' := 2) (M / c₀) (M / c₀)
    refine le_trans h ?_
    rw [show Fintype.card (Mon 2 4) = 15 from by rw [Work.HP.Lat.card_Mon]; decide, hB]
  have hR : B ≤ M * K := by
    have h1 : (⌈M / c₀⌉₊ : ℝ) < M / c₀ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : M / c₀ + 1 ≤ M * (1 / c₀ + 1) := by
      rw [mul_add, mul_one_div, mul_one]
      linarith
    rw [hB, hK]
    nlinarith [h1, h2, hM]
  calc ((RedSet M).ncard : ℝ)
      ≤ ((pairBall 1 3 (M / c₀)).ncard : ℝ) + ((pairBall 2 2 (M / c₀)).ncard : ℝ) := by
        exact_mod_cast hcount
    _ ≤ B ^ 5 * B ^ 35 + B ^ 15 * B ^ 15 := add_le_add hc1 hc2
    _ ≤ 2 * B ^ 40 := by
        have h1 : B ^ 30 ≤ B ^ 40 := pow_le_pow_right₀ hB1 (by norm_num)
        have h2 : B ^ 5 * B ^ 35 = B ^ 40 := by rw [← pow_add]
        have h3 : B ^ 15 * B ^ 15 = B ^ 30 := by rw [← pow_add]
        rw [h2, h3]; linarith
    _ ≤ 2 * (M * K) ^ 40 := by
        have h0 : (0 : ℝ) ≤ M * K := mul_nonneg (by linarith) (by positivity)
        have h4 : B ^ 40 ≤ (M * K) ^ 40 := pow_le_pow_left₀ (by linarith) hR 40
        linarith
    _ = 2 * (2 * (1 / c₀ + 1) + 1) ^ 40 * M ^ 40 := by rw [hK, mul_pow]; ring

end Work.HP.MDEstimates
