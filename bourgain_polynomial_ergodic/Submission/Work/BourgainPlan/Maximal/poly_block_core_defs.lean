import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_defs
import Submission.Work.BourgainPlan.Maximal.poly_arc_witness_unique
import Submission.Work.BourgainPlan.Maximal.polyMajorArcModelPre_eq_single

/-!
# The sharp core and the profile error of the general-polynomial model

The `ℓ²` maximal inequality for the model `polyMajorArcModelPre P (1/4) N` is proved, block by
block, by replacing the oscillatory profile `polyProfile P N` by its *sharp* indicator and
controlling the error.  This file records the vocabulary of that replacement:

* `polyModelTermArc` — a single arc term of the block, restricted to its arc
  `|c θ − a/q − l| ≤ N^{−(d−1/4)}`;
* `polySharpTerm` / `polyBlockCore` / `polyBlockCorePer` — the sharp core: the profile replaced by
  the indicator `|N^d β| ≤ 1` (`β = θ − (a/q+l)/c` the offset), in the two equivalent forms (sum
  over the `l`-window, and weighted periodised-neighbourhood sum);
* `polyBlockT` — the (frequency, weight) family of a dyadic block;
* `polyBlockErr` / `polyErrVal` / `polyErrNorm` / `polyErrMult` — the profile-replacement error;
* `polyActIdx` — the set of indices whose arc contains `θ`.

The analytic statements about these objects (weight cap, frequency separation, sharp-core
identification, profile replacement) are proved in companion files.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Commons.Analysis.ExponentialSums

/-! ## The dyadic dilation, the arc radius and the weight-decay exponent -/

/-- The dyadic dilation `(2^k)^d` of the model at scale `N = 2^k`. -/
noncomputable abbrev polyDil (P : Polynomial ℤ) (k : ℕ) : ℝ := powDil P.natDegree k

/-- The natural major-arc radius `N^{-(d-1/4)}`. -/
noncomputable abbrev polyArcRad (P : Polynomial ℤ) (k : ℕ) : ℝ := powArcRad P.natDegree k

/-- The weight-decay exponent `σ = 2^{-(d+1)}`. -/
noncomputable abbrev polySig (P : Polynomial ℤ) : ℝ := powSig P.natDegree

lemma polyDil_pos (P : Polynomial ℤ) (k : ℕ) : 0 < polyDil P k := powDil_pos _ _

lemma polyArcRad_pos (P : Polynomial ℤ) (k : ℕ) : 0 < polyArcRad P k := powArcRad_pos _ _

/-- `e(2πi n) = 1` for integers `n`. -/
lemma exp_two_pi_I_int (n : ℤ) :
    Complex.exp (((n : ℂ) * (2 * Real.pi * Complex.I))) = 1 := by
  have h1 : ((n : ℂ) * (2 * Real.pi * Complex.I))
      = ((((n : ℝ) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h1, Complex.exp_mul_I]
  have hsin : Complex.sin ((n : ℂ) * (2 * Real.pi)) = 0 := by
    rw [Complex.sin_periodic.int_mul_eq n, Complex.sin_zero]
  push_cast
  rw [Complex.cos_int_mul_two_pi, hsin]
  simp

/-- **The complete-sum weight is invariant under translation of the numerator by the modulus.** -/
lemma polyWeight_add_modulus (P : Polynomial ℤ) (Q : ℕ) (b : ℤ) :
    polyWeight P Q (b + Q) = polyWeight P Q b := by
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · subst hQ; simp [polyWeight]
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ)
  unfold polyWeight
  congr 1
  refine Finset.sum_congr rfl (fun r _ => ?_)
  have hsplit : ((((b + (Q : ℤ) : ℤ) : ℝ)) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ)
      = (((b : ℝ)) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) + ((P.eval (r : ℤ) : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [hsplit]
  rw [show (2 * Real.pi * Complex.I * ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ)
        + ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ))
      = 2 * Real.pi * Complex.I
          * ((((b : ℝ) / (Q : ℝ)) * ((P.eval (r : ℤ) : ℤ) : ℝ) : ℝ) : ℂ)
        + (((P.eval (r : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) by push_cast; ring]
  rw [Complex.exp_add, exp_two_pi_I_int, mul_one]

/-- Translation of the numerator by any multiple of the modulus. -/
lemma polyWeight_add_modulus_mul (P : Polynomial ℤ) (Q : ℕ) (b : ℤ) (m : ℤ) :
    polyWeight P Q (b + m * (Q : ℤ)) = polyWeight P Q b := by
  have hsub : ∀ x : ℤ, polyWeight P Q (x - (Q : ℤ)) = polyWeight P Q x := by
    intro x
    have h := polyWeight_add_modulus P Q (x - (Q : ℤ))
    rw [sub_add_cancel] at h
    exact h.symm
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [show b + ((k : ℤ) + 1) * (Q : ℤ) = (b + (k : ℤ) * (Q : ℤ)) + (Q : ℤ) by ring,
        polyWeight_add_modulus, ih]
  | pred k ih =>
      rw [show b + (-(k : ℤ) - 1) * (Q : ℤ) = (b + (-(k : ℤ)) * (Q : ℤ)) - (Q : ℤ) by ring,
        hsub, ih]

/-! ## The arc-restricted model term and the sharp term -/

open Classical in
/-- A single arc term of the `m`-th block, restricted to its arc. -/
noncomputable def polyModelTermArc (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (k : ℕ) (θ : ℝ) : ℂ :=
  if |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
    then polyModelTermPre P (2^k) q a l θ else 0

open Classical in
/-- The sharp term of a single arc: the profile replaced by the sharp indicator `1_{|N^d β| ≤ 1}`,
`β = θ − (a/q + l)/c` being the offset. -/
noncomputable def polySharpTerm (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (k : ℕ) (θ : ℝ) : ℂ :=
  polyWeight P (q * P.leadingCoeff.toNat) (a + l * q) *
    (if |polyDil P k * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
      then (1:ℂ) else 0)

lemma polyModelTermArc_eq_zero_of_not_act (P : Polynomial ℤ) {k : ℕ} (q a : ℕ) (l : ℤ) (θ : ℝ)
    (h : ¬ |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k) :
    polyModelTermArc P q a l k θ = 0 := by
  unfold polyModelTermArc; rw [if_neg h]

/-- If the sharp window at scale `k` is contained in the major arcs then the sharp term of an arc
vanishes off that arc. -/
lemma polySharpTerm_eq_zero_of_not_act (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {k : ℕ}
    (hcont : (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k)
    (q a : ℕ) (l : ℤ) (θ : ℝ)
    (h : ¬ |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k) :
    polySharpTerm P q a l k θ = 0 := by
  have hc0 : (0 : ℝ) < (P.leadingCoeff : ℝ) := by exact_mod_cast hc
  have hpos : 0 < polyDil P k := polyDil_pos P k
  have key : ¬ |polyDil P k * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1 := by
    intro hc'
    apply h
    have h1 : |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| ≤ (polyDil P k)⁻¹ := by
      rw [abs_mul, abs_of_pos hpos] at hc'
      rw [inv_eq_one_div, le_div_iff₀ hpos]
      linarith
    have halg : ((P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ))
        = (P.leadingCoeff : ℝ) * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) := by
      field_simp
      ring
    rw [halg, abs_mul, abs_of_pos hc0]
    calc (P.leadingCoeff : ℝ) * |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))|
        ≤ (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hc0)
      _ ≤ polyArcRad P k := hcont
  unfold polySharpTerm
  rw [if_neg key, mul_zero]

/-! ## The sharp core and the block error -/

/-- The sharp core of the `m`-th dyadic block: the profile of every arc term of the block replaced
by the sharp indicator, in the `l`-window form. -/
noncomputable def polyBlockCore (P : Polynomial ℤ) (m k : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
    starRingEnd ℂ (polySharpTerm P i.1 i.2 l k θ)

/-- The `l`-window of a block, whose weights are the complete sums of modulus `q·c`. -/
noncomputable def polyBlockCorePer (P : Polynomial ℤ) (m k : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ blockPair m, ∑ s ∈ Finset.range (P.leadingCoeff.toNat),
    starRingEnd ℂ (polyWeight P (i.1 * P.leadingCoeff.toNat)
        ((i.2 : ℤ) + (s : ℤ) * (i.1 : ℤ))) *
      perNbhd (((i.2 : ℝ) + (s : ℝ) * (i.1 : ℝ)) / ((i.1 : ℝ) * (P.leadingCoeff : ℝ)))
        ((polyDil P k)⁻¹) θ

/-- The (frequency, weight) family of the `m`-th dyadic block: frequencies `(a + s q)/(q c)` and
weights the conjugated complete sums of modulus `q·c`. -/
noncomputable def polyBlockT (P : Polynomial ℤ) (m : ℕ) : Finset (ℝ × ℂ) :=
  (blockPair m ×ˢ Finset.range (P.leadingCoeff.toNat)).image
    (fun p : (ℕ × ℕ) × ℕ =>
      (((p.1.2 : ℝ) + (p.2 : ℝ) * (p.1.1 : ℝ)) / ((p.1.1 : ℝ) * (P.leadingCoeff : ℝ)),
        starRingEnd ℂ (polyWeight P (p.1.1 * P.leadingCoeff.toNat)
          ((p.1.2 : ℤ) + (p.2 : ℤ) * (p.1.1 : ℤ)))))

/-- The profile-replacement error of the `m`-th block at scale `k`: model minus sharp core, the
core being switched off below the threshold scale `4m+4`. -/
noncomputable def polyBlockErr (P : Polynomial ℤ) (m k : ℕ) (θ : ℝ) : ℂ :=
  starRingEnd ℂ (polyModelQBlock P m (2^k) θ) -
    (if 4*m+4 ≤ k then polyBlockCore P m k θ else 0)

/-- All index triples `(q,a,l)` of the `m`-th block. -/
noncomputable def polyAllIdx (P : Polynomial ℤ) (m : ℕ) : Finset ((ℕ × ℕ) × ℤ) :=
  blockPair m ×ˢ Finset.Icc (-1 : ℤ) P.leadingCoeff

/-- The active index triples of the `m`-th block at scale `k`: those whose arc contains `θ`. -/
noncomputable def polyActIdx (P : Polynomial ℤ) (m k : ℕ) (θ : ℝ) : Finset ((ℕ × ℕ) × ℤ) :=
  (polyAllIdx P m).filter
    (fun p => |(P.leadingCoeff : ℝ) * θ - (p.1.2 : ℝ)/(p.1.1 : ℝ) - (p.2 : ℝ)| ≤ polyArcRad P k)

/-- The real-valued profile replacement error of the offset `β` at dyadic scale `K`. -/
noncomputable def polyErrVal (P : Polynomial ℤ) (β : ℝ) (K : ℕ) : ℝ :=
  ‖polyProfile P (2^K) β - (if |polyDil P K * β| ≤ 1 then (1:ℂ) else 0)‖

/-- The `ℝ≥0∞`-valued profile replacement error of an arc term at scale `K`. -/
noncomputable def polyErrNorm (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (K : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (polyErrVal P (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) K)

/-- The profile-replacement error of the `m`-th block as a multiplier on `(0,1)`. -/
noncomputable def polyErrMult (P : Polynomial ℤ) (m K : ℕ) (θ : ℝ) : ℂ :=
  if 0 < θ ∧ θ < 1 then polyBlockErr P m K θ else 0

/-! ## Elementary memberships -/

lemma mem_polyAllIdx {P : Polynomial ℤ} {m : ℕ} {p : (ℕ × ℕ) × ℤ} :
    p ∈ polyAllIdx P m ↔ p.1 ∈ blockPair m ∧ p.2 ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff := by
  rw [polyAllIdx, Finset.mem_product]

lemma mem_polyActIdx {P : Polynomial ℤ} {m k : ℕ} {θ : ℝ} {p : (ℕ × ℕ) × ℤ} :
    p ∈ polyActIdx P m k θ ↔ p ∈ polyAllIdx P m ∧
      |(P.leadingCoeff : ℝ) * θ - (p.1.2 : ℝ)/(p.1.1 : ℝ) - (p.2 : ℝ)| ≤ polyArcRad P k := by
  rw [polyActIdx, Finset.mem_filter]

/-- The active index set shrinks as the scale grows. -/
lemma polyActIdx_subset {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) {m : ℕ} {θ : ℝ} {k k' : ℕ}
    (h : k ≤ k') :
    polyActIdx P m k' θ ⊆ polyActIdx P m k θ := by
  intro p hp
  rw [mem_polyActIdx] at hp ⊢
  exact ⟨hp.1, le_trans hp.2 (powArcRad_antitone P.natDegree (by omega) h)⟩

lemma polyActIdx_eq_filter (P : Polynomial ℤ) (m k : ℕ) (θ : ℝ) :
    polyActIdx P m k θ = (polyAllIdx P m).filter
      (fun p => |(P.leadingCoeff : ℝ) * θ - (p.1.2 : ℝ)/(p.1.1 : ℝ) - (p.2 : ℝ)|
        ≤ polyArcRad P k) := rfl

lemma polyProfile_zero_poly (P : Polynomial ℤ) (N : ℕ) : polyProfile P N 0 = 1 :=
  polyProfile_zero P N

/-! ## Measurability of the sharp core and of the block error -/

lemma measurable_polyModelTermArc (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (k : ℕ) :
    Measurable (fun θ : ℝ => polyModelTermArc P q a l k θ) := by
  unfold polyModelTermArc
  exact Measurable.ite (by measurability) (measurable_polyModelTermPre P (2^k) q a l)
    measurable_const

lemma measurable_polySharpTerm (P : Polynomial ℤ) (q a : ℕ) (l : ℤ) (k : ℕ) :
    Measurable (fun θ : ℝ => polySharpTerm P q a l k θ) := by
  unfold polySharpTerm
  refine Measurable.mul measurable_const ?_
  exact Measurable.ite (by measurability) measurable_const measurable_const

lemma measurable_polyBlockCore (P : Polynomial ℤ) (m k : ℕ) :
    Measurable (fun θ : ℝ => polyBlockCore P m k θ) := by
  unfold polyBlockCore
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Finset.measurable_sum _ (fun l _ => ?_)
  exact Complex.continuous_conj.measurable.comp (measurable_polySharpTerm P i.1 i.2 l k)

lemma measurable_polyBlockErr (P : Polynomial ℤ) (m k : ℕ) :
    Measurable (fun θ : ℝ => polyBlockErr P m k θ) := by
  unfold polyBlockErr
  refine Measurable.sub ?_ ?_
  · exact Complex.continuous_conj.measurable.comp (measurable_polyModelQBlock P m (2^k))
  · by_cases h4 : 4*m+4 ≤ k
    · simpa [h4] using measurable_polyBlockCore P m k
    · simpa [h4] using measurable_const (a := (0:ℂ))

lemma measurable_polyErrMult (P : Polynomial ℤ) (m K : ℕ) :
    Measurable (polyErrMult P m K) := by
  unfold polyErrMult
  refine Measurable.ite (by measurability) ?_ measurable_const
  exact measurable_polyBlockErr P m K

/-! ## The structural identity of the block error -/

/-- A gcd-`if` may be pulled out of a sum over any finite set. -/
lemma sum_ite_gcd_eq' (a q : ℕ) (s : Finset ℤ) (Y : ℤ → ℂ) :
    (∑ l ∈ s, (if Nat.gcd a q = 1 then Y l else 0))
      = (if Nat.gcd a q = 1 then ∑ l ∈ s, Y l else 0) := by
  by_cases hg : Nat.gcd a q = 1
  · simp only [hg, if_true]
  · rw [if_neg hg]
    exact Finset.sum_eq_zero (fun l _ => by simp only [hg, if_false])

/-- The `q`-th block of the model at scale `2^k` as a sum of arc-restricted terms. -/
lemma poly_majorArcBlock_two_pow_eq_sum (P : Polynomial ℤ) (q k : ℕ) (θ : ℝ) :
    polyMajorArcBlockPre P ((1:ℝ)/4) (2^k) θ q
      = ∑ a ∈ Finset.range q, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          (if Nat.gcd a q = 1 then polyModelTermArc P q a l k θ else 0) := by
  have hmb : polyMajorArcBlockPre P ((1:ℝ)/4) (2^k) θ q
      = ∑ a ∈ Finset.range q, (if Nat.gcd a q = 1 then
          (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
            (if |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
              then polyModelTermPre P (2^k) q a l θ else 0)) else 0) := by
    unfold polyMajorArcBlockPre
    rfl
  rw [hmb]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hg : Nat.gcd a q = 1
  · simp only [hg, if_true]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold polyModelTermArc
    rfl
  · simp only [hg, if_false, Finset.sum_const_zero]

/-- The model block at scale `2^k` as a sum over the index pairs of the block. -/
lemma poly_modelQBlock_two_pow_eq_blockPair (P : Polynomial ℤ) {m k : ℕ} (hk : 4*m+4 ≤ k)
    (θ : ℝ) :
    starRingEnd ℂ (polyModelQBlock P m (2^k) θ)
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          starRingEnd ℂ (polyModelTermArc P i.1 i.2 l k θ) := by
  have h1 : starRingEnd ℂ (polyModelQBlock P m (2^k) θ)
      = ∑ q ∈ Finset.Ico (2^m) (2^(m+1)),
          ∑ a ∈ (Finset.range q).filter (fun a => Nat.gcd a q = 1),
            ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
              starRingEnd ℂ (polyModelTermArc P q a l k θ) := by
    unfold polyModelQBlock
    rw [blockQ_eq m k hk, map_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [poly_majorArcBlock_two_pow_eq_sum, map_sum]
    have hstep : ∀ a : ℕ,
        starRingEnd ℂ (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
            (if Nat.gcd a q = 1 then polyModelTermArc P q a l k θ else 0))
          = (if Nat.gcd a q = 1 then ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
              starRingEnd ℂ (polyModelTermArc P q a l k θ) else 0) := by
      intro a
      rw [map_sum]
      rw [Finset.sum_congr rfl (fun l _ => conj_ite_zero _ (polyModelTermArc P q a l k θ))]
      exact sum_ite_gcd_eq' a q _ (fun l => starRingEnd ℂ (polyModelTermArc P q a l k θ))
    rw [Finset.sum_congr rfl (fun a _ => hstep a), ← Finset.sum_filter]
  rw [h1, sum_blockPair m]

/-- The sharp core is the sum over the index pairs of the sharp terms. -/
lemma polyBlockCore_eq_sum_sharpTerm (P : Polynomial ℤ) (m k : ℕ) (θ : ℝ) :
    polyBlockCore P m k θ
      = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          starRingEnd ℂ (polySharpTerm P i.1 i.2 l k θ) := rfl

/-- **The error of the `m`-th block is the sum of the arc errors.** -/
lemma polyBlockErr_eq_sum (P : Polynomial ℤ) {m k : ℕ} (hk : 4*m+4 ≤ k) (θ : ℝ) :
    polyBlockErr P m k θ = ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
      starRingEnd ℂ (polyModelTermArc P i.1 i.2 l k θ - polySharpTerm P i.1 i.2 l k θ) := by
  unfold polyBlockErr
  rw [if_pos hk, poly_modelQBlock_two_pow_eq_blockPair P hk θ,
    polyBlockCore_eq_sum_sharpTerm]
  simp_rw [← Finset.sum_sub_distrib, ← map_sub]

/-- **Per-term profile error bound.** -/
lemma norm_polyModelTermArc_sub_sharp_le (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) {k : ℕ}
    (hcont : (P.leadingCoeff : ℝ) * (polyDil P k)⁻¹ ≤ polyArcRad P k) (q a : ℕ) (l : ℤ)
    (θ : ℝ) :
    ‖polyModelTermArc P q a l k θ - polySharpTerm P q a l k θ‖
      ≤ ‖polyWeight P (q * P.leadingCoeff.toNat) (a + l * q)‖ *
          polyErrVal P (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) k := by
  by_cases harc : |(P.leadingCoeff : ℝ) * θ - (a:ℝ)/(q:ℝ) - (l:ℝ)| ≤ polyArcRad P k
  · have h1 : polyModelTermArc P q a l k θ = polyModelTermPre P (2^k) q a l θ := by
      unfold polyModelTermArc; rw [if_pos harc]
    have h2 : polyModelTermPre P (2^k) q a l θ
        = polyWeight P (q * P.leadingCoeff.toNat) (a + l * q) *
            polyProfile P (2^k) (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) := rfl
    have h3 : polySharpTerm P q a l k θ
        = polyWeight P (q * P.leadingCoeff.toNat) (a + l * q) *
            (if |polyDil P k * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
              then (1:ℂ) else 0) := rfl
    rw [h1, h2, h3, ← mul_sub, norm_mul]
    exact mul_le_mul_of_nonneg_left le_rfl (norm_nonneg _)
  · rw [polyModelTermArc_eq_zero_of_not_act P q a l θ harc,
      polySharpTerm_eq_zero_of_not_act P hc hcont q a l θ harc, sub_zero, norm_zero]
    unfold polyErrVal
    positivity

/-- Bound for the sharp core in terms of the number of its terms. -/
lemma norm_polyBlockCore_le (P : Polynomial ℤ) (m k : ℕ) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff, ∀ i ∈ blockPair m,
      ‖polyWeight P (i.1 * P.leadingCoeff.toNat) (i.2 + l * i.1)‖ ≤ A) (θ : ℝ) :
    ‖polyBlockCore P m k θ‖
      ≤ ((blockPair m).card : ℝ) * ((Finset.Icc (-1 : ℤ) P.leadingCoeff).card : ℝ) * A := by
  rw [polyBlockCore_eq_sum_sharpTerm]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ i ∈ blockPair m, ‖∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          starRingEnd ℂ (polySharpTerm P i.1 i.2 l k θ)‖
      ≤ ∑ i ∈ blockPair m, ∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
          ‖polyWeight P (i.1 * P.leadingCoeff.toNat) (i.2 + l * i.1)‖ := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun l hl => ?_))
        rw [Complex.norm_conj]
        unfold polySharpTerm
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (by split_ifs <;> simp)
    _ ≤ ∑ i ∈ blockPair m, ∑ _l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff, A :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun l hl => hA l hl i hi))
    _ = ((blockPair m).card : ℝ) * ((Finset.Icc (-1 : ℤ) P.leadingCoeff).card : ℝ) * A := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
        ring

end Work.BourgainPlan.Maximal
