import Mathlib
import Submission.Work.Peluse.LadderP.stepPAve

/-!
# The mass lower bound of the ladder step

The peeled `(j+1)`-state is bounded below by the average of the box-norm powers of the peeled
difference, and the mass of the "good" part of that average is at least a fixed fraction of `γ`,
provided the bad set (the set of `a` at which the gcd-or-size condition of the Lemma 5.1 input
fails) is small on average.  The whole chain is

* `u ^ (2^(2^(j+1)-1+n)) ≤ M₁^{-(2j+1)} ∑_{h₁,h₁',h'_s} ∑_{km} Gwt · boxAvgA` (hypothesis),
* `boxAvgA ≤ 1` on each term (`boxAvgA_le_one`),
* `∑_{km} Gwt ≤ 1` (`sum_Gwt_le_one`),
* the measure of the bad set is at most `γ` in the `M₁^{-(2j+1)}`-mass (`hbad`),
* the pointwise Lemma 5.1 input `lem`,

from which the "good and not bad" mass is `≥ 2γ` and the conclusion follows termwise.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

abbrev IdxT (j M₁ : ℕ) : Type := (Fin j → Fin M₁) × ((Fin j → Fin M₁) × Fin M₁)

lemma card_IdxT (j M₁ : ℕ) : Fintype.card (IdxT j M₁) = M₁ ^ (2 * j + 1) := by
  change Fintype.card ((Fin j → Fin M₁) × ((Fin j → Fin M₁) × Fin M₁)) = M₁ ^ (2 * j + 1)
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [← mul_assoc, ← pow_add, ← pow_succ]
  congr 1
  omega

/-- The shift weight on the flat index. -/
def Wfun (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (t : IdxT j M₁)
    (km : KmT j n M₁ c L D t.1 t.2.1) : ℝ :=
  Gwt j n M₁ c L D t.1 t.2.1

/-- The averaged box norm of the peeled difference, on the flat index. -/
def FFfun (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) (t : IdxT j M₁)
    (km : KmT j n M₁ c L D t.1 t.2.1) : ℝ :=
  LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) t.1 t.2.1 t.2.2) N
    (Gof j n M₁ c L D t.1 t.2.1 km f)

/-- The box-norm power of the peeled difference, on the flat index. -/
def GGfun (j n s' M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) (t : IdxT j M₁)
    (km : KmT j n M₁ c L D t.1 t.2.1) : ℝ :=
  Gpow j n s' M₁ c L D N t.1 t.2.1 km f

/-- The bad-set predicate on the flat index. -/
def BadFun (j M₁ : ℕ) (η ε : ℝ) (hs : Fin M₁) (t : IdxT j M₁) : Prop :=
  ε * (M₁ : ℝ) < ((stepBad j M₁ η (enumAll j) (Fin.snoc t.1 hs)
    (Fin.snoc t.2.1 t.2.2)).card : ℝ)

/-- The flat form of the averaged box norm of the peeled difference. -/
def massSum (j n M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ∑ t : IdxT j M₁, ∑ km : KmT j n M₁ c L D t.1 t.2.1,
    Wfun j n M₁ c L D t km * FFfun j n M₁ c L D N f t km

/-- The flat form of the averaged box-norm power of the peeled difference. -/
def gpowSum (j n s' M₁ : ℕ) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ) : ℝ :=
  ∑ t : IdxT j M₁, ∑ km : KmT j n M₁ c L D t.1 t.2.1,
    Wfun j n M₁ c L D t km * GGfun j n s' M₁ c L D N f t km

/-! ## The abstract threshold/Markov step -/

/-- **The mass step.**  Let `W` be a sub-probability weight on the fibres `Km t`, `FF` a function
with values in `[0,1]` (only the upper bound is used), `GG ≥ 0`, `Bad` a predicate on the base with
`#Bad ≤ γ |T|`, and suppose that on the complement of `Bad` and above the threshold `γ` the function
`GG` dominates the constant `c`.  If the `W`-average of `FF` is at least `4γ`, then the `W`-average
of `GG` is at least `2 γ c`. -/
lemma massThreshold {T : Type*} [Fintype T] {Km : T → Type*} [∀ t, Fintype (Km t)]
    (W FF GG : (t : T) → Km t → ℝ) (Bad : T → Prop) [DecidablePred Bad]
    {γ c : ℝ} (hW : ∀ t km, 0 ≤ W t km) (hW1 : ∀ t, ∑ km, W t km ≤ 1)
    (hF1 : ∀ t km, FF t km ≤ 1)
    (hG0 : ∀ t km, 0 ≤ GG t km)
    (havg : 4 * γ * (Fintype.card T : ℝ) ≤ ∑ t, ∑ km, W t km * FF t km)
    (hbad : ((Finset.univ.filter Bad).card : ℝ) ≤ γ * (Fintype.card T : ℝ))
    (hlem : ∀ t, ¬ Bad t → ∀ km, γ ≤ FF t km → c ≤ GG t km)
    (hc : 0 < c) (hγ : 0 ≤ γ) :
    2 * γ * c * (Fintype.card T : ℝ) ≤ ∑ t, ∑ km, W t km * GG t km := by
  classical
  set H : T → ℝ := fun t => ∑ km, W t km * (if γ ≤ FF t km then (1:ℝ) else 0) with hH
  have key : ∀ t, (∑ km, W t km * FF t km) ≤ γ * (∑ km, W t km) + (1 - γ) * H t := by
    intro t
    change (∑ km, W t km * FF t km) ≤
      γ * (∑ km, W t km) + (1 - γ) * (∑ km, W t km * (if γ ≤ FF t km then (1:ℝ) else 0))
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun km _ => ?_)
    have hWk := hW t km
    by_cases h : γ ≤ FF t km
    · have h1 : W t km * FF t km ≤ W t km * 1 := mul_le_mul_of_nonneg_left (hF1 t km) hWk
      rw [if_pos h]
      nlinarith [h1]
    · have hlt : FF t km ≤ γ := le_of_lt (not_le.mp h)
      have h1 : W t km * FF t km ≤ W t km * γ := mul_le_mul_of_nonneg_left hlt hWk
      rw [if_neg h]
      nlinarith [h1]
  have hsum : (∑ t, ∑ km, W t km * FF t km)
      ≤ γ * (∑ t, ∑ km, W t km) + (1 - γ) * (∑ t, H t) := by
    calc (∑ t, ∑ km, W t km * FF t km) ≤ ∑ t, (γ * (∑ km, W t km) + (1 - γ) * H t) :=
          Finset.sum_le_sum (fun t _ => key t)
      _ = γ * (∑ t, ∑ km, W t km) + (1 - γ) * (∑ t, H t) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hWsum : (∑ t, ∑ km, W t km) ≤ (Fintype.card T : ℝ) := by
    calc (∑ t, ∑ km, W t km) ≤ ∑ _t : T, (1:ℝ) := Finset.sum_le_sum (fun t _ => hW1 t)
      _ = (Fintype.card T : ℝ) := by simp
  have hH0 : 0 ≤ ∑ t, H t := by
    refine Finset.sum_nonneg (fun t _ => ?_)
    change 0 ≤ ∑ km, W t km * (if γ ≤ FF t km then (1:ℝ) else 0)
    refine Finset.sum_nonneg (fun km _ => ?_)
    by_cases h : γ ≤ FF t km <;> simp [h, hW t km]
  have h3 : 3 * γ * (Fintype.card T : ℝ) ≤ ∑ t, H t := by
    have h5 := le_trans havg hsum
    have h2 : γ * (∑ t, ∑ km, W t km) ≤ γ * (Fintype.card T : ℝ) :=
      mul_le_mul_of_nonneg_left hWsum hγ
    have h4 : (1 - γ) * (∑ t, H t) ≤ 1 * (∑ t, H t) :=
      mul_le_mul_of_nonneg_right (by linarith) hH0
    linarith
  have hHle1 : ∀ t, H t ≤ 1 := by
    intro t
    change (∑ km, W t km * (if γ ≤ FF t km then (1:ℝ) else 0)) ≤ 1
    calc (∑ km, W t km * (if γ ≤ FF t km then (1:ℝ) else 0)) ≤ ∑ km, W t km :=
          Finset.sum_le_sum (fun km _ => by
            by_cases h : γ ≤ FF t km
            · rw [if_pos h, mul_one]
            · rw [if_neg h, mul_zero]; exact hW t km)
      _ ≤ 1 := hW1 t
  set Sg : ℝ := ∑ t ∈ (Finset.univ.filter (fun t => ¬ Bad t)), H t with hSg
  have hsplit : (∑ t, H t) = Sg + ∑ t ∈ (Finset.univ.filter Bad), H t := by
    rw [hSg]
    have hf := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset T) Bad H
    rw [← hf]; ring
  have hbadpart : (∑ t ∈ (Finset.univ.filter Bad), H t) ≤ γ * (Fintype.card T : ℝ) := by
    calc (∑ t ∈ (Finset.univ.filter Bad), H t) ≤ ∑ _t ∈ (Finset.univ.filter Bad), (1:ℝ) :=
          Finset.sum_le_sum (fun t _ => hHle1 t)
      _ = (((Finset.univ.filter Bad).card : ℕ) : ℝ) := by simp
      _ ≤ γ * (Fintype.card T : ℝ) := hbad
  have hSg_low : 2 * γ * (Fintype.card T : ℝ) ≤ Sg := by
    linarith
  have hpoint : ∀ t, ¬ Bad t → ∀ km,
      W t km * (if γ ≤ FF t km then (1:ℝ) else 0) ≤ W t km * (GG t km / c) := by
    intro t ht km
    have hWk := hW t km
    by_cases h : γ ≤ FF t km
    · have hc1 : c ≤ GG t km := hlem t ht km h
      have : (1:ℝ) ≤ GG t km / c := by rw [one_le_div hc]; exact hc1
      rw [if_pos h]
      exact mul_le_mul_of_nonneg_left this hWk
    · have : (0:ℝ) ≤ GG t km / c := div_nonneg (hG0 t km) (le_of_lt hc)
      rw [if_neg h, mul_zero]
      exact mul_nonneg hWk this
  have hSg_upper : Sg ≤ (1 / c) * (∑ t, ∑ km, W t km * GG t km) := by
    rw [hSg]
    calc (∑ t ∈ (Finset.univ.filter (fun t => ¬ Bad t)), H t)
        ≤ ∑ t ∈ (Finset.univ.filter (fun t => ¬ Bad t)), ∑ km, W t km * (GG t km / c) := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          change (∑ km, W t km * (if γ ≤ FF t km then (1:ℝ) else 0)) ≤
            ∑ km, W t km * (GG t km / c)
          refine Finset.sum_le_sum (fun km _ => hpoint t (Finset.mem_filter.mp ht).2 km)
      _ ≤ ∑ t : T, ∑ km, W t km * (GG t km / c) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun t _ _ => Finset.sum_nonneg (fun km _ => mul_nonneg (hW t km)
              (div_nonneg (hG0 t km) (le_of_lt hc))))
      _ = (1 / c) * (∑ t, ∑ km, W t km * GG t km) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun km _ => ?_)
          ring
  have hQ : 2 * γ * (Fintype.card T : ℝ) ≤ (1/c) * (∑ t, ∑ km, W t km * GG t km) :=
    le_trans hSg_low hSg_upper
  have hQc : c * (2 * γ * (Fintype.card T : ℝ)) ≤ ∑ t, ∑ km, W t km * GG t km := by
    have h := mul_le_mul_of_nonneg_left hQ (le_of_lt hc)
    rwa [show c * (1/c * (∑ t, ∑ km, W t km * GG t km)) = ∑ t, ∑ km, W t km * GG t km by
      field_simp] at h
  nlinarith [hQc]

/-! ## Elementary weight bounds -/

/-- The per-slot weight `|A|^{-2}` assigned to each of the `|A|²` shift pairs sums to at most `1`. -/
lemma sum_card_inv_sq_le_one {α : Type*} (A : Finset α) :
    ∑ _p : ↥A × ↥A, ((A.card : ℝ))⁻¹ ^ 2 ≤ 1 := by
  classical
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_coe, nsmul_eq_mul, Nat.cast_mul]
  rcases eq_or_ne A.card 0 with h | h
  · simp [h]
  · have hc : (0:ℝ) < (A.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    have hc' : (A.card : ℝ) ≠ 0 := ne_of_gt hc
    have hkey : (A.card : ℝ) * (A.card : ℝ) * ((A.card : ℝ))⁻¹ ^ 2 = 1 := by
      rw [← pow_two, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hc')]
    rw [hkey]

lemma prod_sum_card_inv_sq_le_one {k : ℕ} (A : Fin k → Finset ℤ) :
    ∑ _x : (i : Fin k) → ↥(A i) × ↥(A i), ∏ i, ((A i).card : ℝ)⁻¹ ^ 2 ≤ 1 := by
  classical
  rw [← Fintype.prod_sum (f := fun i (_ : ↥(A i) × ↥(A i)) => ((A i).card : ℝ)⁻¹ ^ 2)]
  exact Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg (fun p _ => by positivity))
    (fun i _ => sum_card_inv_sq_le_one (A i))

lemma prod_sum_card_inv_sq_nonneg {k : ℕ} (A : Fin k → Finset ℤ) :
    0 ≤ ∑ _x : (i : Fin k) → ↥(A i) × ↥(A i), ∏ i, ((A i).card : ℝ)⁻¹ ^ 2 :=
  Finset.sum_nonneg (fun x _ => Finset.prod_nonneg (fun i _ => by positivity))

/-- The product weight `Gwt` is a sub-probability weight on the shift tuples. -/
lemma sum_Gwt_le_one (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁) :
    ∑ km : KmT j n M₁ c L D h₁ h₁', Gwt j n M₁ c L D h₁ h₁' ≤ 1 := by
  classical
  have h1 := prod_sum_card_inv_sq_le_one (fun i : Fin (2^j-1) => ABlk0 j M₁ c L h₁ h₁' i)
  have h2 := prod_sum_card_inv_sq_le_one (fun _ : Fin n => arithIcc c D)
  have h2n := prod_sum_card_inv_sq_nonneg (fun _ : Fin n => arithIcc c D)
  change (∑ km : ((i : Fin (2^j-1)) → ↥(ABlk0 j M₁ c L h₁ h₁' i) × ↥(ABlk0 j M₁ c L h₁ h₁' i)) ×
      ((i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D)),
      Gwt j n M₁ c L D h₁ h₁') ≤ 1
  rw [Gwt]
  rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum]
  calc _ ≤ 1 * _ := mul_le_mul_of_nonneg_right h1 h2n
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 1 := by norm_num

/-! ## Reindexings -/

lemma sum_prod_three {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    {Km : A → B → Type*} [∀ a b, Fintype (Km a b)]
    (F : (a : A) → (b : B) → (c : C) → Km a b → ℝ) :
    (∑ t : A × (B × C), ∑ km : Km t.1 t.2.1, F t.1 t.2.1 t.2.2 km)
      = ∑ a, ∑ b, ∑ c, ∑ km, F a b c km := by
  have h1 : (∑ t : A × (B × C), ∑ km : Km t.1 t.2.1, F t.1 t.2.1 t.2.2 km)
      = ∑ a : A, ∑ q : B × C, ∑ km : Km a q.1, F a q.1 q.2 km :=
    Fintype.sum_prod_type _
  rw [h1]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact Fintype.sum_prod_type (f := fun q : B × C => ∑ km : Km a q.1, F a q.1 q.2 km)

lemma sum_prod_three_simple {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (G : A → B → C → ℝ) :
    (∑ t : A × (B × C), G t.1 t.2.1 t.2.2) = ∑ a, ∑ b, ∑ c, G a b c := by
  have h1 : (∑ t : A × (B × C), G t.1 t.2.1 t.2.2) = ∑ a : A, ∑ q : B × C, G a q.1 q.2 :=
    Fintype.sum_prod_type _
  rw [h1]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact Fintype.sum_prod_type (f := fun q : B × C => G a q.1 q.2)

lemma sum_prod_three_indep' {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    {Km : A → B → Type*} [∀ a b, Fintype (Km a b)] (F : (a : A) → (b : B) → Km a b → ℝ) :
    (∑ t : A × (B × C), ∑ km : Km t.1 t.2.1, F t.1 t.2.1 km)
      = (Fintype.card C : ℝ) * (∑ a, ∑ b, ∑ km, F a b km) := by
  rw [sum_prod_three (F := fun a b (_ : C) km => F a b km)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## Bounds on the averaged box norm and on the peeled difference -/

lemma boxAvgA_nonneg (s : ℕ) (c : ℤ) (M₁ M₂ : ℕ) (b : Fin s → ℤ) (N : ℕ) (g : ℤ → ℂ) :
    0 ≤ LadderQ.boxAvgA s c M₁ M₂ b N g := by
  rw [LadderQ.boxAvgA]
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => ?_))
  rw [boxNorm]
  exact Real.rpow_nonneg (norm_nonneg _) _

lemma boxAvgA_le_one (s : ℕ) (c : ℤ) (M₁ M₂ : ℕ) (b : Fin s → ℤ) (N : ℕ) (g : ℤ → ℂ)
    (hM₁ : 1 ≤ M₁) (hbd : ∀ x, ‖g x‖ ≤ 1) (hsup : SuppSmall N g) :
    LadderQ.boxAvgA s c M₁ M₂ b N g ≤ 1 := by
  rw [LadderQ.boxAvgA]
  have h1 : ∑ a ∈ Finset.Icc 1 M₁,
      boxNorm s (fun i : Fin s => arithIcc (c * ((a : ℤ) + b i)) M₂) (symIcc N) g ≤ (M₁ : ℝ) := by
    calc ∑ a ∈ Finset.Icc 1 M₁,
        boxNorm s (fun i : Fin s => arithIcc (c * ((a : ℤ) + b i)) M₂) (symIcc N) g
        ≤ ∑ _a ∈ Finset.Icc 1 M₁, (1 : ℝ) :=
          Finset.sum_le_sum (fun a _ => boxNorm_le_one_of_suppSmall hbd hsup)
      _ = ((Finset.Icc 1 M₁).card : ℝ) := by simp
      _ = (M₁ : ℝ) := by rw [Nat.card_Icc]; simp
  calc ((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
        boxNorm s (fun i : Fin s => arithIcc (c * ((a : ℤ) + b i)) M₂) (symIcc N) g
      ≤ ((M₁ : ℝ))⁻¹ * (M₁ : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by
        have hne : (M₁ : ℝ) ≠ 0 := by positivity
        exact inv_mul_cancel₀ hne

lemma Gof_bd (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁)
    (km : KmT j n M₁ c L D h₁ h₁') {f : ℤ → ℂ} (hbd : ∀ z : ℤ, ‖f z‖ ≤ 1) :
    ∀ x : ℤ, ‖Gof j n M₁ c L D h₁ h₁' km f x‖ ≤ 1 := by
  rw [Gof]
  exact Ulower.norm_iterDelta_le_one n _ _
    (Ulower.norm_iterDelta_le_one (2^j - 1) _ _ hbd)

lemma Gof_suppSmall (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h₁ h₁' : Fin j → Fin M₁)
    (km : KmT j n M₁ c L D h₁ h₁') {N : ℕ} {f : ℤ → ℂ} (hsup : SuppSmall N f) :
    SuppSmall N (Gof j n M₁ c L D h₁ h₁' km f) := by
  rw [Gof]
  exact SuppSmall.iterDelta n _ (SuppSmall.iterDelta (2^j - 1) _ hsup)

/-! ## The mass lower bound -/

theorem massLower (j n M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (L D N : ℕ) (f : ℤ → ℂ)
    (hfin : Work.Peluse.FinSuppZ f) (hbd : ∀ z : ℤ, ‖f z‖ ≤ 1) (hsup : Work.Peluse.SupportIn f N)
    (hs : Fin M₁) {u γ η ε : ℝ} {s' e₅₁ : ℕ} (hs' : 1 ≤ s') (he₅₁ : 1 ≤ e₅₁) {C₅₁ : ℝ}
    (hC₅₁ : 0 < C₅₁) (hC₅₁' : C₅₁ ≤ 1)
    (hγ : γ = u ^ (2^(2^(j+1) - 1 + n)) / 4) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hε : ε = C₅₁ * γ ^ e₅₁)
    (havg : u ^ (2^(2^(j+1) - 1 + n))
      ≤ ((M₁ : ℝ))⁻¹ ^ (2*j+1) *
        ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          ∑ km : Work.Peluse.LadderP.KmT j n M₁ c L D h₁ h₁',
            Work.Peluse.LadderP.Gwt j n M₁ c L D h₁ h₁' *
              Work.Peluse.LadderQ.boxAvgA (2^j) c M₁ L
                (Work.Peluse.LadderP.stepShift3E (Work.Peluse.LadderP.enumAll j) h₁ h₁' h'_s) N
                (Work.Peluse.LadderP.Gof j n M₁ c L D h₁ h₁' km f))
    (hbad : ((M₁ : ℝ))⁻¹ ^ (2*j+1) *
        ∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          (if ε * (M₁ : ℝ)
              < ((Work.Peluse.LadderP.stepBad j M₁ η (Work.Peluse.LadderP.enumAll j)
                  (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ)
            then (1 : ℝ) else 0) ≤ γ)
    (lem : ∀ (h₁ : Fin j → Fin M₁) (h₁' : Fin j → Fin M₁) (h'_s : Fin M₁)
        (km : Work.Peluse.LadderP.KmT j n M₁ c L D h₁ h₁'),
      γ ≤ Work.Peluse.LadderQ.boxAvgA (2^j) c M₁ L
            (Work.Peluse.LadderP.stepShift3E (Work.Peluse.LadderP.enumAll j) h₁ h₁' h'_s) N
            (Work.Peluse.LadderP.Gof j n M₁ c L D h₁ h₁' km f) →
      ¬ (ε * (M₁ : ℝ)
          < ((Work.Peluse.LadderP.stepBad j M₁ η (Work.Peluse.LadderP.enumAll j)
              (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ)) →
      (C₅₁ * γ ^ e₅₁) ^ (2^s')
        ≤ Work.Peluse.LadderP.Gpow j n s' M₁ c L D N h₁ h₁' km f)
    : 2 * γ * (C₅₁ * γ ^ e₅₁) ^ (2^s')
      ≤ Work.Peluse.LadderP.patPowState j (n+s') M₁ c L D N f := by
  classical
  have hM1pos : (0:ℝ) < (M₁:ℝ) := by exact_mod_cast (by omega : 0 < M₁)
  have hM1ne : (M₁:ℝ) ≠ 0 := ne_of_gt hM1pos
  have hγpos : 0 < γ := by
    rw [hγ]; exact div_pos (pow_pos hu0 _) (by norm_num)
  have hγnn : 0 ≤ γ := le_of_lt hγpos
  have huK : u ^ (2^(2^(j+1) - 1 + n)) = 4 * γ := by rw [hγ]; ring
  have hcardT := card_IdxT j M₁
  have hmulInv : ∀ X : ℝ, (M₁:ℝ)^(2*j+1) * (((M₁:ℝ))⁻¹ ^ (2*j+1) * X) = X := by
    intro X
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hM1ne, one_pow, one_mul]
  have hmulInv2 : ∀ X : ℝ, (M₁:ℝ)^(2*j) * (((M₁:ℝ))⁻¹ ^ (2*j) * X) = X := by
    intro X
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hM1ne, one_pow, one_mul]
  -- the flat form of the averaged box norm, matched with `havg`
  have hflatFF : massSum j n M₁ c L D N f
      = (∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          ∑ km : KmT j n M₁ c L D h₁ h₁',
            Gwt j n M₁ c L D h₁ h₁' *
              LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
                (Gof j n M₁ c L D h₁ h₁' km f)) := by
    unfold massSum
    exact sum_prod_three (F := fun h₁ h₁' h'_s km =>
      Gwt j n M₁ c L D h₁ h₁' *
        LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) h₁ h₁' h'_s) N
          (Gof j n M₁ c L D h₁ h₁' km f))
  have havgFlat : u ^ (2^(2^(j+1) - 1 + n))
      ≤ ((M₁ : ℝ))⁻¹ ^ (2 * j + 1) * massSum j n M₁ c L D N f := by
    rw [hflatFF]
    exact havg
  have havgt : 4 * γ * (Fintype.card (IdxT j M₁) : ℝ) ≤ massSum j n M₁ c L D N f := by
    have h1 := mul_le_mul_of_nonneg_left havgFlat (show (0:ℝ) ≤ (M₁:ℝ)^(2*j+1) by positivity)
    rw [hmulInv] at h1
    have h2 : (M₁:ℝ)^(2*j+1) * u ^ (2^(2^(j+1) - 1 + n))
        = 4 * γ * (Fintype.card (IdxT j M₁) : ℝ) := by
      rw [huK, hcardT]; push_cast; ring
    linarith [h1, h2]
  -- the bad set
  have hbadSum : (∑ t : IdxT j M₁, (if BadFun j M₁ η ε hs t then (1:ℝ) else 0))
      = (∑ h₁ : Fin j → Fin M₁, ∑ h₁' : Fin j → Fin M₁, ∑ h'_s : Fin M₁,
          (if ε * (M₁:ℝ) < ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs)
              (Fin.snoc h₁' h'_s)).card : ℝ) then (1:ℝ) else 0)) := by
    unfold BadFun
    exact sum_prod_three_simple (fun h₁ h₁' h'_s => if ε * (M₁:ℝ) <
      ((stepBad j M₁ η (enumAll j) (Fin.snoc h₁ hs) (Fin.snoc h₁' h'_s)).card : ℝ)
      then (1:ℝ) else 0)
  have hbadCard : ((Finset.univ.filter (BadFun j M₁ η ε hs)).card : ℝ)
      ≤ γ * (Fintype.card (IdxT j M₁) : ℝ) := by
    have h2 : (∑ t : IdxT j M₁, (if BadFun j M₁ η ε hs t then (1:ℝ) else 0))
        = (((Finset.univ.filter (BadFun j M₁ η ε hs)).card : ℕ) : ℝ) := by
      rw [Finset.card_filter]; push_cast; rfl
    have h3 := mul_le_mul_of_nonneg_left hbad (show (0:ℝ) ≤ (M₁:ℝ)^(2*j+1) by positivity)
    rw [hmulInv] at h3
    rw [← hbadSum, h2] at h3
    rw [hcardT]; push_cast
    linarith [h3]
  -- the weighted sum of the box-norm powers
  have hPP : (∑ a : Fin j → Fin M₁, ∑ b : Fin j → Fin M₁,
        ∑ km : KmT j n M₁ c L D a b,
          Gwt j n M₁ c L D a b * Gpow j n s' M₁ c L D N a b km f)
      = (M₁:ℝ)^(2*j) * patPowState j (n+s') M₁ c L D N f := by
    rw [patPowState_peel j n s' M₁ hs' c L D N f hfin]
    rw [hmulInv2]
  have hGG : gpowSum j n s' M₁ c L D N f
      = (Fintype.card (IdxT j M₁) : ℝ) * patPowState j (n+s') M₁ c L D N f := by
    unfold gpowSum
    unfold Wfun GGfun
    rw [sum_prod_three_indep' (F := fun a b km =>
      Gwt j n M₁ c L D a b * Gpow j n s' M₁ c L D N a b km f)]
    simp only [Fintype.card_fin]
    rw [hPP, hcardT]
    push_cast
    rw [show (2*j+1) = 1 + 2*j by omega, pow_add]
    ring
  -- the pointwise application of the Lemma 5.1 input
  have hlem' : ∀ (t : IdxT j M₁), ¬ BadFun j M₁ η ε hs t →
      ∀ km : KmT j n M₁ c L D t.1 t.2.1,
        γ ≤ LadderQ.boxAvgA (2^j) c M₁ L (stepShift3E (enumAll j) t.1 t.2.1 t.2.2) N
              (Gof j n M₁ c L D t.1 t.2.1 km f) →
        (C₅₁ * γ ^ e₅₁) ^ (2^s') ≤ Gpow j n s' M₁ c L D N t.1 t.2.1 km f :=
    fun t ht km hge => lem t.1 t.2.1 t.2.2 km hge ht
  have hW0 : ∀ (t : IdxT j M₁) (km : KmT j n M₁ c L D t.1 t.2.1),
      0 ≤ Wfun j n M₁ c L D t km := fun t km => Gwt_nonneg j n M₁ c L D t.1 t.2.1
  have hW1 : ∀ t : IdxT j M₁, ∑ km : KmT j n M₁ c L D t.1 t.2.1,
      Wfun j n M₁ c L D t km ≤ 1 :=
    fun t => sum_Gwt_le_one j n M₁ c L D t.1 t.2.1
  have hF1 : ∀ (t : IdxT j M₁) (km : KmT j n M₁ c L D t.1 t.2.1),
      FFfun j n M₁ c L D N f t km ≤ 1 :=
    fun t km => boxAvgA_le_one (2^j) c M₁ L _ N _ hM₁
      (Gof_bd j n M₁ c L D t.1 t.2.1 km hbd)
      (Gof_suppSmall j n M₁ c L D t.1 t.2.1 km (SuppSmall.of_supportIn hsup))
  have hG0 : ∀ (t : IdxT j M₁) (km : KmT j n M₁ c L D t.1 t.2.1),
      0 ≤ GGfun j n s' M₁ c L D N f t km := by
    intro t km
    rw [GGfun]
    rw [Gpow]
    exact boxNormPow_nonneg'
  have hmain := massThreshold
      (T := IdxT j M₁)
      (Km := fun t : IdxT j M₁ => KmT j n M₁ c L D t.1 t.2.1)
      (W := Wfun j n M₁ c L D)
      (FF := FFfun j n M₁ c L D N f)
      (GG := GGfun j n s' M₁ c L D N f)
      (Bad := BadFun j M₁ η ε hs)
      hW0 hW1 hF1 hG0 havgt hbadCard hlem' (by positivity) hγnn
  have hfin : 2 * γ * (C₅₁ * γ ^ e₅₁) ^ (2^s') * (Fintype.card (IdxT j M₁) : ℝ)
      ≤ (Fintype.card (IdxT j M₁) : ℝ) * patPowState j (n+s') M₁ c L D N f := by
    rw [← hGG]
    exact hmain
  have hcardTpos : (0:ℝ) < (Fintype.card (IdxT j M₁) : ℝ) := by
    rw [hcardT]; push_cast; exact pow_pos hM1pos _
  exact le_of_mul_le_mul_left (by
    rw [mul_comm (Fintype.card (IdxT j M₁) : ℝ) (2 * γ * (C₅₁ * γ ^ e₅₁) ^ (2^s'))]
    exact hfin) hcardTpos

end

end Work.Peluse.LadderP
