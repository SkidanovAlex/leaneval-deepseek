import Mathlib

/-!
# Polarization bound for symmetric continuous multilinear maps

For a symmetric continuous `k`-multilinear map `T` on a real normed space, the operator norm
of `T` is controlled by the sup-norm of its restriction to the diagonal, with the classical
polarization constant `k^k / k!`:

`‖T‖ ≤ (k^k / k!) · sup_{‖x‖ ≤ 1} ‖T (x, …, x)‖`.

The proof uses the "signed" polarization identity
`∑_{ε ∈ {±1}^k} (∏ ε_i) T(∑ ε_j v_j, …, ∑ ε_j v_j) = 2^k k! · T(v_1, …, v_k)`,
each argument of which has norm at most `k` on the unit ball.
-/

open Finset

namespace Work.CR.Flat.Cauchy

noncomputable section

/-- Sign of a boolean, as a real number (`true ↦ 1`, `false ↦ -1`). -/
def bsign (b : Bool) : ℝ := if b then 1 else -1

/-- A product of sums over a finite product index type equals a sum of products. -/
lemma sum_bsign_pow (k : ℕ) (a : Fin k → ℕ) :
    (∑ b : Fin k → Bool, ∏ i, bsign (b i) ^ a i) = ∏ i, (1 + (-1 : ℝ) ^ a i) := by
  rw [← Fintype.prod_sum (κ := fun _ : Fin k => Bool) (f := fun i (c : Bool) => bsign c ^ a i)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  simp [bsign]

/-- Rewrite a product over a composed index as a product over the fibers. -/
lemma prod_bsign_comp (k : ℕ) (b : Fin k → Bool) (r : Fin k → Fin k) :
    (∏ i, bsign (b (r i))) = ∏ l, bsign (b l) ^ (Finset.univ.filter (fun i => r i = l)).card := by
  rw [← Finset.prod_fiberwise' (Finset.univ) r (fun l => bsign (b l))]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Finset.prod_const]

lemma add_neg_one_pow_odd {n : ℕ} (h : Odd n) : (1 : ℝ) + (-1) ^ (1 + n) = 2 := by
  rw [pow_add, Odd.neg_one_pow h]; norm_num

lemma add_neg_one_pow_even {n : ℕ} (h : Even n) : (1 : ℝ) + (-1) ^ (1 + n) = 0 := by
  rw [pow_add, Even.neg_one_pow h]; norm_num

lemma prod_factor (k : ℕ) (n : Fin k → ℕ) :
    (∏ l, (1 + (-1 : ℝ) ^ (1 + n l))) = if (∀ l, Odd (n l)) then (2 : ℝ) ^ k else 0 := by
  by_cases h : ∀ l, Odd (n l)
  · rw [if_pos h]
    rw [Finset.prod_congr rfl (fun l _ => add_neg_one_pow_odd (h l)), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]; push_neg at h
    obtain ⟨l, hl⟩ := h; rw [Nat.not_odd_iff_even] at hl
    exact Finset.prod_eq_zero (Finset.mem_univ l) (add_neg_one_pow_even hl)

/-- A map `Fin k → Fin k` is bijective iff all its fibers have odd cardinality. -/
lemma all_odd_fiber_iff (k : ℕ) (r : Fin k → Fin k) :
    (∀ l, Odd ((Finset.univ.filter (fun i => r i = l)).card)) ↔ Function.Bijective r := by
  constructor
  · intro h
    have hsurj : Function.Surjective r := fun l => by
      have hpos : 0 < (Finset.univ.filter (fun i => r i = l)).card := (h l).pos
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    exact ⟨(Finite.injective_iff_surjective.mpr hsurj), hsurj⟩
  · intro h l
    let σ : Fin k ≃ Fin k := Equiv.ofBijective r h
    have hfil : (Finset.univ.filter (fun i => r i = l)) = {σ.symm l} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [Equiv.eq_symm_apply]; simp [σ, Equiv.ofBijective_apply]
    rw [hfil, Finset.card_singleton]; exact odd_one

/-- Sign orthogonality: `∑_b (∏_i ε(b_i)) (∏_i ε(b_{r i}))` is `2^k` iff `r` is a bijection. -/
lemma coeff_sum (k : ℕ) (r : Fin k → Fin k) :
    (∑ b : Fin k → Bool, (∏ i, bsign (b i)) * (∏ i, bsign (b (r i))))
      = if Function.Bijective r then (2 : ℝ) ^ k else 0 := by
  have hterm : ∀ (b : Fin k → Bool), (∏ i, bsign (b i)) * (∏ i, bsign (b (r i)))
      = ∏ l, bsign (b l) ^ (1 + (Finset.univ.filter (fun i => r i = l)).card) := by
    intro b
    have h1 : (∏ i, bsign (b i)) = ∏ l, bsign (b l) ^ 1 := by
      refine Finset.prod_congr rfl (fun l _ => ?_); rw [pow_one]
    rw [h1, prod_bsign_comp]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [pow_add, pow_one]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), sum_bsign_pow, prod_factor]
  by_cases hb : ∀ l, Odd ((Finset.univ.filter (fun i => r i = l)).card)
  · rw [if_pos hb, if_pos ((all_odd_fiber_iff k r).mp hb)]
  · rw [if_neg hb, if_neg (fun hc => hb ((all_odd_fiber_iff k r).mpr hc))]

/-- The subtype of bijective functions `Fin k → Fin k` is equivalent to `Equiv.Perm (Fin k)`. -/
def bijectiveEquiv (k : ℕ) :
    {r : Fin k → Fin k // Function.Bijective r} ≃ Equiv.Perm (Fin k) where
  toFun r := Equiv.ofBijective r.1 r.2
  invFun σ := ⟨σ, σ.bijective⟩
  left_inv r := by ext x; simp
  right_inv σ := by ext x; simp

/-- Card-card version of the sign orthogonality: the sum of `c • g r` over bijective `r` is
`(c * k!) • g id`, provided `g` is constant on the permutation subgroup. -/
lemma sum_bijective_smul {F : Type*} [AddCommGroup F] [Module ℝ F]
    {k : ℕ} (c : ℝ) (g : (Fin k → Fin k) → F)
    (hg : ∀ σ : Equiv.Perm (Fin k), g (⇑σ) = g (id : Fin k → Fin k)) :
    (∑ r : Fin k → Fin k, (if Function.Bijective r then c else 0) • g r)
      = (c * (k.factorial : ℝ)) • g (id : Fin k → Fin k) := by
  have h1 : ∀ r, (if Function.Bijective r then c else 0) • g r
      = if Function.Bijective r then c • g r else 0 := by
    intro r; by_cases h : Function.Bijective r <;> simp [h]
  rw [Finset.sum_congr rfl (fun r _ => h1 r), ← Finset.sum_filter,
    Finset.sum_subtype (p := Function.Bijective) (Finset.univ.filter (Function.Bijective))
      (fun x => by simp),
    Fintype.sum_equiv (bijectiveEquiv k) (fun r => c • g ↑r) (fun σ => c • g ⇑σ)
      (fun r => by simp [bijectiveEquiv])]
  have hsum : (∑ σ : Equiv.Perm (Fin k), g ⇑σ)
      = (k.factorial : ℝ) • g (id : Fin k → Fin k) := by
    rw [Finset.sum_congr rfl (fun σ _ => hg σ), Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  rw [← Finset.smul_sum, hsum, smul_smul]

/-- Multiplicity of the index type `Fin k → Bool`, as a real scalar. -/
lemma sum_const_bool {F : Type*} [AddCommMonoid F] [Module ℝ F] {k : ℕ} (x : F) :
    (∑ _b : Fin k → Bool, x) = ((2 : ℝ) ^ k) • x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ (2 ^ k) x]
  rw [Nat.cast_pow]; norm_num

/-- Multilinear expansion of a diagonal at a signed combination. -/
lemma expansion {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (u : Fin k → E) (b : Fin k → Bool) :
    T (fun _ : Fin k => ∑ i, bsign (b i) • u i)
      = ∑ r : Fin k → Fin k, (∏ i, bsign (b (r i))) • T (u ∘ r) := by
  rw [ContinuousMultilinearMap.map_sum T (fun (_ : Fin k) (j : Fin k) => bsign (b j) • u j)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [ContinuousMultilinearMap.map_smul_univ]; rfl

/-- Multilinear expansion, with the outer sign factor brought inside. -/
lemma expansion_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (u : Fin k → E) (b : Fin k → Bool) :
    (∏ i, bsign (b i)) • T (fun _ : Fin k => ∑ i, bsign (b i) • u i)
      = ∑ r : Fin k → Fin k, ((∏ i, bsign (b i)) * (∏ i, bsign (b (r i)))) • T (u ∘ r) := by
  rw [expansion T u b, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_); rw [← smul_smul]

/-- **Signed polarization identity** for a symmetric continuous multilinear map. -/
lemma polarization {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E), T (v ∘ σ) = T v)
    (u : Fin k → E) :
    ((2 : ℝ) ^ k * (k.factorial : ℝ)) • T u
      = ∑ b : Fin k → Bool,
          (∏ i, bsign (b i)) • T (fun _ : Fin k => ∑ i, bsign (b i) • u i) := by
  rw [Finset.sum_congr rfl (fun b _ => expansion_smul T u b)]
  rw [Finset.sum_comm]
  have key : ∀ r : Fin k → Fin k,
      (∑ b : Fin k → Bool, ((∏ i, bsign (b i)) * (∏ i, bsign (b (r i)))) • T (u ∘ r))
        = (if Function.Bijective r then (2 : ℝ) ^ k else 0) • T (u ∘ r) := by
    intro r
    rw [← Finset.sum_smul, coeff_sum]
  rw [Finset.sum_congr rfl (fun r _ => key r)]
  rw [sum_bijective_smul (k := k) ((2 : ℝ) ^ k) (fun r => T (u ∘ r)) (fun σ => hsym σ u)]
  simp

theorem norm_continuousMultilinearMap_le_of_diagonal {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (hsym : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → E), T (v ∘ σ) = T v)
    {D : ℝ} (hD : ∀ x : E, ‖x‖ ≤ 1 → ‖T (fun _ => x)‖ ≤ D) :
    ‖T‖ ≤ (k : ℝ) ^ k / (k.factorial : ℝ) * D := by
  have hDnn : 0 ≤ D := le_trans (norm_nonneg _) (hD 0 (by simp))
  have habs : ∀ b : Bool, |bsign b| = 1 := by intro b; cases b <;> simp [bsign]
  have hprodnorm : ∀ b : Fin k → Bool, ‖∏ i, bsign (b i)‖ = 1 := by
    intro b
    rw [Real.norm_eq_abs, Finset.abs_prod]
    simp [habs]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; norm_num
    · exact one_le_pow₀ (by exact_mod_cast hk)
  -- diagonal bound on the ball of radius `k`
  have hdiag : ∀ x : E, ‖x‖ ≤ (k : ℝ) → ‖T (fun _ => x)‖ ≤ (k : ℝ) ^ k * D := by
    intro x hx
    rcases eq_or_ne x 0 with hx0 | hx0
    · subst hx0
      refine le_trans (hD 0 (by simp)) ?_
      simpa using mul_le_mul_of_nonneg_right hk1 hDnn
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      set r : ℝ := ‖x‖ with hr
      set y : E := r⁻¹ • x with hy
      have hrpos : 0 < r := by rw [hr]; exact hxpos
      have hynorm : ‖y‖ = 1 := by
        rw [hy, norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt hrpos), hr,
          inv_mul_cancel₀ (ne_of_gt hrpos)]
      have hxd : x = r • y := by
        rw [hy, smul_smul, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]
      have hrr : r ≤ (k : ℝ) := by rw [hr]; exact hx
      have hdiagx : T (fun _ : Fin k => x) = r ^ k • T (fun _ : Fin k => y) := by
        rw [hxd]
        rw [show (fun _ : Fin k => r • y)
              = (fun i => (fun _ : Fin k => r) i • (fun _ : Fin k => y) i) from rfl]
        rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]
      calc ‖T (fun _ : Fin k => x)‖
          = r ^ k * ‖T (fun _ : Fin k => y)‖ := by
            rw [hdiagx, norm_smul, Real.norm_of_nonneg (pow_nonneg (le_of_lt hrpos) k)]
        _ ≤ r ^ k * D :=
            mul_le_mul_of_nonneg_left (hD y (le_of_eq hynorm)) (pow_nonneg (le_of_lt hrpos) k)
        _ ≤ (k : ℝ) ^ k * D :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_of_lt hrpos) hrr k) hDnn
  -- the main polarization estimate on the unit ball
  have hkey : ∀ u : Fin k → E, (∀ i, ‖u i‖ ≤ 1) →
      ‖T u‖ ≤ (k : ℝ) ^ k / (k.factorial : ℝ) * D := by
    intro u hu
    have hpoli := polarization T hsym u
    have hc : (0 : ℝ) < (2 : ℝ) ^ k * (k.factorial : ℝ) :=
      mul_pos (pow_pos (by norm_num) k) (by exact_mod_cast Nat.factorial_pos k)
    have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hterm : ∀ b : Fin k → Bool,
        ‖T (fun _ : Fin k => ∑ i, bsign (b i) • u i)‖ ≤ (k : ℝ) ^ k * D := by
      intro b
      apply hdiag
      calc ‖∑ i, bsign (b i) • u i‖ ≤ ∑ i, ‖bsign (b i) • u i‖ := norm_sum_le _ _
        _ = ∑ i, ‖u i‖ := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [norm_smul, Real.norm_eq_abs, habs (b i), one_mul]
        _ ≤ ∑ _i : Fin k, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hu i)
        _ = (k : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
    have hbound : (2 : ℝ) ^ k * (k.factorial : ℝ) * ‖T u‖ ≤ (2 : ℝ) ^ k * ((k : ℝ) ^ k * D) := by
      have h1 : ‖((2 : ℝ) ^ k * (k.factorial : ℝ)) • T u‖
          = (2 : ℝ) ^ k * (k.factorial : ℝ) * ‖T u‖ := by
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt hc)]
      have h2 : ‖∑ b : Fin k → Bool,
            (∏ i, bsign (b i)) • T (fun _ : Fin k => ∑ i, bsign (b i) • u i)‖
          ≤ (2 : ℝ) ^ k * ((k : ℝ) ^ k * D) := by
        refine le_trans (norm_sum_le _ _) ?_
        have hstep : ∀ b : Fin k → Bool,
            ‖(∏ i, bsign (b i)) • T (fun _ : Fin k => ∑ i, bsign (b i) • u i)‖ ≤ (k : ℝ) ^ k * D := by
          intro b
          rw [norm_smul, hprodnorm b, one_mul]
          exact hterm b
        calc ∑ b : Fin k → Bool,
              ‖(∏ i, bsign (b i)) • T (fun _ : Fin k => ∑ i, bsign (b i) • u i)‖
            ≤ ∑ _b : Fin k → Bool, ((k : ℝ) ^ k * D) := Finset.sum_le_sum (fun b _ => hstep b)
          _ = (2 : ℝ) ^ k * ((k : ℝ) ^ k * D) := by rw [sum_const_bool, smul_eq_mul]
      rw [← h1, hpoli]
      exact h2
    have hmain : (k.factorial : ℝ) * ‖T u‖ ≤ (k : ℝ) ^ k * D := by
      have this : (2 : ℝ) ^ k * ((k.factorial : ℝ) * ‖T u‖)
          ≤ (2 : ℝ) ^ k * ((k : ℝ) ^ k * D) := by
        rw [← mul_assoc]; exact hbound
      exact (mul_le_mul_iff_of_pos_left h2k).mp this
    have hfin : ‖T u‖ ≤ (k : ℝ) ^ k * D / (k.factorial : ℝ) :=
      (le_div_iff₀ hf).mpr (by rw [mul_comm]; exact hmain)
    calc ‖T u‖ ≤ (k : ℝ) ^ k * D / (k.factorial : ℝ) := hfin
      _ = (k : ℝ) ^ k / (k.factorial : ℝ) * D := by ring
  set M : ℝ := (k : ℝ) ^ k / (k.factorial : ℝ) * D with hM
  have hMnn : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (div_nonneg (pow_nonneg (Nat.cast_nonneg k) k) (Nat.cast_nonneg _)) hDnn
  apply ContinuousMultilinearMap.opNorm_le_bound hMnn
  intro v
  rw [hM]
  by_cases hv : ∃ i, ‖v i‖ = 0
  · obtain ⟨i, hi⟩ := hv
    have hv0 : v i = 0 := norm_eq_zero.mp hi
    have hTv : T v = 0 := ContinuousMultilinearMap.map_coord_zero T i hv0
    rw [hTv, norm_zero]
    exact mul_nonneg
      (mul_nonneg (div_nonneg (pow_nonneg (Nat.cast_nonneg k) k) (Nat.cast_nonneg _)) hDnn)
      (Finset.prod_nonneg (fun i _ => norm_nonneg _))
  · push_neg at hv
    set u : Fin k → E := fun i => (‖v i‖)⁻¹ • v i with hu
    have hapos : ∀ i, 0 < ‖v i‖ := fun i => lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hv i))
    have hunorm : ∀ i, ‖u i‖ ≤ 1 := by
      intro i
      rw [hu]
      simp only
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg (v i)), inv_mul_cancel₀ (hv i)]
    have hvs : v = fun i => ‖v i‖ • u i := by
      ext i; rw [hu, smul_smul, mul_inv_cancel₀ (hv i), one_smul]
    have hTv : T v = (∏ i, ‖v i‖) • T u := by
      conv_lhs => rw [hvs]
      rw [ContinuousMultilinearMap.map_smul_univ]
    have hTu := hkey u hunorm
    calc ‖T v‖ = (∏ i, ‖v i‖) * ‖T u‖ := by
          rw [hTv, norm_smul, Real.norm_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg _))]
      _ ≤ (∏ i, ‖v i‖) * ((k : ℝ) ^ k / (k.factorial : ℝ) * D) :=
          mul_le_mul_of_nonneg_left hTu (Finset.prod_nonneg (fun i _ => norm_nonneg _))
      _ = (k : ℝ) ^ k / (k.factorial : ℝ) * D * ∏ i, ‖v i‖ := by ring

end

end Work.CR.Flat.Cauchy
