import Mathlib

/-!
# The weighted lattice count of *FI* (9.7)

We prove `Work.FIArea2.sum_weight_sqcong`: the weighted count of lattice points
`(h₁,h₂) ∈ ℤ²` with `a h₁² ≡ b h₂² (mod q)` is at most `64(H²/q² + 1)` times the
number `N(a,b;q)` of residue solutions `(γ₁,γ₂)` modulo `q`.

The double sum is split over the residues of `h₁`, `h₂` modulo `q`
(`h ↦ (h mod q, h / q)` is the equivalence `Int.divModEquiv q`), which turns it into
`Σ_{(γ₁,γ₂)} S(γ₁)S(γ₂)` with `S(γ) = Σ_k (1 + (kq+γ)²/H²)⁻¹`; the elementary bound
`S(γ) ≤ 2 + 6H/q` (comparison with the telescoping series `Σ 1/n²`) closes it.
-/

namespace Work.FIArea2

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ### Reindexing `ℤ` by `(residue, quotient)` -/

/-- `ℤ ≃ Fin q × ℤ` given by `z ↦ (z mod q, z / q)`. -/
def dq (q : ℕ) [NeZero q] : ℤ ≃ Fin q × ℤ :=
  (Int.divModEquiv q).trans (Equiv.prodComm ℤ (Fin q))

lemma dq_symm_apply (q : ℕ) [NeZero q] (i : Fin q) (k : ℤ) :
    (dq q).symm (i, k) = k * (q : ℤ) + (i : ℤ) := by
  unfold dq
  rw [Equiv.symm_trans_apply, Equiv.prodComm_symm, Equiv.prodComm_apply]
  simp [Int.divModEquiv_symm_apply]

/-- `ℤ × ℤ ≃ (Fin q × Fin q) × (ℤ × ℤ)` separating residues and quotients. -/
def eps (q : ℕ) [NeZero q] : ℤ × ℤ ≃ (Fin q × Fin q) × (ℤ × ℤ) :=
  ((dq q).prodCongr (dq q)).trans (Equiv.prodProdProdComm (Fin q) ℤ (Fin q) ℤ)

lemma eps_symm_apply (q : ℕ) [NeZero q] (i1 i2 : Fin q) (k1 k2 : ℤ) :
    (eps q).symm ((i1, i2), (k1, k2)) =
      ((k1 * (q : ℤ) + (i1 : ℤ)), (k2 * (q : ℤ) + (i2 : ℤ))) := by
  unfold eps
  rw [Equiv.symm_trans_apply]
  have h2 : (Equiv.prodProdProdComm (Fin q) ℤ (Fin q) ℤ).symm ((i1,i2),(k1,k2))
      = ((i1,k1),(i2,k2)) := rfl
  rw [h2, Equiv.prodCongr_symm, Equiv.prodCongr_apply]
  simp only [Prod.map_apply, dq_symm_apply]

/-- Decompose a sum over `ℤ × ℤ` into residue classes modulo `q`. -/
lemma tsum_pair_decomp (q : ℕ) [NeZero q] (F : ℤ × ℤ → ℝ) (hF : Summable F) :
    ∑' p : ℤ × ℤ, F p
      = ∑ b : Fin q × Fin q, ∑' k1 : ℤ, ∑' k2 : ℤ,
          F ((k1 * (q : ℤ) + (b.1 : ℤ)), (k2 * (q : ℤ) + (b.2 : ℤ))) := by
  rw [show ∑' p : ℤ × ℤ, F p
        = ∑' r : (Fin q × Fin q) × (ℤ × ℤ), F ((eps q).symm r) from
      ((Equiv.tsum_eq (eps q).symm F).symm)]
  have hFs : Summable (fun r : (Fin q × Fin q) × (ℤ × ℤ) => F ((eps q).symm r)) :=
    ((eps q).symm).summable_iff.mpr hF
  rw [Summable.tsum_prod' hFs (fun b => Summable.prod_factor hFs b)]
  rw [tsum_fintype]
  refine Finset.sum_congr rfl ?_
  intro b hb
  have hbc : Summable (fun c : ℤ × ℤ => F ((eps q).symm (b, c))) := Summable.prod_factor hFs b
  rw [Summable.tsum_prod' hbc (fun k1 => Summable.prod_factor hbc k1)]
  refine tsum_congr (fun k1 => tsum_congr (fun k2 => ?_))
  rw [eps_symm_apply]

/-! ### The weight `(1 + t²/H²)⁻¹` -/

/-- The smoothing weight `(1 + t²/H²)⁻¹`. -/
def Wt (H : ℝ) (t : ℤ) : ℝ := (1 + (t:ℝ)^2/H^2)⁻¹

lemma summable_Wt (H : ℝ) (hH : 1 ≤ H) : Summable (Wt H) := by
  change Summable (fun t : ℤ => (1 + (t:ℝ)^2/H^2)⁻¹)
  have hHpos : 0 < H := lt_of_lt_of_le one_pos hH
  have hbase : Summable (fun t : ℤ => (1 + (t:ℝ)^2)⁻¹) := by
    apply Summable.of_nonneg_of_le (f := fun t : ℤ => 2 * ((t:ℝ)^2)⁻¹ + (if t = 0 then (1:ℝ) else 0))
    · intro t; positivity
    · intro t
      by_cases h : t = 0
      · simp [h]
      · rw [if_neg h]
        have : (1 + (t:ℝ)^2)⁻¹ ≤ 2 * ((t:ℝ)^2)⁻¹ := by
          rw [show (2:ℝ) * ((t:ℝ)^2)⁻¹ = ((t:ℝ)^2/2)⁻¹ by field_simp]
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          linarith [sq_nonneg (t:ℝ)]
        linarith [this]
    · apply Summable.add
      · have h1 : Summable (fun n : ℤ => 1 / (n:ℝ)^2) :=
          Real.summable_one_div_int_pow.mpr (by norm_num)
        have h2 : Summable (fun n : ℤ => ((n:ℝ)^2)⁻¹) := by simpa [one_div] using h1
        exact h2.mul_left 2
      · apply summable_of_ne_finset_zero (s := {0})
        intro b hb
        simp only [Finset.mem_singleton] at hb
        simp [hb]
  apply Summable.of_nonneg_of_le (f := fun t : ℤ => H^2 * (1 + (t:ℝ)^2)⁻¹)
  · intro t; positivity
  · intro t
    have hH2 : (1:ℝ) ≤ H^2 := by nlinarith [hH]
    have hid : 1 + (t:ℝ)^2/H^2 = (H^2 + (t:ℝ)^2)/H^2 := by field_simp
    rw [hid, inv_div, show H^2 * (1 + (t:ℝ)^2)⁻¹ = H^2/(1 + (t:ℝ)^2) from by field_simp]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  · exact hbase.mul_left (H^2)

lemma Wt_nonneg (H : ℝ) (hH : 1 ≤ H) (t : ℤ) : 0 ≤ Wt H t := by
  change 0 ≤ (1 + (t:ℝ)^2/H^2)⁻¹
  positivity

lemma Wt_le_one (H : ℝ) (hH : 1 ≤ H) (t : ℤ) : Wt H t ≤ 1 := by
  change (1 + (t:ℝ)^2/H^2)⁻¹ ≤ 1
  have hHpos : 0 < H := lt_of_lt_of_le one_pos hH
  rw [inv_le_one₀ (by positivity)]
  have := div_nonneg (sq_nonneg (t:ℝ)) (sq_nonneg H)
  linarith

/-- The weight of a single residue class: `S(γ) = Σ_k (1 + (kq+γ)²/H²)⁻¹`. -/
def Sv (H : ℝ) (q : ℕ) (i : ℤ) : ℝ := ∑' k : ℤ, Wt H (k * (q:ℤ) + i)

lemma Sv_nonneg (H : ℝ) (hH : 1 ≤ H) (q : ℕ) (i : ℤ) : 0 ≤ Sv H q i := by
  unfold Sv; exact tsum_nonneg (fun k => Wt_nonneg H hH _)

/-! ### The pair weight and its summability -/

def Wpair (H : ℝ) (a b : ℤ) (q : ℕ) (h1 h2 : ℤ) : ℝ :=
  Wt H h1 * Wt H h2 * (if (q:ℤ) ∣ a*h1^2 - b*h2^2 then (1:ℝ) else 0)

lemma ind_nonneg (q : ℕ) (a b h1 h2 : ℤ) :
    0 ≤ (if (q:ℤ) ∣ a*h1^2 - b*h2^2 then (1:ℝ) else 0) := by
  split_ifs <;> norm_num

lemma ind_le_one (q : ℕ) (a b h1 h2 : ℤ) :
    (if (q:ℤ) ∣ a*h1^2 - b*h2^2 then (1:ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

lemma Wpair_nonneg (H : ℝ) (hH : 1 ≤ H) (a b : ℤ) (q : ℕ) (h1 h2 : ℤ) :
    0 ≤ Wpair H a b q h1 h2 := by
  rw [Wpair]
  exact mul_nonneg (mul_nonneg (Wt_nonneg H hH h1) (Wt_nonneg H hH h2)) (ind_nonneg q a b h1 h2)

lemma Wpair_le (H : ℝ) (hH : 1 ≤ H) (a b : ℤ) (q : ℕ) (h1 h2 : ℤ) :
    Wpair H a b q h1 h2 ≤ Wt H h1 * Wt H h2 := by
  rw [Wpair]
  calc Wt H h1 * Wt H h2 * (if (q:ℤ) ∣ a*h1^2 - b*h2^2 then (1:ℝ) else 0)
      ≤ Wt H h1 * Wt H h2 * 1 :=
        mul_le_mul_of_nonneg_left (ind_le_one q a b h1 h2)
          (mul_nonneg (Wt_nonneg H hH h1) (Wt_nonneg H hH h2))
    _ = Wt H h1 * Wt H h2 := mul_one _

lemma summable_Wpair (H : ℝ) (hH : 1 ≤ H) (a b : ℤ) (q : ℕ) :
    Summable (fun p : ℤ × ℤ => Wpair H a b q p.1 p.2) := by
  have hu := summable_Wt H hH
  have huu : Summable (fun p : ℤ × ℤ => Wt H p.1 * Wt H p.2) :=
    hu.mul_of_nonneg hu (Wt_nonneg H hH) (Wt_nonneg H hH)
  refine Summable.of_nonneg_of_le (f := fun p : ℤ × ℤ => Wt H p.1 * Wt H p.2) ?_ ?_ huu
  · intro p; exact Wpair_nonneg H hH a b q p.1 p.2
  · intro p; exact Wpair_le H hH a b q p.1 p.2

lemma summable_Wpair_fiber (H : ℝ) (hH : 1 ≤ H) (a b : ℤ) (q : ℕ) (h1 : ℤ) :
    Summable (fun h2 : ℤ => Wpair H a b q h1 h2) := by
  have hu := summable_Wt H hH
  have hb : Summable (fun h2 : ℤ => Wt H h1 * Wt H h2) := hu.mul_left (Wt H h1)
  refine Summable.of_nonneg_of_le (f := fun h2 : ℤ => Wt H h1 * Wt H h2) ?_ ?_ hb
  · intro h2; exact Wpair_nonneg H hH a b q h1 h2
  · intro h2; exact Wpair_le H hH a b q h1 h2

/-! ### Reduction of the congruence modulo `q` -/

lemma dvd_cong (q : ℕ) (a b : ℤ) (i1 i2 : ℤ) (k1 k2 : ℤ) :
    ((q:ℤ) ∣ a * (k1*(q:ℤ)+i1)^2 - b * (k2*(q:ℤ)+i2)^2) ↔ ((q:ℤ) ∣ a*i1^2 - b*i2^2) := by
  have h1 : (q:ℤ) ∣ (k1*(q:ℤ)+i1)^2 - i1^2 := by
    have h : (k1*(q:ℤ)+i1)^2 - i1^2 = (q:ℤ) * (2*k1*i1 + k1^2*(q:ℤ)) := by ring
    rw [h]; exact dvd_mul_right _ _
  have h2 : (q:ℤ) ∣ (k2*(q:ℤ)+i2)^2 - i2^2 := by
    have h : (k2*(q:ℤ)+i2)^2 - i2^2 = (q:ℤ) * (2*k2*i2 + k2^2*(q:ℤ)) := by ring
    rw [h]; exact dvd_mul_right _ _
  have hT : (q:ℤ) ∣ (a*(k1*(q:ℤ)+i1)^2 - b*(k2*(q:ℤ)+i2)^2) - (a*i1^2 - b*i2^2) := by
    have heq : a*(k1*(q:ℤ)+i1)^2 - b*(k2*(q:ℤ)+i2)^2 - (a*i1^2 - b*i2^2)
        = a*((k1*(q:ℤ)+i1)^2 - i1^2) - b*((k2*(q:ℤ)+i2)^2 - i2^2) := by ring
    rw [heq]
    exact dvd_sub (dvd_mul_of_dvd_right h1 a) (dvd_mul_of_dvd_right h2 b)
  constructor
  · intro h
    have h2 := dvd_sub h hT
    have heq : (a*(k1*(q:ℤ)+i1)^2 - b*(k2*(q:ℤ)+i2)^2)
          - ((a*(k1*(q:ℤ)+i1)^2 - b*(k2*(q:ℤ)+i2)^2) - (a*i1^2 - b*i2^2))
        = a*i1^2 - b*i2^2 := by ring
    rwa [heq] at h2
  · intro h
    have h2 := dvd_add h hT
    have heq : (a*i1^2 - b*i2^2)
          + ((a*(k1*(q:ℤ)+i1)^2 - b*(k2*(q:ℤ)+i2)^2) - (a*i1^2 - b*i2^2))
        = a*(k1*(q:ℤ)+i1)^2 - b*(k2*(q:ℤ)+i2)^2 := by ring
    rwa [heq] at h2

/-- The double sum over `k₁,k₂` of the pair weight factors as `c · S(γ₁) · S(γ₂)`. -/
lemma Wpair_double_tsum (H : ℝ) (a b : ℤ) (q : ℕ) (i1 i2 : ℤ) :
    ∑' k1 : ℤ, ∑' k2 : ℤ, Wpair H a b q (k1*(q:ℤ)+i1) (k2*(q:ℤ)+i2)
      = (if (q:ℤ) ∣ a*i1^2 - b*i2^2 then (1:ℝ) else 0) * Sv H q i1 * Sv H q i2 := by
  have hpt : ∀ k1 k2 : ℤ, Wpair H a b q (k1*(q:ℤ)+i1) (k2*(q:ℤ)+i2)
      = Wt H (k1*(q:ℤ)+i1) * Wt H (k2*(q:ℤ)+i2)
          * (if (q:ℤ) ∣ a*i1^2 - b*i2^2 then (1:ℝ) else 0) := by
    intro k1 k2
    rw [Wpair]
    by_cases h : (q:ℤ) ∣ a*(k1*(q:ℤ)+i1)^2 - b*(k2*(q:ℤ)+i2)^2
    · rw [if_pos h, if_pos ((dvd_cong q a b i1 i2 k1 k2).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((dvd_cong q a b i1 i2 k1 k2).mpr hh))]
  simp_rw [hpt]
  have h1 : ∀ k1 : ℤ, (∑' k2 : ℤ, Wt H (k1*(q:ℤ)+i1) * Wt H (k2*(q:ℤ)+i2)
        * (if (q:ℤ) ∣ a*i1^2 - b*i2^2 then (1:ℝ) else 0))
      = Wt H (k1*(q:ℤ)+i1)
        * (Sv H q i2 * (if (q:ℤ) ∣ a*i1^2 - b*i2^2 then (1:ℝ) else 0)) := by
    intro k1
    rw [show (fun k2 : ℤ => Wt H (k1*(q:ℤ)+i1) * Wt H (k2*(q:ℤ)+i2)
          * (if (q:ℤ) ∣ a*i1^2 - b*i2^2 then (1:ℝ) else 0))
        = (fun k2 : ℤ => Wt H (k1*(q:ℤ)+i1) * (Wt H (k2*(q:ℤ)+i2)
          * (if (q:ℤ) ∣ a*i1^2 - b*i2^2 then (1:ℝ) else 0))) from by funext k2; ring]
    rw [tsum_mul_left]
    congr 1
    rw [tsum_mul_right]
    rfl
  rw [tsum_congr h1]
  rw [tsum_mul_right]
  rw [show Sv H q i1 = ∑' k1 : ℤ, Wt H (k1*(q:ℤ)+i1) from rfl]
  ring

/-! ### The tail bound `Σ_{n≥N} 1/n² ≤ 2/N` -/

lemma tsum_inv_sq_shift_le (K : ℕ) (hK : 1 ≤ K) :
    ∑' j : ℕ, (1:ℝ) / ((j:ℝ) + K)^2 ≤ 2 / (K:ℝ) := by
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have htel : HasSum (fun j : ℕ => (1:ℝ)/((j:ℝ)+K) - 1/((j:ℝ)+K+1)) (1/(K:ℝ)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hfun : (fun n : ℕ => ∑ i ∈ Finset.range n, ((1:ℝ)/((i:ℝ)+K) - 1/((i:ℝ)+K+1)))
          = fun n : ℕ => (1:ℝ)/(K:ℝ) - 1/((n:ℝ)+K) := by
        funext n
        have heq : (fun i : ℕ => (1:ℝ)/((i:ℝ)+K) - 1/((i:ℝ)+K+1))
            = (fun i : ℕ => (fun i : ℕ => (1:ℝ)/((i:ℝ)+K)) i
                - (fun i : ℕ => (1:ℝ)/((i:ℝ)+K)) (i+1)) := by
          funext i; push_cast; ring
        rw [heq, Finset.sum_range_sub']
        simp
      rw [hfun]
      have hlim : Filter.Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+K)) Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ => (1:ℝ)/(((n+K:ℕ):ℝ))) Filter.atTop (nhds 0) :=
          (Filter.tendsto_add_atTop_iff_nat K).mpr tendsto_one_div_atTop_nhds_zero_nat
        have h2 : (fun n : ℕ => (1:ℝ)/(((n+K:ℕ):ℝ))) = fun n : ℕ => (1:ℝ)/((n:ℝ)+K) := by
          funext n; push_cast; ring
        rwa [h2] at h1
      have hconst : Filter.Tendsto (fun _ : ℕ => (1:ℝ)/(K:ℝ)) Filter.atTop (nhds (1/(K:ℝ))) :=
        tendsto_const_nhds
      have hh := hconst.sub hlim
      simpa using hh
    · intro j
      apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le (by positivity)
      linarith [Nat.cast_nonneg (α := ℝ) j]
  have hg : Summable (fun j : ℕ => (1:ℝ)/((j:ℝ)+K) - 1/((j:ℝ)+K+1)) := htel.summable
  have hf : Summable (fun j : ℕ => (1:ℝ)/((j:ℝ)+K)^2) := by
    have := (summable_nat_add_iff K).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : (1:ℕ) < 2))
    refine this.congr (fun j => ?_)
    push_cast; rw [one_div]
  have hkey : ∑' j : ℕ, (1:ℝ)/((j:ℝ)+K)^2
      ≤ ∑' j : ℕ, 2*((1:ℝ)/((j:ℝ)+K) - 1/((j:ℝ)+K+1)) := by
    refine Summable.tsum_le_tsum (fun j => ?_) hf (hg.mul_left 2)
    have hj1 : (0:ℝ) < (j:ℝ)+K := by positivity
    have hjK : (1:ℝ) ≤ (j:ℝ)+K := by
      have : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
      linarith [Nat.cast_nonneg (α:=ℝ) j]
    have hden : (0:ℝ) < ((j:ℝ)+K) * ((j:ℝ)+K+1) := by positivity
    have hdiff : (1:ℝ)/((j:ℝ)+K) - 1/((j:ℝ)+K+1) = 1/(((j:ℝ)+K)*((j:ℝ)+K+1)) := by
      field_simp; ring
    rw [hdiff, show (2:ℝ) * (1/(((j:ℝ)+K)*((j:ℝ)+K+1)))
          = 2/(((j:ℝ)+K)*((j:ℝ)+K+1)) by ring]
    rw [div_le_div_iff₀ (by positivity) hden]
    nlinarith [hjK, sq_nonneg ((j:ℝ)+K-1)]
  rw [tsum_mul_left, htel.tsum_eq] at hkey
  calc ∑' j : ℕ, (1:ℝ)/((j:ℝ)+K)^2 ≤ 2*(1/(K:ℝ)) := hkey
    _ = 2/(K:ℝ) := by ring

/-! ### The per-class bound `S(γ) ≤ 2 + 6H/q` -/

lemma swt_le (H : ℝ) (hH : 1 ≤ H) (q : ℕ) (hq : 1 ≤ q) (i : ℤ) (hi0 : 0 ≤ i)
    (hiq : i ≤ (q : ℤ) - 1) :
    ∑' k : ℤ, (1 + (((k * (q : ℤ) + i : ℤ)) : ℝ) ^ 2 / H ^ 2)⁻¹ ≤ 2 + 6 * H / (q : ℝ) := by
  have hHpos : 0 < H := lt_of_lt_of_le one_pos hH
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hqZ : (q:ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (by omega : 0 < q))
  have hanti : ∀ x y : ℝ, 0 ≤ x → x ≤ y →
      (1 + y^2/H^2)⁻¹ ≤ (1 + x^2/H^2)⁻¹ := by
    intro x y hx hxy
    have hxy2 : x^2 ≤ y^2 := by nlinarith
    have hH2 : (0:ℝ) < H^2 := by positivity
    have hd : x^2/H^2 ≤ y^2/H^2 := div_le_div_of_nonneg_right hxy2 (le_of_lt hH2)
    have hy' : 0 < 1 + y^2/H^2 := by positivity
    have hx' : 0 < 1 + x^2/H^2 := by positivity
    exact (inv_le_inv₀ hy' hx').mpr (by linarith)
  set f : ℤ → ℝ := fun t => (1 + (((t * (q:ℤ) + i : ℤ)) : ℝ)^2 / H^2)⁻¹ with hfdef
  set g : ℕ → ℝ := fun n => (1 + ((((n:ℤ) * (q:ℤ) : ℤ)) : ℝ)^2 / H^2)⁻¹ with hgdef
  change ∑' k : ℤ, f k ≤ 2 + 6 * H / (q:ℝ)
  have hf : Summable f := by
    have hinj : Function.Injective (fun t : ℤ => t*(q:ℤ)+i) := by
      intro a b h
      have : a*(q:ℤ) = b*(q:ℤ) := by linarith [h]
      exact mul_right_cancel₀ hqZ this
    have h := (summable_Wt H hH).comp_injective hinj
    exact h.congr (fun t => by rw [hfdef]; rfl)
  have hg : Summable g := by
    have hinj : Function.Injective (fun n : ℕ => (n:ℤ)*(q:ℤ)) := by
      intro a b h
      have : (a:ℤ) = (b:ℤ) := mul_right_cancel₀ hqZ h
      exact_mod_cast this
    have h := (summable_Wt H hH).comp_injective hinj
    exact h.congr (fun n => by rw [hgdef]; rfl)
  have hpt : ∀ n : ℕ, f n + f (-(n+1)) ≤ 2 * g n := by
    intro n
    have h1 : f n ≤ g n := by
      rw [hfdef, hgdef]; simp only
      have hc1 : (((↑n) * (q:ℤ) + i : ℤ) : ℝ) = (n:ℝ)*(q:ℝ) + (i:ℝ) := by push_cast; ring
      have hc2 : ((((n:ℤ)) * (q:ℤ) : ℤ) : ℝ) = (n:ℝ)*(q:ℝ) := by push_cast; ring
      rw [hc1, hc2]
      apply hanti
      · positivity
      · have : (0:ℝ) ≤ (i:ℝ) := by exact_mod_cast hi0
        linarith
    have h2 : f (-(n+1)) ≤ g n := by
      rw [hfdef, hgdef]; simp only
      have hc1 : (((-(↑n+1)) * (q:ℤ) + i : ℤ) : ℝ) = -((n:ℝ)+1)*(q:ℝ) + (i:ℝ) := by push_cast; ring
      have hc2 : ((((n:ℤ)) * (q:ℤ) : ℤ) : ℝ) = (n:ℝ)*(q:ℝ) := by push_cast; ring
      rw [hc1, hc2]
      have hsq : (-((n:ℝ)+1)*(q:ℝ) + (i:ℝ))^2 = (((n:ℝ)+1)*(q:ℝ) - (i:ℝ))^2 := by ring
      rw [hsq]
      apply hanti
      · positivity
      · have hi1 : (i:ℝ) ≤ (q:ℝ) - 1 := by exact_mod_cast hiq
        have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        nlinarith
    linarith
  have hbound1 : ∑' n : ℕ, (f n + f (-(n+1))) ≤ ∑' n : ℕ, 2 * g n := by
    refine Summable.tsum_le_tsum hpt ?_ (hg.mul_left 2)
    refine (hf.comp_injective Nat.cast_injective).add ?_
    refine hf.comp_injective ?_
    intro a b hab
    have h : (a:ℤ) + 1 = (b:ℤ) + 1 := by linarith [hab]
    have h2 : (a:ℤ) = (b:ℤ) := by linarith
    exact_mod_cast h2
  have hcalc : ∑' k : ℤ, f k ≤ 2 * ∑' n : ℕ, g n := by
    rw [← tsum_nat_add_neg_add_one hf]
    rw [← tsum_mul_left]
    exact hbound1
  set N : ℕ := ⌈H/(q:ℝ)⌉₊ with hNdef
  have hNge : H/(q:ℝ) ≤ (N:ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hNlt : (N:ℝ) < H/(q:ℝ) + 1 := by
    rw [hNdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hN1 : 1 ≤ N := by
    have h : (0:ℝ) < H/(q:ℝ) := by positivity
    rw [hNdef]; exact Nat.one_le_ceil_iff.mpr h
  have hsplit : ∑' n : ℕ, g n = (∑ k ∈ Finset.range N, g k) + ∑' n : ℕ, g (n + N) :=
    (Summable.sum_add_tsum_nat_add N hg).symm
  have hpart1 : (∑ k ∈ Finset.range N, g k) ≤ (N:ℝ) := by
    calc ∑ k ∈ Finset.range N, g k ≤ ∑ k ∈ Finset.range N, (1:ℝ) := by
          apply Finset.sum_le_sum
          intro k _
          rw [hgdef]; simp only
          have hX : (0:ℝ) ≤ (↑(↑k * (q:ℤ)) : ℝ)^2/H^2 := by positivity
          rw [inv_le_one₀ (by positivity)]
          linarith
      _ = (N:ℝ) := by simp
  have hpart2 : ∑' n : ℕ, g (n + N) ≤ H^2/(q:ℝ)^2 * (2/(N:ℝ)) := by
    have hRsum : Summable (fun n : ℕ => H^2/(q:ℝ)^2 * (1/(((n:ℝ)+N))^2)) := by
      have h1 : Summable (fun n : ℕ => (1:ℝ)/(((n:ℝ)+N))^2) := by
        have := (summable_nat_add_iff N).mpr (Real.summable_nat_pow_inv.mpr (by norm_num : (1:ℕ)<2))
        refine this.congr (fun j => ?_); push_cast; rw [one_div]
      exact h1.mul_left _
    have hLsum : Summable (fun n : ℕ => g (n + N)) := hg.comp_injective (fun a b h => by omega)
    have hpt2 : ∀ n : ℕ, g (n + N) ≤ H^2/(q:ℝ)^2 * (1/(((n:ℝ)+N))^2) := by
      intro n
      rw [hgdef]; simp only
      have hc : ((↑(↑(n+N) * (q:ℤ)) : ℤ) : ℝ) = ((n:ℝ)+(N:ℝ)) * (q:ℝ) := by push_cast; ring
      rw [hc]
      have hX : (0:ℝ) < ((n:ℝ)+(N:ℝ)) * (q:ℝ) := by
        have h1 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        have h2 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
        positivity
      have hid : 1 + ((((n:ℝ)+(N:ℝ)) * (q:ℝ))^2)/H^2
          = (H^2 + (((n:ℝ)+(N:ℝ)) * (q:ℝ))^2)/H^2 := by field_simp
      rw [hid, inv_div]
      rw [show H^2/(q:ℝ)^2 * (1/(((n:ℝ)+N))^2) = H^2/(((n:ℝ)+N)^2 * (q:ℝ)^2) by field_simp]
      rw [show (((n:ℝ)+(N:ℝ)) * (q:ℝ))^2 = ((n:ℝ)+N)^2 * (q:ℝ)^2 by ring]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [sq_nonneg H]
    have h3 := Summable.tsum_le_tsum hpt2 hLsum hRsum
    rw [tsum_mul_left] at h3
    refine h3.trans ?_
    have hb : ∑' n : ℕ, (1:ℝ)/(((n:ℝ)+N))^2 ≤ 2/(N:ℝ) := tsum_inv_sq_shift_le N hN1
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have hgn : ∑' n : ℕ, g n ≤ 3 * H / (q:ℝ) + 1 := by
    rw [hsplit]
    have hNle : (N:ℝ) ≤ H/(q:ℝ) + 1 := le_of_lt hNlt
    have hHN : H ≤ (q:ℝ) * (N:ℝ) := by
      have := (div_le_iff₀ hqpos).mp hNge
      linarith
    have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le (by positivity : (0:ℝ) < H/(q:ℝ)) hNge
    have hbd : H^2/(q:ℝ)^2 * (2/(N:ℝ)) ≤ 2*H/(q:ℝ) := by
      have hqN : (0:ℝ) < (q:ℝ)^2 * (N:ℝ) := by positivity
      rw [div_mul_div_comm]
      rw [show H^2 * 2 = 2*H^2 by ring]
      rw [div_le_iff₀ hqN]
      have heq : (2:ℝ)*H/(q:ℝ) * ((q:ℝ)^2*(N:ℝ)) = 2*H*(q:ℝ)*(N:ℝ) := by field_simp
      rw [heq]
      nlinarith [mul_le_mul_of_nonneg_right hHN (le_of_lt hHpos)]
    calc (∑ k ∈ Finset.range N, g k) + ∑' n : ℕ, g (n + N)
        ≤ (N:ℝ) + H^2/(q:ℝ)^2 * (2/(N:ℝ)) := add_le_add hpart1 hpart2
      _ ≤ (H/(q:ℝ) + 1) + 2*H/(q:ℝ) := by linarith
      _ = 3 * H / (q:ℝ) + 1 := by ring
  calc ∑' k : ℤ, f k ≤ 2 * ∑' n : ℕ, g n := hcalc
    _ ≤ 2 * (3 * H / (q:ℝ) + 1) := by linarith
    _ = 2 + 6 * H / (q:ℝ) := by ring

/-! ### The residue count matches the statement's `Fin q`-free version -/

set_option maxHeartbeats 2000000 in
lemma card_sols_fin_icc (q : ℕ) (a b : ℤ) [NeZero q] :
    ((Finset.univ : Finset (Fin q × Fin q)).filter
        (fun p => (q : ℤ) ∣ a * (p.1 : ℤ) ^ 2 - b * (p.2 : ℤ) ^ 2)).card =
      (((Finset.Icc 0 ((q : ℤ) - 1)).product (Finset.Icc 0 ((q : ℤ) - 1))).filter
        (fun p : ℤ × ℤ => (q : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card := by
  refine Finset.card_bij
    (s := (Finset.univ : Finset (Fin q × Fin q)).filter
      (fun p => (q : ℤ) ∣ a * (p.1 : ℤ) ^ 2 - b * (p.2 : ℤ) ^ 2))
    (t := ((Finset.Icc 0 ((q : ℤ) - 1)).product (Finset.Icc 0 ((q : ℤ) - 1))).filter
      (fun p : ℤ × ℤ => (q : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2))
    (fun (p : Fin q × Fin q) (_ : p ∈ (Finset.univ : Finset (Fin q × Fin q)).filter
      (fun p => (q : ℤ) ∣ a * (p.1 : ℤ) ^ 2 - b * (p.2 : ℤ) ^ 2)) => ((p.1:ℤ), (p.2:ℤ))) ?_ ?_ ?_
  · intro p hp
    obtain ⟨-, hpdiv⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hpdiv⟩
    · exact Finset.mem_Icc.mpr ⟨Int.natCast_nonneg _, by
        have h : (p.1:ℤ) < (q:ℤ) := by exact_mod_cast p.1.isLt
        omega⟩
    · exact Finset.mem_Icc.mpr ⟨Int.natCast_nonneg _, by
        have h : (p.2:ℤ) < (q:ℤ) := by exact_mod_cast p.2.isLt
        omega⟩
  · intro p1 _ p2 _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext (by exact_mod_cast h.1)) (Fin.ext (by exact_mod_cast h.2))
  · intro p hp
    obtain ⟨hp', hpdiv⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp'
    obtain ⟨hp1a, hp1b⟩ := Finset.mem_Icc.mp hp1
    obtain ⟨hp2a, hp2b⟩ := Finset.mem_Icc.mp hp2
    have h1 : p.1.toNat < q := (Int.toNat_lt hp1a).mpr (by omega)
    have h2 : p.2.toNat < q := (Int.toNat_lt hp2a).mpr (by omega)
    refine ⟨(⟨p.1.toNat, h1⟩, ⟨p.2.toNat, h2⟩), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      push_cast
      rw [Int.toNat_of_nonneg hp1a, Int.toNat_of_nonneg hp2a]
      exact hpdiv
    · refine Prod.ext ?_ ?_
      · exact Int.toNat_of_nonneg hp1a
      · exact Int.toNat_of_nonneg hp2a

theorem sum_weight_sqcong (H : ℝ) (hH : 1 ≤ H) (a b : ℤ) (q : ℕ) (hq : 1 ≤ q) :
    (∑' h1 : ℤ, ∑' h2 : ℤ, (1 + (h1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * (if (q : ℤ) ∣ a * h1 ^ 2 - b * h2 ^ 2 then (1 : ℝ) else 0))
      ≤ 64 * (H ^ 2 / (q : ℝ) ^ 2 + 1)
          * ↑(((Finset.Icc 0 ((q : ℤ) - 1)).product (Finset.Icc 0 ((q : ℤ) - 1))).filter
              (fun p : ℤ × ℤ => (q : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card := by
  haveI : NeZero q := ⟨by omega⟩
  change (∑' h1 : ℤ, ∑' h2 : ℤ, Wpair H a b q h1 h2) ≤
      64 * (H ^ 2 / (q : ℝ) ^ 2 + 1)
          * ↑(((Finset.Icc 0 ((q : ℤ) - 1)).product (Finset.Icc 0 ((q : ℤ) - 1))).filter
              (fun p : ℤ × ℤ => (q : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card
  rw [(Summable.tsum_prod' (summable_Wpair H hH a b q)
        (fun h1 => summable_Wpair_fiber H hH a b q h1)).symm]
  rw [tsum_pair_decomp q (fun p : ℤ × ℤ => Wpair H a b q p.1 p.2) (summable_Wpair H hH a b q)]
  rw [Finset.sum_congr rfl (fun (w : Fin q × Fin q) _ =>
    Wpair_double_tsum H a b q (w.1:ℤ) (w.2:ℤ))]
  have hM0 : (0:ℝ) ≤ 2 + 6*H/(q:ℝ) := by positivity
  have hMbd : ∀ i : Fin q, Sv H q (i:ℤ) ≤ 2 + 6*H/(q:ℝ) := by
    intro i
    have hi0 : (0:ℤ) ≤ (i:ℤ) := Int.natCast_nonneg _
    have hiq : (i:ℤ) ≤ (q:ℤ) - 1 := by
      have h : (i:ℤ) < (q:ℤ) := by exact_mod_cast i.isLt
      omega
    exact swt_le H hH q hq (i:ℤ) hi0 hiq
  have hSnn : ∀ i : Fin q, 0 ≤ Sv H q (i:ℤ) := fun i => Sv_nonneg H hH q (i:ℤ)
  have hsumC : (∑ w : Fin q × Fin q, (if (q:ℤ) ∣ a*(w.1:ℤ)^2 - b*(w.2:ℤ)^2 then (1:ℝ) else 0)
        * Sv H q (w.1:ℤ) * Sv H q (w.2:ℤ))
      = ∑ w ∈ (Finset.univ.filter (fun w : Fin q × Fin q => (q:ℤ) ∣ a*(w.1:ℤ)^2 - b*(w.2:ℤ)^2)),
          Sv H q (w.1:ℤ) * Sv H q (w.2:ℤ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : (q:ℤ) ∣ a*(w.1:ℤ)^2 - b*(w.2:ℤ)^2 <;> simp [h]
  rw [hsumC]
  calc ∑ w ∈ (Finset.univ.filter (fun w : Fin q × Fin q => (q:ℤ) ∣ a*(w.1:ℤ)^2 - b*(w.2:ℤ)^2)),
          Sv H q (w.1:ℤ) * Sv H q (w.2:ℤ)
      ≤ ∑ w ∈ (Finset.univ.filter (fun w : Fin q × Fin q => (q:ℤ) ∣ a*(w.1:ℤ)^2 - b*(w.2:ℤ)^2)),
          (2 + 6*H/(q:ℝ)) * (2 + 6*H/(q:ℝ)) := by
        apply Finset.sum_le_sum
        intro w _
        exact mul_le_mul (hMbd w.1) (hMbd w.2) (hSnn w.2) hM0
    _ = (2 + 6*H/(q:ℝ)) * (2 + 6*H/(q:ℝ))
          * ↑((Finset.univ.filter
              (fun w : Fin q × Fin q => (q:ℤ) ∣ a*(w.1:ℤ)^2 - b*(w.2:ℤ)^2)).card) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 64 * (H^2/(q:ℝ)^2 + 1)
          * ↑((Finset.univ.filter
              (fun w : Fin q × Fin q => (q:ℤ) ∣ a*(w.1:ℤ)^2 - b*(w.2:ℤ)^2)).card) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        have hx : H^2/(q:ℝ)^2 = (H/(q:ℝ))^2 := by rw [div_pow]
        rw [hx]
        have he : (2 + 6 * H / (q:ℝ)) * (2 + 6 * H / (q:ℝ)) = (2 + 6*(H/(q:ℝ)))^2 := by ring
        rw [he]
        nlinarith [sq_nonneg (H/(q:ℝ) - 3/7)]
    _ = 64 * (H^2/(q:ℝ)^2 + 1)
          * ↑(((Finset.Icc 0 ((q : ℤ) - 1)).product (Finset.Icc 0 ((q : ℤ) - 1))).filter
              (fun p : ℤ × ℤ => (q : ℤ) ∣ a * p.1 ^ 2 - b * p.2 ^ 2)).card := by
        rw [card_sols_fin_icc q a b]

end

end Work.FIArea2
