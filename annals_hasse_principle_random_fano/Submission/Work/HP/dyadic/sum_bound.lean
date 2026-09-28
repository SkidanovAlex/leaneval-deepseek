import Mathlib
import Submission.Work.HP.DyadicDefs
import Submission.Work.HP.dyadic.SumDefs
import Submission.Work.HP.dyadic.pow_bigE_eq

set_option autoImplicit false

namespace Work.HP.dyadic

open Finset

noncomputable section

/-! ## Elementary one-variable estimates -/

/-- For `0 < q ≤ 1` powers are antitone in the exponent. -/
lemma pow_le_pow_of_le_one {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) {k l : ℕ} (h : k ≤ l) :
    q ^ l ≤ q ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have hq : q ^ d ≤ 1 := pow_le_one₀ h0 h1
  have hk : 0 ≤ q ^ k := pow_nonneg h0 k
  nlinarith

/-- A truncated geometric series with ratio in `[0,1)` is bounded by the full series. -/
lemma geom_range_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (L : ℕ) :
    ∑ m ∈ Finset.range L, x ^ m ≤ (1 - x)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hkey : (∑ m ∈ Finset.range L, x ^ m) * (1 - x) = 1 - x ^ L := by
    have h := geom_sum_mul x L
    ring_nf at h ⊢
    linarith
  have hle : (∑ m ∈ Finset.range L, x ^ m) * (1 - x) ≤ 1 := by
    rw [hkey]
    have := pow_nonneg hx0 L
    linarith
  calc ∑ m ∈ Finset.range L, x ^ m
      = (∑ m ∈ Finset.range L, x ^ m) * (1 - x) / (1 - x) :=
        (mul_div_cancel_right₀ _ (ne_of_gt hpos)).symm
    _ ≤ 1 / (1 - x) := div_le_div_of_nonneg_right hle (le_of_lt hpos)
    _ = (1 - x)⁻¹ := by rw [one_div]

/-- `(1/2)^k ≤ 1/2` for `k ≥ 1`. -/
lemma half_pow_le_half {k : ℕ} (hk : 1 ≤ k) : (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1) hk
  simpa using this

/-- Summing `q ^ (g c)` over distinct values of `g` is bounded by the full geometric series. -/
lemma sum_pow_image_le {q : ℝ} (hq : 0 ≤ q) {S : Finset ℕ} {g : ℕ → ℕ} {K : ℕ}
    (hinj : Set.InjOn g (S : Set ℕ)) (hsub : S.image g ⊆ Finset.range (K + 1)) :
    ∑ c ∈ S, q ^ (g c) ≤ ∑ m ∈ Finset.range (K + 1), q ^ m := by
  rw [← Finset.sum_image hinj (f := fun m => q ^ m)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => pow_nonneg hq m)

/-- A product inequality for nonnegative reals. -/
lemma prod_le_prod_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have h0a : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
      have hfs : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      have hga : 0 ≤ g a := le_trans h0a (h a (Finset.mem_insert_self a s))
      have h1 := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact mul_le_mul (h a (Finset.mem_insert_self a s)) h1 hfs hga

/-! ## Splitting a sum over `Fin r` into head and tail -/

/-- A sum over `Fin r` splits into a sum over the first three coordinates and a sum over the rest. -/
lemma sum_fin_split (r : ℕ) (hr : 3 ≤ r) {α : Type*} [AddCommMonoid α] (f : Fin r → α) :
    (∑ i : Fin r, f i)
      = (∑ i : Fin 3, f (headIdx r hr i)) + ∑ j : Fin (r - 3), f (tailIdx r hr j) := by
  set φ : ℕ → Fin r := fun k => ⟨k % r, Nat.mod_lt k (by omega)⟩ with hφdef
  have hφ : ∀ i : Fin r, φ (i : ℕ) = i := by
    intro i
    refine Fin.ext ?_
    simp only [hφdef]
    rw [Nat.mod_eq_of_lt i.isLt]
  have hφ3 : ∀ i : Fin 3, φ (i : ℕ) = headIdx r hr i := by
    intro i
    refine Fin.ext ?_
    simp only [hφdef, headIdx]
    rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have hφt : ∀ j : Fin (r - 3), φ (3 + (j : ℕ)) = tailIdx r hr j := by
    intro j
    refine Fin.ext ?_
    simp only [hφdef, tailIdx]
    rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    omega
  calc (∑ i : Fin r, f i)
      = ∑ i : Fin r, f (φ (i : ℕ)) := Finset.sum_congr rfl (fun i _ => by rw [hφ i])
    _ = ∑ k ∈ Finset.range r, f (φ k) := Fin.sum_univ_eq_sum_range (fun k => f (φ k)) r
    _ = ∑ k ∈ Finset.range (3 + (r - 3)), f (φ k) := by rw [show 3 + (r - 3) = r by omega]
    _ = (∑ k ∈ Finset.range 3, f (φ k)) + ∑ k ∈ Finset.range (r - 3), f (φ (3 + k)) :=
        Finset.sum_range_add (fun k => f (φ k)) 3 (r - 3)
    _ = (∑ i : Fin 3, f (headIdx r hr i)) + ∑ j : Fin (r - 3), f (tailIdx r hr j) := by
        congr 1
        · rw [← Fin.sum_univ_eq_sum_range (fun k => f (φ k)) 3]
          exact Finset.sum_congr rfl (fun i _ => congrArg f (hφ3 i))
        · rw [← Fin.sum_univ_eq_sum_range (fun k => f (φ (3 + k))) (r - 3)]
          exact Finset.sum_congr rfl (fun j _ => congrArg f (hφt j))

/-- `sval` and `Pval` split along the head/tail decomposition. -/
theorem sval_Pval_split (r : ℕ) (hr : 3 ≤ r) (n : Fin r → ℕ) :
    sval r n = headW r hr (headPart r hr n) + tailW r hr (tailPart r hr n)
      ∧ Pval r n = tailD r hr (tailPart r hr n) := by
  constructor
  · rw [sval, headW, tailW, sum_fin_split r hr (fun i => n i * wval r i)]
    simp only [headPart_apply, tailPart_apply]
  · rw [Pval, tailD, sum_fin_split r hr (fun i => n i * dval r i)]
    simp only [headPart_apply, tailPart_apply]
    have hzero : (∑ i : Fin 3, n (headIdx r hr i) * dval r (headIdx r hr i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [dval_headIdx r hr i, mul_zero]
    rw [hzero, zero_add]

/-- Membership in the box splits along the head/tail decomposition. -/
theorem mem_piBox_split (r : ℕ) (hr : 3 ≤ r) (M : ℕ) (n : Fin r → ℕ) :
    n ∈ piBox r M ↔ headPart r hr n ∈ piBox 3 M ∧ tailPart r hr n ∈ piBox (r - 3) M := by
  simp only [piBox, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · intro h
    exact ⟨fun i => h (headIdx r hr i), fun j => h (tailIdx r hr j)⟩
  · rintro ⟨h1, h2⟩ i
    by_cases hi : (i : ℕ) < 3
    · have he : headIdx r hr ⟨(i : ℕ), hi⟩ = i := Fin.ext rfl
      rw [← he]
      exact h1 _
    · have he : tailIdx r hr ⟨(i : ℕ) - 3, by omega⟩ = i := by
        refine Fin.ext ?_
        simp only [tailIdx]
        omega
      rw [← he]
      exact h2 _

/-- The head and tail parts determine a vector. -/
lemma head_tail_injOn (r : ℕ) (hr : 3 ≤ r) (s : Finset (Fin r → ℕ)) :
    Set.InjOn (fun n : Fin r → ℕ => (headPart r hr n, tailPart r hr n))
      (s : Set (Fin r → ℕ)) := by
  intro n1 _ n2 _ heq
  have h1 : headPart r hr n1 = headPart r hr n2 := congrArg Prod.fst heq
  have h2 : tailPart r hr n1 = tailPart r hr n2 := congrArg Prod.snd heq
  funext i
  by_cases hi : (i : ℕ) < 3
  · have h := congrFun h1 ⟨(i : ℕ), hi⟩
    have he : headIdx r hr ⟨(i : ℕ), hi⟩ = i := Fin.ext rfl
    simpa [headPart, he] using h
  · have h := congrFun h2 ⟨(i : ℕ) - 3, by omega⟩
    have he : tailIdx r hr ⟨(i : ℕ) - 3, by omega⟩ = i := by
      refine Fin.ext ?_
      simp only [tailIdx]
      omega
    simpa [tailPart, he] using h

/-! ## The head bound -/

/-- The vector `(a,b,c)` as an element of `Fin 3 → ℕ`. -/
def vec3 (a b c : ℕ) : Fin 3 → ℕ
  | 0 => a
  | 1 => b
  | 2 => c

/-- Reindex a sum over the `Fin 3` box as a sum over the triple product. -/
lemma piBox3_sum (M : ℕ) (g : (Fin 3 → ℕ) → ℝ) :
    (∑ k ∈ piBox 3 M, g k)
      = ∑ p ∈ Finset.range (M + 1) ×ˢ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)),
          g (vec3 p.1 p.2.1 p.2.2) := by
  rw [Finset.sum_bij' (fun k _ => (k 0, (k 1, k 2))) (fun p _ => vec3 p.1 p.2.1 p.2.2)]
  · intro k hk
    simp only [piBox, Fintype.mem_piFinset, Finset.mem_range] at hk
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨hk 0, hk 1, hk 2⟩
  · intro p hp
    simp only [piBox, Fintype.mem_piFinset, Finset.mem_range]
    simp only [Finset.mem_product, Finset.mem_range] at hp
    intro i
    fin_cases i
    · simpa [vec3] using hp.1
    · simpa [vec3] using hp.2.1
    · simpa [vec3] using hp.2.2
  · intro k hk
    funext i
    fin_cases i <;> simp [vec3]
  · intro p hp
    simp [vec3]
  · intro k hk
    congr 1
    funext i
    fin_cases i <;> simp [vec3]

/-- The sum over the head, with the slack below a threshold `L`, is `≤ 2 (M+1)^2`. -/
lemma head_bound_fiber (M L : ℕ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 2) (w : Fin 3 → ℕ)
    (hw : ∀ i, 1 ≤ w i) :
    (∑ v ∈ (piBox 3 M).filter (fun v => (∑ i, v i * w i) ≤ L), q ^ (L - ∑ i, v i * w i))
      ≤ 2 * (M + 1) ^ 2 := by
  have hgeom : ∀ K : ℕ, (∑ m ∈ Finset.range (K + 1), q ^ m) ≤ 2 := by
    intro K
    refine le_trans (geom_range_le (le_of_lt hq0) (by linarith) (K + 1)) ?_
    have hle : (1 : ℝ) / 2 ≤ 1 - q := by linarith
    calc (1 - q)⁻¹ = 1 / (1 - q) := by rw [one_div]
      _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hle
      _ = 2 := by norm_num
  set F : (Fin 3 → ℕ) → ℝ :=
    fun k => if (∑ i, k i * w i) ≤ L then q ^ (L - ∑ i, k i * w i) else 0 with hF
  have hval : ∀ a b c : ℕ, F (vec3 a b c)
      = (if a * w 0 + b * w 1 + c * w 2 ≤ L
          then q ^ (L - (a * w 0 + b * w 1 + c * w 2)) else 0) := by
    intro a b c
    simp only [hF, Fin.sum_univ_three, vec3]
    exact if_congr Iff.rfl rfl rfl
  have hinner : ∀ a b : ℕ, a ∈ Finset.range (M + 1) → b ∈ Finset.range (M + 1) →
      (∑ c ∈ Finset.range (M + 1), (if a * w 0 + b * w 1 + c * w 2 ≤ L
          then q ^ (L - (a * w 0 + b * w 1 + c * w 2)) else 0))
        ≤ (if a * w 0 + b * w 1 ≤ L then 2 else 0) := by
    intro a b ha hb
    by_cases hab : a * w 0 + b * w 1 ≤ L
    · rw [if_pos hab]
      have heq : (∑ c ∈ Finset.range (M + 1), (if a * w 0 + b * w 1 + c * w 2 ≤ L
            then q ^ (L - (a * w 0 + b * w 1 + c * w 2)) else 0))
          = ∑ c ∈ (Finset.range (M + 1)).filter (fun c => c * w 2 ≤ L - (a * w 0 + b * w 1)),
              q ^ ((L - (a * w 0 + b * w 1)) - c * w 2) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun c hc => ?_)
        by_cases hc2 : c * w 2 ≤ L - (a * w 0 + b * w 1)
        · rw [if_pos hc2, if_pos (by omega : a * w 0 + b * w 1 + c * w 2 ≤ L)]
          congr 1
          omega
        · rw [if_neg hc2, if_neg (by omega : ¬ (a * w 0 + b * w 1 + c * w 2 ≤ L))]
      rw [heq]
      have hinj : Set.InjOn (fun c => (L - (a * w 0 + b * w 1)) - c * w 2)
          (((Finset.range (M + 1)).filter
            (fun c => c * w 2 ≤ L - (a * w 0 + b * w 1))) : Set ℕ) := by
        intro c1 hc1 c2 hc2 heq2
        have h1 : c1 * w 2 ≤ L - (a * w 0 + b * w 1) := (Finset.mem_filter.mp hc1).2
        have h2 : c2 * w 2 ≤ L - (a * w 0 + b * w 1) := (Finset.mem_filter.mp hc2).2
        have heq3 : (L - (a * w 0 + b * w 1)) - c1 * w 2
            = (L - (a * w 0 + b * w 1)) - c2 * w 2 := heq2
        have hmul : c1 * w 2 = c2 * w 2 := by omega
        have hw2 : 0 < w 2 := by have := hw 2; omega
        exact le_antisymm (Nat.le_of_mul_le_mul_right (le_of_eq hmul) hw2)
          (Nat.le_of_mul_le_mul_right (le_of_eq hmul.symm) hw2)
      have hsub : ((Finset.range (M + 1)).filter
            (fun c => c * w 2 ≤ L - (a * w 0 + b * w 1))).image
              (fun c => (L - (a * w 0 + b * w 1)) - c * w 2)
          ⊆ Finset.range (L - (a * w 0 + b * w 1) + 1) := by
        intro m hm
        rw [Finset.mem_image] at hm
        obtain ⟨c, hc, rfl⟩ := hm
        rw [Finset.mem_range]
        omega
      exact le_trans (sum_pow_image_le (le_of_lt hq0) hinj hsub) (hgeom _)
    · rw [if_neg hab]
      refine le_of_eq (Finset.sum_eq_zero (fun c hc => ?_))
      rw [if_neg (by omega : ¬ (a * w 0 + b * w 1 + c * w 2 ≤ L))]
  have hcount : (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
      (if a * w 0 + b * w 1 ≤ L then (1 : ℝ) else 0)) ≤ ((M + 1) * (M + 1) : ℕ) := by
    calc (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
          (if a * w 0 + b * w 1 ≤ L then (1 : ℝ) else 0))
        ≤ ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), (1 : ℝ) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => by split <;> norm_num))
      _ = ((M + 1) * (M + 1) : ℕ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_mul]
  have h2 : (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        (if a * w 0 + b * w 1 ≤ L then (2 : ℝ) else 0))
      = 2 * (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
          (if a * w 0 + b * w 1 ≤ L then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    split_ifs with h <;> norm_num
  have houter : (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
        (if a * w 0 + b * w 1 ≤ L then (2 : ℝ) else 0)) ≤ 2 * (M + 1) ^ 2 := by
    calc (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
          (if a * w 0 + b * w 1 ≤ L then (2 : ℝ) else 0))
        = 2 * (∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
            (if a * w 0 + b * w 1 ≤ L then (1 : ℝ) else 0)) := h2
      _ ≤ 2 * ((M + 1) * (M + 1) : ℕ) := mul_le_mul_of_nonneg_left hcount (by norm_num)
      _ = 2 * (M + 1) ^ 2 := by push_cast; ring
  have hstep : (∑ v ∈ (piBox 3 M).filter (fun v => (∑ i, v i * w i) ≤ L),
        q ^ (L - ∑ i, v i * w i))
      = ∑ p ∈ Finset.range (M + 1) ×ˢ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)),
          F (vec3 p.1 p.2.1 p.2.2) := by
    rw [Finset.sum_filter, piBox3_sum]
  have hnest : (∑ p ∈ Finset.range (M + 1) ×ˢ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)),
        F (vec3 p.1 p.2.1 p.2.2))
      = ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), ∑ c ∈ Finset.range (M + 1),
          F (vec3 a b c) := by
    have h2 : ∀ x : ℕ, (∑ y ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1),
          F (vec3 x y.1 y.2))
        = ∑ b ∈ Finset.range (M + 1), ∑ c ∈ Finset.range (M + 1), F (vec3 x b c) := by
      intro x
      rw [Finset.sum_product (f := fun z : ℕ × ℕ => F (vec3 x z.1 z.2))]
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => h2 a)
  rw [hstep, hnest]
  calc ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), ∑ c ∈ Finset.range (M + 1),
        F (vec3 a b c)
      = ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1), ∑ c ∈ Finset.range (M + 1),
          (if a * w 0 + b * w 1 + c * w 2 ≤ L
            then q ^ (L - (a * w 0 + b * w 1 + c * w 2)) else 0) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
          Finset.sum_congr rfl (fun c _ => hval a b c)))
    _ ≤ ∑ a ∈ Finset.range (M + 1), ∑ b ∈ Finset.range (M + 1),
          (if a * w 0 + b * w 1 ≤ L then (2 : ℝ) else 0) :=
        Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => hinner a b ha hb))
    _ ≤ 2 * (M + 1) ^ 2 := houter

/-! ## The tail bound -/

/-- The tail contribution is bounded by a constant depending only on the data. -/
lemma tail_bound (k : ℕ) (d : Fin k → ℕ) (hd : ∀ i, 1 ≤ d i) (M : ℕ) :
    (∑ u ∈ piBox k M, (1 / 2 : ℝ) ^ (∑ i, d i * u i))
      ≤ ∏ i, (1 - (1 / 2 : ℝ) ^ (d i))⁻¹ := by
  have hcongr : (∑ u ∈ piBox k M, (1 / 2 : ℝ) ^ (∑ i, d i * u i))
      = ∑ u ∈ piBox k M, ∏ i, ((1 / 2 : ℝ) ^ (d i)) ^ (u i) := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [pow_mul]
  rw [hcongr]
  change (∑ u ∈ Fintype.piFinset (fun _ : Fin k => Finset.range (M + 1)),
      ∏ i, ((1 / 2 : ℝ) ^ (d i)) ^ (u i)) ≤ ∏ i, (1 - (1 / 2 : ℝ) ^ (d i))⁻¹
  rw [Finset.sum_prod_piFinset]
  refine prod_le_prod_nonneg _ _ _ (fun i _ => ?_) (fun i _ => ?_)
  · positivity
  · refine geom_range_le (by positivity) ?_ (M + 1)
    have h2 : (1 / 2 : ℝ) ^ (d i) ≤ 1 / 2 := half_pow_le_half (hd i)
    linarith

/-! ## Splitting the constrained box sum -/

/-- The main estimate: the constrained sum is bounded by the head bound times the tail sum. -/
theorem sum_le_head_tail (r : ℕ) (hr : 3 ≤ r) (M : ℕ) (q : ℝ) (hq0 : 0 < q)
    (hq1 : q ≤ 1 / 2) :
    (∑ n ∈ (piBox r M).filter (fun n => sval r n ≤ M),
        q ^ (M - sval r n) * (1 / 2 : ℝ) ^ (Pval r n))
      ≤ 2 * (M + 1) ^ 2 * (∑ u ∈ piBox (r - 3) M, (1 / 2 : ℝ) ^ (tailD r hr u)) := by
  have hinj := head_tail_injOn r hr ((piBox r M).filter (fun n => sval r n ≤ M))
  have hsub : ((piBox r M).filter (fun n => sval r n ≤ M)).image
        (fun n => (headPart r hr n, tailPart r hr n))
      ⊆ ((piBox 3 M) ×ˢ piBox (r - 3) M).filter
          (fun p => headW r hr p.1 + tailW r hr p.2 ≤ M) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_product]
      exact (mem_piBox_split r hr M n).mp hn.1
    · have hsp := (sval_Pval_split r hr n).1
      have hsp' : headW r hr (headPart r hr n) + tailW r hr (tailPart r hr n) ≤ M := by
        rw [← hsp]; exact hn.2
      simpa using hsp'
  have hfiber : ∀ u ∈ piBox (r - 3) M,
      (∑ v ∈ piBox 3 M, (if headW r hr v + tailW r hr u ≤ M
            then q ^ (M - (headW r hr v + tailW r hr u)) * (1 / 2 : ℝ) ^ (tailD r hr u)
            else 0))
        ≤ (1 / 2 : ℝ) ^ (tailD r hr u) * (2 * (M + 1) ^ 2) := by
    intro u hu
    have hfac : (∑ v ∈ piBox 3 M, (if headW r hr v + tailW r hr u ≤ M
            then q ^ (M - (headW r hr v + tailW r hr u)) * (1 / 2 : ℝ) ^ (tailD r hr u)
            else 0))
        ≤ (1 / 2 : ℝ) ^ (tailD r hr u) *
            (∑ v ∈ (piBox 3 M).filter (fun v => headW r hr v ≤ M - tailW r hr u),
              q ^ ((M - tailW r hr u) - headW r hr v)) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_le_sum (fun v hv => ?_)
      by_cases hc : headW r hr v + tailW r hr u ≤ M
      · rw [if_pos hc, if_pos (by omega : headW r hr v ≤ M - tailW r hr u)]
        have hexp : M - (headW r hr v + tailW r hr u)
            = (M - tailW r hr u) - headW r hr v := by omega
        rw [hexp]
        exact le_of_eq (mul_comm _ _)
      · rw [if_neg hc]
        positivity
    calc (∑ v ∈ piBox 3 M, (if headW r hr v + tailW r hr u ≤ M
            then q ^ (M - (headW r hr v + tailW r hr u)) * (1 / 2 : ℝ) ^ (tailD r hr u)
            else 0))
        ≤ (1 / 2 : ℝ) ^ (tailD r hr u) *
            (∑ v ∈ (piBox 3 M).filter (fun v => headW r hr v ≤ M - tailW r hr u),
              q ^ ((M - tailW r hr u) - headW r hr v)) := hfac
      _ ≤ (1 / 2 : ℝ) ^ (tailD r hr u) * (2 * (M + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left
            (head_bound_fiber M (M - tailW r hr u) q hq0 hq1
              (fun i => wval r (headIdx r hr i)) (fun i => wval_pos (headIdx r hr i)))
            (by positivity)
  calc (∑ n ∈ (piBox r M).filter (fun n => sval r n ≤ M),
        q ^ (M - sval r n) * (1 / 2 : ℝ) ^ (Pval r n))
      = ∑ p ∈ ((piBox r M).filter (fun n => sval r n ≤ M)).image
            (fun n => (headPart r hr n, tailPart r hr n)),
          q ^ (M - (headW r hr p.1 + tailW r hr p.2)) * (1 / 2 : ℝ) ^ (tailD r hr p.2) := by
        rw [Finset.sum_image (f := fun p => q ^ (M - (headW r hr p.1 + tailW r hr p.2))
          * (1 / 2 : ℝ) ^ (tailD r hr p.2)) hinj]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        obtain ⟨hs, hp⟩ := sval_Pval_split r hr n
        rw [hs, hp]
    _ ≤ ∑ p ∈ ((piBox 3 M) ×ˢ piBox (r - 3) M).filter
            (fun p => headW r hr p.1 + tailW r hr p.2 ≤ M),
          q ^ (M - (headW r hr p.1 + tailW r hr p.2)) * (1 / 2 : ℝ) ^ (tailD r hr p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ = ∑ u ∈ piBox (r - 3) M, ∑ v ∈ piBox 3 M,
          (if headW r hr v + tailW r hr u ≤ M
            then q ^ (M - (headW r hr v + tailW r hr u)) * (1 / 2 : ℝ) ^ (tailD r hr u)
            else 0) := by
        rw [Finset.sum_filter, Finset.sum_product]
        exact Finset.sum_comm
    _ ≤ ∑ u ∈ piBox (r - 3) M, (1 / 2 : ℝ) ^ (tailD r hr u) * (2 * (M + 1) ^ 2) :=
        Finset.sum_le_sum hfiber
    _ = 2 * (M + 1) ^ 2 * (∑ u ∈ piBox (r - 3) M, (1 / 2 : ℝ) ^ (tailD r hr u)) := by
        rw [← Finset.sum_mul]
        ring

/-! ## The main theorem -/

theorem sum_bound (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      (∑ n ∈ Nset N r M, (2:ℝ) ^ (bigE' N r n)) ≤ C * 2 ^ ((N-2)*M) * (M+1)^2 := by
  set q : ℝ := (1 / 2 : ℝ) ^ (N - 2) with hqdef
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hqhalf : q ≤ 1 / 2 := by
    rw [hqdef]
    exact half_pow_le_half (by omega : 1 ≤ N - 2)
  set D : ℝ := ∏ j : Fin (r - 3), (1 - (1 / 2 : ℝ) ^ dval r (tailIdx r hr j))⁻¹ with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    refine Finset.prod_pos (fun j _ => ?_)
    have h2 : (1 / 2 : ℝ) ^ dval r (tailIdx r hr j) ≤ 1 / 2 :=
      half_pow_le_half (dval_tailIdx_le r hr j)
    exact inv_pos.mpr (by linarith)
  refine ⟨2 * D, by positivity, fun M => ?_⟩
  have hNset : Nset N r M = (piBox r M).filter (fun n => sval r n ≤ M) := rfl
  have hmain : (∑ n ∈ Nset N r M, (2:ℝ) ^ (bigE' N r n))
      = (2 : ℝ) ^ ((N - 2) * M) * ∑ n ∈ (piBox r M).filter (fun n => sval r n ≤ M),
            q ^ (M - sval r n) * (1 / 2 : ℝ) ^ (Pval r n) := by
    rw [hNset, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hs : sval r n ≤ M := (Finset.mem_filter.mp hn).2
    rw [pow_bigE_eq N r M hr hrN n hs]
    have h2 : (1 / 2 : ℝ) ^ ((N - 2) * (M - sval r n)) = q ^ (M - sval r n) := by
      rw [hqdef, pow_mul]
    rw [h2]
    ring
  rw [hmain]
  have hsplit := sum_le_head_tail r hr M q hq0 hqhalf
  have htail : (∑ u ∈ piBox (r - 3) M, (1 / 2 : ℝ) ^ (tailD r hr u)) ≤ D := by
    have h1 : (∑ u ∈ piBox (r - 3) M, (1 / 2 : ℝ) ^ (tailD r hr u))
        = ∑ u ∈ piBox (r - 3) M, (1 / 2 : ℝ) ^ (∑ j, dval r (tailIdx r hr j) * u j) := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      congr 1
      simp only [tailD]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [h1, hDdef]
    exact tail_bound (r - 3) (fun j => dval r (tailIdx r hr j))
      (fun j => dval_tailIdx_le r hr j) M
  calc (2 : ℝ) ^ ((N - 2) * M) * ∑ n ∈ (piBox r M).filter (fun n => sval r n ≤ M),
          q ^ (M - sval r n) * (1 / 2 : ℝ) ^ (Pval r n)
      ≤ (2 : ℝ) ^ ((N - 2) * M)
          * (2 * (M + 1) ^ 2 * (∑ u ∈ piBox (r - 3) M, (1 / 2 : ℝ) ^ (tailD r hr u))) :=
        mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ ≤ (2 : ℝ) ^ ((N - 2) * M) * (2 * (M + 1) ^ 2 * D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail (by positivity)) (by positivity)
    _ = (2 * D) * 2 ^ ((N - 2) * M) * (M + 1) ^ 2 := by ring

end

end Work.HP.dyadic
