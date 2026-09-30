import Mathlib
import Submission.Work.BMF.SD.separated_card_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

open Classical

namespace Work.BMF.SD

open Finset

/-! ## Counting integers in a real interval -/

/-- The number of integers lying in the real interval `[x,y]` is at most `y - x + 1`. -/
lemma card_int_Icc_le (x y : ℝ) (h : 0 ≤ y - x) :
    ((Finset.Icc ⌈x⌉ ⌊y⌋ : Finset ℤ).card : ℝ) ≤ y - x + 1 := by
  rcases lt_or_ge ⌊y⌋ ⌈x⌉ with h1 | h1
  · have hempty : (Finset.Icc ⌈x⌉ ⌊y⌋ : Finset ℤ) = ∅ :=
      Finset.Icc_eq_empty_iff.mpr (not_le.mpr h1)
    rw [hempty, Finset.card_empty, Nat.cast_zero]; linarith
  · rw [Int.card_Icc]
    have hnn : (0:ℤ) ≤ ⌊y⌋ + 1 - ⌈x⌉ := by omega
    have hcast : (((⌊y⌋ + 1 - ⌈x⌉).toNat : ℕ) : ℝ) = ((⌊y⌋ + 1 - ⌈x⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnn
    rw [hcast]; push_cast
    have h2 : (⌊y⌋ : ℝ) ≤ y := Int.floor_le y
    have h3 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
    linarith

/-! ## Counting near-integers along an arithmetic progression -/

/-- For `s ≠ 0`, the number of integers `t ∈ [0,T]` for which `a + s·t` lies within `ε` of an
integer is at most `(|s|·T + 2ε + 1)·(2ε/|s| + 1)`. -/
lemma count_affine (a s ε : ℝ) (hs : s ≠ 0) (hε : 0 < ε) (T : ℕ) :
    (((Finset.Icc (0:ℤ) (T:ℤ)).filter
        (fun (t : ℤ) => ∃ k : ℤ, |a + s * (t : ℝ) - (k : ℝ)| ≤ ε)).card : ℝ)
      ≤ (|s| * (T : ℝ) + 2 * ε + 1) * (2 * ε / |s| + 1) := by
  have hspos : 0 < |s| := abs_pos.mpr hs
  set x₀ : ℝ := min a (a + s * (T:ℝ)) with hx₀
  set x₁ : ℝ := max a (a + s * (T:ℝ)) with hx₁
  have hlen : x₁ - x₀ = |s| * (T:ℝ) := by
    rw [hx₀, hx₁, max_sub_min_eq_abs]
    have h1 : a + s*(T:ℝ) - a = s*(T:ℝ) := by ring
    rw [h1, abs_mul, Nat.abs_cast]
  set K : Finset ℤ := Finset.Icc ⌈x₀ - ε⌉ ⌊x₁ + ε⌋ with hK
  have hKcard : (K.card : ℝ) ≤ |s| * (T:ℝ) + 2*ε + 1 := by
    rw [hK]
    have hle0 : 0 ≤ (x₁ + ε) - (x₀ - ε) := by
      rw [show x₁ + ε - (x₀ - ε) = (x₁ - x₀) + 2*ε by ring, hlen]; positivity
    have h := card_int_Icc_le (x₀ - ε) (x₁ + ε) hle0
    calc ((Finset.Icc ⌈x₀ - ε⌉ ⌊x₁ + ε⌋ : Finset ℤ).card : ℝ)
        ≤ (x₁ + ε) - (x₀ - ε) + 1 := h
      _ = |s| * (T:ℝ) + 2*ε + 1 := by
          rw [show x₁ + ε - (x₀ - ε) + 1 = (x₁ - x₀) + 2*ε + 1 by ring, hlen]
  set G : Finset ℤ := (Finset.Icc (0:ℤ) (T:ℤ)).filter
      (fun (t : ℤ) => ∃ k : ℤ, |a + s*(t:ℝ) - (k:ℝ)| ≤ ε) with hG
  set Gk : ℤ → Finset ℤ := fun k => (Finset.Icc (0:ℤ) (T:ℤ)).filter
      (fun (t : ℤ) => |a + s*(t:ℝ) - (k:ℝ)| ≤ ε) with hGk
  have hperk : ∀ k : ℤ, ((Gk k).card : ℝ) ≤ 2*ε/|s| + 1 := by
    intro k
    set u : ℝ := ((k:ℝ) - ε - a)/s with hu
    set v : ℝ := ((k:ℝ) + ε - a)/s with hv
    have hu' : a + s*u = (k:ℝ) - ε := by rw [hu]; field_simp; ring
    have hv' : a + s*v = (k:ℝ) + ε := by rw [hv]; field_simp; ring
    have huv_len : max u v - min u v = 2*ε/|s| := by
      rw [max_sub_min_eq_abs, abs_sub_comm]
      have huv : u - v = -(2*ε/s) := by rw [hu, hv]; field_simp; ring
      rw [huv, abs_neg, abs_div, abs_of_pos (by linarith : (0:ℝ) < 2*ε)]
    have hsub : Gk k ⊆ (Finset.Icc ⌈min u v⌉ ⌊max u v⌋ : Finset ℤ) := by
      intro t ht
      rw [hGk] at ht
      obtain ⟨htR, hgood⟩ := Finset.mem_filter.mp ht
      rw [Finset.mem_Icc]
      rw [abs_le] at hgood
      obtain ⟨hlo, hhi⟩ := hgood
      have h1 : (k:ℝ) - ε ≤ a + s*(t:ℝ) := by linarith
      have h2 : a + s*(t:ℝ) ≤ (k:ℝ) + ε := by linarith
      constructor
      · rw [Int.ceil_le]
        rcases lt_or_gt_of_ne hs with hsneg | hspos'
        · have hsv : s * v = (k:ℝ) + ε - a := by linarith [hv']
          have hstep : s * (t:ℝ) ≤ s * v := by rw [hsv]; linarith
          have hle : v ≤ (t:ℝ) := (mul_le_mul_left_of_neg hsneg).mp hstep
          exact le_trans (min_le_right u v) hle
        · have hsu : s * u = (k:ℝ) - ε - a := by linarith [hu']
          have hstep : s * u ≤ s * (t:ℝ) := by rw [hsu]; linarith
          have hle : u ≤ (t:ℝ) := (mul_le_mul_iff_of_pos_left hspos').mp hstep
          exact le_trans (min_le_left u v) hle
      · rw [Int.le_floor]
        rcases lt_or_gt_of_ne hs with hsneg | hspos'
        · have hsu : s * u = (k:ℝ) - ε - a := by linarith [hu']
          have hstep : s * u ≤ s * (t:ℝ) := by rw [hsu]; linarith
          have hle : (t:ℝ) ≤ u := (mul_le_mul_left_of_neg hsneg).mp hstep
          exact le_trans hle (le_max_left u v)
        · have hsv : s * v = (k:ℝ) + ε - a := by linarith [hv']
          have hstep : s * (t:ℝ) ≤ s * v := by rw [hsv]; linarith
          have hle : (t:ℝ) ≤ v := (mul_le_mul_iff_of_pos_left hspos').mp hstep
          exact le_trans hle (le_max_right u v)
    calc ((Gk k).card : ℝ)
        ≤ ((Finset.Icc ⌈min u v⌉ ⌊max u v⌋ : Finset ℤ).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (max u v) - (min u v) + 1 :=
          card_int_Icc_le _ _ (by rw [huv_len]; positivity)
      _ = 2*ε/|s| + 1 := by rw [huv_len]
  have hsub2 : G ⊆ K.biUnion Gk := by
    intro t ht
    rw [hG] at ht
    obtain ⟨htR, hgood⟩ := Finset.mem_filter.mp ht
    obtain ⟨k, hk⟩ := hgood
    rw [Finset.mem_biUnion]
    refine ⟨k, ?_, ?_⟩
    · rw [hK, Finset.mem_Icc]
      rw [abs_le] at hk
      obtain ⟨hlo, hhi⟩ := hk
      have h2 : a + s*(t:ℝ) ≤ (k:ℝ) + ε := by linarith
      have ht0 : (0:ℝ) ≤ (t:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp htR).1
      have htT : (t:ℝ) ≤ (T:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp htR).2
      have hle1 : x₀ ≤ a + s*(t:ℝ) := by
        rw [hx₀]
        rcases le_or_gt 0 s with hsnn | hsneg
        · have h := mul_nonneg hsnn ht0
          exact le_trans (min_le_left _ _) (by linarith)
        · have h := mul_le_mul_of_nonpos_left htT (le_of_lt hsneg)
          exact le_trans (min_le_right _ _) (by linarith)
      have hle2 : a + s*(t:ℝ) ≤ x₁ := by
        rw [hx₁]
        rcases le_or_gt 0 s with hsnn | hsneg
        · have h := mul_le_mul_of_nonneg_left htT hsnn
          exact le_trans (by linarith) (le_max_right _ _)
        · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hsneg) ht0
          exact le_trans (by linarith) (le_max_left _ _)
      constructor
      · rw [Int.ceil_le]; linarith
      · rw [Int.le_floor]; linarith
    · rw [hGk]
      exact Finset.mem_filter.mpr ⟨htR, hk⟩
  calc (G.card : ℝ) ≤ ((K.biUnion Gk).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub2
    _ ≤ ((∑ k ∈ K, (Gk k).card : ℕ) : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ = ∑ k ∈ K, ((Gk k).card : ℝ) := by push_cast; ring
    _ ≤ ∑ k ∈ K, (2*ε/|s| + 1) := Finset.sum_le_sum (fun k _ => hperk k)
    _ = (K.card : ℝ) * (2*ε/|s| + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (|s| * (T:ℝ) + 2*ε + 1) * (2*ε/|s| + 1) :=
        mul_le_mul_of_nonneg_right hKcard (by positivity)

/-! ## Green–Tao style counting bound -/

/-- Let `|θ n - k| ≤ ε` for `δL` values of `n ∈ [1,L]`, and let `q ≥ 1`, `m ∈ ℤ` with
`s := θq - m ≠ 0`. Then `δL ≤ (|s| L + 2q)(2ε/|s| + 1)`. -/
lemma counting_bound (θ : ℝ) (L q : ℕ) (hq : 1 ≤ q) (m : ℤ) (ε : ℝ) (hε : 0 < ε)
    (hβ0 : 0 < |θ * (q:ℝ) - (m:ℝ)|) (hεhalf : ε ≤ 1/2) :
    ((Finset.filter (fun (n:ℕ) => ∃ k : ℤ, |θ * (n:ℝ) - (k:ℝ)| ≤ ε)
        (Finset.Icc 1 L)).card : ℝ)
      ≤ (|θ * (q:ℝ) - (m:ℝ)| * (L:ℝ) + 2*(q:ℝ)) *
          (2*ε/|θ * (q:ℝ) - (m:ℝ)| + 1) := by
  set s : ℝ := θ*(q:ℝ) - (m:ℝ) with hsdef
  have hs : s ≠ 0 := by
    intro h; rw [h] at hβ0; simp at hβ0
  rw [show |θ * (q:ℝ) - (m:ℝ)| = |s| by rw [hsdef]]
  set bs : ℝ := |s| with hsabs
  have hbspos : 0 < bs := hβ0
  set T : ℕ := L / q with hT
  have hqT : q * T ≤ L := by rw [hT]; exact Nat.mul_div_le L q
  set Gr : ℕ → Finset ℤ := fun r => (Finset.Icc (0:ℤ) (T:ℤ)).filter
      (fun t => ∃ k:ℤ, |θ*(r:ℝ) + s*(t:ℝ) - (k:ℝ)| ≤ ε) with hGr
  have hGr_card : ∀ r, ((Gr r).card : ℝ) ≤ (bs * (T:ℝ) + 2*ε + 1) * (2*ε/bs + 1) := by
    intro r
    have h := count_affine (θ*(r:ℝ)) s ε hs hε T
    rw [← hsabs] at h
    simpa [hGr] using h
  set S : Finset ℕ := (Finset.Icc 1 L).filter (fun n => ∃ k:ℤ, |θ*(n:ℝ) - (k:ℝ)| ≤ ε)
    with hS
  have hfiber : ∀ r ∈ Finset.range q,
      ((S.filter (fun n => n % q = r)).card) ≤ (Gr r).card := by
    intro r hr
    apply Finset.card_le_card_of_injOn (f := fun n : ℕ => (((n / q : ℕ)) : ℤ))
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter] at hn
      obtain ⟨hn1, hnr⟩ := hn
      rw [hS] at hn1
      obtain ⟨hn1I, hgood⟩ := Finset.mem_filter.mp hn1
      rw [hGr]
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [Finset.mem_Icc]
        refine ⟨?_, ?_⟩
        · show (0:ℤ) ≤ ((n / q : ℕ) : ℤ); positivity
        · rw [hT]
          show ((n / q : ℕ) : ℤ) ≤ ((L / q : ℕ) : ℤ)
          exact_mod_cast (Nat.div_le_div_right (c := q) (Finset.mem_Icc.mp hn1I).2 : n / q ≤ L / q)
      · obtain ⟨k, hk⟩ := hgood
        set d : ℕ := n / q with hd
        refine ⟨k - m * (d : ℤ), ?_⟩
        have hnn : n = q * d + r := by
          have := Nat.div_add_mod n q
          rw [← hd] at this
          omega
        have hcast : (n:ℝ) = (q:ℝ)*(d:ℝ) + (r:ℝ) := by
          rw [hnn]; push_cast; ring
        have hrel : θ*(n:ℝ) - (k:ℝ)
            = θ*(r:ℝ) + s*((d:ℤ):ℝ) - ((k - m * (d:ℤ) : ℤ) : ℝ) := by
          rw [hsdef, hcast, Int.cast_sub, Int.cast_mul, Int.cast_natCast]; ring
        rw [← hrel]; exact hk
    · rintro n hn n' hn' heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hn hn'
      have hnm : n % q = n' % q := by rw [hn.2, hn'.2]
      have hnd : n / q = n' / q := Int.ofNat.inj heq
      calc n = q * (n / q) + n % q := (Nat.div_add_mod n q).symm
        _ = q * (n' / q) + n' % q := by rw [hnd, hnm]
        _ = n' := Nat.div_add_mod n' q
  have hcard1 := Finset.card_eq_sum_card_fiberwise (f := fun n : ℕ => n % q) (s := S)
      (t := Finset.range q) (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n (by omega)))
  calc ((S.card : ℝ)) = ∑ r ∈ Finset.range q, ((S.filter (fun n => n % q = r)).card : ℝ) := by
        rw [hcard1]; push_cast; ring
    _ ≤ ∑ r ∈ Finset.range q, ((Gr r).card : ℝ) :=
        Finset.sum_le_sum (fun r hr => by exact_mod_cast hfiber r hr)
    _ ≤ ∑ r ∈ Finset.range q, (bs * (T:ℝ) + 2*ε + 1) * (2*ε/bs + 1) :=
        Finset.sum_le_sum (fun r _ => hGr_card r)
    _ = (q:ℝ) * ((bs * (T:ℝ) + 2*ε + 1) * (2*ε/bs + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (bs * (L:ℝ) + 2*(q:ℝ)) * (2*ε/bs + 1) := by
        rw [show (q:ℝ) * ((bs * (T:ℝ) + 2*ε + 1) * (2*ε/bs + 1))
              = ((q:ℝ) * (bs * (T:ℝ) + 2*ε + 1)) * (2*ε/bs + 1) by ring]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hA : (q:ℝ) * (bs * (T:ℝ)) ≤ bs * (L:ℝ) := by
          have hcast : ((q*T : ℕ) : ℝ) ≤ (L:ℝ) := by exact_mod_cast hqT
          have hqT' : (q:ℝ) * (T:ℝ) ≤ (L:ℝ) := by rw [← Nat.cast_mul]; exact hcast
          calc (q:ℝ) * (bs * (T:ℝ)) = bs * ((q:ℝ) * (T:ℝ)) := by ring
            _ ≤ bs * (L:ℝ) := mul_le_mul_of_nonneg_left hqT' hbspos.le
        have hB : (q:ℝ) * (2*ε + 1) ≤ 2*(q:ℝ) := by
          have h2e : 2*ε ≤ 1 := by linarith
          have hqnn : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
          nlinarith [h2e, hqnn]
        nlinarith [hA, hB, hbspos.le]

/-- **Pinning a real `β` to a rational.**  If a positive-density set `A ⊆ [1,L]` has
`‖β h‖ ≤ ε` for all `h ∈ A`, then some `q ≤ C/δ` has `‖q β‖ ≤ C ε/(δ³ L)`. -/
theorem beta_pinning :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (L : ℕ) (δ ε : ℝ) (A : Finset ℕ),
      1 ≤ L → 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ ^ 2 / 100 →
      (∀ h ∈ A, 1 ≤ h ∧ h ≤ L) →
      δ * (L:ℝ) ≤ (A.card : ℝ) →
      (∀ h ∈ A, ∃ m : ℤ, |β * (h:ℝ) - m| ≤ ε) →
      ∃ q : ℕ, 1 ≤ q ∧ (q:ℝ) ≤ C / δ ∧ ∃ m : ℤ,
        |(q:ℝ) * β - m| ≤ C * ε / (δ ^ 3 * (L:ℝ)) := by
  refine ⟨1000, by norm_num, ?_⟩
  intro β L δ ε A hL hδ0 hδ hε hεδ hA hAcard hgood
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast hL
  have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLpos
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have h2ε : 2*ε ≤ δ^2/50 := by nlinarith [hεδ]
  have hεhalf : ε ≤ 1/2 := by nlinarith [hεδ, hδ0, hδ]
  have h2nneg : (0:ℝ) ≤ 2*ε := by linarith [hε.le]
  rcases lt_or_ge (δ * (L:ℝ)) 2 with hsmall | hbig
  · -- trivial case `δL < 2`
    have hne : A.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp; rw [hemp, Finset.card_empty] at hAcard; simp at hAcard
      exact absurd hAcard (not_le.mpr (mul_pos hδ0 hLpos))
    have hmem := Finset.min'_mem A hne
    refine ⟨A.min' hne, (hA _ hmem).1, ?_, ?_⟩
    · have h3 : ((A.min' hne : ℕ):ℝ) ≤ (L:ℝ) := by exact_mod_cast (hA _ hmem).2
      have h2 : (L:ℝ) < 2/δ := by rw [lt_div_iff₀ hδ0]; linarith
      have h4 : (2:ℝ)/δ ≤ 1000/δ := div_le_div_of_nonneg_right (by norm_num) hδ0.le
      linarith
    · obtain ⟨m, hm⟩ := hgood _ hmem
      refine ⟨m, ?_⟩
      have hδ3L : δ^3 * (L:ℝ) ≤ 1000 := by
        have h2 : δ^2 ≤ 1/4 := by nlinarith [hδ, hδ0]
        have h3 : δ^3 * (L:ℝ) = δ^2 * (δ * (L:ℝ)) := by ring
        rw [h3]; nlinarith [h2, hsmall, hδ0.le, hLpos.le]
      calc |((A.min' hne : ℕ):ℝ) * β - m| = |β * ((A.min' hne : ℕ):ℝ) - m| := by rw [mul_comm]
        _ ≤ ε := hm
        _ ≤ 1000 * ε / (δ^3 * (L:ℝ)) := by
            rw [le_div_iff₀ (by positivity)]
            nlinarith [hδ3L, hε.le]
  · -- main case `2 ≤ δL`
    have hAcard2 : 2 ≤ A.card := by
      have : (2:ℝ) ≤ (A.card:ℝ) := le_trans hbig hAcard
      exact_mod_cast this
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    -- the gap is `2ε`-good
    have hgap : ∀ {x y : ℕ}, x ∈ A → y ∈ A → x ≠ y →
        ∃ k : ℤ, |β * ((max x y - min x y : ℕ):ℝ) - k| ≤ 2*ε := by
      intro x y hx hy hxy
      rcases le_total x y with h | h
      · rw [max_eq_right h, min_eq_left h]
        obtain ⟨ma, hma⟩ := hgood x hx
        obtain ⟨mb, hmb⟩ := hgood y hy
        refine ⟨mb - ma, ?_⟩
        rw [Nat.cast_sub h, Int.cast_sub]
        have h2 : β * ((y:ℝ) - (x:ℝ)) - ((mb:ℝ) - (ma:ℝ))
            = (β*(y:ℝ) - (mb:ℝ)) - (β*(x:ℝ) - (ma:ℝ)) := by ring
        rw [h2]
        calc |(β*(y:ℝ) - (mb:ℝ)) - (β*(x:ℝ) - (ma:ℝ))|
            ≤ |β*(y:ℝ) - (mb:ℝ)| + |β*(x:ℝ) - (ma:ℝ)| := by
              have h3 := abs_sub_le (β*(y:ℝ) - (mb:ℝ)) 0 (β*(x:ℝ) - (ma:ℝ))
              rwa [sub_zero, zero_sub, abs_neg] at h3
          _ ≤ 2*ε := by linarith
      · rw [max_eq_left h, min_eq_right h]
        obtain ⟨ma, hma⟩ := hgood x hx
        obtain ⟨mb, hmb⟩ := hgood y hy
        refine ⟨ma - mb, ?_⟩
        rw [Nat.cast_sub h, Int.cast_sub]
        have h2 : β * ((x:ℝ) - (y:ℝ)) - ((ma:ℝ) - (mb:ℝ))
            = (β*(x:ℝ) - (ma:ℝ)) - (β*(y:ℝ) - (mb:ℝ)) := by ring
        rw [h2]
        calc |(β*(x:ℝ) - (ma:ℝ)) - (β*(y:ℝ) - (mb:ℝ))|
            ≤ |β*(x:ℝ) - (ma:ℝ)| + |β*(y:ℝ) - (mb:ℝ)| := by
              have h3 := abs_sub_le (β*(x:ℝ) - (ma:ℝ)) 0 (β*(y:ℝ) - (mb:ℝ))
              rwa [sub_zero, zero_sub, abs_neg] at h3
          _ ≤ 2*ε := by linarith
    have hex : ∃ n : ℕ, 1 ≤ n ∧ ∃ m : ℤ, |β*(n:ℝ) - m| ≤ 2*ε := by
      refine ⟨max a b - min a b, ?_, hgap ha hb hab⟩
      rcases le_total a b with h | h
      · rw [max_eq_right h, min_eq_left h]; omega
      · rw [max_eq_left h, min_eq_right h]; omega
    set q₀ : ℕ := Nat.find hex with hq0def
    have hq0spec : 1 ≤ q₀ ∧ ∃ m : ℤ, |β*(q₀:ℝ) - m| ≤ 2*ε := by
      rw [hq0def]; exact Nat.find_spec hex
    have hq0min : ∀ m : ℕ, (1 ≤ m ∧ ∃ k : ℤ, |β*(m:ℝ) - k| ≤ 2*ε) → q₀ ≤ m := by
      intro m hm; rw [hq0def]; exact Nat.find_min' hex hm
    obtain ⟨m₀, hm₀⟩ := hq0spec.2
    set β₀ : ℝ := |β*(q₀:ℝ) - (m₀:ℝ)| with hβ0def
    have hβ0le : β₀ ≤ 2*ε := hm₀
    have hβ0nn : 0 ≤ β₀ := abs_nonneg _
    have hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → q₀ ≤ max x y - min x y := by
      intro x hx y hy hxy
      exact hq0min _ ⟨by
        rcases le_total x y with h | h
        · rw [max_eq_right h, min_eq_left h]; omega
        · rw [max_eq_left h, min_eq_right h]; omega, hgap hx hy hxy⟩
    have hsep' := separated_card_bound A q₀ L hq0spec.1 (fun x hx => (hA x hx).2) hsep
    have hq0le : (q₀:ℝ) ≤ 2/δ := by
      have hc1ge : δ*(L:ℝ)/2 ≤ ((A.card - 1 : ℕ):ℝ) := by
        have hc1 : ((A.card - 1 : ℕ):ℝ) = (A.card:ℝ) - 1 := by
          have h1 : 1 ≤ A.card := by omega
          rw [Nat.cast_sub h1]; norm_num
        rw [hc1]; linarith [hAcard, hbig]
      have hsepR : ((A.card - 1 : ℕ):ℝ) * (q₀:ℝ) ≤ (L:ℝ) := by exact_mod_cast hsep'
      have hpos : 0 < δ*(L:ℝ)/2 := by linarith
      have hq0nn : (0:ℝ) ≤ (q₀:ℝ) := Nat.cast_nonneg q₀
      have hstep : (δ*(L:ℝ)/2) * (q₀:ℝ) ≤ (L:ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hc1ge hq0nn) hsepR
      have h1 : (q₀:ℝ) ≤ (L:ℝ)/(δ*(L:ℝ)/2) := by
        rw [le_div_iff₀ hpos]; linarith [hstep]
      have h2 : (L:ℝ)/(δ*(L:ℝ)/2) = 2/δ := by
        rw [div_eq_div_iff (ne_of_gt hpos) hδne]; ring
      rw [h2] at h1; exact h1
    have hq0le1000 : (q₀:ℝ) ≤ 1000/δ := le_trans hq0le (div_le_div_of_nonneg_right (by norm_num) hδ0.le)
    by_cases hβ0zero : β₀ = 0
    · refine ⟨q₀, hq0spec.1, hq0le1000, ⟨m₀, ?_⟩⟩
      rw [mul_comm, show |β*(q₀:ℝ) - (m₀:ℝ)| = 0 by rw [← hβ0def]; exact hβ0zero]
      positivity
    · have hβ0pos : 0 < β₀ := lt_of_le_of_ne hβ0nn (Ne.symm hβ0zero)
      rcases lt_or_ge (δ*(L:ℝ)) (100/δ) with hmid | hlarge
      · -- `2 ≤ δL < 100/δ`
        refine ⟨q₀, hq0spec.1, hq0le1000, ⟨m₀, ?_⟩⟩
        rw [mul_comm, show |β*(q₀:ℝ) - (m₀:ℝ)| = β₀ by rw [hβ0def]]
        have h5 : 2*δ^3*(L:ℝ) ≤ 1000 := by
          have h7 : δ^3*(L:ℝ) = δ^2 * (δ*(L:ℝ)) := by ring
          have h8 : δ^2 * (δ*(L:ℝ)) < δ^2 * (100/δ) :=
            mul_lt_mul_of_pos_left hmid (by positivity)
          have h9 : δ^2 * (100/δ) = 100*δ := by field_simp
          nlinarith [h7, h8, h9, hδ, hδ0]
        calc β₀ ≤ 2*ε := hβ0le
          _ ≤ 1000*ε/(δ^3*(L:ℝ)) := by
              rw [le_div_iff₀ (by positivity)]
              nlinarith [h5, hε.le]
      · -- `100/δ ≤ δL`
        have hArd : (A.card:ℝ) ≤
            ((Finset.filter (fun (n:ℕ) => ∃ k : ℤ, |β*(n:ℝ) - (k:ℝ)| ≤ ε) (Finset.Icc 1 L)).card : ℝ) := by
          have hsub : A ⊆ (Finset.Icc 1 L).filter (fun n => ∃ k:ℤ, |β*(n:ℝ) - (k:ℝ)| ≤ ε) := by
            intro n hn
            exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hA n hn).1, (hA n hn).2⟩, hgood n hn⟩
          exact_mod_cast Finset.card_le_card hsub
        have hcount := counting_bound β L q₀ hq0spec.1 m₀ ε hε
          (by rw [← hβ0def]; exact hβ0pos) hεhalf
        have hmain : δ*(L:ℝ) ≤ β₀*(L:ℝ) + 2*ε*(L:ℝ) + 4*ε*(q₀:ℝ)/β₀ + 2*(q₀:ℝ) := by
          have h1 := le_trans (le_trans hAcard hArd) hcount
          rw [show |β*(q₀:ℝ) - (m₀:ℝ)| = β₀ by rw [hβ0def]] at h1
          have h2 : (β₀*(L:ℝ) + 2*(q₀:ℝ)) * (2*ε/β₀ + 1)
              = β₀*(L:ℝ) + 2*ε*(L:ℝ) + 4*ε*(q₀:ℝ)/β₀ + 2*(q₀:ℝ) := by
            field_simp; ring
          linarith [h1, h2.le, h2.ge]
        rcases lt_or_ge (δ*(L:ℝ)/2) (4*ε*(q₀:ℝ)/β₀) with hcaseB | hcaseA
        · have hbl : β₀ < 8*ε*(q₀:ℝ)/(δ*(L:ℝ)) := by
            rw [lt_div_iff₀ hβ0pos] at hcaseB
            rw [lt_div_iff₀ (by positivity : 0 < δ*(L:ℝ))]
            nlinarith [hcaseB]
          have hb2 : 8*ε*(q₀:ℝ)/(δ*(L:ℝ)) ≤ 16*ε/(δ^2*(L:ℝ)) := by
            rw [div_le_div_iff₀ (by positivity : (0:ℝ) < δ*(L:ℝ))
                  (by positivity : (0:ℝ) < δ^2*(L:ℝ))]
            have hd : (q₀:ℝ)*δ ≤ 2 := by rw [← le_div_iff₀ hδ0]; exact hq0le
            have h1 : 8*ε*(q₀:ℝ)*(δ^2*(L:ℝ)) = (8*ε*δ*(L:ℝ)) * ((q₀:ℝ)*δ) := by ring
            have h2 : 16*ε*(δ*(L:ℝ)) = (8*ε*δ*(L:ℝ)) * 2 := by ring
            rw [h1, h2]
            exact mul_le_mul_of_nonneg_left hd (by positivity)
          have hb3 : 16*ε/(δ^2*(L:ℝ)) ≤ 1000*ε/(δ^3*(L:ℝ)) := by
            rw [div_le_div_iff₀ (by positivity : (0:ℝ) < δ^2*(L:ℝ))
                  (by positivity : (0:ℝ) < δ^3*(L:ℝ))]
            have h1 : 16*ε*(δ^3*(L:ℝ)) = (16*ε*(δ^2*(L:ℝ))) * δ := by ring
            have h2 : 1000*ε*(δ^2*(L:ℝ)) = (16*ε*(δ^2*(L:ℝ))) * ((1000:ℝ)/16) := by ring
            rw [h1, h2]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [hδ]
          exact ⟨q₀, hq0spec.1, hq0le1000, ⟨m₀, by
            rw [mul_comm, show |β*(q₀:ℝ) - (m₀:ℝ)| = β₀ by rw [hβ0def]]
            exact le_trans hbl.le (le_trans hb2 hb3)⟩⟩
        · exfalso
          have hb0ge : δ/2 - 2*ε - 2*(q₀:ℝ)/(L:ℝ) ≤ β₀ := by
            have h2 : δ*(L:ℝ)/2 ≤ β₀*(L:ℝ) + 2*ε*(L:ℝ) + 2*(q₀:ℝ) := by
              nlinarith [hmain, hcaseA]
            have h3 : δ/2 - β₀ - 2*ε ≤ 2*(q₀:ℝ)/(L:ℝ) := by
              rw [le_div_iff₀ hLpos]; nlinarith [h2]
            linarith
          have hq0L : 2*(q₀:ℝ)/(L:ℝ) ≤ δ/25 := by
            have h3 : 50*(q₀:ℝ) ≤ δ*(L:ℝ) := by
              have h4 : 50*(q₀:ℝ) ≤ 50*(2/δ) := by
                have := hq0le; nlinarith [hδ0]
              have h5 : 50*(2/δ) = 100/δ := by field_simp; ring
              have := mul_le_mul_of_nonneg_right hlarge hδ0.le
              rw [h5] at h4
              have h6 : (100/δ)*δ = 100 := by field_simp
              rw [h6] at this
              nlinarith [h4, this]
            rw [div_le_iff₀ hLpos]
            nlinarith [h3]
          have h2e : 2*ε ≤ δ/100 := by nlinarith [h2ε, hδ0, hδ]
          have hge : (9:ℝ)/20 * δ ≤ β₀ := by linarith [hb0ge, hq0L, h2e]
          have hle : β₀ ≤ (1:ℝ)/100 * δ := by linarith [hβ0le, h2e]
          nlinarith [hge, hle, hδ0]

end Work.BMF.SD
