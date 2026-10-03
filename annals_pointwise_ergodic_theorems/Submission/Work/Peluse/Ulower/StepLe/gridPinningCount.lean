import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Ulower.StepLe

/-- The number of integers lying in a real interval `[u,v]` is at most `⌊v-u⌋+1`.
(Standard interval count: map `m ↦ m - ⌈u⌉` injectively into `{0,…,⌊v-u⌋} ⊂ ℤ`.) -/
private lemma card_le_floor_sub_add_one {u v : ℝ} (huv : u ≤ v) (F : Finset ℕ)
    (h : ∀ m ∈ F, u ≤ (m : ℝ) ∧ (m : ℝ) ≤ v) :
    F.card ≤ Nat.floor (v - u) + 1 := by
  have hvu : 0 ≤ v - u := sub_nonneg.mpr huv
  have hfl : 0 ≤ ⌊v - u⌋ := Int.floor_nonneg.mpr hvu
  have hinj : Function.Injective (fun m : ℕ => (m : ℤ) - ⌈u⌉) := by
    intro a b hab
    have hab' : (a : ℤ) - ⌈u⌉ = (b : ℤ) - ⌈u⌉ := hab
    have : (a : ℤ) = (b : ℤ) := by linarith
    exact_mod_cast this
  have hsub : F.image (fun m : ℕ => (m : ℤ) - ⌈u⌉) ⊆ Finset.Icc (0 : ℤ) ⌊v - u⌋ := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h1, h2⟩ := h m hm
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have hcu : (⌈u⌉ : ℤ) ≤ (m : ℤ) := by
        rw [Int.ceil_le]; exact_mod_cast h1
      omega
    · rw [Int.le_floor]
      have hc : u ≤ ((⌈u⌉ : ℤ) : ℝ) := Int.le_ceil u
      have h2' : ((m : ℤ) : ℝ) ≤ v := by exact_mod_cast h2
      have hcast : (((m : ℤ) - ⌈u⌉ : ℤ) : ℝ) = ((m:ℤ) : ℝ) - ((⌈u⌉ : ℤ) : ℝ) := by
        push_cast; ring
      rw [hcast]
      linarith
  calc F.card = (F.image (fun m : ℕ => (m : ℤ) - ⌈u⌉)).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (Finset.Icc (0 : ℤ) ⌊v - u⌋).card := Finset.card_le_card hsub
    _ = (⌊v - u⌋ + 1).toNat := by rw [Int.card_Icc]; norm_num
    _ = Nat.floor (v - u) + 1 := by
        rw [Int.toNat_add hfl (by norm_num), Int.floor_toNat]
        norm_num

/-- The number of integers lying in a real interval `[u,u+len]` of length `len ≥ 0` is at most
`⌊len⌋+1`. -/
private lemma card_le_floor_add_one {u len : ℝ} (hlen : 0 ≤ len) (F : Finset ℕ)
    (h : ∀ m ∈ F, u ≤ (m : ℝ) ∧ (m : ℝ) ≤ u + len) :
    F.card ≤ Nat.floor len + 1 := by
  have hsub : ∀ m ∈ F, u ≤ (m:ℝ) ∧ (m:ℝ) ≤ u + len := h
  have := card_le_floor_sub_add_one (u := u) (v := u + len) (by linarith) F hsub
  rwa [add_sub_cancel_left] at this

/-- **Grid pinning count.**  Let `S` be a set of integers `m ≤ 2^σ · T` such that each `m/T` lies
within `ε` of a rational number with denominator at most `T₀`.  Then
`|S| ≤ 4 ((2^σ T₀ + 1) T₀) (⌊2εT⌋+1)`:  the `ε`-broadened grid of rationals with denominator
`≤ T₀` pins at most that many integer points, each grid point contributing an interval of length
`2εT` (when `2εT₀ < 1`, the regime counted by the second factor), while for `2εT₀ ≥ 1` the grid
already covers the whole line and only the crude range bound is used. -/
theorem gridPinningCount {σ T₀ T : ℕ} (hT : 1 ≤ T) {ε : ℝ} (hε : 0 ≤ ε)
    (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ≤ 2 ^ σ * T ∧ ∃ t : ℕ, 1 ≤ t ∧ t ≤ T₀ ∧ ∃ a : ℤ,
      |(m : ℝ) / (T : ℝ) - (a : ℝ) / (t : ℝ)| ≤ ε) :
    (S.card : ℝ) ≤ 4 * ((2 ^ σ * T₀ + 1) * T₀) * (Nat.floor (2 * ε * (T : ℝ)) + 1) := by
  have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast hT
  have hT0le : (0:ℝ) ≤ (T:ℝ) := le_of_lt hTpos
  set D : ℕ := Nat.floor (2 * ε * (T : ℝ)) + 1 with hDdef
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by
    have h : 1 ≤ D := by omega
    exact_mod_cast h
  have hDge : 2 * ε * (T:ℝ) ≤ (D:ℝ) := by
    have h := Nat.lt_floor_add_one (2 * ε * (T:ℝ))
    rw [hDdef]; push_cast; linarith
  have hDcast : ((Nat.floor (2 * ε * (T:ℝ)) : ℝ) + 1) = (D:ℝ) := by
    rw [hDdef]; push_cast; ring
  rcases le_or_gt (1:ℝ) (2 * ε * (T₀:ℝ)) with hbig | hsmall
  · -- Case `2εT₀ ≥ 1`: the grid is `ε`-dense, only the range bound is used.
    have hT0 : 1 ≤ T₀ := by
      rcases Nat.eq_zero_or_pos T₀ with h | h
      · rw [h] at hbig; push_cast at hbig; linarith
      · exact h
    have hT0R : (1:ℝ) ≤ (T₀:ℝ) := by exact_mod_cast hT0
    have hScard : (S.card : ℝ) ≤ (2:ℝ)^σ * (T:ℝ) + 1 := by
      have hsub : S ⊆ Finset.Icc 0 (2^σ * T) :=
        fun m hm => Finset.mem_Icc.mpr ⟨Nat.zero_le _, (hS m hm).1⟩
      have h := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.sub_zero] at h
      exact_mod_cast h
    have hpow1 : (1:ℝ) ≤ (2:ℝ)^σ := one_le_pow₀ (by norm_num)
    have hTD : (T:ℝ) ≤ (T₀:ℝ) * (D:ℝ) := by
      have h1 : (T:ℝ) ≤ (T₀:ℝ) * (2*ε*(T:ℝ)) := by nlinarith [hbig, hT0le]
      nlinarith [h1, hDge, hT0le]
    have hScard' : (S.card : ℝ) ≤ (2:ℝ)^σ * ((T₀:ℝ)*(D:ℝ)) + 1 := by nlinarith [hScard, hTD]
    have hA0 : (0:ℝ) ≤ (2:ℝ)^σ * (T₀:ℝ) * (D:ℝ) := by positivity
    have hprod : (2:ℝ)^σ * (T₀:ℝ) * (D:ℝ) * 1 ≤ (2:ℝ)^σ * (T₀:ℝ) * (D:ℝ) * (T₀:ℝ) :=
      mul_le_mul_of_nonneg_left hT0R hA0
    have hATD : (1:ℝ) ≤ (2:ℝ)^σ * (T₀:ℝ) * (D:ℝ) := by nlinarith [hpow1, hT0R, hD1]
    rw [hDcast]
    nlinarith [hScard', hprod, hATD, hA0, show (0:ℝ) ≤ (T₀:ℝ)*(D:ℝ) by positivity]
  · -- Case `2εT₀ < 1`: count the grid points used, each pinning `⌊2εT⌋+1` integers.
    let f : ℕ → ℕ × ℤ := fun m =>
      if hm : m ∈ S then ((hS m hm).2.choose, (hS m hm).2.choose_spec.2.2.choose) else (1, 0)
    have hf_spec : ∀ m ∈ S, 1 ≤ (f m).1 ∧ (f m).1 ≤ T₀ ∧
        |(m:ℝ)/(T:ℝ) - ((f m).2:ℝ)/((f m).1:ℝ)| ≤ ε := by
      intro m hm
      have hfm : f m = ((hS m hm).2.choose, (hS m hm).2.choose_spec.2.2.choose) := dif_pos hm
      rw [hfm]
      exact ⟨(hS m hm).2.choose_spec.1, (hS m hm).2.choose_spec.2.1,
             (hS m hm).2.choose_spec.2.2.choose_spec⟩
    -- each grid point (witness) pins at most `D` elements of `S`
    have hfib : ∀ b ∈ S.image f, (S.filter (fun m => f m = b)).card ≤ D := by
      intro b hb
      have hsub : S.filter (fun m => f m = b) ⊆
          S.filter (fun m => |(m:ℝ)/(T:ℝ) - ((b.2:ℝ)/((b.1:ℝ)))| ≤ ε) := by
        intro m hm
        simp only [Finset.mem_filter] at hm ⊢
        obtain ⟨hmS, hfm⟩ := hm
        exact ⟨hmS, by simpa [hfm] using (hf_spec m hmS).2.2⟩
      refine le_trans (Finset.card_le_card hsub) ?_
      rw [hDdef]
      have hlen : (0:ℝ) ≤ 2*ε*(T:ℝ) := by positivity
      apply card_le_floor_add_one (u := (T:ℝ)*((b.2:ℝ)/(b.1:ℝ)) - ε*(T:ℝ)) hlen
      intro m hm
      simp only [Finset.mem_filter] at hm
      obtain ⟨_, hmr⟩ := hm
      obtain ⟨hlo, hhi⟩ := abs_le.mp hmr
      have hTm : (T:ℝ) * ((m:ℝ)/(T:ℝ)) = (m:ℝ) := by field_simp
      constructor
      · have h1 := mul_le_mul_of_nonneg_left hlo hT0le
        nlinarith [h1, hTm]
      · have h1 := mul_le_mul_of_nonneg_left hhi hT0le
        nlinarith [h1, hTm]
    set K : ℕ := 2^σ * T₀ + 1 with hKdef
    have hKeq : ((2:ℝ)^σ * (T₀:ℝ) + 1) = (K:ℝ) := by rw [hKdef]; push_cast; ring
    -- the witnesses all lie in a box of size `T₀ × (2K+1)`
    have hbox : S.image f ⊆ (Finset.Icc 1 T₀) ×ˢ (Finset.Icc (-(K:ℤ)) (K:ℤ)) := by
      intro b hb
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
      obtain ⟨h1t, h2t, hineq⟩ := hf_spec m hm
      have htpos : (0:ℝ) < ((f m).1 : ℝ) := by exact_mod_cast h1t
      have hm_le : (m:ℝ) ≤ (2:ℝ)^σ * (T:ℝ) := by
        have h := (hS m hm).1
        have h' : (m:ℝ) ≤ ((2^σ * T : ℕ) : ℝ) := by exact_mod_cast h
        simpa using h'
      have hmT_le : (m:ℝ)/(T:ℝ) ≤ (2:ℝ)^σ := by
        rw [div_le_iff₀ hTpos]; linarith
      have hmT_abs : |(m:ℝ)/(T:ℝ)| ≤ (2:ℝ)^σ := by
        rw [abs_of_nonneg (by positivity)]; exact hmT_le
      have hat : |((f m).2 : ℝ)/((f m).1 : ℝ)| ≤ (2:ℝ)^σ + ε := by
        have h1 := (abs_sub_le_iff.mp hineq).1
        have h2 := (abs_sub_le_iff.mp hineq).2
        have h3 := (abs_le.mp hmT_abs).1
        have h4 := (abs_le.mp hmT_abs).2
        rw [abs_le]
        constructor <;> linarith
      have hK : |(f m).2| ≤ (K:ℤ) := by
        have habs : |((f m).2 : ℝ)| ≤ (2:ℝ)^σ * (T₀:ℝ) + 1 := by
          have h1 : |((f m).2:ℝ)| ≤ ((2:ℝ)^σ + ε) * ((f m).1:ℝ) := by
            have h := hat
            rw [abs_div, abs_of_pos htpos] at h
            rw [div_le_iff₀ htpos] at h
            linarith [h]
          have h2 : ((2:ℝ)^σ + ε) * ((f m).1:ℝ) ≤ ((2:ℝ)^σ + ε) * (T₀:ℝ) :=
            mul_le_mul_of_nonneg_left (by exact_mod_cast h2t) (by positivity)
          have h3 : ε * (T₀:ℝ) < 1/2 := by linarith [hsmall]
          nlinarith [h1, h2, h3]
        have hcast : ((|(f m).2| : ℤ) : ℝ) ≤ (K:ℝ) := by
          rw [Int.cast_abs]; linarith [habs, hKeq]
        exact_mod_cast hcast
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨h1t, h2t⟩, Finset.mem_Icc.mpr ?_⟩
      exact abs_le.mp hK
    have hboxcard : (S.image f).card ≤ T₀ * (2 * K + 1) := by
      have h2 : (Finset.Icc (1:ℕ) T₀).card = T₀ := by rw [Nat.card_Icc]; omega
      have h3 : (Finset.Icc (-(K:ℤ)) (K:ℤ)).card = 2*K+1 := by
        rw [Int.card_Icc]
        have h : (K:ℤ) + 1 - (-(K:ℤ)) = 2*(K:ℤ)+1 := by ring
        rw [h]; omega
      calc (S.image f).card ≤ ((Finset.Icc 1 T₀) ×ˢ (Finset.Icc (-(K:ℤ)) (K:ℤ))).card :=
            Finset.card_le_card hbox
        _ = T₀ * (2*K+1) := by rw [Finset.card_product, h2, h3]
    have hcard1 : S.card ≤ D * (S.image f).card := Finset.card_le_mul_card_image S D hfib
    have hcard2 : (S.card : ℝ) ≤ (D:ℝ) * (T₀:ℝ) * (2 * (K:ℝ) + 1) := by
      have hh : S.card ≤ D * (T₀ * (2*K+1)) := le_trans hcard1 (Nat.mul_le_mul_left D hboxcard)
      have := (Nat.cast_le (α := ℝ)).mpr hh
      push_cast at this
      linarith [this]
    have hK2 : 2*(K:ℝ) + 1 ≤ 4*(K:ℝ) := by
      have h1 : (1:ℝ) ≤ (K:ℝ) := by
        have : 1 ≤ K := by omega
        exact_mod_cast this
      linarith
    rw [hKeq, hDcast]
    nlinarith [hcard2, hK2, hD1, show (0:ℝ) ≤ (T₀:ℝ) by positivity,
      show (0:ℝ) ≤ (K:ℝ) by positivity]

end Work.Peluse.Ulower.StepLe
