import Mathlib
import Submission.Work.Analysis.Hilbert.shift_lattice_kernel_identity
import Submission.Work.A7.varphiN_integrable_measurable
import Submission.Work.KMTAreas.A7.varphiNt_bounds
import Submission.Work.KMTPlan.A6.MdlTleKer

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A7Hi

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Elementary Fourier identities on the circle -/

lemma fourier_point_add (n : ℤ) (x y : Circ) :
    fourier (T := 1) n (x + y) = fourier (T := 1) n x * fourier (T := 1) n y := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

lemma fourier_point_neg (n : ℤ) (y : Circ) :
    fourier (T := 1) n (-y) = fourier (T := 1) (-n) y := by
  rw [fourier_apply, fourier_apply, smul_neg, neg_smul]

lemma fourier_point_sub (n : ℤ) (x y : Circ) :
    fourier (T := 1) n (x - y) = fourier (T := 1) n x * fourier (T := 1) (-n) y := by
  rw [sub_eq_add_neg, fourier_point_add, fourier_point_neg]

/-! ## The Fejér kernel is a nonnegative real -/

/-! ## The geometric sum over the `Q`-grid -/

lemma sum_range_fourier_zero (Q : ℕ) (_hQ : 0 < Q) (γ : Circ) (hγ : Q • γ = 0) :
    ∑ a ∈ Finset.range Q, fourier (T := 1) (a : ℤ) γ = if γ = 0 then (Q : ℂ) else 0 := by
  have hstep : ∀ n : ℕ, fourier (T := 1) ((n + 1 : ℕ) : ℤ) γ
      = fourier (T := 1) (n : ℤ) γ * fourier (T := 1) (1 : ℤ) γ := by
    intro n
    have h1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [h1, fourier_add]
  have hQ0 : fourier (T := 1) (Q : ℤ) γ = 1 := by
    rw [fourier_apply, natCast_zsmul, hγ, AddCircle.toCircle_zero]
    rfl
  have htel : (∑ a ∈ Finset.range Q, fourier (T := 1) (a : ℤ) γ) *
      (fourier (T := 1) (1 : ℤ) γ - 1) = 0 := by
    have h0 := Finset.sum_range_sub (fun i : ℕ => fourier (T := 1) (i : ℤ) γ) Q
    have hc : ∑ i ∈ Finset.range Q,
        (fourier (T := 1) ((i + 1 : ℕ) : ℤ) γ - fourier (T := 1) (i : ℤ) γ)
        = ∑ i ∈ Finset.range Q,
            fourier (T := 1) (i : ℤ) γ * (fourier (T := 1) (1 : ℤ) γ - 1) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hstep i, mul_sub, mul_one]
    rw [hc, ← Finset.sum_mul] at h0
    rw [hQ0] at h0
    simpa using h0
  by_cases h0 : γ = 0
  · subst h0
    rw [if_pos rfl]
    have h1 : ∀ a : ℕ, fourier (T := 1) (a : ℤ) (0 : Circ) = 1 := by
      intro a; simp
    rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  · rw [if_neg h0]
    rcases mul_eq_zero.mp htel with hS | hω
    · exact hS
    · exfalso
      have h1 : fourier (T := 1) (1 : ℤ) γ = 1 := sub_eq_zero.mp hω
      rw [fourier_one] at h1
      exact h0 (AddCircle.injective_toCircle (T := 1) one_ne_zero
        (by rw [AddCircle.toCircle_zero]; exact Subtype.ext h1))

lemma sum_range_fourier_div (Q : ℕ) (i : ℤ) :
    ∑ a ∈ Finset.range Q, fourier (T := 1) i (((a : ℝ) / (Q : ℝ)) : Circ)
      = if (Q : ℤ) ∣ i then (Q : ℂ) else 0 := by
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
  · subst hQ0
    rw [Finset.range_zero, Finset.sum_empty]
    by_cases hi : i = 0
    · subst hi; simp
    · rw [if_neg (by rintro ⟨c, hc⟩; exact hi (by simpa using hc))]
  · have hsub : ∀ a : ℕ, fourier (T := 1) i (((a : ℝ) / (Q : ℝ)) : Circ)
        = fourier (T := 1) (a : ℤ) (((i : ℝ) / (Q : ℝ)) : Circ) := by
      intro a
      rw [fourier_coe_apply, fourier_coe_apply]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun a _ => hsub a)]
    have hγ : Q • (((i : ℝ) / (Q : ℝ)) : Circ) = 0 := by
      rw [← AddCircle.coe_nsmul (1 : ℝ) (n := Q) (x := (i : ℝ) / (Q : ℝ)), nsmul_eq_mul]
      have h1 : (Q : ℝ) * ((i : ℝ) / (Q : ℝ)) = (i : ℝ) := by field_simp
      rw [h1]
      exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨i, by simp⟩
    rw [sum_range_fourier_zero Q hQpos _ hγ]
    have hiff : (((i : ℝ) / (Q : ℝ)) : Circ) = 0 ↔ (Q : ℤ) ∣ i := by
      constructor
      · intro hzero
        obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
        have hn' : (n : ℝ) = (i : ℝ) / (Q : ℝ) := by simpa using hn
        refine ⟨n, ?_⟩
        have h2 : ((i : ℤ) : ℝ) = (((Q : ℤ) * n : ℤ) : ℝ) := by
          push_cast
          field_simp at hn'
          linarith
        exact_mod_cast h2
      · rintro ⟨n, hn⟩
        have h1 : (i : ℝ) / (Q : ℝ) = (n : ℝ) := by
          rw [hn]; push_cast; field_simp
        rw [h1]
        exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨n, by simp⟩
    by_cases hd : (Q : ℤ) ∣ i
    · rw [if_pos (hiff.mpr hd), if_pos hd]
    · rw [if_neg (fun h => hd (hiff.mp h)), if_neg hd]

/-! ## Counting the multiples of `Q` in an interval -/

lemma card_multiples_Icc_le (N Q : ℕ) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun j : ℤ => (Q : ℤ) ∣ j)).card
      ≤ 2 * (N / Q) + 1 := by
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
  · subst hQ0
    have hsub : (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun j : ℤ => ((0 : ℕ) : ℤ) ∣ j)
        ⊆ {0} := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      obtain ⟨-, c, hc⟩ := hj
      simp only [Finset.mem_singleton]
      simpa using hc
    rw [Nat.div_zero, mul_zero, zero_add, ← Finset.card_singleton (0 : ℤ)]
    exact Finset.card_le_card hsub
  · set T : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun j : ℤ => (Q : ℤ) ∣ j) with hT
    set c : ℕ := N / Q with hc
    have hQZ : (Q : ℤ) ≠ 0 := by exact_mod_cast hQpos.ne'
    let f : ℤ → ℤ := fun j => j / (Q : ℤ)
    have hmaps : Set.MapsTo f ↑T ↑(Finset.Icc (-((c : ℕ) : ℤ)) ((c : ℕ) : ℤ)) := by
      intro j hj
      simp only [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_Icc] at hj
      obtain ⟨⟨hj1, hj2⟩, hdvd⟩ := hj
      obtain ⟨m, hm⟩ := hdvd
      have hjm : f j = m := by
        show j / (Q : ℤ) = m
        rw [hm, Int.mul_ediv_cancel_left m hQZ]
      rw [hjm]
      have habs : |j| ≤ (N : ℤ) := abs_le.mpr ⟨hj1, hj2⟩
      have h3 : (Q : ℤ) * (m.natAbs : ℤ) ≤ (N : ℤ) := by
        calc (Q : ℤ) * (m.natAbs : ℤ) = (Q : ℤ) * |m| := by rw [Int.natCast_natAbs]
          _ = |(Q : ℤ) * m| := by
            have hQnn : (0:ℤ) ≤ (Q:ℤ) := by exact_mod_cast hQpos.le
            rw [abs_mul, abs_of_nonneg hQnn]
          _ = |j| := by rw [hm]
          _ ≤ (N : ℤ) := habs
      have hmabs : m.natAbs ≤ c := by
        rw [hc]
        refine (Nat.le_div_iff_mul_le hQpos).mpr ?_
        have h4 : ((m.natAbs * Q : ℕ) : ℤ) ≤ (N : ℤ) := by simpa [mul_comm] using h3
        exact_mod_cast h4
      have h5 : |m| ≤ ((c : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hmabs
      exact Finset.mem_Icc.mpr (abs_le.mp h5)
    have hinj : Set.InjOn f ↑T := by
      intro j1 hj1 j2 hj2 heq
      simp only [Finset.mem_coe, hT, Finset.mem_filter] at hj1 hj2
      obtain ⟨-, hd1⟩ := hj1
      obtain ⟨-, hd2⟩ := hj2
      calc j1 = f j1 * (Q : ℤ) := (Int.ediv_mul_cancel hd1).symm
        _ = f j2 * (Q : ℤ) := by rw [heq]
        _ = j2 := Int.ediv_mul_cancel hd2
    have hcard : T.card ≤ (Finset.Icc (-((c : ℕ) : ℤ)) ((c : ℕ) : ℤ)).card :=
      Finset.card_le_card_of_injOn f hmaps hinj
    have hIcc : (Finset.Icc (-((c : ℕ) : ℤ)) ((c : ℕ) : ℤ)).card = 2 * c + 1 := by
      rw [Int.card_Icc]
      have h6 : ((c : ℕ) : ℤ) + 1 - (-((c : ℕ) : ℤ)) = (((2 * c + 1 : ℕ)) : ℤ) := by
        push_cast; ring
      rw [h6, Int.toNat_natCast]
    rw [hIcc] at hcard
    exact hcard

/-! ## The grid identity for the Fejér kernel -/

/-! ## The `3`-bound for the grid sum -/

lemma norm_fejer_grid_sum_mul_le_three (ℓ Q : ℕ) (hQ : 0 < Q) (hQN : Q ≤ 2 ^ ℓ) (ξ : Circ) :
    (Q : ℝ) * ‖∑ j ∈ (Finset.Icc (-(((2:ℕ)^ℓ : ℕ) : ℤ)) (((2:ℕ)^ℓ : ℕ) : ℤ)).filter
        (fun j : ℤ => (Q : ℤ) ∣ j),
        ((Work.Analysis.Hilbert.triKernel ℓ j : ℝ) : ℂ) * fourier (T := 1) (-j) ξ‖ ≤ 3 := by
  set T : Finset ℤ := (Finset.Icc (-(((2:ℕ)^ℓ : ℕ) : ℤ)) (((2:ℕ)^ℓ : ℕ) : ℤ)).filter
    (fun j : ℤ => (Q : ℤ) ∣ j) with hT
  set S : ℂ := ∑ j ∈ T, ((Work.Analysis.Hilbert.triKernel ℓ j : ℝ) : ℂ) *
    fourier (T := 1) (-j) ξ with hS
  have hQposR : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hNpos : (0:ℝ) < (2:ℝ)^ℓ := by positivity
  have hcastR : (((2:ℕ)^ℓ : ℕ) : ℝ) = (2:ℝ)^ℓ := by push_cast; ring
  have hcard : (T.card : ℝ) ≤ 2 * (2:ℝ)^ℓ / (Q : ℝ) + 1 := by
    have h1 : T.card ≤ 2 * (((2:ℕ)^ℓ) / Q) + 1 := card_multiples_Icc_le ((2:ℕ)^ℓ) Q
    have h4 : ((((2:ℕ)^ℓ) / Q : ℕ) : ℝ) ≤ (2:ℝ)^ℓ / (Q : ℝ) := by
      have hh := Nat.cast_div_le (α := ℝ) (m := (2:ℕ)^ℓ) (n := Q)
      rwa [hcastR] at hh
    have h5 : (T.card : ℝ) ≤ 2 * ((((2:ℕ)^ℓ) / Q : ℕ) : ℝ) + 1 := by
      have hh : ((T.card : ℕ) : ℝ) ≤ ((2 * (((2:ℕ)^ℓ) / Q) + 1 : ℕ) : ℝ) := by
        exact_mod_cast h1
      push_cast at hh
      exact hh
    have h6 : 2 * ((((2:ℕ)^ℓ) / Q : ℕ) : ℝ) + 1 ≤ 2 * ((2:ℝ)^ℓ / (Q : ℝ)) + 1 := by
      linarith [h4]
    have h7 : 2 * ((2:ℝ)^ℓ / (Q : ℝ)) + 1 = 2 * (2:ℝ)^ℓ / (Q : ℝ) + 1 := by
      rw [mul_div_assoc]
    linarith [h5, h6, h7]
  have hSbound : ‖S‖ ≤ (2 * (2:ℝ)^ℓ / (Q : ℝ) + 1) * ((2:ℝ)^ℓ)⁻¹ := by
    have h1 : ‖S‖ ≤ ∑ j ∈ T, ‖((Work.Analysis.Hilbert.triKernel ℓ j : ℝ) : ℂ) *
        fourier (T := 1) (-j) ξ‖ := norm_sum_le T _
    calc ‖S‖ ≤ ∑ j ∈ T, ‖((Work.Analysis.Hilbert.triKernel ℓ j : ℝ) : ℂ) *
          fourier (T := 1) (-j) ξ‖ := h1
      _ ≤ ∑ _j ∈ T, ((2:ℝ)^ℓ)⁻¹ := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            rw [norm_mul, Complex.norm_real,
              Real.norm_of_nonneg (Work.Analysis.Hilbert.triKernel_nonneg ℓ j),
              show ‖fourier (T := 1) (-j) ξ‖ = 1 from by
                rw [fourier_apply]; exact Circle.norm_coe _, mul_one]
            exact Work.Analysis.Hilbert.triKernel_le ℓ j
      _ = (T.card : ℝ) * ((2:ℝ)^ℓ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * (2:ℝ)^ℓ / (Q : ℝ) + 1) * ((2:ℝ)^ℓ)⁻¹ :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
  have hfinal : (Q : ℝ) * ‖S‖ ≤ 3 := by
    calc (Q : ℝ) * ‖S‖ ≤ (Q : ℝ) * ((2 * (2:ℝ)^ℓ / (Q : ℝ) + 1) * ((2:ℝ)^ℓ)⁻¹) :=
          mul_le_mul_of_nonneg_left hSbound hQposR.le
      _ = 2 + (Q : ℝ) / (2:ℝ)^ℓ := by
            have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQposR
            have hNne : (2:ℝ)^ℓ ≠ 0 := ne_of_gt hNpos
            field_simp
      _ ≤ 3 := by
            have h1 : (Q : ℝ) / (2:ℝ)^ℓ ≤ 1 := by
              rw [div_le_one hNpos]
              exact_mod_cast hQN
            linarith
  exact hfinal

/-! ## Injectivity of the grid map -/

lemma grid_inj {Q : ℕ} (hQ : 0 < Q) :
    Set.InjOn (fun a : ℕ => (((a : ℝ) / (Q : ℝ)) : Circ)) ↑(Finset.range Q) := by
  intro a ha b hb hab
  have hQne : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hQposR : (0:ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have key : ∀ n : ℕ, n ∈ Finset.range Q →
      (n : ℝ) / (Q : ℝ) ∈ Set.Ico (0:ℝ) (0 + 1) := by
    intro n hn
    refine ⟨div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg Q), ?_⟩
    have h : (n : ℝ) / (Q : ℝ) < 1 := by
      rw [div_lt_one hQposR]
      exact_mod_cast (Finset.mem_range.mp hn)
    simpa using h
  have h2 : (a : ℝ) / (Q : ℝ) = (b : ℝ) / (Q : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1:ℝ)) (a := (0:ℝ)) (key a ha) (key b hb)).mp hab
  have h3 : (a : ℝ) = (b : ℝ) := by
    have h4 : (a : ℝ) / (Q : ℝ) * (Q : ℝ) = (b : ℝ) / (Q : ℝ) * (Q : ℝ) := by rw [h2]
    simpa [div_mul_cancel₀ _ hQne] using h4
  exact Nat.cast_injective h3

/-! ## The arithmetic frequency set lies on the `arithQ`-grid -/

lemma iwArithFreqs_subset_grid (ρ : ℝ) (l : ℕ) :
    Work.Analysis.IonescuWainger.iwArithFreqs ρ l ⊆
      (Finset.range (Work.KMTAreas.A7.arithQ ρ l)).image
        (fun a : ℕ => (((a : ℝ) / ((Work.KMTAreas.A7.arithQ ρ l : ℕ) : ℝ)) : Circ)) := by
  intro α hα
  rw [Work.Analysis.IonescuWainger.iwArithFreqs, Finset.mem_biUnion] at hα
  obtain ⟨q, hq, hα⟩ := hα
  rw [Finset.mem_image] at hα
  obtain ⟨a, ha, rfl⟩ := hα
  have ha' : a < q := Finset.mem_range.mp ha
  have hQpos : 0 < Work.KMTAreas.A7.arithQ ρ l := Work.KMTAreas.A7.arithQ_pos ρ l
  have hdvd : q ∣ Work.KMTAreas.A7.arithQ ρ l := by
    have h1 : q ∣ (Work.Analysis.IonescuWainger.iwP ρ l).lcm id := Finset.dvd_lcm hq
    have h2 : (Work.Analysis.IonescuWainger.iwP ρ l).lcm id = Work.KMTAreas.A7.arithQ ρ l := by
      have hpos : 0 < (Work.Analysis.IonescuWainger.iwP ρ l).lcm id := by
        have hh := Work.Analysis.IonescuWainger.iwQl_pos (ρ := ρ) (l := l)
        rw [Work.Analysis.IonescuWainger.iwQl] at hh
        exact hh
      rw [Work.KMTAreas.A7.arithQ]
      omega
    rwa [h2] at h1
  obtain ⟨k, hk⟩ := hdvd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      rw [h0, mul_zero] at hk
      exact absurd hk (ne_of_gt hQpos)
    · exact h0
  have hqne : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Work.Analysis.IonescuWainger.ne_zero_of_mem_iwP hq)
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
  refine Finset.mem_image.mpr ⟨a * k, Finset.mem_range.mpr ?_, ?_⟩
  · rw [hk]
    exact Nat.mul_lt_mul_of_pos_right ha' hkpos
  · have hreal : (((a * k : ℕ) : ℝ)) / ((Work.KMTAreas.A7.arithQ ρ l : ℕ) : ℝ)
        = (a : ℝ) / (q : ℝ) := by
      rw [hk]; push_cast; field_simp
    rw [hreal]

end

end Work.KMTAreas.A7Hi
