import Mathlib
import Submission.Work.Peluse.Holds.Corrected
import Submission.Work.Peluse.LadderQ.Lemma51Defs

set_option autoImplicit false

/-! LEAD-FROZEN (curric-46, 2026-10-03): power-loss replacement for the refuted constant-loss ladder.
Design: Submission/Work/Peluse/LADDER_STEP_LEAD.md. Do not edit. The open nodes P1–P5 are separate requests. -/

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section
open Work.Peluse

/-- Peluse Lemma 5.1 at level `t`, power loss, with explicit window smallness, `M₂`-nondegeneracy
and the gcd/size exceptional set (all indices). -/
def lemma51P (t : ℕ) : Prop := by
  classical
  exact
  ∀ B₀ : ℕ, ∃ s' : ℕ, 1 ≤ s' ∧ ∃ e : ℕ, 1 ≤ e ∧ ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
  ∀ (c : ℤ) (M₁ M₂ N D : ℕ) (b : Fin t → ℤ) (γ η ε : ℝ) (f : ℤ → ℂ),
    0 < c → 2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ)) → 1 ≤ D →
    (∀ i : Fin t, |b i| ≤ (B₀ : ℤ) * (M₁ : ℤ)) →
    SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
    0 < γ → γ ≤ 1 → 0 < η → η ≤ C * γ ^ e → 0 ≤ ε → ε ≤ C * γ ^ e →
    (D : ℝ) ≤ C * (γ * η) ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) →
    ((M₁ : ℝ) * (M₂ : ℝ)) ^ e ≤ C * (γ * η * (D : ℝ)) ^ e * (M₂ : ℝ) →
    (((Finset.Icc 1 M₁).filter (fun a : ℕ =>
        ¬ ((∀ i k : Fin t, i ≠ k →
              ((Int.gcd ((a : ℤ) + b i) ((a : ℤ) + b k) : ℕ) : ℝ) ≤ 1 / η)
            ∧ ∀ i : Fin t, η * (M₁ : ℝ) ≤ ((|(a : ℤ) + b i| : ℤ) : ℝ)))).card : ℝ)
      ≤ ε * (M₁ : ℝ) →
    γ ≤ LadderQ.boxAvgA t c M₁ M₂ b N f →
    C * γ ^ e ≤ uNorm s' (arithIcc c D) (symIcc N) f

/-- One ladder step = Peluse Lemma 5.6 at `s = j+1`, power loss, `n` long slots carried. -/
def ladderStepP (j : ℕ) : Prop :=
  ∀ n : ℕ, ∃ s' : ℕ, 1 ≤ s' ∧ ∃ e : ℕ, 1 ≤ e ∧ ∃ C : ℝ, 0 < C ∧ C ≤ 1 ∧
  ∀ (c : ℤ) (M₁ L D N : ℕ) (f : ℤ → ℂ) (u : ℝ),
    0 < c → 2 ≤ L → L ≤ M₁ → 1 ≤ N → ((M₁ : ℝ) * (L : ℝ) ≤ (N : ℝ) / (c : ℝ)) → 1 ≤ D →
    SupportIn f N → (∀ z : ℤ, ‖f z‖ ≤ 1) →
    0 < u → u ≤ 1 →
    (D : ℝ) ≤ C * u ^ e * ((M₁ : ℝ) * (L : ℝ)) →
    ((M₁ : ℝ) * (L : ℝ)) ^ e ≤ C * (u * (D : ℝ)) ^ e * (L : ℝ) →
    u ≤ boxLadderNorm (j + 1) n M₁ c (Holds.omegaOf (j + 1)) L D N f →
    C * u ^ e ≤ boxLadderNorm j (n + s') M₁ c (Holds.omegaOf j) L D N f

/-- `ConcatBridgeShortA` with the input exponent `K₁` decoupled from the window exponent `K`. -/
def ConcatBridgeShortB : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∀ C₁ : ℝ, 0 < C₁ → ∀ K₁ : ℕ, 1 ≤ K₁ →
    ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ K₀ : ℕ, 1 ≤ K₀ ∧
    ∀ (c : ℤ), 0 < c → ∀ K : ℕ, K₀ ≤ K →
      ∀ (N M₁ M₂ : ℕ) (γ γ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < γ → γ ≤ 1 → 0 < γ' → A * γ' ≤ γ ^ K → A ≤ (M₂ : ℝ) * (γ * γ') ^ K →
        (∃ ωOf : Fin (2 ^ s - 1) → (Fin s → Bool),
          Function.Injective ωOf ∧ (∀ i : Fin (2 ^ s - 1), ωOf i ≠ 0) ∧
          C₁ * γ ^ K₁ ≤ Concat.boxAvg s M₁ c ωOf (⌊γ' * (M₂ : ℝ)⌋).toNat N f) →
        C * (γ * γ') ^ K ≤
          uNorm s' (arithIcc c (⌊γ' * γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc N) f

/-- B is a weakening of the frozen A (sanity check of the direction). -/
theorem concatBridgeShortB_of_A (h : C46.ConcatBridgeShortA) : ConcatBridgeShortB := by
  intro s hs C₁ hC₁ K₁ hK₁
  obtain ⟨s', hs', C, hC, A, hA, K₀, hK₀, H⟩ := h s hs C₁ hC₁
  refine ⟨s', hs', C, hC, A, hA, max K₀ K₁, le_trans hK₀ (le_max_left _ _), ?_⟩
  intro c hc K hK N M₁ M₂ γ γ' f h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hbox
  refine H c hc K (le_trans (le_max_left _ _) hK) N M₁ M₂ γ γ' f h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 ?_
  obtain ⟨ω, hω1, hω2, hb⟩ := hbox
  refine ⟨ω, hω1, hω2, le_trans ?_ hb⟩
  have : γ ^ K ≤ γ ^ K₁ := pow_le_pow_of_le_one h7.le h8 (le_trans (le_max_right _ _) hK)
  exact mul_le_mul_of_nonneg_left this hC₁.le

theorem peluseConcatFixed_of_shortsB (hA : C46.ExpansionPETShortA) (hB : ConcatBridgeShortB) :
    UControl.PeluseConcatFixed := by
  intro Cnn s hs
  obtain ⟨CA, hCApos, AE, hAE1, K0E, hK0E1, hA'⟩ := hA s hs Cnn
  obtain ⟨s', hs'2, CB, hCBpos, AB, hAB1, K0B, hK0B1, hB'⟩ := hB s hs CA hCApos K0E hK0E1
  refine ⟨s', by omega, CB, hCBpos, (max AE AB) ^ 2, ?_, 2 * max K0E K0B, ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max AE AB := le_trans hAE1 (le_max_left AE AB)
    have h2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) h1 2
    simpa using h2
  · have h1 : 1 ≤ max K0E K0B := le_trans hK0E1 (le_max_left K0E K0B)
    have h2 : max K0E K0B ≤ 2 * max K0E K0B := Nat.le_mul_of_pos_left _ (by norm_num)
    exact le_trans h1 h2
  · intro c hc N M₁ M₂ d δ δ' f hM2 hM21 hN hNM hb hsup hbd hδ0 hδ1 hδ'0 hfixA hfixA2 hbox
    set K : ℕ := max K0E K0B with hK
    have hKE : K0E ≤ K := by rw [hK]; exact le_max_left _ _
    have hKB : K0B ≤ K := by rw [hK]; exact le_max_right _ _
    have hAmax1 : (1 : ℝ) ≤ max AE AB := le_trans hAE1 (le_max_left AE AB)
    have hA1 : (1 : ℝ) ≤ (max AE AB) ^ 2 := by
      have h2 := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hAmax1 2
      simpa using h2
    have hAmax_sq : max AE AB ≤ (max AE AB) ^ 2 := by nlinarith [hAmax1]
    -- `δ' ≤ 1`
    have hδ'1 : δ' ≤ 1 := by
      have h2 : δ' ≤ (max AE AB) ^ 2 * δ' := by
        calc δ' = 1 * δ' := (one_mul δ').symm
          _ ≤ (max AE AB) ^ 2 * δ' := mul_le_mul_of_nonneg_right hA1 (le_of_lt hδ'0)
      have h3 : δ ^ (2 * K) ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
      linarith
    -- the square-root bookkeeping
    have hsqa : ((max AE AB) * Real.sqrt δ') ^ 2 = (max AE AB) ^ 2 * δ' := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hδ'0)]
    have hsqb : (δ ^ K) ^ 2 = δ ^ (2 * K) := by
      rw [← pow_mul, Nat.mul_comm K 2]
    have hmax : (max AE AB) * Real.sqrt δ' ≤ δ ^ K := by
      have hsqmax : ((max AE AB) * Real.sqrt δ') ^ 2 ≤ (δ ^ K) ^ 2 := by
        rw [hsqa, hsqb]
        exact hfixA
      have hna : 0 ≤ (max AE AB) * Real.sqrt δ' :=
        mul_nonneg (le_trans zero_le_one hAmax1) (Real.sqrt_nonneg _)
      have hnb : 0 ≤ δ ^ K := pow_nonneg (le_of_lt hδ0) K
      have h1 : |(max AE AB) * Real.sqrt δ'| ≤ |δ ^ K| := sq_le_sq.mp hsqmax
      rwa [abs_of_nonneg hna, abs_of_nonneg hnb] at h1
    -- `δ' ≤ √δ'` and `(δδ')² ≤ δ√δ'`
    have hsle : δ' ≤ Real.sqrt δ' := by
      have h : Real.sqrt (δ' ^ 2) ≤ Real.sqrt δ' :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (le_of_lt hδ'0)] at h
    have hsle2 : δ' ^ 2 ≤ Real.sqrt δ' := le_trans (by nlinarith) hsle
    have hbase : (δ * δ') ^ 2 ≤ δ * Real.sqrt δ' := by
      have hδsq : δ ^ 2 ≤ δ := by nlinarith
      have e : (δ * δ') ^ 2 = δ ^ 2 * δ' ^ 2 := by ring
      rw [e]
      calc δ ^ 2 * δ' ^ 2 ≤ δ * δ' ^ 2 :=
            mul_le_mul_of_nonneg_right hδsq (by positivity)
        _ ≤ δ * Real.sqrt δ' := mul_le_mul_of_nonneg_left hsle2 (le_of_lt hδ0)
    have h3 : (δ * δ') ^ (2 * K) ≤ (δ * Real.sqrt δ') ^ K := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) hbase K
    -- the two conditions, uniformly in the constant `x ≤ max A_E A_B`
    have key1 : ∀ x : ℝ, x ≤ max AE AB → x * Real.sqrt δ' ≤ δ ^ K := fun x hx =>
      le_trans (mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _)) hmax
    have key2 : ∀ x : ℝ, x ≤ max AE AB → x ≤ (M₂ : ℝ) * (δ * Real.sqrt δ') ^ K := by
      intro x hx
      have hx1 : x ≤ (max AE AB) ^ 2 := le_trans hx hAmax_sq
      have hx2 : x ≤ (M₂ : ℝ) * (δ * δ') ^ (2 * K) := le_trans hx1 hfixA2
      exact le_trans hx2 (mul_le_mul_of_nonneg_left h3 (by positivity))
    -- the expansion half at `δ'_E = √δ'`
    have hpE : δ ^ K ≤ δ ^ K0E := pow_le_pow_of_le_one hδ0.le hδ1 hKE
    have hsq1 : Real.sqrt δ' ≤ 1 := Real.sqrt_le_one.mpr hδ'1
    have hpE2 : (δ * Real.sqrt δ') ^ K ≤ (δ * Real.sqrt δ') ^ K0E :=
      pow_le_pow_of_le_one (by positivity) (by nlinarith [Real.sqrt_nonneg δ']) hKE
    obtain ⟨ωOf, hinj, hne, hboxAvg⟩ :=
      hA' c hc K0E le_rfl N M₁ M₂ d δ (Real.sqrt δ') f hM2 hM21 hN hNM hb hsup hbd hδ0 hδ1
        (Real.sqrt_pos.mpr hδ'0) (le_trans (key1 AE (le_max_left _ _)) hpE)
        (le_trans (key2 AE (le_max_left _ _)) (mul_le_mul_of_nonneg_left hpE2 (by positivity))) hbox
    -- the bridge half at `γ = δ`, `γ' = √δ'`
    have hbr := hB' c hc K hKB N M₁ M₂ δ (Real.sqrt δ') f hM2 hM21 hN hNM hsup hbd hδ0 hδ1
      (Real.sqrt_pos.mpr hδ'0) (key1 AB (le_max_right _ _)) (key2 AB (le_max_right _ _))
      ⟨ωOf, hinj, hne, hboxAvg⟩
    have hwin : (Int.floor (Real.sqrt δ' * Real.sqrt δ' * (M₁ : ℝ) * (M₂ : ℝ))).toNat
        = (Int.floor (δ' * (M₁ : ℝ) * (M₂ : ℝ))).toNat := by
      congr 1
      rw [← sq, Real.sq_sqrt (le_of_lt hδ'0)]
    rw [hwin] at hbr
    exact le_trans (mul_le_mul_of_nonneg_left h3 hCBpos.le) hbr


end
end Work.Peluse.LadderP
