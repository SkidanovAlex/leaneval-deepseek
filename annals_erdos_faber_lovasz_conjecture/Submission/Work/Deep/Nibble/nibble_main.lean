import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.nibble_defs
import Submission.Work.Deep.Nibble.nibble_round2
import Submission.Work.Deep.Nibble.bj_talagrand
import Submission.Work.Deep.Nibble.nibble_state
import Submission.Work.Deep.Nibble.nibble_round_lemmas
import Submission.Work.Deep.Nibble.nibble_step
import Submission.Work.Deep.Nibble.nibble_iter
import Submission.Work.Deep.Nibble.log_one_sub_bound

set_option maxHeartbeats 8000000

namespace Work.Deep.Nibble



open scoped BigOperators

/-! ## Arithmetic helpers for the iteration -/

/-- The expected level is at most a factor `exp (-(2(r-1)θ))` below the current level. -/
theorem rPred_ge {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) {L : ℕ}
    (hL : 1 ≤ L) : (L : ℝ) * Real.exp (-(2 * ((r : ℝ) - 1) * θ)) ≤ rPred r θ L := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hx1 : θ / (L : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hLpos]
    have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hx0 : 0 ≤ θ / (L : ℝ) := div_nonneg hθ0.le hLpos.le
  have hbase : (0 : ℝ) < 1 - θ / (L : ℝ) := by linarith
  have hlog : -(2 * (θ / (L : ℝ)) * (((r - 1) * (L - 1) : ℕ) : ℝ)) ≤
      (((r - 1) * (L - 1) : ℕ) : ℝ) * Real.log (1 - θ / (L : ℝ)) := by
    have h1 : -(2 * (θ / (L : ℝ))) ≤ Real.log (1 - θ / (L : ℝ)) := by
      have := log_one_sub_bound hx0 hx1
      linarith
    have h2 : (0 : ℝ) ≤ (((r - 1) * (L - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 h2]
  have hmain : Real.exp (-(2 * (θ / (L : ℝ)) * (((r - 1) * (L - 1) : ℕ) : ℝ))) ≤
      (1 - θ / (L : ℝ)) ^ ((r - 1) * (L - 1)) := by
    rw [← Real.exp_log (pow_pos hbase _), Real.log_pow]
    exact Real.exp_le_exp.mpr hlog
  have hexp : -(2 * ((r : ℝ) - 1) * θ) ≤ -(2 * (θ / (L : ℝ)) * (((r - 1) * (L - 1) : ℕ) : ℝ)) := by
    have h3 : (θ / (L : ℝ)) * (((r - 1) * (L - 1) : ℕ) : ℝ) ≤ θ * ((r : ℝ) - 1) := by
      have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ r)]; norm_num
      have hL1 : ((L - 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.sub_le L 1
      have h5 : (((r - 1) * (L - 1) : ℕ) : ℝ) ≤ ((r : ℝ) - 1) * (L : ℝ) := by
        calc (((r - 1) * (L - 1) : ℕ) : ℝ)
            = ((r - 1 : ℕ) : ℝ) * ((L - 1 : ℕ) : ℝ) := by push_cast; ring
          _ = ((r : ℝ) - 1) * ((L - 1 : ℕ) : ℝ) := by rw [hr1]
          _ ≤ ((r : ℝ) - 1) * (L : ℝ) := by
              exact mul_le_mul_of_nonneg_left hL1 (by
                have : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
                linarith)
      calc (θ / (L : ℝ)) * (((r - 1) * (L - 1) : ℕ) : ℝ)
          ≤ (θ / (L : ℝ)) * (((r : ℝ) - 1) * (L : ℝ)) :=
            mul_le_mul_of_nonneg_left h5 (div_nonneg hθ0.le hLpos.le)
        _ = θ * ((r : ℝ) - 1) := by field_simp
    linarith [h3]
  calc (L : ℝ) * Real.exp (-(2 * ((r : ℝ) - 1) * θ))
      ≤ (L : ℝ) * Real.exp (-(2 * (θ / (L : ℝ)) * (((r - 1) * (L - 1) : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hLpos.le
    _ ≤ (L : ℝ) * (1 - θ / (L : ℝ)) ^ ((r - 1) * (L - 1)) :=
        mul_le_mul_of_nonneg_left hmain hLpos.le
    _ = rPred r θ L := by rw [rPred]

theorem nextD_ge {r : ℕ} {θ : ℝ} {D : ℕ} {ε' : ℝ} :
    (1 - 3 * ε') * rPred r θ D ≤ (nextD r θ D ε' : ℝ) := by
  rw [nextD]
  exact Nat.le_ceil _

theorem nextD_le {r : ℕ} {θ : ℝ} {D : ℕ} {ε' : ℝ}
    (h : 0 ≤ (1 - 3 * ε') * rPred r θ D) :
    (nextD r θ D ε' : ℝ) ≤ (1 - 3 * ε') * rPred r θ D + 1 := by
  rw [nextD]
  exact le_of_lt (Nat.ceil_lt_add_one h)

theorem rPred_pos {r : ℕ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) {D : ℕ} (hD : 1 ≤ D) :
    0 < rPred r θ D := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  rw [rPred]
  refine mul_pos hDpos (pow_pos ?_ _)
  rw [sub_pos, div_lt_one hDpos]
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  linarith

theorem one_add_mul_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  have := Real.add_one_le_exp x
  linarith

theorem div_le_div_iff' {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  have h1 : a / b ≤ c / d ↔ a / b * (b*d) ≤ c / d * (b*d) := by
    constructor
    · intro h; exact mul_le_mul_of_nonneg_right h (by positivity)
    · intro h; exact le_of_mul_le_mul_right h (by positivity : (0:ℝ) < b*d)
  rw [h1]
  rw [show a/b*(b*d) = a*d by field_simp, show c/d*(b*d) = c*b by field_simp]

variable {n : ℕ}

/-- Helper: `deg` on `univ` is `hd`. -/
theorem mul_ge_one {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have h := mul_le_mul ha hb (by norm_num : (0:ℝ) ≤ 1) (le_trans zero_le_one ha)
  simpa using h

theorem nibble_main (r : ℕ) (hr : 2 ≤ r) {γ : ℝ} (hγ0 : 0 < γ) :
    ∃ κ D₀ : ℝ, 0 < κ ∧ 0 < D₀ ∧
      ∀ (n : ℕ) (𝓗 : Set (Set (Fin n))) (D : ℕ),
        Work.Deep.Nibble.HLin 𝓗 → Work.Deep.Nibble.HUnif 𝓗 r → D₀ ≤ (D : ℝ) →
        (∀ v : Fin n, |((Work.Deep.Nibble.hd 𝓗 v : ℝ)) - (D : ℝ)| ≤ κ * (D : ℝ)) →
        ∃ M : Set 𝓗, (∀ e f : 𝓗, e ∈ M → f ∈ M → e ≠ f →
            Disjoint ((e : 𝓗) : Set (Fin n)) ((f : 𝓗) : Set (Fin n))) ∧
          (((Set.univ : Set (Fin n)) \ ⋃ e ∈ M, ((e : 𝓗) : Set (Fin n))).ncard : ℝ)
            ≤ γ * (n : ℝ) := by
  classical
  by_cases hγge : 1 ≤ γ
  · -- trivial case: γ ≥ 1
    refine ⟨1/2, 1, by norm_num, by norm_num, ?_⟩
    intro n 𝓗 D hl hu hD hdeg
    refine ⟨∅, ?_, ?_⟩
    · intro e f he hf hne
      rw [Set.mem_empty_iff_false] at he
      exact absurd he not_false
    · have h1 : ((Set.univ : Set (Fin n)) \ ⋃ e ∈ (∅ : Set 𝓗), ((e : 𝓗) : Set (Fin n)))
          = Set.univ := by
        rw [Set.biUnion_empty, Set.sdiff_empty]
      rw [h1, Set.ncard_univ]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      nlinarith
  · -- main case
    have hγ1 : γ < 1 := not_le.mp hγge
    have hr0 : (0:ℝ) ≤ (r:ℝ) := Nat.cast_nonneg r
    have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    set θ : ℝ := min (1/100) (γ/(20*((r:ℝ)+1))) with hθdef
    have hθ0 : 0 < θ := by
      rw [hθdef]; exact lt_min (by norm_num) (by positivity)
    have hθ1 : θ ≤ 1/100 := by rw [hθdef]; exact min_le_left _ _
    have hθle : θ ≤ γ/(20*((r:ℝ)+1)) := by rw [hθdef]; exact min_le_right _ _
    have hrθ : (r:ℝ)*θ ≤ γ/20 := by
      have h2 : θ ≤ γ/20 := by
        have h1 : γ/(20*((r:ℝ)+1)) ≤ γ/20 := by
          have hpos : (0:ℝ) < 20*((r:ℝ)+1) := by linarith
          have hnonneg : (0:ℝ) ≤ γ * ((r:ℝ)/(20*((r:ℝ)+1))) := by positivity
          have he : γ/(20*((r:ℝ)+1)) = γ/20 - γ * ((r:ℝ)/(20*((r:ℝ)+1))) := by
            field_simp
            ring
          rw [he]
          linarith
        linarith [hθle, h1]
      have h3 : (r:ℝ)*θ ≤ (r:ℝ)*(γ/(20*((r:ℝ)+1))) := mul_le_mul_of_nonneg_left hθle hr0
      have h4 : (r:ℝ)*(γ/(20*((r:ℝ)+1))) ≤ γ/20 := by
        have h : (r:ℝ)*(γ/(20*((r:ℝ)+1))) = ((r:ℝ)*γ)/(20*((r:ℝ)+1)) := by ring
        rw [h, div_le_iff₀ (by positivity : (0:ℝ) < 20*((r:ℝ)+1))]
        nlinarith [hγ0.le, hr0]
      linarith
    set L : ℝ := Real.log (2/γ) + 2 with hLdef
    have hL2 : 1 ≤ L := by
      have h2 : 1 < 2/γ := by rw [lt_div_iff₀ hγ0]; linarith
      have h3 : 0 < Real.log (2/γ) := Real.log_pos h2
      rw [hLdef]; linarith
    have hLpos : 0 < L := by linarith [hL2]
    set δ : ℝ := θ/(1000*L) with hδdef
    have hδ0 : 0 < δ := by rw [hδdef]; positivity
    have hδθ : 2*δ ≤ θ/2 := by
      rw [hδdef]
      have h1 : θ/(1000*L) ≤ θ/4 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 1000*L)]
        nlinarith [hθ0.le, hL2]
      linarith
    have hδ1 : δ ≤ θ/100 := by
      rw [hδdef, div_le_iff₀ (by positivity : (0:ℝ) < 1000*L)]
      nlinarith [hθ0.le, hL2]
    set T : ℕ := ⌈L/θ⌉₊ + 1 with hTdef
    have hT1 : 1 ≤ T := by rw [hTdef]; omega
    have hTθ : L ≤ (T:ℝ)*θ := by
      have h1 : L/θ ≤ (T:ℝ) := by
        rw [hTdef]; push_cast
        exact le_trans (Nat.le_ceil _) (by linarith)
      exact (div_le_iff₀ hθ0).mp h1
    have hTθ' : (T:ℝ)*θ ≤ L + 2*θ := by
      have h1 : (↑(⌈L/θ⌉₊) : ℝ) < L/θ + 1 := Nat.ceil_lt_add_one (div_nonneg hLpos.le hθ0.le)
      rw [hTdef]; push_cast
      have h2 : L/θ*θ = L := by field_simp
      nlinarith
    set Cc : ℝ := 800*(1 + (r:ℝ)*θ) with hCcdef
    have hCc1 : 1 ≤ Cc := by rw [hCcdef]; nlinarith [hr0, hθ0.le]
    have hCcpos : 0 < Cc := lt_of_lt_of_le (by norm_num) hCc1
    set ε0 : ℝ := δ/(8*Cc^T) with hε0def
    have hε0pos : 0 < ε0 := by rw [hε0def]; positivity
    set εs : ℕ → ℝ := fun j => ε0 * Cc^j with hεsdef
    set εs' : ℕ → ℝ := fun j => 100*(1 + (r:ℝ)*θ)*εs j with hεs'def
    have ha_pos : (0:ℝ) ≤ 2*((r:ℝ)-1)*θ := by positivity
    have hεs0 : εs 0 = ε0 := by rw [hεsdef]; simp
    have hεs_eq : ∀ j, εs (j+1) = 8*εs' j := by
      intro j
      have h1 : εs (j+1) = ε0*Cc^(j+1) := by rw [hεsdef]
      have h2 : εs' j = 100*(1+(r:ℝ)*θ)*(ε0*Cc^j) := by rw [hεs'def, hεsdef]
      rw [h1, h2, pow_succ, hCcdef]
      ring
    have hεs_pos : ∀ j, 0 < εs j := by
      intro j
      show 0 < ε0 * Cc^j
      exact mul_pos hε0pos (pow_pos hCcpos j)
    have hεs_mono : ∀ {j k : ℕ}, j ≤ k → εs j ≤ εs k := by
      intro j k hjk
      show ε0 * Cc^j ≤ ε0 * Cc^k
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hCc1 hjk) hε0pos.le
    have hεs_T : εs (T-1) = δ/(8*Cc) := by
      have h1 : εs (T-1) = ε0*Cc^(T-1) := by rw [hεsdef]
      have h2 : Cc^T = Cc^(T-1)*Cc := by
        rw [← pow_succ, Nat.sub_add_cancel hT1]
      rw [h1, hε0def, h2]
      field_simp
    have hεs_le : ∀ j, j < T → εs j ≤ δ/8 := by
      intro j hj
      calc εs j ≤ εs (T-1) := hεs_mono (by omega)
        _ = δ/(8*Cc) := hεs_T
        _ ≤ δ/8 := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 8*Cc)]
            nlinarith [hδ0.le, hCc1]
    have hεsδ : ∀ j, j < T → 4*εs j ≤ δ := by
      intro j hj
      have h := hεs_le j hj
      linarith
    have hεs_θ : ∀ j, j < T → εs j ≤ θ/100 := by
      intro j hj
      have h1 := hεs_le j hj
      have h2 : δ/8 ≤ θ/100 := by
        rw [hδdef, div_le_iff₀ (by positivity : (0:ℝ) < 8),
          div_le_iff₀ (by positivity : (0:ℝ) < 1000*L)]
        nlinarith [hθ0.le, hL2, hθ1]
      linarith
    have hεs'pos : ∀ j, 0 < εs' j := by
      intro j; rw [hεs'def]
      exact mul_pos (mul_pos (by norm_num) (by positivity)) (hεs_pos j)
    have hεs'2 : ∀ j, 100*(εs j + εs j*(r:ℝ)*θ) ≤ εs' j := by
      intro j; rw [hεs'def]; nlinarith [hεs_pos j]
    have hεs'_le : ∀ j, j < T → εs' j ≤ δ/64 := by
      intro j hj
      have h1 : εs j ≤ εs (T-1) := hεs_mono (by omega)
      have h2 : (100:ℝ)*(1+(r:ℝ)*θ)*εs (T-1) = δ/64 := by
        rw [hεs_T, hCcdef]
        field_simp
        ring
      rw [hεs'def]
      calc 100*(1+(r:ℝ)*θ)*εs j ≤ 100*(1+(r:ℝ)*θ)*εs (T-1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = δ/64 := h2
    have hεs'half : ∀ j, j < T → εs' j ≤ 1/2 := by
      intro j hj
      have h := hεs'_le j hj
      have h2 : δ/64 ≤ 1/2 := by
        rw [hδdef, div_le_iff₀ (by positivity : (0:ℝ) < 64),
          div_le_iff₀ (by positivity : (0:ℝ) < 1000*L)]
        nlinarith [hθ0.le, hL2, hθ1]
      linarith
    have hεs'six : ∀ j, j < T → εs' j ≤ 1/6 := by
      intro j hj
      have h := hεs'_le j hj
      have h2 : δ/64 ≤ 1/6 := by
        rw [hδdef, div_le_iff₀ (by positivity : (0:ℝ) < 64),
          div_le_iff₀ (by positivity : (0:ℝ) < 1000*L)]
        nlinarith [hθ0.le, hL2, hθ1]
      linarith
    -- the contraction factor
    set lam : ℝ := (1 + 2*δ) * Real.exp (-θ) with hlamdef
    have hlam0 : 0 ≤ lam := by rw [hlamdef]; positivity
    have hlam_T : lam^T ≤ γ/2 := by
      have h1 : lam ≤ Real.exp (2*δ - θ) := by
        rw [hlamdef]
        calc (1+2*δ)*Real.exp (-θ) ≤ Real.exp (2*δ)*Real.exp (-θ) :=
              mul_le_mul_of_nonneg_right (one_add_mul_le_exp (2*δ)) (Real.exp_pos _).le
          _ = Real.exp (2*δ - θ) := by rw [← Real.exp_add]; ring_nf
      have h2 : lam^T ≤ Real.exp ((T:ℝ)*(2*δ-θ)) := by
        calc lam^T ≤ (Real.exp (2*δ-θ))^T := pow_le_pow_left₀ hlam0 h1 T
          _ = Real.exp ((T:ℝ)*(2*δ-θ)) := (Real.exp_nat_mul (2*δ-θ) T).symm
      have hT : L/θ ≤ (T:ℝ) := by
        rw [hTdef]; push_cast
        exact le_trans (Nat.le_ceil _) (by linarith)
      have hneg : 2*δ - θ ≤ 0 := by linarith [hδθ]
      have h3 : (T:ℝ)*(2*δ-θ) ≤ 1/500 - L := by
        have h1 : (0:ℝ) ≤ -(2*δ-θ) := by linarith [hneg]
        have h2 := mul_le_mul_of_nonneg_right hT h1
        have h5 : (L/θ)*(2*δ-θ) = 1/500 - L := by
          rw [hδdef]
          field_simp
          ring
        have h4 : (T:ℝ)*(2*δ-θ) ≤ (L/θ)*(2*δ-θ) := by
          have e1 : (L/θ)*(2*δ-θ) = -((L/θ)*(-(2*δ-θ))) := by ring
          have e2 : (T:ℝ)*(2*δ-θ) = -((T:ℝ)*(-(2*δ-θ))) := by ring
          rw [e1, e2]
          linarith [h2]
        linarith
      have h6 : Real.exp ((T:ℝ)*(2*δ-θ)) ≤ Real.exp (1/500 - L) := Real.exp_le_exp.mpr h3
      have h7 : Real.exp (1/500 - L) ≤ γ/2 := by
        have h9 : Real.exp (-L) = (γ/2) * Real.exp (-2) := by
          rw [Real.exp_neg, hLdef, Real.exp_add, Real.exp_log (by positivity : (0:ℝ) < 2/γ),
            Real.exp_neg, mul_inv, inv_div]
        calc Real.exp (1/500 - L) = Real.exp (1/500) * Real.exp (-L) := by
              rw [← Real.exp_add]; ring_nf
          _ = Real.exp (1/500) * ((γ/2) * Real.exp (-2)) := by rw [h9]
          _ = (Real.exp (1/500) * Real.exp (-2)) * (γ/2) := by ring
          _ ≤ 1 * (γ/2) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [← Real.exp_add, Real.exp_le_one_iff]
              norm_num
          _ = γ/2 := by ring
      linarith
    have h1mlam : θ/4 ≤ 1 - lam := by
      rw [hlamdef]
      have h1 : (1+2*δ)*Real.exp (-θ) ≤ Real.exp (2*δ - θ) := by
        calc (1+2*δ)*Real.exp (-θ) ≤ Real.exp (2*δ)*Real.exp (-θ) :=
              mul_le_mul_of_nonneg_right (one_add_mul_le_exp (2*δ)) (Real.exp_pos _).le
          _ = Real.exp (2*δ - θ) := by rw [← Real.exp_add]; ring_nf
      have h2 : Real.exp (2*δ - θ) ≤ Real.exp (-θ/2) := Real.exp_le_exp.mpr (by linarith [hδθ])
      have h3 : Real.exp (-θ/2) ≤ 1 - θ/4 := by
        have hx : (0:ℝ) ≤ θ/4 := by linarith [hθ0.le]
        have hx1 : θ/4 ≤ 1/2 := by linarith [hθ1]
        have hlog : -2*(θ/4) ≤ Real.log (1 - θ/4) := log_one_sub_bound hx hx1
        rw [← Real.exp_log (by linarith [hθ0.le] : (0:ℝ) < 1 - θ/4)]
        exact Real.exp_le_exp.mpr (by linarith)
      linarith
    -- the level sequence
    set κ : ℝ := ε0/8 with hκdef
    have hκ0 : 0 < κ := by rw [hκdef]; positivity
    -- the round thresholds
    have hround0 : ∀ j, j < T → ∃ Dmin : ℕ, 1 ≤ Dmin ∧
        ∀ {V : Type} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (D' : ℕ),
          Dmin ≤ D' → D' ≤ Fintype.card V → HLin 𝓖 → HUnif 𝓖 r →
          (∀ v : V, |((hd 𝓖 v : ℝ)) - (D' : ℝ)| ≤ εs j * (D' : ℝ)) →
          ∃ ω : 𝓖 → Bool, RoundGood 𝓖 r D' θ δ (εs' j) (rPred r θ D') ω := by
      intro j hj
      exact nibble_round2 hr hθ0 hθ1 hδ0 hδ1 (hεs'pos j) (hεs'half j hj) (hεs'2 j)
        (hεs_pos j) (hεs_θ j hj) (hεsδ j hj)
    let DminOf : ℕ → ℕ := fun j => if hj : j < T then (hround0 j hj).choose else 0
    set Dmax : ℕ := (Finset.range T).sup DminOf with hDmaxdef
    set Dthr : ℝ := ((Dmax : ℝ) + 1/ε0 + 1) * (2:ℝ)^(T+1) *
      (Real.exp (2*((r:ℝ)-1)*θ))^(T+1) * 16 with hDthrdef
    refine ⟨κ, Dthr, hκ0, ?_, ?_⟩
    · rw [hDthrdef]
      have h1 : (0:ℝ) < 1/ε0 := by positivity
      have h2 : (0:ℝ) < (Dmax : ℝ) + 1/ε0 + 1 := by
        have h3 : (0:ℝ) ≤ (Dmax : ℝ) := Nat.cast_nonneg Dmax
        linarith
      positivity
    intro n 𝓗 D hl hu hDthr hdeg
    -- per-instance constants
    set D0 : ℕ := ⌊(1 - κ) * (D:ℝ)⌋₊ with hD0def
    set q : ℝ := (1/2) * Real.exp (-(2*((r:ℝ)-1)*θ)) with hqdef
    let lev : ℕ → ℕ := fun j => Nat.rec D0 (fun k lk => nextD r θ lk (εs' k)) j
    have hlev0 : lev 0 = D0 := rfl
    have hlev_succ : ∀ j, lev (j+1) = nextD r θ (lev j) (εs' j) := fun j => rfl
    -- (A) basic level facts
    have hε0_1 : ε0 ≤ 1 := by
      have h1 : ε0 ≤ δ/8 := by
        rw [hε0def, div_le_iff₀ (by positivity : (0:ℝ) < 8*Cc^T)]
        have h2 : (1:ℝ) ≤ Cc^T := one_le_pow₀ hCc1
        nlinarith [hδ0.le, h2]
      have h3 : δ/8 ≤ 1 := by
        rw [hδdef, div_le_iff₀ (by positivity : (0:ℝ) < 8),
          div_le_iff₀ (by positivity : (0:ℝ) < 1000*L)]
        nlinarith [hθ0.le, hL2, hθ1]
      linarith
    have hκ4 : κ ≤ 1/4 := by rw [hκdef]; linarith [hε0_1]
    have hA1 : (1:ℝ) ≤ (Dmax:ℝ) + 1/ε0 + 1 := by
      have h2 : (0:ℝ) ≤ (Dmax:ℝ) := Nat.cast_nonneg Dmax
      have h3 : (0:ℝ) < 1/ε0 := by positivity
      linarith
    have hA0 : (0:ℝ) < (Dmax:ℝ) + 1/ε0 + 1 := by linarith [hA1]
    have hP1 : (1:ℝ) ≤ (2:ℝ)^(T+1) := one_le_pow₀ (by norm_num)
    have hP0 : (0:ℝ) < (2:ℝ)^(T+1) := by positivity
    have hE1 : (1:ℝ) ≤ (Real.exp (2*((r:ℝ)-1)*θ))^(T+1) :=
      one_le_pow₀ (Real.one_le_exp ha_pos)
    have hE0 : (0:ℝ) < (Real.exp (2*((r:ℝ)-1)*θ))^(T+1) := by positivity
    have hDthr_ge : (4:ℝ) ≤ Dthr := by
      rw [hDthrdef]
      have h1 : (1:ℝ) ≤ ((Dmax:ℝ) + 1/ε0 + 1) * (2:ℝ)^(T+1) :=
        mul_ge_one hA1 hP1
      have h2 : (1:ℝ) ≤ ((Dmax:ℝ) + 1/ε0 + 1) * (2:ℝ)^(T+1)
          * (Real.exp (2*((r:ℝ)-1)*θ))^(T+1) := mul_ge_one h1 hE1
      have h3 : (4:ℝ) ≤ ((Dmax:ℝ) + 1/ε0 + 1) * (2:ℝ)^(T+1)
          * (Real.exp (2*((r:ℝ)-1)*θ))^(T+1) * 16 := by
        have h4 : (4:ℝ) ≤ 1 * 16 := by norm_num
        calc (4:ℝ) ≤ 1 * 16 := h4
          _ ≤ (((Dmax:ℝ) + 1/ε0 + 1) * (2:ℝ)^(T+1)
              * (Real.exp (2*((r:ℝ)-1)*θ))^(T+1)) * 16 := by
              exact mul_le_mul_of_nonneg_right h2 (by norm_num)
      exact h3
    have hD4 : (4:ℝ) ≤ (D:ℝ) := by linarith [hDthr_ge, hDthr]
    have hTexp : 2 * (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T ≤ (D:ℝ) := by
      have h5 : (1:ℝ) ≤ Real.exp (2*((r:ℝ)-1)*θ) := Real.one_le_exp ha_pos
      have h2 : 2 * (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T ≤ Dthr := by
        have hP' : (2:ℝ)^(T+1) = 2 * (2:ℝ)^T := by rw [pow_succ']
        have hE' : (Real.exp (2*((r:ℝ)-1)*θ))^(T+1)
            = (Real.exp (2*((r:ℝ)-1)*θ))^T * Real.exp (2*((r:ℝ)-1)*θ) := by rw [pow_succ]
        rw [hDthrdef, hP', hE']
        have hK : (1:ℝ) ≤ ((Dmax:ℝ) + 1/ε0 + 1) * Real.exp (2*((r:ℝ)-1)*θ) * 16 :=
          mul_ge_one (mul_ge_one hA1 h5) (by norm_num)
        have h6 : (0:ℝ) < 2 * (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T := by positivity
        nlinarith [hK, h6]
      linarith [h2, hDthr]
    have hD_big : 16/ε0 ≤ (D:ℝ) := by
      have h2 : 16/ε0 ≤ Dthr := by
        rw [hDthrdef]
        have h3 : (16:ℝ)/ε0 = (1/ε0) * 16 := by ring
        rw [h3]
        have hK : (1:ℝ) ≤ (2:ℝ)^(T+1) * (Real.exp (2*((r:ℝ)-1)*θ))^(T+1) :=
          mul_ge_one hP1 hE1
        have h5 : (0:ℝ) < 1/ε0 := by positivity
        have h6 : (0:ℝ) ≤ (Dmax:ℝ) := Nat.cast_nonneg Dmax
        nlinarith [hK, h5, h6, hP0, hE0]
      linarith [h2, hDthr]
    have hκD : (1:ℝ) ≤ κ * (D:ℝ) := by
      rw [hκdef]
      have h7 : ε0 * (16/ε0) ≤ ε0 * (D:ℝ) := mul_le_mul_of_nonneg_left hD_big hε0pos.le
      have h8 : ε0 * (16/ε0) = 16 := by field_simp
      nlinarith [h7, h8]
    have hD0_1 : (1:ℝ) ≤ (D0:ℝ) := by
      have h1 : (2:ℝ) ≤ (1-κ)*(D:ℝ) := by nlinarith [hκ4, hD4]
      have h2 : (1-κ)*(D:ℝ) - 1 < (D0:ℝ) := by
        have h := Nat.lt_floor_add_one ((1-κ)*(D:ℝ))
        have h3 : (D0:ℝ) = ↑⌊(1-κ)*(D:ℝ)⌋₊ := by rw [hD0def]
        rw [h3]
        linarith
      linarith
    have hD0_le : (D0:ℝ) ≤ (D:ℝ) := by
      have h1 : (0:ℝ) ≤ (1-κ)*(D:ℝ) := by nlinarith [hκ4, hD4]
      have h2 : (D0:ℝ) ≤ (1-κ)*(D:ℝ) := by
        rw [hD0def]
        exact Nat.floor_le h1
      nlinarith [h2, hκ4, hD4]
    have hD0_ge : (1-2*κ)*(D:ℝ) ≤ (D0:ℝ) := by
      have h2 : (1-κ)*(D:ℝ) - 1 < (D0:ℝ) := by
        have h := Nat.lt_floor_add_one ((1-κ)*(D:ℝ))
        have h3 : (D0:ℝ) = ↑⌊(1-κ)*(D:ℝ)⌋₊ := by rw [hD0def]
        rw [h3]
        linarith
      nlinarith [h2, hκD]
    have hD0half : (D:ℝ)/2 ≤ (D0:ℝ) := by nlinarith [hD0_ge, hκ4, hD4]
    have hq0 : 0 < q := by rw [hqdef]; positivity
    have hq1 : q ≤ 1 := by
      rw [hqdef]
      have h1 : Real.exp (-(2*((r:ℝ)-1)*θ)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ha_pos])
      linarith
    have hqK : q^T * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) = 1 := by
      rw [hqdef, mul_pow]
      rw [show (1/2:ℝ) = (2:ℝ)⁻¹ by norm_num, inv_pow]
      rw [← Real.exp_nat_mul]
      rw [show (T:ℝ) * -(2*((r:ℝ)-1)*θ) = -((T:ℝ) * (2*((r:ℝ)-1)*θ)) by ring]
      rw [Real.exp_neg, ← Real.exp_nat_mul]
      field_simp
    have hD0q : ∀ j ≤ T, (1:ℝ) ≤ (D0:ℝ) * q^j := by
      intro j hj
      have h1 : q^T ≤ q^j := pow_le_pow_of_le_one (le_of_lt hq0) hq1 hj
      have h2 : (1:ℝ) ≤ (D0:ℝ) * q^T := by
        have h3 : (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T ≤ (D0:ℝ) := by
          nlinarith [hD0half, hTexp]
        have h3pos : (0:ℝ) < (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T := by positivity
        calc (1:ℝ) = (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T * q^T := by rw [mul_comm, hqK]
          _ ≤ (D0:ℝ) * q^T := by
              exact mul_le_mul_of_nonneg_right h3 (by positivity)
      have h4 : (0:ℝ) ≤ q^j := by positivity
      have h5 : (0:ℝ) ≤ (D0:ℝ) := by linarith [hD0_1]
      nlinarith [h1, h2, h4, h5]
    have hDmax_le : (Dmax:ℝ) ≤ (D0:ℝ) * q^T := by
      have hK2 : (0:ℝ) < (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T := by positivity
      have h1 : (Dmax:ℝ) * 2 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) ≤ (D:ℝ) := by
        have h2 : (Dmax:ℝ) * 2 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) ≤ Dthr := by
          have hP' : (2:ℝ)^(T+1) = 2 * (2:ℝ)^T := by rw [pow_succ']
          have hE' : (Real.exp (2*((r:ℝ)-1)*θ))^(T+1)
              = (Real.exp (2*((r:ℝ)-1)*θ))^T * Real.exp (2*((r:ℝ)-1)*θ) := by rw [pow_succ]
          rw [hDthrdef, hP', hE']
          have h5 : (1:ℝ) ≤ Real.exp (2*((r:ℝ)-1)*θ) := Real.one_le_exp ha_pos
          have h6 : (0:ℝ) ≤ (Dmax:ℝ) := Nat.cast_nonneg Dmax
          have h7 : (0:ℝ) < (2:ℝ)^T := by positivity
          have h8 : (0:ℝ) < (Real.exp (2*((r:ℝ)-1)*θ))^T := by positivity
          have h9 : (0:ℝ) < 1/ε0 := by positivity
          have h16 : (1:ℝ) ≤ Real.exp (2*((r:ℝ)-1)*θ) * 16 := mul_ge_one h5 (by norm_num)
          have h10 : (0:ℝ) ≤ (Dmax:ℝ) + 1/ε0 + 1 := by linarith [hA1]
          have h11 : (0:ℝ) ≤ 2 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) := by positivity
          have h17 : (Dmax:ℝ) ≤ (Dmax:ℝ) + 1/ε0 + 1 := by linarith [h7, h6]
          calc (Dmax:ℝ) * 2 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T)
              ≤ ((Dmax:ℝ) + 1/ε0 + 1) * (2 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T)) := by
                nlinarith [h17, h11]
            _ ≤ ((Dmax:ℝ) + 1/ε0 + 1) * (2 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T))
                * (Real.exp (2*((r:ℝ)-1)*θ) * 16) := by
                have h18 : (0:ℝ) ≤ ((Dmax:ℝ) + 1/ε0 + 1) * (2 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T)) := by positivity
                nlinarith [h16, h18]
            _ = ((Dmax:ℝ) + 1/ε0 + 1) * (2 * (2:ℝ)^T) * ((Real.exp (2*((r:ℝ)-1)*θ))^T * Real.exp (2*((r:ℝ)-1)*θ)) * 16 := by ring
        linarith [h2, hDthr]
      have h4 : (Dmax:ℝ) * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) ≤ (D0:ℝ) := by
        nlinarith [h1, hD0half, hK2]
      calc (Dmax:ℝ) = (Dmax:ℝ) * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T * q^T) := by
            rw [mul_comm ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) (q^T), hqK, mul_one]
        _ = (Dmax:ℝ) * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) * q^T := by ring
        _ ≤ (D0:ℝ) * q^T := mul_le_mul_of_nonneg_right h4 (by positivity)
    have hlev_both : ∀ j : ℕ, j ≤ T → (((D0 : ℝ) * q ^ j ≤ (Nat.cast (lev j) : ℝ)) ∧ ((1 : ℝ) ≤ (Nat.cast (lev j) : ℝ))) := by
      intro j
      induction j with
      | zero =>
        intro hj
        refine ⟨?_, ?_⟩
        · rw [hlev0]; simp
        · rw [hlev0]; exact hD0_1
      | succ j ih =>
        intro hj
        obtain ⟨ih1, ih2⟩ := ih (by omega)
        have hstep : (1/2 : ℝ) * (Nat.cast (lev j) : ℝ) * Real.exp (-(2*((r:ℝ)-1)*θ))
            ≤ (Nat.cast (lev (j+1)) : ℝ) := by
          have h1 : (1 - 3*εs' j) * rPred r θ (lev j) ≤ (Nat.cast (lev (j+1)) : ℝ) := by
            rw [hlev_succ]
            exact nextD_ge
          have h2 : (1/2:ℝ) ≤ 1 - 3*εs' j := by
            have := hεs'six j (by omega)
            linarith
          have h3 : (Nat.cast (lev j) : ℝ) * Real.exp (-(2*((r:ℝ)-1)*θ)) ≤ rPred r θ (lev j) :=
            rPred_ge hr hθ0 hθ1 (by exact_mod_cast ih2)
          have h4 : (0:ℝ) ≤ (Nat.cast (lev j) : ℝ) * Real.exp (-(2*((r:ℝ)-1)*θ)) := by positivity
          nlinarith [h1, h2, h3, h4]
        have hqj : (D0:ℝ) * (q^j * q) ≤ (Nat.cast (lev (j+1)) : ℝ) := by
          calc (D0:ℝ) * (q^j * q) = q * ((D0:ℝ) * q^j) := by ring
            _ ≤ q * (Nat.cast (lev j) : ℝ) :=
                mul_le_mul_of_nonneg_left ih1 (le_of_lt hq0)
            _ = (1/2) * (Nat.cast (lev j) : ℝ) * Real.exp (-(2*((r:ℝ)-1)*θ)) := by rw [hqdef]; ring
            _ ≤ (Nat.cast (lev (j+1)) : ℝ) := hstep
        constructor
        · rw [pow_succ]; exact hqj
        · have h5 : (1:ℝ) ≤ (D0:ℝ) * q^(j+1) := hD0q (j+1) (by omega)
          have h6 : (D0:ℝ) * q^(j+1) ≤ (Nat.cast (lev (j+1)) : ℝ) := by rw [pow_succ]; exact hqj
          exact_mod_cast le_trans h5 h6
    have hlev1 : ∀ j < T, (1:ℕ) ≤ lev j := by
      intro j hj
      exact_mod_cast (hlev_both j (le_of_lt hj)).2
    have hminD : ∀ j < T, DminOf j ≤ lev j := by
      intro j hj
      have h1 : DminOf j ≤ Dmax := by
        rw [hDmaxdef]
        exact Finset.le_sup (Finset.mem_range.mpr hj)
      have h2 : (Dmax:ℝ) ≤ (Nat.cast (lev j) : ℝ) := by
        have h3 : (D0:ℝ) * q^j ≤ (Nat.cast (lev j) : ℝ) := (hlev_both j (le_of_lt hj)).1
        have h4 : q^T ≤ q^j := pow_le_pow_of_le_one (le_of_lt hq0) hq1 (le_of_lt hj)
        have h5 : (0:ℝ) ≤ (D0:ℝ) := by linarith [hD0_1]
        nlinarith [hDmax_le, h3, h4, h5]
      have h1' : ((DminOf j : ℕ) : ℝ) ≤ (Dmax:ℝ) := by exact_mod_cast h1
      have hc : ((DminOf j : ℕ) : ℝ) ≤ (Nat.cast (lev j) : ℝ) := le_trans h1' h2
      exact_mod_cast hc
    have hbigL : ∀ j < T, (1:ℝ) ≤ εs' j * rPred r θ (lev j) := by
      intro j hj
      have h1 : εs' 0 ≤ εs' j := by
        rw [hεs'def]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        show εs 0 ≤ εs j
        rw [hεsdef]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hCc1 (Nat.zero_le j)) hε0pos.le
      have h2 : εs' 0 = 100*(1 + (r:ℝ)*θ)*ε0 := by
        show 100*(1 + (r:ℝ)*θ)*εs 0 = 100*(1 + (r:ℝ)*θ)*ε0
        rw [hεs0]
      have h3 : (Nat.cast (lev j) : ℝ) * Real.exp (-(2*((r:ℝ)-1)*θ)) ≤ rPred r θ (lev j) :=
        rPred_ge hr hθ0 hθ1 (hlev1 j hj)
      have h4 : (D0:ℝ) * q^T ≤ (Nat.cast (lev j) : ℝ) := by
        have h5 : (D0:ℝ) * q^j ≤ (Nat.cast (lev j) : ℝ) := (hlev_both j (le_of_lt hj)).1
        have h6 : q^T ≤ q^j := pow_le_pow_of_le_one (le_of_lt hq0) hq1 (le_of_lt hj)
        have h7 : (0:ℝ) ≤ (D0:ℝ) := le_trans zero_le_one hD0_1
        nlinarith only [h5, h6, h7]
      have h100 : (1:ℝ) ≤ 100*(1 + (r:ℝ)*θ) := by
        have h0 : (0:ℝ) ≤ (r:ℝ)*θ := by positivity
        have h1' : (1:ℝ) ≤ 1 + (r:ℝ)*θ := by linarith only [h0]
        have h2' : (100:ℝ)*1 ≤ 100*(1 + (r:ℝ)*θ) :=
          mul_le_mul_of_nonneg_left h1' (by norm_num)
        linarith only [h2']
      have hP' : (2:ℝ)^(T+1) = 2 * (2:ℝ)^T := by rw [pow_succ']
      have hE' : (Real.exp (2*((r:ℝ)-1)*θ))^(T+1)
          = (Real.exp (2*((r:ℝ)-1)*θ))^T * Real.exp (2*((r:ℝ)-1)*θ) := by rw [pow_succ]
      have hDthr32 : (1/ε0) * 32 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T)
            * Real.exp (2*((r:ℝ)-1)*θ) ≤ Dthr := by
        have hnn : (0:ℝ) ≤ (2 * (2:ℝ)^T)
            * ((Real.exp (2*((r:ℝ)-1)*θ))^T * Real.exp (2*((r:ℝ)-1)*θ)) * 16 := by positivity
        have hS : (1/ε0) ≤ (Dmax:ℝ) + 1/ε0 + 1 := by
          have h6 : (0:ℝ) ≤ (Dmax:ℝ) := Nat.cast_nonneg Dmax
          linarith
        have hkey : (1/ε0) * 32 * ((2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T)
              * Real.exp (2*((r:ℝ)-1)*θ)
            = (1/ε0) * ((2 * (2:ℝ)^T)
                * ((Real.exp (2*((r:ℝ)-1)*θ))^T * Real.exp (2*((r:ℝ)-1)*θ)) * 16) := by ring
        have hkey2 : Dthr = ((Dmax:ℝ) + 1/ε0 + 1) * ((2 * (2:ℝ)^T)
                * ((Real.exp (2*((r:ℝ)-1)*θ))^T * Real.exp (2*((r:ℝ)-1)*θ)) * 16) := by
          rw [hDthrdef, hP', hE']
          ring
        rw [hkey, hkey2]
        exact mul_le_mul_of_nonneg_right hS hnn
      have hED : Real.exp (2*((r:ℝ)-1)*θ) ≤ 100*(1+(r:ℝ)*θ)*ε0 * ((D0:ℝ) * q^T) :=
        nibble_ED (T := T) (A := Real.exp (2*((r:ℝ)-1)*θ))
          (W := (2:ℝ)^T * (Real.exp (2*((r:ℝ)-1)*θ))^T) (q := q)
          (D := (D:ℝ)) (D0 := (D0:ℝ)) (ε0 := ε0) (K := 100*(1+(r:ℝ)*θ))
          (by positivity) hqK hε0pos (by positivity)
          (le_trans hDthr32 hDthr) hD0half h100
      have h11 : (1:ℝ) ≤ 100*(1 + (r:ℝ)*θ)*ε0 * ((D0:ℝ) * q^T)
          * Real.exp (-(2*((r:ℝ)-1)*θ)) := by
        have hm : (1:ℝ) = Real.exp (2*((r:ℝ)-1)*θ) * Real.exp (-(2*((r:ℝ)-1)*θ)) := by
          rw [← Real.exp_add,
            show 2*((r:ℝ)-1)*θ + -(2*((r:ℝ)-1)*θ) = 0 from by ring, Real.exp_zero]
        calc (1:ℝ) = Real.exp (2*((r:ℝ)-1)*θ) * Real.exp (-(2*((r:ℝ)-1)*θ)) := hm
          _ ≤ (100*(1 + (r:ℝ)*θ)*ε0 * ((D0:ℝ) * q^T))
              * Real.exp (-(2*((r:ℝ)-1)*θ)) :=
              mul_le_mul_of_nonneg_right hED (by positivity)
          _ = 100*(1 + (r:ℝ)*θ)*ε0 * ((D0:ℝ) * q^T)
              * Real.exp (-(2*((r:ℝ)-1)*θ)) := by ring
      have h13 : 100*(1 + (r:ℝ)*θ)*ε0 * ((D0:ℝ) * q^T)
          * Real.exp (-(2*((r:ℝ)-1)*θ)) ≤ εs' j * rPred r θ (lev j) := by
        have hexpnn : (0:ℝ) ≤ Real.exp (-(2*((r:ℝ)-1)*θ)) := by positivity
        have h16 : 100*(1 + (r:ℝ)*θ)*ε0 ≤ εs' j := by rw [← h2]; exact h1
        have hDqnn : (0:ℝ) ≤ (D0:ℝ) * q^T :=
          mul_nonneg (le_trans zero_le_one hD0_1) (pow_pos hq0 T).le
        calc 100*(1 + (r:ℝ)*θ)*ε0 * ((D0:ℝ) * q^T) * Real.exp (-(2*((r:ℝ)-1)*θ))
            = (100*(1 + (r:ℝ)*θ)*ε0)
              * ((D0:ℝ) * q^T * Real.exp (-(2*((r:ℝ)-1)*θ))) := by ring
          _ ≤ (εs' j) * ((D0:ℝ) * q^T * Real.exp (-(2*((r:ℝ)-1)*θ))) :=
              mul_le_mul_of_nonneg_right h16 (mul_nonneg hDqnn hexpnn)
          _ ≤ (εs' j) * ((Nat.cast (lev j) : ℝ) * Real.exp (-(2*((r:ℝ)-1)*θ))) := by
              refine mul_le_mul_of_nonneg_left ?_ (hεs'pos j).le
              exact mul_le_mul_of_nonneg_right h4 hexpnn
          _ ≤ εs' j * rPred r θ (lev j) := mul_le_mul_of_nonneg_left h3 (hεs'pos j).le
      exact le_trans h11 h13
    -- the initial degree condition
    have hinit : ∀ v : Fin n, ((D0 : ℝ) ≤ (hd 𝓗 v : ℝ)) ∧
        ((hd 𝓗 v : ℝ) ≤ (1 + εs 0) * (D0 : ℝ)) := by
      intro v
      have hv := hdeg v
      have h1 : (1 - κ) * (D : ℝ) ≤ (hd 𝓗 v : ℝ) := by
        have h2 := (abs_le.mp hv).1
        linarith only [h2]
      have h3 : (D0 : ℝ) ≤ (1 - κ) * (D : ℝ) := by
        have h4 : (0:ℝ) ≤ (1 - κ) * (D:ℝ) := by nlinarith only [hκ4, hD4]
        rw [hD0def]
        exact Nat.floor_le h4
      have h5 : (hd 𝓗 v : ℝ) ≤ (1 + κ) * (D:ℝ) := by
        have h2 := (abs_le.mp hv).2
        linarith only [h2]
      have h6 : (D:ℝ) ≤ (D0:ℝ) / (1 - 2*κ) := by
        rw [le_div_iff₀ (by linarith only [hκ4])]
        have h7 : (D:ℝ) * (1 - 2*κ) = (1 - 2*κ) * (D:ℝ) := by ring
        rw [h7]
        exact hD0_ge
      have h8 : (1 + κ) / (1 - 2*κ) ≤ 1 + ε0 := by
        rw [div_le_iff₀ (by linarith only [hκ4])]
        rw [hκdef]
        nlinarith only [hε0_1, hε0pos.le]
      have h9 : (hd 𝓗 v : ℝ) ≤ (1 + εs 0) * (D0:ℝ) := by
        have h10 : (0:ℝ) ≤ 1 + κ := add_nonneg zero_le_one hκ0.le
        have hεs0' : (1 + εs 0) = 1 + ε0 := by rw [hεs0]
        rw [hεs0']
        calc (hd 𝓗 v : ℝ) ≤ (1 + κ) * (D:ℝ) := h5
          _ ≤ (1 + κ) * ((D0:ℝ)/(1-2*κ)) := mul_le_mul_of_nonneg_left h6 h10
          _ = ((1+κ)/(1-2*κ)) * (D0:ℝ) := by ring
          _ ≤ (1 + ε0) * (D0:ℝ) := mul_le_mul_of_nonneg_right h8 (le_trans zero_le_one hD0_1)
      exact ⟨le_trans h3 h1, h9⟩
    -- the round lemma at round `j`
    have hminD1 : ∀ j < T, 1 ≤ DminOf j := by
      intro j hj
      have hDm : DminOf j = (hround0 j hj).choose := by
        show (if hj' : j < T then (hround0 j hj').choose else 0) = (hround0 j hj).choose
        exact dif_pos hj
      rw [hDm]
      exact (hround0 j hj).choose_spec.1
    have hround' : ∀ j < T, ∀ {V : Type} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (D' : ℕ),
        DminOf j ≤ D' → D' ≤ Fintype.card V → HLin 𝓖 → HUnif 𝓖 r →
        (∀ v : V, |((hd 𝓖 v : ℝ)) - (D' : ℝ)| ≤ εs j * (D' : ℝ)) →
        ∃ ω : 𝓖 → Bool, RoundGood 𝓖 r D' θ δ (εs' j) (rPred r θ D') ω := by
      intro j hj
      have hDm : DminOf j = (hround0 j hj).choose := by
        show (if hj' : j < T then (hround0 j hj').choose else 0) = (hround0 j hj).choose
        exact dif_pos hj
      refine fun {V : Type} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) (D' : ℕ)
          (h1 : DminOf j ≤ D') (h2 : D' ≤ Fintype.card V) (h3 : HLin 𝓖)
          (h4 : HUnif 𝓖 r)
          (h5 : ∀ v : V, |((hd 𝓖 v : ℝ)) - (D' : ℝ)| ≤ εs j * (D' : ℝ)) =>
        (hround0 j hj).choose_spec.2 𝓖 D' (hDm ▸ h1) h2 h3 h4 h5
    -- run the iteration
    obtain ⟨U, Acc, M, hinv⟩ :=
      nibble_iter (r := r) (θ := θ) (δ := δ) (lam := lam) (T := T) (lev := lev)
        (εs := εs) (εs' := εs') (Dmin := DminOf)
        hr hθ0 hθ1 hδ0 hδ1 hlam0 hlamdef hεs_pos (fun j hj => hεs_θ j hj)
        (fun j hj => hεsδ j hj) hεs'pos (fun j hj => hεs'half j hj)
        (fun j _ => hεs'2 j) (fun j hj => hεs'six j hj) (fun j _ => hεs_eq j)
        (fun j _ => hlev_succ j) hminD1 hminD hround' hbigL 𝓗 D0 hl hu hlev0 hinit
    -- the final count
    have hlam1 : lam ≤ 1 := by
      rw [hlamdef]
      have h2 : (1 + 2*δ) ≤ Real.exp (2*δ) := one_add_mul_le_exp (2*δ)
      calc (1 + 2*δ) * Real.exp (-θ) ≤ Real.exp (2*δ) * Real.exp (-θ) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = Real.exp (2*δ - θ) := by rw [← Real.exp_add]; ring_nf
        _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hδθ, hθ0])
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hinv
    refine ⟨{e : 𝓗 | (e : Set (Fin n)) ∈ M}, ?_, ?_⟩
    · rintro ⟨e, he⟩ ⟨f, hf⟩ heM hfM hne
      exact h5 e heM f hfM (fun hc => hne (Subtype.ext hc))
    · have hunion : (⋃ e ∈ ({e : 𝓗 | (e : Set (Fin n)) ∈ M} : Set 𝓗),
          ((e : 𝓗) : Set (Fin n))) = ⋃₀ M := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_iUnion] at hx
          obtain ⟨e, he⟩ := hx
          rw [Set.mem_iUnion] at he
          obtain ⟨heM, hxe⟩ := he
          exact ⟨(e : Set (Fin n)), heM, hxe⟩
        · intro hx
          rw [Set.mem_sUnion] at hx
          obtain ⟨s, hsM, hxs⟩ := hx
          rw [Set.mem_iUnion]
          refine ⟨⟨s, h3 hsM⟩, ?_⟩
          rw [Set.mem_iUnion]
          exact ⟨hsM, hxs⟩
      rw [hunion]
      have hsubmem : Set.univ \ ⋃₀ M ⊆ U ∪ Acc := by
        intro x hx
        rcases h1 hx.1 with (hxU | hxM) | hxAcc
        · exact Or.inl hxU
        · exact absurd hxM hx.2
        · exact Or.inr hxAcc
      have hb : ((Set.univ \ ⋃₀ M).ncard : ℝ) ≤ (U.ncard : ℝ) + (Acc.ncard : ℝ) := by
        calc ((Set.univ \ ⋃₀ M).ncard : ℝ) ≤ ((U ∪ Acc).ncard : ℝ) := by
              exact_mod_cast Set.ncard_le_ncard hsubmem (Set.toFinite _)
          _ ≤ (U.ncard : ℝ) + (Acc.ncard : ℝ) := by
              exact_mod_cast Set.ncard_union_le U Acc
      have hexpnn : (0:ℝ) ≤ θ - θ*Real.exp (-θ) := by
        have h2' : Real.exp (-θ) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hθ0.le)
        rw [show θ - θ*Real.exp (-θ) = θ * (1 - Real.exp (-θ)) by ring]
        exact mul_nonneg hθ0.le (sub_nonneg.mpr h2')
      have hCnn : (0:ℝ) ≤ (r:ℝ)*(1+δ)*(θ - θ*Real.exp (-θ)) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg r) (add_nonneg zero_le_one hδ0.le)) hexpnn
      have hS := sum_geom_le (T := T) hθ0 hlam0 hlam1 h1mlam
      calc ((Set.univ \ ⋃₀ M).ncard : ℝ)
          ≤ (U.ncard : ℝ) + (Acc.ncard : ℝ) := hb
        _ ≤ (n:ℝ)*lam^T + (n:ℝ)*((r:ℝ)*(1+δ)*(θ - θ*Real.exp (-θ))*(4/θ)) := by
            refine add_le_add h7 ?_
            have hC' : (n:ℝ)*(r:ℝ)*(1+δ)*(θ - θ*Real.exp (-θ))*(∑ i ∈ Finset.range T, lam^i)
                = (n:ℝ) * (((r:ℝ)*(1+δ)*(θ - θ*Real.exp (-θ)))
                    * (∑ i ∈ Finset.range T, lam^i)) := by ring
            calc (Acc.ncard : ℝ)
                ≤ (n:ℝ) * (((r:ℝ)*(1+δ)*(θ - θ*Real.exp (-θ)))
                    * (∑ i ∈ Finset.range T, lam^i)) := by rw [← hC']; exact h8
              _ ≤ (n:ℝ) * (((r:ℝ)*(1+δ)*(θ - θ*Real.exp (-θ))) * (4/θ)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS hCnn)
                    (Nat.cast_nonneg n)
        _ ≤ γ*(n:ℝ) := final_bound (Nat.cast_nonneg n) hθ0 hθ1 hδ0 hδ1 hr0 hrθ hlam_T
