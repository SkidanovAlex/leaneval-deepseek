/-
  `slot_step` : the telescoping step of the slot lemma `Work.WilC4.slot_bound`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.slot_aux
import Submission.Work.WilC4.chain_arith
import Submission.Work.WilC4.tent_sum
import Submission.Work.WilC4.isRpow_rpow
import Submission.Work.WilC4.abs_logb_leftover_le

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilC4

open Work.WilC4.Route (Gr InD valY ratioY eq_valY valY_mem)

variable {k : ℕ}

/-- On an interval free of `B`, the doubling ratio at a point whose double also lies in the
interval is a genuine value of the relation `RatW`. -/
lemma ratW_ratioY_of_free {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    {c : Fin k → ℝ} {a b z : ℝ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgood : GoodFibre Y B) (hab : a < b)
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B)
    (hz : z ∈ Set.Ioo a b) (h2z : 2*z ∈ Set.Ioo a b) : RatW Y c z (ratioY Y c z) :=
  (ratW_iff_valY hfun c z (ratioY Y c z)).mpr
    ⟨(valY_gr_ne hgood hab hfree hz).1, (valY_gr_ne hgood hab hfree h2z).1,
     (valY_gr_ne hgood hab hfree hz).2, rfl⟩

theorem slot_step {k : ℕ}
    {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)} {E : Set ℝ}
    {η : ℚ} {β : ℝ} (hη : 0 < η) (hβ : 0 < β)
    {c : Fin k → ℝ} {a b x₁ x₂ y₁ y₂ : ℝ} {N : ℕ}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgood : GoodFibre Y B)
    (hsgn : (∀ z ∈ Set.Ioo a b, 0 < valY Y c z) ∨ (∀ z ∈ Set.Ioo a b, valY Y c z < 0))
    (hmono : MonotoneOn (fun z => |valY Y c z|) (Set.Ioo a b) ∨
      AntitoneOn (fun z => |valY Y c z|) (Set.Ioo a b))
    (hab : a < b) (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B)
    (ha : 0 < a) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) (hlt : x₁ < x₂)
    (hN2 : (2:ℝ) ≤ (N:ℝ)) (hN1 : (1:ℝ) ≤ (N:ℝ))
    (hNax : (N:ℝ) * a < x₁) (hNxb : (N:ℝ) * x₂ < b)
    (hGr₁ : Gr Y c x₁ y₁) (hGr₂ : Gr Y c x₂ y₂)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ q ∈ ExpSet E, |(q:ℝ)| ≤ D)
    (hbigA : (8 * (4:ℝ)^(η:ℝ) * β / (1 - (2:ℝ)^(-(η:ℝ))) + 4 * β * (8:ℝ)^(η:ℝ))
        * (N:ℝ)^(-(η:ℝ)) + 2*D ≤ Real.logb 2 (N:ℝ))
    (hsmall : β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) ≤ 1/2)
    (q0 : ℚ) (hq0mem : q0 ∈ ExpSet E)
    (hclose : ∀ (j : ℕ), j < Nat.ceil (Real.logb 2 (x₂ / x₁)) →
      |ratioY Y c (SlotPt x₁ j) / (2:ℝ)^(q0:ℝ) - 1| ≤ β * (SlotM N x₁ b j) ^ (-(η:ℝ))) :
    ∃ t₁ t₂ : ℝ, IsRpow x₁ q0 t₁ ∧ IsRpow x₂ q0 t₂ ∧
      |y₂| * t₁ ≤ (N:ℝ) * (|y₁| * t₂) ∧ |y₁| * t₂ ≤ (N:ℝ) * (|y₂| * t₁) := by
  classical
  have hη0 : (0:ℝ) < (η:ℝ) := by exact_mod_cast hη
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNnat : 1 ≤ N := by exact_mod_cast (le_trans (by norm_num : (1:ℝ) ≤ 2) hN2)
  -- ## The chain
  have hx2div : 0 < x₂ / x₁ := div_pos hx₂ hx₁
  have hrat1 : 1 < x₂ / x₁ := (one_lt_div hx₁).mpr hlt
  have hlogpos : 0 < Real.logb 2 (x₂ / x₁) := Real.logb_pos (by norm_num) hrat1
  set K : ℕ := Nat.ceil (Real.logb 2 (x₂ / x₁)) with hKdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact Nat.one_le_ceil_iff.mpr hlogpos
  have hKpos : 0 < K := hK1
  have hKne : K ≠ 0 := by omega
  have hKle : Real.logb 2 (x₂ / x₁) ≤ (K:ℝ) := by rw [hKdef]; exact Nat.le_ceil _
  have hKlt : (K:ℝ) < Real.logb 2 (x₂ / x₁) + 1 := by
    rw [hKdef]; exact Nat.ceil_lt_add_one hlogpos.le
  have ht0 : SlotPt x₁ 0 = x₁ := by simp [SlotPt]
  have htsucc : ∀ j, SlotPt x₁ (j+1) = 2 * SlotPt x₁ j := by
    intro j; simp only [SlotPt, pow_succ]; ring
  have htpos : ∀ j, 0 < SlotPt x₁ j := fun j => mul_pos hx₁ (pow_pos (by norm_num) j)
  have htge : ∀ j, x₁ ≤ SlotPt x₁ j := fun j =>
    le_mul_of_one_le_right hx₁.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j))
  have ht_mono : Monotone (SlotPt x₁) := fun i j hij =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hij) hx₁.le
  have hx₁hb : x₁ < b/2 := by nlinarith [hNxb, hx₂, hlt.le, hN2]
  have h2x2b : 2 * x₂ < b := by nlinarith [hNxb, hN2, hx₂]
  have hax₁ : a < x₁ := by
    rcases lt_or_ge a 0 with h | h
    · linarith
    · exact lt_of_le_of_lt (le_mul_of_one_le_left h hN1) hNax
  have htK_ge : x₂ ≤ SlotPt x₁ K := by
    have h : x₂ / x₁ ≤ (2:ℝ)^((K:ℝ)) :=
      (Real.logb_le_iff_le_rpow (by norm_num) hx2div).mp hKle
    rw [Real.rpow_natCast] at h
    have h2 := mul_le_mul_of_nonneg_left h hx₁.le
    rw [mul_div_cancel₀ _ hx₁.ne'] at h2
    simpa [SlotPt] using h2
  have htKm1_lt : SlotPt x₁ (K-1) < x₂ := by
    have hcast : ((K-1 : ℕ) : ℝ) = (K:ℝ) - 1 := by rw [Nat.cast_sub hK1]; norm_num
    have hltlog : ((K-1 : ℕ) : ℝ) < Real.logb 2 (x₂ / x₁) := by rw [hcast]; linarith
    have h : (2:ℝ)^((K-1:ℕ) : ℝ) < x₂ / x₁ :=
      (Real.lt_logb_iff_rpow_lt (by norm_num) hx2div).mp hltlog
    rw [Real.rpow_natCast] at h
    have h2 := mul_lt_mul_of_pos_left h hx₁
    rw [mul_div_cancel₀ _ hx₁.ne'] at h2
    simpa [SlotPt] using h2
  have htK_lt : SlotPt x₁ K < 2 * x₂ := by
    have hltlog : (K:ℝ) - 1 < Real.logb 2 (x₂ / x₁) := by linarith
    have h : (2:ℝ)^((K:ℝ) - 1) < x₂ / x₁ :=
      (Real.lt_logb_iff_rpow_lt (by norm_num) hx2div).mp hltlog
    have h2 : (2:ℝ)^((K:ℝ) - 1) = (2:ℝ)^K / 2 := by
      rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one, Real.rpow_natCast]
    rw [h2] at h
    have h3 : (2:ℝ)^K < 2 * (x₂ / x₁) := by nlinarith [h]
    have h4 := mul_lt_mul_of_pos_left h3 hx₁
    have heq2 : x₁ * (2 * (x₂ / x₁)) = 2 * x₂ := by field_simp
    rw [heq2] at h4
    simpa [SlotPt] using h4
  have htI : ∀ j ≤ K, SlotPt x₁ j ∈ Set.Ioo a b := fun j hj =>
    ⟨lt_of_lt_of_le hax₁ (htge j),
     lt_of_le_of_lt (ht_mono hj) (lt_trans htK_lt h2x2b)⟩
  have hx₁I : x₁ ∈ Set.Ioo a b := by rw [← ht0]; exact htI 0 (by omega)
  have hx₂I : x₂ ∈ Set.Ioo a b :=
    ⟨lt_of_lt_of_le hax₁ hlt.le, lt_trans (by linarith : x₂ < 2 * x₂) h2x2b⟩
  have hy₁ : y₁ = valY Y c x₁ := eq_valY hfun hGr₁
  have hy₂ : y₂ = valY Y c x₂ := eq_valY hfun hGr₂
  have hy₁ne : y₁ ≠ 0 := by rw [hy₁]; exact (valY_gr_ne hgood hab hfree hx₁I).2
  have hy₂ne : y₂ ≠ 0 := by rw [hy₂]; exact (valY_gr_ne hgood hab hfree hx₂I).2
  -- ## The chain data
  set aa : ℝ := x₁ / (2 * (N:ℝ)) with hadef
  have haapos : 0 < aa := by rw [hadef]; positivity
  have hdaa : (N:ℝ) * aa < x₁ := by
    have h2 : (N:ℝ) * aa = x₁/2 := by rw [hadef]; field_simp
    rw [h2]; linarith
  have hminpos : ∀ j, 0 < min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) := fun j =>
    lt_min (div_pos (htpos j) haapos) (div_pos (by linarith) (htpos j))
  have hMpos : ∀ j, 0 < SlotM N x₁ b j := fun j => by
    show 0 < min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) / 4
    exact div_pos (hminpos j) (by norm_num)
  have hMle1 : ∀ j, SlotM N x₁ b j ≤ SlotPt x₁ j / (4 * aa) := fun j => by
    show min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) / 4 ≤ SlotPt x₁ j / (4 * aa)
    have h1 : min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) / 4 ≤ (SlotPt x₁ j / aa) / 4 :=
      div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have h2 : (SlotPt x₁ j / aa) / 4 = SlotPt x₁ j / (4 * aa) := by ring
    linarith
  have hMle2 : ∀ j, SlotM N x₁ b j ≤ b / (4 * SlotPt x₁ j) := fun j => by
    show min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) / 4 ≤ b / (4 * SlotPt x₁ j)
    have h1 : min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) / 4 ≤ (b / SlotPt x₁ j) / 4 :=
      div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have h2 : (b / SlotPt x₁ j) / 4 = b / (4 * SlotPt x₁ j) := by ring
    linarith
  have hMge : ∀ j, j < K → (N:ℝ)/8 ≤ SlotM N x₁ b j := by
    intro j hj
    show (N:ℝ)/8 ≤ min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) / 4
    have h1 : (N:ℝ)/2 ≤ SlotPt x₁ j / aa := by
      rw [hadef, le_div_iff₀ (by positivity)]
      have heq1 : (N:ℝ)/2 * (x₁ / (2 * (N:ℝ))) = x₁/4 := by field_simp; ring
      rw [heq1]; nlinarith [htge j, hx₁]
    have h2 : (N:ℝ)/2 ≤ b / SlotPt x₁ j := by
      have ht2 : SlotPt x₁ j < 2 * x₂ := lt_of_le_of_lt (ht_mono (le_of_lt hj)) htK_lt
      rw [le_div_iff₀ (htpos j)]
      nlinarith [hNxb, ht2, hNpos]
    have h3 : (N:ℝ)/2 ≤ min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) := le_min h1 h2
    linarith
  -- ## Deviation bounds per chain point
  set epsN : ℕ → ℝ := fun j => β * (SlotM N x₁ b j) ^ (-(η:ℝ)) with hepsdef
  set eps : Fin K → ℝ := fun j => epsN ↑j with hepsKdef
  set w : Fin K → ℝ := fun j => ratioY Y c (SlotPt x₁ ↑j) with hwdef
  have hq0D : |(q0:ℝ)| ≤ D := hD q0 hq0mem
  have heps0 : ∀ j : Fin K, 0 ≤ eps j := fun j =>
    mul_nonneg hβ.le (Real.rpow_pos_of_pos (hMpos ↑j) _).le
  have heps_le : ∀ j : Fin K, eps j ≤ β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) := by
    intro j
    show β * (SlotM N x₁ b ↑j) ^ (-(η:ℝ)) ≤ _
    have h1 : β * (SlotM N x₁ b ↑j) ^ (-(η:ℝ)) ≤ β * ((N:ℝ)/8) ^ (-(η:ℝ)) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith : (0:ℝ) < (N:ℝ)/8) (hMge ↑j j.isLt)
          (neg_nonpos.mpr hη0.le)) hβ.le
    have h2 : β * ((N:ℝ)/8) ^ (-(η:ℝ)) = β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)) := by
      rw [div_rpow_neg hNpos (by norm_num : (0:ℝ) < 8)]
      ring
    linarith [h1, h2]
  have heps2 : ∀ j : Fin K, eps j ≤ 1/2 := by
    intro j
    have h1 := heps_le j
    linarith [h1, hsmall]
  have hclose' : ∀ j : Fin K, |w j / (2:ℝ)^(q0:ℝ) - 1| ≤ eps j := by
    intro j
    have h := hclose ↑j (by simpa only [hKdef] using j.isLt)
    simpa [w, eps, epsN] using h
  -- ## The sum bound by `tent_sum`
  have hSeps : (∑ j : Fin K, eps j)
      ≤ (4:ℝ)^(η:ℝ) * (2 * β * (N:ℝ)^(-(η:ℝ)) / (1 - (2:ℝ)^(-(η:ℝ)))) := by
    rw [show (∑ j : Fin K, eps j) = ∑ j ∈ Finset.range K, epsN j from
      Fin.sum_univ_eq_sum_range epsN K]
    have hstep : ∀ j ∈ Finset.range K,
        epsN j = (4:ℝ)^(η:ℝ) * (β * (min (SlotPt x₁ j / aa) (b / SlotPt x₁ j)) ^ (-(η:ℝ))) := by
      intro j _
      show β * (SlotM N x₁ b j) ^ (-(η:ℝ)) = _
      rw [show SlotM N x₁ b j = min (SlotPt x₁ j / aa) (b / SlotPt x₁ j) / 4 from rfl,
        div_rpow_neg (hminpos j) (by norm_num : (0:ℝ) < 4) (η:ℝ)]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ (4:ℝ)^(η:ℝ))
    have hts : ∑ j ∈ Finset.range (Nat.ceil (Real.logb 2 (x₂ / x₁))),
          (fun Mm => β * Mm ^ (-(η:ℝ))) (min (x₁ * (2:ℝ)^j / aa) (b / (x₁ * (2:ℝ)^j)))
        ≤ 2 * β * (N:ℝ)^(-(η:ℝ)) / (1 - (2:ℝ)^(-(η:ℝ))) :=
      tent_sum (N := N) (δ := fun Mm => β * Mm ^ (-(η:ℝ))) (β := β) (η := (η:ℝ))
        hNnat (fun Mm hM => mul_nonneg hβ.le (Real.rpow_pos_of_pos hM _).le)
        (fun Mm Mm' hM hM' => mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hM hM' (neg_nonpos.mpr hη0.le)) hβ.le)
        hη0 hβ (fun Mm _ => le_refl _) hx₁ hlt.le haapos (by linarith) hdaa hNxb
    rw [hKdef]
    simpa only [SlotPt] using hts
  -- ## The telescoping
  have hne_t : ∀ j ≤ K, valY Y c (SlotPt x₁ j) ≠ 0 := fun j hj =>
    (valY_gr_ne hgood hab hfree (htI j hj)).2
  have htel : ∏ j : Fin K, w j = valY Y c (SlotPt x₁ K) / valY Y c x₁ := by
    have h1 : ∀ j : ℕ,
        ratioY Y c (SlotPt x₁ j) = valY Y c (SlotPt x₁ (j+1)) / valY Y c (SlotPt x₁ j) := by
      intro j; simp only [ratioY]; rw [htsucc j]
    rw [show (∏ j : Fin K, w j) = ∏ j ∈ Finset.range K, ratioY Y c (SlotPt x₁ j) from
      Fin.prod_univ_eq_prod_range (fun j => ratioY Y c (SlotPt x₁ j)) K]
    rw [Finset.prod_congr rfl (fun j _ => h1 j)]
    rw [prod_range_div_real (fun j => valY Y c (SlotPt x₁ j)) K (fun j hj => hne_t j hj), ht0]
  set L : ℝ := valY Y c x₂ / valY Y c (SlotPt x₁ K) with hLdef
  have hLne : L ≠ 0 := by
    rw [hLdef]
    exact div_ne_zero (by rw [← hy₂]; exact hy₂ne) (hne_t K le_rfl)
  have hy_eq : y₂ = y₁ * (∏ j : Fin K, w j) * L := by
    rw [hy₂, hy₁, htel, hLdef]
    have h1ne : valY Y c x₁ ≠ 0 := by rw [← hy₁]; exact hy₁ne
    have hKne : valY Y c (SlotPt x₁ K) ≠ 0 := hne_t K le_rfl
    field_simp
  -- ## The leftover factor
  have hLb : |Real.logb 2 L| ≤ |(q0:ℝ)| + 4 * eps ⟨K-1, Nat.sub_one_lt hKne⟩ := by
    have h2τ : 2 * SlotPt x₁ (K-1) = SlotPt x₁ K := by
      rw [← htsucc (K-1), Nat.sub_add_cancel hK1]
    have hτpos : 0 < SlotPt x₁ (K-1) := htpos _
    have hτle : SlotPt x₁ (K-1) ≤ x₂ := le_of_lt htKm1_lt
    have hle2 : x₂ ≤ 2 * SlotPt x₁ (K-1) := by rw [h2τ]; exact htK_ge
    have hsub4 : Set.Icc (SlotPt x₁ (K-1)) (2 * SlotPt x₁ (K-1)) ⊆ Set.Ioo a b := by
      intro z hz
      refine ⟨lt_of_lt_of_le hax₁ (le_trans (htge (K-1)) hz.1), ?_⟩
      exact lt_of_le_of_lt hz.2 (lt_of_lt_of_le (by rw [h2τ]; exact htK_lt) h2x2b.le)
    have hpos4 : ∀ z ∈ Set.Icc (SlotPt x₁ (K-1)) (2 * SlotPt x₁ (K-1)), 0 < |valY Y c z| :=
      fun z hz => abs_pos.mpr ((valY_gr_ne hgood hab hfree (hsub4 hz)).2)
    have hmono4 : MonotoneOn (fun z => |valY Y c z|) (Set.Icc (SlotPt x₁ (K-1)) (2 * SlotPt x₁ (K-1))) ∨
        AntitoneOn (fun z => |valY Y c z|) (Set.Icc (SlotPt x₁ (K-1)) (2 * SlotPt x₁ (K-1))) := by
      rcases hmono with h | h
      · exact Or.inl (h.mono hsub4)
      · exact Or.inr (h.mono hsub4)
    have hD4 := abs_logb_leftover_le hτpos hτle hle2 hpos4 hmono4
    rw [h2τ] at hD4
    have hss1 : 0 < valY Y c x₂ / valY Y c (SlotPt x₁ K) := by
      rcases hsgn with hp | hn
      · exact div_pos (hp x₂ hx₂I) (hp (SlotPt x₁ K) (htI K le_rfl))
      · exact div_pos_of_neg_of_neg (hn x₂ hx₂I) (hn (SlotPt x₁ K) (htI K le_rfl))
    have hss2 : 0 < valY Y c (SlotPt x₁ K) / valY Y c (SlotPt x₁ (K-1)) := by
      rcases hsgn with hp | hn
      · exact div_pos (hp (SlotPt x₁ K) (htI K le_rfl))
          (hp (SlotPt x₁ (K-1)) (htI (K-1) (by omega)))
      · exact div_pos_of_neg_of_neg (hn (SlotPt x₁ K) (htI K le_rfl))
          (hn (SlotPt x₁ (K-1)) (htI (K-1) (by omega)))
    have h1eq : |valY Y c x₂| / |valY Y c (SlotPt x₁ K)| = valY Y c x₂ / valY Y c (SlotPt x₁ K) := by
      rw [← abs_div]; exact abs_of_pos hss1
    have h2eq : |valY Y c (SlotPt x₁ K)| / |valY Y c (SlotPt x₁ (K-1))|
        = valY Y c (SlotPt x₁ K) / valY Y c (SlotPt x₁ (K-1)) := by
      rw [← abs_div]; exact abs_of_pos hss2
    have hweq : valY Y c (SlotPt x₁ K) / valY Y c (SlotPt x₁ (K-1))
        = w ⟨K-1, Nat.sub_one_lt hKne⟩ := by
      show valY Y c (SlotPt x₁ K) / valY Y c (SlotPt x₁ (K-1))
        = ratioY Y c (SlotPt x₁ (K-1))
      simp only [ratioY]
      rw [h2τ]
    have hcl := hclose' ⟨K-1, Nat.sub_one_lt hKne⟩
    have hwne : w ⟨K-1, Nat.sub_one_lt hKne⟩ ≠ 0 := by
      intro h0
      have hcl' := hcl
      rw [h0, zero_div] at hcl'
      norm_num at hcl'
      have h2 := heps2 ⟨K-1, Nat.sub_one_lt hKne⟩
      linarith
    have hhalf : (1/2:ℝ) ≤ w ⟨K-1, Nat.sub_one_lt hKne⟩ / (2:ℝ)^(q0:ℝ) := by
      have h1 := (abs_le.mp hcl).1
      have h2 := heps2 ⟨K-1, Nat.sub_one_lt hKne⟩
      linarith
    have hb2q : (2:ℝ)^(q0:ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    have hsplit : Real.logb 2 (w ⟨K-1, Nat.sub_one_lt hKne⟩)
        = (q0:ℝ) + Real.logb 2 (w ⟨K-1, Nat.sub_one_lt hKne⟩ / (2:ℝ)^(q0:ℝ)) := by
      rw [Real.logb_div hwne hb2q, Real.logb_rpow (by norm_num) (by norm_num)]
      ring
    have hsmall2 : |Real.logb 2 (w ⟨K-1, Nat.sub_one_lt hKne⟩ / (2:ℝ)^(q0:ℝ))|
        ≤ 4 * eps ⟨K-1, Nat.sub_one_lt hKne⟩ := by
      have h1 := abs_logb_two_le hhalf
      have h2 : 4 * |w ⟨K-1, Nat.sub_one_lt hKne⟩ / (2:ℝ)^(q0:ℝ) - 1|
          ≤ 4 * eps ⟨K-1, Nat.sub_one_lt hKne⟩ := by linarith [hcl]
      linarith [h1, h2]
    calc |Real.logb 2 L| = |Real.logb 2 (valY Y c x₂ / valY Y c (SlotPt x₁ K))| := by rw [hLdef]
      _ = |Real.logb 2 (|valY Y c x₂| / |valY Y c (SlotPt x₁ K)|)| := by rw [← h1eq]
      _ ≤ |Real.logb 2 (|valY Y c (SlotPt x₁ K)| / |valY Y c (SlotPt x₁ (K-1))|)| := hD4
      _ = |Real.logb 2 (valY Y c (SlotPt x₁ K) / valY Y c (SlotPt x₁ (K-1)))| := by rw [h2eq]
      _ = |Real.logb 2 (w ⟨K-1, Nat.sub_one_lt hKne⟩)| := by rw [← hweq]
      _ ≤ |(q0:ℝ)| + 4 * eps ⟨K-1, Nat.sub_one_lt hKne⟩ := by
          rw [hsplit]
          have h3 := abs_add_le ((q0:ℝ))
            (Real.logb 2 (w ⟨K-1, Nat.sub_one_lt hKne⟩ / (2:ℝ)^(q0:ℝ)))
          linarith [h3, hsmall2]
  -- ## Assemble the key inequality and apply `chain_arith`
  have hsum4 : 4 * (∑ j : Fin K, eps j)
      ≤ (8 * (4:ℝ)^(η:ℝ) * β / (1 - (2:ℝ)^(-(η:ℝ)))) * (N:ℝ)^(-(η:ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hSeps (by norm_num : (0:ℝ) ≤ 4)
    have heq4 : 4 * ((4:ℝ)^(η:ℝ) * (2 * β * (N:ℝ)^(-(η:ℝ)) / (1 - (2:ℝ)^(-(η:ℝ)))))
        = (8 * (4:ℝ)^(η:ℝ) * β / (1 - (2:ℝ)^(-(η:ℝ)))) * (N:ℝ)^(-(η:ℝ)) := by ring
    linarith [h, heq4]
  have hLb2 : |Real.logb 2 L| ≤ D + (4 * β * (8:ℝ)^(η:ℝ)) * (N:ℝ)^(-(η:ℝ)) := by
    have h1 := hLb
    have h2 := heps_le ⟨K-1, Nat.sub_one_lt hKne⟩
    have h3 : 4 * eps ⟨K-1, Nat.sub_one_lt hKne⟩
        ≤ (4 * β * (8:ℝ)^(η:ℝ)) * (N:ℝ)^(-(η:ℝ)) := by
      have h4 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 4)
      have heq5 : 4 * (β * (8:ℝ)^(η:ℝ) * (N:ℝ)^(-(η:ℝ)))
          = (4 * β * (8:ℝ)^(η:ℝ)) * (N:ℝ)^(-(η:ℝ)) := by ring
      linarith [h4, heq5]
    linarith [h1, h3]
  have hkey : 4 * (∑ j : Fin K, eps j) + |Real.logb 2 L| + |(q0:ℝ)| ≤ Real.logb 2 (N:ℝ) := by
    have htot : 4 * (∑ j : Fin K, eps j) + |Real.logb 2 L| + |(q0:ℝ)|
        ≤ (8 * (4:ℝ)^(η:ℝ) * β / (1 - (2:ℝ)^(-(η:ℝ))) + 4 * β * (8:ℝ)^(η:ℝ))
          * (N:ℝ)^(-(η:ℝ)) + 2 * D := by
      nlinarith [hsum4, hLb2, hq0D, hD0]
    linarith [htot, hbigA]
  obtain ⟨ha1, ha2⟩ := chain_arith (q := q0) (K := K) (w := w) (ε := eps)
    (y₁ := y₁) (y₂ := y₂) (L := L) (x₁ := x₁) (x₂ := x₂) (N := (N:ℝ))
    hy₁ne hLne hx₁ hx₂ hN1 heps0 heps2 hclose' hKle (by linarith [hKlt]) hkey hy_eq
  exact ⟨x₁^(q0:ℝ), x₂^(q0:ℝ), isRpow_rpow hx₁ q0, isRpow_rpow hx₂ q0, ha1, ha2⟩

end Work.WilC4
