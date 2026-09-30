import Mathlib
import Submission.Work.BMF.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj
import Submission.Work.BMF.smooth_decomp_exists
import Submission.Work.BMF.norm_cpow_neg_I_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Classical
open MeasureTheory
open scoped ComplexConjugate

namespace Work.BMF

/-! ## Helper statements (delegated / proven here) -/

theorem char_expansion (M : ℕ) [NeZero M] (φ : ℕ → ℂ) (hper : Function.Periodic φ M)
    (m : ℕ) (hm : m.Coprime M) :
    φ m = ∑ χ : DirichletCharacter ℂ M,
      ((M.totient : ℂ)⁻¹ * ∑ g : ZMod M, φ g.val * conj (χ g)) * χ m := by
  classical
  have hφM : (M.totient : ℂ) ≠ 0 := by
    have h := Nat.totient_pos.mpr (NeZero.pos M)
    exact_mod_cast h.ne'
  have hunit : IsUnit (m : ZMod M) := (ZMod.isUnit_iff_coprime m M).mpr hm
  have hval : φ (m : ZMod M).val = φ m := by
    rw [ZMod.val_natCast]
    exact hper.map_mod_nat m
  rw [← hval]
  have horth : ∀ g : ZMod M,
      (∑ χ : DirichletCharacter ℂ M, conj (χ g) * χ (m : ZMod M))
        = if g = (m : ZMod M) then (M.totient : ℂ) else 0 := by
    intro g
    have h := Commons.NumberTheory.DirichletCharacter.sum_char_mul_conj M hunit g
    have e1 : (∑ χ : DirichletCharacter ℂ M, conj (χ g) * χ (m : ZMod M))
        = ∑ χ : DirichletCharacter ℂ M, χ (m : ZMod M) * conj (χ g) :=
      Finset.sum_congr rfl fun χ _ => by ring
    rw [e1, h]
    by_cases hg : (m : ZMod M) = g
    · rw [if_pos hg, if_pos hg.symm]
    · rw [if_neg hg, if_neg (fun hh => hg hh.symm)]
  have hterm : ∀ χ : DirichletCharacter ℂ M,
      ((M.totient : ℂ)⁻¹ * ∑ g : ZMod M, φ g.val * conj (χ g)) * χ (m : ZMod M)
      = (M.totient : ℂ)⁻¹ *
        ∑ g : ZMod M, φ g.val * (conj (χ g) * χ (m : ZMod M)) := by
    intro χ
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun g _ => by ring)
  have h1 : (∑ χ : DirichletCharacter ℂ M,
        ((M.totient : ℂ)⁻¹ * ∑ g : ZMod M, φ g.val * conj (χ g)) * χ (m : ZMod M))
      = ∑ χ : DirichletCharacter ℂ M,
        (M.totient : ℂ)⁻¹ *
          ∑ g : ZMod M, φ g.val * (conj (χ g) * χ (m : ZMod M)) :=
    Finset.sum_congr rfl fun χ _ => hterm χ
  rw [h1, ← Finset.mul_sum, Finset.sum_comm]
  have h4 : (∑ g : ZMod M, ∑ χ : DirichletCharacter ℂ M,
        φ g.val * (conj (χ g) * χ (m : ZMod M)))
      = ∑ g : ZMod M, φ g.val *
        (∑ χ : DirichletCharacter ℂ M, conj (χ g) * χ (m : ZMod M)) :=
    Finset.sum_congr rfl fun g _ => (Finset.mul_sum ..).symm
  rw [h4]
  have h5 : (∑ g : ZMod M, φ g.val *
        (∑ χ : DirichletCharacter ℂ M, conj (χ g) * χ (m : ZMod M)))
      = ∑ g : ZMod M, φ g.val * (if g = (m : ZMod M) then (M.totient : ℂ) else 0) :=
    Finset.sum_congr rfl fun g _ => by rw [horth g]
  rw [h5, Finset.sum_eq_single (m : ZMod M)]
  · rw [if_pos rfl, mul_comm (φ (m : ZMod M).val) (M.totient : ℂ)]
    rw [inv_mul_cancel_left₀ hφM]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem smooth_decomp_unique {r s₁ s₂ m₁ m₂ : ℕ}
    (hs₁ : ∀ q, q.Prime → q ∣ s₁ → q ∣ r) (hs₂ : ∀ q, q.Prime → q ∣ s₂ → q ∣ r)
    (hm₁ : m₁.Coprime r) (hm₂ : m₂.Coprime r) (h : s₁ * m₁ = s₂ * m₂) : s₁ = s₂ := by
  have hc₁ : s₁.Coprime m₂ := by
    refine Nat.coprime_of_dvd fun k hk hks hkm => ?_
    have hkr : k ∣ r := hs₁ k hk hks
    have hkg : k ∣ m₂.gcd r := Nat.dvd_gcd hkm hkr
    rw [hm₂.gcd_eq_one] at hkg
    exact hk.not_dvd_one hkg
  have hc₂ : s₂.Coprime m₁ := by
    refine Nat.coprime_of_dvd fun k hk hks hkm => ?_
    have hkr : k ∣ r := hs₂ k hk hks
    have hkg : k ∣ m₁.gcd r := Nat.dvd_gcd hkm hkr
    rw [hm₁.gcd_eq_one] at hkg
    exact hk.not_dvd_one hkg
  exact Nat.dvd_antisymm (hc₁.dvd_of_dvd_mul_right (h ▸ dvd_mul_right s₁ m₁))
    (hc₂.dvd_of_dvd_mul_right (h.symm ▸ dvd_mul_right s₂ m₂))

theorem mem_natIcc_div_iff {s : ℕ} (hs : 0 < s) {y H : ℝ} (hyH : 0 ≤ y + H) {m : ℕ} :
    s * m ∈ natIcc y (y + H) ↔ m ∈ natIcc (y / s) (y / s + H / s) := by
  have hsR : (0:ℝ) < s := by exact_mod_cast hs
  have hsplit : y / s + H / s = (y + H) / s := (add_div y H (s:ℝ)).symm
  have hyH' : 0 ≤ (y + H) / s := div_nonneg hyH hsR.le
  rw [hsplit, natIcc, natIcc, Finset.mem_Icc, Finset.mem_Icc, Nat.ceil_le, Nat.ceil_le,
      Nat.le_floor_iff hyH, Nat.le_floor_iff hyH']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hsR]; rw [Nat.cast_mul, mul_comm (↑s:ℝ) (↑m)] at h1; linarith
    · rw [le_div_iff₀ hsR]; rw [Nat.cast_mul, mul_comm (↑s:ℝ) (↑m)] at h2; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [div_le_iff₀ hsR] at h1; rw [Nat.cast_mul, mul_comm (↑s:ℝ) (↑m)]; linarith
    · rw [le_div_iff₀ hsR] at h2; rw [Nat.cast_mul, mul_comm (↑s:ℝ) (↑m)]; linarith

theorem sum_bij_div_coprime {s r : ℕ} (hs : 0 < s) {y H : ℝ} (hyH : 0 ≤ y + H) (G : ℕ → ℂ) :
    (∑ n ∈ (natIcc y (y + H)).filter (fun n => s ∣ n ∧ (n / s).Coprime r), G (n / s))
      = ∑ m ∈ (natIcc (y / s) (y / s + H / s)).filter (fun m => m.Coprime r), G m := by
  classical
  refine Finset.sum_bij (fun n _ => n / s) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    have hnL : s * (n / s) ∈ natIcc y (y + H) := by
      rw [Nat.mul_div_cancel' hn.2.1]; exact hn.1
    exact ⟨(mem_natIcc_div_iff hs hyH).mp hnL, hn.2.2⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    rw [Finset.mem_filter] at hn₁ hn₂
    have d1 := Nat.mul_div_cancel' hn₁.2.1
    have d2 := Nat.mul_div_cancel' hn₂.2.1
    rw [heq] at d1
    exact d1.symm.trans d2
  · intro m hm
    rw [Finset.mem_filter] at hm
    refine ⟨s * m, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, dvd_mul_right s m, ?_⟩
      · rw [mem_natIcc_div_iff hs hyH]; exact hm.1
      · rw [Nat.mul_div_cancel_left m hs]; exact hm.2
    · exact Nat.mul_div_cancel_left m hs
  · intro n hn
    rfl

theorem sum_split_rSmooth (r K : ℕ) (hr : 1 ≤ r) (L : Finset ℕ) (F : ℕ → ℂ) :
    ((r ^ K).divisors : Finset ℕ).sum
        (fun s => (L.filter (fun n => s ∣ n ∧ (n / s).Coprime r)).sum F)
      = (L.filter (fun n => ∃ s ∈ (r ^ K).divisors,
           s ∣ n ∧ (n / s).Coprime r)).sum F := by
  classical
  set t : ℕ → Finset ℕ := fun s => L.filter (fun n => s ∣ n ∧ (n / s).Coprime r) with ht
  have hrK : r ^ K ≠ 0 := pow_ne_zero _ (by omega)
  have hMsmooth : ∀ s ∈ (r^K).divisors, ∀ q, q.Prime → q ∣ s → q ∣ r := by
    intro s hsM q hq hqs
    rw [Nat.mem_divisors] at hsM
    exact hq.dvd_of_dvd_pow (dvd_trans hqs hsM.1)
  have hdisj : ((↑((r^K).divisors) : Set ℕ)).PairwiseDisjoint t := by
    intro s1 hs1 s2 hs2 hne
    change Disjoint (t s1) (t s2)
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    rw [ht, Finset.mem_filter] at hn1 hn2
    exact hne (smooth_decomp_unique (hMsmooth s1 hs1) (hMsmooth s2 hs2)
      hn1.2.2 hn2.2.2 (by rw [Nat.mul_div_cancel' hn1.2.1, Nat.mul_div_cancel' hn2.2.1]))
  rw [← Finset.sum_biUnion hdisj]
  congr 1
  ext n
  simp only [ht, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨s, hsS, hnL, hd, hc⟩
    exact ⟨hnL, s, hsS, hd, hc⟩
  · rintro ⟨hnL, s, hsS, hd, hc⟩
    exact ⟨s, hsS, hnL, hd, hc⟩

theorem measurable_stepFun (g : ℕ → ℂ) (H : ℝ) :
    Measurable (fun y : ℝ => ∑ n ∈ natIcc y (y + H), g n) := by
  have h : (fun y : ℝ => ∑ n ∈ natIcc y (y + H), g n)
      = fun y : ℝ => (fun ab : ℕ × ℕ => ∑ n ∈ Finset.Icc ab.1 ab.2, g n)
          (⌈y⌉₊, ⌊y + H⌋₊) := rfl
  rw [h]
  exact (measurable_of_countable (fun ab : ℕ × ℕ => ∑ n ∈ Finset.Icc ab.1 ab.2, g n)).comp
    (Measurable.prodMk Nat.measurable_ceil
      ((Nat.measurable_floor).comp (measurable_id.add measurable_const)))

theorem integrableOn_norm_stepFun (g : ℕ → ℂ) (H a b : ℝ) :
    MeasureTheory.IntegrableOn (fun y : ℝ => ‖∑ n ∈ natIcc y (y + H), g n‖) (Set.Ioc a b) := by
  classical
  have hmeas : Measurable (fun y : ℝ => ‖∑ n ∈ natIcc y (y + H), g n‖) :=
    (measurable_stepFun g H).norm
  refine MeasureTheory.IntegrableOn.of_bound ?_ hmeas.aestronglyMeasurable.restrict
    (∑ n ∈ Finset.range (⌊b + H⌋₊ + 1), ‖g n‖) ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun y hy => ?_
    rw [norm_norm]
    have hsub : natIcc y (y + H) ⊆ Finset.range (⌊b + H⌋₊ + 1) := by
      intro n hn
      rw [natIcc, Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      have hmono : ⌊y + H⌋₊ ≤ ⌊b + H⌋₊ := Nat.floor_mono (by linarith [hy.2])
      omega
    calc ‖∑ n ∈ natIcc y (y + H), g n‖ ≤ ∑ n ∈ natIcc y (y + H), ‖g n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (⌊b + H⌋₊ + 1), ‖g n‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)

/-- If `n ≥ 1` is not "covered" (i.e. `n = s m` with `s ∣ r ^ Kc` `r`-smooth and `m` coprime
to `r`), then `n` is divisible by `p ^ (Kc+1)` for some prime `p ∣ r`. -/
lemma not_covered_imp (r Kc n : ℕ) (hr : 0 < r) (hn : 1 ≤ n) :
    (¬ ∃ s ∈ (r ^ Kc).divisors, s ∣ n ∧ (n / s).Coprime r) →
      ∃ p ∈ r.primeFactors, p ^ (Kc + 1) ∣ n := by
  intro h
  obtain ⟨s, m, hsmooth, hsm, hmcop⟩ := smooth_decomp_exists r n hn
  have hspos : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · rw [h0, zero_mul] at hsm; omega
    · exact h0
  have hrne : r ≠ 0 := hr.ne'
  by_contra hcon
  push_neg at hcon
  apply h
  refine ⟨s, ?_, ⟨m, hsm.symm⟩, ?_⟩
  · rw [Nat.mem_divisors]
    refine ⟨?_, pow_ne_zero _ hrne⟩
    rw [← Nat.factorization_le_iff_dvd hspos.ne' (pow_ne_zero _ hrne), Finsupp.le_def]
    intro p
    rw [Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (s.factorization p) with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · have hpne : s.factorization p ≠ 0 := by omega
      have hpprime : p.Prime := by
        by_contra hp
        exact hpne ((Nat.factorization_eq_zero_iff s p).mpr (Or.inl hp))
      have hps : p ∣ s := Nat.dvd_of_factorization_pos hpne
      have hpr : p ∈ r.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hpprime, hsmooth p hpprime hps, hrne⟩
      have hrfac : 1 ≤ r.factorization p :=
        (hpprime.dvd_iff_one_le_factorization hrne).mp (Nat.mem_primeFactors.mp hpr).2.1
      have hle1 : s.factorization p ≤ n.factorization p :=
        (Finsupp.le_def.mp ((Nat.factorization_le_iff_dvd hspos.ne' (by omega)).mpr
          ⟨m, hsm.symm⟩)) p
      have hle2 : n.factorization p ≤ Kc := by
        by_contra hlt
        push_neg at hlt
        exact hcon p hpr ((hpprime.pow_dvd_iff_le_factorization (by omega)).mpr hlt)
      calc s.factorization p ≤ n.factorization p := hle1
        _ ≤ Kc := hle2
        _ = Kc * 1 := (mul_one Kc).symm
        _ ≤ Kc * r.factorization p := Nat.mul_le_mul_left _ hrfac
  · rw [← hsm, Nat.mul_div_cancel_left m hspos]; exact hmcop

/-- Pigeonhole: if a finite sum is at least `C`, some term is at least `C / card`. -/
lemma Finset.exists_ge_card_div {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℝ} {C : ℝ}
    (h : C ≤ ∑ i ∈ s, f i) : ∃ i ∈ s, C / s.card ≤ f i := by
  by_contra hc
  push_neg at hc
  have hlt : ∑ i ∈ s, f i < ∑ _i ∈ s, (C / s.card) :=
    Finset.sum_lt_sum_of_nonempty hs fun i hi => hc i hi
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hcard : (0:ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  rw [mul_div_cancel₀ _ hcard.ne'] at hlt
  linarith

private lemma final_step {η H' Y Nb Ab s : ℝ}
    (hAb : 0 < Ab) (hNb : 0 < Nb) (hη : 0 < η) (hH : 0 < H') (hY : 0 < Y) (hs1 : 1 ≤ s) :
    (η / (2 * Nb * Ab)) * (H'/s) * (Y/s) ≤ (η/2) * H' * Y / Nb / (Ab*s) := by
  have hs : (0:ℝ) < s := lt_of_lt_of_le one_pos hs1
  have hp : (0:ℝ) < η*H'*Y := by positivity
  have hL : (η / (2 * Nb * Ab)) * (H'/s) * (Y/s) = η*H'*Y/(2*Nb*Ab*s^2) := by
    field_simp
  have hR : (η/2) * H' * Y / Nb / (Ab*s) = η*H'*Y/(2*Nb*Ab*s) := by
    field_simp
  rw [hL, hR]
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*Nb*Ab*s^2) (by positivity : (0:ℝ) < 2*Nb*Ab*s)]
  have hss : (0:ℝ) ≤ s^2 - s := by nlinarith [hs, hs1]
  have hcoef : (0:ℝ) ≤ η*H'*Y*(2*Nb*Ab) := by positivity
  nlinarith [mul_nonneg hss hcoef]

/-! ## Target -/

theorem twist_reduction (θ θ' η : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < 1) (hθ'₀ : 0 < θ') (hθ'₁ : θ' < θ)
    (hη : 0 < η) (R : ℕ) :
    ∃ X₁ η' K : ℝ, 1 ≤ X₁ ∧ 0 < η' ∧ 1 ≤ K ∧
      ∀ (f : ArithmeticFunction ℂ), f.IsMultiplicative → BoundedMultiplicativeFunctions.IsOneBounded f →
      ∀ (r : ℕ) (ψ : ℕ → ℂ), 0 < r → r ≤ R → (∀ n, ψ (n + r) = ψ n) → (∀ n, ‖ψ n‖ ≤ 1) →
      ∀ (T₀ Y H' : ℝ), X₁ ≤ Y → Y ^ θ ≤ H' → H' ≤ Y → Work.BMF.TwistCorr f ψ T₀ Y H' η →
        ∃ (χ : DirichletCharacter ℂ r) (Y' H'' : ℝ),
          Y / K ≤ Y' ∧ Y' ≤ Y ∧ H' / K ≤ H'' ∧ H'' ≤ H' ∧ Y' / H'' = Y / H' ∧
          (Y') ^ θ' ≤ H'' ∧
          Work.BMF.TwistCorr (fun n ↦ (f n) * (χ n)) (fun _ ↦ 1) T₀ Y' H'' η' := by
  classical
  by_cases hR0 : R = 0
  · refine ⟨1, 1, 1, le_rfl, one_pos, le_rfl, ?_⟩
    intro f hf hf' r ψ hr hrR hper hbd T₀ Y H' hY hYH hHH hTw
    omega
  · have hR1 : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr hR0
    set Rr : ℝ := (R : ℝ) + 1 with hRr
    have hRrpos : 0 < Rr := by rw [hRr]; positivity
    have hRr1 : 1 ≤ Rr := by rw [hRr]; linarith [Nat.cast_nonneg (α := ℝ) R]
    obtain ⟨Kc, hKc⟩ : ∃ Kc : ℕ, Rr / 2 ^ Kc ≤ η / 8 := by
      have h2 : Filter.Tendsto (fun n : ℕ => (2:ℝ)^n) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h2.eventually_ge_atTop (8 * Rr / η))
      refine ⟨N, ?_⟩
      have hN' : 8 * Rr / η ≤ (2:ℝ)^N := hN N le_rfl
      have h2N : (0:ℝ) < 2^N := pow_pos (by norm_num) N
      rw [div_le_div_iff₀ h2N (by norm_num : (0:ℝ) < 8)]
      have hm := mul_le_mul_of_nonneg_right hN' (le_of_lt hη)
      rw [div_mul_cancel₀ _ hη.ne'] at hm
      nlinarith [hm]
    set K : ℝ := Rr ^ Kc with hK
    set Ab : ℝ := Rr with hAb
    set Nb : ℝ := (Rr ^ Kc + 1) * Rr with hNb
    set et : ℝ := η / (2 * Nb * Ab) with het
    have hetpos : 0 < et := by rw [het]; positivity
    have hK1 : 1 ≤ K := by rw [hK]; exact one_le_pow₀ hRr1
    have hAbpos : 0 < Ab := hAb ▸ hRrpos
    set X1 : ℝ := max 1 (max (K ^ ((1 - θ') / (θ - θ'))) ((16 * Rr / η) ^ (1 / θ))) with hX1
    have hX1ge1 : (1:ℝ) ≤ X1 := by rw [hX1]; exact le_max_left 1 _
    have hX1nn : (0:ℝ) ≤ X1 := le_trans zero_le_one hX1ge1
    refine ⟨X1, et, K, hX1ge1, hetpos, hK1, ?_⟩
    intro f hf hf' r ψ hr hrR hper hbd T₀ Y H' hY hYH hHH hTw
    haveI : NeZero r := ⟨hr.ne'⟩
    have hr1 : 1 ≤ r := hr
    have hY1 : (1:ℝ) ≤ Y := le_trans hX1ge1 hY
    have h1Y : (1:ℝ) ≤ Y^θ := Real.one_le_rpow hY1 hθ₀.le
    have hH'1 : 1 ≤ H' := le_trans h1Y hYH
    have hH'pos : 0 < H' := lt_of_lt_of_le one_pos hH'1
    have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
    have hY2Y : Y ≤ 2 * Y := by linarith
    have hAexp : (16 * Rr / η) ^ (1 / θ) ≤ X1 :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hX1pow : 16 * Rr / η ≤ X1 ^ θ := by
      have h0 : (0:ℝ) < 16 * Rr / η := by positivity
      calc 16 * Rr / η = ((16 * Rr / η) ^ (1/θ)) ^ θ := by
              rw [← Real.rpow_mul h0.le]
              rw [one_div, inv_mul_cancel₀ hθ₀.ne', Real.rpow_one]
        _ ≤ X1 ^ θ := Real.rpow_le_rpow (Real.rpow_nonneg h0.le _) hAexp hθ₀.le
    have hH'big : 16 * Rr / η ≤ H' :=
      le_trans hX1pow (le_trans (Real.rpow_le_rpow hX1nn hY hθ₀.le) hYH)
    have hX1K : K ^ ((1 - θ') / (θ - θ')) ≤ X1 :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hMsmooth : ∀ s ∈ (r^Kc).divisors, ∀ q, q.Prime → q ∣ s → q ∣ r := by
      intro s hsM q hq hqs
      rw [Nat.mem_divisors] at hsM
      exact hq.dvd_of_dvd_pow (dvd_trans hqs hsM.1)
    set X : ℕ → ℂ := fun n => (n : ℂ) ^ (-(Complex.I * T₀)) with hX
    have hXmul : ∀ s m : ℕ, X (s * m) = X s * X m := by
      intro s m
      simp only [hX, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    have hXnorm : ∀ n : ℕ, 1 ≤ n → ‖X n‖ = 1 := fun n hn => by
      simp only [hX]; exact norm_cpow_neg_I_mul T₀ hn
    set a : ℕ → DirichletCharacter ℂ r → ℂ :=
      fun s χ => ((r.totient : ℂ))⁻¹ * ∑ g : ZMod r, ψ (s * g.val) * conj (χ g) with ha
    have ha_bound : ∀ s χ, ‖a s χ‖ ≤ Ab := by
      intro s χ
      have hχ : ∀ g : ZMod r, ‖χ g‖ ≤ 1 := by
        intro g
        by_cases hg : IsUnit g
        · have h := DirichletCharacter.unit_norm_eq_one χ hg.unit
          rw [IsUnit.unit_spec] at h
          exact le_of_eq h
        · rw [MulChar.map_nonunit χ hg]; simp
      have hsum : ‖∑ g : ZMod r, ψ (s * g.val) * conj (χ g)‖ ≤ (r : ℝ) := by
        refine (norm_sum_le _ _).trans ?_
        calc ∑ g : ZMod r, ‖ψ (s * g.val) * conj (χ g)‖
            ≤ ∑ _g : ZMod r, (1:ℝ) := Finset.sum_le_sum fun g _ => by
                rw [norm_mul, Complex.norm_conj]
                exact mul_le_one₀ (hbd (s * g.val)) (norm_nonneg _) (hχ g)
          _ = (r : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
      have hnorm_inv : ‖((r.totient : ℂ))⁻¹‖ = ((r.totient : ℝ))⁻¹ := by
        rw [norm_inv, Complex.norm_natCast]
      have htot1 : (1:ℝ) ≤ (r.totient : ℝ) := by
        exact_mod_cast (Nat.totient_pos.mpr hr)
      calc ‖a s χ‖ = ‖((r.totient : ℂ))⁻¹ * ∑ g : ZMod r, ψ (s * g.val) * conj (χ g)‖ := by
              simp only [ha]
        _ ≤ ‖((r.totient : ℂ))⁻¹‖ * ‖∑ g : ZMod r, ψ (s * g.val) * conj (χ g)‖ := norm_mul_le _ _
        _ ≤ ((r.totient : ℝ))⁻¹ * (r : ℝ) := by
              rw [hnorm_inv]
              exact mul_le_mul_of_nonneg_left hsum (by positivity)
        _ ≤ 1 * (r:ℝ) :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ htot1) (Nat.cast_nonneg r)
        _ ≤ Ab := by
              rw [one_mul, hAb]
              have : (r:ℝ) ≤ (R:ℝ) := by exact_mod_cast hrR
              linarith
    have hexp : ∀ (s m : ℕ), m.Coprime r →
        ψ (s * m) = ∑ χ : DirichletCharacter ℂ r, a s χ * χ m := by
      intro s m hm
      have hper_per : Function.Periodic ψ r := hper
      have hper' : Function.Periodic (fun t => ψ (s * t)) r := by
        intro t
        show ψ (s * (t + r)) = ψ (s * t)
        have h := hper_per.nsmul s (s * t)
        rw [Nat.mul_add]
        simpa [nsmul_eq_mul] using h
      have hchar := char_expansion r (fun t => ψ (s * t)) hper' m hm
      simp only [ha]
      exact hchar
    have hpoint : ∀ (s n : ℕ), s ∈ (r^Kc).divisors → s ∣ n → (n / s).Coprime r →
        f n * ψ n * X n
          = ∑ χ : DirichletCharacter ℂ r,
              a s χ * (f s * X s) * (f (n / s) * X (n / s) * χ (n / s)) := by
      intro s n hsM hd hc
      have hq : ∀ q, q.Prime → q ∣ s → q ∣ r := hMsmooth s hsM
      have hcop : s.Coprime (n / s) := by
        refine Nat.coprime_of_dvd fun q hq' hqs hqm => ?_
        have hqr : q ∣ r := hq q hq' hqs
        have : q ∣ (n/s).gcd r := Nat.dvd_gcd hqm hqr
        rw [hc.gcd_eq_one] at this
        exact hq'.not_dvd_one this
      have hsn : s * (n / s) = n := Nat.mul_div_cancel' hd
      have hfeq : f n = f s * f (n / s) := by
        conv_lhs => rw [show n = s * (n / s) from hsn.symm]
        exact hf.map_mul_of_coprime hcop.gcd_eq_one
      have hψeq : ψ n = ∑ χ : DirichletCharacter ℂ r, a s χ * χ (n / s) := by
        conv_lhs => rw [show n = s * (n / s) from hsn.symm]
        exact hexp s (n / s) hc
      have hXeq : X n = X s * X (n / s) := by
        conv_lhs => rw [show n = s * (n / s) from hsn.symm]
        exact hXmul s (n / s)
      rw [hfeq, hψeq, hXeq, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun χ _ => ?_
      ring
    set SF : ℝ → ℂ := fun y => ∑ n ∈ natIcc y (y + H'), f n * ψ n * X n with hSF
    set tailF : ℝ → ℂ := fun y => ∑ n ∈ (natIcc y (y + H')).filter
        (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n / s).Coprime r),
        f n * ψ n * X n with htailF
    set Vf : ℕ → DirichletCharacter ℂ r → ℝ → ℂ :=
      fun s χ z => ∑ m ∈ (natIcc z (z + H'/s)).filter (fun m => m.Coprime r),
        f m * X m * χ m with hVf
    have hdecomp : ∀ y : ℝ, 0 ≤ y + H' → SF y =
        (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
          a s χ * (f s * X s) * Vf s χ (y / s)) + tailF y := by
      intro y hyH
      have h1 : SF y = (∑ n ∈ (natIcc y (y+H')).filter
            (fun n => ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r),
              f n * ψ n * X n) + tailF y := by
        simp only [hSF, htailF]
        exact (Finset.sum_filter_add_sum_filter_not (s := natIcc y (y+H'))
          (p := fun n => ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r)
          (f := fun n => f n * ψ n * X n)).symm
      rw [h1, ← sum_split_rSmooth r Kc hr1 (natIcc y (y+H')) (fun n => f n * ψ n * X n)]
      congr 1
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs' : 0 < s := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hs).1 (pow_pos hr Kc)
      have hinner : (∑ n ∈ (natIcc y (y+H')).filter (fun n => s ∣ n ∧ (n/s).Coprime r),
            f n * ψ n * X n)
          = ∑ n ∈ (natIcc y (y+H')).filter (fun n => s ∣ n ∧ (n/s).Coprime r),
              ∑ χ : DirichletCharacter ℂ r,
                a s χ * (f s * X s) * (f (n/s) * X (n/s) * χ (n/s)) :=
        Finset.sum_congr rfl fun n hn =>
          hpoint s n hs (Finset.mem_filter.mp hn).2.1 (Finset.mem_filter.mp hn).2.2
      rw [hinner, Finset.sum_comm]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      rw [hVf]
      exact sum_bij_div_coprime hs' hyH (fun m => f m * X m * χ m)
    have hmultcard : ∀ (p : ℕ) (y : ℝ), 0 < p → 0 ≤ y + H' →
        ((natIcc y (y+H')).filter (fun n => p ∣ n)).card ≤ H'/p + 1 := by
      intro p y hp hyH
      have hbij : (natIcc y (y+H')).filter (fun n => p ∣ n)
          = (natIcc (y/p) (y/p + H'/p)).image (fun j => p * j) := by
        ext n
        rw [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨hn, hdvd⟩
          refine ⟨n/p, ?_, Nat.mul_div_cancel' hdvd⟩
          have : p * (n/p) ∈ natIcc y (y+H') := by rw [Nat.mul_div_cancel' hdvd]; exact hn
          exact (mem_natIcc_div_iff hp hyH).mp this
        · rintro ⟨j, hj, rfl⟩
          exact ⟨(mem_natIcc_div_iff hp hyH).mpr hj, dvd_mul_right p j⟩
      set A : ℕ := ⌈y/p⌉₊ with hAdef
      set B : ℕ := ⌊y/p + H'/p⌋₊ with hBdef
      have hcard : (natIcc (y/p) (y/p + H'/p)).card = B + 1 - A := by
        rw [natIcc, hAdef, hBdef, Nat.card_Icc]
      rw [hbij]
      have hc1 : (((natIcc (y/p) (y/p + H'/p)).image (fun j => p * j)).card : ℝ)
          ≤ ((natIcc (y/p) (y/p + H'/p)).card : ℝ) := by
        exact_mod_cast (Finset.card_image_le (s := natIcc (y/p) (y/p + H'/p)) (f := fun j => p * j))
      refine hc1.trans ?_
      rw [hcard]
      have hBle : (B:ℝ) ≤ y/p + H'/p :=
        Nat.floor_le (by rw [← add_div]; exact div_nonneg hyH (Nat.cast_nonneg p))
      have hAle : y/p ≤ (A:ℝ) := Nat.le_ceil _
      by_cases hab : A ≤ B + 1
      · rw [Nat.cast_sub hab]
        push_cast
        linarith
      · have : B + 1 - A = 0 := by omega
        rw [this]
        push_cast
        have : (0:ℝ) ≤ H'/p := by positivity
        linarith
    have htail_card : ∀ y : ℝ, 1 ≤ y →
        (((natIcc y (y+H')).filter
          (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r)).card : ℝ)
        ≤ Rr * (H'/2^(Kc+1) + 1) := by
      intro y hy
      have hyH : 0 ≤ y + H' := by linarith [hH'pos]
      have hsub : (natIcc y (y+H')).filter
          (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r)
          ⊆ r.primeFactors.biUnion
              (fun p => (natIcc y (y+H')).filter (fun n => p^(Kc+1) ∣ n)) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_biUnion]
        have hn1 : 1 ≤ n := by
          rw [natIcc, Finset.mem_Icc] at hn
          have hc1 : 1 ≤ ⌈y⌉₊ := Nat.ceil_pos.mpr (by linarith)
          omega
        obtain ⟨p, hp, hpd⟩ := not_covered_imp r Kc n hr hn1 hn.2
        exact ⟨p, hp, by rw [Finset.mem_filter]; exact ⟨hn.1, hpd⟩⟩
      have h1 : (((natIcc y (y+H')).filter
          (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r)).card : ℝ)
          ≤ ((r.primeFactors.biUnion
              (fun p => (natIcc y (y+H')).filter (fun n => p^(Kc+1) ∣ n))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      refine h1.trans ?_
      refine ((by exact_mod_cast (Finset.card_biUnion_le :
          (r.primeFactors.biUnion (fun p => (natIcc y (y+H')).filter (fun n => p^(Kc+1) ∣ n))).card
          ≤ ∑ p ∈ r.primeFactors, ((natIcc y (y+H')).filter (fun n => p^(Kc+1) ∣ n)).card)
        : ((r.primeFactors.biUnion (fun p => (natIcc y (y+H')).filter (fun n => p^(Kc+1) ∣ n))).card : ℝ)
          ≤ ((∑ p ∈ r.primeFactors, ((natIcc y (y+H')).filter (fun n => p^(Kc+1) ∣ n)).card : ℕ) : ℝ))).trans ?_
      rw [Nat.cast_sum]
      have h2 : ∑ p ∈ r.primeFactors,
            (((natIcc y (y+H')).filter (fun n => p^(Kc+1) ∣ n)).card : ℝ)
          ≤ ∑ _p ∈ r.primeFactors, (H'/2^(Kc+1) + 1) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        have hppos : 0 < p := hpprime.pos
        have hple : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hpprime.two_le
        have hpe : (2:ℝ) ^ (Kc+1) ≤ (p:ℝ) ^ (Kc+1) :=
          pow_le_pow_left₀ (by norm_num) hple _
        have h2p : (0:ℝ) < (2:ℝ)^(Kc+1) := by positivity
        have hpp : (0:ℝ) < (p:ℝ)^(Kc+1) := by positivity
        have hmm := hmultcard (p^(Kc+1)) y (pow_pos hppos _) hyH
        refine hmm.trans ?_
        have hdiv : H'/((p:ℝ)^(Kc+1)) ≤ H'/((2:ℝ)^(Kc+1)) := by
          rw [div_le_div_iff₀ hpp h2p]
          nlinarith [hH'pos, hpe]
        have hcast : ((p^(Kc+1) : ℕ) : ℝ) = (p:ℝ)^(Kc+1) := by push_cast; ring
        rw [hcast]
        linarith
      refine h2.trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : ((r.primeFactors.card : ℕ) : ℝ) ≤ Rr := by
        have hcard3 : r.primeFactors.card ≤ R + 1 := by
          refine (Finset.card_le_card ?_).trans_eq (Finset.card_range (R+1))
          intro q hq
          rw [Finset.mem_range]
          have := (Nat.mem_primeFactors.mp hq).2.1
          have hqr : q ≤ r := Nat.le_of_dvd hr this
          omega
        have : ((r.primeFactors.card : ℕ) : ℝ) ≤ (R:ℝ) + 1 := by exact_mod_cast hcard3
        exact this
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have htail_bound : ∀ y : ℝ, 1 ≤ y →
        ‖tailF y‖ ≤ (Rr / 2^(Kc+1)) * H' + Rr := by
      intro y hy
      have hsummand : ∀ n ∈ (natIcc y (y+H')).filter
            (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r),
          ‖f n * ψ n * X n‖ ≤ 1 := by
        intro n hn
        rw [Finset.mem_filter] at hn
        have hn1 : 1 ≤ n := by
          rw [natIcc, Finset.mem_Icc] at hn
          have hc1 : 1 ≤ ⌈y⌉₊ := Nat.ceil_pos.mpr (by linarith)
          omega
        rw [norm_mul, norm_mul, hXnorm n hn1, mul_one]
        exact mul_le_one₀ (hf' n) (norm_nonneg _) (hbd n)
      have hcardb := htail_card y hy
      calc ‖tailF y‖
          = ‖∑ n ∈ (natIcc y (y+H')).filter
              (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r),
              f n * ψ n * X n‖ := by rw [htailF]
        _ ≤ ∑ n ∈ (natIcc y (y+H')).filter
              (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r),
              ‖f n * ψ n * X n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ (natIcc y (y+H')).filter
              (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r), (1:ℝ) :=
              Finset.sum_le_sum hsummand
        _ = (((natIcc y (y+H')).filter
              (fun n => ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n/s).Coprime r)).card : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ Rr * (H'/2^(Kc+1) + 1) := by exact_mod_cast hcardb
        _ = (Rr / 2^(Kc+1)) * H' + Rr := by
              rw [div_eq_mul_inv]; ring
    have hpt : ∀ y ∈ Set.Icc Y (2*Y),
        ‖SF y‖ ≤ (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
            Ab * ‖Vf s χ (y/s)‖) + ‖tailF y‖ := by
      intro y hy
      have hyH : 0 ≤ y + H' := by
        have : (1:ℝ) ≤ y := le_trans hY1 hy.1
        linarith [hH'pos]
      rw [hdecomp y hyH]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ?_ (le_refl _)
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun s hs => ?_
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun χ _ => ?_
      have hs1 : 1 ≤ s := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hs).1 (pow_pos hr Kc)
      calc ‖a s χ * (f s * X s) * Vf s χ (y/s)‖
          ≤ ‖a s χ * (f s * X s)‖ * ‖Vf s χ (y/s)‖ := norm_mul_le _ _
        _ ≤ Ab * ‖Vf s χ (y/s)‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            calc ‖a s χ * (f s * X s)‖ ≤ ‖a s χ‖ * ‖f s * X s‖ := norm_mul_le _ _
              _ ≤ Ab * 1 := by
                  refine mul_le_mul (ha_bound s χ) ?_ (norm_nonneg _) hAbpos.le
                  rw [norm_mul, hXnorm s hs1, mul_one]
                  exact hf' s
              _ = Ab := mul_one Ab
    -- integrability
    have hSFint : IntervalIntegrable (fun y : ℝ => ‖SF y‖) volume Y (2 * Y) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY2Y]
      have h := integrableOn_norm_stepFun (fun n => f n * ψ n * X n) H' Y (2 * Y)
      simpa only [hSF] using h
    have htailint : IntervalIntegrable (fun y : ℝ => ‖tailF y‖) volume Y (2 * Y) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY2Y]
      have h := integrableOn_norm_stepFun
        (fun n => if ¬ ∃ s ∈ (r^Kc).divisors, s ∣ n ∧ (n / s).Coprime r
          then f n * ψ n * X n else 0) H' Y (2 * Y)
      simpa only [htailF, Finset.sum_filter] using h
    have hVint : ∀ s χ, IntervalIntegrable
        (fun y : ℝ => Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) volume Y (2 * Y) := by
      intro s χ
      set gV : ℕ → ℂ := fun m => if m.Coprime r then f m * X m * χ m else 0 with hgV
      have hVeq : ∀ z : ℝ, Vf s χ z = ∑ m ∈ natIcc z (z + H'/s), gV m := by
        intro z
        simp only [hVf, hgV, Finset.sum_filter]
      have hA : IntervalIntegrable (fun y : ℝ =>
          Ab * ‖∑ m ∈ natIcc ((s:ℝ)⁻¹*y) ((s:ℝ)⁻¹*y + H'/s), gV m‖) volume Y (2*Y) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hY2Y]
        have hmeas : Measurable (fun y : ℝ =>
            ∑ m ∈ natIcc ((s:ℝ)⁻¹ * y) ((s:ℝ)⁻¹ * y + H'/s), gV m) :=
          (measurable_stepFun gV (H'/s)).comp (measurable_const.mul measurable_id)
        refine MeasureTheory.IntegrableOn.of_bound ?_ ((hmeas.norm.const_mul Ab).aestronglyMeasurable)
          (Ab * ∑ m ∈ Finset.range (⌊(s:ℝ)⁻¹ * (2*Y) + H'/s⌋₊ + 1), ‖gV m‖) ?_
        · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
        · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
          refine Filter.Eventually.of_forall fun y hy => ?_
          have hsub : natIcc ((s:ℝ)⁻¹*y) ((s:ℝ)⁻¹*y + H'/s) ⊆
              Finset.range (⌊(s:ℝ)⁻¹ * (2*Y) + H'/s⌋₊ + 1) := by
            intro m hm
            rw [natIcc, Finset.mem_Icc] at hm
            rw [Finset.mem_range]
            have hyl : (s:ℝ)⁻¹*y ≤ (s:ℝ)⁻¹*(2*Y) :=
              mul_le_mul_of_nonneg_left hy.2 (by positivity : (0:ℝ) ≤ (s:ℝ)⁻¹)
            have : ⌊(s:ℝ)⁻¹*y + H'/s⌋₊ ≤ ⌊(s:ℝ)⁻¹*(2*Y) + H'/s⌋₊ :=
              Nat.floor_mono (by linarith)
            omega
          calc ‖Ab * ‖∑ m ∈ natIcc ((s:ℝ)⁻¹*y) ((s:ℝ)⁻¹*y + H'/s), gV m‖‖
              = Ab * ‖∑ m ∈ natIcc ((s:ℝ)⁻¹*y) ((s:ℝ)⁻¹*y + H'/s), gV m‖ := by
                rw [norm_mul, Real.norm_of_nonneg hAbpos.le, norm_norm]
            _ ≤ Ab * ∑ m ∈ Finset.range (⌊(s:ℝ)⁻¹ * (2*Y) + H'/s⌋₊ + 1), ‖gV m‖ := by
                refine mul_le_mul_of_nonneg_left ?_ hAbpos.le
                exact (norm_sum_le _ _).trans
                  (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _))
      exact IntervalIntegrable.congr (f := fun y : ℝ =>
        Ab * ‖∑ m ∈ natIcc ((s:ℝ)⁻¹*y) ((s:ℝ)⁻¹*y + H'/s), gV m‖)
        (fun x _ => by rw [hVeq ((s:ℝ)⁻¹*x)]) hA
    have hphint : IntervalIntegrable (fun y : ℝ => ∑ s ∈ (r^Kc).divisors,
        ∑ χ : DirichletCharacter ℂ r, Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) volume Y (2*Y) := by
      have h1 : IntervalIntegrable (∑ s ∈ (r^Kc).divisors,
          fun y : ℝ => ∑ χ : DirichletCharacter ℂ r, Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖)
          volume Y (2*Y) := by
        refine IntervalIntegrable.sum (s := (r^Kc).divisors) ?_
        intro s hs
        refine IntervalIntegrable.congr (f := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)),
            fun y : ℝ => Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) ?_ ?_
        · intro x _
          rw [Finset.sum_apply]
        · refine IntervalIntegrable.sum (s := Finset.univ) ?_
          intro χ _
          exact IntervalIntegrable.congr (f := fun y : ℝ => Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖)
            (fun x _ => rfl) (hVint s χ)
      refine IntervalIntegrable.congr (f := ∑ s ∈ (r^Kc).divisors,
          fun y : ℝ => ∑ χ : DirichletCharacter ℂ r, Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) ?_ h1
      intro x _
      rw [Finset.sum_apply]
    have hPhint : IntervalIntegrable (fun y : ℝ =>
        (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
          Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) + ‖tailF y‖) volume Y (2 * Y) :=
      hphint.add htailint
    have hmono : ∫ y in Y..(2*Y), ‖SF y‖ ≤ ∫ y in Y..(2*Y),
        (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
          Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) + ‖tailF y‖ := by
      refine intervalIntegral.integral_mono_on hY2Y hSFint hPhint fun y hy => ?_
      have hyI : y ∈ Set.Icc Y (2*Y) := ⟨hy.1, hy.2⟩
      refine (hpt y hyI).trans ?_
      refine add_le_add ?_ (le_refl _)
      refine Finset.sum_le_sum fun s hs => ?_
      refine Finset.sum_le_sum fun χ _ => ?_
      rw [show ((s:ℝ)⁻¹ * y) = y/s from by rw [div_eq_inv_mul]]
    have hsplitint : ∫ y in Y..(2*Y),
        (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
          Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) + ‖tailF y‖
        = (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
            Ab * ∫ y in Y..(2*Y), ‖Vf s χ ((s:ℝ)⁻¹ * y)‖)
          + ∫ y in Y..(2*Y), ‖tailF y‖ := by
      rw [intervalIntegral.integral_add hphint htailint]
      congr 1
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl fun s hs => ?_
        rw [intervalIntegral.integral_finset_sum]
        · refine Finset.sum_congr rfl fun χ _ => ?_
          rw [intervalIntegral.integral_const_mul]
        · intro χ _; exact hVint s χ
      · intro s hs
        refine IntervalIntegrable.congr (f := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ r)),
            fun y : ℝ => Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) ?_ ?_
        · intro x _
          rw [Finset.sum_apply]
        · refine IntervalIntegrable.sum (s := Finset.univ) ?_
          intro χ _
          exact IntervalIntegrable.congr (f := fun y : ℝ => Ab * ‖Vf s χ ((s:ℝ)⁻¹ * y)‖)
            (fun x _ => rfl) (hVint s χ)
    have hcov : ∀ s ∈ (r^Kc).divisors, ∀ χ : DirichletCharacter ℂ r,
        ∫ y in Y..(2*Y), ‖Vf s χ ((s:ℝ)⁻¹ * y)‖
          = (s:ℝ) * ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖ := by
      intro s hs χ
      have hspos : (0:ℝ) < s := by
        exact_mod_cast Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hs).1 (pow_pos hr Kc)
      have hsne : ((s:ℝ)⁻¹) ≠ 0 := inv_ne_zero hspos.ne'
      have h := intervalIntegral.integral_comp_mul_left (a := Y) (b := 2*Y) (fun z : ℝ => ‖Vf s χ z‖) hsne
      rw [h]
      simp only [inv_inv, smul_eq_mul, div_eq_inv_mul]
    have htailintbound : ∫ y in Y..(2*Y), ‖tailF y‖ ≤ (η/2) * H' * Y := by
      have hmono2 : ∫ y in Y..(2*Y), ‖tailF y‖ ≤
          ∫ _y in Y..(2*Y), ((Rr / 2^(Kc+1)) * H' + Rr) := by
        refine intervalIntegral.integral_mono_on hY2Y htailint intervalIntegrable_const ?_
        intro y hy
        exact htail_bound y (le_trans hY1 hy.1)
      refine hmono2.trans ?_
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have hA : Rr / 2^(Kc+1) ≤ η/16 := by
        have : Rr / 2^(Kc+1) = (Rr / 2^Kc)/2 := by rw [pow_succ]; ring
        rw [this]; linarith [hKc]
      have hB : Rr ≤ (η/16) * H' := by
        have h1 : (η/16) * (16*Rr/η) = Rr := by field_simp
        have h2 := mul_le_mul_of_nonneg_left hH'big (by positivity : (0:ℝ) ≤ η/16)
        rwa [h1] at h2
      have hYnn : (0:ℝ) ≤ Y := hYpos.le
      nlinarith [hA, hB, hYnn, hH'pos,
        mul_le_mul_of_nonneg_right hA hH'pos.le, mul_nonneg hH'pos.le hYnn]
    have hhyp : η * H' * Y ≤ ∫ y in Y..(2*Y), ‖SF y‖ := by
      have h := hTw
      simpa only [TwistCorr, hSF, hX] using h
    have hkey : (η/2) * H' * Y ≤ ∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
        Ab * ((s:ℝ) * ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖) := by
      have h3 : η * H' * Y ≤ (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
            Ab * ∫ y in Y..(2*Y), ‖Vf s χ ((s:ℝ)⁻¹ * y)‖) + ∫ y in Y..(2*Y), ‖tailF y‖ := by
        rw [← hsplitint]
        exact (hhyp.trans hmono)
      have h4 : (∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
            Ab * ∫ y in Y..(2*Y), ‖Vf s χ ((s:ℝ)⁻¹ * y)‖)
          = ∑ s ∈ (r^Kc).divisors, ∑ χ : DirichletCharacter ℂ r,
            Ab * ((s:ℝ) * ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖) := by
        refine Finset.sum_congr rfl fun s hs => ?_
        refine Finset.sum_congr rfl fun χ _ => by rw [hcov s hs χ]
      rw [h4] at h3
      linarith [htailintbound]
    have hDpos : ((r^Kc).divisors).Nonempty :=
      ⟨1, Nat.one_mem_divisors.mpr (pow_ne_zero _ hr.ne')⟩
    have hunivpos : (Finset.univ : Finset (DirichletCharacter ℂ r)).Nonempty :=
      ⟨1, Finset.mem_univ _⟩
    obtain ⟨s, hs, hsC⟩ := Finset.exists_ge_card_div hDpos hkey
    obtain ⟨χ, -, hχC⟩ := Finset.exists_ge_card_div hunivpos hsC
    -- number of terms
    have hNterms : ((r^Kc).divisors.card : ℝ) * (Fintype.card (DirichletCharacter ℂ r) : ℝ)
        ≤ Nb := by
      rw [hNb]
      have h1 : ((r^Kc).divisors.card : ℝ) ≤ Rr^Kc + 1 := by
        have hcard1 : (r^Kc).divisors.card ≤ r^Kc + 1 := by
          refine (Finset.card_le_card ?_).trans_eq (Finset.card_range (r^Kc + 1))
          intro q hq
          rw [Finset.mem_range, Nat.lt_succ_iff]
          exact Nat.le_of_dvd (pow_pos hr Kc) (Nat.mem_divisors.mp hq).1
        have hrr : (r:ℝ)^Kc ≤ Rr^Kc := by
          refine pow_le_pow_left₀ (Nat.cast_nonneg r) ?_ Kc
          show (r:ℝ) ≤ (R:ℝ) + 1
          have h : (r:ℝ) ≤ (R:ℝ) := by exact_mod_cast hrR
          linarith [h, Nat.cast_nonneg (α := ℝ) R]
        have hcast : ((r^Kc + 1 : ℕ) : ℝ) = (r:ℝ)^Kc + 1 := by push_cast; ring
        calc ((r^Kc).divisors.card : ℝ) ≤ ((r^Kc + 1 : ℕ) : ℝ) := by exact_mod_cast hcard1
          _ = (r:ℝ)^Kc + 1 := hcast
          _ ≤ Rr^Kc + 1 := by linarith
      have h2 : (Fintype.card (DirichletCharacter ℂ r) : ℝ) ≤ Rr := by
        have hc : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
        rw [hc]
        have h1' : r.totient ≤ r := Nat.totient_le r
        have h2' : (r:ℝ) ≤ Rr := by
          show (r:ℝ) ≤ (R:ℝ) + 1
          have h : (r:ℝ) ≤ (R:ℝ) := by exact_mod_cast hrR
          linarith [h, Nat.cast_nonneg (α := ℝ) R]
        calc (r.totient : ℝ) ≤ (r:ℝ) := by exact_mod_cast h1'
          _ ≤ Rr := h2'
      refine mul_le_mul h1 h2 (by positivity) (by positivity)
    have hsleK : (s:ℝ) ≤ K := by
      have hsle : s ≤ r^Kc := Nat.le_of_dvd (pow_pos hr Kc) (Nat.mem_divisors.mp hs).1
      have h1 : (s:ℝ) ≤ (r:ℝ)^Kc := by exact_mod_cast hsle
      have h2 : (r:ℝ)^Kc ≤ Rr^Kc := by
        refine pow_le_pow_left₀ (Nat.cast_nonneg r) ?_ Kc
        show (r:ℝ) ≤ (R:ℝ) + 1
        have h : (r:ℝ) ≤ (R:ℝ) := by exact_mod_cast hrR
        linarith [h, Nat.cast_nonneg (α := ℝ) R]
      rw [hK]
      linarith
    have hs1 : 1 ≤ s := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hs).1 (pow_pos hr Kc)
    have hspos : (0:ℝ) < s := by exact_mod_cast hs1
    have hcardpos : (0:ℝ) < ((r^Kc).divisors.card : ℝ) :=
      by exact_mod_cast Finset.card_pos.mpr hDpos
    have hcpos : (0:ℝ) < (Fintype.card (DirichletCharacter ℂ r) : ℝ) :=
      by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(1 : DirichletCharacter ℂ r)⟩
    have hstep : (η/2) * H' * Y / Nb
        ≤ Ab * ((s:ℝ) * ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖) := by
      refine le_trans ?_ hχC
      rw [div_div]
      refine div_le_div_of_nonneg_left (by positivity) (mul_pos hcardpos hcpos) hNterms
    have hfinal : et * (H'/s) * (Y/s) ≤ ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖ := by
      have habs : (0:ℝ) < Ab * (s:ℝ) := mul_pos hAbpos hspos
      have hInt : (η/2) * H' * Y / Nb / (Ab * (s:ℝ))
          ≤ ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖ := by
        rw [div_le_iff₀ habs]
        calc (η/2) * H' * Y / Nb ≤ Ab * ((s:ℝ) * ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖) := hstep
          _ = (∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖) * (Ab * (s:ℝ)) := by ring
      refine le_trans ?_ hInt
      have hNbpos : (0:ℝ) < Nb := by positivity
      rw [het]
      exact final_step hAbpos hNbpos hη hH'pos hYpos (by exact_mod_cast hs1)
    have hKpos : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
    have hbH : (0:ℝ) ≤ (θ-θ')/(1-θ') :=
      div_nonneg (sub_pos.mpr hθ'₁).le (sub_pos.mpr (lt_trans hθ'₁ hθ₁)).le
    have hKle : K ≤ Y ^ ((θ-θ')/(1-θ')) := by
      calc K = (K ^ ((1-θ')/(θ-θ'))) ^ ((θ-θ')/(1-θ')) := by
              rw [← Real.rpow_mul hKpos.le]
              have hne1 : θ - θ' ≠ 0 := (sub_pos.mpr hθ'₁).ne'
              have hne2 : (1:ℝ) - θ' ≠ 0 := (sub_pos.mpr (lt_trans hθ'₁ hθ₁)).ne'
              have : (1-θ')/(θ-θ') * ((θ-θ')/(1-θ')) = 1 := by
                field_simp
              rw [this, Real.rpow_one]
        _ ≤ Y ^ ((θ-θ')/(1-θ')) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hKpos.le _) (hX1K.trans hY) hbH
    have hsleY : (s:ℝ) ≤ Y ^ ((θ-θ')/(1-θ')) := hsleK.trans hKle
    have hs_pow : (s:ℝ) ^ (1-θ') ≤ Y ^ (θ-θ') := by
      have h1 := Real.rpow_le_rpow hspos.le hsleY (by linarith : (0:ℝ) ≤ 1-θ')
      rwa [← Real.rpow_mul hYpos.le,
        show (θ-θ')/(1-θ') * (1-θ') = θ-θ' from
          div_mul_cancel₀ _ (sub_pos.mpr (lt_trans hθ'₁ hθ₁)).ne'] at h1
    have hmain1 : Y^θ' * (s:ℝ)^(1-θ') ≤ H' := by
      calc Y^θ' * (s:ℝ)^(1-θ') ≤ Y^θ' * Y^(θ-θ') :=
            mul_le_mul_of_nonneg_left hs_pow (Real.rpow_nonneg hYpos.le _)
        _ = Y^(θ' + (θ-θ')) := by rw [Real.rpow_add hYpos]
        _ = Y^θ := by ring_nf
        _ ≤ H' := hYH
    refine ⟨χ, Y/s, H'/s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [div_le_div_iff₀ hKpos hspos]
      exact mul_le_mul_of_nonneg_left hsleK hYpos.le
    · rw [div_le_iff₀ hspos]
      have h1s : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs1
      simpa using mul_le_mul_of_nonneg_left h1s hYpos.le
    · rw [div_le_div_iff₀ hKpos hspos]
      exact mul_le_mul_of_nonneg_left hsleK hH'pos.le
    · rw [div_le_iff₀ hspos]
      have h1s : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs1
      simpa using mul_le_mul_of_nonneg_left h1s hH'pos.le
    · field_simp
    · rw [Real.div_rpow hYpos.le hspos.le,
        div_le_div_iff₀ (Real.rpow_pos_of_pos hspos _) hspos]
      have hsθ'pos : (0:ℝ) < (s:ℝ)^θ' := Real.rpow_pos_of_pos hspos _
      have hs1sub : (s:ℝ)^(1-θ') = (s:ℝ)/(s:ℝ)^θ' := by
        rw [Real.rpow_sub hspos]; norm_num
      rw [hs1sub] at hmain1
      have h1 : Y^θ' * ((s:ℝ)/(s:ℝ)^θ') * (s:ℝ)^θ' = Y^θ' * (s:ℝ) := by
        rw [mul_assoc, div_mul_cancel₀ _ hsθ'pos.ne']
      have h2 := mul_le_mul_of_nonneg_right hmain1 hsθ'pos.le
      rw [h1] at h2
      linarith [h2]
    · have hVeq2 : ∀ z : ℝ, Vf s χ z
          = ∑ n ∈ natIcc z (z + H'/s), (f n * χ n) * 1 * (n:ℂ)^(-(Complex.I * T₀)) := by
        intro z
        have hone : (∑ n ∈ (natIcc z (z + H'/s)).filter (fun m => m.Coprime r),
            f n * X n * χ n)
            = ∑ n ∈ natIcc z (z + H'/s), (f n * χ n) * 1 * (n:ℂ)^(-(Complex.I * T₀)) := by
          calc (∑ n ∈ (natIcc z (z + H'/s)).filter (fun m => m.Coprime r), f n * X n * χ n)
              = ∑ n ∈ (natIcc z (z + H'/s)).filter (fun m => m.Coprime r),
                  (f n * χ n) * 1 * (n:ℂ)^(-(Complex.I * T₀)) :=
                Finset.sum_congr rfl (fun n _ => by rw [hX]; ring)
            _ = ∑ n ∈ natIcc z (z + H'/s), (f n * χ n) * 1 * (n:ℂ)^(-(Complex.I * T₀)) :=
                Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hnf => by
                  rw [Finset.mem_filter, not_and] at hnf
                  have hnc : ¬ n.Coprime r := hnf hn
                  rw [MulChar.map_nonunit χ ((ZMod.isUnit_iff_coprime n r).not.mpr hnc)]
                  ring)
        show (∑ m ∈ (natIcc z (z + H'/s)).filter (fun m => m.Coprime r), f m * X m * χ m)
            = ∑ n ∈ natIcc z (z + H'/s), (f n * χ n) * 1 * (n:ℂ)^(-(Complex.I * T₀))
        exact hone
      have hIeq : ∫ z in Y/s..(2*Y)/s, ‖Vf s χ z‖
          = ∫ z in Y/s..(2*(Y/s)), ‖∑ n ∈ natIcc z (z + H'/s),
              (f n * χ n) * 1 * (n:ℂ)^(-(Complex.I * T₀))‖ := by
        rw [show (2*Y)/s = 2*(Y/s) from by ring]
        refine intervalIntegral.integral_congr fun z _ => ?_
        rw [hVeq2 z]
      change et * (H'/s) * (Y/s) ≤ ∫ z in (Y/s)..(2*(Y/s)),
        ‖∑ n ∈ natIcc z (z + H'/s), (f n * χ n) * 1 * (n:ℂ)^(-(Complex.I * T₀))‖
      rw [hIeq] at hfinal
      exact hfinal
end Work.BMF
