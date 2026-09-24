import Mathlib
import Submission.Work.GM.S2.Defs
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.hhat_sum_tail
import Submission.Work.GM.S2.hhat_neg_symm
import Submission.Work.GM.S2.trunc_tail_bound
import Submission.Work.GM.S2.tail_arith2
import Submission.Work.GM.S2.geom_two_sums
import Submission.Work.GM.S2.level_sum_arith
import Submission.Work.GM.S2.levN_rpow_bound
import Submission.Work.GM.S2.small_level_sum_arith
import Submission.Work.GM.S2.pos_half_reflection
import Submission.Work.GM.S2.ghat1_weighted_mass
import Submission.Work.GM.S2.hb_poly_pair_sum
import Submission.Work.GM.S2.norm_Sall_le
import Submission.Work.GM.S2.norm_Sall_small
import Submission.Work.GM.S2.level_count_bound
import Submission.Work.GM.S2.eventually_large

/-!
# GM §6: the pair-sum bound (`S₂`)

This file proves the "pair sum" form of Guth–Maynard Proposition 6.1 with `k = 4`:
with `T = M N = N^{6/5}` and `W ⊆ [0,T]` a `T^ε`-separated finite set,

`Σ_{t₁,t₂ ∈ W} ‖Σ_{m ≠ 0} ĥ_{t₁-t₂}(mN)‖² ⪅ |W|²/N + T|W|^{7/4}/N² + T^{1/8}|W|^{29/16}/N`,

which is `S₂/(3N³ĥ₀(0))` by the identity of §6 (the terms with `t₁ = t₃` are negligible
and `ĥ_0(0) = ∫ w²` is a positive constant).

The proof follows the paper:
* diagonal / small `|t₁-t₂|`: the decay of `ĥ_t` (`hdec`) gives an absolutely convergent
  majorant, hence a bound `≪ T^{-ηj}`;
* for a dyadic level `|t₁-t₂| ≍ 2^k`, the reflection hypothesis `hrefl` turns both halves of
  `Σ_{m≠0}` into the short Dirichlet polynomial `Σ_{m ≤ Y_k} m^{i(t₁-t₂±2πξ)}` of length
  `Y_k ≍ 2^k T^η/N`; Cauchy–Schwarz in `ξ` and the fully processed Heath–Brown bound
  (`hhb`, i.e. GM (6.3) with `k = 4`) bound the pair sum at that level.
-/

open Complex Finset MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.GM.S2

/-! ## The truncation length `M N = N^{6/5}` and the dyadic level -/

lemma one_le_M {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Submission.LargeValues.M N := by
  rw [Submission.LargeValues.M]
  exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)

lemma M_pos {N : ℕ} (hN : 1 ≤ N) : 0 < Submission.LargeValues.M N :=
  lt_of_lt_of_le zero_lt_one (one_le_M hN)

/-- `2^{lev t} ≤ |t|` for `|t| ≥ 1` (where `lev t = ⌊log₂ |t|⌋`). -/
lemma pow_lev_le_abs {t : ℝ} (ht : 1 ≤ |t|) : (2 : ℝ) ^ (lev t) ≤ |t| := by
  have hfl : 0 < ⌊|t|⌋₊ := Nat.floor_pos.mpr ht
  have hne : ⌊|t|⌋₊ ≠ 0 := by omega
  calc (2 : ℝ) ^ (lev t) = ((2 ^ Nat.log 2 ⌊|t|⌋₊ : ℕ) : ℝ) := by
        simp only [lev, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((⌊|t|⌋₊ : ℕ) : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hne
    _ ≤ |t| := Nat.floor_le (abs_nonneg t)

/-- `|t| < 2^{lev t + 1}`. -/
lemma abs_lt_pow_lev_succ (t : ℝ) : |t| < (2 : ℝ) ^ (lev t + 1) := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊|t|⌋₊
  have h2 : ((⌊|t|⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊|t|⌋₊).succ : ℕ) : ℝ) := by
    exact_mod_cast h
  have h3 : |t| < ((⌊|t|⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one |t|
  calc |t| < ((⌊|t|⌋₊ : ℕ) : ℝ) + 1 := h3
    _ ≤ ((2 ^ (Nat.log 2 ⌊|t|⌋₊).succ : ℕ) : ℝ) := h2
    _ = (2 : ℝ) ^ (lev t + 1) := by
        simp only [lev, Nat.succ_eq_add_one, Nat.cast_pow, Nat.cast_ofNat]

lemma lev_mono {t : ℝ} {D : ℕ} (h : ⌊|t|⌋₊ ≤ D) : lev t ≤ Nat.log 2 D :=
  Nat.log_mono_right h

/-- For a pair of points of `W ⊆ [0,T]`, the difference has absolute value `≤ 2T`. -/
lemma abs_sub_le_two {W : Finset ℝ} {T : ℝ} (hW : ∀ t ∈ W, t ∈ Set.Icc 0 T)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ W) (h₂ : t₂ ∈ W) : |t₁ - t₂| ≤ 2 * T := by
  have h1 := hW t₁ h₁; have h2 := hW t₂ h₂
  rw [abs_sub_le_iff]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## Reindexing the double sum over `W × W` by `Fin W.card` -/

/-- The enumeration of `W` by `Fin W.card`. -/
noncomputable def enum (W : Finset ℝ) (i : Fin W.card) : ℝ := (W.equivFin.symm i : ℝ)

lemma enum_mem (W : Finset ℝ) (i : Fin W.card) : enum W i ∈ W := (W.equivFin.symm i).2

lemma enum_injective (W : Finset ℝ) : Function.Injective (enum W) := by
  intro i j hij
  have h : W.equivFin.symm i = W.equivFin.symm j := Subtype.ext hij
  have h2 := congrArg W.equivFin h
  simpa using h2

lemma sum_finset_enum (W : Finset ℝ) (G : ℝ → ℝ) :
    (∑ x ∈ W, G x) = ∑ i : Fin W.card, G (enum W i) := by
  rw [← Finset.sum_coe_sort W G]
  exact (Equiv.sum_comp (W.equivFin.symm) (fun x : ↥W => G (x : ℝ))).symm

/-- The double sum over `W × W` of a function of the difference is the double sum over
`Fin W.card`, using the canonical enumeration of `W`. -/
lemma sum_fin_pair (W : Finset ℝ) (f : ℝ → ℝ) :
    (∑ p ∈ W ×ˢ W, f (p.1 - p.2))
      = ∑ i : Fin W.card, ∑ j : Fin W.card, f (enum W i - enum W j) := by
  rw [Finset.sum_product]
  have h1 : ∀ x : ℝ, (∑ y ∈ W, f (x - y)) = ∑ j : Fin W.card, f (x - enum W j) :=
    fun x => sum_finset_enum W (fun y => f (x - y))
  calc (∑ x ∈ W, ∑ y ∈ W, f (x - y))
      = ∑ x ∈ W, ∑ j : Fin W.card, f (x - enum W j) := Finset.sum_congr rfl (fun x _ => h1 x)
    _ = ∑ i : Fin W.card, ∑ j : Fin W.card, f (enum W i - enum W j) :=
        sum_finset_enum W (fun x => ∑ j : Fin W.card, f (x - enum W j))

/-- Separation for the enumerated points. -/
lemma sep_enum {W : Finset ℝ} {s : ℝ} (hs : Submission.GM.Separated W s) :
    ∀ i j : Fin W.card, i ≠ j → s ≤ |enum W i - enum W j| := by
  intro i j hij
  have hne : enum W i ≠ enum W j := fun h => hij (enum_injective W h)
  exact hs _ (enum_mem W i) _ (enum_mem W j) hne

/-! ## Reindexing the flipped pair sum -/

lemma sum_fin_pair_flip (W : Finset ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin W.card, ∑ j : Fin W.card, f (enum W j - enum W i))
      = ∑ p ∈ W ×ˢ W, f (p.2 - p.1) := by
  have h := sum_fin_pair W (fun x => f (-x))
  have h2 : (∑ i : Fin W.card, ∑ j : Fin W.card, f (enum W j - enum W i))
      = ∑ i : Fin W.card, ∑ j : Fin W.card, f (-(enum W i - enum W j)) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [neg_sub]
  rw [h2, ← h]
  exact Finset.sum_congr rfl (fun p _ => by rw [neg_sub])

/-! ## The tail of the reflection at one dyadic level -/

lemma level_tail_bound (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (j : ℕ) (hj : 2 ≤ j)
    (hηj : 25 ≤ η * j) (hη1 : η ≤ 1) (kk : ℕ)
    (hkkT : (2 : ℝ) ^ (kk + 1) ≤ 4 * Submission.LargeValues.M N)
    (hcrit : ((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η > (N : ℝ))
    {a : ℝ} (ha : 0 ≤ a) (haA : a ≤ (1 : ℝ) + (2 : ℝ) ^ (kk + 1)) :
    (a ^ j / ((N : ℝ) ^ j * (Ylev N η kk) ^ (j - 1))) ^ 2
      ≤ (8 * (Submission.LargeValues.M N) ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 := by
  have hT1 : 1 ≤ Submission.LargeValues.M N := one_le_M hN
  have hT0 : 0 < Submission.LargeValues.M N := lt_of_lt_of_le zero_lt_one hT1
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hA0 : 0 < (1:ℝ) + (2:ℝ)^(kk+1) := by positivity
  have hcritdiv : 1 < ((1:ℝ) + (2:ℝ)^(kk+1)) * (Submission.LargeValues.M N)^η / (N:ℝ) := by
    rw [lt_div_iff₀ hN0]
    calc (1:ℝ) * (N:ℝ) = (N:ℝ) := by ring
      _ < ((1:ℝ) + (2:ℝ)^(kk+1)) * (Submission.LargeValues.M N)^η := hcrit
  have hYj : Ylev N η kk
      = ((1:ℝ) + (2:ℝ)^(kk+1)) * (Submission.LargeValues.M N)^η / (N:ℝ) := by
    rw [Ylev]
    exact max_eq_right (le_of_lt hcritdiv)
  have hηj24 : 24 ≤ η * ((j:ℝ) - 1) := by
    have h25 : 25 ≤ η * (j:ℝ) := by
      have hjc : (j:ℝ) = (j:ℕ) := by simp
      rw [hjc]; exact hηj
    have hsplit : η * ((j:ℝ)-1) = η * (j:ℝ) - η := by ring
    rw [hsplit]; linarith
  have hbase : a^j / ((N:ℝ)^j * (Ylev N η kk)^(j-1))
      ≤ ((1:ℝ) + (2:ℝ)^(kk+1)) / ((N:ℝ) * (Submission.LargeValues.M N)^(η*((j:ℝ)-1))) :=
    trunc_tail_bound (a := a) (A := (1:ℝ)+(2:ℝ)^(kk+1)) (N := (N:ℝ))
      (T := Submission.LargeValues.M N) (η := η) (Y := Ylev N η kk) (j := j)
      hj ha haA hA0 hN0 hT1 hYj
  have h2 : ((1:ℝ) + (2:ℝ)^(kk+1)) / ((N:ℝ) * (Submission.LargeValues.M N)^(η*((j:ℝ)-1)))
      ≤ 8 * (Submission.LargeValues.M N)^(-(23:ℝ)) / (N:ℝ) :=
    tail_arith2 (A := (1:ℝ)+(2:ℝ)^(kk+1)) (T := Submission.LargeValues.M N) (η := η)
      (N := (N:ℝ)) (kk := kk) (j := j) rfl hkkT hT1 hN0 hηj24 hη
  have hYpos : 0 ≤ Ylev N η kk := by rw [hYj]; positivity
  exact pow_le_pow_left₀ (div_nonneg (pow_nonneg ha j)
    (mul_nonneg (pow_nonneg (Nat.cast_nonneg N) j) (pow_nonneg hYpos (j-1))))
    (le_trans hbase h2) 2

/-! ## The estimate at one dyadic level (reflection regime) -/

/-- At a dyadic level `kk` with `Ylev N η kk > 1`, both halves of `Σ_{m≠0} ĥ_t(mN)` are
estimated by the reflection hypothesis (`pos_half_reflection`), Cauchy–Schwarz in `ξ`
produces `∫ gwt ξ · PolySum²`, and the Heath–Brown input `hhbB` bounds the resulting pair
sum of the short Dirichlet polynomials. -/
lemma level_bound_refl
    (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ)
    (hW : ∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N))
    (hsep : Submission.GM.Separated W 1)
    (η : ℝ) (hη : 0 < η) (j : ℕ) (hj : 2 ≤ j) (hηj : 25 ≤ η * j) (hη1 : η ≤ 1)
    (Cp m1 : ℝ) (hm1 : 0 ≤ m1) (hCp : 0 < Cp)
    (hgwt : Integrable gwt) (hmass : (∫ ξ, gwt ξ) ≤ m1)
    (hposrefB : ∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
      ‖Spos N t‖ ^ 2 ≤ Cp * ((1 + |t|)⁻¹ * (m1 * ∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2)
        + ((1 + |t|) ^ j / ((N : ℝ) ^ j * Y ^ (j - 1))) ^ 2))
    (hSall : ∀ (N : ℕ), 1 ≤ N → ∀ t : ℝ, ‖Sall N t‖ ≤ ‖Spos N t‖ + ‖Spos N (-t)‖)
    (Chb : ℝ) (hChb : 0 < Chb) (Nhb : ℕ) (δ : ℝ)
    (hhbB : ∀ (N' : ℕ), Nhb ≤ N' → ∀ (Ty Y : ℝ), 1 ≤ Ty → Ty ≤ (N' : ℝ) ^ 2 → 1 ≤ Y →
      Y ≤ (N' : ℝ) →
      ∀ (ξ : ℝ) (R : ℕ) (t : Fin R → ℝ),
        (∀ i, t i ∈ Set.Icc 0 Ty) → (∀ i jj, i ≠ jj → 1 ≤ |t i - t jj|) →
        (∑ i : Fin R, ∑ jj : Fin R, ‖PolySum Y (t i - t jj + 2 * Real.pi * ξ)‖ ^ 2)
          ≤ Chb * (N' : ℝ) ^ (δ / 8) * ((R : ℝ) ^ 2 * Y + (R : ℝ) ^ ((7 : ℝ) / 4) * Y ^ 2
              + (R : ℝ) ^ ((29 : ℝ) / 16) * Ty ^ (1 / 8 : ℝ) * Y))
    (kk : ℕ) (hkk1 : 1 ≤ kk) (hkkT : (2 : ℝ) ^ (kk + 1) ≤ 4 * Submission.LargeValues.M N)
    (hcrit : ((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η > (N : ℝ)) :
    (∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = kk), ‖Sall N (p.1 - p.2)‖ ^ 2)
      ≤ 8 * Cp * m1 ^ 2 * ((1 / 2 : ℝ) ^ kk) *
          (Chb * ((levN N η Nhb kk : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Ylev N η kk + (W.card : ℝ) ^ ((7 : ℝ) / 4) * (Ylev N η kk) ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * (Submission.LargeValues.M N) ^ (1 / 8 : ℝ)
                * Ylev N η kk))
        + 512 * Cp * (W.card : ℝ) ^ 2
            * ((Submission.LargeValues.M N) ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 := by
  set T : ℝ := Submission.LargeValues.M N with hT
  have hT1 : 1 ≤ T := by rw [hT]; exact one_le_M hN
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set A : ℝ := (1 : ℝ) + (2 : ℝ) ^ (kk + 1) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set Yj : ℝ := Ylev N η kk with hYjdef
  have hcritdiv : 1 < A * T ^ η / (N : ℝ) := by
    rw [lt_div_iff₀ hN0, hA, hT]
    calc (1 : ℝ) * (N : ℝ) = (N : ℝ) := by ring
      _ < ((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * (Submission.LargeValues.M N) ^ η := hcrit
  have hYj : Yj = A * T ^ η / (N : ℝ) := by
    rw [hYjdef, Ylev, hA, hT]
    exact max_eq_right (le_of_lt hcritdiv)
  have hYj1 : 1 ≤ Yj := by rw [hYj]; exact le_of_lt hcritdiv
  set Nl : ℕ := levN N η Nhb kk with hNldef
  have hNlNhb : Nhb ≤ Nl := le_levN_Nhb N η Nhb kk
  have hNlY : Yj ≤ (Nl : ℝ) := by rw [hNldef]; exact Ylev_le_levN N η Nhb kk
  have hNlT : T ≤ (Nl : ℝ) ^ 2 := by rw [hNldef, hT]; exact M_le_levN_sq N η Nhb kk
  set F : Finset (ℝ × ℝ) := (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = kk) with hF
  have hFW : ∀ p ∈ F, p.1 ∈ W ∧ p.2 ∈ W := by
    intro p hp
    exact Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  have hlt : ∀ p ∈ F, lev (p.1 - p.2) = kk := fun p hp => (Finset.mem_filter.mp hp).2
  have habs1 : ∀ p ∈ F, 1 ≤ |p.1 - p.2| := by
    intro p hp
    have hlevp := hlt p hp
    have hfl2 : 2 ≤ ⌊|p.1 - p.2|⌋₊ := by
      by_contra hcon
      have hle : ⌊|p.1 - p.2|⌋₊ ≤ 1 := by omega
      have hmono := lev_mono (t := p.1 - p.2) (D := 1) hle
      rw [hlevp] at hmono
      simp [Nat.log_one_right] at hmono
      omega
    exact le_trans (by norm_num : (1:ℝ) ≤ 2)
      (le_trans (by exact_mod_cast hfl2) (Nat.floor_le (abs_nonneg _)))
  have hltpow : ∀ p ∈ F, |p.1 - p.2| < (2 : ℝ) ^ (kk + 1) := by
    intro p hp
    have h := abs_lt_pow_lev_succ (p.1 - p.2)
    rwa [hlt p hp] at h
  have habs2 : ∀ p ∈ F, (2 : ℝ) ^ kk ≤ |p.1 - p.2| := by
    intro p hp
    have h := pow_lev_le_abs (habs1 p hp)
    rwa [hlt p hp] at h
  -- the tail bound, uniform over the level
  have htail : ∀ p ∈ F, ((1 + |p.1 - p.2|) ^ j / ((N : ℝ) ^ j * Yj ^ (j - 1))) ^ 2
      ≤ (8 * T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 := by
    intro p hp
    have h1 := level_tail_bound N hN η hη j hj hηj hη1 kk hkkT hcrit
      (a := 1 + |p.1 - p.2|) (by positivity) (by have := hltpow p hp; linarith)
    rw [hYjdef, hT]
    exact h1
  -- the Heath–Brown input at this level
  have hB := fun (ξ : ℝ) (t : Fin W.card → ℝ)
      (ht : ∀ i, t i ∈ Set.Icc 0 T) (hsp : ∀ i jj, i ≠ jj → 1 ≤ |t i - t jj|) =>
    hhbB Nl hNlNhb T Yj hT1 hNlT hYj1 hNlY ξ (W.card) t ht hsp
  -- the two reflected pair sums
  have hI1 : (∑ p ∈ F, ∫ ξ, gwt ξ * ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2)
      ≤ m1 * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
          ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
            + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) := by
    rw [show (∑ p ∈ F, ∫ ξ, gwt ξ * ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2)
        = ∑ p ∈ F, ∫ ξ, gwt ξ * ‖PolySum Yj (1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2 from by
          simp only [one_mul]]
    rw [sum_integral_gwt_poly F Yj 1 hgwt]
    have hptwise : ∀ ξ : ℝ, gwt ξ * ∑ p ∈ F, ‖PolySum Yj (1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2
        ≤ gwt ξ * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
          ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
            + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) := by
      intro ξ
      refine mul_le_mul_of_nonneg_left ?_ (gwt_nonneg ξ)
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun p hp _ => by positivity)) ?_
      rw [show (∑ p ∈ W ×ˢ W, ‖PolySum Yj (1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2)
          = ∑ p ∈ W ×ˢ W, ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2 from
        Finset.sum_congr rfl (fun p _ => by rw [one_mul])]
      rw [sum_fin_pair W (fun x => ‖PolySum Yj (x + 2 * Real.pi * ξ)‖ ^ 2)]
      exact hB ξ (enum W) (fun i => hW _ (enum_mem W i))
        (fun i jj hij => hsep _ (enum_mem W i) _ (enum_mem W jj) (fun h => hij (enum_injective W h)))
    calc ∫ ξ, gwt ξ * ∑ p ∈ F, ‖PolySum Yj (1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2
        ≤ ∫ ξ, gwt ξ * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall
            (fun ξ => mul_nonneg (gwt_nonneg ξ) (Finset.sum_nonneg (fun p hp => by positivity))))
            (hgwt.mul_const _) (Filter.Eventually.of_forall hptwise)
      _ = (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) * ∫ ξ, gwt ξ := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun ξ => by ring))
      _ ≤ (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) * m1 :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = m1 * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) := by ring
  have hI2 : (∑ p ∈ F, ∫ ξ, gwt ξ * ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2)
      ≤ m1 * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
          ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
            + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) := by
    rw [show (∑ p ∈ F, ∫ ξ, gwt ξ * ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2)
        = ∑ p ∈ F, ∫ ξ, gwt ξ * ‖PolySum Yj (-1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2 from by
          refine Finset.sum_congr rfl (fun p _ => ?_)
          congr 3
          ring]
    rw [sum_integral_gwt_poly F Yj (-1) hgwt]
    have hptwise : ∀ ξ : ℝ, gwt ξ * ∑ p ∈ F, ‖PolySum Yj (-1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2
        ≤ gwt ξ * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
          ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
            + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) := by
      intro ξ
      refine mul_le_mul_of_nonneg_left ?_ (gwt_nonneg ξ)
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun p hp _ => by positivity)) ?_
      rw [show (∑ p ∈ W ×ˢ W, ‖PolySum Yj (-1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2)
          = ∑ p ∈ W ×ˢ W, ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2 from
        Finset.sum_congr rfl (fun p _ => by congr 2; ring)]
      rw [← sum_fin_pair_flip W (fun x => ‖PolySum Yj (x + 2 * Real.pi * ξ)‖ ^ 2)]
      have hswap : (∑ i : Fin W.card, ∑ jj : Fin W.card,
            ‖PolySum Yj (enum W jj - enum W i + 2 * Real.pi * ξ)‖ ^ 2)
          = ∑ i : Fin W.card, ∑ jj : Fin W.card,
            ‖PolySum Yj ((T - enum W i) - (T - enum W jj) + 2 * Real.pi * ξ)‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun jj _ => ?_))
        rw [show (T - enum W i) - (T - enum W jj) + 2 * Real.pi * ξ
            = enum W jj - enum W i + 2 * Real.pi * ξ from by ring]
      rw [hswap]
      refine hB ξ (fun i => T - enum W i) (fun i => ?_) (fun i jj hij => ?_)
      · have h := hW _ (enum_mem W i)
        rw [hT] at h
        exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
      have h := hsep _ (enum_mem W i) _ (enum_mem W jj)
        (fun h => hij (enum_injective W h))
      have hsub : (T - enum W i) - (T - enum W jj) = enum W jj - enum W i := by ring
      rw [hsub]; rwa [abs_sub_comm] at h
    calc ∫ ξ, gwt ξ * ∑ p ∈ F, ‖PolySum Yj (-1 * (p.1 - p.2) + 2 * Real.pi * ξ)‖ ^ 2
        ≤ ∫ ξ, gwt ξ * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall
            (fun ξ => mul_nonneg (gwt_nonneg ξ) (Finset.sum_nonneg (fun p hp => by positivity))))
            (hgwt.mul_const _) (Filter.Eventually.of_forall hptwise)
      _ = (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) * ∫ ξ, gwt ξ := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun ξ => by ring))
      _ ≤ (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) * m1 :=
          mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = m1 * (Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
            ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
              + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj)) := by ring
  -- per-pair bound
  have hI1p : ∀ p ∈ F, (0:ℝ) ≤ ∫ ξ, gwt ξ * ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2 :=
    fun p hp => integral_nonneg (fun ξ => mul_nonneg (gwt_nonneg ξ) (by positivity))
  have hI2p : ∀ p ∈ F, (0:ℝ) ≤ ∫ ξ, gwt ξ * ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2 :=
    fun p hp => integral_nonneg (fun ξ => mul_nonneg (gwt_nonneg ξ) (by positivity))
  -- abbreviations
  set X : ℝ := Chb * ((Nl : ℕ) : ℝ) ^ (δ / 8) *
      ((W.card : ℝ) ^ 2 * Yj + (W.card : ℝ) ^ ((7 : ℝ) / 4) * Yj ^ 2
        + (W.card : ℝ) ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Yj) with hXdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  set A1 : ℝ × ℝ → ℝ := fun p => (1 + |p.1 - p.2|)⁻¹ *
      (m1 * ∫ ξ, gwt ξ * ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2) with hA1def
  set A2 : ℝ × ℝ → ℝ := fun p => (1 + |p.1 - p.2|)⁻¹ *
      (m1 * ∫ ξ, gwt ξ * ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2) with hA2def
  set tb : ℝ := (8 * T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 with htbdef
  have htb0 : 0 ≤ tb := by rw [htbdef]; positivity
  have hAn1 : ∀ p ∈ F, 0 ≤ A1 p := by
    intro p hp
    simp only [hA1def]
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) (mul_nonneg hm1 (hI1p p hp))
  have hAn2 : ∀ p ∈ F, 0 ≤ A2 p := by
    intro p hp
    simp only [hA2def]
    exact mul_nonneg (inv_nonneg.mpr (by positivity)) (mul_nonneg hm1 (hI2p p hp))
  have hper : ∀ p ∈ F, ‖Sall N (p.1 - p.2)‖ ^ 2 ≤ 2 * Cp * (A1 p + tb + A2 p + tb) := by
    intro p hp
    have h1 := hposrefB N hN (p.1 - p.2) Yj (habs1 p hp) hYj1
    have h2 := hposrefB N hN (p.2 - p.1) Yj (by rw [abs_sub_comm]; exact habs1 p hp) hYj1
    rw [abs_sub_comm (p.2) (p.1)] at h2
    have h3 := hSall N hN (p.1 - p.2)
    have ht := htail p hp
    have hsq : ‖Sall N (p.1 - p.2)‖ ^ 2
        ≤ 2 * (‖Spos N (p.1 - p.2)‖ ^ 2 + ‖Spos N (p.2 - p.1)‖ ^ 2) := by
      have h4 : ‖Spos N (-(p.1 - p.2))‖ = ‖Spos N (p.2 - p.1)‖ := by rw [neg_sub]
      rw [h4] at h3
      calc ‖Sall N (p.1 - p.2)‖ ^ 2 ≤ (‖Spos N (p.1 - p.2)‖ + ‖Spos N (p.2 - p.1)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h3 2
        _ ≤ 2 * (‖Spos N (p.1 - p.2)‖ ^ 2 + ‖Spos N (p.2 - p.1)‖ ^ 2) := by
            nlinarith [sq_nonneg (‖Spos N (p.1 - p.2)‖ - ‖Spos N (p.2 - p.1)‖)]
    have hn1 := hAn1 p hp
    have hn2 := hAn2 p hp
    simp only [hA1def, hA2def, htbdef]
    nlinarith [hsq, h1, h2, ht, hI1p p hp, hI2p p hp, hn1, hn2, le_of_lt hCp, hm1]
  -- summation over the level
  have hfac : ∀ p ∈ F, (1 + |p.1 - p.2|)⁻¹ ≤ (1 / 2 : ℝ) ^ kk := by
    intro p hp
    have h2 := habs2 p hp
    have hle : (2 : ℝ) ^ kk ≤ 1 + |p.1 - p.2| := by linarith
    have hpos : (0:ℝ) < 2 ^ kk := by positivity
    have h3 := (inv_le_inv₀ (by positivity : (0:ℝ) < 1 + |p.1 - p.2|) hpos).mpr hle
    simpa [inv_pow, one_div] using h3
  have hS1 : (∑ p ∈ F, A1 p) ≤ (1 / 2 : ℝ) ^ kk * (m1 * (m1 * X)) := by
    simp only [hA1def]
    calc (∑ p ∈ F, (1 + |p.1 - p.2|)⁻¹ *
          (m1 * ∫ ξ, gwt ξ * ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2))
        ≤ ∑ p ∈ F, (1 / 2 : ℝ) ^ kk *
          (m1 * ∫ ξ, gwt ξ * ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          exact mul_le_mul_of_nonneg_right (hfac p hp) (mul_nonneg hm1 (hI1p p hp))
      _ = (1 / 2 : ℝ) ^ kk * (m1 * ∑ p ∈ F,
            ∫ ξ, gwt ξ * ‖PolySum Yj (p.1 - p.2 + 2 * Real.pi * ξ)‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ kk * (m1 * (m1 * X)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ hm1
          rw [hXdef]
          exact hI1
  have hS2 : (∑ p ∈ F, A2 p) ≤ (1 / 2 : ℝ) ^ kk * (m1 * (m1 * X)) := by
    simp only [hA2def]
    calc (∑ p ∈ F, (1 + |p.1 - p.2|)⁻¹ *
          (m1 * ∫ ξ, gwt ξ * ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2))
        ≤ ∑ p ∈ F, (1 / 2 : ℝ) ^ kk *
          (m1 * ∫ ξ, gwt ξ * ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          exact mul_le_mul_of_nonneg_right (hfac p hp) (mul_nonneg hm1 (hI2p p hp))
      _ = (1 / 2 : ℝ) ^ kk * (m1 * ∑ p ∈ F,
            ∫ ξ, gwt ξ * ‖PolySum Yj (p.2 - p.1 + 2 * Real.pi * ξ)‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ kk * (m1 * (m1 * X)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine mul_le_mul_of_nonneg_left ?_ hm1
          rw [hXdef]
          exact hI2
  have hcardsq : (F.card : ℝ) ≤ (W.card : ℝ) ^ 2 := by
    calc (F.card : ℝ) ≤ ((W ×ˢ W).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (W.card : ℝ) ^ 2 := by rw [Finset.card_product]; push_cast; ring
  have hstep : (∑ p ∈ F, ‖Sall N (p.1 - p.2)‖ ^ 2)
      ≤ ∑ p ∈ F, 2 * Cp * (A1 p + tb + A2 p + tb) := Finset.sum_le_sum hper
  have hexp : (∑ p ∈ F, 2 * Cp * (A1 p + tb + A2 p + tb))
      = 2 * Cp * ((∑ p ∈ F, A1 p) + (F.card : ℝ) * tb
          + ((∑ p ∈ F, A2 p) + (F.card : ℝ) * tb)) := by
    have hsA : (∑ p ∈ F, 2 * Cp * (A1 p + tb + A2 p + tb))
        = 2 * Cp * (∑ p ∈ F, (A1 p + tb + A2 p + tb)) := by rw [Finset.mul_sum]
    have hsB : (∑ p ∈ F, (A1 p + tb + A2 p + tb))
        = (∑ p ∈ F, A1 p) + (F.card : ℝ) * tb
          + ((∑ p ∈ F, A2 p) + (F.card : ℝ) * tb) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsA, hsB]
  have hfinal : (∑ p ∈ F, ‖Sall N (p.1 - p.2)‖ ^ 2)
      ≤ 4 * Cp * (1 / 2 : ℝ) ^ kk * (m1 ^ 2 * X) + 4 * Cp * ((W.card : ℝ) ^ 2 * tb) := by
    rw [hexp] at hstep
    have h_le3 : (F.card : ℝ) * tb ≤ (W.card : ℝ) ^ 2 * tb :=
      mul_le_mul_of_nonneg_right hcardsq htb0
    calc (∑ p ∈ F, ‖Sall N (p.1 - p.2)‖ ^ 2)
        ≤ 2 * Cp * ((∑ p ∈ F, A1 p) + (F.card : ℝ) * tb
            + ((∑ p ∈ F, A2 p) + (F.card : ℝ) * tb)) := hstep
      _ ≤ 2 * Cp * ((1 / 2 : ℝ) ^ kk * (m1 * (m1 * X)) + (W.card : ℝ) ^ 2 * tb
            + ((1 / 2 : ℝ) ^ kk * (m1 * (m1 * X)) + (W.card : ℝ) ^ 2 * tb)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact add_le_add (add_le_add hS1 h_le3) (add_le_add hS2 h_le3)
      _ = 4 * Cp * (1 / 2 : ℝ) ^ kk * (m1 ^ 2 * X) + 4 * Cp * ((W.card : ℝ) ^ 2 * tb) := by
          ring
  -- final comparison, in the abbreviations `X` (the Heath–Brown bound), `tb` (the tail)
  have hCnn : 0 ≤ Cp := le_of_lt hCp
  have hm1sq : 0 ≤ m1 ^ 2 := sq_nonneg m1
  have hhalf : 0 ≤ (1 / 2 : ℝ) ^ kk := by positivity
  have hR2 : 0 ≤ (W.card : ℝ) ^ 2 := sq_nonneg (W.card : ℝ)
  refine le_trans hfinal ?_
  have hmm0 : 0 ≤ (T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 := by positivity
  have h1 : 4 * Cp * (1 / 2 : ℝ) ^ kk * (m1 ^ 2 * X) ≤ 8 * Cp * m1 ^ 2 * (1 / 2 : ℝ) ^ kk * X := by
    have hp : 0 ≤ Cp * ((1 / 2 : ℝ) ^ kk * (m1 ^ 2 * X)) :=
      mul_nonneg hCnn (mul_nonneg hhalf (mul_nonneg hm1sq hX0))
    nlinarith [hp]
  have h2 : 4 * Cp * ((W.card : ℝ) ^ 2 * tb)
      ≤ 512 * Cp * (W.card : ℝ) ^ 2 * (T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 := by
    rw [htbdef]
    have h8 : (8 * T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 = 64 * (T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 := by ring
    rw [h8]
    have hp : 0 ≤ Cp * ((W.card : ℝ) ^ 2 * ((T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2)) :=
      mul_nonneg hCnn (mul_nonneg hR2 hmm0)
    nlinarith [hp]
  linarith [h1, h2]

/-! ## The constant of the pair-sum bound -/

noncomputable def bigC (δ : ℝ) (Cp m1 Chb Cs : ℝ) (Nhb : ℕ) : ℝ :=
  1 + (Cs ^ 2 + 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * 256 + 512 * Cp)

/-! ## Summing the levels -/

/-- The pair sum is bounded by summing the estimates of the individual dyadic levels. -/
theorem pair_sum_bound_core
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (η : ℝ) (hη : 0 < η) (j : ℕ) (hj : 2 ≤ j) (hηj : 25 ≤ η * j) (hη1 : η ≤ 1)
    (hη2 : 6 * η ≤ 1 / 10) (hη24 : 24 * η ≤ δ)
    (m1 : ℝ) (hm1 : 0 ≤ m1) (hgwt : Integrable gwt) (hmass : (∫ ξ, gwt ξ) ≤ m1)
    (Cp : ℝ) (hCp : 0 < Cp) (Cs : ℝ) (hCs : 0 < Cs)
    (Nhb : ℕ) (Chb : ℝ) (hChb : 0 < Chb)
    (hposrefB : ∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
      ‖Spos N t‖ ^ 2 ≤ Cp * ((1 + |t|)⁻¹ * (m1 * ∫ ξ, gwt ξ * ‖PolySum Y (t + 2 * Real.pi * ξ)‖ ^ 2)
        + ((1 + |t|) ^ j / ((N : ℝ) ^ j * Y ^ (j - 1))) ^ 2))
    (hSall : ∀ (N : ℕ), 1 ≤ N → ∀ t : ℝ, ‖Sall N t‖ ≤ ‖Spos N t‖ + ‖Spos N (-t)‖)
    (hsmallB : ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ),
      (1 + |t|) * (Submission.LargeValues.M N) ^ η ≤ (N : ℝ) →
      ‖Sall N t‖ ≤ Cs * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))))
    (hhbB : ∀ (N' : ℕ), Nhb ≤ N' → ∀ (Ty Y : ℝ), 1 ≤ Ty → Ty ≤ (N' : ℝ) ^ 2 → 1 ≤ Y →
      Y ≤ (N' : ℝ) →
      ∀ (ξ : ℝ) (R : ℕ) (t : Fin R → ℝ),
        (∀ i, t i ∈ Set.Icc 0 Ty) → (∀ i jj, i ≠ jj → 1 ≤ |t i - t jj|) →
        (∑ i : Fin R, ∑ jj : Fin R, ‖PolySum Y (t i - t jj + 2 * Real.pi * ξ)‖ ^ 2)
          ≤ Chb * (N' : ℝ) ^ (δ / 8) * ((R : ℝ) ^ 2 * Y + (R : ℝ) ^ ((7 : ℝ) / 4) * Y ^ 2
              + (R : ℝ) ^ ((29 : ℝ) / 16) * Ty ^ (1 / 8 : ℝ) * Y))
    (hcount : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (Nat.log 2 ⌊2 * Submission.LargeValues.M N⌋₊ + 1 : ℝ) ≤ (N : ℝ) ^ (δ / 4))
    (hlarge : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (3 * (Submission.LargeValues.M N) ^ η ≤ (N : ℝ)) ∧
      ((Submission.LargeValues.M N) ^ η ≤ (N : ℝ) ^ (δ / 4)) ∧
      ((Submission.LargeValues.M N) ^ (2 * η) ≤ (N : ℝ) ^ (δ / 4))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      (∑ t₁ ∈ W, ∑ t₂ ∈ W,
        ‖∑' (m : {m : ℤ // m ≠ 0}), Submission.GM.hhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))‖ ^ 2)
        ≤ C * (N : ℝ) ^ δ * ((W.card : ℝ) ^ 2 / (N : ℝ)
            + Submission.LargeValues.M N / (N : ℝ) ^ 2 * (W.card : ℝ) ^ ((7 : ℝ) / 4)
            + (W.card : ℝ) ^ ((29 : ℝ) / 16) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8)
              / (N : ℝ)) := by
  obtain ⟨Ncount, hcountB⟩ := hcount
  obtain ⟨Nlarge, hlargeB⟩ := hlarge
  refine ⟨bigC δ Cp m1 Chb Cs Nhb, by unfold bigC; positivity,
    max (max (Ncount + 1) (Nlarge + 1)) (Nhb + 1), ?_⟩
  intro N hN W hW hsep
  have hNcount : Ncount ≤ N :=
    le_trans (le_trans (le_trans (Nat.le_succ Ncount) (le_max_left _ _)) (le_max_left _ _)) hN
  have hNlarge : Nlarge ≤ N :=
    le_trans (le_trans (le_trans (Nat.le_succ Nlarge) (le_max_right _ _)) (le_max_left _ _)) hN
  have hNhb : Nhb ≤ N :=
    le_trans (le_trans (Nat.le_succ Nhb) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (by omega : 1 ≤ max (max (Ncount + 1) (Nlarge + 1)) (Nhb + 1)) hN
  obtain ⟨hL1, hL2, hL3⟩ := hlargeB N hNlarge
  have hcountN := hcountB N hNcount
  set T : ℝ := Submission.LargeValues.M N with hT
  have hT1 : 1 ≤ T := by rw [hT]; exact one_le_M hN1
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set R : ℝ := (W.card : ℝ) with hR
  -- separation at scale one
  have hsep1 : Submission.GM.Separated W 1 := by
    intro x hx y hy hxy
    have h1 := hsep x hx y hy hxy
    have h2 : (1 : ℝ) ≤ T ^ ε := Real.one_le_rpow hT1 (le_of_lt hε)
    linarith
  -- the degenerate case of an empty `W`
  by_cases hW0 : W.card = 0
  · have hWe : W = ∅ := Finset.card_eq_zero.mp hW0
    have hCpos : 0 < bigC δ Cp m1 Chb Cs Nhb := by
      unfold bigC
      have h : 0 ≤ Cs ^ 2 + 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * 256 + 512 * Cp := by
        positivity
      linarith
    have hR0 : R = 0 := by rw [hR, hWe]; simp
    have hz1 : (0 : ℝ) ^ ((7 : ℝ) / 4) = 0 := Real.zero_rpow (by norm_num)
    have hz2 : (0 : ℝ) ^ ((29 : ℝ) / 16) = 0 := Real.zero_rpow (by norm_num)
    rw [hWe]
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero]
    rw [hR0, hz1, hz2]
    simp
  -- the number of dyadic levels
  set K : ℕ := Nat.log 2 ⌊2 * T⌋₊ + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; omega
  have hKpos : 0 < K := hK1
  have h2K : (2 : ℝ) ^ K ≤ 4 * T := by
    have hne : ⌊2 * T⌋₊ ≠ 0 := by
      apply Nat.pos_iff_ne_zero.mp
      exact Nat.floor_pos.mpr (by linarith)
    have h1 : 2 ^ Nat.log 2 ⌊2 * T⌋₊ ≤ ⌊2 * T⌋₊ := Nat.pow_log_le_self 2 hne
    have h2 : ((2 : ℕ) ^ Nat.log 2 ⌊2 * T⌋₊ : ℝ) ≤ 2 * T :=
      le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))
    calc (2 : ℝ) ^ K = 2 * ((2 : ℕ) ^ Nat.log 2 ⌊2 * T⌋₊ : ℝ) := by
          rw [hK, pow_succ]; push_cast; ring
      _ ≤ 2 * (2 * T) := by linarith
      _ = 4 * T := by ring
  -- the target bracket
  set S : ℝ := R ^ 2 / (N : ℝ) + T / (N : ℝ) ^ 2 * R ^ ((7 : ℝ) / 4)
      + R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) / (N : ℝ) with hS
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  -- the criterion for the small regime at a level (the divided form of `Ylev N η kk = 1`)
  -- level sets
  have hlev_lt : ∀ p ∈ W ×ˢ W, lev (p.1 - p.2) < K := by
    intro p hp
    have h1 : p.1 ∈ W := (Finset.mem_product.mp hp).1
    have h2 : p.2 ∈ W := (Finset.mem_product.mp hp).2
    have habs : |p.1 - p.2| ≤ 2 * T := by
      have := abs_sub_le_two hW h1 h2
      rwa [hT] at this
    have hfl : ⌊|p.1 - p.2|⌋₊ ≤ ⌊2 * T⌋₊ := Nat.floor_mono habs
    calc lev (p.1 - p.2) = Nat.log 2 ⌊|p.1 - p.2|⌋₊ := rfl
      _ ≤ Nat.log 2 ⌊2 * T⌋₊ := Nat.log_mono_right hfl
      _ < K := by rw [hK]; omega
  set G : ℝ × ℝ → Fin K :=
    fun p => if hp : p ∈ W ×ˢ W then ⟨lev (p.1 - p.2), hlev_lt p hp⟩ else ⟨0, hKpos⟩ with hGdef
  have hG : ∀ p ∈ W ×ˢ W, (G p : ℕ) = lev (p.1 - p.2) := by
    intro p hp
    simp only [hGdef]
    rw [dif_pos hp]
  have hfiber : (∑ p ∈ W ×ˢ W, ‖Sall N (p.1 - p.2)‖ ^ 2)
      = ∑ jj : Fin K,
          ∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)), ‖Sall N (p.1 - p.2)‖ ^ 2 := by
    rw [← Finset.sum_fiberwise (s := W ×ˢ W) (g := G) (f := fun p => ‖Sall N (p.1 - p.2)‖ ^ 2)]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    refine Finset.sum_congr ?_ (fun p hp => rfl)
    exact Finset.filter_congr (fun p hp => by
      constructor
      · intro h
        have := congrArg Fin.val h
        simpa [hG p hp] using this
      · intro h
        exact Fin.ext (by simpa [hG p hp] using h))
  -- the LHS is the pair sum over `W × W`
  have hLHS : (∑ t₁ ∈ W, ∑ t₂ ∈ W,
        ‖∑' (m : {m : ℤ // m ≠ 0}), Submission.GM.hhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))‖ ^ 2)
      = ∑ p ∈ W ×ˢ W, ‖Sall N (p.1 - p.2)‖ ^ 2 := by
    rw [Finset.sum_product]
    rfl
  -- the per-level estimate
  have hlevel : ∀ jj : Fin K,
      (∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)), ‖Sall N (p.1 - p.2)‖ ^ 2)
      ≤ (if ((1 : ℝ) + (2 : ℝ) ^ ((jj : ℕ) + 1)) * T ^ η ≤ (N : ℝ)
         then (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2
         else 8 * Cp * m1 ^ 2 * ((1 / 2 : ℝ) ^ (jj : ℕ)) *
              (Chb * (((levN N η Nhb (jj : ℕ) : ℕ) : ℝ) ^ (δ / 8) *
                (R ^ 2 * Ylev N η (jj : ℕ) + R ^ ((7 : ℝ) / 4) * (Ylev N η (jj : ℕ)) ^ 2
                  + R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Ylev N η (jj : ℕ))))
            + 512 * Cp * R ^ 2 * (T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2) := by
    intro jj
    by_cases hc : ((1 : ℝ) + (2 : ℝ) ^ ((jj : ℕ) + 1)) * T ^ η ≤ (N : ℝ)
    · rw [if_pos hc]
      have hcritq : ((1 : ℝ) + (2 : ℝ) ^ ((jj : ℕ) + 1)) * T ^ η ≤ (N : ℝ) := hc
      have hpers : ∀ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)),
          ‖Sall N (p.1 - p.2)‖ ^ 2 ≤ (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 := by
        intro p hp
        have hlevp : lev (p.1 - p.2) = (jj : ℕ) := (Finset.mem_filter.mp hp).2
        have h1 : (1 + |p.1 - p.2|) * T ^ η ≤ (N : ℝ) := by
          have h2 : |p.1 - p.2| < (2 : ℝ) ^ ((jj : ℕ) + 1) := by
            have := abs_lt_pow_lev_succ (p.1 - p.2)
            rwa [hlevp] at this
          calc (1 + |p.1 - p.2|) * T ^ η ≤ (1 + (2 : ℝ) ^ ((jj : ℕ) + 1)) * T ^ η := by
                apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0.le _)
                linarith
            _ ≤ (N : ℝ) := hcritq
        have h3 := hsmallB N hN1 (p.1 - p.2) (by rw [hT] at h1; exact h1)
        rw [← hT] at h3
        exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hcard : (((W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ))).card : ℝ) ≤ R ^ 2 := by
        rw [hR]
        calc (((W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ))).card : ℝ)
            ≤ ((W ×ˢ W).card : ℝ) := by
              exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
          _ = (W.card : ℝ) ^ 2 := by rw [Finset.card_product]; push_cast; ring
      calc (∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)), ‖Sall N (p.1 - p.2)‖ ^ 2)
          ≤ ∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)),
              (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 := Finset.sum_le_sum hpers
        _ = (((W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ))).card : ℝ)
              * (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ R ^ 2 * (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ = (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2 := by ring
    · rw [if_neg hc]
      have hcrit' : ((1 : ℝ) + (2 : ℝ) ^ ((jj : ℕ) + 1)) * (Submission.LargeValues.M N) ^ η > (N : ℝ) := by
        have h' : (N : ℝ) < ((1 : ℝ) + (2 : ℝ) ^ ((jj : ℕ) + 1)) * T ^ η := lt_of_not_ge hc
        rwa [hT] at h'
      have hkk1 : 1 ≤ (jj : ℕ) := by
        rcases Nat.eq_zero_or_pos (jj : ℕ) with h0 | hp
        · exfalso
          apply hc
          have h2 : (2:ℝ) ^ ((jj:ℕ) + 1) = 2 := by rw [h0]; norm_num
          rw [h2]
          norm_num
          simpa only [← hT] using hL1
        · exact hp
      have hkkT : (2 : ℝ) ^ ((jj : ℕ) + 1) ≤ 4 * Submission.LargeValues.M N := by
        have h1 : (2 : ℝ) ^ ((jj : ℕ) + 1) ≤ (2 : ℝ) ^ K := by
          apply pow_le_pow_right₀ (by norm_num)
          have := jj.isLt
          omega
        calc (2 : ℝ) ^ ((jj : ℕ) + 1) ≤ (2 : ℝ) ^ K := h1
          _ ≤ 4 * T := h2K
          _ = 4 * Submission.LargeValues.M N := by rw [hT]
      have hlbr := level_bound_refl N hN1 W hW hsep1 η hη j hj hηj hη1 Cp m1 hm1 hCp hgwt
        hmass hposrefB hSall Chb hChb Nhb δ hhbB (jj : ℕ) hkk1 hkkT hcrit'
      simp only [hR, mul_assoc] at hlbr ⊢
      exact hlbr
  -- abbreviations for the level bounds
  let raw : ℕ → ℝ := fun kk => ((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * T ^ η / (N : ℝ)
  let Rbr : Fin K → ℝ := fun jj => R ^ 2 * Ylev N η (jj : ℕ)
      + R ^ ((7 : ℝ) / 4) * (Ylev N η (jj : ℕ)) ^ 2
      + R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * Ylev N η (jj : ℕ)
  let hbf : Fin K → ℝ := fun jj => 8 * Cp * m1 ^ 2 * ((1 / 2 : ℝ) ^ (jj : ℕ)) *
      (Chb * (((levN N η Nhb (jj : ℕ) : ℕ) : ℝ) ^ (δ / 8) * Rbr jj))
  let Xf : ℕ → ℝ := fun kk => R ^ 2 * raw kk + R ^ ((7 : ℝ) / 4) * (raw kk) ^ 2
      + R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) * raw kk
  let hbfX : Fin K → ℝ := fun jj => 8 * Cp * m1 ^ 2 * ((1 / 2 : ℝ) ^ (jj : ℕ)) *
      (Chb * (((levN N η Nhb (jj : ℕ) : ℕ) : ℝ) ^ (δ / 8) * Xf (jj : ℕ)))
  let tbf : ℝ := 512 * Cp * R ^ 2 * (T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2
  let sbf : Fin K → ℝ := fun jj => (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2
  let cf : Fin K → Prop := fun jj => ((1 : ℝ) + (2 : ℝ) ^ ((jj : ℕ) + 1)) * T ^ η ≤ (N : ℝ)
  -- `R^2/N ≤ S`
  have hR2div : R ^ 2 / (N : ℝ) ≤ S := by
    rw [hS]
    have h6 : 0 ≤ T / (N : ℝ) ^ 2 * R ^ ((7 : ℝ) / 4) := by positivity
    have h7 : 0 ≤ R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) / (N : ℝ) := by positivity
    linarith
  -- the sum of the per-level bounds
  have hsum : (∑ jj : Fin K, ∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)),
        ‖Sall N (p.1 - p.2)‖ ^ 2)
      ≤ ∑ jj : Fin K, (if cf jj then sbf jj else hbf jj + tbf) := by
    refine Finset.sum_le_sum (fun jj _ => ?_)
    have h := hlevel jj
    simp only [hbf, sbf, tbf, Rbr, cf, mul_assoc] at h ⊢
    exact h
  -- the two parts of the sum
  have hsplit : (∑ jj : Fin K, (if cf jj then sbf jj else hbf jj + tbf))
      = (∑ jj : Fin K, (if cf jj then sbf jj else 0))
        + (∑ jj : Fin K, (if cf jj then 0 else hbf jj + tbf)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun jj _ => ?_)
    by_cases h : cf jj <;> simp [h]
  -- the small levels
  have hSA : (∑ jj : Fin K, (if cf jj then sbf jj else 0)) ≤ Cs ^ 2 * ((N : ℝ) ^ δ * S) := by
    have hKle : (K : ℝ) ≤ (N : ℝ) ^ (δ / 4) := by
      rw [hK]; push_cast; exact hcountN
    have h1 : (∑ jj : Fin K, (if cf jj then sbf jj else 0))
        ≤ Cs ^ 2 * (N : ℝ) ^ (δ / 4) * S := by
      rw [hS]
      have h9 := small_level_sum_arith N K R Cs j δ η
        (by rw [hR]; positivity) hN1 hδ hη hCs hKle hηj
      have heq : Cs ^ 2 * (N : ℝ) ^ (δ / 4) *
            (R ^ 2 / (N : ℝ) + Submission.LargeValues.M N * R ^ ((7 : ℝ) / 4) / (N : ℝ) ^ 2
              + (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / (N : ℝ))
          = Cs ^ 2 * (N : ℝ) ^ (δ / 4) *
            (R ^ 2 / (N : ℝ) + T / (N : ℝ) ^ 2 * R ^ ((7 : ℝ) / 4)
              + R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) / (N : ℝ)) := by
        rw [hT]; ring
      rw [heq] at h9
      refine le_trans ?_ h9
      have h2 : (∑ jj : Fin K, (if cf jj then sbf jj else 0)) ≤ ∑ jj : Fin K, sbf jj := by
        refine Finset.sum_le_sum (fun jj _ => ?_)
        by_cases h : cf jj
        · simp [h]
        · simp only [h, if_false]; simp only [sbf]; positivity
      refine le_trans h2 ?_
      have h3 : (∑ jj : Fin K, sbf jj)
          = ∑ _kk ∈ Finset.range K, (Cs * T ^ (-(η * (j : ℝ)))) ^ 2 * R ^ 2 := by
        simp only [sbf, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
          Finset.card_range]
      rw [h3]
    refine le_trans h1 ?_
    have h2 : (N : ℝ) ^ (δ / 4) ≤ (N : ℝ) ^ δ :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith [hδ])
    calc Cs ^ 2 * (N : ℝ) ^ (δ / 4) * S ≤ Cs ^ 2 * (N : ℝ) ^ δ * S := by
          apply mul_le_mul_of_nonneg_right _ hS0
          exact mul_le_mul_of_nonneg_left h2 (sq_nonneg Cs)
      _ = Cs ^ 2 * ((N : ℝ) ^ δ * S) := by ring
  -- the reflection levels
  have hYlev_eq : ∀ jj : Fin K, ¬ cf jj → Ylev N η (jj : ℕ) = raw (jj : ℕ) := by
    intro jj hj
    have hlt : (N : ℝ) < ((1 : ℝ) + (2 : ℝ) ^ ((jj : ℕ) + 1)) * T ^ η := lt_of_not_ge hj
    simp only [raw, Ylev]
    apply max_eq_right
    rw [le_div_iff₀ hNpos]
    linarith
  have hXnn : ∀ kk : ℕ, 0 ≤ Xf kk := by
    intro kk; simp only [Xf, raw]; positivity
  have hbfXnn : ∀ jj : Fin K, 0 ≤ hbfX jj := by
    intro jj; simp only [hbfX]; positivity
  have hSB : (∑ jj : Fin K, (if cf jj then 0 else hbf jj + tbf))
      ≤ 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * (256 * ((N : ℝ) ^ δ * S))
        + 512 * Cp * ((N : ℝ) ^ δ * S) := by
    have hKle : (K : ℝ) ≤ (N : ℝ) ^ (δ / 4) := by
      rw [hK]; push_cast; exact hcountN
    -- replace `Ylev` by `raw` in the reflection branch
    have h1 : (∑ jj : Fin K, (if cf jj then 0 else hbf jj + tbf))
        ≤ ∑ jj : Fin K, (hbfX jj + tbf) := by
      refine Finset.sum_le_sum (fun jj _ => ?_)
      by_cases h : cf jj
      · simp only [h, if_true]
        have hx : 0 ≤ hbfX jj + tbf := by
          have := hbfXnn jj
          have ht : 0 ≤ tbf := by simp only [tbf]; positivity
          linarith
        exact hx
      · simp only [h, if_false]
        have heq : hbf jj = hbfX jj := by
          simp only [hbf, hbfX, Rbr, Xf]
          rw [hYlev_eq jj h]
        rw [heq]
    refine le_trans h1 ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · -- the Heath--Brown terms of the level bound
      -- the arithmetic inputs
      have hKT : (K : ℝ) * (Submission.LargeValues.M N) ^ η ≤ (N : ℝ) ^ (δ / 2) := by
        have h2 : (Submission.LargeValues.M N) ^ η ≤ (N : ℝ) ^ (δ / 4) := hL2
        calc (K : ℝ) * (Submission.LargeValues.M N) ^ η
            ≤ (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (δ / 4) :=
              mul_le_mul hKle h2 (Real.rpow_nonneg (by rw [Submission.LargeValues.M]; positivity) η)
                (Real.rpow_nonneg hNpos.le _)
          _ = (N : ℝ) ^ (δ / 2) := by rw [← Real.rpow_add hNpos]; ring_nf
      have hT2η : (Submission.LargeValues.M N) ^ (2 * η) ≤ (N : ℝ) ^ (δ / 2) := by
        refine le_trans hL3 ?_
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
        linarith [hδ]
      have h2K' : (2 : ℝ) ^ K ≤ 4 * Submission.LargeValues.M N := by rw [← hT]; exact h2K
      -- bound `(levN)^{δ/8}` termwise and factor the constant out
      have hstep1 : (∑ jj : Fin K, hbfX jj)
          ≤ 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * (N : ℝ) ^ (3 * δ / 40) *
              (∑ jj : Fin K, (1 / 2 : ℝ) ^ (jj : ℕ) * Xf (jj : ℕ)) := by
        have hbound : (∑ jj : Fin K, hbfX jj)
            ≤ ∑ jj : Fin K, 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8))
                * ((N : ℝ) ^ (3 * δ / 40) * ((1 / 2 : ℝ) ^ (jj : ℕ) * Xf (jj : ℕ))) := by
          refine Finset.sum_le_sum (fun jj _ => ?_)
          have hlev : ((levN N η Nhb (jj : ℕ) : ℕ) : ℝ) ^ (δ / 8)
              ≤ ((Nhb : ℝ) + 22) ^ (δ / 8) * (N : ℝ) ^ (3 * δ / 40) :=
            levN_rpow_bound N η δ hη hη1 hη2 hδ hN1 Nhb (jj : ℕ) K jj.isLt h2K'
          have hX := hXnn (jj : ℕ)
          simp only [hbfX]
          have hinner : Chb * (((levN N η Nhb (jj : ℕ) : ℕ) : ℝ) ^ (δ / 8) * Xf (jj : ℕ))
              ≤ Chb * ((((Nhb : ℝ) + 22) ^ (δ / 8) * (N : ℝ) ^ (3 * δ / 40)) * Xf (jj : ℕ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlev hX) (le_of_lt hChb)
          calc 8 * Cp * m1 ^ 2 * ((1 / 2 : ℝ) ^ (jj : ℕ)) *
                (Chb * (((levN N η Nhb (jj : ℕ) : ℕ) : ℝ) ^ (δ / 8) * Xf (jj : ℕ)))
              ≤ 8 * Cp * m1 ^ 2 * ((1 / 2 : ℝ) ^ (jj : ℕ)) *
                  (Chb * ((((Nhb : ℝ) + 22) ^ (δ / 8) * (N : ℝ) ^ (3 * δ / 40)) * Xf (jj : ℕ))) :=
                mul_le_mul_of_nonneg_left hinner (by positivity)
            _ = 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8))
                  * ((N : ℝ) ^ (3 * δ / 40) * ((1 / 2 : ℝ) ^ (jj : ℕ) * Xf (jj : ℕ))) := by ring
        refine le_trans hbound ?_
        rw [Finset.mul_sum]
        refine le_of_eq ?_
        refine Finset.sum_congr rfl (fun jj _ => ?_)
        ring
      -- the geometric level sum
      have hstep2 : (∑ jj : Fin K, (1 / 2 : ℝ) ^ (jj : ℕ) * Xf (jj : ℕ)) ≤ 256 * (N : ℝ) ^ (δ / 2) * S := by
        rw [hS]
        have hconv : (∑ jj : Fin K, (1 / 2 : ℝ) ^ (jj : ℕ) * Xf (jj : ℕ))
            = ∑ kk ∈ Finset.range K, (1 / 2 : ℝ) ^ kk *
                (R ^ 2 * (((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * T ^ η / (N : ℝ))
                  + R ^ ((7 : ℝ) / 4) * ((((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * T ^ η / (N : ℝ)) ^ 2)
                  + R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ)
                    * (((1 : ℝ) + (2 : ℝ) ^ (kk + 1)) * T ^ η / (N : ℝ))) := by
          rw [Fin.sum_univ_eq_sum_range (fun kk => (1 / 2 : ℝ) ^ kk * Xf kk) K]
        rw [hconv]
        have hla := level_sum_arith N K R δ η (by rw [hR]; positivity) hN1 hδ hη h2K' hKT hT2η
        have hconv2 : 256 * (N : ℝ) ^ (δ / 2) *
              (R ^ 2 / (N : ℝ) + Submission.LargeValues.M N * R ^ ((7 : ℝ) / 4) / (N : ℝ) ^ 2
                + (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8) * R ^ ((29 : ℝ) / 16) / (N : ℝ))
            = 256 * (N : ℝ) ^ (δ / 2) *
              (R ^ 2 / (N : ℝ) + T / (N : ℝ) ^ 2 * R ^ ((7 : ℝ) / 4)
                + R ^ ((29 : ℝ) / 16) * T ^ (1 / 8 : ℝ) / (N : ℝ)) := by
          rw [hT]; ring
        rw [hconv2] at hla
        refine le_trans (le_of_eq ?_) hla
        refine Finset.sum_congr rfl (fun kk hk => ?_)
        rw [hT]
      -- absorb the powers of `N`
      have hpow : (N : ℝ) ^ (3 * δ / 40) * (N : ℝ) ^ (δ / 2) ≤ (N : ℝ) ^ δ := by
        rw [← Real.rpow_add hNpos]
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
        linarith [hδ]
      calc (∑ jj : Fin K, hbfX jj)
          ≤ 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * (N : ℝ) ^ (3 * δ / 40) *
              (∑ jj : Fin K, (1 / 2 : ℝ) ^ (jj : ℕ) * Xf (jj : ℕ)) := hstep1
        _ ≤ 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * (N : ℝ) ^ (3 * δ / 40)
              * (256 * (N : ℝ) ^ (δ / 2) * S) :=
            mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ = 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8))
              * ((N : ℝ) ^ (3 * δ / 40) * (N : ℝ) ^ (δ / 2)) * (256 * S) := by ring
        _ ≤ 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * (N : ℝ) ^ δ * (256 * S) := by
            have hbase : 0 ≤ 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) := by positivity
            have h256 : 0 ≤ 256 * S := by linarith [hS0]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hbase) h256
        _ = 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * (256 * ((N : ℝ) ^ δ * S)) := by
            ring
    · -- the tail terms of the level bound
      have hcard : ((Finset.univ : Finset (Fin K)).card : ℝ) ≤ (K : ℝ) := by
        rw [Finset.card_univ, Fintype.card_fin]
      have hT46 : (T ^ (-(23 : ℝ)) / (N : ℝ)) ^ 2 = T ^ (-(46 : ℝ)) / (N : ℝ) ^ 2 := by
        rw [div_pow, ← Real.rpow_natCast (T ^ (-(23 : ℝ))) 2, ← Real.rpow_mul hT0.le]
        norm_num
      have hT46le : T ^ (-(46 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hT1 (by norm_num)
      have hR2pos : (0 : ℝ) < R ^ 2 := by
        rw [hR]
        have h1 : 1 ≤ W.card := by omega
        have h2 : (1 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast h1
        nlinarith
      have hstep1 : K * (T ^ (-(46 : ℝ)) / (N : ℝ) ^ 2)
          ≤ (N : ℝ) ^ δ * (R ^ 2 / (N : ℝ)) * (R ^ 2)⁻¹ := by
        have h1 : K * (T ^ (-(46 : ℝ)) / (N : ℝ) ^ 2)
            ≤ (N : ℝ) ^ (δ / 4) * ((1 : ℝ) / (N : ℝ) ^ 2) := by
          apply mul_le_mul hKle (div_le_div_of_nonneg_right hT46le (by positivity))
            (by positivity) (by positivity)
        have h2 : (N : ℝ) ^ (δ / 4) * ((1 : ℝ) / (N : ℝ) ^ 2) ≤ (N : ℝ) ^ (δ - 1) := by
          rw [mul_one_div, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_sub hNpos]
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
          linarith [hδ]
        have h3 : (N : ℝ) ^ (δ - 1) ≤ (N : ℝ) ^ δ * (R ^ 2 / (N : ℝ)) * (R ^ 2)⁻¹ := by
          rw [Real.rpow_sub hNpos]
          have hRne : R ≠ 0 := fun h => by rw [h] at hR2pos; norm_num at hR2pos
          have hkey : (N : ℝ) ^ δ * (R ^ 2 / (N : ℝ)) * (R ^ 2)⁻¹ = (N : ℝ) ^ δ / (N : ℝ) := by
            field_simp [ne_of_gt hR2pos, ne_of_gt hNpos]
          rw [hkey]
          rw [Real.rpow_one]
        exact le_trans h1 (le_trans h2 h3)
      calc (∑ jj : Fin K, tbf) = (K : ℝ) * tbf := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        _ = (K : ℝ) * (512 * Cp * R ^ 2 * (T ^ (-(46 : ℝ)) / (N : ℝ) ^ 2)) := by
            simp only [tbf, hT46]
        _ = 512 * Cp * R ^ 2 * (K * (T ^ (-(46 : ℝ)) / (N : ℝ) ^ 2)) := by ring
        _ ≤ 512 * Cp * R ^ 2 * ((N : ℝ) ^ δ * (R ^ 2 / (N : ℝ)) * (R ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ = 512 * Cp * (N : ℝ) ^ δ * ((R ^ 2 * (R ^ 2)⁻¹) * (R ^ 2 / (N : ℝ))) := by ring
        _ = 512 * Cp * (N : ℝ) ^ δ * (R ^ 2 / (N : ℝ)) := by
            rw [mul_inv_cancel₀ (ne_of_gt hR2pos)]; ring
        _ ≤ 512 * Cp * (N : ℝ) ^ δ * S :=
            mul_le_mul_of_nonneg_left hR2div (by positivity)
        _ = 512 * Cp * ((N : ℝ) ^ δ * S) := by ring
  -- final assembly
  have hbig : Cs ^ 2 + 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * 256 + 512 * Cp
      ≤ bigC δ Cp m1 Chb Cs Nhb := by
    unfold bigC; linarith
  have hgoal : (∑ jj : Fin K, ∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)),
        ‖Sall N (p.1 - p.2)‖ ^ 2) ≤ bigC δ Cp m1 Chb Cs Nhb * ((N : ℝ) ^ δ * S) := by
    refine le_trans hsum ?_
    rw [hsplit]
    refine le_trans (add_le_add hSA hSB) ?_
    have hyA : 0 ≤ (N : ℝ) ^ δ * S := mul_nonneg (Real.rpow_nonneg hNpos.le _) hS0
    have hbracket : (Cs ^ 2 + 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * 256
        + 512 * Cp) * ((N : ℝ) ^ δ * S) ≤ bigC δ Cp m1 Chb Cs Nhb * ((N : ℝ) ^ δ * S) :=
      mul_le_mul_of_nonneg_right hbig hyA
    have hCsnn : 0 ≤ Cs ^ 2 := sq_nonneg Cs
    have hAllnn : 0 ≤ 8 * Cp * m1 ^ 2 * Chb * (((Nhb : ℝ) + 22) ^ (δ / 8)) * 256 := by positivity
    have hCpn : 0 ≤ 512 * Cp := by positivity
    nlinarith [hbracket, hyA, hCsnn, hAllnn, hCpn]
  rw [hLHS, hfiber]
  calc (∑ jj : Fin K, ∑ p ∈ (W ×ˢ W).filter (fun p => lev (p.1 - p.2) = (jj : ℕ)),
        ‖Sall N (p.1 - p.2)‖ ^ 2)
      ≤ bigC δ Cp m1 Chb Cs Nhb * ((N : ℝ) ^ δ * S) := hgoal
    _ = bigC δ Cp m1 Chb Cs Nhb * (N : ℝ) ^ δ * S := by ring


/-! ## The pair-sum bound -/

theorem pair_sum_bound
    (hhb : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (T X : ℝ), 1 ≤ T → T ≤ (N : ℝ) ^ 2 → 1 ≤ X → X ≤ (N : ℝ) →
      ∀ (R : ℕ) (t : Fin R → ℝ),
        (∀ i, t i ∈ Set.Icc 0 T) → (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
        (∀ (a : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ m : ℕ, X < (m : ℝ) → a m = 0) →
          (∑ i : Fin R, ∑ j : Fin R,
            ‖∑ m ∈ Finset.Icc (1 : ℕ) (Nat.floor X),
                a m * (m : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2)
          ≤ C * (N : ℝ) ^ δ * ((R : ℝ) ^ 2 * X + (R : ℝ) ^ ((7 : ℝ) / 4) * X ^ 2
              + (R : ℝ) ^ ((29 : ℝ) / 16) * T ^ ((1 : ℝ) / 8) * X)))
    (hrefl : ∃ Cr : ℝ, 0 < Cr ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t Y : ℝ), 1 ≤ |t| → 1 ≤ Y →
      ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y), Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
        ≤ Cr * ∫ ξ, ‖Work.GM.S2.ghat1 ξ‖ * (1 + |t + 2 * Real.pi * ξ|) ^ (-(1 / 2 : ℝ)) *
            ‖∑ m ∈ Finset.Icc 1 (Nat.floor Y),
              (m : ℂ) ^ (Complex.I * ((t + 2 * Real.pi * ξ : ℝ) : ℂ))‖)
    (hdec : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ξ : ℝ, ξ ≠ 0 →
      ‖Submission.GM.hhat t ξ‖ ≤ C * (1 + |t|) ^ j / |ξ| ^ j)
    (hdecay : ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, ‖Work.GM.S2.ghat1 ξ‖ ≤ C / (1 + |ξ|) ^ 2)
    (hfin : ∃ M : ℝ, 0 < M ∧ (∫ ξ, ‖Work.GM.S2.ghat1 ξ‖) ≤ M) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ W : Finset ℝ,
      (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
      (∑ t₁ ∈ W, ∑ t₂ ∈ W,
        ‖∑' (m : {m : ℤ // m ≠ 0}), Submission.GM.hhat (t₁ - t₂) ((m : ℝ) * (N : ℝ))‖ ^ 2)
        ≤ C * (N : ℝ) ^ δ * ((W.card : ℝ) ^ 2 / (N : ℝ)
            + Submission.LargeValues.M N / (N : ℝ) ^ 2 * (W.card : ℝ) ^ ((7 : ℝ) / 4)
            + (W.card : ℝ) ^ ((29 : ℝ) / 16) * (Submission.LargeValues.M N) ^ ((1 : ℝ) / 8)
              / (N : ℝ)) := by
  intro ε δ hε hδ
  -- parameters
  set η : ℝ := min (δ / 100) (1 / 100) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; exact lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ 1 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (by norm_num)
  have hη2 : 6 * η ≤ 1 / 10 := by
    have h : η ≤ 1 / 100 := by rw [hηdef]; exact min_le_right _ _
    linarith
  have hη24 : 24 * η ≤ δ := by
    have h : η ≤ δ / 100 := by rw [hηdef]; exact min_le_left _ _
    linarith
  set j : ℕ := Nat.ceil (30 / η) + 3 with hjdef
  have hj : 2 ≤ j := by rw [hjdef]; omega
  have hηj : 25 ≤ η * j := by
    have h1 : 30 ≤ η * j := by
      have h2 : (30 : ℝ) / η ≤ (Nat.ceil (30 / η) : ℝ) := Nat.le_ceil _
      have h3 : (30 : ℝ) / η ≤ (j : ℝ) := by
        rw [hjdef]; push_cast; linarith
      have h4 : η * ((30 : ℝ) / η) = 30 := by field_simp
      calc (30 : ℝ) = η * ((30 : ℝ) / η) := h4.symm
        _ ≤ η * (j : ℝ) := mul_le_mul_of_nonneg_left h3 (le_of_lt hηpos)
    linarith
  -- the auxiliary results
  obtain ⟨m1, hm1pos, hgwti, hmass⟩ := ghat1_weighted_mass hdecay hfin
  have hm1 : 0 ≤ m1 := le_of_lt hm1pos
  obtain ⟨Cp, hCp, hposrefB⟩ := pos_half_reflection hrefl hdec j hj m1 hm1 hgwti hmass
  obtain ⟨Cs, hCs, hsmallB⟩ := norm_Sall_small hdec j hj η hηpos
  have hSallB : ∀ (N : ℕ), 1 ≤ N → ∀ t : ℝ,
      ‖Sall N t‖ ≤ ‖Spos N t‖ + ‖Spos N (-t)‖ :=
    fun N hN t => norm_Sall_le (fun s ξ => hhat_neg_symm s ξ) hdec N hN t
  have hhb' : HBFull := hhb
  obtain ⟨Chb, hChb, Nhb, hhbB⟩ := hb_poly_pair_sum hhb' (δ / 8) (by linarith)
  have hcount : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (Nat.log 2 ⌊2 * Submission.LargeValues.M N⌋₊ + 1 : ℝ) ≤ (N : ℝ) ^ (δ / 4) :=
    level_count_bound δ hδ
  have hlarge : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (3 * (Submission.LargeValues.M N) ^ η ≤ (N : ℝ)) ∧
      ((Submission.LargeValues.M N) ^ η ≤ (N : ℝ) ^ (δ / 4)) ∧
      ((Submission.LargeValues.M N) ^ (2 * η) ≤ (N : ℝ) ^ (δ / 4)) :=
    eventually_large η δ hηpos hδ hη24 (by linarith)
  exact pair_sum_bound_core ε δ hε hδ η hηpos j hj hηj hη1 hη2 hη24 m1 hm1 hgwti hmass
    Cp hCp Cs hCs Nhb Chb hChb hposrefB hSallB hsmallB hhbB hcount hlarge

end Work.GM.S2
