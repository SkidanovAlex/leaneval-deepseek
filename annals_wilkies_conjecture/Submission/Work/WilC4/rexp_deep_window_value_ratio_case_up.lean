/-
  WilC4/rexp_deep_window_value_ratio_case_up : **Case A** of the proof of
  `Work.WilC4.rexp_deep_window_value_ratio` (the doubling ratio is *nondecreasing* on the window).

  Setting: `Y` is a definable family of fibres whose fibre at `c` is a function, `B₀` a breakpoint
  family with `ULPMStruct Y B₀` (fibre continuous and nonzero off `B₀`, doubling ratio
  monotone off `B₀`), `Bm` a breakpoint family with at most `N₁` points per fibre off which the
  fibre is three-point monotone-or-antitone (`ulpm_mono_param`), and `Γ` the scale of the uniform
  deep-ratio bound (`deep_ratio_scale_bdd`).

  Two facts drive the argument.

  * *Telescoping.*  With `G x = |valY Y c x|` and `ρ = ratioY Y c`, one has `G (2x) = ρ x · G x`, so
    `G (2^k z') / G (2^k z) = (∏_{j<k} ρ (2^j z')) / (∏_{j<k} ρ (2^j z)) · G z' / G z`.  If `ρ` is
    nondecreasing, the pair `(z, z')` can be *replaced* by the shifted pair `(2^k z, 2^k z')`.
  * *A breakpoint-free slot exists.*  The slots `(2^k z, 2^{k+1} z)`, `k = 1, …, N₁+2`, are pairwise
    disjoint and lie in the window, so at most `N₁` of them meet `Bm`.  Pick a `Bm`-free slot: the
    fibre is monotone-or-antitone there, and since `2^k z' ∈ [2^k z, 2^{k+1} z]`,
      `G (2^k z') ≤ (N/2) · G (2^k z)`,
    where the factor `N/2` is the deep-ratio bound at `2^k z` (the scale `N z' / (2^{k+1} z)` is
    `≥ Γ` by the choice of `N`).
-/
import Mathlib
import Submission.Work.WilC4.rexp_deep_window_value_ratio_aux

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr valY ratioY valY_mem InD eq_valY)

variable {k : ℕ}

/-- **Case A.**  If the doubling ratio of the fibre is nondecreasing on the window, then the value
ratio over a pair `z ≤ z' ≤ 2z` whose window `[z/N, N z']` is free of `B₀` is bounded by `N/2`,
provided `N` is large compared with `Γ` and `N₁`. -/
theorem window_ratio_case_up {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {B₀ Bm : Set (Fin (k + 1) → ℝ)}
    (hst : ULPMStruct Y B₀)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    {N₁ : ℕ} (hBmcard : ∀ c : Fin k → ℝ, {x : ℝ | Fin.cons x c ∈ Bm}.encard ≤ N₁)
    (htri : ∀ c : Fin k → ℝ, ∀ a b : ℝ, a < b →
      (∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ Bm) →
      ∀ x₁ x₂ x₃ y₁ y₂ y₃ : ℝ, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → x₃ ∈ Set.Ioo a b →
        x₁ < x₂ → x₂ < x₃ → Gr Y c x₁ y₁ → Gr Y c x₂ y₂ → Gr Y c x₃ y₃ →
        (y₁ ≤ y₂ ∧ y₂ ≤ y₃) ∨ (y₃ ≤ y₂ ∧ y₂ ≤ y₁))
    {Γ Nr : ℝ} (hΓ1 : 1 ≤ Γ)
    (hΓbd : ∀ β : ℝ, Γ ≤ β → ∀ (c : Fin k → ℝ) (x w : ℝ), 0 < x →
      IsDeepR B₀ c β x → RatW Y c x w → |w| < β)
    (hNr2Γ : 2 * Γ ≤ Nr) (hNrbig : Γ * (2 : ℝ) ^ (N₁ + 3) ≤ Nr)
    (hNrpow : (2 : ℝ) ^ (N₁ + 4) ≤ Nr)
    {c : Fin k → ℝ} {z z' : ℝ} (hz : 0 < z) (hle : z ≤ z') (h2z : z' ≤ 2 * z)
    (hfree : ∀ t : ℝ, z / Nr ≤ t → t ≤ Nr * z' → Fin.cons t c ∉ B₀)
    {y y' : ℝ} (hgz : Gr Y c z y) (hgz' : Gr Y c z' y') (hy : y ≠ 0)
    (hρmono : MonotoneOn (ratioY Y c) (Set.Ioo (z / Nr) (Nr * z' / 2))) :
    |y'| ≤ (Nr / 2) * |y| := by
  classical
  have hNr2 : (2 : ℝ) ≤ Nr := by linarith
  have hNrpos : 0 < Nr := by linarith
  have hNr1 : (1 : ℝ) < Nr := by linarith
  have hz'pos : 0 < z' := lt_of_lt_of_le hz hle
  have hzp : (0 : ℝ) < z / Nr := div_pos hz hNrpos
  -- the window is nondegenerate
  have hab : z / Nr < Nr * z' := by
    have h1 : z / Nr ≤ z / 2 := div_le_div_of_nonneg_left hz.le (by norm_num) hNr2
    have h2 : z / 2 < z := div_lt_self hz (by norm_num)
    have h3 : z < Nr * z' := by nlinarith [hz'pos, hNr2]
    linarith
  have hfreeW : ∀ x ∈ Set.Ioo (z / Nr) (Nr * z'), Fin.cons x c ∉ B₀ :=
    fun x hx => hfree x (le_of_lt hx.1) (le_of_lt hx.2)
  obtain ⟨huq, hnz, -⟩ := hst.1 c (z / Nr) (Nr * z') hab hfreeW
  have hval_ne : ∀ {s : ℝ}, s ∈ Set.Ioo (z / Nr) (Nr * z') → valY Y c s ≠ 0 :=
    fun hs => hnz _ hs _ (valY_mem Y c _ ((huq _ hs).exists.imp fun y hy => hy))
  -- z and z' lie in the window
  have hzW : z ∈ Set.Ioo (z / Nr) (Nr * z') :=
    ⟨div_lt_self hz hNr1, by nlinarith [hz'pos, hle, hNr2]⟩
  have hz'W : z' ∈ Set.Ioo (z / Nr) (Nr * z') :=
    ⟨lt_of_lt_of_le (div_lt_self hz hNr1) hle, by nlinarith [hz'pos, hNr1]⟩
  -- ### the breakpoint-free slot
  obtain ⟨i, hi_le, hifree⟩ :=
    exists_free_slot (P := {x : ℝ | Fin.cons x c ∈ Bm}) (K := N₁ + 1)
      (le_trans (hBmcard c) (by exact_mod_cast Nat.le_succ N₁))
      (fun i => (2 : ℝ) ^ (i + 1) * z) (fun i => (2 : ℝ) ^ (i + 2) * z)
      (by
        intro i j hij
        rw [Set.disjoint_left]
        intro p hp1 hp2
        have hkey : (2 : ℝ) ^ (i + 2) * z ≤ (2 : ℝ) ^ (j + 1) * z := by
          have hp : (2 : ℝ) ^ (i + 2) ≤ (2 : ℝ) ^ (j + 1) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          nlinarith [hp, hz]
        linarith [hp1.2, hp2.1, hkey])
  set k : ℕ := i + 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hk_le : k ≤ N₁ + 2 := by omega
  have hk_le3 : k + 1 ≤ N₁ + 3 := by omega
  set t : ℝ := (2 : ℝ) ^ k * z with htdef
  have ht_eq : t = (2 : ℝ) ^ (i + 1) * z := by rw [htdef, hkdef]
  have h2t_eq2 : 2 * t = (2 : ℝ) ^ (i + 2) * z := by
    rw [ht_eq]
    have hpow : (2 : ℝ) ^ (i + 2) = (2 : ℝ) ^ (i + 1) * 2 := by
      rw [show i + 2 = (i + 1) + 1 by omega, pow_succ]
    rw [hpow]; ring
  have hslot_free : ∀ p ∈ Set.Ioo t (2 * t), Fin.cons p c ∉ Bm := by
    intro p hp hBm
    refine hifree p hBm ?_
    rw [ht_eq, h2t_eq2] at hp
    exact hp
  -- ### numerical bounds
  have hi1 : i + 1 ≤ N₁ + 2 := by omega
  have hi2 : i + 2 ≤ N₁ + 3 := by omega
  have hNrq4 : (2 : ℝ) ^ (N₁ + 2) ≤ Nr / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hpow : (2 : ℝ) ^ (N₁ + 4) = 4 * (2 : ℝ) ^ (N₁ + 2) := by
      rw [show N₁ + 4 = (N₁ + 2) + 2 by omega, pow_add]; ring
    linarith [hNrpow, hpow]
  have hNrq2 : (2 : ℝ) ^ (N₁ + 3) ≤ Nr / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hpow : (2 : ℝ) ^ (N₁ + 4) = 2 * (2 : ℝ) ^ (N₁ + 3) := by
      rw [show N₁ + 4 = (N₁ + 3) + 1 by omega, pow_succ]; ring
    linarith [hNrpow, hpow]
  have ht_ge : z ≤ t := by
    rw [ht_eq]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (i + 1) := one_le_pow₀ (by norm_num)
    nlinarith [hz]
  have ht_pos : 0 < t := lt_of_lt_of_le hz ht_ge
  have ht_lt : t < Nr * z' := by
    rw [ht_eq]
    have h1 : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ (N₁ + 2) :=
      pow_le_pow_right₀ (by norm_num) hi1
    have hA : (2 : ℝ) ^ (N₁ + 2) * z ≤ Nr / 4 * z :=
      mul_le_mul_of_nonneg_right hNrq4 hz.le
    have hB : Nr / 4 * z ≤ Nr / 4 * z' := mul_le_mul_of_nonneg_left hle (by positivity)
    have hC : Nr / 4 * z' < Nr * z' := by nlinarith [hNrpos, hz'pos]
    have hD : (2 : ℝ) ^ (i + 1) * z ≤ (2 : ℝ) ^ (N₁ + 2) * z :=
      mul_le_mul_of_nonneg_right h1 hz.le
    linarith
  have h2t_lt : 2 * t < Nr * z' := by
    rw [h2t_eq2]
    have h1 : (2 : ℝ) ^ (i + 2) ≤ (2 : ℝ) ^ (N₁ + 3) :=
      pow_le_pow_right₀ (by norm_num) hi2
    have hA : (2 : ℝ) ^ (N₁ + 3) * z ≤ Nr / 2 * z :=
      mul_le_mul_of_nonneg_right hNrq2 hz.le
    have hB : Nr / 2 * z ≤ Nr / 2 * z' := mul_le_mul_of_nonneg_left hle (by positivity)
    have hC : Nr / 2 * z' < Nr * z' := by nlinarith [hNrpos, hz'pos]
    have hD : (2 : ℝ) ^ (i + 2) * z ≤ (2 : ℝ) ^ (N₁ + 3) * z :=
      mul_le_mul_of_nonneg_right h1 hz.le
    linarith
  have htW : t ∈ Set.Ioo (z / Nr) (Nr * z') :=
    ⟨lt_of_lt_of_le (div_lt_self hz hNr1) ht_ge, ht_lt⟩
  have h2tW : 2 * t ∈ Set.Ioo (z / Nr) (Nr * z') :=
    ⟨lt_of_lt_of_le (lt_of_lt_of_le (div_lt_self hz hNr1) ht_ge) (by linarith [ht_pos]),
      h2t_lt⟩
  -- ### the deep-ratio bound at `t`
  have hΓβ : Γ ≤ Nr * z' / ((2 : ℝ) ^ (k + 1) * z) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (N₁ + 3) := pow_le_pow_right₀ (by norm_num) hk_le3
    have h2 : Γ * (2 : ℝ) ^ (k + 1) ≤ Nr := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
      nlinarith [h1, hNrbig, hΓ1, hpos]
    nlinarith [h2, hz, hle]
  have hdeep : IsDeepR B₀ c (Nr * z' / ((2 : ℝ) ^ (k + 1) * z)) t := by
    intro b hb hmem
    obtain ⟨hm1, hm2⟩ := hmem
    set β : ℝ := Nr * z' / ((2 : ℝ) ^ (k + 1) * z) with hβdef
    have hβpos : 0 < β := by rw [hβdef]; positivity
    have ht2β : 2 * β * t = Nr * z' := by
      rw [hβdef, htdef]
      have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
      rw [hpow]
      field_simp
    have htdiv : t / (2 * β) = t ^ 2 / (Nr * z') := by
      rw [hβdef, htdef]
      have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
      rw [hpow]
      field_simp
    have hleft : z / Nr ≤ b := by
      have ht_ge2 : 2 * z ≤ t := by
        rw [htdef]
        have h1 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk1
        nlinarith [h1, hz]
      have key : z / Nr ≤ t ^ 2 / (Nr * z') := by
        rw [div_le_div_iff₀ hNrpos (by positivity)]
        have ht0 : 0 ≤ t := le_of_lt ht_pos
        have hsq : 4 * z ^ 2 ≤ t ^ 2 := by nlinarith [ht_ge2, ht0, hz]
        have hzz' : z * z' ≤ t ^ 2 := by nlinarith [hsq, hle, h2z, hz]
        nlinarith [hzz', hNrpos]
      rw [← htdiv] at key
      exact le_trans key hm1
    have hright : b ≤ Nr * z' := by
      rw [ht2β] at hm2
      exact hm2
    exact hfree b hleft hright hb
  have hrat : RatW Y c t (ratioY Y c t) := ratW_ratioY hfun hst.1 hab hfreeW htW h2tW
  have hρt_pos : 0 < ratioY Y c t := free_ratioY_pos hst.1 hab hfreeW htW h2tW
  have hρt_lt : ratioY Y c t < Nr / 2 := by
    have h1 : |ratioY Y c t| < Nr * z' / ((2 : ℝ) ^ (k + 1) * z) :=
      hΓbd _ hΓβ c t (ratioY Y c t) ht_pos hdeep hrat
    rw [abs_of_pos hρt_pos] at h1
    have h3 : Nr * z' / ((2 : ℝ) ^ (k + 1) * z) ≤ Nr / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
      have hk2 : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hk1
      have hz2 : 2 * z ≤ (2 : ℝ) ^ k * z := by
        have := mul_le_mul_of_nonneg_right hk2 hz.le
        simpa using this
      have hz'le : z' ≤ (2 : ℝ) ^ k * z := le_trans h2z hz2
      rw [hpow]
      nlinarith [hz'le, hz, hNrpos]
    linarith
  -- ### the slot comparison
  have hslot : MonotoneOn (valY Y c) (Set.Icc t (2 * t)) ∨
      AntitoneOn (valY Y c) (Set.Icc t (2 * t)) :=
    slot_monoOrAnti (u := z / Nr) (v := Nr * z') (t₁ := t) (t₂ := 2 * t) hab hfreeW
      (by
        intro x hx
        exact ⟨lt_of_lt_of_le (div_lt_self hz hNr1) (le_trans ht_ge hx.1),
          lt_of_le_of_lt hx.2 h2t_lt⟩)
      (by linarith [ht_pos])
      (fun x hx => hfreeW x ⟨lt_of_lt_of_le (div_lt_self hz hNr1) (le_trans ht_ge (le_of_lt hx.1)),
        lt_of_lt_of_le hx.2 h2t_lt.le⟩)
      (fun x hx => hslot_free x hx)
      hfun hst.1 htri
  have hRk : |valY Y c ((2 : ℝ) ^ k * z')| ≤ (Nr / 2) * |valY Y c t| := by
    have hmem : (2 : ℝ) ^ k * z' ∈ Set.Icc t (2 * t) := by
      rw [htdef]
      have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      constructor
      · nlinarith [hle]
      · nlinarith [hle, hz]
    have h2tval : |valY Y c (2 * t)| = ratioY Y c t * |valY Y c t| := by
      have hne : valY Y c t ≠ 0 := hval_ne htW
      have h1 : valY Y c (2 * t) = ratioY Y c t * valY Y c t := by
        rw [ratioY]; field_simp
      rw [h1, abs_mul, abs_of_pos hρt_pos]
    have hrat_slot : |valY Y c (2 * t)| ≤ (Nr / 2) * |valY Y c t| := by
      rw [h2tval]
      exact mul_le_mul_of_nonneg_right hρt_lt.le (abs_nonneg _)
    exact abs_le_of_slot_mono ht_pos (by linarith) hslot hrat_slot hmem
  -- ### the telescoping
  have hsub2 : ∀ x ∈ Set.Ioo (z / Nr) (Nr * z' / 2), 2 * x ∈ Set.Ioo (z / Nr) (Nr * z') := by
    intro x hx
    exact ⟨by nlinarith [hx.1, hzp, hz], by nlinarith [hx.2]⟩
  have hwin_of_sub : ∀ {x : ℝ}, x ∈ Set.Ioo (z / Nr) (Nr * z' / 2) →
      x ∈ Set.Ioo (z / Nr) (Nr * z') :=
    fun hx => ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith [hz'pos, hNrpos])⟩
  have hGrel : ∀ x ∈ Set.Ioo (z / Nr) (Nr * z' / 2),
      |valY Y c (2 * x)| = ratioY Y c x * |valY Y c x| := by
    intro x hx
    have hxW : x ∈ Set.Ioo (z / Nr) (Nr * z') := ⟨hx.1, by linarith [hx.2, hz'pos, hNrpos]⟩
    have h2xW := hsub2 x hx
    have hne : valY Y c x ≠ 0 := hval_ne hxW
    have h1 : valY Y c (2 * x) = ratioY Y c x * valY Y c x := by
      rw [ratioY]; field_simp
    have hpos : 0 < ratioY Y c x := free_ratioY_pos hst.1 hab hfreeW hxW h2xW
    rw [h1, abs_mul, abs_of_pos hpos]
  have hmemSub : ∀ j : ℕ, j ≤ k → (2 : ℝ) ^ j * z ∈ Set.Ioo (z / Nr) (Nr * z' / 2) := by
    intro j hj
    have hpj : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have h1 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (N₁ + 2) :=
      le_trans (pow_le_pow_right₀ (by norm_num) hj)
        (pow_le_pow_right₀ (by norm_num) hk_le)
    have hA : (2 : ℝ) ^ (N₁ + 2) * z ≤ Nr / 4 * z := mul_le_mul_of_nonneg_right hNrq4 hz.le
    have hB : Nr / 4 * z ≤ Nr / 4 * z' := mul_le_mul_of_nonneg_left hle (by positivity)
    have hC : Nr / 4 * z' < Nr / 2 * z' := by nlinarith [hNrpos, hz'pos]
    have hD : (2 : ℝ) ^ j * z ≤ (2 : ℝ) ^ (N₁ + 2) * z := mul_le_mul_of_nonneg_right h1 hz.le
    constructor
    · have h5 : z / Nr < z := div_lt_self hz hNr1
      have hzle : z ≤ (2 : ℝ) ^ j * z := by
        have hone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        nlinarith [hone, hz]
      exact lt_of_lt_of_le h5 hzle
    · linarith
  have hmemSub' : ∀ j : ℕ, j ≤ k → (2 : ℝ) ^ j * z' ∈ Set.Ioo (z / Nr) (Nr * z' / 2) := by
    intro j hj
    have hpj : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have h1 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (N₁ + 2) :=
      le_trans (pow_le_pow_right₀ (by norm_num) hj)
        (pow_le_pow_right₀ (by norm_num) hk_le)
    have hA : (2 : ℝ) ^ j * z' ≤ (2 : ℝ) ^ (N₁ + 2) * z' := mul_le_mul_of_nonneg_right h1 hz'pos.le
    have hB : (2 : ℝ) ^ (N₁ + 2) * z' ≤ Nr / 4 * z' := mul_le_mul_of_nonneg_right hNrq4 hz'pos.le
    have hC : Nr / 4 * z' < Nr / 2 * z' := by nlinarith [hNrpos, hz'pos]
    constructor
    · have h5 : z / Nr < z := div_lt_self hz hNr1
      have h6 : z ≤ (2 : ℝ) ^ j * z' := by
        have hone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
        have h1' : z' ≤ (2 : ℝ) ^ j * z' := by nlinarith [hone, hz'pos]
        exact le_trans hle h1'
      exact lt_of_lt_of_le h5 h6
    · linarith
  have hchain : |valY Y c z'| * |valY Y c ((2 : ℝ) ^ k * z)| ≤
      |valY Y c ((2 : ℝ) ^ k * z')| * |valY Y c z| := by
    refine rise_le_shift_up (G := fun x => |valY Y c x|) (ρ := ratioY Y c)
      (hprod := telescoping_up (G := fun x => |valY Y c x|) (ρ := ratioY Y c) z k
        (fun j hj => hGrel _ (hmemSub j (le_of_lt hj))))
      (hprod' := telescoping_up (G := fun x => |valY Y c x|) (ρ := ratioY Y c) z' k
        (fun j hj => hGrel _ (hmemSub' j (le_of_lt hj))))
      (hpos := abs_pos.mpr (hval_ne hzW)) (hpos' := abs_pos.mpr (hval_ne hz'W))
      (hmono := fun j hj =>
        hρmono (hmemSub j (le_of_lt hj)) (hmemSub' j (le_of_lt hj))
          (mul_le_mul_of_nonneg_left hle (by positivity)))
      (hρnn := fun j hj => le_of_lt (free_ratioY_pos hst.1 hab hfreeW
        (hwin_of_sub (hmemSub j (le_of_lt hj))) (hsub2 _ (hmemSub j (le_of_lt hj)))))
  -- ### assemble
  have hApos : 0 < |valY Y c ((2 : ℝ) ^ k * z)| := abs_pos.mpr (hval_ne htW)
  have hkey : |valY Y c z'| ≤ (Nr / 2) * |valY Y c z| := by
    have h1 : |valY Y c z'| * |valY Y c ((2 : ℝ) ^ k * z)| ≤
        ((Nr / 2) * |valY Y c z|) * |valY Y c ((2 : ℝ) ^ k * z)| := by
      calc |valY Y c z'| * |valY Y c ((2 : ℝ) ^ k * z)|
          ≤ |valY Y c ((2 : ℝ) ^ k * z')| * |valY Y c z| := hchain
        _ ≤ ((Nr / 2) * |valY Y c t|) * |valY Y c z| :=
            mul_le_mul_of_nonneg_right hRk (abs_nonneg _)
        _ = ((Nr / 2) * |valY Y c z|) * |valY Y c t| := by ring
        _ = ((Nr / 2) * |valY Y c z|) * |valY Y c ((2 : ℝ) ^ k * z)| := by rw [htdef]
    exact (mul_le_mul_iff_of_pos_right hApos).mp h1
  rw [eq_valY hfun hgz', eq_valY hfun hgz]
  exact hkey

end Work.WilC4
