/-
  WilC4/rexp_deep_window_value_ratio_case_down : **Case B** of the proof of
  `Work.WilC4.rexp_deep_window_value_ratio` (the doubling ratio is *nonincreasing* on the window).

  The mirrored argument of `...case_up`: if the doubling ratio `ρ` is nonincreasing, then the value
  ratio `G (z') / G (z)` is at most the value ratio over the *backward* shifted pair
  `(z / 2^i, z' / 2^i)` (telescoping along the halving chain), and the slots
  `(z / 2^i, 2 z / 2^i)`, `i = 0, …, N₁+2`, are pairwise disjoint, so one of them meets `Bm` in no
  point.  On that slot the fibre is monotone-or-antitone and the deep-ratio bound at `t = z / 2^i`
  (with the scale `N / 2^{i+1}`) gives `G (z' / 2^i) ≤ (N/2) · G (z / 2^i)`.
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

/-- **Case B.**  If the doubling ratio of the fibre is nonincreasing on the window, then the value
ratio over a pair `z ≤ z' ≤ 2z` whose window `[z/N, N z']` is free of `B₀` is bounded by `N/2`,
provided `N` is large compared with `Γ` and `N₁`. -/
theorem window_ratio_case_down {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {B₀ Bm : Set (Fin (k + 1) → ℝ)}
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
    (hρanti : AntitoneOn (ratioY Y c) (Set.Ioo (z / Nr) (Nr * z' / 2))) :
    |y'| ≤ (Nr / 2) * |y| := by
  classical
  have hNr2 : (2 : ℝ) ≤ Nr := by linarith
  have hNrpos : 0 < Nr := by linarith
  have hNr1 : (1 : ℝ) < Nr := by linarith
  have hNr2lt : (2 : ℝ) < Nr := by
    have h1 : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ (N₁ + 4) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ 4 = 16 := by norm_num
    linarith [h1, h2, hNrpow]
  have hz'pos : 0 < z' := lt_of_lt_of_le hz hle
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
  have hzW : z ∈ Set.Ioo (z / Nr) (Nr * z') :=
    ⟨div_lt_self hz hNr1, by nlinarith [hz'pos, hle, hNr2]⟩
  have hz'W : z' ∈ Set.Ioo (z / Nr) (Nr * z') :=
    ⟨lt_of_lt_of_le (div_lt_self hz hNr1) hle, by nlinarith [hz'pos, hNr1]⟩
  -- ### the breakpoint-free slot
  obtain ⟨i, hi_le, hifree⟩ :=
    exists_free_slot (P := {x : ℝ | Fin.cons x c ∈ Bm}) (K := N₁ + 2)
      (le_trans (hBmcard c) (by exact_mod_cast (show N₁ ≤ N₁ + 2 by omega)))
      (fun i => z / (2 : ℝ) ^ i) (fun i => 2 * z / (2 : ℝ) ^ i)
      (by
        intro i j hij
        rw [Set.disjoint_left]
        intro p hp1 hp2
        have hkey : 2 * z / (2 : ℝ) ^ j ≤ z / (2 : ℝ) ^ i := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hp : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have hpow : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by rw [pow_succ]; ring
          have h1 : (2 : ℝ) ^ (i + 1) * z ≤ (2 : ℝ) ^ j * z :=
            mul_le_mul_of_nonneg_right hp hz.le
          rw [hpow] at h1
          nlinarith [h1, hz]
        linarith [hp2.2, hp1.1, hkey])
  -- ### the numerical bounds
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
  have hPowlt : ∀ j : ℕ, j ≤ N₁ + 2 → (2 : ℝ) ^ j < Nr := by
    intro j hj
    have h1 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (N₁ + 2) := pow_le_pow_right₀ (by norm_num) hj
    linarith [h1, hNrq4, hNrpos]
  have hi3 : i + 1 ≤ N₁ + 3 := by omega
  -- ### the slot, the point `t` and its double
  set t : ℝ := z / (2 : ℝ) ^ i with htdef
  have ht_eq : t = z / (2 : ℝ) ^ i := htdef
  have h2t_eq : 2 * t = 2 * z / (2 : ℝ) ^ i := by
    rw [htdef, mul_div_assoc]
  have hslot_free : ∀ p ∈ Set.Ioo t (2 * t), Fin.cons p c ∉ Bm := by
    intro p hp hBm
    refine hifree p hBm ?_
    rw [ht_eq, h2t_eq] at hp
    exact hp
  have ht_pos : 0 < t := by rw [ht_eq]; positivity
  have ht_ge : z / Nr < t := by
    rw [ht_eq, div_lt_div_iff₀ hNrpos (by positivity)]
    have hp : (2 : ℝ) ^ i < Nr := hPowlt i hi_le
    nlinarith [hp, hz]
  have ht_lt : t < Nr * z' := by
    have h1 : t ≤ z := by
      rw [ht_eq, div_le_iff₀ (by positivity)]
      have hone : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      nlinarith [hone, hz]
    have h2 : z < Nr * z' := by nlinarith [hNr1, hz, hle, hz'pos]
    linarith
  have h2t_ge : z / Nr < 2 * t := lt_of_lt_of_le ht_ge (by linarith [ht_pos])
  have h2t_lt : 2 * t < Nr * z' := by
    have h1 : 2 * t ≤ 2 * z := by
      rw [h2t_eq, div_le_iff₀ (by positivity)]
      have hone : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      nlinarith [hone, hz]
    have h2 : 2 * z ≤ 2 * z' := by linarith
    have h3 : 2 * z' < Nr * z' := by nlinarith [hz'pos, hNr2lt]
    linarith
  have htW : t ∈ Set.Ioo (z / Nr) (Nr * z') := ⟨ht_ge, ht_lt⟩
  have h2tW : 2 * t ∈ Set.Ioo (z / Nr) (Nr * z') := ⟨h2t_ge, h2t_lt⟩
  -- ### the deep-ratio bound at `t`
  have hΓβ : Γ ≤ Nr / (2 : ℝ) ^ (i + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ (N₁ + 3) :=
      pow_le_pow_right₀ (by norm_num) hi3
    have h2 : Γ * (2 : ℝ) ^ (i + 1) ≤ Nr := by
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (i + 1) := by positivity
      nlinarith [h1, hNrbig, hΓ1, hpos]
    linarith
  have hdeep : IsDeepR B₀ c (Nr / (2 : ℝ) ^ (i + 1)) t := by
    intro b hb hmem
    obtain ⟨hm1, hm2⟩ := hmem
    set β : ℝ := Nr / (2 : ℝ) ^ (i + 1) with hβdef
    have ht2β : 2 * β * t = Nr * z / ((2 : ℝ) ^ i * (2 : ℝ) ^ i) := by
      rw [hβdef, ht_eq]
      have hpow : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by rw [pow_succ]; ring
      rw [hpow]
      field_simp
    have htdiv : t / (2 * β) = z / Nr := by
      rw [hβdef, ht_eq]
      have hpow : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by rw [pow_succ]; ring
      rw [hpow]
      field_simp
    have hleft : z / Nr ≤ b := by
      rw [← htdiv]
      exact hm1
    have hright : b ≤ Nr * z' := by
      have hp2 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      have hNrzz : Nr * z / ((2 : ℝ) ^ i * (2 : ℝ) ^ i) ≤ Nr * z' := by
        rw [div_le_iff₀ (by positivity)]
        have h1 : Nr * z ≤ Nr * z' := mul_le_mul_of_nonneg_left hle hNrpos.le
        have h2 : Nr * z' * 1 ≤ Nr * z' * ((2 : ℝ) ^ i * (2 : ℝ) ^ i) := by
          have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ i := by nlinarith [hp2]
          nlinarith [h3, hNrpos, hz'pos]
        linarith
      rw [ht2β] at hm2
      linarith
    exact hfree b hleft hright hb
  have hrat : RatW Y c t (ratioY Y c t) := ratW_ratioY hfun hst.1 hab hfreeW htW h2tW
  have hρt_pos : 0 < ratioY Y c t := free_ratioY_pos hst.1 hab hfreeW htW h2tW
  have hρt_lt : ratioY Y c t < Nr / 2 := by
    have h1 : |ratioY Y c t| < Nr / (2 : ℝ) ^ (i + 1) :=
      hΓbd _ hΓβ c t (ratioY Y c t) ht_pos hdeep hrat
    rw [abs_of_pos hρt_pos] at h1
    have h3 : Nr / (2 : ℝ) ^ (i + 1) ≤ Nr / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      have hone : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
      have hpow : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by rw [pow_succ]; ring
      nlinarith [hone, hpow, hNrpos]
    linarith
  -- ### the slot comparison at `z'/2^i`
  have hslot : MonotoneOn (valY Y c) (Set.Icc t (2 * t)) ∨
      AntitoneOn (valY Y c) (Set.Icc t (2 * t)) :=
    slot_monoOrAnti (u := z / Nr) (v := Nr * z') (t₁ := t) (t₂ := 2 * t) hab hfreeW
      (fun x hx => ⟨lt_of_lt_of_le ht_ge hx.1, lt_of_le_of_lt hx.2 h2t_lt⟩)
      (by linarith [ht_pos])
      (fun x hx => hfreeW x ⟨lt_of_lt_of_le ht_ge (le_of_lt hx.1), lt_trans hx.2 h2t_lt⟩)
      (fun x hx => hslot_free x hx)
      hfun hst.1 htri
  have hRk : |valY Y c (z' / (2 : ℝ) ^ i)| ≤ (Nr / 2) * |valY Y c t| := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
    have hmem : z' / (2 : ℝ) ^ i ∈ Set.Icc t (2 * t) := by
      rw [ht_eq, h2t_eq]
      constructor
      · rw [div_le_div_iff₀ hp hp]; nlinarith [hle]
      · rw [div_le_div_iff₀ hp (by positivity)]
        nlinarith [h2z, hz'pos, hp]
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
    exact ⟨by nlinarith [hx.1, div_pos hz hNrpos], by nlinarith [hx.2]⟩
  have hwin_of_sub : ∀ {x : ℝ}, x ∈ Set.Ioo (z / Nr) (Nr * z' / 2) →
      x ∈ Set.Ioo (z / Nr) (Nr * z') :=
    fun hx => ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith [hz'pos, hNrpos])⟩
  have hGrel : ∀ x ∈ Set.Ioo (z / Nr) (Nr * z' / 2),
      |valY Y c (2 * x)| = ratioY Y c x * |valY Y c x| := by
    intro x hx
    have hxW : x ∈ Set.Ioo (z / Nr) (Nr * z') := hwin_of_sub hx
    have h2xW := hsub2 x hx
    have hne : valY Y c x ≠ 0 := hval_ne hxW
    have h1 : valY Y c (2 * x) = ratioY Y c x * valY Y c x := by
      rw [ratioY]; field_simp
    have hpos : 0 < ratioY Y c x := free_ratioY_pos hst.1 hab hfreeW hxW h2xW
    rw [h1, abs_mul, abs_of_pos hpos]
  have hmemD : ∀ j : ℕ, j < i → z / (2 : ℝ) ^ (j + 1) ∈ Set.Ioo (z / Nr) (Nr * z' / 2) := by
    intro j hj
    have hp : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
    have h1 : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h1' : (2 : ℝ) ^ (j + 1) < Nr :=
      lt_of_le_of_lt (le_trans h1 (pow_le_pow_right₀ (by norm_num) hi_le))
        (hPowlt (N₁ + 2) le_rfl)
    constructor
    · rw [div_lt_div_iff₀ hNrpos hp]
      nlinarith [h1', hz]
    · rw [div_lt_iff₀ hp]
      have h2 : z < Nr * z' := by nlinarith [hNr1, hz, hle, hz'pos]
      have hpow : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
      have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have h3 : Nr * z' ≤ Nr * z' / 2 * (2 : ℝ) ^ (j + 1) := by
        rw [hpow]
        nlinarith [h2j, hz'pos, hNrpos]
      linarith
  have hmemD' : ∀ j : ℕ, j < i → z' / (2 : ℝ) ^ (j + 1) ∈ Set.Ioo (z / Nr) (Nr * z' / 2) := by
    intro j hj
    have hp : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
    have h1 : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h1' : (2 : ℝ) ^ (j + 1) < Nr :=
      lt_of_le_of_lt (le_trans h1 (pow_le_pow_right₀ (by norm_num) hi_le))
        (hPowlt (N₁ + 2) le_rfl)
    constructor
    · rw [div_lt_div_iff₀ hNrpos hp]
      have h2 : z * (2 : ℝ) ^ (j + 1) ≤ z' * (2 : ℝ) ^ (j + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
      have h3 : z' * (2 : ℝ) ^ (j + 1) < z' * Nr := by nlinarith [h1', hz'pos]
      linarith
    · rw [div_lt_iff₀ hp]
      have h2 : z' < Nr * z' := by nlinarith [hNr1, hz'pos]
      have hpow : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
      have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have h3 : Nr * z' ≤ Nr * z' / 2 * (2 : ℝ) ^ (j + 1) := by
        rw [hpow]
        nlinarith [h2j, hz'pos, hNrpos]
      linarith
  have hchain : |valY Y c z'| * |valY Y c (z / (2 : ℝ) ^ i)| ≤
      |valY Y c (z' / (2 : ℝ) ^ i)| * |valY Y c z| := by
    refine rise_le_shift_down (G := fun x => |valY Y c x|) (ρ := ratioY Y c)
      (hprod := telescoping_down (G := fun x => |valY Y c x|) (ρ := ratioY Y c) z i
        (fun j hj => hGrel _ (hmemD j hj)))
      (hprod' := telescoping_down (G := fun x => |valY Y c x|) (ρ := ratioY Y c) z' i
        (fun j hj => hGrel _ (hmemD' j hj)))
      (hA := abs_nonneg _) (hB := abs_nonneg _)
      (hmono := fun j hj =>
        hρanti (hmemD j hj) (hmemD' j hj) (by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          exact mul_le_mul_of_nonneg_right hle (by positivity)))
      (hρnn := fun j hj => le_of_lt (free_ratioY_pos hst.1 hab hfreeW
        (hwin_of_sub (hmemD' j hj)) (hsub2 _ (hmemD' j hj))))
  -- ### assemble
  have hApos : 0 < |valY Y c (z / (2 : ℝ) ^ i)| := abs_pos.mpr (hval_ne htW)
  have hkey : |valY Y c z'| ≤ (Nr / 2) * |valY Y c z| := by
    have h1 : |valY Y c z'| * |valY Y c (z / (2 : ℝ) ^ i)| ≤
        ((Nr / 2) * |valY Y c z|) * |valY Y c (z / (2 : ℝ) ^ i)| := by
      calc |valY Y c z'| * |valY Y c (z / (2 : ℝ) ^ i)|
          ≤ |valY Y c (z' / (2 : ℝ) ^ i)| * |valY Y c z| := hchain
        _ ≤ ((Nr / 2) * |valY Y c t|) * |valY Y c z| :=
            mul_le_mul_of_nonneg_right hRk (abs_nonneg _)
        _ = ((Nr / 2) * |valY Y c z|) * |valY Y c t| := by ring
        _ = ((Nr / 2) * |valY Y c z|) * |valY Y c (z / (2 : ℝ) ^ i)| := by rw [ht_eq]
    exact (mul_le_mul_iff_of_pos_right hApos).mp h1
  rw [eq_valY hfun hgz', eq_valY hfun hgz]
  exact hkey

end Work.WilC4
