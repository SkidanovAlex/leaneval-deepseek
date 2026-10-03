import Mathlib
import Submission.Work.Peluse.SwapC.concatGlue
import Submission.Work.Peluse.SwapC.mCubeSum_norm_le
import Submission.Work.Peluse.SwapC.mCubeSum_le_one_scaled

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-! ## Cardinality bookkeeping for `symIcc` and `mixWin` -/

/-- `(symIcc N).card = 2N+1`. -/
private lemma card_symIcc (N : ℕ) : (symIcc N).card = 2 * N + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- `(mixWin x₀ dH0 N).card = 6N+1` (it is a translate of `symIcc (3N)`). -/
private lemma card_mixWin (x₀ dH0 : ℤ) (N : ℕ) : (mixWin x₀ dH0 N).card = 6 * N + 1 := by
  rw [mixWin, Finset.card_map, card_symIcc]
  ring

/-- The cardinality ratio of the mixed window to the base window is at most `3`. -/
private lemma card_mixWin_ratio (x₀ dH0 : ℤ) (N : ℕ) :
    ((mixWin x₀ dH0 N).card : ℝ) / ((symIcc N).card : ℝ) ≤ 3 := by
  rw [card_mixWin, card_symIcc]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ))]
  push_cast
  linarith

/-! ## Elementary shift estimates -/

/-- Shifting by `c` shifts the support bound by `|c|`. -/
private lemma lt_natAbs_add (z c : ℤ) (A : ℕ) (h : A + c.natAbs < z.natAbs) :
    A < (z + c).natAbs := by
  have h1 : ((A : ℤ) + (c.natAbs : ℤ)) < (z.natAbs : ℤ) := by exact_mod_cast h
  rw [Int.natCast_natAbs, Int.natCast_natAbs] at h1
  have h2 : |z| ≤ |z + c| + |c| := by
    have h3 := abs_add_le (z + c) (-c)
    rw [abs_neg] at h3
    rwa [show z + c + -c = z by ring] at h3
  have h4 : (A : ℤ) < ((z + c).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    linarith
  exact_mod_cast h4

/-- A function supported in `[-L,L]` vanishes on `z + c` when `z` is far enough out. -/
private lemma shift_eq_zero {f : ℤ → ℂ} {L : ℕ} (hf : SupportIn f L) {c z : ℤ}
    (hz : L + c.natAbs < z.natAbs) : f (z + c) = 0 :=
  hf (z + c) (lt_natAbs_add z c L hz)

/-- If both halves of a `2s`-fold sign pattern are identically `false`, the pattern is `0`. -/
private lemma cL_cR_false_eq_zero {s : ℕ} {ω : Fin (2 * s) → Bool}
    (hL : ∀ j : Fin s, cL s ω j = false) (hR : ∀ j : Fin s, cR s ω j = false) : ω = 0 := by
  funext i
  rcases i with ⟨v, hv⟩
  by_cases h : v < s
  · have hh := hL ⟨v, h⟩
    rw [cL] at hh
    have heq : (⟨v, by omega⟩ : Fin (2 * s)) = ⟨v, hv⟩ := Fin.ext rfl
    rw [heq] at hh
    exact hh
  · have hh := hR ⟨v - s, by omega⟩
    rw [cR] at hh
    have heq : (⟨s + (v - s), by omega⟩ : Fin (2 * s)) = ⟨v, hv⟩ := by
      apply Fin.ext; simp; omega
    rw [heq] at hh
    exact hh

/-! ## The support of `cFunI` and the per-corner box bound -/

/-- Every entry of the truncated corner family `cFunI` has finite support: either it is one of the
products of `f`'s (supported in a translate of `symIcc N`), or it is the indicator of the mixed
window `mixWin x₀ dH0 N`. -/
private lemma cFunI_finSupp (s : ℕ) (f : ℤ → ℂ) (x₀ dH0 dH1 : ℤ) (N : ℕ)
    (hsup : ∀ x : ℤ, x ∉ (symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0)
    (ω : Fin (2 * s) → Bool) : FinSuppZ (cFunI s f x₀ dH0 dH1 N ω) := by
  have hf : SupportIn f (N + x₀.natAbs) := by
    intro x hx
    refine hsup x ?_
    intro hmem
    rw [Finset.mem_map] at hmem
    obtain ⟨a, ha, hax⟩ := hmem
    have hax' : a + x₀ = x := by simpa using hax
    have haN : a.natAbs ≤ N := mem_symIcc_iff.mp ha
    have h1 : x.natAbs ≤ N + x₀.natAbs := by
      rw [← hax']
      calc (a + x₀).natAbs ≤ a.natAbs + x₀.natAbs := Int.natAbs_add_le a x₀
        _ ≤ N + x₀.natAbs := Nat.add_le_add_right haN _
    omega
  refine ⟨3 * N + x₀.natAbs + dH0.natAbs + dH1.natAbs, fun z hz => ?_⟩
  by_cases hmix : (∀ j : Fin s, cL s ω j = false) ∨ (∀ j : Fin s, cR s ω j = false)
  · rw [cFunI_eq_cFun hmix, cFun_eq_cUB]
    simp only [cUB]
    by_cases hR : ∀ j : Fin s, cR s ω j = false
    · by_cases hL : ∀ j : Fin s, cL s ω j = false
      · rw [if_pos ⟨hL, hR⟩]
        have hz0 : (N + x₀.natAbs + dH0.natAbs) < z.natAbs := by omega
        rw [shift_eq_zero hf (c := dH0) hz0]
        simp
      · rw [if_neg (fun h => hL h.1), if_pos hR]
        have hz0 : (N + x₀.natAbs) < z.natAbs := by omega
        rw [hf z hz0]
        simp
    · rw [if_neg (fun h => hR h.2), if_neg hR]
      by_cases hL : ∀ j : Fin s, cL s ω j = false
      · rw [if_pos hL]
        have hz0 : (N + x₀.natAbs + dH1.natAbs) < z.natAbs := by omega
        rw [shift_eq_zero hf (c := dH1) hz0]
        simp
      · exact absurd (hmix.resolve_right hR) hL
  · rw [cFunI_eq_indicator hmix]
    by_cases hz' : z ∈ mixWin x₀ dH0 N
    · exfalso
      rw [mixWin, Finset.mem_map] at hz'
      obtain ⟨a, ha, haz⟩ := hz'
      have haz' : a + x₀ + dH0 = z := by simpa using haz
      have haN : a.natAbs ≤ 3 * N := mem_symIcc_iff.mp ha
      have h1 : z.natAbs ≤ 3 * N + x₀.natAbs + dH0.natAbs := by
        rw [← haz']
        calc (a + x₀ + dH0).natAbs ≤ (a + x₀).natAbs + dH0.natAbs := Int.natAbs_add_le _ _
          _ ≤ (a.natAbs + x₀.natAbs) + dH0.natAbs := Nat.add_le_add_right (Int.natAbs_add_le a x₀) _
          _ ≤ 3 * N + x₀.natAbs + dH0.natAbs := by omega
      omega
    · simp [hz']

/-- **The per-corner box bound.**  For `ω ≠ 0` the box power of the single entry `cFunI ω` is at
most `3`: a non-mixed corner is one of the products `f z · \bar f (z+dH0)` or
`\bar f z · f (z+dH1)`, supported in a translate of `symIcc N` (ratio `≤ 1`), while a mixed corner
is the indicator of `mixWin`, whose cardinality is `3` times that of `symIcc N` (up to the additive
`1`, which vanishes in the ratio `(6N+1)/(2N+1) ≤ 3`). -/
private lemma cFunI_factor_le (s M N : ℕ) (qL₁ qL₂ qR₁ qR₂ : Fin s → ℤ) (dH0 dH1 : ℤ)
    (f : ℤ → ℂ) (x₀ : ℤ) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hsup : ∀ x : ℤ, x ∉ (symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0)
    (ω : Fin (2 * s) → Bool) (hω : ω ≠ 0) :
    ‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂) (symIcc N)
      (fun _ => cFunI s f x₀ dH0 dH1 N ω)‖ ≤ 3 := by
  have hSpos : (symIcc N).card ≠ 0 := by rw [card_symIcc]; omega
  by_cases hmix : (∀ j : Fin s, cL s ω j = false) ∨ (∀ j : Fin s, cR s ω j = false)
  · rw [cFunI_eq_cFun hmix]
    rcases hmix with hL | hR
    · -- the `cL`-half vanishes: the corner is `\bar f z · f (z + dH1)`
      have hR' : ¬ (∀ j : Fin s, cR s ω j = false) := fun hR => hω (cL_cR_false_eq_zero hL hR)
      have hfmt : cFun s f dH0 dH1 ω = fun z => star (f z) * f (z + dH1) := by
        rw [cFun_eq_cUB]
        simp only [cUB]
        rw [if_neg (fun h => hR' h.2), if_neg hR', if_pos hL]
      rw [hfmt]
      have h1 := mCubeSum_le_one_scaled (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂)
        (symIcc N) (Finset.image (fun s => s - dH1) ((symIcc N).map (Equiv.addRight x₀).toEmbedding))
        (fun z => star (f z) * f (z + dH1)) hSpos ?_ ?_
      · refine le_trans h1 ?_
        have hpos : (0 : ℝ) < ((symIcc N).card : ℝ) := by rw [card_symIcc]; positivity
        rw [div_le_iff₀ hpos]
        have hcard : ((Finset.image (fun s => s - dH1) ((symIcc N).map
            (Equiv.addRight x₀).toEmbedding)).card : ℝ) ≤ ((symIcc N).card : ℝ) := by
          have h : (Finset.image (fun s => s - dH1) ((symIcc N).map
              (Equiv.addRight x₀).toEmbedding)).card ≤ (symIcc N).card := by
            calc _ ≤ ((symIcc N).map (Equiv.addRight x₀).toEmbedding).card := Finset.card_image_le
              _ = (symIcc N).card := Finset.card_map _
          exact_mod_cast h
        have hnn : (0 : ℝ) ≤ ((symIcc N).card : ℝ) := by positivity
        nlinarith
      · intro z hz
        have hz' : f (z + dH1) = 0 :=
          hsup _ (fun hmem => hz (Finset.mem_image.mpr ⟨z + dH1, hmem, by ring⟩))
        rw [hz']
        simp
      · intro z
        rw [norm_mul, norm_star]
        exact mul_le_one₀ (hb z) (norm_nonneg _) (hb _)
    · -- the `cR`-half vanishes: the corner is `f z · \bar f (z + dH0)`
      have hL' : ¬ (∀ j : Fin s, cL s ω j = false) := fun hL => hω (cL_cR_false_eq_zero hL hR)
      have hfmt : cFun s f dH0 dH1 ω = fun z => f z * star (f (z + dH0)) := by
        rw [cFun_eq_cUB]
        simp only [cUB]
        rw [if_neg (fun h => hL' h.1), if_pos hR]
      rw [hfmt]
      have h1 := mCubeSum_le_one_scaled (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂)
        (symIcc N) ((symIcc N).map (Equiv.addRight x₀).toEmbedding)
        (fun z => f z * star (f (z + dH0))) hSpos ?_ ?_
      · refine le_trans h1 ?_
        have hpos : (0 : ℝ) < ((symIcc N).card : ℝ) := by rw [card_symIcc]; positivity
        have hcard : (((symIcc N).map (Equiv.addRight x₀).toEmbedding).card : ℝ)
            = ((symIcc N).card : ℝ) := by
          rw [Finset.card_map]
        rw [hcard, div_self (ne_of_gt hpos)]
        norm_num
      · intro z hz
        rw [hsup z hz]
        simp
      · intro z
        rw [norm_mul, norm_star]
        exact mul_le_one₀ (hb z) (norm_nonneg _) (hb _)
  · -- mixed corner: the indicator of `mixWin`
    rw [cFunI_eq_indicator hmix]
    have h1 := mCubeSum_le_one_scaled (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂)
      (symIcc N) (mixWin x₀ dH0 N)
      (fun z => if z ∈ mixWin x₀ dH0 N then (1 : ℂ) else 0) hSpos ?_ ?_
    · exact le_trans h1 (card_mixWin_ratio x₀ dH0 N)
    · intro z hz
      simp [hz]
    · intro z
      by_cases hz : z ∈ mixWin x₀ dH0 N <;> simp [hz]

/-- The entry of `cFunI` at the corner `ω = 0` is the kernel `\bar f(· + dH0) f(· + dH1)`. -/
private lemma cFunI_entry_zero (s : ℕ) (f : ℤ → ℂ) (x₀ dH0 dH1 : ℤ) (N : ℕ) :
    (fun _ : Fin (2 * s) → Bool => cFunI s f x₀ dH0 dH1 N 0)
      = fun _ => fun y => star (f (y + dH0)) * f (y + dH1) :=
  funext fun _ => cFunI_zero f x₀ dH0 dH1 N

/-! ## The box bound -/

/-- **KKL's truncation step for the concatenation identification.**  The box power of the truncated
corner family `cFunI` is bounded by the box power of its `ω = 0` corner, with the loss `3` coming
from the mixed corners (indicator of a `3N`-window) and the exponent `1/2^{2s}` from the
Gowers–Cauchy–Schwarz inequality `mCubeSum_norm_le`. -/
theorem cFunICubeLe (s M N : ℕ) (hs : 1 ≤ s) (qL₁ qL₂ qR₁ qR₂ : Fin s → ℤ) (dH0 dH1 : ℤ)
    (f : ℤ → ℂ) (x₀ : ℤ) (hb : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hsup : ∀ x : ℤ, x ∉ (Work.Peluse.symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0) :
    ‖Work.Peluse.SwapC.mCubeSum (2 * s) (Fin M × Fin M)
        (Work.Peluse.SwapC.catDir M qL₁ qL₂ qR₁ qR₂) (Work.Peluse.symIcc N)
        (Work.Peluse.SwapC.cFunI s f x₀ dH0 dH1 N)‖
      ≤ 3 * (‖Work.Peluse.SwapC.mCubeSum (2 * s) (Fin M × Fin M)
            (Work.Peluse.SwapC.catDir M qL₁ qL₂ qR₁ qR₂) (Work.Peluse.symIcc N)
            (fun _ => fun y => star (f (y + dH0)) * f (y + dH1))‖) ^ (1 / (2 : ℝ) ^ (2 * s)) := by
  classical
  let e : ℝ := 1 / (2 : ℝ) ^ (2 * s)
  let A : (Fin (2 * s) → Bool) → ℝ := fun ω =>
    ‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂) (symIcc N)
      (fun _ => cFunI s f x₀ dH0 dH1 N ω)‖
  have he : e = 1 / (2 : ℝ) ^ (2 * s) := rfl
  have he0 : 0 ≤ e := by rw [he]; positivity
  have hfin : ∀ ω : Fin (2 * s) → Bool, FinSuppZ (cFunI s f x₀ dH0 dH1 N ω) :=
    fun ω => cFunI_finSupp s f x₀ dH0 dH1 N hsup ω
  have key := mCubeSum_norm_le (2 * s) (by omega) (Fin M × Fin M)
    (catDir M qL₁ qL₂ qR₁ qR₂) (symIcc N) (cFunI s f x₀ dH0 dH1 N) hfin
  have herase : ∏ ω ∈ Finset.univ.erase (0 : Fin (2 * s) → Bool), A ω ^ e ≤ 3 := by
    have hle : ∀ ω ∈ Finset.univ.erase (0 : Fin (2 * s) → Bool), A ω ≤ 3 := by
      intro ω hω
      rw [Finset.mem_erase] at hω
      exact cFunI_factor_le s M N qL₁ qL₂ qR₁ qR₂ dH0 dH1 f x₀ hb hsup ω hω.1
    calc ∏ ω ∈ Finset.univ.erase (0 : Fin (2 * s) → Bool), A ω ^ e
        ≤ ∏ _ω ∈ Finset.univ.erase (0 : Fin (2 * s) → Bool), (3 : ℝ) ^ e := by
          refine Finset.prod_le_prod₀ (fun ω _ => Real.rpow_nonneg (norm_nonneg _) e)
            (fun ω hω => Real.rpow_le_rpow (norm_nonneg _) (hle ω hω) he0)
      _ = ((3 : ℝ) ^ e) ^ (Finset.univ.erase (0 : Fin (2 * s) → Bool)).card :=
          Finset.prod_const _
      _ ≤ ((3 : ℝ) ^ e) ^ (2 ^ (2 * s)) := by
          refine pow_le_pow_right₀ (Real.one_le_rpow (by norm_num) he0) ?_
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin]
          exact Nat.sub_le _ _
      _ = 3 := by
          rw [← Real.rpow_natCast ((3 : ℝ) ^ e) (2 ^ (2 * s)),
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) e (((2 ^ (2 * s) : ℕ)) : ℝ)]
          have h1 : e * (((2 ^ (2 * s) : ℕ)) : ℝ) = 1 := by
            rw [he, Nat.cast_pow, Nat.cast_ofNat]
            rw [div_mul_eq_mul_div, one_mul, div_self]
            exact pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)
          rw [h1, Real.rpow_one]
  have hA0 : A 0 = ‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂) (symIcc N)
      (fun _ => fun y => star (f (y + dH0)) * f (y + dH1))‖ := by
    show ‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂) (symIcc N)
      (fun _ => cFunI s f x₀ dH0 dH1 N 0)‖ = _
    rw [cFunI_entry_zero]
  calc ‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂) (symIcc N)
        (cFunI s f x₀ dH0 dH1 N)‖
      ≤ ∏ ω : Fin (2 * s) → Bool, A ω ^ e := key
    _ = A 0 ^ e * ∏ ω ∈ Finset.univ.erase (0 : Fin (2 * s) → Bool), A ω ^ e :=
        (Finset.mul_prod_erase (Finset.univ : Finset (Fin (2 * s) → Bool))
          (fun ω => A ω ^ e) (Finset.mem_univ 0)).symm
    _ ≤ A 0 ^ e * 3 := mul_le_mul_of_nonneg_left herase (Real.rpow_nonneg (norm_nonneg _) e)
    _ = 3 * A 0 ^ e := by ring
    _ = 3 * (‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M qL₁ qL₂ qR₁ qR₂) (symIcc N)
          (fun _ => fun y => star (f (y + dH0)) * f (y + dH1))‖) ^ e := by rw [hA0]

end

end Work.Peluse.SwapC
