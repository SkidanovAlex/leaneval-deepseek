import Mathlib.Data.ZMod.Basic
import Submission.Commons.Data.Nat.card_multiples_window_bound

namespace Commons.NumberTheory.CongruenceWindows

open Finset

set_option linter.style.haveILetI false

/-- The number of `n ∈ [N, 2N]` with `n % M = r` equals the number of
`t < N + 1` with `(N + t) % M = r` (translate the window down by `N`). -/
private lemma card_Icc_filter_mod_eq_card_range (N M r : ℕ) :
    ((Finset.Icc N (2 * N)).filter (fun n => n % M = r)).card =
      ((Finset.range (N + 1)).filter (fun t => (N + t) % M = r)).card := by
  classical
  refine Finset.card_bij (fun n _ => n - N) ?_ ?_ ?_
  · intro n hn
    have hnN : N ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hn2N : n ≤ 2 * N := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_range.mpr (by omega)
    · have hnmod : n % M = r := (Finset.mem_filter.mp hn).2
      rw [Nat.add_sub_of_le hnN]
      exact hnmod
  · intro a₁ ha₁ a₂ ha₂ h
    have ha₁N : N ≤ a₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha₁).1).1
    have ha₂N : N ≤ a₂ := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha₂).1).1
    omega
  · intro b hb
    have hb_range : b < N + 1 := by simpa using (Finset.mem_filter.mp hb).1
    refine ⟨N + b, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · have hbmod : (N + b) % M = r := (Finset.mem_filter.mp hb).2
        simpa using hbmod
    · omega

/-- `(N + t) % M = r` iff `t` lies in the residue class `v` (mod `M`), where
`v = (r : ZMod M) - (N : ZMod M)`. -/
private lemma window_modEq_iff_val (N M r t : ℕ) (hM : 1 ≤ M) (hr : r < M) :
    ((N + t) % M = r) ↔ t ≡ ((r : ZMod M) - (N : ZMod M)).val [MOD M] := by
  have hmod : ((N + t) % M = r) ↔ ((N + t : ℕ) : ZMod M) = (r : ZMod M) := by
    rw [ZMod.natCast_eq_natCast_iff]
    change (N + t) % M = r ↔ (N + t) % M = r % M
    rw [Nat.mod_eq_of_lt hr]
  have hshift : ((N + t : ℕ) : ZMod M) = (r : ZMod M) ↔
      (t : ZMod M) = (r : ZMod M) - (N : ZMod M) := by
    rw [eq_sub_iff_add_eq]
    simp [Nat.cast_add, add_comm]
  haveI : NeZero M := ⟨by omega⟩
  let v : ZMod M := (r : ZMod M) - (N : ZMod M)
  have hval : (t : ZMod M) = v ↔ t ≡ v.val [MOD M] := by
    let u : ℕ := v.val
    have hu : (u : ZMod M) = v := by
      dsimp [u]
      exact ZMod.natCast_zmod_val v
    change (t : ZMod M) = v ↔ t ≡ u [MOD M]
    rw [← hu]
    exact ZMod.natCast_eq_natCast_iff t u M
  calc
    (N + t) % M = r ↔ ((N + t : ℕ) : ZMod M) = (r : ZMod M) := hmod
    _ ↔ (t : ZMod M) = (r : ZMod M) - (N : ZMod M) := hshift
    _ ↔ t ≡ ((r : ZMod M) - (N : ZMod M)).val [MOD M] := by
      simpa [v] using hval

/-- `(N + t) % M = r` iff `t ≡ u [MOD M]` for `u` the natural representative of
`(r : ZMod M) - (N : ZMod M)`. -/
private lemma window_modEq_iff {N M r u t : ℕ} (hM : 1 ≤ M) (hr : r < M)
    (hu : u = ((r : ZMod M) - (N : ZMod M)).val) :
    ((N + t) % M = r) ↔ t ≡ u [MOD M] := by
  rw [hu]
  exact window_modEq_iff_val N M r t hM hr

/-- The window count equals `Nat.count` of a fixed residue class below `N + 1`. -/
private lemma card_window_modEq_eq_count {N M r u : ℕ} (hM : 1 ≤ M) (hr : r < M)
    (hu : u = ((r : ZMod M) - (N : ZMod M)).val) :
    ((Finset.Icc N (2 * N)).filter (fun n => n % M = r)).card =
      Nat.count (fun t => t ≡ u [MOD M]) (N + 1) := by
  classical
  rw [card_Icc_filter_mod_eq_card_range]
  rw [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro t ht
  exact window_modEq_iff hM hr hu

theorem card_window_modEq_bounds {N M r : ℕ} (hM : 1 ≤ M) (hr : r < M) :
    |(((Finset.Icc N (2 * N)).filter fun n => n % M = r).card : ℝ) -
        (N : ℝ) / (M : ℝ)| ≤ 2 := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  let u : ℕ := ((r : ZMod M) - (N : ZMod M)).val
  have hu : u = ((r : ZMod M) - (N : ZMod M)).val := rfl
  let c : ℕ := ((Finset.Icc N (2 * N)).filter fun n => n % M = r).card
  have hcount := Nat.count_modEq_card (b := N + 1) (r := M) (hr := by omega) (v := u)
  have hmain : c = (N + 1) / M + if u % M < (N + 1) % M then 1 else 0 := by
    dsimp [c]
    rw [card_window_modEq_eq_count hM hr hu]
    exact hcount
  have hle : c ≤ (N + 1) / M + 1 := by
    have hd : (if u % M < (N + 1) % M then 1 else 0 : ℕ) ≤ 1 := by
      by_cases h : u % M < (N + 1) % M <;> simp [h]
    omega
  have hge : (N + 1) / M ≤ c := by
    have hd : (1 : ℕ) ≤ (if u % M < (N + 1) % M then 1 else 0) + 1 := by omega
    omega
  have hMpos : 0 < (M : ℝ) := by positivity
  have hdivle : (((N + 1) / M : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) / (M : ℝ) := by
    exact_mod_cast (Commons.Data.Nat.card_multiples_nat_div_le_real_div (N + 1) M)
  have hdivlt : ((N + 1 : ℕ) : ℝ) / (M : ℝ) < (((N + 1) / M : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Commons.Data.Nat.card_multiples_real_div_lt_nat_div_add_one (N + 1) M)
  have hsplit : ((N + 1 : ℕ) : ℝ) / (M : ℝ) = (N : ℝ) / (M : ℝ) + (1 : ℝ) / (M : ℝ) := by
    norm_num
    field_simp [hMpos.ne']
  have hMle : (1 : ℝ) / (M : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hMpos]
    rw [one_mul]
    exact_mod_cast hM
  have hMge : (0 : ℝ) ≤ (1 : ℝ) / (M : ℝ) := by positivity
  have hleR : (c : ℝ) ≤ (N : ℝ) / (M : ℝ) + 2 := by
    have h1 : (c : ℝ) ≤ (((N + 1) / M : ℕ) : ℝ) + 1 := by exact_mod_cast hle
    have hstep : ((N + 1 : ℕ) : ℝ) / (M : ℝ) ≤ (N : ℝ) / (M : ℝ) + 1 := by
      rw [hsplit]
      nlinarith
    linarith
  have hgeR : (N : ℝ) / (M : ℝ) - 2 ≤ (c : ℝ) := by
    have h1 : (((N + 1) / M : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast hge
    have hq : ((N + 1 : ℕ) : ℝ) / (M : ℝ) - 1 ≤ (((N + 1) / M : ℕ) : ℝ) := by linarith
    have hN : (N : ℝ) / (M : ℝ) - 1 ≤ ((N + 1 : ℕ) : ℝ) / (M : ℝ) - 1 := by
      rw [hsplit]
      nlinarith
    linarith
  have hz : |(c : ℝ) - (N : ℝ) / (M : ℝ)| ≤ 2 := by
    rw [abs_le]
    constructor
    · nlinarith [hgeR]
    · nlinarith [hleR]
  simpa [c] using hz

end Commons.NumberTheory.CongruenceWindows