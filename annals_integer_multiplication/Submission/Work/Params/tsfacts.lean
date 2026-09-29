import Mathlib
import Submission.Work.Params.basic
import Submission.Work.Params.defs

/-!
# Facts about the list `tsPar n` of transform sizes (paper §5.1)

`tsPar n` is the ascending list of the `D` transform sizes `t₁ ≤ … ≤ t_D`, namely
`d' = dpar n` copies of `r/2` followed by `D - d'` copies of `r = rpar n`, where
`r = 2^{kr}`, `kr = krpar n = ⌈kT/d⌉`, `d' = d·kr - kT ∈ [0,d)` and `T = 2^{kT} = Tpar n`.

The main work is the combinatorial identity `∏ tᵢ = r^{d'} · (r/2)^{D-d'} = 2^{kT}`.
-/

set_option autoImplicit false

namespace Work.Params

open HvdH

/-- `a ≤ b · ⌈a/b⌉` for `b > 0`, in the "add `b-1` then divide" incarnation of the ceiling. -/
theorem ts_le_mul_div_add (a b : ℕ) (hb : 0 < b) : a ≤ b * ((a + b - 1) / b) := by
  have h := Nat.div_add_mod (a + b - 1) b
  have hlt := Nat.mod_lt (a + b - 1) hb
  omega

/-- `(a - b) + (c - a) = c - b` for `b ≤ a ≤ c`. -/
theorem ts_nat_add_sub_sub_cancel {a b c : ℕ} (h1 : b ≤ a) (h2 : a ≤ c) :
    (a - b) + (c - a) = c - b := by
  omega

/-- `kT ≤ d · ⌈kT/d⌉`, i.e. `T ≤ r^d`. -/
theorem ts_kT_le_mul_kr (n : ℕ) : kTpar n ≤ D * krpar n := by
  have hb : 0 < D := by decide
  unfold krpar
  exact ts_le_mul_div_add (kTpar n) D hb

theorem ts_rpar_eq (n : ℕ) : rpar n = 2 ^ krpar n := rfl

theorem ts_Tpar_eq (n : ℕ) : Tpar n = 2 ^ kTpar n := rfl

/-- `r = 2 · 2^{kr-1}` when `kr ≥ 1`. -/
theorem ts_rpar_eq_two_mul (n : ℕ) (hk : 1 ≤ krpar n) : rpar n = 2 * 2 ^ (krpar n - 1) := by
  have hkr : krpar n = (krpar n - 1) + 1 := (Nat.sub_add_cancel hk).symm
  conv_lhs => rw [ts_rpar_eq, hkr]
  rw [Nat.pow_succ']

/-- `r/2 = 2^{kr-1}` when `kr ≥ 1`. -/
theorem ts_rpar_div_two (n : ℕ) (hk : 1 ≤ krpar n) : rpar n / 2 = 2 ^ (krpar n - 1) := by
  rw [ts_rpar_eq_two_mul n hk, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]

/-- `2 · (r/2) = r` when `kr ≥ 1`. -/
theorem ts_two_mul_rpar_div_two (n : ℕ) (hk : 1 ≤ krpar n) : 2 * (rpar n / 2) = rpar n := by
  rw [ts_rpar_div_two n hk]
  exact (ts_rpar_eq_two_mul n hk).symm

/-- `tsPar n` is `d'` copies of `r/2` followed by `D - d'` copies of `r`, when `d' ≤ D`. -/
theorem ts_tsPar_eq (n : ℕ) (hd : dpar n ≤ D) :
    tsPar n = List.replicate (dpar n) (rpar n / 2) ++ List.replicate (D - dpar n) (rpar n) := by
  have h1 : (List.range (dpar n)).map (fun k => if k < dpar n then rpar n / 2 else rpar n)
          = List.replicate (dpar n) (rpar n / 2) := by
    have h : ∀ k ∈ List.range (dpar n),
        (fun k => if k < dpar n then rpar n / 2 else rpar n) k = rpar n / 2 := by
      intro k hk; rw [List.mem_range] at hk; simp [hk]
    calc (List.range (dpar n)).map (fun k => if k < dpar n then rpar n / 2 else rpar n)
        = (List.range (dpar n)).map (fun _ => rpar n / 2) := List.map_congr_left h
      _ = List.replicate (List.range (dpar n)).length (rpar n / 2) := List.map_const'
      _ = List.replicate (dpar n) (rpar n / 2) := by rw [List.length_range]
  have h2 : (List.map (fun x => dpar n + x) (List.range (D - dpar n))).map
        (fun k => if k < dpar n then rpar n / 2 else rpar n)
      = List.replicate (D - dpar n) (rpar n) := by
    have h : ∀ k ∈ List.map (fun x => dpar n + x) (List.range (D - dpar n)),
        (fun k => if k < dpar n then rpar n / 2 else rpar n) k = rpar n := by
      intro k hk
      rw [List.mem_map] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      rw [List.mem_range] at hx
      simp [show ¬ (dpar n + x < dpar n) by omega]
    calc (List.map (fun x => dpar n + x) (List.range (D - dpar n))).map
            (fun k => if k < dpar n then rpar n / 2 else rpar n)
        = (List.map (fun x => dpar n + x) (List.range (D - dpar n))).map (fun _ => rpar n) :=
            List.map_congr_left h
      _ = List.replicate (List.map (fun x => dpar n + x) (List.range (D - dpar n))).length
            (rpar n) := List.map_const'
      _ = List.replicate (D - dpar n) (rpar n) := by rw [List.length_map, List.length_range]
  unfold tsPar
  conv_lhs => rw [← Nat.add_sub_of_le hd]
  rw [List.range_add, List.map_append, h1, h2]

/-- Exponentiation identity behind `∏ tᵢ = T`: `(kr-1)·d' + kr·(d-d') = kT`. -/
theorem ts_exp_identity (n : ℕ) (hk : 1 ≤ krpar n) (hd : dpar n ≤ D) :
    (krpar n - 1) * dpar n + krpar n * (D - dpar n) = kTpar n := by
  have hkle : kTpar n ≤ D * krpar n := ts_kT_le_mul_kr n
  have hdef : dpar n = D * krpar n - kTpar n := rfl
  have hE1 : (krpar n - 1) * dpar n = krpar n * dpar n - dpar n := by
    rw [Nat.sub_mul, one_mul]
  have hE2 : krpar n * (D - dpar n) = krpar n * D - krpar n * dpar n :=
    Nat.mul_sub_left_distrib _ _ _
  rw [hE1, hE2]
  have h1 : dpar n ≤ krpar n * dpar n := Nat.le_mul_of_pos_left (n := krpar n) (dpar n) (by omega)
  have h2 : krpar n * dpar n ≤ krpar n * D := Nat.mul_le_mul_left (n := dpar n) (m := D) (krpar n) hd
  rw [ts_nat_add_sub_sub_cancel h1 h2, Nat.mul_comm (krpar n) D]
  have h5 : dpar n + kTpar n = D * krpar n := by rw [hdef]; omega
  omega

theorem tsfacts (n : ℕ) (hk : 1 ≤ Work.Params.krpar n) (hd : Work.Params.dpar n ≤ HvdH.D) :
    (Work.Params.tsPar n).length = HvdH.D ∧
    (Work.Params.tsPar n).Pairwise (fun a b => a ≤ b) ∧
    (Work.Params.tsPar n).prod = HvdH.Tpar n ∧
    (∀ t ∈ Work.Params.tsPar n, t = HvdH.rpar n ∨ 2 * t = HvdH.rpar n) ∧
    (∀ i < HvdH.D, (Work.Params.tsPar n).getD i 0 = (if i < Work.Params.dpar n then HvdH.rpar n / 2 else HvdH.rpar n)) := by
  have hts := ts_tsPar_eq n hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hts, List.length_append, List.length_replicate, List.length_replicate]
    omega
  · rw [hts, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_replicate]; exact Or.inr (le_refl _)
    · rw [List.pairwise_replicate]; exact Or.inr (le_refl _)
    · intro x hx y hy
      rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
      exact Nat.div_le_self _ _
  · rw [hts, List.prod_append, List.prod_replicate, List.prod_replicate]
    rw [ts_rpar_div_two n hk, ts_rpar_eq, ts_Tpar_eq]
    rw [← pow_mul, ← pow_mul, ← pow_add, ts_exp_identity n hk hd]
  · intro t ht
    rw [hts, List.mem_append] at ht
    rcases ht with ht | ht
    · right; rw [List.eq_of_mem_replicate ht]; exact ts_two_mul_rpar_div_two n hk
    · left; exact List.eq_of_mem_replicate ht
  · intro i hi
    have hlen : i < ((List.range D).map (fun k => if k < dpar n then rpar n / 2 else rpar n)).length := by
      rw [List.length_map, List.length_range]; exact hi
    show ((List.range D).map (fun k => if k < dpar n then rpar n / 2 else rpar n)).getD i 0
        = (if i < dpar n then rpar n / 2 else rpar n)
    rw [List.getD_eq_getElem _ 0 hlen, List.getElem_map, List.getElem_range]

end Work.Params
