import Mathlib
import Submission.Work.Params.basic
import Submission.Work.Params.defs

/-!
# `rpar` dominates the constants of the `sᵢ` construction

For `n ≥ n₁` the parameter `r = rpar n = 2^{⌈k_T/d⌉}` is so large that it dominates the constants
`8d(FQ + Fd + 1)` and `4d(1 + 2FQ + 2Fd)` appearing in the window conditions for the `sᵢ`, where
`F = Ffac = (d-1)!` and `Q = Qall`.  We also record the elementary bounds `1 ≤ k_T`,
`1 ≤ ⌈k_T/d⌉` and `d' = d⌈k_T/d⌉ - k_T ≤ d`.

## Design (important, see `DESIGN.md`)

The kernel's built-in evaluator for `Nat.pow` *refuses* to evaluate closed powers whose exponent
does not fit in 32 bits, and it *does* try to do so whenever `isDefEq` compares two closed `Nat`
terms (in particular it does so for every `Nat.pow_le_pow_right` application whose exponents are
concrete).  Since `n₁ = 2^(2^40·8·d)` has such an exponent, all the arguments are formulated with
*symbolic* exponents:

* `Ffac_le_pow`, `Qall_le_pow` bound `Ffac`, `Qall` by `2^E` for an arbitrary `E`;
* `bound1`, `bound2` bound the two constants by `2^K` for an arbitrary `K ≥ 2^27`;
* `kT_ge_aux` turns `n₁ ≤ n` into `k_T n ≥ k + 1` for an arbitrary `k` with `2k+2 ≤ E`
  (where `E` is related to `n₁` by the hypothesis `n₁ = 2^E`);
* `krpar_ge_aux` converts that into `2^27 ≤ krpar n`.

The only place where a concrete huge exponent has to be touched is the definitional identity
`n₁ = 2^(2^40·8·d)`.  In the main proof it is stated as `n1 = 2^E` where `E` is a *local* `let`
for `2^40·8·d`: from the kernel's point of view the exponent is then a variable, so the kernel
never has to evaluate a concrete `Nat.pow` with a huge exponent (which it refuses to do).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 500000

namespace Work.Params

open HvdH

/-! ## Elementary power arithmetic with symbolic exponents -/

theorem aux_succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    omega

theorem aux_pow_plus_one_le (x : ℕ) (hx : 1 ≤ x) : x + 1 ≤ 2 * x := by omega

/-- Monotonicity of `2 ^ ·`, stated with variable exponents (proved by induction so that the
kernel never has to evaluate a concrete power). -/
theorem pow_two_mono {a b : ℕ} (h : a ≤ b) : (2:ℕ) ^ a ≤ 2 ^ b := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  subst hd
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    calc (2:ℕ) ^ a ≤ 2 ^ (a + d) := ih
      _ ≤ 2 ^ (a + d) * 2 := by
            have := Nat.one_le_two_pow (n := a + d)
            omega
      _ = 2 ^ (a + d + 1) := (pow_succ 2 (a + d)).symm
      _ = 2 ^ (a + (d + 1)) := by congr 1

/-- For `x ≥ 2k+2` one has `2^k (x+1) ≤ 2^x`. -/
theorem aux_two_pow_mul_succ_le (k x : ℕ) (h : 2 * k + 2 ≤ x) : 2 ^ k * (x + 1) ≤ 2 ^ x := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  induction j with
  | zero =>
    have h1 : 2 * k + 3 ≤ 2 ^ (k + 2) := by
      have := aux_succ_le_two_pow k
      calc 2 * k + 3 ≤ 4 * (k + 1) := by omega
        _ ≤ 4 * 2 ^ k := by nlinarith [this]
        _ = 2 ^ (k + 2) := by ring
    calc 2 ^ k * (2 * k + 2 + 0 + 1) = 2 ^ k * (2 * k + 3) := by ring
      _ ≤ 2 ^ k * 2 ^ (k + 2) := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (k + (k + 2)) := by rw [← pow_add]
      _ = 2 ^ (2 * k + 2 + 0) := by ring_nf
  | succ j ih =>
    have h2 : 2 ^ k ≤ 2 ^ (2 * k + 2 + j) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have ih' := ih (by omega)
    calc 2 ^ k * (2 * k + 2 + (j + 1) + 1)
        = 2 ^ k * (2 * k + 2 + j + 1) + 2 ^ k := by ring
      _ ≤ 2 ^ (2 * k + 2 + j) + 2 ^ (2 * k + 2 + j) := Nat.add_le_add ih' h2
      _ = 2 ^ (2 * k + 2 + (j + 1)) := by ring

/-- `clog 2 n ≤ n / 2^k` for `n ≥ 2^{2k+2}`. -/
theorem aux_clog_le_div_pow (n k : ℕ) (h : 2 ^ (2 * k + 2) ≤ n) :
    Nat.clog 2 n ≤ n / 2 ^ k := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  set q := n / 2 ^ k with hqdef
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hq1 : 2 ^ (k + 2) ≤ q := by
    have h' : 2 ^ (k + 2) * 2 ^ k ≤ n := by
      calc 2 ^ (k + 2) * 2 ^ k = 2 ^ (k + 2 + k) := (pow_add _ _ _).symm
        _ = 2 ^ (2 * k + 2) := by ring_nf
        _ ≤ n := h
    have := Nat.div_le_div_right h' (c := 2 ^ k)
    rwa [Nat.mul_div_cancel _ hpos] at this
  have hq2 : 2 * k + 2 ≤ q := by
    have h1 := aux_succ_le_two_pow (k + 1)
    have h2 : 2 ^ (k + 1) ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 * k + 2 = 2 * (k + 1) := by ring
      _ ≤ 2 * 2 ^ (k+1) := by omega
      _ = 2 ^ (k + 2) := by ring
      _ ≤ q := hq1
  have hq' : 2 ^ k * (q + 1) ≤ 2 ^ q := aux_two_pow_mul_succ_le k q hq2
  have hn : n < 2 ^ k * (q + 1) := by
    have hdm : 2 ^ k * (n / 2 ^ k) + n % 2 ^ k = n := Nat.div_add_mod n (2 ^ k)
    have hmod : n % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpos
    calc n = 2 ^ k * (n / 2 ^ k) + n % 2 ^ k := hdm.symm
      _ = 2 ^ k * q + n % 2 ^ k := by rw [hqdef]
      _ < 2 ^ k * q + 2 ^ k := by omega
      _ = 2 ^ k * (q + 1) := by ring
  exact le_of_lt (lt_of_lt_of_le hn hq')

/-! ## Bounds for `Ffac` and `Qall`, with symbolic exponents -/

theorem Ffac_le_two_pow : Ffac ≤ 2 ^ 19008 := by
  have hD1 : HvdH.D - 1 = 1728 := Work.Params.D_sub
  unfold Work.Params.Ffac
  rw [hD1]
  calc Nat.factorial 1728 ≤ 1728 ^ 1728 := Nat.factorial_le_pow 1728
    _ ≤ (2 ^ 11) ^ 1728 := Nat.pow_le_pow_left (by norm_num) 1728
    _ = 2 ^ (11 * 1728) := (pow_mul 2 11 1728).symm
    _ = 2 ^ 19008 := by norm_num

theorem Ffac_le_pow (E : ℕ) (hE : 19008 ≤ E) : Ffac ≤ 2 ^ E :=
  le_trans Ffac_le_two_pow (pow_two_mono hE)

theorem FfacD_le_pow : Ffac * HvdH.D ≤ 2 ^ 19019 := by
  have he : Ffac * HvdH.D = Ffac * 1729 := rfl
  rw [he]
  calc Ffac * 1729 ≤ 2 ^ 19008 * 1729 := Nat.mul_le_mul_right 1729 Ffac_le_two_pow
    _ ≤ 2 ^ 19008 * 2 ^ 11 := Nat.mul_le_mul_left _ (by norm_num)
    _ = 2 ^ (19008 + 11) := (pow_add 2 19008 11).symm
    _ = 2 ^ 19019 := by norm_num

/-- `2 F 1728 + 1 ≤ 2^19021`. -/
theorem A_le_two_pow : 2 * Ffac * 1728 + 1 ≤ 2 ^ 19021 := by
  have h1 : 2 * Ffac * 1728 ≤ 2 ^ 19020 := by
    calc 2 * Ffac * 1728 = 3456 * Ffac := by ring
      _ ≤ 3456 * 2 ^ 19008 := Nat.mul_le_mul_left _ Ffac_le_two_pow
      _ ≤ 2 ^ 12 * 2 ^ 19008 := Nat.mul_le_mul_right _ (by norm_num)
      _ = 2 ^ (12 + 19008) := (pow_add 2 12 19008).symm
      _ = 2 ^ 19020 := by norm_num
  calc 2 * Ffac * 1728 + 1 ≤ 2 ^ 19020 + 1 := Nat.add_le_add_right h1 1
    _ ≤ 2 * 2 ^ 19020 := aux_pow_plus_one_le _ (Nat.one_le_two_pow (n := 19020))
    _ = 2 ^ 19021 := (pow_succ' 2 19020).symm

/-- `Q = ∏ (2Fk+1)(2Fk-1) ≤ 2^E` for any `E ≥ 19021·3456`. -/
theorem Qall_le_pow (E : ℕ) (hE : 19021 * 3456 ≤ E) : Qall ≤ 2 ^ E := by
  have hb1 : 19021 ≤ E / 3456 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3456)]
    exact hE
  have hA : 2 * Ffac * 1728 + 1 ≤ 2 ^ (E / 3456) :=
    le_trans A_le_two_pow (pow_two_mono hb1)
  unfold Work.Params.Qall
  have hlen : (List.range (HvdH.D - 1)).length = 1728 := by
    rw [List.length_range, Work.Params.D_sub]
  have hmem : ∀ x ∈ (List.range (HvdH.D - 1)).map
        (fun j => (2 * Ffac * (j + 1) + 1) * (2 * Ffac * (j + 1) - 1)),
      x ≤ (2 ^ (E / 3456)) ^ 2 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
    have hjlt : j < 1728 := by
      have := List.mem_range.mp hj
      rwa [Work.Params.D_sub] at this
    have hjle : j + 1 ≤ 1728 := by omega
    have h1 : 2 * Ffac * (j + 1) + 1 ≤ 2 ^ (E / 3456) := by
      have h2 : 2 * Ffac * (j + 1) + 1 ≤ 2 * Ffac * 1728 + 1 := by
        have h3 : 2 * Ffac * (j + 1) ≤ 2 * Ffac * 1728 := Nat.mul_le_mul_left _ hjle
        omega
      omega
    have h2 : 2 * Ffac * (j + 1) - 1 ≤ 2 ^ (E / 3456) := by omega
    calc (2 * Ffac * (j + 1) + 1) * (2 * Ffac * (j + 1) - 1)
        ≤ 2 ^ (E / 3456) * 2 ^ (E / 3456) := Nat.mul_le_mul h1 h2
      _ = (2 ^ (E / 3456)) ^ 2 := (pow_two _).symm
  calc (List.map (fun j => (2 * Ffac * (j + 1) + 1) * (2 * Ffac * (j + 1) - 1))
        (List.range (HvdH.D - 1))).prod
      ≤ ((2 ^ (E / 3456)) ^ 2) ^ (List.map _ (List.range (HvdH.D - 1))).length :=
        List.prod_le_pow_length _ _ hmem
    _ = ((2 ^ (E / 3456)) ^ 2) ^ 1728 := by rw [List.length_map, hlen]
    _ = (2 ^ (E / 3456)) ^ (2 * 1728) := (pow_mul (2 ^ (E / 3456)) 2 1728).symm
    _ = (2 ^ (E / 3456)) ^ 3456 := by norm_num
    _ = 2 ^ ((E / 3456) * 3456) := (pow_mul 2 (E / 3456) 3456).symm
    _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.div_mul_le_self E 3456)

/-! ## The two constant bounds, with symbolic exponent -/

theorem bound1 (K : ℕ) (hK : 2 ^ 27 ≤ K) :
    8 * HvdH.D * (Ffac * Qall + Ffac * HvdH.D + 1) ≤ 2 ^ K := by
  have hKbig : 131511168 ≤ K := le_trans (by norm_num : 131511168 ≤ 2 ^ 27) hK
  set A := K / 2 with hAdef
  have hA_ge : 65755584 ≤ A := by rw [hAdef]; omega
  have hA19008 : 19008 ≤ A := by omega
  have hQall : Qall ≤ 2 ^ (A - 19008) := Qall_le_pow (A - 19008) (by omega)
  have hFQ : Ffac * Qall ≤ 2 ^ A := by
    calc Ffac * Qall ≤ 2 ^ 19008 * 2 ^ (A - 19008) := Nat.mul_le_mul Ffac_le_two_pow hQall
      _ = 2 ^ (19008 + (A - 19008)) := (pow_add 2 19008 (A - 19008)).symm
      _ = 2 ^ A := by rw [Nat.add_sub_of_le hA19008]
  have hFD : Ffac * HvdH.D ≤ 2 ^ A :=
    le_trans FfacD_le_pow (pow_two_mono (by omega))
  have hsum : Ffac * Qall + Ffac * HvdH.D + 1 ≤ 2 ^ (A + 2) := by
    have h1 : Ffac * Qall + Ffac * HvdH.D ≤ 2 ^ A + 2 ^ A := Nat.add_le_add hFQ hFD
    have h2 : (2:ℕ) ^ A + 2 ^ A = 2 ^ (A + 1) := by
      rw [← two_mul]
      exact (pow_succ' 2 A).symm
    calc Ffac * Qall + Ffac * HvdH.D + 1 ≤ (2 ^ A + 2 ^ A) + 1 := Nat.add_le_add_right h1 1
      _ = 2 ^ (A + 1) + 1 := by rw [h2]
      _ ≤ 2 * 2 ^ (A + 1) := aux_pow_plus_one_le _ (Nat.one_le_two_pow)
      _ = 2 ^ (A + 2) := (pow_succ' 2 (A + 1)).symm
  calc 8 * HvdH.D * (Ffac * Qall + Ffac * HvdH.D + 1)
      ≤ 8 * HvdH.D * 2 ^ (A + 2) := Nat.mul_le_mul_left _ hsum
    _ ≤ 2 ^ 14 * 2 ^ (A + 2) := Nat.mul_le_mul_right _ (by norm_num [HvdH.D] : 8 * HvdH.D ≤ 2 ^ 14)
    _ = 2 ^ (14 + (A + 2)) := (pow_add 2 14 (A + 2)).symm
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by rw [hAdef]; omega)

theorem bound2 (K : ℕ) (hK : 2 ^ 27 ≤ K) :
    4 * HvdH.D * (1 + 2 * Ffac * Qall + 2 * Ffac * HvdH.D) ≤ 2 ^ K := by
  have hKbig : 131511168 ≤ K := le_trans (by norm_num : 131511168 ≤ 2 ^ 27) hK
  set A := K / 2 with hAdef
  have hA_ge : 65755584 ≤ A := by rw [hAdef]; omega
  have hA19008 : 19008 ≤ A := by omega
  have hQall : Qall ≤ 2 ^ (A - 19008) := Qall_le_pow (A - 19008) (by omega)
  have hFQ : Ffac * Qall ≤ 2 ^ A := by
    calc Ffac * Qall ≤ 2 ^ 19008 * 2 ^ (A - 19008) := Nat.mul_le_mul Ffac_le_two_pow hQall
      _ = 2 ^ (19008 + (A - 19008)) := (pow_add 2 19008 (A - 19008)).symm
      _ = 2 ^ A := by rw [Nat.add_sub_of_le hA19008]
  have hFD : Ffac * HvdH.D ≤ 2 ^ A :=
    le_trans FfacD_le_pow (pow_two_mono (by omega))
  have hsum : 1 + 2 * Ffac * Qall + 2 * Ffac * HvdH.D ≤ 2 ^ (A + 3) := by
    have h2FQ : 2 * Ffac * Qall ≤ 2 ^ (A + 1) := by
      calc 2 * Ffac * Qall = 2 * (Ffac * Qall) := by ring
        _ ≤ 2 * 2 ^ A := Nat.mul_le_mul_left _ hFQ
        _ = 2 ^ (A + 1) := (pow_succ' 2 A).symm
    have h2FD : 2 * Ffac * HvdH.D ≤ 2 ^ (A + 1) := by
      calc 2 * Ffac * HvdH.D = 2 * (Ffac * HvdH.D) := by ring
        _ ≤ 2 * 2 ^ A := Nat.mul_le_mul_left _ hFD
        _ = 2 ^ (A + 1) := (pow_succ' 2 A).symm
    have h1 : 1 + 2 * Ffac * Qall + 2 * Ffac * HvdH.D
        ≤ 2 ^ (A + 1) + 2 ^ (A + 1) + 2 ^ (A + 1) := by
      have hone : (1:ℕ) ≤ 2 ^ (A + 1) := Nat.one_le_two_pow
      omega
    have h4 : (4:ℕ) * 2 ^ (A + 1) = 2 ^ (A + 3) := by
      rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega
    calc 1 + 2 * Ffac * Qall + 2 * Ffac * HvdH.D
        ≤ 2 ^ (A + 1) + 2 ^ (A + 1) + 2 ^ (A + 1) := h1
      _ ≤ 4 * 2 ^ (A + 1) := by omega
      _ = 2 ^ (A + 3) := h4
  calc 4 * HvdH.D * (1 + 2 * Ffac * Qall + 2 * Ffac * HvdH.D)
      ≤ 4 * HvdH.D * 2 ^ (A + 3) := Nat.mul_le_mul_left _ hsum
    _ ≤ 2 ^ 13 * 2 ^ (A + 3) := Nat.mul_le_mul_right _ (by norm_num [HvdH.D] : 4 * HvdH.D ≤ 2 ^ 13)
    _ = 2 ^ (13 + (A + 3)) := (pow_add 2 13 (A + 3)).symm
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by rw [hAdef]; omega)

/-! ## Lower bounds for `k_T` and `k_r` -/

/-- If `n₁ = 2^E` and `2k+2 ≤ E` then `k_T n ≥ k + 1` for every `n ≥ n₁`. -/
theorem kT_ge_aux (E k : ℕ) (hE : n1 = 2 ^ E) (n : ℕ) (hn : n1 ≤ n)
    (h_exp : 2 * k + 2 ≤ E) : k + 1 ≤ HvdH.kTpar n := by
  have hnbig : 2 ^ (2 * k + 2) ≤ n := by
    have h1 : 2 ^ (2 * k + 2) ≤ 2 ^ E := pow_two_mono h_exp
    exact le_trans h1 (le_trans (le_of_eq hE.symm) hn)
  have hb_le : HvdH.bpar n ≤ n / 2 ^ k := aux_clog_le_div_pow n k hnbig
  have hn_gt1 : 1 < n := by
    have h1 : (2:ℕ) ^ 1 ≤ 2 ^ (2 * k + 2) := pow_two_mono (by omega)
    omega
  have hbpos : 0 < HvdH.bpar n := by
    rw [HvdH.bpar]
    exact Nat.clog_pos (by norm_num : 1 < 2) hn_gt1
  have hbk : HvdH.bpar n * 2 ^ k ≤ n := (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).mp hb_le
  have hb_le_n : HvdH.bpar n ≤ n := le_trans hb_le (Nat.div_le_self n _)
  have hm_ge : 2 ^ k + 1 ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n := by
    have h1 : (4 * n) / HvdH.bpar n ≤ (4 * n + HvdH.bpar n - 1) / HvdH.bpar n :=
      Nat.div_le_div_right (by omega)
    have h2 : 2 ^ k + 1 ≤ (4 * n) / HvdH.bpar n := by
      rw [Nat.le_div_iff_mul_le hbpos]
      have hmul : (2 ^ k + 1) * HvdH.bpar n = HvdH.bpar n * 2 ^ k + HvdH.bpar n := by ring
      rw [hmul]
      omega
    exact le_trans h2 h1
  have hlt : k < HvdH.kTpar n := by
    rw [HvdH.kTpar, Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) hm_ge
  omega

/-- `⌈k_T/d⌉ ≥ 2^27` as soon as `k_T ≥ 2^38 - 2`. -/
theorem krpar_ge_aux (n : ℕ) (hkT : 2 ^ 38 - 2 ≤ HvdH.kTpar n) : 2 ^ 27 ≤ krpar n := by
  have h1 : HvdH.kTpar n / HvdH.D ≤ krpar n := by
    unfold Work.Params.krpar
    apply Nat.div_le_div_right
    have hD1 : 1 ≤ HvdH.D := by norm_num [HvdH.D]
    omega
  have h2 : 2 ^ 27 ≤ HvdH.kTpar n / HvdH.D := by
    have h3 : (2:ℕ) ^ 27 ≤ (2 ^ 38 - 2) / HvdH.D := by
      rw [Nat.le_div_iff_mul_le (by norm_num [HvdH.D] : 0 < HvdH.D)]
      norm_num [HvdH.D]
    exact le_trans h3 (Nat.div_le_div_right hkT)
  exact le_trans h2 h1

/-! ## The main statement -/

theorem rparbig (n : ℕ) (hn : Work.Params.n1 ≤ n) :
    8 * HvdH.D * (Work.Params.Ffac * Work.Params.Qall + Work.Params.Ffac * HvdH.D + 1) ≤ HvdH.rpar n ∧
    4 * HvdH.D * (1 + 2 * Work.Params.Ffac * Work.Params.Qall + 2 * Work.Params.Ffac * HvdH.D) ≤ HvdH.rpar n ∧
    1 ≤ Work.Params.krpar n ∧ 1 ≤ HvdH.kTpar n ∧ Work.Params.dpar n ≤ HvdH.D := by
  have h_exp : 2 * (2 ^ 38 - 3) + 2 ≤ 2 ^ 40 * 8 * D := by norm_num [HvdH.D]
  let E : ℕ := 2 ^ 40 * 8 * D
  have hE : n1 = 2 ^ E := rfl
  have hkT : 2 ^ 38 - 2 ≤ HvdH.kTpar n := kT_ge_aux E (2 ^ 38 - 3) hE n hn h_exp
  have hkr : 2 ^ 27 ≤ krpar n := krpar_ge_aux n hkT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact bound1 (krpar n) hkr
  · exact bound2 (krpar n) hkr
  · exact le_trans (by norm_num : 1 ≤ 2 ^ 27) hkr
  · exact le_trans (by norm_num : 1 ≤ 2 ^ 38 - 2) hkT
  · unfold Work.Params.dpar Work.Params.krpar
    have hD1 : 1 ≤ HvdH.D := by norm_num [HvdH.D]
    have h := Nat.div_mul_le_self (HvdH.kTpar n + HvdH.D - 1) HvdH.D
    rw [Nat.mul_comm] at h
    omega

end Work.Params
