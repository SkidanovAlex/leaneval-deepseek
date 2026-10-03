import Mathlib
import Submission.Work.FIArea2.Tsum_odd_defs
import Submission.Work.FIArea2.ram_primepow_exact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Auxiliary computations for `uvSum_eq_ramSum` -/

/-- `p^m · [p^m ∣ c]`, the value of the geometric sum `T (p^m) c` (`uvPPow_eq_T`). -/
private def uvPPow (p c : ℕ) (m : ℕ) : ℂ := (p : ℂ) ^ m * (if p ^ m ∣ c then 1 else 0)

private lemma uvPPow_eq_T {p : ℕ} (hp : p.Prime) (c m : ℕ) :
    uvPPow p c m = T (p ^ m) (c : ℤ) := by
  rw [T_eq (p ^ m) (Nat.one_le_pow m p hp.pos) (c : ℤ)]
  unfold uvPPow
  by_cases h : p ^ m ∣ c
  · rw [if_pos h, if_pos (by exact_mod_cast h), Nat.cast_pow, mul_one]
  · rw [if_neg h, if_neg (fun hh => h (by exact_mod_cast hh)), mul_zero]

private lemma uvPPow_zero (p c : ℕ) : uvPPow p c 0 = 1 := by
  unfold uvPPow
  simp

private lemma ram_one (c : ℤ) : ram 1 c = 1 := by
  unfold ram
  rw [show (Finset.Icc 1 1).filter (fun η => Nat.Coprime η 1) = {1} by
    ext η
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, by decide⟩]
  rw [Finset.sum_singleton]
  simp [E_int]

private lemma ram_term_eq {p : ℕ} (hp : p.Prime) (c : ℤ) (j : ℕ) :
    T (p ^ j) c - (if j = 0 then 0 else T (p ^ (j - 1)) c) = ram (p ^ j) c := by
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    rw [if_pos rfl, sub_zero, pow_zero, T_eq 1 le_rfl c, ram_one]
    simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [if_neg (by omega : ¬ (k + 1 = 0)), show k + 1 - 1 = k from by omega]
    have h := ram_primepow_exact p (k + 1) hp (by omega) c
    rw [show k + 1 - 1 = k from by omega] at h
    rw [← T_eq (p ^ (k + 1)) (Nat.one_le_pow (k + 1) p hp.pos) c,
        ← T_eq (p ^ k) (Nat.one_le_pow k p hp.pos) c] at h
    exact h.symm

private lemma uvRam_ppow {p : ℕ} (hp : p.Prime) (c : ℕ) (j : ℕ) :
    uvPPow p c j - (if j = 0 then 0 else uvPPow p c (j - 1)) = ram (p ^ j) (c : ℤ) := by
  by_cases h0 : j = 0
  · subst h0
    rw [if_pos rfl, sub_zero, uvPPow_zero, pow_zero, ram_one]
  · have h := ram_term_eq (p := p) hp (c : ℤ) j
    rw [if_neg h0] at h
    rw [uvPPow_eq_T hp c j, if_neg h0, uvPPow_eq_T hp c (j - 1)]
    exact h

/-- `u * v = 0` in `ZMod (p^ν)` says exactly that `v` is divisible by `p^(ν - ordv u)`. -/
private lemma mul_eq_zero_iff {p ν : ℕ} (hp : p.Prime) [NeZero (p ^ ν)] (u v : ZMod (p ^ ν)) :
    u * v = 0 ↔ p ^ (ν - ordv p ν u) ∣ v.val := by
  have hprod : (u * v = 0) ↔ ((p ^ ν : ℕ) : ℤ) ∣ ((u.val * v.val : ℕ) : ℤ) := by
    have h : u * v = (((u.val * v.val : ℕ) : ℤ) : ZMod (p ^ ν)) := by
      rw [Int.cast_natCast, Nat.cast_mul, ZMod.natCast_zmod_val u, ZMod.natCast_zmod_val v]
    rw [h]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  rw [hprod, Int.ofNat_dvd, dvd_iff_le_cval_mul hp le_rfl u.val v.val]
  rw [ordv_val, dvd_iff_le_cval hp (Nat.sub_le ν (cval p ν u.val)) v.val]
  have hc := cval_le p ν u.val
  constructor <;> intro h <;> omega

/-- The `ordv`-fibre sum over `i < ν` is the difference of the two consecutive layer sums. -/
private lemma sum_ordv_eq {p ν i : ℕ} (hp : p.Prime) (hi : i < ν) [NeZero (p ^ ν)]
    (f : ZMod (p ^ ν) → ℂ) :
    (∑ u : ZMod (p ^ ν), if ordv p ν u = i then f u else 0)
      = (∑ u : ZMod (p ^ ν), if p ^ i ∣ u.val then f u else 0)
        - (∑ u : ZMod (p ^ ν), if p ^ (i + 1) ∣ u.val then f u else 0) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have e1 : p ^ i ∣ u.val ↔ i ≤ ordv p ν u := dvd_val_iff_le_ordv hp (le_of_lt hi) u
  have e2 : p ^ (i + 1) ∣ u.val ↔ i + 1 ≤ ordv p ν u := dvd_val_iff_le_ordv hp (by omega) u
  by_cases h1 : p ^ i ∣ u.val
  · have ho1 : i ≤ ordv p ν u := e1.mp h1
    by_cases h2 : p ^ (i + 1) ∣ u.val
    · have ho2 : i + 1 ≤ ordv p ν u := e2.mp h2
      rw [if_neg (by omega : ¬ (ordv p ν u = i)), if_pos h1, if_pos h2]
      ring
    · have ho2 : ¬ (i + 1 ≤ ordv p ν u) := fun h => h2 (e2.mpr h)
      rw [if_pos (by omega : ordv p ν u = i), if_pos h1, if_neg h2, sub_zero]
  · have ho1 : ¬ (i ≤ ordv p ν u) := fun h => h1 (e1.mpr h)
    have h2 : ¬ p ^ (i + 1) ∣ u.val :=
      fun h => ho1 (le_trans (Nat.le_succ i) (e2.mp h))
    rw [if_neg (by omega : ¬ (ordv p ν u = i)), if_neg h1, if_neg h2, sub_zero]

/-- The top `ordv`-fibre (`i = ν`, i.e. `u = 0`) is the layer `p^ν ∣ u.val`. -/
private lemma sum_ordv_eq_nu {p ν : ℕ} (hp : p.Prime) [NeZero (p ^ ν)]
    (f : ZMod (p ^ ν) → ℂ) :
    (∑ u : ZMod (p ^ ν), if ordv p ν u = ν then f u else 0)
      = ∑ u : ZMod (p ^ ν), if p ^ ν ∣ u.val then f u else 0 := by
  refine Finset.sum_congr rfl (fun u _ => ?_)
  have e : p ^ ν ∣ u.val ↔ ν ≤ ordv p ν u := dvd_val_iff_le_ordv hp le_rfl u
  by_cases h : p ^ ν ∣ u.val
  · have ho : ν ≤ ordv p ν u := e.mp h
    rw [if_pos (le_antisymm (ordv_le u) ho), if_pos h]
  · have ho : ¬ (ν ≤ ordv p ν u) := fun hh => h (e.mpr hh)
    rw [if_neg (by omega : ¬ (ordv p ν u = ν)), if_neg h]

/-- Regrouping `Σ_u f u · Q (ν - ordv u)` by the value of `ordv p ν u`. -/
private lemma uvSwap {p ν : ℕ} (_hp : p.Prime) [NeZero (p ^ ν)] (f : ZMod (p ^ ν) → ℂ)
    (Q : ℕ → ℂ) :
    (∑ u : ZMod (p ^ ν), f u * Q (ν - ordv p ν u))
      = ∑ i ∈ Finset.range (ν + 1),
          (∑ u : ZMod (p ^ ν), if ordv p ν u = i then f u else 0) * Q (ν - i) := by
  have hstep : ∀ u : ZMod (p ^ ν),
      Q (ν - ordv p ν u)
        = ∑ i ∈ Finset.range (ν + 1), (if ordv p ν u = i then Q (ν - i) else 0) := by
    intro u
    rw [Finset.sum_eq_single (ordv p ν u)]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg (fun h => hb h.symm)]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (ordv_le u))) h
  calc ∑ u, f u * Q (ν - ordv p ν u)
      = ∑ u, f u * ∑ i ∈ Finset.range (ν + 1),
          (if ordv p ν u = i then Q (ν - i) else 0) :=
        Finset.sum_congr rfl (fun u _ => by rw [hstep u])
    _ = ∑ u, ∑ i ∈ Finset.range (ν + 1),
          f u * (if ordv p ν u = i then Q (ν - i) else 0) :=
        Finset.sum_congr rfl (fun u _ => by rw [Finset.mul_sum])
    _ = ∑ i ∈ Finset.range (ν + 1), ∑ u,
          f u * (if ordv p ν u = i then Q (ν - i) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i ∈ Finset.range (ν + 1),
          (∑ u, if ordv p ν u = i then f u else 0) * Q (ν - i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        by_cases h : ordv p ν u = i
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, zero_mul, mul_zero]

/-- Abel/telescoping identity: a difference-sum in `D` equals a difference-sum in `Q`. -/
private lemma uvAlg (D Q : ℕ → ℂ) (ν : ℕ) :
    (∑ i ∈ Finset.range ν, (D i - D (i + 1)) * Q (ν - i)) + D ν * Q 0
      = ∑ j ∈ Finset.range (ν + 1),
          D j * (Q (ν - j) - (if j = 0 then 0 else Q (ν - j + 1))) := by
  have h2 : (∑ j ∈ Finset.range (ν + 1), D j * (if j = 0 then 0 else Q (ν - j + 1)))
      = ∑ i ∈ Finset.range ν, D (i + 1) * Q (ν - i) := by
    rw [Finset.sum_range_succ' (fun j => D j * (if j = 0 then 0 else Q (ν - j + 1))) ν]
    rw [if_pos rfl, mul_zero, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [if_neg (by omega : ¬ (i + 1 = 0)),
        show ν - (i + 1) + 1 = ν - i from by omega]
  calc (∑ i ∈ Finset.range ν, (D i - D (i + 1)) * Q (ν - i)) + D ν * Q 0
      = (∑ i ∈ Finset.range ν, D i * Q (ν - i))
          - (∑ i ∈ Finset.range ν, D (i + 1) * Q (ν - i)) + D ν * Q 0 := by
        rw [← Finset.sum_sub_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ = (∑ i ∈ Finset.range (ν + 1), D i * Q (ν - i))
          - (∑ i ∈ Finset.range ν, D (i + 1) * Q (ν - i)) := by
        rw [Finset.sum_range_succ, Nat.sub_self]
        ring
    _ = (∑ i ∈ Finset.range (ν + 1), D i * Q (ν - i))
          - (∑ j ∈ Finset.range (ν + 1), D j * (if j = 0 then 0 else Q (ν - j + 1))) := by
        rw [h2]
    _ = ∑ j ∈ Finset.range (ν + 1),
          D j * (Q (ν - j) - (if j = 0 then 0 else Q (ν - j + 1))) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        ring

/-- The layer sums of `Φ (p^ν) (· * c)` over the multiples of `p^i`. -/
private lemma layerVal {p ν : ℕ} (hp : p.Prime) [NeZero (p ^ ν)] (c : ZMod (p ^ ν)) (i : ℕ)
    (hi : i ≤ ν) :
    (∑ z : ZMod (p ^ ν), if p ^ i ∣ z.val then Phi (p ^ ν) (z * c) else 0)
      = uvPPow p c.val (ν - i) := by
  have hp' : NeZero p := ⟨hp.ne_zero⟩
  rw [sum_A_Phi hp hi c, uvPPow_eq_T hp c.val (ν - i)]

/-- **Layer decomposition of the `uv = 0` double sum.**  Splitting `{uv = 0}` into the layers
`{ordv u = i} × {p^(ν-i) ∣ v}` and the point `u = 0` gives, for arbitrary `f, g`,

  `Σ_{uv=0} f u g v = Σ_{i<ν} (D_i - D_{i+1}) Q_{ν-i} + D_ν Q_0`. -/
private lemma uvSum_layers {p ν : ℕ} (hp : p.Prime) (_hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (f g : ZMod (p ^ ν) → ℂ) :
    (∑ u : ZMod (p ^ ν), ∑ v : ZMod (p ^ ν), (if u * v = 0 then f u * g v else 0))
      = (∑ i ∈ Finset.range ν,
            ((∑ u : ZMod (p ^ ν), if p ^ i ∣ u.val then f u else 0)
              - (∑ u : ZMod (p ^ ν), if p ^ (i + 1) ∣ u.val then f u else 0))
              * (∑ v : ZMod (p ^ ν), if p ^ (ν - i) ∣ v.val then g v else 0))
          + (∑ u : ZMod (p ^ ν), if p ^ ν ∣ u.val then f u else 0)
              * (∑ v : ZMod (p ^ ν), if p ^ 0 ∣ v.val then g v else 0) := by
  have h1 : (∑ u : ZMod (p ^ ν), ∑ v : ZMod (p ^ ν), (if u * v = 0 then f u * g v else 0))
      = ∑ u : ZMod (p ^ ν),
          f u * (∑ v : ZMod (p ^ ν), if p ^ (ν - ordv p ν u) ∣ v.val then g v else 0) := by
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    by_cases h : u * v = 0
    · rw [if_pos h, if_pos ((mul_eq_zero_iff hp u v).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((mul_eq_zero_iff hp u v).mpr hh)), mul_zero]
  have h2 : (∑ u : ZMod (p ^ ν),
        f u * (∑ v : ZMod (p ^ ν), if p ^ (ν - ordv p ν u) ∣ v.val then g v else 0))
      = ∑ i ∈ Finset.range (ν + 1),
          (∑ u : ZMod (p ^ ν), if ordv p ν u = i then f u else 0)
            * (∑ v : ZMod (p ^ ν), if p ^ (ν - i) ∣ v.val then g v else 0) :=
    uvSwap hp f (fun j => ∑ v : ZMod (p ^ ν), if p ^ j ∣ v.val then g v else 0)
  have h3 : (∑ i ∈ Finset.range (ν + 1),
          (∑ u : ZMod (p ^ ν), if ordv p ν u = i then f u else 0)
            * (∑ v : ZMod (p ^ ν), if p ^ (ν - i) ∣ v.val then g v else 0))
      = (∑ i ∈ Finset.range ν,
            ((∑ u : ZMod (p ^ ν), if p ^ i ∣ u.val then f u else 0)
              - (∑ u : ZMod (p ^ ν), if p ^ (i + 1) ∣ u.val then f u else 0))
              * (∑ v : ZMod (p ^ ν), if p ^ (ν - i) ∣ v.val then g v else 0))
          + (∑ u : ZMod (p ^ ν), if p ^ ν ∣ u.val then f u else 0)
              * (∑ v : ZMod (p ^ ν), if p ^ 0 ∣ v.val then g v else 0) := by
    rw [Finset.sum_range_succ, sum_ordv_eq_nu hp f, show ν - ν = 0 from Nat.sub_self ν]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [sum_ordv_eq hp hi f]
  exact h1.trans (h2.trans h3)

/-- **Decomposition of the `uv = 0` character sum into Ramanujan sums.**  For `p` prime, `ν ≥ 1`
and `α, β : ZMod (p^ν)`,

  `∑_{uv = 0} Φ (p^ν) (u α + v β) = ∑_{k = 0}^{ν} p^{ν-k} [p^{ν-k} ∣ α.val] · ram (p^k) β.val`.

Route.  Let `A_i := {u : ZMod (p^ν) | p^i ∣ u.val}` be the `i`-th layer of the `p`-adic filtration
(its elements are the `iota p ν i z`, `z : ZMod (p^{ν-i})`; see `Work.FIArea2.iota_val`,
`Work.FIArea2.exists_iota_iff`, `Work.FIArea2.sum_dvd_val`).  The sets
`(A_i \ A_{i+1}) × A_{ν-i}` for `i = 0, …, ν-1`, together with `A_ν × A_0` (note that
`A_ν = A_{ν+1} = {0}`, since `u.val < p^ν`), are pairwise disjoint and cover `{uv = 0}`: if
`u = 0` then `v` is arbitrary; if `u ≠ 0` and `i = ordv p ν u < ν` then `p^i ∣ u.val`,
`p^{i+1} ∤ u.val` and (`uv = 0` gives) `p^{ν-i} ∣ v.val`; conversely `p^i ∣ u.val` and
`p^{ν-i} ∣ v.val` give `uv = 0`.  `Φ` is additive (`Work.FIArea2.Phi_add`), so the sum splits into
products over the layers, and `Work.FIArea2.sum_A_Phi` evaluates them:

  `D_i := ∑_{u ∈ A_i} Φ (p^ν) (u α) = T (p^{ν-i}) α.val = p^{ν-i} [p^{ν-i} ∣ α.val]`  (by `T_eq`),
  `E_j := ∑_{v ∈ A_j} Φ (p^ν) (v β) = T (p^{ν-j}) β.val = p^{ν-j} [p^{ν-j} ∣ β.val]`.

So with `P_m := p^m [p^m ∣ α.val]` and `Q_m := p^m [p^m ∣ β.val]` we get `D_i = P_{ν-i}`,
`E_j = Q_{ν-j}` and

  `∑_{uv=0} Φ (uα+vβ) = ∑_{i=0}^{ν-1} (D_i - D_{i+1}) E_{ν-i} + D_ν E_0
      = ∑_{i=0}^{ν} P_{ν-i} Q_i - ∑_{i=0}^{ν-1} P_{ν-i-1} Q_i
      = ∑_{k=0}^{ν} P_{ν-k} (Q_k - Q_{k-1})`   (`Q_{-1} := 0`),

and `Q_k - Q_{k-1} = ram (p^k) β.val`: for `k ≥ 1` this is the prime-power value
`ram (p^k) c = (if p^k ∣ c then p^k else 0) - (if p^{k-1} ∣ c then p^{k-1} else 0)`, obtained by
writing `ram` as the full geometric sum `T (p^k) c` minus the terms with `p ∣ η`, which reindex to
`T (p^{k-1}) c`, and evaluating both with `T_eq`; for `k = 0`, `ram 1 c = 1` and `Q_0 = 1`.
(The same computation is done inside `Work.FIArea2.ramanujan_primepow` for the *bound* on `ram`
at prime powers; its helper `ram_pp_decomp` is `private`, so it may have to be redone here.  The
layer `i = 0` is the unit layer and its evaluation is `Work.FIArea2.units_sum_ram`.) -/
theorem uvSum_eq_ramSum {p ν : ℕ} (hp : p.Prime) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
    (α β : ZMod (p ^ ν)) :
    (∑ u : ZMod (p ^ ν), ∑ v : ZMod (p ^ ν),
        (if u * v = 0 then Phi (p ^ ν) (u * α + v * β) else 0))
      = ∑ k ∈ Finset.range (ν + 1),
          ((p : ℂ) ^ (ν - k)) * (if p ^ (ν - k) ∣ α.val then (1 : ℂ) else 0)
            * ram (p ^ k) (β.val : ℤ) := by
  have hp' : NeZero p := ⟨hp.ne_zero⟩
  have h1 : (∑ u : ZMod (p ^ ν), ∑ v : ZMod (p ^ ν),
        (if u * v = 0 then Phi (p ^ ν) (u * α + v * β) else 0))
      = ∑ u : ZMod (p ^ ν), ∑ v : ZMod (p ^ ν),
        (if u * v = 0 then Phi (p ^ ν) (u * α) * Phi (p ^ ν) (v * β) else 0) := by
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
    by_cases h : u * v = 0
    · rw [if_pos h, if_pos h, Phi_add]
    · rw [if_neg h, if_neg h]
  have h2 := uvSum_layers (p := p) (ν := ν) hp hν
    (fun u : ZMod (p ^ ν) => Phi (p ^ ν) (u * α)) (fun v : ZMod (p ^ ν) => Phi (p ^ ν) (v * β))
  have h3 := uvAlg
    (fun i => ∑ u : ZMod (p ^ ν), if p ^ i ∣ u.val then Phi (p ^ ν) (u * α) else 0)
    (fun j => ∑ v : ZMod (p ^ ν), if p ^ j ∣ v.val then Phi (p ^ ν) (v * β) else 0) ν
  have h4 : (∑ j ∈ Finset.range (ν + 1),
          (∑ u : ZMod (p ^ ν), if p ^ j ∣ u.val then Phi (p ^ ν) (u * α) else 0)
            * ((∑ v : ZMod (p ^ ν), if p ^ (ν - j) ∣ v.val then Phi (p ^ ν) (v * β) else 0)
                - (if j = 0 then 0 else
                    (∑ v : ZMod (p ^ ν), if p ^ (ν - j + 1) ∣ v.val then
                      Phi (p ^ ν) (v * β) else 0))))
      = ∑ k ∈ Finset.range (ν + 1),
          ((p : ℂ) ^ (ν - k)) * (if p ^ (ν - k) ∣ α.val then (1 : ℂ) else 0)
            * ram (p ^ k) (β.val : ℤ) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hjle : j ≤ ν := Nat.lt_succ_iff.mp hj
    by_cases hj0 : j = 0
    · rw [hj0, Nat.sub_zero]
      rw [layerVal hp α 0 (Nat.zero_le ν), layerVal hp β ν le_rfl]
      rw [Nat.sub_self ν, if_pos rfl, sub_zero]
      rw [pow_zero, ram_one (β.val : ℤ), mul_one, uvPPow_zero, mul_one]
      simp only [uvPPow, Nat.sub_zero]
    · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      rw [layerVal hp α j hjle, layerVal hp β (ν - j) (Nat.sub_le _ _),
          Nat.sub_sub_self hjle, layerVal hp β (ν - j + 1) (by omega),
          show ν - (ν - j + 1) = j - 1 from by omega]
      rw [uvRam_ppow hp β.val j]
      simp only [uvPPow]
  exact h1.trans (h2.trans (h3.trans h4))

end

end Work.FIArea2
