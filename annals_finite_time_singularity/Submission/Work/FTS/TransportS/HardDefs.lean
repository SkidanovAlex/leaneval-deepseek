import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.TransportS.T2S
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.HhardZibp
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.integrable_prod_of_iterated
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.PairIntegralLe
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS

set_option autoImplicit false

/-!
# The slot decomposition of the `D_z`-transport hard part

This module collects the *definitions* (and the immediate product-measure facts and
elementary identities) used by the proof of `Work.FTS.TransportS.T2Hard`, the bound on the
five order-five terms `Work.FTS.H2.Hhard α f g` of the `D_z`-transport pairing.

`Hhard α f g z θ = f z θ · z · ∑_{k : Fin 5} pz (Thard g k) z θ · Thard g k z θ · w² · sghard α k θ`
(`Work.FTS.H2.T2Defs`), and `z · pz (Thard g k) z θ = Work.Spaces.Dz (Thard g k) z θ`
(`Dz_Thard` below).  Each of the five summands is thus the product `f · X_k · Y_k` of the
coefficient `f` with the two weighted derivatives

* `Xz α g k` — the order-`4` factor: `D_z^4 g · w/sin(2θ)^{η/2}` for `k = 0`, and
  `D_z^{4-k}D_θ^k g · W` for `k ≥ 1`,
* `Yz α g k` — the order-`5` factor: `D_z^5 g · w/sin(2θ)^{η/2}` for `k = 0`, and
  `D_z^{5-k}D_θ^k g · W` for `k ≥ 1`,

whose *squares* are single summands of `HkIntegrand α 4 g` resp. `HkIntegrand α 5 g`.  The
pointwise AM–GM inequality `|X Y| ≤ (X² + Y²)/2` therefore makes `Hhard` dominated by
`5 Mf · HkIntegrand α 5 g`, which is product-integrable for `g ∈ ℋ⁵`; this is the
integrability input of the Fubini argument behind `T2Hard`.
-/

/-- The weighted order-`4` factor of the `k`-th hard slot.  Its square is the corresponding
summand of `Work.Spaces.HkIntegrand α 4 g`: the `D_z^4 g`-slot (weight `w/sin(2θ)^{η/2}`) for
`k = 0` and the mixed slot `D_z^{4-k}D_θ^k g` (weight `W`) for `k ≥ 1`. -/
def Xz (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  if k.val = 0 then fun z θ => Work.Spaces.DzIter 4 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
  else fun z θ => Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ

/-- The weighted order-`5` factor of the `k`-th hard slot: the same construction with
`D_z(D_z^4 g) = D_z^5 g` resp. `D_z(D_z^{4-k}D_θ^k g) = D_z^{5-k}D_θ^k g`. -/
def Yz (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  if k.val = 0 then fun z θ => Work.Spaces.DzIter 5 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
  else fun z θ => Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ

/-- The `k`-th summand of `Hhard`, in the exact shape in which it occurs in the sum (with the
plain `∂_z` of the slot). -/
def gK (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ * z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
    * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ

/-- The `k`-th summand of `Hhard` with the `z ∂_z` written as `D_z`; it is equal to `gK`
(`gK_eq_hK`). -/
def hK (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  fun z θ => f z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ
    * Work.FTS.H2.Thard g k z θ * Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ

/-- The `z`-slice integrand obtained by integrating by parts the `k`-th summand of `Hhard`
(one half of `∂_z (f z θ · z w²) · (Thard g k z θ)²`). -/
def gK' (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
    * (Work.FTS.H2.Thard g k z θ) ^ 2

/-! ## The elementary identities -/

/-- `D_z` of the `k`-th order-`4` slot is the order-`5` slot with the same angular part. -/
theorem Dz_Thard (g : ℝ → ℝ → ℝ) (k : Fin 5) :
    Work.Spaces.Dz (Work.FTS.H2.Thard g k)
      = fun z θ => Work.Spaces.mixed (5 - k.val) k.val g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed g k]
  funext z θ
  fin_cases k <;> rfl

/-- `Hhard` is the sum of its five summands `gK`. -/
theorem Hhard_eq_sum_gK (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.H2.Hhard α f g z θ = ∑ k : Fin 5, gK α f g k z θ := by
  simp only [Work.FTS.H2.Hhard, gK, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `gK` and `hK` agree (the identity `z ∂_z Thard = D_z Thard`). -/
theorem gK_eq_hK (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) : gK α f g k = hK α f g k := by
  funext z θ
  simp only [gK, hK, Work.Spaces.Dz]
  ring

/-! ## The elementary weight algebra

The weight of the `k`-th order-`4` (resp. order-`5`) factor is `w z / sin(2θ)^{η/2}` for
`k = 0` and `W = w z · sin(2θ)^{-γ/2}` for `k ≥ 1`; in both cases the *square* of the weight is
`w(z)² · sin(2θ)^{-c}` (`c = η` resp. `c = γ`), which is the weight of the corresponding
summand of `Work.Spaces.HkIntegrand`.  The `rpow` identities behind this are collected here;
everything is pointwise and holds trivially when `sin(2θ) = 0` (`0 ^ c = 0` for `c ≠ 0` and
`0 ^ 0 = 1`). -/

/-- `(w / s^{c/2}) · (w / s^{c/2}) = w² · s^{-c}` for `s ≥ 0`. -/
theorem mul_self_div_rpow {w s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (w / s ^ (c / 2)) * (w / s ^ (c / 2)) = w ^ 2 * s ^ (-c) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [show (0 : ℝ) / 2 = 0 by norm_num, show -(0 : ℝ) = 0 by norm_num,
      Real.rpow_zero, div_one, mul_one]
    ring
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have h1 : (c / 2 : ℝ) ≠ 0 := fun hh => hc (by linarith)
      rw [Real.zero_rpow h1, div_zero, mul_zero,
        Real.zero_rpow (by simpa using neg_ne_zero.mpr hc), mul_zero]
    · have hpos : 0 < s := h
      have h2 : s ^ (c / 2) * s ^ (c / 2) = s ^ c := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      rw [div_mul_div_comm, h2, div_eq_mul_inv, ← Real.rpow_neg hpos.le]
      ring

/-- `(w / s^{c/2})² = w² · s^{-c}` for `s ≥ 0`. -/
theorem sq_div_rpow {w s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (w / s ^ (c / 2)) ^ 2 = w ^ 2 * s ^ (-c) := by
  rw [pow_two]
  exact mul_self_div_rpow hs c

/-- `(s^{-c/2})² = s^{-c}` for `s ≥ 0`. -/
theorem sq_rpow_neg_half {s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (s ^ (-(c / 2))) ^ 2 = s ^ (-c) := by
  rcases eq_or_ne c 0 with hc | hc
  · subst hc
    rw [show -((0 : ℝ) / 2) = 0 by norm_num, show -(0 : ℝ) = 0 by norm_num, Real.rpow_zero]
    norm_num
  · rcases eq_or_lt_of_le hs with h | h
    · subst h
      have h1 : (-(c / 2) : ℝ) ≠ 0 := fun hh => hc (by linarith)
      rw [Real.zero_rpow h1, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        Real.zero_rpow (by simpa using neg_ne_zero.mpr hc)]
    · have hpos : 0 < s := h
      have h2 : (s ^ (-(c / 2))) * (s ^ (-(c / 2))) = s ^ (-c) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      rw [pow_two]; exact h2

/-- `(w · s^{-c/2})² = w² · s^{-c}` for `s ≥ 0`. -/
theorem sq_mul_rpow_neg_half {w s : ℝ} (hs : 0 ≤ s) (c : ℝ) :
    (w * s ^ (-(c / 2))) ^ 2 = w ^ 2 * s ^ (-c) := by
  rw [mul_pow, sq_rpow_neg_half hs c]

/-! ## Pointwise forms of the slot data -/

/-- The order-`4` weighted factor of the `k`-th slot, for `k = 0`. -/
theorem Xz_apply_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Xz α g 0 z θ = Work.Spaces.DzIter 4 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  simp only [Xz]
  rw [if_pos (show ((0 : Fin 5).val = 0) from rfl)]

/-- The order-`5` weighted factor of the `k`-th slot, for `k = 0`. -/
theorem Yz_apply_zero (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Yz α g 0 z θ = Work.Spaces.DzIter 5 g z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
  simp only [Yz]
  rw [if_pos (show ((0 : Fin 5).val = 0) from rfl)]

theorem Xz_apply_ne {α : ℝ} {g : ℝ → ℝ → ℝ} {k : Fin 5} (hk : k.val ≠ 0) (z θ : ℝ) :
    Xz α g k z θ = Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ := by
  simp only [Xz]
  rw [if_neg hk]

theorem Yz_apply_ne {α : ℝ} {g : ℝ → ℝ → ℝ} {k : Fin 5} (hk : k.val ≠ 0) (z θ : ℝ) :
    Yz α g k z θ = Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ := by
  simp only [Yz]
  rw [if_neg hk]

/-- The order-`4` slot, for `k = 0`. -/
theorem Thard_apply_zero (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.H2.Thard g 0 z θ = Work.Spaces.DzIter 4 g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed]
  rfl

/-- The order-`4` slot, in mixed-derivative form (valid for every `k : Fin 5`). -/
theorem Thard_apply (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    Work.FTS.H2.Thard g k z θ = Work.Spaces.mixed (4 - k.val) k.val g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed]

/-- The order-`4` slot, for `k ≠ 0`. -/
theorem Thard_apply_ne {g : ℝ → ℝ → ℝ} {k : Fin 5} (hk : k.val ≠ 0) (z θ : ℝ) :
    Work.FTS.H2.Thard g k z θ = Work.Spaces.mixed (4 - k.val) k.val g z θ := by
  rw [Work.FTS.H2.Thard_eq_mixed]

/-- `D_z` of the order-`4` slot is the order-`5` slot. -/
theorem Dz_Thard_apply (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
      = Work.Spaces.mixed (5 - k.val) k.val g z θ := by
  rw [Dz_Thard g k]

/-- The square of the `k`-th order-`4` weighted factor is `w² · sin(2θ)^{-η_k}` times the
square of the slot `Thard g k`. -/
theorem Xz_sq {α : ℝ} (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Xz α g k z θ) ^ 2
      = (Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.sghard α k θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Xz_apply_zero, Thard_apply_zero, Work.FTS.H2.sghard_apply_zero, mul_pow,
      sq_div_rpow hs Work.Spaces.eta]
    ring
  · have hW : Work.Spaces.Wt α z θ ^ 2
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      show (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 = _
      exact sq_mul_rpow_neg_half hs (Work.Spaces.gam α)
    rw [Xz_apply_ne hk, Thard_apply_ne hk, Work.FTS.H2.sghard_apply_ne α k hk θ, mul_pow, hW]
    ring

/-- The same for the order-`5` weighted factor, with `D_z (Thard g k)` in place of
`Thard g k`. -/
theorem Yz_sq {α : ℝ} (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Yz α g k z θ) ^ 2
      = (Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.sghard α k θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    have hd : Work.Spaces.Dz (Work.FTS.H2.Thard g 0) z θ = Work.Spaces.DzIter 5 g z θ := by
      rw [Dz_Thard_apply g 0 z θ]
      rfl
    rw [Yz_apply_zero, hd, Work.FTS.H2.sghard_apply_zero, mul_pow,
      sq_div_rpow hs Work.Spaces.eta]
    ring
  · have hd : Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
        = Work.Spaces.mixed (5 - k.val) k.val g z θ := Dz_Thard_apply g k z θ
    have hW : Work.Spaces.Wt α z θ ^ 2
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      show (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2 = _
      exact sq_mul_rpow_neg_half hs (Work.Spaces.gam α)
    rw [Yz_apply_ne hk, hd, Work.FTS.H2.sghard_apply_ne α k hk θ, mul_pow, hW]
    ring

/-- The product of the two weighted factors of a slot is `Thard g k · D_z(Thard g k) · w² σ_k`. -/
theorem Xz_mul_Yz {α : ℝ} (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    Xz α g k z θ * Yz α g k z θ
      = Work.FTS.H2.Thard g k z θ * Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
        * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.Spaces.sin_two_nonneg_of_Iθ hθ
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    have hd : Work.Spaces.Dz (Work.FTS.H2.Thard g 0) z θ = Work.Spaces.DzIter 5 g z θ := by
      rw [Dz_Thard_apply g 0 z θ]
      rfl
    have ht := mul_self_div_rpow (s := Real.sin (2 * θ)) (w := Work.Spaces.w z) hs
      Work.Spaces.eta
    rw [Xz_apply_zero, Yz_apply_zero, Thard_apply_zero, hd, Work.FTS.H2.sghard_apply_zero]
    rw [show (Work.Spaces.DzIter 4 g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
          * (Work.Spaces.DzIter 5 g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)))
        = Work.Spaces.DzIter 4 g z θ * Work.Spaces.DzIter 5 g z θ
          * ((Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) from by ring,
      ht]
    ring
  · have hW : Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ
        = (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      show (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2)))
          * (Work.Spaces.w z * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) = _
      rw [← pow_two]
      exact sq_mul_rpow_neg_half hs (Work.Spaces.gam α)
    rw [Xz_apply_ne hk, Yz_apply_ne hk, Thard_apply_ne hk, Dz_Thard_apply,
      Work.FTS.H2.sghard_apply_ne α k hk θ]
    rw [show (Work.Spaces.mixed (4 - k.val) k.val g z θ * Work.Spaces.Wt α z θ)
          * (Work.Spaces.mixed (5 - k.val) k.val g z θ * Work.Spaces.Wt α z θ)
        = Work.Spaces.mixed (4 - k.val) k.val g z θ
          * Work.Spaces.mixed (5 - k.val) k.val g z θ
          * (Work.Spaces.Wt α z θ * Work.Spaces.Wt α z θ) from by ring,
      hW]
    ring

/-- `w² · ZU α g` is the sum of the squares of the five order-`4` weighted factors. -/
theorem w_sq_ZU_eq_sum {α : ℝ} (g : ℝ → ℝ → ℝ) (z θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * Work.FTS.H2.ZU α g z θ
      = ∑ k : Fin 5, (Xz α g k z θ) ^ 2 := by
  rw [Work.FTS.H2.ZU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Xz_sq g k z θ hθ]
  ring

/-- A single order-`4` weighted factor is a summand of `HkIntegrand α 5 g`. -/
theorem Xz_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    (Xz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Xz_apply_zero]
    exact Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ 4 (by norm_num)
  · rw [Xz_apply_ne hk]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ k.val (4 - k.val)
      (Nat.one_le_iff_ne_zero.mpr hk) (by omega)

/-- The same with the order-`4` integrand (used for the final numerical bound). -/
theorem Xz_sq_le_HkIntegrand4 (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    (Xz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Xz_apply_zero]
    exact Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ 4 le_rfl
  · rw [Xz_apply_ne hk]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ k.val (4 - k.val)
      (Nat.one_le_iff_ne_zero.mpr hk) (by omega)

/-- A single order-`5` weighted factor is a summand of `HkIntegrand α 5 g`. -/
theorem Yz_sq_le_HkIntegrand (α : ℝ) (g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ) :
    (Yz α g k z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 5 g z θ := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Yz_apply_zero]
    exact Work.Spaces.sq_le_HkIntegrand_z α 5 g z θ 5 le_rfl
  · rw [Yz_apply_ne hk]
    exact Work.Spaces.sq_le_HkIntegrand_mixed α 5 g z θ k.val (5 - k.val)
      (Nat.one_le_iff_ne_zero.mpr hk) (by omega)

/-! ## The pointwise bounds

`Hhard α f g` is the sum of the five summands `gK α f g k`, each of which is `f · X_k · Y_k`
with the two weighted factors of `HardDefs`; the AM–GM inequality `|X Y| ≤ (X² + Y²)/2`
turns these into a bound by `Mf · HkIntegrand α 5 g`.  The corresponding bound for the
integration-by-parts integrand `gK'` uses `|∂_z (f · z w²)| ≤ 4 Mf w²` and
`sin(2θ)^{η_k} ≤ 1` (`1 ≤ sghard α k θ`). -/

/-- `1 ≤ s^{-c}` for `0 < s ≤ 1` and `0 ≤ c`. -/
theorem one_le_rpow_neg_of_le_one {s c : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hc : 0 ≤ c) :
    1 ≤ s ^ (-c) := by
  rw [Real.rpow_neg hs.le, one_le_inv₀ (Real.rpow_pos_of_pos hs _)]
  exact Real.rpow_le_one hs.le hs1 hc

/-- The angular weight of each hard slot is at least `1` on the open interval. -/
theorem one_le_sghard {α : ℝ} (hα : 0 < α) (k : Fin 5) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 1 ≤ Work.FTS.H2.sghard α k θ := by
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    rw [Work.FTS.H2.sghard_apply_zero]
    exact one_le_rpow_neg_of_le_one hs (Real.sin_le_one _) (le_of_lt Work.Spaces.eta_pos)
  · rw [Work.FTS.H2.sghard_apply_ne α k hk θ]
    exact one_le_rpow_neg_of_le_one hs (Real.sin_le_one _) (by rw [Work.Spaces.gam]; linarith)

/-- Each summand of `Hhard` is `f` times the product of the two weighted slot factors. -/
theorem gK_eq_mul (α : ℝ) (f g : ℝ → ℝ → ℝ) (k : Fin 5) (z θ : ℝ)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    gK α f g k z θ = f z θ * (Xz α g k z θ * Yz α g k z θ) := by
  have hDz : Work.Spaces.Dz (Work.FTS.H2.Thard g k) z θ
      = Work.Spaces.mixed (5 - k.val) k.val g z θ := Dz_Thard_apply g k z θ
  have hpz : z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
      = Work.Spaces.mixed (5 - k.val) k.val g z θ := by
    rw [← hDz]
    rfl
  rw [gK, Xz_mul_Yz g k z θ hθ, hDz,
    show f z θ * z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
        * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.H2.sghard α k θ
      = f z θ * (z * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        * Work.FTS.H2.Thard g k z θ * (Work.Spaces.w z) ^ 2
        * Work.FTS.H2.sghard α k θ from by ring,
    hpz]
  ring

/-- The pointwise bound on a single summand of `Hhard`. -/
theorem abs_gK_le {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (k : Fin 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |gK α f g k z θ| ≤ Mf * Work.Spaces.HkIntegrand α 5 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hAM : |Xz α g k z θ| * |Yz α g k z θ|
      ≤ ((Xz α g k z θ) ^ 2 + (Yz α g k z θ) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|Xz α g k z θ| - |Yz α g k z θ|), sq_abs (Xz α g k z θ),
      sq_abs (Yz α g k z θ)]
  have hX := Xz_sq_le_HkIntegrand α g k z θ
  have hY := Yz_sq_le_HkIntegrand α g k z θ
  rw [gK_eq_mul α f g k z θ hθI, abs_mul, abs_mul]
  calc |f z θ| * (|Xz α g k z θ| * |Yz α g k z θ|)
      ≤ Mf * (((Xz α g k z θ) ^ 2 + (Yz α g k z θ) ^ 2) / 2) :=
        mul_le_mul (hf z θ hz hθ.1 hθ.2) hAM (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hMf
    _ ≤ Mf * ((Work.Spaces.HkIntegrand α 5 g z θ + Work.Spaces.HkIntegrand α 5 g z θ) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hMf
    _ = Mf * Work.Spaces.HkIntegrand α 5 g z θ := by ring

/-- The pointwise bound on `Hhard` itself. -/
theorem abs_Hhard_le {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS.H2.Hhard α f g z θ| ≤ 5 * Mf * Work.Spaces.HkIntegrand α 5 g z θ := by
  set H : ℝ := Work.Spaces.HkIntegrand α 5 g z θ with hH
  rw [Hhard_eq_sum_gK]
  calc |∑ k : Fin 5, gK α f g k z θ| ≤ ∑ k : Fin 5, |gK α f g k z θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 5, Mf * H := Finset.sum_le_sum fun k _ => by
        rw [hH]; exact abs_gK_le hMf hf k hz hθ
    _ = 5 * (Mf * H) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
    _ = 5 * Mf * H := by ring

/-- The pointwise bound on the integration-by-parts integrand `gK'`. -/
theorem abs_gK'_le {α Mf : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hDzf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf)
    (k : Fin 5) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |gK' α f g k z θ| ≤ 4 * Mf * Work.Spaces.HkIntegrand α 5 g z θ := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  have hratio : |(z - 3) / (1 + z)| ≤ 3 := Work.FTS.H2.abs_ratio_le_three z hz
  have hpz : |Work.Spaces.pz f z θ * z| = |Work.Spaces.Dz f z θ| := by
    rw [Work.Spaces.Dz, mul_comm]
  have h2 : |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2| ≤ Mf * (Work.Spaces.w z) ^ 2 := by
    rw [show Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          = (Work.Spaces.pz f z θ * z) * (Work.Spaces.w z) ^ 2 from by ring,
      abs_mul, abs_of_nonneg hw2, hpz]
    exact mul_le_mul_of_nonneg_right (hDzf z θ hz hθ.1 hθ.2) hw2
  have h3 : |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
      ≤ 3 * Mf * (Work.Spaces.w z) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hw2]
    calc |f z θ| * ((Work.Spaces.w z) ^ 2 * |(z - 3) / (1 + z)|)
        ≤ Mf * ((Work.Spaces.w z) ^ 2 * 3) := by
          refine mul_le_mul (hf z θ hz hθ.1 hθ.2) ?_ (mul_nonneg hw2 (abs_nonneg _)) hMf
          exact mul_le_mul_of_nonneg_left hratio hw2
      _ = 3 * Mf * (Work.Spaces.w z) ^ 2 := by ring
  have h1 : |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
      + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
      ≤ 4 * Mf * (Work.Spaces.w z) ^ 2 := by
    calc _ ≤ |Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2|
          + |f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))| := abs_add_le _ _
      _ ≤ Mf * (Work.Spaces.w z) ^ 2 + 3 * Mf * (Work.Spaces.w z) ^ 2 := add_le_add h2 h3
      _ = 4 * Mf * (Work.Spaces.w z) ^ 2 := by ring
  have hsk : 1 ≤ Work.FTS.H2.sghard α k θ := one_le_sghard hα k hθ
  have hskpos : 0 < Work.FTS.H2.sghard α k θ := lt_of_lt_of_le zero_lt_one hsk
  have hsq := Xz_sq (α := α) g k z θ hθI
  have hVW : (Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      = (Xz α g k z θ) ^ 2 / Work.FTS.H2.sghard α k θ := by
    rw [hsq, eq_div_iff (ne_of_gt hskpos)]
  have hX := Xz_sq_le_HkIntegrand α g k z θ
  rw [gK', abs_mul, abs_of_nonneg (sq_nonneg (Work.FTS.H2.Thard g k z θ))]
  calc (|Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)))|
        * (Work.FTS.H2.Thard g k z θ) ^ 2)
      ≤ (4 * Mf * (Work.Spaces.w z) ^ 2) * (Work.FTS.H2.Thard g k z θ) ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = 4 * Mf * ((Xz α g k z θ) ^ 2 / Work.FTS.H2.sghard α k θ) := by
        rw [show (4 * Mf * (Work.Spaces.w z) ^ 2) * (Work.FTS.H2.Thard g k z θ) ^ 2
              = 4 * Mf * ((Work.FTS.H2.Thard g k z θ) ^ 2 * (Work.Spaces.w z) ^ 2)
            from by ring, hVW]
    _ ≤ 4 * Mf * (Xz α g k z θ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [div_le_iff₀ hskpos]
        nlinarith [sq_nonneg (Xz α g k z θ), hsk]
    _ ≤ 4 * Mf * Work.Spaces.HkIntegrand α 5 g z θ :=
        mul_le_mul_of_nonneg_left hX (by linarith)

/-! ## The one-dimensional integration by parts on the half line -/

/-- A function with a limit along `𝓝[>] a` (whose value at `a` is that limit) is continuous
within `Ici a` at `a`.  (The `Ioi`-filter is finer than the `Ici`-filter, so the implication
needs the explicit value; we prove it through the basis `Ico a u` of `𝓝[Ici a] a`.) -/
theorem tendsto_Ici_of_tendsto_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds b)) (hb : F a = b) :
    Filter.Tendsto F (nhdsWithin a (Set.Ici a)) (nhds b) := by
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩

/-- **Integration by parts on `(0,∞)`.**  If `φ` and `V` are differentiable on `(0,∞)` with
derivatives `φ'` resp. `V'`, the products `φ V V'` and `φ' V²` are integrable on `(0,∞)`,
`|φ z| ≤ Mf · z w(z)²` and `z (V w)² → 0` at `0⁺` and at `+∞`, then
`∫_{0}^{∞} φ V V' = -(1/2) ∫_{0}^{∞} φ' V²`. -/
theorem zibp_Ioi {Mf : ℝ} (hMf : 0 ≤ Mf) {φ φ' V V' : ℝ → ℝ}
    (hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (φ' z) z)
    (hderivV : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt V (V' z) z)
    (hint1 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)))
    (hint2 : MeasureTheory.IntegrableOn (fun z => φ' z * V z ^ 2) (Set.Ioi (0 : ℝ)))
    (hφbnd : ∀ z ∈ Set.Ici (0 : ℝ), |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2))
    (hlim0 : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlimTop : Filter.Tendsto (fun z => z * (V z * Work.Spaces.w z) ^ 2) atTop (nhds 0)) :
    ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z
      = -(1 / 2) * ∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2 := by
  -- `φ 0 = 0` (the bound at `z = 0` is `|φ 0| ≤ Mf · 0 = 0`)
  have hφ0 : φ 0 = 0 := by
    have h := hφbnd 0 (Set.mem_Ici.mpr le_rfl)
    have hw : (0 : ℝ) * (Work.Spaces.w 0) ^ 2 = 0 := by ring
    rw [hw, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  set F : ℝ → ℝ := fun z => (1 / 2) * (φ z * V z ^ 2) with hF
  set F' : ℝ → ℝ := fun z => (1 / 2) * φ' z * V z ^ 2 + φ z * V z * V' z with hF'
  -- the derivative of `F`
  have hderivF : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' z) z := by
    intro z hz
    have h1 := ((hderivφ z hz).mul ((hderivV z hz).pow 2))
    have h2 := h1.const_mul (1 / 2)
    convert h2 using 1
    rw [hF']
    simp only [Pi.pow_apply]
    ring_nf
  have hintF : MeasureTheory.IntegrableOn F' (Set.Ioi (0 : ℝ)) := by
    have h3 : MeasureTheory.IntegrableOn (fun z => (1 / 2) * φ' z * V z ^ 2) (Set.Ioi (0 : ℝ)) :=
      (hint2.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun z => by ring)
    have h4 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)) := hint1
    refine (h3.add h4).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, hF']
  -- the two limits of `F`
  have hFbound : ∀ z ∈ Set.Ici (0 : ℝ), |F z| ≤ (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2) := by
    intro z hz
    have hzw : 0 ≤ z * (Work.Spaces.w z) ^ 2 :=
      mul_nonneg hz (sq_nonneg _)
    have h := hφbnd z hz
    rw [hF]
    calc |(1 / 2) * (φ z * V z ^ 2)|
        = (1 / 2) * (|φ z| * V z ^ 2) := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), abs_mul,
            abs_of_nonneg (sq_nonneg (V z))]
      _ ≤ (1 / 2) * ((Mf * (z * (Work.Spaces.w z) ^ 2)) * V z ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right h (sq_nonneg _)) (by norm_num)
      _ = (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2) := by ring
  have hF0eq : F 0 = 0 := by
    rw [hF]; simp [hφ0]
  have hFtop : Filter.Tendsto F atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun z => (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2))
      (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with z hz
      rw [Real.norm_eq_abs]
      exact hFbound z hz
    · have h3 := hlimTop.const_mul ((1 / 2) * Mf)
      simpa only [mul_zero] using h3
  have hF0 : Filter.Tendsto F (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (g := fun z => (1 / 2) * Mf * (z * (V z * Work.Spaces.w z) ^ 2))
      (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with z hz
      rw [Real.norm_eq_abs]
      exact hFbound z (Set.mem_Ici.mpr (le_of_lt hz))
    · have h3 := hlim0.const_mul ((1 / 2) * Mf)
      simpa only [mul_zero] using h3
  have hcont : ContinuousWithinAt F (Set.Ici 0) 0 := by
    rw [ContinuousWithinAt]
    have hlim : Filter.Tendsto F (nhdsWithin (0:ℝ) (Set.Ici 0)) (nhds 0) :=
      tendsto_Ici_of_tendsto_Ioi hF0 hF0eq
    rw [hF0eq]
    exact hlim
  -- the fundamental theorem of calculus
  have hFTC : (∫ z in Set.Ioi (0 : ℝ), F' z) = 0 := by
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderivF hintF hFtop, hF0eq,
      sub_zero]
  -- split the integral and conclude
  have hsplit : (∫ z in Set.Ioi (0 : ℝ), F' z)
      = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2)
        + ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z := by
    have h3 : MeasureTheory.IntegrableOn (fun z => (1 / 2) * φ' z * V z ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      (hint2.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun z => by ring)
    have h4 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)) := hint1
    rw [show (∫ z in Set.Ioi (0 : ℝ), F' z)
        = ∫ z in Set.Ioi (0 : ℝ),
            ((1 / 2) * φ' z * V z ^ 2 + φ z * V z * V' z) from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [hF']]
    have h5 : (∫ z in Set.Ioi (0:ℝ), (1 / 2) * φ' z * V z ^ 2)
        = (1 / 2) * ∫ z in Set.Ioi (0:ℝ), φ' z * V z ^ 2 := by
      rw [show (fun z => (1 / 2) * φ' z * V z ^ 2)
          = fun z => (1 / 2) * (φ' z * V z ^ 2) from by funext z; ring,
        MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add h3 h4, h5]
  linarith [hFTC, hsplit]

/-! ## Continuity of the blocks on the open quadrant -/

theorem continuousOn_w_Qd :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
  rw [hfun]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_prod.mp hp).1))

theorem continuousOn_w_sq_Qd :
    ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2) Work.FTS.LocData.Qd :=
  continuousOn_w_Qd.pow 2

theorem continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Work.FTS.LocData.Qd := by
  have hsinpos : ∀ p ∈ Work.FTS.LocData.Qd, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Set.mem_prod.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).rpow_const
    (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))

theorem continuousOn_wdivsin_Qd :
    ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) Work.FTS.LocData.Qd := by
  have hsinpos : ∀ p ∈ Work.FTS.LocData.Qd, 0 < Real.sin (2 * p.2) := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Set.mem_prod.mp hp
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact continuousOn_w_Qd.div (continuousOn_sinpow_Qd _)
    (fun p hp => ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _))

theorem continuousOn_sghard_Qd (α : ℝ) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.sghard α k p.2) Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    refine (continuousOn_sinpow_Qd (-(Work.Spaces.eta))).congr fun p _ => ?_
    simp only [Work.FTS.H2.sghard_apply_zero]
  · refine (continuousOn_sinpow_Qd (-(Work.Spaces.gam α))).congr fun p _ => ?_
    simp only [Work.FTS.H2.sghard_apply_ne α k hk]

theorem continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ =>
          Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Qd.mul (continuousOn_sinpow_Qd _)

theorem continuousOn_mixed_Qd {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Work.FTS.LocData.Qd := by
  refine ((Work.FTS.LocData.contDiffOn_mixed (V := Work.Spaces.quadU) Work.Spaces.isOpen_quadU hsg
    j i).continuousOn).mono ?_
  intro p hp
  obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
  have h1' : (0 : ℝ) < p.1 := h1
  exact Set.mem_prod.mpr ⟨Set.mem_Ioi.mpr (by linarith), h2⟩

theorem continuousOn_Thard_Qd {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.Thard g k p.1 p.2) Work.FTS.LocData.Qd := by
  refine (continuousOn_mixed_Qd hsg (4 - k.val) k.val).congr fun p _ => ?_
  simp only [Work.FTS.H2.Thard_eq_mixed]

theorem continuousOn_Xz_Qd {α : ℝ} {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Xz α g k p.1 p.2) Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    refine ((continuousOn_mixed_Qd hsg 4 0).mul continuousOn_wdivsin_Qd).congr fun p _ => ?_
    simp only [Xz_apply_zero, Work.Spaces.mixed_zero_right, Pi.mul_apply]
  · refine ((continuousOn_mixed_Qd hsg (4 - k.val) k.val).mul
      (continuousOn_Wt_Qd α)).congr fun p _ => ?_
    simp only [Xz_apply_ne hk, Pi.mul_apply]

theorem continuousOn_Yz_Qd {α : ℝ} {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g)
    (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => Yz α g k p.1 p.2) Work.FTS.LocData.Qd := by
  rcases eq_or_ne k.val 0 with hk | hk
  · have hk' : k = 0 := Fin.ext hk
    subst hk'
    refine ((continuousOn_mixed_Qd hsg 5 0).mul continuousOn_wdivsin_Qd).congr fun p _ => ?_
    simp only [Yz_apply_zero, Work.Spaces.mixed_zero_right, Pi.mul_apply]
  · refine ((continuousOn_mixed_Qd hsg (5 - k.val) k.val).mul
      (continuousOn_Wt_Qd α)).congr fun p _ => ?_
    simp only [Yz_apply_ne hk, Pi.mul_apply]

theorem continuousOn_ZU_Qd {α : ℝ} {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.ZU α g p.1 p.2) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.H2.ZU α g p.1 p.2)
      = fun p : ℝ × ℝ => ∑ k : Fin 5,
          Work.FTS.H2.Thard g k p.1 p.2 ^ 2 * Work.FTS.H2.sghard α k p.2 := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_finsetSum Finset.univ fun k _ =>
    ((continuousOn_Thard_Qd hsg k).pow 2).mul (continuousOn_sghard_Qd α k)

theorem continuousOn_gK_Qd {α : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.LocData.SmoothQuad g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => gK α f g k p.1 p.2) Work.FTS.LocData.Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.continuousOn).mono fun p hp => hp
  refine (hf.mul ((continuousOn_Xz_Qd (α := α) hsg k).mul
    (continuousOn_Yz_Qd (α := α) hsg k))).congr fun p hp => ?_
  have hp' := Set.mem_prod.mp hp
  rw [gK_eq_mul α f g k p.1 p.2 ⟨le_of_lt hp'.2.1, le_of_lt hp'.2.2⟩]
  simp only [Pi.mul_apply]

theorem continuousOn_gK'_Qd {α : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.LocData.SmoothQuad g) (k : Fin 5) :
    ContinuousOn (fun p : ℝ × ℝ => gK' α f g k p.1 p.2) Work.FTS.LocData.Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.continuousOn).mono fun p hp => hp
  have hpf : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.pz.continuousOn).mono fun p hp => hp
  have hratio : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) Work.FTS.LocData.Qd :=
    ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
      (continuousOn_const.add continuousOn_fst) (fun p hp => by
        have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
        linarith)
  refine ((((hpf.mul continuousOn_fst).mul continuousOn_w_sq_Qd).add
    (hf.mul (continuousOn_w_sq_Qd.mul hratio))).mul
      ((continuousOn_Thard_Qd hsg k).pow 2)).congr fun p _ => ?_
  simp only [gK', Pi.mul_apply, Pi.add_apply, Pi.pow_apply]

theorem continuousOn_Hhard_Qd {α : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.Hhard α f g p.1 p.2) Work.FTS.LocData.Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.FTS.H2.Hhard α f g p.1 p.2)
      = fun p : ℝ × ℝ => ∑ k : Fin 5, gK α f g k p.1 p.2 := by
    funext p; exact Hhard_eq_sum_gK α f g p.1 p.2
  rw [hfun]
  exact continuousOn_finsetSum Finset.univ fun k _ => continuousOn_gK_Qd hsf hsg k

theorem continuousOn_ZE_Qd {α : ℝ} {f g : ℝ → ℝ → ℝ} (hsf : Work.FTS.EllipticEst.SmoothOpen f)
    (hsg : Work.FTS.LocData.SmoothQuad g) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.H2.ZE α f g p.1 p.2) Work.FTS.LocData.Qd := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.continuousOn).mono fun p hp => hp
  have hDz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz f p.1 p.2) Work.FTS.LocData.Qd :=
    (hsf.Dz.continuousOn).mono fun p hp => hp
  have hratio : ContinuousOn (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) Work.FTS.LocData.Qd :=
    ContinuousOn.div (continuousOn_fst.sub continuousOn_const)
      (continuousOn_const.add continuousOn_fst) (fun p hp => by
        have h1 : (0 : ℝ) < p.1 := (Set.mem_prod.mp hp).1
        linarith)
  refine ((continuousOn_const (c := (1 / 2 : ℝ))).mul (((hDz.mul continuousOn_w_sq_Qd).add
    (hf.mul (continuousOn_w_sq_Qd.mul hratio))))).mul (continuousOn_ZU_Qd (α := α) hsg) |>.congr
    fun p _ => ?_
  simp only [Work.FTS.H2.ZE, Pi.mul_apply, Pi.add_apply]

/-! ## The product measure, and a.e. statements on the open quadrant -/

/-- The product of the two restricted Lebesgue measures is the restriction of the planar
Lebesgue measure to `Iz ×ˢ Iθ`. -/
theorem prod_restrict_eq :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod ℝ ℝ]

/-- A statement true on the whole open quadrant holds a.e. for the product of the two
restricted Lebesgue measures. -/
theorem ae_of_forall_Qd {P : ℝ × ℝ → Prop}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → P (z, θ)) :
    ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)), P p := by
  have hz : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[(volume : MeasureTheory.Measure (ℝ × ℝ))] (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    exact MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [prod_restrict_eq, MeasureTheory.Measure.restrict_congr_set hprod]
  exact MeasureTheory.ae_restrict_of_forall_mem (isOpen_Ioi.prod isOpen_Ioo).measurableSet
    fun p hp => h p.1 p.2 hp.1 hp.2.1 hp.2.2

/-- The open quadrant has full measure for the product of the two restricted Lebesgue
measures. -/
theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  have hθ : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := 0) (b := π / 2)).symm
  rw [MeasureTheory.Measure.restrict_congr_set hθ]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- A.e. membership in the open quadrant for the product measure. -/
theorem ae_mem_Qd : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ)), 0 < p.1 ∧ 0 < p.2 ∧ p.2 < π / 2 :=
  ae_of_forall_Qd fun z θ hz hθ hθ' => ⟨hz, hθ, hθ'⟩

/-- The θ-marginal of a product-integrable function is a.e. integrable on `Iz`. -/
theorem ae_integrableOn_slice {H : ℝ × ℝ → ℝ}
    (hH : MeasureTheory.Integrable H
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))) :
    ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun z => H (z, θ)) Work.Spaces.Iz := by
  have h := MeasureTheory.Integrable.prod_left_ae hH
  simpa only [MeasureTheory.IntegrableOn, Function.uncurry_apply_pair] using h

/-! ## The per-angle integration by parts identity -/

/-- **The per-angle integration by parts identity.**  For a fixed angle `θ` and a coefficient
bound `Mf` with `|f z θ| ≤ Mf` (`z > 0`), the boundary conditions `z (Thard g k z θ · w z)² → 0`
at `0⁺` and `+∞` for every slot `k`, and the `z`-slice integrability of the summands `gK` and
of the integration-by-parts integrands `gK'`, the `z`-integral of `Hhard` is minus that of
`ZE`.

The proof is the five term-by-term integrations by parts `zibp_Ioi`, summed with
`Hhard = ∑_k gK k`, `gK k = s_k · (s_k·φ)·V·V'`, `gK' k = φ'·V_k²` and
`ZE = ½ ∂_z(f z w²)·ZU`, `ZU = ∑_k V_k² σ_k`. -/
theorem slice_identity {α Mf : ℝ} {f g : ℝ → ℝ → ℝ} {θ : ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hMf : 0 ≤ Mf) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hfM : ∀ z ∈ Set.Ioi (0 : ℝ), |f z θ| ≤ Mf)
    (hbnd : ∀ k : Fin 5,
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.FTS.H2.Thard g k z θ * Work.Spaces.w z) ^ 2)
        atTop (nhds 0))
    (hint1 : ∀ k : Fin 5, MeasureTheory.IntegrableOn
      (fun z => gK α f g k z θ) Work.Spaces.Iz)
    (hint2 : ∀ k : Fin 5, MeasureTheory.IntegrableOn
      (fun z => gK' α f g k z θ) Work.Spaces.Iz) :
    (∫ z in Work.Spaces.Iz, Work.FTS.H2.Hhard α f g z θ)
      = -(∫ z in Work.Spaces.Iz, Work.FTS.H2.ZE α f g z θ) := by
  -- the per-slot integration by parts
  have hk : ∀ k : Fin 5,
      (∫ z in Work.Spaces.Iz, gK α f g k z θ)
        = -(1 / 2) * ∫ z in Work.Spaces.Iz,
            Work.FTS.H2.sghard α k θ * gK' α f g k z θ := by
    intro k
    set s : ℝ := Work.FTS.H2.sghard α k θ with hs
    have hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z' => s * (f z' θ * (z' * (Work.Spaces.w z') ^ 2)))
          (s * (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))) z := by
      intro z hz
      have h := ((hsf.hasDerivAt_slice hθ hz).mul (Work.FTS.H2.hasDerivAt_zw2 hz)).const_mul s
      convert h using 1
      ring_nf
    have hderivV : ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z' => Work.FTS.H2.Thard g k z' θ)
          (Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ) z := by
      intro z hz
      have hth : Work.FTS.H2.Thard g k
          = fun z θ => Work.Spaces.mixed (4 - k.val) k.val g z θ :=
        Work.FTS.H2.Thard_eq_mixed g k
      have hz0 : (0 : ℝ) < z := hz
      have hd := (hsg.differentiableAt_slice_mixed (4 - k.val) k.val
        (show z ∈ Set.Ioi (-1) from Set.mem_Ioi.mpr (by linarith)) hθ).hasDerivAt
      rw [show (fun z' => Work.FTS.H2.Thard g k z' θ)
            = fun z' => Work.Spaces.mixed (4 - k.val) k.val g z' θ from by
          funext z'; rw [hth],
        show Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ
            = deriv (fun z' => Work.Spaces.mixed (4 - k.val) k.val g z' θ) z from by
          rw [hth]; rfl]
      exact hd
    have hint1' : MeasureTheory.IntegrableOn
        (fun z => s * (f z θ * (z * (Work.Spaces.w z) ^ 2))
          * (Work.FTS.H2.Thard g k z θ) * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        (Set.Ioi (0 : ℝ)) := by
      refine ((hint1 k).mono_set Set.Ioi_subset_Ici_self).congr ?_
      filter_upwards with z
      simp only [gK, ← hs]
      ring_nf
    have hint2' : MeasureTheory.IntegrableOn
        (fun z => s * (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
          * (Work.FTS.H2.Thard g k z θ) ^ 2) (Set.Ioi (0 : ℝ)) := by
      have htmp : MeasureTheory.IntegrableOn (fun z => s * gK' α f g k z θ)
          (Set.Ioi (0 : ℝ)) :=
        ((hint2 k).mono_set Set.Ioi_subset_Ici_self).const_mul s
      refine htmp.congr ?_
      filter_upwards with z
      simp only [gK']
      ring_nf
    have hφbnd : ∀ z ∈ Set.Ici (0 : ℝ),
        |s * (f z θ * (z * (Work.Spaces.w z) ^ 2))|
          ≤ (|s| * Mf) * (z * (Work.Spaces.w z) ^ 2) := by
      intro z hz
      have hz0 : (0 : ℝ) ≤ z := hz
      rcases eq_or_lt_of_le hz0 with rfl | hzpos
      · have h0 : (0 : ℝ) * (Work.Spaces.w 0) ^ 2 = 0 := by ring
        rw [h0]
        simp
      · have hw : 0 ≤ z * (Work.Spaces.w z) ^ 2 :=
          mul_nonneg hzpos.le (sq_nonneg _)
        rw [abs_mul, abs_mul, abs_of_nonneg hw]
        calc |s| * (|f z θ| * (z * (Work.Spaces.w z) ^ 2))
            ≤ |s| * (Mf * (z * (Work.Spaces.w z) ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (hfM z hzpos) hw) (abs_nonneg s)
          _ = (|s| * Mf) * (z * (Work.Spaces.w z) ^ 2) := by ring
    have hφ' := zibp_Ioi (Mf := |s| * Mf) (mul_nonneg (abs_nonneg s) hMf)
      hderivφ hderivV hint1' hint2' hφbnd (hbnd k).1 (hbnd k).2
    have hIz : Work.Spaces.Iz = Set.Ici (0 : ℝ) := rfl
    have hφ'' : (∫ z in Work.Spaces.Iz, s * (f z θ * (z * (Work.Spaces.w z) ^ 2))
          * (Work.FTS.H2.Thard g k z θ) * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ)
        = -(1 / 2) * ∫ z in Work.Spaces.Iz, s *
            (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
              + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
          * (Work.FTS.H2.Thard g k z θ) ^ 2 := by
      rw [hIz, MeasureTheory.integral_Ici_eq_integral_Ioi,
        MeasureTheory.integral_Ici_eq_integral_Ioi]
      exact hφ'
    have h1 : (fun z => gK α f g k z θ)
        = fun z => s * (f z θ * (z * (Work.Spaces.w z) ^ 2)) * (Work.FTS.H2.Thard g k z θ)
            * Work.Spaces.pz (Work.FTS.H2.Thard g k) z θ := by
      funext z
      simp only [gK, ← hs]
      ring_nf
    have h2 : (fun z => Work.FTS.H2.sghard α k θ * gK' α f g k z θ)
        = fun z => s * (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
          * (Work.FTS.H2.Thard g k z θ) ^ 2 := by
      funext z
      simp only [gK', ← hs]
      ring_nf
    rw [h1, h2]
    exact hφ''
  -- sum over the five slots
  have hsum : (∫ z in Work.Spaces.Iz, Work.FTS.H2.Hhard α f g z θ)
      = -(1 / 2) * ∑ k : Fin 5, ∫ z in Work.Spaces.Iz,
          Work.FTS.H2.sghard α k θ * gK' α f g k z θ := by
    rw [show (fun z => Work.FTS.H2.Hhard α f g z θ)
        = fun z => ∑ k : Fin 5, gK α f g k z θ from
          funext fun z => Hhard_eq_sum_gK α f g z θ,
      MeasureTheory.integral_finsetSum Finset.univ (fun k _ => hint1 k),
      Finset.sum_congr rfl (fun k _ => hk k), Finset.mul_sum]
  -- the pointwise reconstruction of `ZU`
  have hpt : ∀ z : ℝ, ∑ k : Fin 5, Work.FTS.H2.sghard α k θ * gK' α f g k z θ
      = (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
        * Work.FTS.H2.ZU α g z θ := by
    intro z
    rw [Work.FTS.H2.ZU, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [gK']
    ring_nf
  have hlast : (∑ k : Fin 5, ∫ z in Work.Spaces.Iz,
        Work.FTS.H2.sghard α k θ * gK' α f g k z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
        * Work.FTS.H2.ZU α g z θ := by
    rw [← MeasureTheory.integral_finsetSum Finset.univ
      (fun k _ => (hint2 k).const_mul _),
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hZE : (∫ z in Work.Spaces.Iz, Work.FTS.H2.ZE α f g z θ)
      = (1 / 2) * ∫ z in Work.Spaces.Iz, (Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
          + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
        * Work.FTS.H2.ZU α g z θ := by
    rw [show (fun z => Work.FTS.H2.ZE α f g z θ)
        = fun z => (1 / 2) * ((Work.Spaces.pz f z θ * z * (Work.Spaces.w z) ^ 2
            + f z θ * ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))))
          * Work.FTS.H2.ZU α g z θ) from funext fun z => by
          simp only [Work.FTS.H2.ZE, Work.Spaces.Dz]
          ring_nf,
      MeasureTheory.integral_const_mul]
  rw [hsum, hlast, hZE]
  ring

/-! ## Product-measure facts for the `ℋ^k`-integrand -/

/-- The uncurried `HkIntegrand α k g` is a.e. strongly measurable for the product of the
restricted Lebesgue measures, for `g` smooth on the open quadrant. -/
theorem aesm_HkIntegrand_prod {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _
    (Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α k g hg)

/-- The `ℋ^k`-integrand of `g` is product-integrable with respect to the product of the two
restricted Lebesgue measures, and its product integral is `HkSq α k g`. -/
theorem integrable_HkIntegrand_prod {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α k g) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k g p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ∧ (∫ p, Work.Spaces.HkIntegrand α k g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        = Work.Spaces.HkSq α k g := by
  have h := Work.Spaces.integrable_prod_of_iterated
    (μ := volume.restrict Work.Spaces.Iz) (ν := volume.restrict Work.Spaces.Iθ)
    (G := fun z θ => Work.Spaces.HkIntegrand α k g z θ)
    (fun z θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
    (aesm_HkIntegrand_prod hg)
    ((MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iz from
      measurableSet_Ici)).mpr (Filter.Eventually.of_forall fun z hz => hmem.1 z hz))
    hmem.2
  exact ⟨h.1, by rw [h.2]; rfl⟩

/-- A single order-`4` weighted factor is a summand of `HkIntegrand α 4 g`, hence
product-integrable. -/
theorem integrable_Xz_sq {α : ℝ} {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g)
    (hmg4 : Work.Spaces.HkMem α 4 g) (k : Fin 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => (Xz α g k p.1 p.2) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono' (integrable_HkIntegrand_prod hsg hmg4).1
    (Work.Spaces.aesm_of_continuousOn_Qd _ ((continuousOn_Xz_Qd hsg k).pow 2)) ?_
  filter_upwards [ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    (Xz α g k p.1 p.2) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g p.1 p.2)
    fun z θ hz hθ hθ' => Xz_sq_le_HkIntegrand4 α g k z θ] with p hp
  simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hp

/-- `w(z)² ZU α g z θ ≤ 5 HkIntegrand α 4 g z θ` on the open quadrant. -/
theorem w_sq_ZU_le {α : ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.w z) ^ 2 * Work.FTS.H2.ZU α g z θ
      ≤ 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
  rw [w_sq_ZU_eq_sum (α := α) g z θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩]
  calc ∑ k : Fin 5, (Xz α g k z θ) ^ 2
      ≤ ∑ _k : Fin 5, Work.Spaces.HkIntegrand α 4 g z θ :=
        Finset.sum_le_sum fun k _ => Xz_sq_le_HkIntegrand4 α g k z θ
    _ = 5 * Work.Spaces.HkIntegrand α 4 g z θ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- `∫∫ w(z)² ZU α g ≤ 5 HkSq α 4 g`. -/
theorem integral_w_sq_ZU_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hsg : Work.FTS.LocData.SmoothQuad g)
    (hmg4 : Work.Spaces.HkMem α 4 g) :
    (∫ p, (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      ≤ 5 * Work.Spaces.HkSq α 4 g := by
  have hae : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2)
      =ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)]
        fun p => ∑ k : Fin 5, (Xz α g k p.1 p.2) ^ 2 :=
    ae_of_forall_Qd fun z θ hz hθ hθ' =>
      w_sq_ZU_eq_sum g z θ ⟨le_of_lt hθ, le_of_lt hθ'⟩
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_finsetSum Finset.univ
      (fun k _ => integrable_Xz_sq hsg hmg4 k)]
  calc ∑ k : Fin 5, ∫ p, (Xz α g k p.1 p.2) ^ 2
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ≤ ∑ _k : Fin 5, Work.Spaces.HkSq α 4 g :=
        Finset.sum_le_sum fun k _ => by
          calc (∫ p, (Xz α g k p.1 p.2) ^ 2
                ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
              ≤ ∫ p, Work.Spaces.HkIntegrand α 4 g p.1 p.2
                  ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
                MeasureTheory.integral_mono_ae (integrable_Xz_sq hsg hmg4 k)
                  (integrable_HkIntegrand_prod hsg hmg4).1
                  (Filter.Eventually.of_forall fun p : ℝ × ℝ =>
                    Xz_sq_le_HkIntegrand4 α g k p.1 p.2)
            _ = Work.Spaces.HkSq α 4 g := (integrable_HkIntegrand_prod hsg hmg4).2
    _ = 5 * Work.Spaces.HkSq α 4 g := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-! ## Product-integrability of the blocks -/

/-- Each of the five summands `gK` of `Hhard` is product-integrable, and its product integral
is bounded by `Mf · ∫∫ HkIntegrand α 5 g`. -/
theorem integrable_gK {α Mf : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hmg5 : Work.Spaces.HkMem α 5 g) (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) (k : Fin 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => gK α f g k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono'
    ((integrable_HkIntegrand_prod hsg hmg5).1.const_mul Mf)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_gK_Qd hsf hsg k)) ?_
  filter_upwards [ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    |gK α f g k p.1 p.2| ≤ Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2)
    fun z θ hz hθ hθ' => abs_gK_le hMf hf k hz ⟨hθ, hθ'⟩] with p hp
  simpa only [Real.norm_eq_abs, mul_comm] using hp

/-- `Hhard` itself is product-integrable. -/
theorem integrable_Hhard {α Mf : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hmg5 : Work.Spaces.HkMem α 5 g) (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.H2.Hhard α f g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono'
    (((integrable_HkIntegrand_prod hsg hmg5).1.const_mul Mf).const_mul 5)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_Hhard_Qd hsf hsg)) ?_
  filter_upwards [ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    |Work.FTS.H2.Hhard α f g p.1 p.2| ≤ 5 * Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2)
    fun z θ hz hθ hθ' => abs_Hhard_le hMf hf hz ⟨hθ, hθ'⟩] with p hp
  rw [Real.norm_eq_abs]
  calc |Work.FTS.H2.Hhard α f g p.1 p.2|
      ≤ 5 * Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2 := hp
    _ = 5 * (Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2) := by ring

/-- The integration-by-parts integrand `gK'` is product-integrable. -/
theorem integrable_gK' {α Mf : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hmg5 : Work.Spaces.HkMem α 5 g) (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hDzf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) (k : Fin 5) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => gK' α f g k p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine MeasureTheory.Integrable.mono'
    (((integrable_HkIntegrand_prod hsg hmg5).1.const_mul Mf).const_mul 4)
    (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_gK'_Qd hsf hsg k)) ?_
  filter_upwards [ae_of_forall_Qd (P := fun p : ℝ × ℝ =>
    |gK' α f g k p.1 p.2| ≤ 4 * Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2)
    fun z θ hz hθ hθ' => abs_gK'_le hα hMf hf hDzf k hz ⟨hθ, hθ'⟩] with p hp
  rw [Real.norm_eq_abs]
  calc |gK' α f g k p.1 p.2| ≤ 4 * Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2 := hp
    _ = 4 * (Mf * Work.Spaces.HkIntegrand α 5 g p.1 p.2) := by ring

/-- The correction term `ZE` is product-integrable and its absolute product integral is at
most `10 Mf HkSq α 4 g`. -/
theorem integrable_ZE_and_bound {α Mf : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsf : Work.FTS.EllipticEst.SmoothOpen f) (hsg : Work.FTS.LocData.SmoothQuad g)
    (hmg4 : Work.Spaces.HkMem α 4 g) (hMf : 0 ≤ Mf)
    (hf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |f z θ| ≤ Mf)
    (hDzf : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |Work.Spaces.Dz f z θ| ≤ Mf) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.H2.ZE α f g p.1 p.2)
        ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      ∧ (∫ p, |Work.FTS.H2.ZE α f g p.1 p.2|
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
        ≤ 10 * Mf * Work.Spaces.HkSq α 4 g := by
  have hZE : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      |Work.FTS.H2.ZE α f g p.1 p.2|
        ≤ 2 * Mf * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2) := by
    filter_upwards [ae_mem_Qd] with p hp
    have h := Work.FTS.H2.ZE_bound (α := α) (f := f) (g := g) hMf (le_of_lt hp.1)
      ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩ (hf p.1 p.2 hp.1 hp.2.1 hp.2.2)
      (hDzf p.1 p.2 hp.1 hp.2.1 hp.2.2)
    calc |Work.FTS.H2.ZE α f g p.1 p.2|
        ≤ 2 * Mf * (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2 := h
      _ = 2 * Mf * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2) := by ring
  have hZE' : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      |Work.FTS.H2.ZE α f g p.1 p.2|
        ≤ 10 * Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2 := by
    filter_upwards [hZE, ae_mem_Qd] with p hp hq
    calc |Work.FTS.H2.ZE α f g p.1 p.2|
        ≤ 2 * Mf * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2) := hp
      _ ≤ 2 * Mf * (5 * Work.Spaces.HkIntegrand α 4 g p.1 p.2) :=
          mul_le_mul_of_nonneg_left (w_sq_ZU_le ⟨hq.2.1, hq.2.2⟩) (by linarith)
      _ = 10 * Mf * Work.Spaces.HkIntegrand α 4 g p.1 p.2 := by ring
  have hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.FTS.H2.ZE α f g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine MeasureTheory.Integrable.mono'
      ((integrable_HkIntegrand_prod hsg hmg4).1.const_mul (10 * Mf))
      (Work.Spaces.aesm_of_continuousOn_Qd _ (continuousOn_ZE_Qd hsf hsg)) ?_
    filter_upwards [hZE'] with p hp
    simpa only [Real.norm_eq_abs, mul_assoc] using hp
  have hZUint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    have hae : (fun p : ℝ × ℝ => (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2)
        =ᵐ[(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)]
          fun p => ∑ k : Fin 5, (Xz α g k p.1 p.2) ^ 2 :=
      ae_of_forall_Qd fun z θ hz hθ hθ' =>
        w_sq_ZU_eq_sum g z θ ⟨le_of_lt hθ, le_of_lt hθ'⟩
    exact (integrable_finsetSum Finset.univ fun k _ => integrable_Xz_sq hsg hmg4 k).congr hae.symm
  refine ⟨hInt, ?_⟩
  calc (∫ p, |Work.FTS.H2.ZE α f g p.1 p.2|
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
      ≤ ∫ p, 2 * Mf * ((Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2)
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
        MeasureTheory.integral_mono_ae hInt.abs (hZUint.const_mul (2 * Mf)) hZE
    _ = 2 * Mf * ∫ p, (Work.Spaces.w p.1) ^ 2 * Work.FTS.H2.ZU α g p.1 p.2
          ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 2 * Mf * (5 * Work.Spaces.HkSq α 4 g) :=
        mul_le_mul_of_nonneg_left (integral_w_sq_ZU_le hsg hmg4) (by linarith)
    _ = 10 * Mf * Work.Spaces.HkSq α 4 g := by ring

/-! ## Product-measure facts for the `ℋ^k`-integrand -/