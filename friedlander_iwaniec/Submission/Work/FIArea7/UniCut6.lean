/-
# `Submission.Work.FIArea7.UniCut6` — the "uniform" (paper's `W`) cut, the small-moduli strip,
and the reduction of area 7 to *FI* Proposition 17.3

*FI* §17 estimates the partial sum `W(β)` of `T(β)` over the moduli with the *complementary*
divisor small: `d* = |Δ|/(4d) < X`, i.e. `|Δ| < 4dX`, with **no** condition on `d` itself (the
`d ≤ X` part of the range is carried by the smooth partition `f + f* = 1` of (10.14)–(10.17): see
the remarks after (10.17), "`V(β)` ranges over `d` with `X < d < |Δ|X^{-1}` ... while `W(β)` ranges
over `d` with `d* = |Δ|/4d < X`", and `U(β)` over `d ≤ X`).

The round-6 objects of `Defs6` split the moduli **sharply**:

| cut | condition |
|---|---|
| `Ucut` | `d ≤ X` |
| `Vcut` | `X < d ∧ 4dX < \|Δ\|` |
| `Wcut` | `X < d ∧ 4dX > \|Δ\|` |
| `Bcut` | `X < d ∧ 4dX = \|Δ\|` |

so `Wcut + Bcut` is the paper's sharp `W = {|Δ| ≤ 4dX}` **intersected with** `{X < d}`: it is the
paper's sharp `W` minus the *small-moduli strip* `Strip = {d ≤ X ∧ |Δ| ≤ 4dX}`.  The identity is
`Wcut6_add_Bcut6_eq_WUni6_sub_Strip6` below (a naming of the pieces of
`Wcut6_add_Bcut6_eq_uniform_sub`).

The strip lies inside the `U`-range `{d ≤ X}`, but the (17.10) character expansion cannot see it:
at fixed `(b,e)` the identity (16.11)/(17.10) applies to a *square* of `z`-sums, i.e. to a
congruence condition `z₁ ≡ ω z₂ (mod Q)`, whereas the strip's extra condition `4eX < |Δ|` (the
image of `X < d` under the reflection) is pair-dependent — a condition on `Δ` itself.  What *is*
uniform in the pair is the reflected range of the paper's cut: under `d ↦ e = |Δ|/(4d)`
(`Work.FIArea7.WBcut_reflection`),

* `|Δ| ≤ 4dX` becomes `e ≤ X` — a range **uniform** in the pair (the object `WUni6` below);
* `X < d` becomes `4eX < |Δ|` — the pair-dependent condition that (17.9) cannot absorb.

So `Wcut + Bcut = WUni6 − Strip6`, and the contract follows from

1. the bound for the **uniform** object `WUni6` — this is *FI* Proposition 17.3 (17.19) at the
   sharp cut, and it is exactly what the (17.1) → (17.9) → (17.10) → (17.13) → Proposition 17.2
   chain computes (the reflected `e`-range is uniform, so the `(b,e)`-sums can be pulled outside
   the pair sums and (16.11) applies verbatim); and
2. an elementary bound for the **strip** `Strip6`: its pairs satisfy `|Δ| ≤ 4X²`
   (`Work.FIArea7.card_pairs_gBox_absDelta_lt`), each carries at most `X` admissible moduli
   `d ≤ X`, and the coefficient mass is `Σ_z ‖β z‖² ≪ (θN+√N+1)(log N)³`
   (`Work.FIArea6.vsq_polar`), giving `‖Strip6‖ ≪ X²N^{3/2}(log N)^4 ≪ (Pz⁻¹+X⁻¹)N²log N` as
   soon as `X⁹ ≤ N`.

`Work.FIArea7.area7_6_of_uniform_of_strip : Area7Uni6 → Area7Strip6 → Work.FITop4.Area7_6` is the
reduction.  **No change to the round-6 contract is needed**: the strip is the only part of
`Area7_6` beyond the paper's Proposition 17.3, and it is elementary.
-/
import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea7.WBcutTools
import Submission.Work.FITop3.Defs3

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. `Work.FITop4.Tcut` book-keeping

(Moved here from `area7_6.lean` so that this file — and every module that depends on it — stays
free of the round-6 §17 `sorry`.)
-/


/-- `Work.FITop4.Tcut` writes its inner sum in a context of expected type `ℂ`; this lemma
exhibits it as the coercion of the corresponding `ℝ`-valued inner sum, the form in which the
§17 identities (`WBcut_inner_totient_expansion`) are stated. -/
theorem Tcut6_eq_sum_ofReal (Rz : ℤ) (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz cut β
      = 2 * ∑ z1 ∈ Work.FIPlan.gBox Rz, ∑ z2 ∈ Work.FIPlan.gBox Rz,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            β z1 * star (β z2)
              * ((∑ d ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
                    (fun d => 4 * d ∣ Work.FIPlan.absDelta z1 z2),
                    ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
                      * (Work.FITop4.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
           else 0) := by
  simp only [Work.FITop4.Tcut, Work.FITop4.Sset]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro d _
    push_cast; ring
  · simp only [hg, if_false]

/-- `Work.FITop4.Tcut` is additive in its cut (there is no rearrangement in the `d`-sum), so
that `Wcut + Bcut` is `Tcut` with the sum of the two indicator cuts. -/
theorem Tcut6_add_cut (Rz : ℤ) (c1 c2 : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Tcut Rz c1 β + Work.FITop4.Tcut Rz c2 β
      = Work.FITop4.Tcut Rz (fun z1 z2 d => c1 z1 z2 d + c2 z1 z2 d) β := by
  rw [Tcut6_eq_sum_ofReal Rz c1 β, Tcut6_eq_sum_ofReal Rz c2 β,
    Tcut6_eq_sum_ofReal Rz (fun z1 z2 d => c1 z1 z2 d + c2 z1 z2 d) β]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    rw [← mul_add, ← Complex.ofReal_add]
    congr 1
    rw [Complex.ofReal_inj, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro d _
    ring
  · simp only [hg, if_false]; ring

/-- `Work.FITop4.Tcut` depends only on the values of its cut. -/
theorem Tcut6_congr_cut (Rz : ℤ) (c1 c2 : GaussianInt → GaussianInt → ℕ → ℝ)
    (β : GaussianInt → ℂ) (h : ∀ z1 z2 d, c1 z1 z2 d = c2 z1 z2 d) :
    Work.FITop4.Tcut Rz c1 β = Work.FITop4.Tcut Rz c2 β := by
  simp only [Work.FITop4.Tcut, Work.FITop4.Sset]
  congr 1
  apply Finset.sum_congr rfl; intro z1 _
  apply Finset.sum_congr rfl; intro z2 _
  by_cases hg : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hg, if_true]
    congr 1
    apply Finset.sum_congr rfl; intro d _
    rw [h z1 z2 d]
  · simp only [hg, if_false]

/-- **`Wcut + Bcut` is the paper's `W` minus the small-moduli strip.**  Pointwise in the cut
functions, `[X < d ∧ |Δ| ≤ 4dX] = [|Δ| ≤ 4dX] − [d ≤ X ∧ |Δ| ≤ 4dX]`. -/
theorem Wcut6_add_Bcut6_eq_uniform_sub (Rz : ℤ) (X : ℕ) (β : GaussianInt → ℂ) :
    Work.FITop4.Wcut Rz X β + Work.FITop4.Bcut Rz X β
      = Work.FITop4.Tcut Rz (fun z1 z2 d =>
            if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β
        - Work.FITop4.Tcut Rz (fun z1 z2 d =>
            if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β := by
  have h1 : Work.FITop4.Wcut Rz X β + Work.FITop4.Bcut Rz X β
      = Work.FITop4.Tcut Rz (fun z1 z2 d =>
          if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β := by
    rw [Work.FITop4.Wcut, Work.FITop4.Bcut, Tcut6_add_cut]
    exact Tcut6_congr_cut _ _ _ _ (fun z1 z2 d => cutW_add_cutB _ _ _)
  have h2 : Work.FITop4.Tcut Rz (fun z1 z2 d =>
        if X < d ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β
      = Work.FITop4.Tcut Rz (fun z1 z2 d =>
          (if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
            - (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)) β := by
    refine Tcut6_congr_cut _ _ _ _ (fun z1 z2 d => ?_)
    by_cases hM : Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X
    · by_cases hd : d ≤ X
      · rw [if_neg (by rintro ⟨hh, _⟩; omega), if_pos hM, if_pos ⟨hd, hM⟩]; ring
      · rw [if_pos ⟨Nat.lt_of_not_le hd, hM⟩, if_pos hM, if_neg (by rintro ⟨hd', _⟩; omega)]
        ring
    · rw [if_neg (by rintro ⟨_, hh⟩; exact hM hh), if_neg hM,
        if_neg (by rintro ⟨_, hh⟩; exact hM hh)]
      ring
  have h3 : Work.FITop4.Tcut Rz (fun z1 z2 d =>
          (if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
            - (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)) β
      = Work.FITop4.Tcut Rz (fun z1 z2 d =>
            if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β
        - Work.FITop4.Tcut Rz (fun z1 z2 d =>
            if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β := by
    have h := Tcut6_add_cut Rz
      (fun z1 z2 d => (if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
        - (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0))
      (fun z1 z2 d => if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β
    have hsum : (fun z1 z2 d =>
          ((if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0)
            - (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0))
          + (if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0))
        = (fun z1 z2 d => if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) := by
      funext z1 z2 d
      by_cases hM : Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X <;>
        by_cases hd : d ≤ X <;> simp [hM, hd]
    rw [hsum] at h
    rw [eq_sub_iff_add_eq]
    exact h
  rw [h1, h2, h3]

/-! ## 2. The uniform (paper's `W`) cut and the small-moduli strip -/

/-- ***FI* (17.1)/(17.9) for the paper's cut `|Δ| ≤ 4dX`** (no condition on `d`), reflected by
`d ↦ e = |Δ|/(4d)` and expanded by `φ(m)/m = Σ_{b∣m} μ(b)/b` with `m = |Δ|/(4e)`.

Compared with `Work.FIArea7.WBcutExpandedInner` — the *union* `W ∪ B` of the two cuts, whose
`e`-range is the pair-dependent `e ≤ X ∧ 4eX < |Δ|` — the only difference is that the extra
condition `4eX < |Δ|` (the image of `X < d`) is dropped.  The reflected `e`-range `e ≤ X` is
uniform in the pair, which is exactly what the §16 expansion (17.10) needs. -/
def WUniInner (X : ℕ) (sym : ℕ → ℤ) (L : ℝ) (M : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 (M / 4 + 1),
    ∑ e ∈ (Finset.Icc 1 (M / 4 + 1)).filter (fun e => 4 * b * e ∣ M ∧ e ≤ X),
      ((ArithmeticFunction.moebius b : ℝ) / (b : ℝ)) * (sym (M / (4 * e)) : ℝ) * L

/-- The uniform inner sum at the ratio symbol and the round-6 logarithmic factor. -/
def WUniInner6 (X : ℕ) (z1 z2 : GaussianInt) : ℝ :=
  WUniInner X (fun d => Work.FITop4.ratioSym z1 z2 d) (Work.FITop4.logFac6 z1 z2)
    (Work.FIPlan.absDelta z1 z2)

/-- **The paper's `W` at the sharp cut** (`|Δ| ≤ 4dX`, reflected range `e ≤ X`): `Tcut` with the
cut function `1_{|Δ| ≤ 4dX}`.  This is the object of *FI* Proposition 17.3 (17.19). -/
def WUni6 (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Work.FITop4.Tcut (Work.FITop.radN Pa)
    (fun z1 z2 d => if Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β

/-- **The small-moduli strip** `{d ≤ X ∧ |Δ| ≤ 4dX}`: the part of the paper's `W` that the round-6
cut `W ∪ B` does *not* contain (in the reflected variable `e = |Δ|/(4d)`, the part
`{|Δ|/(4X) ≤ e ≤ X}` of the paper's range). -/
def Strip6 (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  Work.FITop4.Tcut (Work.FITop.radN Pa)
    (fun z1 z2 d =>
      if d ≤ X ∧ Work.FIPlan.absDelta z1 z2 ≤ 4 * d * X then (1 : ℝ) else 0) β

/-- **`Wcut + Bcut` is the paper's `W` minus the small-moduli strip.**  This is the cut-level
identity `[X < d ∧ |Δ| ≤ 4dX] = [|Δ| ≤ 4dX] − [d ≤ X ∧ |Δ| ≤ 4dX]` transported through
`Work.FITop4.Tcut` (`Wcut6_add_Bcut6_eq_uniform_sub`, with the two pieces named). -/
theorem Wcut6_add_Bcut6_eq_WUni6_sub_Strip6 (Pa : Work.FITop.Params) (X : ℕ)
    (β : GaussianInt → ℂ) :
    Work.FITop4.Wcut (Work.FITop.radN Pa) X β + Work.FITop4.Bcut (Work.FITop.radN Pa) X β
      = WUni6 Pa X β - Strip6 Pa X β := by
  simpa only [WUni6, Strip6] using
    Wcut6_add_Bcut6_eq_uniform_sub (Work.FITop.radN Pa) X β

/-- The identity in the form `WUni6 = (Wcut + Bcut) + Strip6`. -/
theorem WUni6_eq_Wcut6_add_Bcut6_add_Strip6 (Pa : Work.FITop.Params) (X : ℕ)
    (β : GaussianInt → ℂ) :
    WUni6 Pa X β
      = (Work.FITop4.Wcut (Work.FITop.radN Pa) X β
          + Work.FITop4.Bcut (Work.FITop.radN Pa) X β) + Strip6 Pa X β := by
  rw [Wcut6_add_Bcut6_eq_WUni6_sub_Strip6]
  abel

/-! ## 3. The two predicates, and the reduction of the contract -/

/-- **The paper's Proposition 17.3 (17.19) at the sharp uniform cut**: for every exponent
`η ∈ (0, 3/32)` there are `δ, c, x₀ > 0` such that for `1 ≤ X < N^δ` and every coefficient of
(4.13)+(5.13)+(5.7),

  `‖WUni6‖ ≤ c·(Pz⁻¹ + X⁻¹)·N²·log N`.

This is *FI*'s §17 statement (their `W(β)`, with the smooth weight `f*` replaced by the sharp
indicator `1_{|Δ| ≤ 4dX}` — the argument uses only `f* ≤ 1`), and it is the target of the
(17.9)/(17.10)/(17.13)/Proposition-17.2 chain. -/
def Area7Uni6 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ δ c x0 : ℝ, 0 < δ ∧ 0 < c ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) < Pa.N ^ δ →
    ‖WUni6 Pa X β‖
      ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-- **The small-moduli strip is bounded.**  For `X⁹ ≤ N` (so `X ≤ N^{1/9}`, comfortably inside the
elementary range `X ≲ N^{1/3}/log N`) and large enough `x`,

  `‖Strip6‖ ≤ C·(Pz⁻¹ + X⁻¹)·N²·log N`. -/
def Area7Strip6 : Prop :=
  ∃ C x0 : ℝ, 0 < C ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → (X : ℝ) ^ 9 ≤ Pa.N →
    ‖Strip6 Pa X β‖
      ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

/-- **The round-6 contract follows from the paper's Proposition 17.3 and the strip bound.**
Take `δ = min δ_Uni 1/9`, so that `X < N^δ` gives both `X < N^{δ_Uni}` (the uniform object's
range) and `X⁹ ≤ N` (the strip's range), and add the two bounds.  (The round-6.2/6.3 side
condition `X ≤ (log N)^{nuU}` of `Area7_6` is *not* used: this route proves the bound in the
strictly larger range `X < N^{1/9}`.) -/
theorem area7_6_of_uniform_of_strip (hU : Area7Uni6) (hS : Area7Strip6) :
    Work.FITop4.Area7_6 := by
  intro η hη0 hηlt
  obtain ⟨δ, c, xU, hδ, hc, hU⟩ := hU η hη0 hηlt
  obtain ⟨C, xS, hC, hS⟩ := hS
  refine ⟨min δ ((1 : ℝ) / 9), c + C, max xU xS, lt_min hδ (by norm_num),
    by positivity, ?_⟩
  intro Pa hx hηPa X φ z0 β hβ hX hXδ _
  have hxU' : xU ≤ (Pa.x : ℝ) := le_trans (le_max_left _ _) hx
  have hxS' : xS ≤ (Pa.x : ℝ) := le_trans (le_max_right _ _) hx
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hδ' : (X : ℝ) < Pa.N ^ δ :=
    lt_of_lt_of_le hXδ (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_left _ _))
  have h9 : (X : ℝ) ^ 9 ≤ Pa.N := by
    have hXle : (X : ℝ) ≤ Pa.N ^ ((1 : ℝ) / 9) :=
      le_of_lt (lt_of_lt_of_le hXδ (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)))
    have h9' : (Pa.N ^ ((1 : ℝ) / 9)) ^ 9 = Pa.N := by
      rw [← Real.rpow_natCast (Pa.N ^ ((1 : ℝ) / 9)) 9, ← Real.rpow_mul hNpos.le]
      norm_num
    calc (X : ℝ) ^ 9 ≤ (Pa.N ^ ((1 : ℝ) / 9)) ^ 9 :=
          pow_le_pow_left₀ (by positivity) hXle 9
      _ = Pa.N := h9'
  have h1 := hU Pa hxU' hηPa X φ z0 β hβ hX hδ'
  have h2 := hS Pa hxS' X φ z0 β hβ hX h9
  have hRnn : (0 : ℝ) ≤ ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by
    have hPpos : (0 : ℝ) < (Pa.Pz : ℝ) := by
      have h : (0 : ℕ) < Pa.Pz := lt_of_lt_of_le Nat.zero_lt_two Pa.hP2
      exact_mod_cast h
    have hXpos : (0 : ℝ) < (X : ℝ) := by
      have h : (0 : ℕ) < X := lt_of_lt_of_le Nat.zero_lt_one hX
      exact_mod_cast h
    have h1 : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ := inv_nonneg.mpr hPpos.le
    have h2 : (0 : ℝ) ≤ (X : ℝ)⁻¹ := inv_nonneg.mpr hXpos.le
    have h3 : (0 : ℝ) ≤ Pa.N ^ 2 := sq_nonneg _
    exact mul_nonneg (mul_nonneg (add_nonneg h1 h2) h3) (Real.log_nonneg hN1)
  calc ‖Work.FITop4.Wcut (Work.FITop.radN Pa) X β
          + Work.FITop4.Bcut (Work.FITop.radN Pa) X β‖
      = ‖WUni6 Pa X β - Strip6 Pa X β‖ := by rw [Wcut6_add_Bcut6_eq_WUni6_sub_Strip6]
    _ ≤ ‖WUni6 Pa X β‖ + ‖Strip6 Pa X β‖ := norm_sub_le _ _
    _ ≤ c * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N
          + C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N :=
        add_le_add h1 h2
    _ = (c + C) * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N := by ring

end

end Work.FIArea7
