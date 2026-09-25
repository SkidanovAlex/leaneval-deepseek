import Mathlib
import Submission.Work.LT.lr_local_defs

/-!
# Upper bound for the `M`-operator: `Work.LT.lr_M_case`

The target is the bound `⟨1_R, M 1_R⟩ ≤ |R|(p + μ(1-p))` for the vertex operator
`M = Up ∘ M₀ ∘ Down` studied in the analysis of the DELLM local search (Proposition 4.8 and
Claims 4.10/4.11 of `Locally testable codes with constant rate, distance, and locality`).

This file provides the finite-sum infrastructure (`Work.LT.lrM_*`) and the proof of the requested
lemma.  All the auxiliary lemmas are about the concrete objects of `Submission.Work.LT.lr_local_defs`
(`Vtx`, `M0`, `Sfun`, `gfun`, `Qfun`, `MForm`, `dispCount`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

/-! ## Elementary finite-sum identities on a finite type -/

/-- Centring a function subtracts `card · c` from the sum. -/
lemma lrM_sum_sub_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    ∑ i, (f i - c) = (∑ i, f i) - (Fintype.card ι : ℝ) * c := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The variance identity: centring a function changes the sum of squares as displayed. -/
lemma lrM_sum_sq_sub_const {ι : Type*} [Fintype ι] (f : ι → ℝ) (c : ℝ) :
    ∑ i, (f i - c) ^ 2
      = (∑ i, f i ^ 2) - 2 * c * (∑ i, f i) + (Fintype.card ι : ℝ) * c ^ 2 := by
  have h : ∀ i, (f i - c) ^ 2 = f i ^ 2 - 2 * c * f i + c ^ 2 := by intro i; ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Expanding a sum of products of two centred functions; the cross terms vanish because `u` and
`w` are mean zero. -/
lemma lrM_sum_add_mul_add {ι : Type*} [Fintype ι] (u w : ι → ℝ) (c : ℝ)
    (hu : ∑ i, u i = 0) (hw : ∑ i, w i = 0) :
    ∑ i, (c + u i) * (c + w i) = (Fintype.card ι : ℝ) * c ^ 2 + ∑ i, u i * w i := by
  have h : ∀ i, (c + u i) * (c + w i) = c ^ 2 + c * w i + u i * c + u i * w i := by
    intro i; ring
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hw, hu]
  ring

variable {G : Type*} [Group G] [Fintype G] {Δ : ℕ}

/-! ## The vertex operator `M₀` -/

/-- The vertex type has `4 |G|` elements. -/
lemma lrM_card_Vtx (G : Type*) [Group G] [Fintype G] :
    Fintype.card (Vtx G) = 4 * Fintype.card G := by
  simp [Vtx, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The A-step `v ↦ nA A v i` is an involution of the vertex set. -/
def lrM_nAEquiv (A : Fin Δ → G) (i : Fin Δ) : Vtx G ≃ Vtx G :=
  { toFun := fun v => nA A v i, invFun := fun v => nA A v i,
    left_inv := fun v => nA_nA A v i, right_inv := fun v => nA_nA A v i }

/-- Summation over the A-neighbours in a fixed direction is summation over all vertices. -/
lemma lrM_sum_nA (A : Fin Δ → G) (i : Fin Δ) (h : Vtx G → ℝ) :
    ∑ v : Vtx G, h (nA A v i) = ∑ v, h v :=
  Equiv.sum_comp (lrM_nAEquiv A i) h

/-- The B-step `v ↦ nB B v j` is an involution of the vertex set. -/
def lrM_nBEquiv (B : Fin Δ → G) (j : Fin Δ) : Vtx G ≃ Vtx G :=
  { toFun := fun v => nB B v j, invFun := fun v => nB B v j,
    left_inv := fun v => nB_nB B v j, right_inv := fun v => nB_nB B v j }

/-- Summation over the B-neighbours in a fixed direction is summation over all vertices. -/
lemma lrM_sum_nB (B : Fin Δ → G) (j : Fin Δ) (h : Vtx G → ℝ) :
    ∑ v : Vtx G, h (nB B v j) = ∑ v, h v :=
  Equiv.sum_comp (lrM_nBEquiv B j) h

/-- `M₀` preserves sums: it is an averaging operator along the `2Δ` edge directions. -/
lemma lrM_sum_M0 (A B : Fin Δ → G) (hΔ : 0 < Δ) (h : Vtx G → ℝ) :
    ∑ v : Vtx G, M0 A B h v = ∑ v, h v := by
  simp only [M0]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have h1 : (∑ v : Vtx G, ∑ i : Fin Δ, h (nA A v i)) = (Δ : ℝ) * ∑ v, h v := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun i _ => lrM_sum_nA A i h)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have h2 : (∑ v : Vtx G, ∑ j : Fin Δ, h (nB B v j)) = (Δ : ℝ) * ∑ v, h v := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun j _ => lrM_sum_nB B j h)]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2]
  have hne : (Δ : ℝ) ≠ 0 := by exact_mod_cast hΔ.ne'
  field_simp
  try ring

/-- `M₀` fixes constants. -/
lemma lrM_M0_const_add (A B : Fin Δ → G) (hΔ : 0 < Δ) (c : ℝ) (h : Vtx G → ℝ) (v : Vtx G) :
    M0 A B (fun u => c + h u) v = c + M0 A B h v := by
  simp only [M0]
  have hne : (Δ : ℝ) ≠ 0 := by exact_mod_cast hΔ.ne'
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  try ring

/-! ## The disputed-edge count `Sfun` and its normalisation `gfun` -/

/-- At most `2Δ` disputed edges pass through any vertex. -/
lemma lrM_Sfun_le (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    Sfun A B W v ≤ 2 * Δ := by
  classical
  simp only [Sfun, rA, rB]
  have h1 : (((Finset.univ : Finset (Fin Δ)).filter (fun i : Fin Δ => dispAE A W v i)).card : ℝ)
      ≤ (Δ : ℝ) := by
    have hle := Finset.card_filter_le (Finset.univ : Finset (Fin Δ))
      (fun i : Fin Δ => dispAE A W v i)
    rw [Finset.card_univ, Fintype.card_fin] at hle
    exact_mod_cast hle
  have h2 : (((Finset.univ : Finset (Fin Δ)).filter (fun j : Fin Δ => dispBE B W v j)).card : ℝ)
      ≤ (Δ : ℝ) := by
    have hle := Finset.card_filter_le (Finset.univ : Finset (Fin Δ))
      (fun j : Fin Δ => dispBE B W v j)
    rw [Finset.card_univ, Fintype.card_fin] at hle
    exact_mod_cast hle
  linarith

/-- `Sfun` is nonnegative. -/
lemma lrM_Sfun_nonneg (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (v : Vtx G) :
    0 ≤ Sfun A B W v := by
  classical
  simp only [Sfun, rA, rB]
  positivity

/-- The mean of `gfun` over the vertices is `|R| / Δ`. -/
lemma lrM_sum_gfun (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (hΔ : 0 < Δ)
    (hsum : (∑ v : Vtx G, Sfun A B W v) = 2 * (dispCount A B W : ℝ)) :
    ∑ v : Vtx G, gfun A B W v = (dispCount A B W : ℝ) / Δ := by
  simp only [gfun]
  rw [← Finset.sum_div, hsum]
  have hne : (Δ : ℝ) ≠ 0 := by exact_mod_cast hΔ.ne'
  field_simp
  try ring

/-- `MForm = ⟨1_R, M 1_R⟩` written in terms of `gfun = Sfun/(2Δ)`: the factor `2Δ` cancels
against the `1/2` in the definition of `MForm`. -/
lemma lrM_MForm_eq (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (hΔ : 0 < Δ) :
    MForm A B W = (Δ : ℝ) * ∑ v : Vtx G, gfun A B W v * Qfun A B W v := by
  have hne : (Δ : ℝ) ≠ 0 := by exact_mod_cast hΔ.ne'
  have h : ∀ v : Vtx G, Sfun A B W v * Qfun A B W v
      = 2 * (Δ : ℝ) * (gfun A B W v * Qfun A B W v) := by
    intro v
    have hg : Sfun A B W v = 2 * (Δ : ℝ) * gfun A B W v := by
      simp only [gfun]
      field_simp
      try ring
    rw [hg]; ring
  simp only [MForm]
  rw [Finset.sum_congr rfl (fun v _ => h v), ← Finset.mul_sum]
  ring

/-- The `M`-form of `1_R` is bounded by `|R|` up to the factor `Δ`: since `gfun v ≤ 1` and
`Σ_v Sfun v = 2|R|`, we get `Δ Σ_v gfun v² = Σ_v Sfun v²/(4Δ) ≤ Σ_v Sfun v/2 = |R|`. -/
lemma lrM_Delta_sum_sq_le (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (hΔ : 0 < Δ)
    (hsum : (∑ v : Vtx G, Sfun A B W v) = 2 * (dispCount A B W : ℝ)) :
    (Δ : ℝ) * ∑ v : Vtx G, gfun A B W v ^ 2 ≤ (dispCount A B W : ℝ) := by
  have hkey : ∀ v : Vtx G, (Δ : ℝ) * gfun A B W v ^ 2 ≤ Sfun A B W v / 2 := by
    intro v
    have hx0 := lrM_Sfun_nonneg A B W v
    have hx1 := lrM_Sfun_le A B W v
    simp only [gfun]
    rw [div_pow]
    field_simp
    nlinarith
  calc (Δ : ℝ) * ∑ v, gfun A B W v ^ 2
      = ∑ v, (Δ : ℝ) * gfun A B W v ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ v, Sfun A B W v / 2 := Finset.sum_le_sum (fun v _ => hkey v)
    _ = (∑ v, Sfun A B W v) / 2 := by rw [Finset.sum_div]
    _ = (dispCount A B W : ℝ) := by rw [hsum]; ring

/-! ## The main bound -/

/-- **Upper bound for the `M`-operator.** With `Sfun = rA + rB`, `gfun = Sfun/(2Δ)` (the average of
`1_R` over the edges through a vertex) and `MForm = ½ ∑_v Sfun v * M0 (gfun) v = ⟨1_R, M 1_R⟩`
(where `M = Up ∘ M₀ ∘ Down`), the quadratic form is at most `|R| (p + μ(1-p))` with
`p = |R|/(4Δ|G|) = |R|/|E|`. Proof: decompose `gfun = p·1 + ĝ` with `Σ ĝ = 0`; `M0 1 = 1` and `M0`
preserves sums, so `MForm = p|R| + Δ⟨ĝ, M0 ĝ⟩ ≤ p|R| + Δμ‖ĝ‖²`; and
`Δ‖ĝ‖² = ΔΣ gfun² - p²|E| ≤ |R| - p|R|` since `Σ_v Sfun v = 2|R|` (hypothesis `hsum`) and
`Sfun v ≤ 2Δ`, so `ΔΣ gfun² = Σ Sfun²/(4Δ) ≤ Σ Sfun/2 = |R|`. -/
theorem lr_M_case {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (μ : ℝ)
    (hΔ : 0 < Δ) (hμ : 0 ≤ μ)
    (hgap : ∀ h : Vtx G → ℝ, (∑ v, h v) = 0 →
      ∑ v, h v * M0 A B h v ≤ μ * ∑ v, h v ^ 2)
    (hsum : (∑ v : Vtx G, Sfun A B W v) = 2 * (dispCount A B W : ℝ)) :
    MForm A B W ≤ (dispCount A B W : ℝ) *
      ((dispCount A B W : ℝ) / (4 * Δ * Fintype.card G)
        + μ * (1 - (dispCount A B W : ℝ) / (4 * Δ * Fintype.card G))) := by
  classical
  have hΔ0 : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hΔne : (Δ : ℝ) ≠ 0 := hΔ0.ne'
  have hNpos : (0 : ℝ) < (Fintype.card G : ℝ) := by
    have h : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast h
  -- Abbreviate `|R| = dispCount`, `|G| = N`, `p = |R|/(4Δ|G|)`; this rewrites the goal to
  -- `MForm ≤ R * (p + μ * (1 - p))`.
  set R : ℝ := (dispCount A B W : ℝ) with hRdef
  set N : ℝ := (Fintype.card G : ℝ) with hNdef
  set p : ℝ := R / (4 * (Δ : ℝ) * N) with hpdef
  have hVcard : (Fintype.card (Vtx G) : ℝ) = 4 * N := by
    rw [lrM_card_Vtx]; rw [hNdef]
    push_cast
    ring
  -- The mean-zero part of `gfun`.
  set ĝ : Vtx G → ℝ := fun v => gfun A B W v - p with hĝdef
  have hsumg : ∑ v : Vtx G, gfun A B W v = R / (Δ : ℝ) := by
    rw [lrM_sum_gfun A B W hΔ hsum, hRdef]
  have h4ΔNp : 4 * (Δ : ℝ) * N * p = R := by
    rw [hpdef]; field_simp; try ring
  have h4Np : 4 * N * p = R / (Δ : ℝ) := by
    rw [eq_div_iff hΔne]
    linarith [h4ΔNp]
  have hĝ0 : ∑ v : Vtx G, ĝ v = 0 := by
    rw [hĝdef, lrM_sum_sub_const, hVcard, hsumg, h4Np]
    ring
  have hM0ĝ0 : ∑ v : Vtx G, M0 A B ĝ v = 0 := by
    rw [lrM_sum_M0 A B hΔ ĝ, hĝ0]
  have hgv : ∀ v : Vtx G, gfun A B W v = p + ĝ v := by
    intro v; rw [hĝdef]; ring
  have hQv : ∀ v : Vtx G, Qfun A B W v = p + M0 A B ĝ v := by
    intro v
    have hfun : (fun u : Vtx G => p + ĝ u) = gfun A B W := by
      funext u; exact (hgv u).symm
    show M0 A B (gfun A B W) v = p + M0 A B ĝ v
    rw [← hfun]
    exact lrM_M0_const_add A B hΔ p ĝ v
  have hexp : ∑ v : Vtx G, (p + ĝ v) * (p + M0 A B ĝ v)
      = 4 * N * p ^ 2 + ∑ v, ĝ v * M0 A B ĝ v := by
    rw [lrM_sum_add_mul_add ĝ (M0 A B ĝ) p hĝ0 hM0ĝ0, hVcard]
  have hĝsq : ∑ v : Vtx G, ĝ v ^ 2
      = (∑ v, gfun A B W v ^ 2) - 2 * p * (R / (Δ : ℝ)) + 4 * N * p ^ 2 := by
    rw [hĝdef, lrM_sum_sq_sub_const, hVcard, hsumg]
  have h4NΔp2 : (Δ : ℝ) * (4 * N * p ^ 2) = p * R := by
    linear_combination p * h4ΔNp
  have h2pR : (Δ : ℝ) * (2 * p * (R / (Δ : ℝ))) = 2 * p * R := by
    field_simp; try ring
  have hvar : (Δ : ℝ) * ∑ v : Vtx G, ĝ v ^ 2
      = (Δ : ℝ) * (∑ v, gfun A B W v ^ 2) - p * R := by
    rw [hĝsq, mul_add, mul_sub, h2pR, h4NΔp2]
    ring
  calc MForm A B W
      = (Δ : ℝ) * ∑ v, gfun A B W v * Qfun A B W v := lrM_MForm_eq A B W hΔ
    _ = (Δ : ℝ) * ∑ v, (p + ĝ v) * (p + M0 A B ĝ v) := by
          congr 1
          apply Finset.sum_congr rfl
          intro v _
          rw [hgv v, hQv v]
    _ = (Δ : ℝ) * (4 * N * p ^ 2 + ∑ v, ĝ v * M0 A B ĝ v) := by rw [hexp]
    _ = p * R + (Δ : ℝ) * (∑ v, ĝ v * M0 A B ĝ v) := by
          rw [mul_add, h4NΔp2]
    _ ≤ p * R + (Δ : ℝ) * (μ * ∑ v, ĝ v ^ 2) := by
          have hg := hgap ĝ hĝ0
          have h1 : (Δ : ℝ) * (∑ v, ĝ v * M0 A B ĝ v)
              ≤ (Δ : ℝ) * (μ * ∑ v, ĝ v ^ 2) :=
            mul_le_mul_of_nonneg_left hg hΔ0.le
          linarith
    _ = p * R + μ * ((Δ : ℝ) * ∑ v, ĝ v ^ 2) := by ring
    _ = p * R + μ * ((Δ : ℝ) * (∑ v, gfun A B W v ^ 2) - p * R) := by rw [hvar]
    _ ≤ p * R + μ * (R - p * R) := by
          have hb := lrM_Delta_sum_sq_le A B W hΔ hsum
          nlinarith [hμ, hb]
    _ = R * (p + μ * (1 - p)) := by ring

end Work.LT
