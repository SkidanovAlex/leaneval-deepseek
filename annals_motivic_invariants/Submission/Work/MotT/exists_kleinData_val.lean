import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotT.valAux
import Submission.Work.MotT.exists_eval_one_add_pow_ne_zero
import Submission.Work.MotT.exists_kleinData_kleinParam

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/MotT/exists_kleinData_val` — node T7

The target theorem `Work.MotT.exists_kleinData_val` asks for a `Good` Klein model whose Klein
parameters `(a, b)` are *units* at a discrete valuation `v` with uniformizer `π`
(`v π = vOne`), uniformly in the characteristic `≠ 5`.

## The piece of the argument that lives here

The mathematical content of T7 splits into three cleanly separated pieces:

1. **the parametric Klein model** in the "Klein parameter" normalisation `(a, b) = (u, 1)`,
   delegated as `Work.MotT.exists_kleinData_kleinParam`; the construction (the Pfaffian quintic
   `C_{u,1}`, its Weierstrass model, the coordinate matrix and the two order-5 symmetries that
   make `T_diag` true) is documented in `Submission/Work/MotT/GUIDE_T7.md`;
2. **avoidance of the finitely many bad values of `m`**, delegated as
   `Work.MotT.exists_eval_one_add_pow_ne_zero`: `u := 1 + π ^ m` must avoid the finite `bad` set
   of piece 1 and the roots of `X ^ 10 - 11 X ^ 5 - 1`;
3. **the elementary valuation step** (`valAux.lean` + this file): `v (1 + π ^ m) = 1`, so that
   `a = u = 1 + π ^ m` and `b = 1` are units; `K` is infinite (a uniformizer has infinitely many
   distinct powers), which is the hypothesis under which piece 1 is stated.

The assembly `exists_kleinData_val_of_pieces` below takes pieces 1 and 2 as *hypotheses*, so
nothing here depends on them; it is stated in the exact shape in which the two delegated lemmas
supply them, so the final proof of `exists_kleinData_val` is a three-line application.

The normalisation `Work.MotT.vOne = ofAdd (-1)` in `ℤᵐ⁰` is the one in which `v u = 1` means that
`u` is a unit and `v π = vOne` that `π` is a uniformizer: indeed
`v (1 + π ^ m) = max (v 1) (v (π ^ m)) = max 1 (vOne ^ m) = 1` for `m ≥ 1`, because
`vOne ^ m < 1` (`Valuation.map_add_of_distinct_val`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
open scoped WithZero
open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotT

noncomputable section

/-! ## §1 Elementary properties of `π` and of `1 + π ^ m` -/

/-- A uniformizer is nonzero. -/
lemma pi_ne_zero {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) {π : K}
    (hπ : v π = vOne) : π ≠ 0 := by
  intro h0
  rw [h0, Valuation.map_zero] at hπ
  exact WithZero.coe_ne_zero hπ.symm

/-- The powers of a uniformizer are pairwise distinct. -/
lemma pow_pi_injective {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    {π : K} (hπ : v π = vOne) : Function.Injective fun m : ℕ => π ^ m := by
  intro m m' h
  have h' : π ^ m = π ^ m' := h
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exfalso
    have h1 : π ^ (m' - m) = 1 := by
      have h2 : π ^ m * π ^ (m' - m) = π ^ m * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le, h', mul_one]
      exact mul_left_cancel₀ (pow_ne_zero m (pi_ne_zero v hπ)) h2
    have hv : vOne ^ (m' - m) = 1 := by
      rw [← hπ, ← Valuation.map_pow, h1, Valuation.map_one]
    exact absurd hv (ne_of_lt (vOne_pow_lt_one (Nat.sub_pos_of_lt hlt)))
  · exact heq
  · exfalso
    have h1 : π ^ (m - m') = 1 := by
      have h2 : π ^ m' * π ^ (m - m') = π ^ m' * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' hgt.le, ← h', mul_one]
      exact mul_left_cancel₀ (pow_ne_zero m' (pi_ne_zero v hπ)) h2
    have hv : vOne ^ (m - m') = 1 := by
      rw [← hπ, ← Valuation.map_pow, h1, Valuation.map_one]
    exact absurd hv (ne_of_lt (vOne_pow_lt_one (Nat.sub_pos_of_lt hgt)))

/-- A field carrying a valuation with a uniformizer is infinite.  (This is what makes the
`[Infinite K]` hypothesis of the parametric Klein model available in T7.) -/
lemma infinite_of_uniformizer {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    {π : K} (hπ : v π = vOne) : Infinite K :=
  Infinite.of_injective _ (pow_pi_injective v hπ)

/-- The map `m ↦ 1 + π ^ m` is injective. -/
lemma one_add_pow_injective {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    {π : K} (hπ : v π = vOne) : Function.Injective fun m : ℕ => 1 + π ^ m := by
  intro m m' h
  exact pow_pi_injective v hπ (add_left_cancel h)

/-- `1 + π ^ m ≠ 0` for `0 < m` (it is a unit). -/
lemma one_add_pow_ne_zero {K : Type} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    {π : K} (hπ : v π = vOne) (m : ℕ) (hm : 0 < m) : (1 + π ^ m) ≠ 0 := by
  intro h
  have h1 := v_one_add_pow_pi v hπ m hm
  rw [h, Valuation.map_zero] at h1
  exact zero_ne_one h1

/-! ## §2 Choosing `m` so that `1 + π ^ m` avoids a fixed finite set -/

/-- For any finite set `bad ⊆ K` the values `1 + π ^ m` avoid `bad` for all large `m`. -/
lemma exists_forall_one_add_pow_notMem {K : Type} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) {π : K} (hπ : v π = vOne)
    (bad : Finset K) : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 1 + π ^ m ∉ bad := by
  have hpre : ((fun m : ℕ => 1 + π ^ m) ⁻¹' (bad : Set K)).Finite :=
    Set.Finite.preimage ((one_add_pow_injective v hπ).injOn) bad.finite_toSet
  obtain ⟨M, hM⟩ := hpre.bddAbove
  exact ⟨M + 1, fun m hm hmem => by have := hM hmem; omega⟩

/-! ## §3 The Klein discriminant condition `u ^ 10 - 11 * u ^ 5 - 1 ≠ 0` -/

/-- The polynomial `X ^ 10 - 11 * X ^ 5 - 1` is nonzero (its `X ^ 10`-coefficient is `1`). -/
lemma X_pow_ten_sub_C_mul_X_pow_five_sub_C_one_ne_zero (K : Type) [Field K] :
    (Polynomial.X ^ 10 - Polynomial.C (11 : K) * Polynomial.X ^ 5 - Polynomial.C 1 :
      Polynomial K) ≠ 0 := by
  intro h
  have hc : (Polynomial.X ^ 10 - Polynomial.C (11 : K) * Polynomial.X ^ 5 - Polynomial.C 1 :
      Polynomial K).coeff 10 = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow_self, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    norm_num
  rw [h, Polynomial.coeff_zero] at hc
  exact one_ne_zero hc.symm

/-! ## §4 The assembly -/

/-- **Assembly of T7.**  Given the parametric Klein model in the normalisation `(a, b) = (u, 1)`
(`Work.MotT.exists_kleinData_kleinParam`), the target `exists_kleinData_val` follows by taking
`u := 1 + π ^ m` for large `m`: then `u` is a unit (`v_one_add_pow_pi`), `b = 1` is a unit, and the
two excluded conditions hold by construction of `m` (the finite bad set of the parametric model,
and `X ^ 10 - 11 * X ^ 5 - 1 ≠ 0`, which is
`Work.MotT.exists_eval_one_add_pow_ne_zero`). -/
theorem exists_kleinData_val_of_pieces {K : Type} [Field K] (hk : ringChar K ≠ 5)
    (v : Valuation K (WithZero (Multiplicative ℤ))) {π : K} (hπ : v π = vOne)
    (hparam : ∃ bad : Finset K, ∀ u : K, u ∉ bad → u ≠ 0 → u ^ 10 - 11 * u ^ 5 - 1 ≠ 0 →
      ∃ D : Work.MotV.KleinData K, D.Good ∧ D.a = u ∧ D.b = 1) :
    ∃ D : Work.MotV.KleinData K, D.Good ∧ v D.a = 1 ∧ v D.b = 1 := by
  obtain ⟨bad, hbad⟩ := hparam
  obtain ⟨M₁, hM₁⟩ := exists_eval_one_add_pow_ne_zero v hπ _
    (X_pow_ten_sub_C_mul_X_pow_five_sub_C_one_ne_zero K)
  obtain ⟨M₂, hM₂⟩ := exists_forall_one_add_pow_notMem v hπ bad
  have hm₁ : M₁ ≤ max M₁ M₂ + 1 := by omega
  have hm₂ : M₂ ≤ max M₁ M₂ + 1 := by omega
  have hpos : 0 < max M₁ M₂ + 1 := by omega
  have hne : (1 + π ^ (max M₁ M₂ + 1)) ≠ 0 := one_add_pow_ne_zero v hπ _ hpos
  have hΔ : (1 + π ^ (max M₁ M₂ + 1)) ^ 10 - 11 * (1 + π ^ (max M₁ M₂ + 1)) ^ 5 - 1 ≠ 0 := by
    have h1 := hM₁ _ hm₁
    have h2 : (Polynomial.X ^ 10 - Polynomial.C (11 : K) * Polynomial.X ^ 5 -
        Polynomial.C 1 : Polynomial K).eval (1 + π ^ (max M₁ M₂ + 1)) =
        (1 + π ^ (max M₁ M₂ + 1)) ^ 10 - 11 * (1 + π ^ (max M₁ M₂ + 1)) ^ 5 - 1 := by
      simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
    rwa [h2] at h1
  obtain ⟨D, hD, ha, hb⟩ := hbad _ (hM₂ _ hm₂) hne hΔ
  refine ⟨D, hD, ?_, ?_⟩
  · rw [ha]; exact v_one_add_pow_pi v hπ _ hpos
  · rw [hb, Valuation.map_one]

/-- **T7.** Klein data with *unit* Klein parameters at a discrete valuation: the `(a, b)` are units
(`v a = v b = 1`), which is exactly the hypothesis of the twisted-point valuation lemma
`Work.MotV.Work.MotV.tp`.  This is the node that makes the T-route available over an arbitrary base
field with a valuation, uniformly in the characteristic `≠ 5`.

Route (`MOTIVIC_C6_R4_LEAD.md` §3.3, T7): take a KDATA family in the *Klein* parameter `(u : 1)`
(the Tate normal form `y² + (1-b)xy - by = x³ - bx²` with the Klein coordinates in the basis
`1, x, y, x², xy` of `𝓛(5O)`, as described in `Submission/Work/MotK/GUIDE.md`; the model, `E` and the
coordinate matrix are polynomial in the parameter over `ℤ[u, 1/Δ(u)]`, `Δ(u) = u(u¹⁰ - 11u⁵ - 1)`;
the CAS script `Papers/motivic_cas/tlink.py` is the template).  Choose `u = 1 + π^m` with `m` large
enough that `Δ(u) ≠ 0`, `j(u) ≠ 0` and `j(u) ≠ 1728`: these are finitely many nonzero polynomial
conditions in every characteristic `≠ 5`, so a suitable `m` exists, and `v u = 1` because
`v 1 = 0 > -m = v (π^m)`; then `a := u`, `b := 1` are units.
`Work.MotT.kleinData_normalise` and `Work.MotT.kleinP_smul_ab` are available for the rescaling.

**Status: proved.**  The parametric model is
`Work.MotT.exists_kleinData_kleinParam` (`Submission/Work/MotT/KleinParamData.lean` and the sibling
`kpData_*` modules: the universal curve over `X(5)`, with `T_diag` from
`Work.MotT.kpData_T_diag`), and the valuation argument is
`Work.MotT.exists_kleinData_val_of_pieces`; the two lines below are the whole proof.

Note that a *non-parametric* `Good` model cannot be used here: its parameters cannot in general be
made units, since `Work.MotT.kleinP_smul_ab` only rescales `(a, b)` by a common unit, which
preserves `v a − v b`. -/
theorem exists_kleinData_val {K : Type} [Field K] (hk : ringChar K ≠ 5)
    (v : Valuation K (WithZero (Multiplicative ℤ))) {π : K} (hπ : v π = Work.MotT.vOne) :
    ∃ D : Work.MotV.KleinData K, D.Good ∧ v D.a = 1 ∧ v D.b = 1 := by
  haveI : Infinite K := infinite_of_uniformizer v hπ
  exact exists_kleinData_val_of_pieces hk v hπ (exists_kleinData_kleinParam hk)

end

end Work.MotT
