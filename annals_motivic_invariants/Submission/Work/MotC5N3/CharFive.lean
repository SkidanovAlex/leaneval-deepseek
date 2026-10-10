import Mathlib
import ChallengeDeps
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotT.Defs
import Submission.Work.MotV5.tp_as
import Submission.Work.MotV5.D11_shift_kp
import Submission.Work.MotV5.exists_kleinData_ASGood

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Part N of the characteristic-`5`, `n = 3` route: valuation arithmetic

This is Part N of `MOTIVIC_CHAR5_N3_LEAD.md` Appendix A, at the general base field `K` (the design
namespace was `Work.MotASG`).

* `exp_one_ne_pow_five` — `exp 1` is not a fifth power in `ℤᵐ⁰` (N1);
* `val_eq_one_of_pow_four`, `val_inv_uniformizer` — the valuation of `π⁻¹` for a uniformiser `π` (N2);
* `not_mem_pe_inv_uniformizer` — `π⁻¹ ∉ ℘(K)` (N3);
* `rigidity_AS_val_of_lam` — rigidity of the AS link at a place, from the node `lam_AS` (N4);
* `not_gen_three_of_val_charFive_of_nodes` — `¬ GenByPseudoRegularizable K 3` for every infinite
  field `K` of characteristic `5` with a discrete valuation, from the nodes G-DATA, G-EQ, G-CO,
  G-LAM, G-LK (N5).

The two results that quote a port node take that node's *statement* as a hypothesis, so that this
module compiles independently of the port; the unconditional versions are obtained by applying them
to `Work.MotC5N3.lam_AS` and `Work.MotC5N3.linkCertAS` once those land.
-/

set_option autoImplicit false
open scoped WithZero

namespace Work.MotC5N3
noncomputable section

open Work.MotC5N3

/-- **N1** `exp 1` is not a fifth power in `ℤᵐ⁰`. -/
theorem exp_one_ne_pow_five (x : ℤᵐ⁰) : x ^ 5 ≠ WithZero.exp 1 := by
  intro h
  by_cases hx : x = 0
  · rw [hx] at h; simp at h; exact WithZero.exp_ne_zero h.symm
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = WithZero.exp k := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h
    push_cast at h
    omega

/-- **N2** a valuation is trivial on elements with `c ^ 4 = 1` (the nonzero prime-field elements in
characteristic `5`). -/
theorem val_eq_one_of_pow_four {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {c : K}
    (hc : c ^ 4 = 1) : v c = 1 := by
  have h := congrArg v hc
  rw [map_pow, map_one] at h
  rcases lt_trichotomy (v c) 1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le hlt (by norm_num)))
  · exact heq
  · exact absurd h (ne_of_gt (one_lt_pow₀ hgt (by norm_num)))

/-- the value of `π⁻¹` (part of N2). -/
theorem val_inv_uniformizer {K : Type} [Field K] (v : Valuation K ℤᵐ⁰) {π : K}
    (hπ : v π = Work.MotT.vOne) : v π⁻¹ = WithZero.exp 1 := by
  rw [map_inv₀, hπ]
  show (WithZero.exp (-1 : ℤ))⁻¹ = _
  rw [← WithZero.exp_neg, neg_neg]

/-- **N3** the AS class `π⁻¹` (pole of order one) is not in `℘(K)`. -/
theorem not_mem_pe_inv_uniformizer {K : Type} [Field K] [CharP K 5] (v : Valuation K ℤᵐ⁰)
    {π : K} (hπ : v π = Work.MotT.vOne) : ¬ ∃ u : K, u ^ 5 - u = π⁻¹ := by
  rintro ⟨u, hu⟩
  have hg := val_inv_uniformizer v hπ
  rw [← hu] at hg
  have h1 : (1 : ℤᵐ⁰) < WithZero.exp 1 := by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  by_cases hu1 : v u ≤ 1
  · have : v (u ^ 5 - u) ≤ 1 := by
      refine le_trans (Valuation.map_sub v _ _) (max_le ?_ hu1)
      rw [map_pow]; exact pow_le_one₀ zero_le hu1
    exact absurd (hg ▸ this) (not_le.mpr h1)
  · push Not at hu1
    have hlt : v u < v (u ^ 5) := by
      rw [map_pow]
      calc v u = v u ^ 1 := (pow_one _).symm
        _ < v u ^ 5 := pow_lt_pow_right₀ hu1 (by norm_num)
    rw [Valuation.map_sub_eq_of_lt_left v hlt, map_pow] at hg
    exact exp_one_ne_pow_five _ hg

/-- The node `lam_AS` (G-LAM) as a hypothesis: a `K`-isomorphism of two AS twist fields gives a
`K`-point of the twist by `f₁ - ε f₂`, `ε = ±1`. -/
abbrev LamASStatement : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : K)
    (τ₁ τ₂ : OmA K D ≃ₐ[K] OmA K D) (σS : OmA K D ≃ₐ[KbA K] OmA K D)
    (σ₁ σ₂ : KbA K ≃ₐ[K] KbA K)
    (h1 : ASTwistData 𝕜 D f₁ τ₁ σS σ₁) (h2 : ASTwistData 𝕜 D f₂ τ₂ σS σ₂),
    (↥(asTwistFieldTrue D f₁ τ₁ σS) ≃ₐ[K] ↥(asTwistFieldTrue D f₂ τ₂ σS)) →
    ∃ (ε : ℤ) (_ : ε = 1 ∨ ε = -1) (y : Fin 5 → K), y ≠ 0 ∧
      ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (KbA K) D.a) (algebraMap 𝕜 (KbA K) D.b)
        (Work.MotV.asCoord (asRoot (f₁ - algebraMap 𝕜 K ((ε : ℤ) : 𝕜) * f₂))
          (fun j => algebraMap K (KbA K) (y j))) k = 0

/-- **N4 = RIG_K**, from the port node G-LAM: rigidity of the AS link at a place — the twists by
`π⁻¹` and `2 π⁻¹` are not `K`-isomorphic. -/
theorem rigidity_AS_val_of_lam (hlam : LamASStatement) (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    {K : Type} [Field K] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (v : Valuation K ℤᵐ⁰) (ha : v (algebraMap 𝕜 K D.a) = 1) (hb : v (algebraMap 𝕜 K D.b) = 1)
    (hab : v (algebraMap 𝕜 K (D.a ^ 2 - D.a * D.b - D.b ^ 2)) = 1)
    {π : K} (hπ : v π = Work.MotT.vOne)
    (τ τ₂ : OmA K D ≃ₐ[K] OmA K D) (σS : OmA K D ≃ₐ[KbA K] OmA K D) (σ σ₂ : KbA K ≃ₐ[K] KbA K)
    (h1 : ASTwistData 𝕜 D π⁻¹ τ σS σ) (h2 : ASTwistData 𝕜 D (2 • π⁻¹) τ₂ σS σ₂) :
    IsEmpty (↥(asTwistFieldTrue D π⁻¹ τ σS) ≃ₐ[K] ↥(asTwistFieldTrue D (2 • π⁻¹) τ₂ σS)) := by
  haveI : CharP K 5 := charP_of_injective_algebraMap (algebraMap 𝕜 K).injective 5
  refine ⟨fun θ => ?_⟩
  obtain ⟨ε, hε, y, hy, heq⟩ := hlam 𝕜 D hD π⁻¹ (2 • π⁻¹) τ τ₂ σS σ σ₂ h1 h2 θ
  set c : K := 1 - 2 * (ε : K) with hc
  have hgc : π⁻¹ - algebraMap 𝕜 K ((ε : ℤ) : 𝕜) * (2 • π⁻¹) = c * π⁻¹ := by
    rw [map_intCast, two_smul, hc]; ring
  have h5 : (5 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 5
  have hc4 : c ^ 4 = 1 := by
    rcases hε with rfl | rfl
    · rw [hc]; push_cast; ring
    · rw [hc]; push_cast; linear_combination (16 : K) * h5
  have hval : v (c * π⁻¹) = WithZero.exp 1 := by
    rw [map_mul, val_eq_one_of_pow_four v hc4, one_mul, val_inv_uniformizer v hπ]
  have h1lt : (1 : ℤᵐ⁰) < v (c * π⁻¹) := by
    rw [hval, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)
  have hab' : v ((algebraMap 𝕜 K D.a) ^ 2 - algebraMap 𝕜 K D.a * algebraMap 𝕜 K D.b
      - (algebraMap 𝕜 K D.b) ^ 2) = 1 := by
    simpa [map_sub, map_mul, map_pow] using hab
  have hw := asRoot_spec (c * π⁻¹)
  have heq' : ∀ k, Work.MotK.kleinP (algebraMap K (KbA K) (algebraMap 𝕜 K D.a))
      (algebraMap K (KbA K) (algebraMap 𝕜 K D.b))
      (Work.MotV.asCoord (asRoot (c * π⁻¹)) (fun j => algebraMap K (KbA K) (y j))) k = 0 := by
    intro k
    have := heq k
    rw [hgc] at this
    simpa only [← IsScalarTower.algebraMap_apply] using this
  obtain ⟨u, hu⟩ := Work.MotV5.tp_as v (asRoot (c * π⁻¹)) (c * π⁻¹) hw ha hb hab' hy heq' h1lt
  exact exp_one_ne_pow_five (v u) (hu ▸ hval)

end
end Work.MotC5N3
