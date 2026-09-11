import Submission.MatrixFacts

open EquiangularLinesFixedAngle
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

/-! A crude Gerzon-type bound: at most `d²` unit vectors in `𝔼^d` can have pairwise inner
products of absolute value `< 1`. (Any bound suffices to make the `sSup` in the definition of
`N` behave like a genuine maximum.) -/

abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The rank-one operator `x ↦ ⟪u, x⟫ • u`. -/
noncomputable def rankOne {d : ℕ} (u : Euc d) : Euc d →ₗ[ℝ] Euc d where
  toFun x := ⟪u, x⟫ • u
  map_add' x y := by
    rw [inner_add_right, add_smul]
  map_smul' a x := by
    rw [inner_smul_right]
    simp [smul_smul]

lemma rankOne_apply {d : ℕ} (u x : Euc d) : rankOne u x = ⟪u, x⟫ • u := rfl

/-- Linear independence of rank-one operators of an equiangular family. -/
lemma linearIndependent_rankOne {α : ℝ} {n d : ℕ} (v : Fin n → Euc d)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) :
    LinearIndependent ℝ (fun i : Fin n => rankOne (v i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hα2lt : α ^ 2 < 1 := by nlinarith [sq_nonneg α]
  -- For every l, applying the zero combination to v l and taking inner product with v l:
  have hmain : ∀ l : Fin n, c l + α ^ 2 * ((∑ i : Fin n, c i) - c l) = 0 := by
    intro l
    have happ : (∑ i : Fin n, c i • rankOne (v i)) (v l) = 0 := by
      simpa using congrArg (fun T : Euc d →ₗ[ℝ] Euc d => T (v l)) hc
    have hvec : (∑ i : Fin n, (c i • ⟪v i, v l⟫) • v i) = 0 := by
      have hsum_app : (∑ i : Fin n, c i • rankOne (v i)) (v l)
          = ∑ i : Fin n, (c i • ⟪v i, v l⟫) • v i := by
        simp [rankOne, Finset.sum_apply, Pi.smul_apply, smul_smul]
      simpa [hsum_app] using happ
    have hinner : ∑ i : Fin n, c i * ⟪v i, v l⟫ * ⟪v i, v l⟫ = 0 := by
      have h0 := congrArg (fun w : Euc d => ⟪w, v l⟫) hvec
      simpa [sum_inner, inner_smul_left, star_trivial] using h0
    have hdiag : ⟪v l, v l⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hvnorm l]
      norm_num
    -- split off i = l
    have hmain_erase : (∑ i ∈ Finset.univ.erase l, c i * α ^ 2) + c l = 0 := by
      have h1 := hinner
      -- h1 : ∑ x ∈ univ, c x * ⟨vx,vl⟩ * ⟨vx,vl⟩ = 0
      rw [← Finset.sum_erase_add (s := Finset.univ) (f := fun i : Fin n => c i * ⟪v i, v l⟫ * ⟪v i, v l⟫) (Finset.mem_univ l)] at h1
      -- erase part: rewrite ⟨vi,vl⟩² = α² for i ≠ l
      have herase : (∑ i ∈ Finset.univ.erase l, c i * ⟪v i, v l⟫ * ⟪v i, v l⟫)
          = ∑ i ∈ Finset.univ.erase l, c i * α ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ l := Finset.ne_of_mem_erase hi
        have hpair := hvangle hne
        have hval : ⟪v i, v l⟫ = α ∨ ⟪v i, v l⟫ = -α := eq_or_eq_neg_of_abs_eq hpair
        rcases hval with hp | hn
        · rw [hp]
          ring
        · rw [hn]
          ring
      rw [herase] at h1
      rw [hdiag] at h1
      ring_nf at h1
      exact h1
    -- move to total-sum form
    have htot : (∑ i ∈ Finset.univ.erase l, c i) = (∑ i : Fin n, c i) - c l := by
      exact Finset.sum_erase_eq_sub (s := Finset.univ) (f := fun i : Fin n => c i) (a := l) (Finset.mem_univ l)
    have hfac : (∑ i ∈ Finset.univ.erase l, c i * α ^ 2) = α ^ 2 * (∑ i ∈ Finset.univ.erase l, c i) := by
      calc
        (∑ i ∈ Finset.univ.erase l, c i * α ^ 2) = (∑ i ∈ Finset.univ.erase l, α ^ 2 * c i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = α ^ 2 * (∑ i ∈ Finset.univ.erase l, c i) := by
          rw [← Finset.mul_sum]
    have hres : (∑ i ∈ Finset.univ.erase l, c i * α ^ 2) = α ^ 2 * ((∑ i : Fin n, c i) - c l) := by
      rw [hfac, htot]
    nlinarith
  -- all c's equal
  have hceq : ∀ l m : Fin n, c l = c m := by
    intro l m
    have h1 := hmain l
    have h2 := hmain m
    have : (α ^ 2 - 1) * (c l - c m) = 0 := by nlinarith
    have hcoef : α ^ 2 - 1 ≠ 0 := by nlinarith
    have : c l - c m = 0 := (mul_eq_zero.mp this).resolve_left hcoef
    linarith
  -- force c = 0 using the equation at any index
  intro i
  have h1 := hmain i
  have hsum : (∑ j : Fin n, c j) = (Fintype.card (Fin n) : ℝ) * c i := by
    calc
      (∑ j : Fin n, c j) = ∑ j : Fin n, c i := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hceq j i
      _ = (Fintype.card (Fin n) : ℝ) * c i := by
        rw [Finset.sum_const, nsmul_eq_mul]
        simp
  have hcard : (1 : ℝ) ≤ (Fintype.card (Fin n) : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
  have hzero : c i * (1 + α ^ 2 * ((Fintype.card (Fin n) : ℝ) - 1)) = 0 := by nlinarith
  have hcoef : 1 + α ^ 2 * ((Fintype.card (Fin n) : ℝ) - 1) ≠ 0 := by
    have : 0 ≤ α ^ 2 * ((Fintype.card (Fin n) : ℝ) - 1) := by positivity
    nlinarith
  exact (mul_eq_zero.mp hzero).resolve_right hcoef

/-- The space of linear operators on `𝔼^d` has dimension `d²`. -/
lemma finrank_linearMap_Euc (d : ℕ) : Module.finrank ℝ (Euc d →ₗ[ℝ] Euc d) = d ^ 2 := by
  classical
  rw [Module.finrank_linearMap ℝ ℝ (Euc d) (Euc d)]
  have hd : Module.finrank ℝ (Euc d) = d := by
    rw [Module.finrank_eq_card_basis (EuclideanSpace.basisFun (Fin d) ℝ).toBasis, Fintype.card_fin]
  rw [hd]
  ring

/-- At most `d²` unit vectors in `𝔼^d` with pairwise `|⟨v i, v j⟩| = α` (`0 < α < 1`). -/
lemma card_le_sq {α : ℝ} {n d : ℕ} (v : Fin n → Euc d)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hvnorm : ∀ i, ‖v i‖ = 1)
    (hvangle : ∀ ⦃i j : Fin n⦄, i ≠ j → |⟪v i, v j⟫| = α) : n ≤ d ^ 2 := by
  classical
  have hli := linearIndependent_rankOne v hα0 hα1 hvnorm hvangle
  have hle := hli.fintype_card_le_finrank
  simpa [finrank_linearMap_Euc] using hle

end Submission
