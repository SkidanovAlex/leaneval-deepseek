import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.StabHorosphereBase
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.horSpec

/-!
# A parabolic element fixing `ξ` cannot commute with a level-scaling element

For `ξ ∈ Sph n`, let `δ` be a parabolic isometry fixing `ξ` and let `h` be an isometry fixing `ξ`
which shifts the horosphere levels at `ξ` (`bCocy h ξ ≠ 0`).  Then `δ` and a non-trivial power of
`h` cannot commute.

## Proof sketch

`bCocy δ ξ = 0` (`bCocy_parabolic`), so `δ` preserves every horosphere at `ξ`; by
`stabFlatAction` there are `A : E n →ₗ[ℝ] E n` and `v : E n` with `A` norm-preserving on `ξ^⊥`
such that `δ` acts on the flat coordinate `yc ξ ·` of every horosphere by `y ↦ A y + v`, keeping
the levels.  Since `δ` has no fixed point, the affine isometry `y ↦ A y + v` of `ξ^⊥` has no
fixed point, so its displacement function `F y = ‖A y + v - y‖` is bounded below by the positive
distance `c` from `v` to the closed subspace `im (A - 1)`.

Let `β = lev ξ (h • 0) > 0` be the level scaling of `h`.  The horospherical formula
`levYcFormula` for the hyperbolic distance gives, for every `u`,

`cosh (hdist u (δ • u)) = 1 + (lev ξ u)^2 * F (yc ξ u)^2 / 2`,

while `h δ = δ h` makes the displacement function `h`-invariant.  Since
`lev ξ (h • u) = β * lev ξ u`, this gives `F (yc ξ (h • u)) = F (yc ξ u) / β` for all `u`;
iterating along the orbit of the point of level `1`, flat coordinate `0`,
`c ≤ F (yc ξ (h^k • u)) = ‖v‖ / β^k` for all `k : ℕ`, which forces `β ≤ 1`.

Applying this to `h = γ^m` and to `h = γ⁻¹^m` (level scalings `β` and `β⁻¹`, both commuting with
`δ`) gives `β ≤ 1` and `β⁻¹ ≤ 1`, hence `β = 1`; but `β = exp (bCocy (γ^m) ξ) =
exp (m * bCocy γ ξ) ≠ 1`.  Contradiction.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Elementary bookkeeping -/

/-- Powers of an isometry fixing a boundary point fix it. -/
lemma pnc_bd_pow_fixed (hA : POActionProp n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n)
    (hg : bd g ξ = ξ) : ∀ k : ℕ, bd (g ^ k) ξ = ξ := by
  intro k
  induction k with
  | zero => simpa using (POBasic.ofProp hA).bd_one ξ hξ
  | succ k ih =>
      rw [pow_succ', (POBasic.ofProp hA).bd_mul g (g ^ k) ξ hξ, ih, hg]

/-- The Busemann cocycle of a power is the multiple of the cocycle. -/
lemma pnc_bCocy_pow (hA : POActionProp n) (hI : HypIsometryProp n) (g : PO n 1) {ξ : E n}
    (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ) (k : ℕ) : bCocy (g ^ k) ξ = k * bCocy g ξ := by
  induction k with
  | zero => rw [pow_zero, bCocy_one hA hI ξ hξ, Nat.cast_zero, zero_mul]
  | succ k ih =>
      rw [pow_succ', bCocy_mul hA hI g (g ^ k) ξ hξ, pnc_bd_pow_fixed hA g hξ hg k, ih,
        Nat.cast_succ]
      ring

/-- `lev ξ 0 = 1`. -/
lemma pnc_lev_zero (ξ : E n) : lev ξ (0 : E n) = 1 := by
  simp [lev, tpart, inner_zero_left]

/-! ## A lower bound for the displacement of a fixed-point-free affine isometry -/

/-- A fixed-point-free affine isometry `y ↦ A y + v` of a Euclidean space, restricted to the
hyperplane `ξ^⊥`, has a displacement function bounded below by a positive constant. -/
theorem pnc_affineDispLowerBound {n : ℕ} (A : E n →ₗ[ℝ] E n) (v : E n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (h : ∀ y : E n, inner ℝ y ξ = 0 → A y + v ≠ y) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : E n, inner ℝ y ξ = 0 → c ≤ ‖A y + v - y‖ := by
  set W : Submodule ℝ (E n) :=
    { carrier := {y | inner ℝ y ξ = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [inner_add_left, ha, hb, add_zero]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [real_inner_smul_left, ha, mul_zero] } with hW
  set S : Submodule ℝ (E n) := W.map (A - 1) with hS
  have hmem : ∀ y : E n, inner ℝ y ξ = 0 → A y - y ∈ S := by
    intro y hy
    refine ⟨y, ?_, ?_⟩
    · rw [hW]; exact hy
    · simp [LinearMap.sub_apply]
  have hnotmem : (-v) ∉ S := by
    rintro ⟨y, hy, hyv⟩
    rw [hW] at hy
    have h2 : A y - y = -v := by simpa [LinearMap.sub_apply] using hyv
    have h3 : A y + v = y := by
      calc A y + v = (A y - y) + y + v := by abel
        _ = -v + y + v := by rw [h2]
        _ = y := by abel
    exact h y hy h3
  refine ⟨Metric.infDist (-v) S, ?_, ?_⟩
  · exact ((Submodule.closed_of_finiteDimensional S).notMem_iff_infDist_pos
      ⟨0, S.zero_mem⟩).1 hnotmem
  · intro y hy
    have h1 : A y - y ∈ (S : Set (E n)) := hmem y hy
    have h2 : Metric.infDist (-v) (S : Set (E n)) ≤ dist (-v) (A y - y) :=
      Metric.infDist_le_dist_of_mem h1
    have h3 : dist (-v) (A y - y) = ‖A y + v - y‖ := by
      rw [dist_eq_norm, ← norm_neg]
      congr 1
      abel
    rwa [h3] at h2

/-! ## The main step: the level scaling of any commuting element is `≤ 1` -/

/-- If `δ` is parabolic fixing `ξ` and `h` fixes `ξ` and commutes with `δ`, then the level
scaling of `h` at `ξ` is at most `1`. -/
theorem pnc_lev_smul_le_one (hA : POActionProp n) (hI : HypIsometryProp n)
    (δ : PO n 1) (hδ : IsParabolic δ) (ξ : E n) (hξ : ξ ∈ Sph n) (hδξ : bd δ ξ = ξ)
    (h : PO n 1) (hhξ : bd h ξ = ξ) (hcomm : δ * h = h * δ) :
    lev ξ (h • (0 : E n)) ≤ 1 := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  -- `δ` preserves the Busemann function at `ξ`
  have hβ : busemann ξ (δ • (0 : E n)) = 0 := by
    simpa only [bCocy, hδξ] using bCocy_parabolic hA hI δ hδ ξ hξ hδξ
  -- the flat (horospherical) action of `δ`
  obtain ⟨A, v, hvξ, hAξ, hAnorm, hact⟩ := stabFlatAction n hA hI ξ hξ δ hδξ hβ
  have hlevδ : ∀ u : E n, lev ξ (δ • u) = lev ξ u := by
    intro u
    have hD : 0 < lev ξ u := lev_pos ξ hξ u
    have hy : inner ℝ (yc ξ u) ξ = 0 := yc_inner_orth hξ
    have hu : hptOf ξ (yc ξ u) (lev ξ u) = u := hptOf_yc ξ hξ (lev ξ u) hD u rfl
    rw [← hu, (hact (yc ξ u) (lev ξ u) hy hD).1,
      (hptOf_level ξ hξ (lev ξ u) hD (yc ξ u) hy).1]
  have hycδ : ∀ u : E n, yc ξ (δ • u) = A (yc ξ u) + v := by
    intro u
    have hD : 0 < lev ξ u := lev_pos ξ hξ u
    have hy : inner ℝ (yc ξ u) ξ = 0 := yc_inner_orth hξ
    have hu : hptOf ξ (yc ξ u) (lev ξ u) = u := hptOf_yc ξ hξ (lev ξ u) hD u rfl
    rw [← hu, (hact (yc ξ u) (lev ξ u) hy hD).2,
      (hptOf_level ξ hξ (lev ξ u) hD (yc ξ u) hy).2]
  -- the displacement formula in horospherical coordinates
  have hdisp : ∀ u : E n,
      Real.cosh (hdist u (δ • u))
        = 1 + (lev ξ u) ^ 2 * ‖A (yc ξ u) + v - yc ξ u‖ ^ 2 / 2 := by
    intro u
    have h := levYcFormula hξ u (δ • u)
    rw [hlevδ u, hycδ u, div_self (ne_of_gt (lev_pos ξ hξ u)), Real.log_one,
      Real.cosh_zero] at h
    rw [h, show ‖yc ξ u - (A (yc ξ u) + v)‖ = ‖A (yc ξ u) + v - yc ξ u‖ by
      rw [← norm_neg, neg_sub]]
    ring
  -- `δ` has no fixed flat point
  have hno : ∀ y : E n, inner ℝ y ξ = 0 → A y + v ≠ y := by
    intro y hy hyv
    have hl : lev ξ (hptOf ξ y 1) = 1 := (hptOf_level ξ hξ 1 one_pos y hy).1
    have hyc' : yc ξ (hptOf ξ y 1) = y := (hptOf_level ξ hξ 1 one_pos y hy).2
    have key : δ • (hptOf ξ y 1) = hptOf ξ y 1 := by
      rw [← hptOf_yc ξ hξ (lev ξ (δ • (hptOf ξ y 1)))
        (lev_pos ξ hξ _) (δ • (hptOf ξ y 1)) rfl]
      rw [hycδ (hptOf ξ y 1), hlevδ (hptOf ξ y 1), hyc', hyv, hl]
    exact hδ.1 _ key
  obtain ⟨c, hcpos, hcle⟩ := pnc_affineDispLowerBound A v ξ hξ hno
  -- the invariance relation `F (yc ξ (h • u)) * β = F (yc ξ u)`
  have hinv : ∀ u : E n,
      ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖ * lev ξ (h • (0 : E n))
        = ‖A (yc ξ u) + v - yc ξ u‖ := by
    intro u
    have hcommu : δ • (h • u) = h • (δ • u) := by
      rw [← hA'.mul_smul δ h u, hcomm, hA'.mul_smul h δ u]
    have heq : hdist u (δ • u) = hdist (h • u) (δ • (h • u)) := by
      rw [hcommu, hI'.isom_smul h u (δ • u)]
    have h4 : 1 + (lev ξ u) ^ 2 * ‖A (yc ξ u) + v - yc ξ u‖ ^ 2 / 2
        = 1 + (lev ξ (h • u)) ^ 2 * ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖ ^ 2 / 2 := by
      rw [← hdisp u, ← hdisp (h • u), heq]
    have h5 : lev ξ (h • u) = lev ξ u * lev ξ (h • (0 : E n)) :=
      lev_smul_self hI' hA' ξ hξ h u hhξ
    have hL : 0 < lev ξ u := lev_pos ξ hξ u
    have hβ0 : 0 < lev ξ (h • (0 : E n)) := lev_pos ξ hξ _
    have hF : 0 ≤ ‖A (yc ξ u) + v - yc ξ u‖ := norm_nonneg _
    have hF' : 0 ≤ ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖ := norm_nonneg _
    have h3 : (lev ξ u) ^ 2 * ‖A (yc ξ u) + v - yc ξ u‖ ^ 2
        = (lev ξ u) ^ 2
            * (lev ξ (h • (0 : E n)) * ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖) ^ 2 := by
      rw [h5] at h4
      have h6 : (lev ξ u * lev ξ (h • (0 : E n))) ^ 2
            * ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖ ^ 2
          = (lev ξ u) ^ 2
            * (lev ξ (h • (0 : E n)) * ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖) ^ 2 :=
        mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) (by ring)
      linarith [h4, h6]
    have key : ‖A (yc ξ u) + v - yc ξ u‖ * ‖A (yc ξ u) + v - yc ξ u‖
        = (lev ξ (h • (0 : E n)) * ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖)
            * (lev ξ (h • (0 : E n)) * ‖A (yc ξ (h • u)) + v - yc ξ (h • u)‖) := by
      rw [← pow_two, ← pow_two]
      exact mul_left_cancel₀ (ne_of_gt (pow_pos hL 2)) h3
    have hres := (mul_self_inj_of_nonneg hF (mul_nonneg (le_of_lt hβ0) hF')).mp key
    rw [hres, mul_comm]
  -- iterate along the orbit of the point of level `1` and flat coordinate `0`
  set β : ℝ := lev ξ (h • (0 : E n)) with hβdef
  have hβpos : 0 < β := lev_pos ξ hξ _
  have hbase : yc ξ (hptOf ξ (0 : E n) 1) = (0 : E n) :=
    (hptOf_level ξ hξ 1 one_pos (0 : E n) (by simp)).2
  have hiter : ∀ k : ℕ,
      ‖A (yc ξ ((h ^ k) • hptOf ξ (0 : E n) 1)) + v
          - yc ξ ((h ^ k) • hptOf ξ (0 : E n) 1)‖ = ‖v‖ / β ^ k := by
    intro k
    induction k with
    | zero =>
        simp only [pow_zero, hA'.one_smul, hbase, map_zero, zero_add, sub_zero, div_one]
    | succ k ih =>
        have hstep : (h ^ (k + 1)) • hptOf ξ (0 : E n) 1
            = h • ((h ^ k) • hptOf ξ (0 : E n) 1) := by
          rw [pow_succ', hA'.mul_smul]
        rw [hstep]
        have hkey := hinv ((h ^ k) • hptOf ξ (0 : E n) 1)
        rw [ih] at hkey
        have hβne : β ≠ 0 := ne_of_gt hβpos
        have hgoal : ‖v‖ / β ^ (k + 1) = (‖v‖ / β ^ k) / β := by
          rw [pow_succ, div_div]
        rw [hgoal, ← hkey]
        exact (eq_div_iff hβne).mpr rfl
  have hbound : ∀ k : ℕ, c ≤ ‖v‖ / β ^ k := by
    intro k
    have h1 := hcle _ (yc_inner_orth (ξ := ξ) (u := (h ^ k) • hptOf ξ (0 : E n) 1) hξ)
    rwa [hiter k] at h1
  by_contra hle
  push Not at hle
  have hlim : Filter.Tendsto (fun k : ℕ => ‖v‖ / β ^ k) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (β⁻¹) ^ k) Filter.atTop (nhds 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_lt_one
      · exact le_of_lt (inv_pos.mpr hβpos)
      · rw [inv_lt_one_iff₀]
        exact Or.inr hle
    simpa [div_eq_mul_inv, inv_pow] using h1.const_mul ‖v‖
  obtain ⟨k, hk⟩ := (hlim.eventually (eventually_lt_nhds hcpos)).exists
  exact absurd (hbound k) (not_le.mpr hk)

end

/-- A parabolic element fixing `ξ` cannot commute with an element that fixes `ξ` but shifts the
horosphere levels there. -/
theorem parabolic_not_commute_levelScaling (n : ℕ) (hn : 2 ≤ n)
    (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (δ γ : LeanEval.Geometry.MostowRigidity.PO n 1) (hδ : Submission.Mostow.IsParabolic δ)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hδξ : Submission.Mostow.bd δ ξ = ξ) (hγξ : Submission.Mostow.bd γ ξ = ξ)
    (hc : Work.Mostow.bCocy γ ξ ≠ 0) (m : ℕ) (hm : 0 < m)
    (hcomm : δ * γ ^ m = γ ^ m * δ) : False := by
  have hA' : POBasic n := POBasic.ofProp hA
  have hI' : HypIsoData n := HypIsoData.ofProp hI
  -- `γ^m` fixes `ξ` and commutes with `δ`, so its level scaling is `≤ 1`
  have hγm : bd (γ ^ m) ξ = ξ := pnc_bd_pow_fixed hA γ hξ hγξ m
  have h1 : lev ξ ((γ ^ m) • (0 : E n)) ≤ 1 :=
    pnc_lev_smul_le_one hA hI δ hδ ξ hξ hδξ (γ ^ m) hγm hcomm
  -- `γ⁻¹` fixes `ξ` and commutes with `δ` as well
  have hγi : bd γ⁻¹ ξ = ξ := by
    have h := hA'.bd_mul γ⁻¹ γ ξ hξ
    rw [inv_mul_cancel, hA'.bd_one ξ hξ, hγξ] at h
    exact h.symm
  have hγim : bd ((γ⁻¹) ^ m) ξ = ξ := pnc_bd_pow_fixed hA γ⁻¹ hξ hγi m
  have hcomm' : δ * (γ⁻¹) ^ m = (γ⁻¹) ^ m * δ := by
    have h2 : ((γ ^ m))⁻¹ * δ = δ * ((γ ^ m))⁻¹ := by
      calc ((γ ^ m))⁻¹ * δ = ((γ ^ m))⁻¹ * (δ * γ ^ m) * ((γ ^ m))⁻¹ := by group
        _ = ((γ ^ m))⁻¹ * (γ ^ m * δ) * ((γ ^ m))⁻¹ := by rw [hcomm]
        _ = δ * ((γ ^ m))⁻¹ := by group
    rw [← inv_pow] at h2
    exact h2.symm
  have h2 : lev ξ ((γ⁻¹) ^ m • (0 : E n)) ≤ 1 :=
    pnc_lev_smul_le_one hA hI δ hδ ξ hξ hδξ ((γ⁻¹) ^ m) hγim hcomm'
  -- the two level scalings are reciprocal
  have hprod : lev ξ (γ ^ m • (0 : E n)) * lev ξ ((γ⁻¹) ^ m • (0 : E n)) = 1 := by
    have h := lev_smul_self hI' hA' ξ hξ (γ ^ m) ((γ⁻¹) ^ m • (0 : E n)) hγm
    have h0 : γ ^ m • ((γ⁻¹) ^ m • (0 : E n)) = (0 : E n) := by
      rw [← hA'.mul_smul, inv_pow, mul_inv_cancel, hA'.one_smul]
    rw [h0, pnc_lev_zero, mul_comm] at h
    exact h.symm
  have hbpos : 0 < lev ξ (γ ^ m • (0 : E n)) := lev_pos ξ hξ _
  have h3 : lev ξ ((γ⁻¹) ^ m • (0 : E n)) = (lev ξ (γ ^ m • (0 : E n)))⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  -- hence the level scaling of `γ^m` is `1`
  have hbm : lev ξ (γ ^ m • (0 : E n)) = 1 := by
    have h2' : (lev ξ (γ ^ m • (0 : E n)))⁻¹ ≤ 1 := by rw [← h3]; exact h2
    have hone : 1 ≤ lev ξ (γ ^ m • (0 : E n)) := by
      have hh := mul_le_mul_of_nonneg_left h2' (le_of_lt hbpos)
      rwa [mul_inv_cancel₀ (ne_of_gt hbpos), mul_one] at hh
    linarith
  -- but that level scaling is `exp (m * bCocy γ ξ) ≠ 1`
  have hbne : lev ξ (γ ^ m • (0 : E n)) ≠ 1 := by
    intro hcon
    have hb : lev ξ (γ ^ m • (0 : E n)) = Real.exp (bCocy (γ ^ m) ξ) := by
      rw [lev_eq_exp hξ]
      congr 1
      rw [bCocy, hγm]
    rw [hb, Real.exp_eq_one_iff, pnc_bCocy_pow hA hI γ hξ hγξ m] at hcon
    exact hc ((mul_eq_zero.mp hcon).resolve_left (Nat.cast_ne_zero.mpr (ne_of_gt hm)))
  exact hbne hbm

end Work.Mostow
