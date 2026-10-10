import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Defs.Basic
import Submission.Work.SSGRoute.PT.shapiro_H3_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The homotopy identity in degree `3`: `d² (s2c c) = c - Ψ₃ (Φ₃ c)`

For a `3`-cocycle `c` of `G` with values in the coinduced module `Coind U G M` we prove the
degree-`3` analogue of `s1_d1_apply` (`shapiro_H2_inj`):

  `d² (s2c U c) (g,h,k) x = c (g,h,k) x - coord x • c (A g (xU)) (A h (g⁻¹•xU)) (A k ((gh)⁻¹•xU)) 1`.

The proof is a "cascade" of `3`-cocycle conditions (`Z3_eval`), one for each slot in which the
section representative is inserted: at `(g,h,k,secC ((g(hk))⁻¹•xU))` (fourth slot), at
`(secC xU, A g (xU), A h (g⁻¹•xU), A k ((gh)⁻¹•xU))` (all slots reduced), at
`(g, secC (g⁻¹•xU), A h (g⁻¹•xU), A k ((gh)⁻¹•xU))` (second slot) and at
`(g, h, secC ((gh)⁻¹•xU), A k ((gh)⁻¹•xU))` (third slot).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

/-- Rearrangement of the five terms of the `3`-cocycle condition: isolate the *fifth* term. -/
theorem iso_e {A : Type*} [AddCommGroup A] {a b c d e : A} (h : a - b + c - d + e = 0) :
    e = -a + b - c + d := by
  have hY : e - (-a + b - c + d) = a - b + c - d + e := by abel
  exact sub_eq_zero.mp (hY.trans h)

/-- Rearrangement: isolate the *fourth* term. -/
theorem iso_d {A : Type*} [AddCommGroup A] {a b c d e : A} (h : a - b + c - d + e = 0) :
    d = a - b + c + e := by
  have hY : d - (a - b + c + e) = -(a - b + c - d + e) := by abel
  have hZ : (-(a - b + c - d + e) : A) = 0 :=
    (congrArg (fun t : A => -t) h).trans neg_zero
  exact sub_eq_zero.mp (hY.trans hZ)

/-- Rearrangement: isolate the *third* term. -/
theorem iso_c {A : Type*} [AddCommGroup A] {a b c d e : A} (h : a - b + c - d + e = 0) :
    c = -a + b + d - e := by
  have hY : c - (-a + b + d - e) = a - b + c - d + e := by abel
  exact sub_eq_zero.mp (hY.trans h)

/-- Rearrangement: isolate the *second* term. -/
theorem iso_b {A : Type*} [AddCommGroup A] {a b c d e : A} (h : a - b + c - d + e = 0) :
    b = a + c - d + e := by
  have hY : b - (a + c - d + e) = -(a - b + c - d + e) := by abel
  have hZ : (-(a - b + c - d + e) : A) = 0 :=
    (congrArg (fun t : A => -t) h).trans neg_zero
  exact sub_eq_zero.mp (hY.trans hZ)

variable {G : Type*} [Group G] [TopologicalSpace G] (U : Subgroup G)
variable {M : Type*} [AddCommGroup M] [DistribMulAction U M]

theorem s2c_d2_apply {c : G × G × G → Coind G U M}
    (hc : c ∈ Work.SSGRoute.Z3 (M := Coind G U M) G) (g h k x : G) :
    (Work.GroupCohomology.d2 G (Coind G U M) (s2c U c) (g, h, k) : G → M) x
      = (c (g, h, k) : G → M) x
        - coord U x • ((c ((Shapiro.A 0 G U g (x : G ⧸ U) : G),
            (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
            (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G))) : G → M) 1 := by
  classical
  -- ### 0. the second term of the right-hand side as an evaluation of `c`
  have htwist : coord U x • ((c ((Shapiro.A 0 G U g (x : G ⧸ U) : G),
        (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
        (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G))) : G → M) 1
      = (c ((Shapiro.A 0 G U g (x : G ⧸ U) : G),
        (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
        (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G))) ((coord U x : G)⁻¹) := by
    conv_lhs => rw [show coord U x = ((coord U x)⁻¹)⁻¹ from (inv_inv (coord U x)).symm]
    rw [← Coind.coe_mul (c ((Shapiro.A 0 G U g (x : G ⧸ U) : G),
        (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
        (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G))) (1 : G) ((coord U x)⁻¹),
      one_mul, Subgroup.coe_inv]
  rw [htwist]
  -- ### 1. the auxiliary group identities
  have hs0x : (secC U (x : G ⧸ U))⁻¹ * x = (coord U x : G)⁻¹ := by
    rw [coe_coord U x, mul_inv_rev, inv_inv]
  have hAgN : secC U (x : G ⧸ U) * (Shapiro.A 0 G U g (x : G ⧸ U) : G)
      = g * secC U (g⁻¹ • (x : G ⧸ U)) := (secC_mul_A U g (x : G ⧸ U)).symm
  have hAhN : secC U (g⁻¹ • (x : G ⧸ U)) * (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)
      = h * secC U ((g * h)⁻¹ • (x : G ⧸ U)) := by
    have hC : h⁻¹ • (g⁻¹ • (x : G ⧸ U)) = (g * h)⁻¹ • (x : G ⧸ U) := by
      simp only [mul_inv_rev, mul_smul]
    rw [← secC_mul_A U h (g⁻¹ • (x : G ⧸ U)), hC]
  have hsec3 : k * secC U ((g * (h * k))⁻¹ • (x : G ⧸ U))
      = secC U ((g * h)⁻¹ • (x : G ⧸ U))
        * (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G) := by
    have hC : (g * (h * k))⁻¹ • (x : G ⧸ U) = k⁻¹ • ((g * h)⁻¹ • (x : G ⧸ U)) := by
      simp only [mul_inv_rev, mul_smul]
    rw [hC, secC_mul_A]
  -- ### 2. the four oriented cocycle relations
  have k1 : (c (g, h, k) : G → M) x
      = - (c (h, k, secC U ((g * (h * k))⁻¹ • (x : G ⧸ U))) : G → M) (g⁻¹ * x)
        + (c (g * h, k, secC U ((g * (h * k))⁻¹ • (x : G ⧸ U))) : G → M) x
        - (c (g, h * k, secC U ((g * (h * k))⁻¹ • (x : G ⧸ U))) : G → M) x
        + (c (g, h, secC U ((g * h)⁻¹ • (x : G ⧸ U))
            * (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x := by
    have h := Z3_eval U hc g h k (secC U ((g * (h * k))⁻¹ • (x : G ⧸ U))) x
    rw [hsec3] at h
    exact iso_e h
  have k4 : (c (g, h, secC U ((g * h)⁻¹ • (x : G ⧸ U))
        * (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
      = (c (h, secC U ((g * h)⁻¹ • (x : G ⧸ U)),
          (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) (g⁻¹ * x)
        - (c (g * h, secC U ((g * h)⁻¹ • (x : G ⧸ U)),
          (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        + (c (g, h * secC U ((g * h)⁻¹ • (x : G ⧸ U)),
          (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        + (c (g, h, secC U ((g * h)⁻¹ • (x : G ⧸ U))) : G → M) x := by
    have h := Z3_eval U hc g h (secC U ((g * h)⁻¹ • (x : G ⧸ U)))
      (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U))) x
    exact iso_d h
  have k3 : (c (g, h * secC U ((g * h)⁻¹ • (x : G ⧸ U)),
        (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
      = - (c (secC U (g⁻¹ • (x : G ⧸ U)),
          (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
          (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) (g⁻¹ * x)
        + (c (g * secC U (g⁻¹ • (x : G ⧸ U)),
          (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
          (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        + (c (g, secC U (g⁻¹ • (x : G ⧸ U)),
          (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)
            * (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        - (c (g, secC U (g⁻¹ • (x : G ⧸ U)),
          (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x := by
    have h := Z3_eval U hc g (secC U (g⁻¹ • (x : G ⧸ U)))
      (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)))
      (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U))) x
    rw [hAhN] at h
    exact iso_c h
  have k2 : (c (g * secC U (g⁻¹ • (x : G ⧸ U)),
        (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
        (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
      = (c ((Shapiro.A 0 G U g (x : G ⧸ U) : G),
          (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
          (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) ((coord U x : G)⁻¹)
        + (c (secC U (x : G ⧸ U),
          (Shapiro.A 0 G U g (x : G ⧸ U) : G)
            * (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G),
          (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        - (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G),
          (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)
            * (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)) : G)) : G → M) x
        + (c (secC U (x : G ⧸ U), (Shapiro.A 0 G U g (x : G ⧸ U) : G),
          (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)) : G)) : G → M) x := by
    have h := Z3_eval U hc (secC U (x : G ⧸ U)) (Shapiro.A 0 G U g (x : G ⧸ U))
      (Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)))
      (Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U))) x
    rw [hs0x, hAgN] at h
    exact iso_b h
  -- ### 3. expand and normalise the goal
  rw [Work.GroupCohomology.d2_apply]
  simp only [Coind.smul_apply, s2c_apply, AddSubgroup.coe_add, AddSubgroup.coe_sub,
    Pi.add_apply, Pi.sub_apply]
  simp only [coset_smul, ← mul_smul, ← mul_inv_rev, mul_assoc, A_mul',
    Subgroup.coe_mul, Subgroup.coe_inv]
  -- ### 4. conclude
  rw [k1, k4, k3, k2]
  abel

end

end Work.SSGRoute.PT
