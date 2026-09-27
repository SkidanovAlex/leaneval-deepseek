import Mathlib
import Submission.Work.Mostow.StabHorosphereBase
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.cuspZ2Defs
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.cuspCocompactAtLevel
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.parabolic_not_commute_levelScaling

/-!
# The stabiliser of a parabolic fixed point preserves the horospheres there

`Work.Mostow.geomFiniteStabHorosphere`: for a discrete subgroup `Γ ≤ PO(n,1)`, a parabolic fixed
point `ξ` of `Γ` and `γ ∈ Γ` fixing `ξ`, the Busemann cocycle of `γ` at `ξ` vanishes.

The proof is the standard discreteness argument.  Let `δ ∈ Γ` be parabolic with `bd δ ξ = ξ`; then
`bCocy δ ξ = 0`, so `δ` preserves the horospheres of `ξ` and acts on them by an isometry
`y ↦ A y + v` of the flat space `ξ^⊥` (`stabFlatAction`).  If `c = bCocy γ ξ > 0`, then `γ`
strictly expands the levels at `ξ`, the points `p_k = (γ⁻¹)^k • 0` have level `e^{-kc}` and flat
coordinates growing at most like `e^{kc}` (`gfsh_yc_growth`), so the conjugates
`ν_k = γ^k δ γ^{-k} ∈ Γ` are displaced from `0` by a uniformly bounded amount.  By
`finite_nearStab` the `ν_k` cannot be pairwise distinct, so `δ` commutes with a nonzero power of
`γ`, contradicting `parabolic_not_commute_levelScaling`.  Applying this to `γ` or `γ⁻¹` proves the
claim.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Elementary cocycle and level identities -/

/-- `bd` of the inverse at a fixed boundary point. -/
lemma gfsh_bd_inv (hA : POActionProp n) {g : PO n 1} {ξ : E n} (hξ : ξ ∈ Sph n)
    (hg : bd g ξ = ξ) : bd g⁻¹ ξ = ξ := by
  have hAb := POBasic.ofProp hA
  have h := hAb.bd_mul g⁻¹ g ξ hξ
  rw [inv_mul_cancel, hAb.bd_one ξ hξ, hg] at h
  exact h.symm

/-- The Busemann cocycle of the inverse at a fixed boundary point. -/
lemma gfsh_bCocy_inv (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ) :
    bCocy g⁻¹ ξ = - bCocy g ξ := by
  have h1 := bCocy_mul hA hI g⁻¹ g ξ hξ
  rw [inv_mul_cancel, bCocy_one hA hI ξ hξ] at h1
  rw [hg] at h1
  linarith

/-- An isometry fixing `ξ` scales the horosphere levels at `ξ` by `exp (bCocy g ξ)`. -/
lemma gfsh_lev_smul_cocycle (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ) (u : E n) :
    lev ξ (g • u) = lev ξ u * Real.exp (bCocy g ξ) := by
  have hbus := hI.2.2.2.2.2.2.2.2.2.2.2.2 g ξ u hξ
  rw [hg] at hbus
  have hb : busemann ξ (g • (0 : E n)) = bCocy g ξ := by rw [bCocy, hg]
  rw [hb] at hbus
  rw [lev_eq_exp hξ (g • u), lev_eq_exp hξ u, hbus, Real.exp_add]

/-- The level of `(γ⁻¹)^k • 0` for `γ` fixing `ξ`. -/
lemma gfsh_lev_pow_inv_zero (hA : POActionProp n) (hI : HypIsometryProp n)
    (γ : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) (hγ : bd γ ξ = ξ) (k : ℕ) :
    lev ξ (((γ⁻¹) ^ k) • (0 : E n)) = Real.exp (-(k : ℝ) * bCocy γ ξ) := by
  have hγinv : bd γ⁻¹ ξ = ξ := gfsh_bd_inv hA hξ hγ
  have hbdk : bd ((γ⁻¹) ^ k) ξ = ξ := pnc_bd_pow_fixed hA (γ⁻¹) hξ hγinv k
  have hbus : busemann ξ (((γ⁻¹) ^ k) • (0 : E n)) = bCocy ((γ⁻¹) ^ k) ξ := by
    rw [bCocy, hbdk]
  rw [lev_eq_exp hξ, hbus, pnc_bCocy_pow hA hI γ⁻¹ hξ hγinv k, gfsh_bCocy_inv hA hI γ hξ hγ]
  congr 1
  ring

lemma gfsh_yc_zero (ξ : E n) : yc ξ (0 : E n) = 0 := by
  simp [yc, wc, lev, tpart, inner_zero_left]

/-! ## Growth of the flat coordinate along the orbit of a level-scaling element -/

/-- If `γ` fixes `ξ` and `c = bCocy γ ξ > 0`, then the flat coordinates of the points
`(γ⁻¹)^k • 0` grow at most like `e^{kc}`. -/
lemma gfsh_yc_growth (hA : POActionProp n) (hI : HypIsometryProp n)
    (γ : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) (hγ : bd γ ξ = ξ) (hc : 0 < bCocy γ ξ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k : ℕ,
      Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ (((γ⁻¹) ^ k) • (0 : E n))‖ ≤ R := by
  have hAb := POBasic.ofProp hA
  have hId := HypIsoData.ofProp hI
  set c : ℝ := bCocy γ ξ with hcdef
  have hγinv : bd γ⁻¹ ξ = ξ := gfsh_bd_inv hA hξ hγ
  -- step length of the orbit
  set L : ℝ := hdist (0 : E n) (γ⁻¹ • (0 : E n)) with hLdef
  have hstep : ∀ k : ℕ,
      hdist (((γ⁻¹) ^ k) • (0 : E n)) (((γ⁻¹) ^ (k+1)) • (0 : E n)) = L := by
    intro k
    have hp1 : (((γ⁻¹) ^ (k+1)) • (0 : E n)) = (γ⁻¹) • (((γ⁻¹) ^ k) • (0 : E n)) := by
      rw [pow_succ', hAb.mul_smul]
    rw [hp1]
    have h2 := hId.isom_smul (((γ⁻¹) ^ k)⁻¹) (((γ⁻¹) ^ k) • (0 : E n))
      ((γ⁻¹) • (((γ⁻¹) ^ k) • (0 : E n)))
    rw [hLdef, ← h2]
    have hc1 : ((γ⁻¹) ^ k)⁻¹ * (γ⁻¹ * (γ⁻¹) ^ k) = γ⁻¹ := by
      rw [← pow_succ', pow_succ, ← mul_assoc, inv_mul_cancel, one_mul]
    have hc2 : ((γ⁻¹) ^ k)⁻¹ * γ⁻¹ * (γ⁻¹) ^ k = γ⁻¹ := by
      rw [mul_assoc]; exact hc1
    have e1 : (((γ⁻¹) ^ k)⁻¹) • (((γ⁻¹) ^ k) • (0 : E n)) = (0 : E n) := by
      rw [← hAb.mul_smul, inv_mul_cancel, hAb.one_smul]
    have e2 : (((γ⁻¹) ^ k)⁻¹) • ((γ⁻¹) • (((γ⁻¹) ^ k) • (0 : E n))) = γ⁻¹ • (0 : E n) := by
      rw [← hAb.mul_smul, ← hAb.mul_smul, hc2]
    rw [e1, e2]
  -- `c ≤ L`
  have hb1 : busemann ξ (γ⁻¹ • (0 : E n)) = -c := by
    have h : bCocy γ⁻¹ ξ = busemann ξ (γ⁻¹ • (0 : E n)) := by rw [bCocy, hγinv]
    rw [← h, gfsh_bCocy_inv hA hI γ hξ hγ, hcdef]
  have hLc : c ≤ L := by
    have hbus := busemann_lipschitz hI ξ hξ (0 : E n) (γ⁻¹ • (0 : E n))
    have h0 : busemann ξ (0 : E n) = 0 := by simp [busemann, tpart]
    rw [h0, hb1, ← hLdef] at hbus
    simpa only [zero_sub, neg_neg, abs_of_pos hc] using hbus
  have hcoshLc : Real.cosh c ≤ Real.cosh L :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_nonneg hc.le, abs_of_nonneg (hId.nonneg _ _)]; exact hLc)
  -- the constant `K`
  set K : ℝ := Real.sqrt (2 * (Real.cosh L - Real.cosh c)) with hKdef
  have hKs : K ^ 2 = 2 * (Real.cosh L - Real.cosh c) := by
    rw [hKdef, Real.sq_sqrt]
    linarith
  -- the flat step length
  have hflatstep : ∀ k : ℕ,
      ‖yc ξ (((γ⁻¹) ^ k) • (0 : E n)) - yc ξ (((γ⁻¹) ^ (k+1)) • (0 : E n))‖
        = K * Real.exp ((k : ℝ) * c + c / 2) := by
    intro k
    set d : ℝ := ‖yc ξ (((γ⁻¹) ^ k) • (0 : E n)) - yc ξ (((γ⁻¹) ^ (k+1)) • (0 : E n))‖ with hddef
    have hdnn : 0 ≤ d := by rw [hddef]; positivity
    have hd2 : ‖yc ξ (((γ⁻¹) ^ k) • (0 : E n))
        - yc ξ (((γ⁻¹) ^ (k+1)) • (0 : E n))‖ ^ 2 = d ^ 2 := by rw [hddef]
    have hlevk := gfsh_lev_pow_inv_zero hA hI γ hξ hγ k
    rw [← hcdef] at hlevk
    have hlevk1 := gfsh_lev_pow_inv_zero hA hI γ hξ hγ (k+1)
    have hcast : -(((k+1 : ℕ)) : ℝ) * c = -((k : ℝ) + 1) * c := by push_cast; ring
    rw [hcast] at hlevk1
    have hform := levYcFormula hξ (((γ⁻¹) ^ k) • (0 : E n))
      (((γ⁻¹) ^ (k+1)) • (0 : E n))
    have hdiv : Real.exp (-(k : ℝ) * c) / Real.exp (-((k : ℝ) + 1) * c) = Real.exp c := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hstep k, hlevk, hlevk1, hdiv, hd2, Real.log_exp] at hform
    have he : Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c) * d ^ 2 = K ^ 2 := by
      rw [hKs]
      nlinarith [hform]
    have hea : Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c)
        * (Real.exp ((k : ℝ) * c + c / 2)) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      have hz : -(k : ℝ) * c + (-((k : ℝ) + 1) * c)
          + ((2:ℕ):ℝ) * ((k : ℝ) * c + c / 2) = 0 := by push_cast; ring
      rw [hz, Real.exp_zero]
    have hpos : 0 < Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c) := by positivity
    have hd2' : d ^ 2 = (K * Real.exp ((k : ℝ) * c + c / 2)) ^ 2 := by
      have h3 : Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c) * d ^ 2
          = Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c)
            * (K * Real.exp ((k : ℝ) * c + c / 2)) ^ 2 := by
        rw [he, mul_pow]
        rw [show Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c)
              * (K ^ 2 * (Real.exp ((k : ℝ) * c + c / 2)) ^ 2) = K ^ 2 by
            rw [show Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c)
                  * (K ^ 2 * (Real.exp ((k : ℝ) * c + c / 2)) ^ 2)
                = K ^ 2 * (Real.exp (-(k : ℝ) * c) * Real.exp (-((k : ℝ) + 1) * c)
                  * (Real.exp ((k : ℝ) * c + c / 2)) ^ 2) by ring, hea, mul_one]]
      exact mul_left_cancel₀ (ne_of_gt hpos) h3
    have hnn : (0:ℝ) ≤ K * Real.exp ((k : ℝ) * c + c / 2) := by
      have : 0 < Real.exp ((k : ℝ) * c + c / 2) := Real.exp_pos _
      nlinarith [Real.sqrt_nonneg (2 * (Real.cosh L - Real.cosh c))]
    calc ‖yc ξ (((γ⁻¹) ^ k) • (0 : E n)) - yc ξ (((γ⁻¹) ^ (k+1)) • (0 : E n))‖
        = Real.sqrt (‖yc ξ (((γ⁻¹) ^ k) • (0 : E n))
            - yc ξ (((γ⁻¹) ^ (k+1)) • (0 : E n))‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = d := by rw [hd2, Real.sqrt_sq hdnn]
      _ = Real.sqrt (d ^ 2) := (Real.sqrt_sq hdnn).symm
      _ = Real.sqrt ((K * Real.exp ((k : ℝ) * c + c / 2)) ^ 2) := by rw [hd2']
      _ = K * Real.exp ((k : ℝ) * c + c / 2) := Real.sqrt_sq hnn
  -- the bound, by induction
  refine ⟨K * Real.exp (c / 2) / (Real.exp c - 1), ?_, ?_⟩
  · have h1 : 0 < Real.exp c - 1 := by
      have := Real.one_lt_exp_iff.mpr hc
      linarith
    positivity
  intro k
  have hexpc1 : 0 < Real.exp c - 1 := by
    have := Real.one_lt_exp_iff.mpr hc
    linarith
  have hmain : ∀ j : ℕ,
      Real.exp (-(j : ℝ) * c) * ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n))‖
        ≤ K * Real.exp (c / 2) / (Real.exp c - 1) := by
    intro j
    induction j with
    | zero =>
        rw [pow_zero, hAb.one_smul, gfsh_yc_zero, norm_zero]
        simp only [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, one_mul]
        positivity
    | succ j ih =>
        have hexpj : Real.exp (-(((j:ℕ)+1 : ℕ) : ℝ) * c)
            = Real.exp (-(j : ℝ) * c) * Real.exp (-c) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
        rw [hexpj]
        have htri : ‖yc ξ (((γ⁻¹) ^ (j+1)) • (0 : E n))‖
            ≤ ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n))‖
              + ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n)) - yc ξ (((γ⁻¹) ^ (j+1)) • (0 : E n))‖ := by
          have h : ‖yc ξ (((γ⁻¹) ^ (j+1)) • (0 : E n))‖
              ≤ ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n))‖
                + ‖yc ξ (((γ⁻¹) ^ (j+1)) • (0 : E n)) - yc ξ (((γ⁻¹) ^ j) • (0 : E n))‖ := by
            calc ‖yc ξ (((γ⁻¹) ^ (j+1)) • (0 : E n))‖
                = ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n))
                    + (yc ξ (((γ⁻¹) ^ (j+1)) • (0 : E n))
                      - yc ξ (((γ⁻¹) ^ j) • (0 : E n)))‖ := by
                  congr 1; abel
              _ ≤ _ := norm_add_le _ _
          rwa [norm_sub_rev] at h
        have hstep2 : ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n)) - yc ξ (((γ⁻¹) ^ (j+1)) • (0 : E n))‖
            = K * Real.exp ((j : ℝ) * c + c / 2) := hflatstep j
        have hb := mul_le_mul_of_nonneg_left htri
          (by positivity : (0:ℝ) ≤ Real.exp (-(j : ℝ) * c) * Real.exp (-c))
        rw [mul_add] at hb
        rw [hstep2] at hb
        have h21 : Real.exp (-(j : ℝ) * c) * Real.exp (-c)
            * ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n))‖
            = Real.exp (-c) * (Real.exp (-(j : ℝ) * c)
              * ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n))‖) := by ring
        have h22 : Real.exp (-(j : ℝ) * c) * Real.exp (-c)
            * (K * Real.exp ((j : ℝ) * c + c / 2))
            = Real.exp (-c) * (K * Real.exp (c / 2)) := by
          rw [show Real.exp (-(j : ℝ) * c) * Real.exp (-c)
              * (K * Real.exp ((j : ℝ) * c + c / 2))
              = Real.exp (-c) * (K * (Real.exp (-(j : ℝ) * c)
                * Real.exp ((j : ℝ) * c + c / 2))) by ring]
          rw [show Real.exp (-(j : ℝ) * c) * Real.exp ((j : ℝ) * c + c / 2)
              = Real.exp (c / 2) by
            rw [← Real.exp_add]; congr 1; ring]
        rw [h21, h22] at hb
        have hA' : Real.exp (-c) * (Real.exp (-(j : ℝ) * c)
              * ‖yc ξ (((γ⁻¹) ^ j) • (0 : E n))‖)
            ≤ Real.exp (-c) * (K * Real.exp (c / 2) / (Real.exp c - 1)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        have heq : Real.exp (-c) * (K * Real.exp (c / 2) / (Real.exp c - 1))
            + Real.exp (-c) * (K * Real.exp (c / 2))
            = K * Real.exp (c / 2) / (Real.exp c - 1) := by
          rw [Real.exp_neg]
          have hne1 : Real.exp c ≠ 0 := Real.exp_ne_zero c
          have hne2 : Real.exp c - 1 ≠ 0 := ne_of_gt hexpc1
          field_simp
          ring
        linarith [hb, hA', heq.le]
  exact hmain k

/-! ## Elementary group identities -/

section GfshGroupLemmas

variable {G : Type*} [Group G]

private lemma gfsh_aux_conj_mul (a x : G) : a⁻¹ * (a * x * a⁻¹) * a = x := by group

private lemma gfsh_aux_conj_mul' (a b x : G) :
    a⁻¹ * (a * b * x * (b⁻¹ * a⁻¹)) * a = b * x * b⁻¹ := by group

private lemma gfsh_aux_conj_mul'' (a x : G) : (a * x * a⁻¹) * a = a * x := by group

end GfshGroupLemmas

/-! ## The engine: discreteness forces the cocycle to vanish -/

lemma gfsh_stab_cocycle_zero (hA : POActionProp n) (hI : HypIsometryProp n) (hn : 2 ≤ n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (δ γ : PO n 1) (hδΓ : δ ∈ Γ) (hγΓ : γ ∈ Γ) (hδpar : IsParabolic δ)
    (ξ : E n) (hξ : ξ ∈ Sph n) (hδξ : bd δ ξ = ξ) (hγξ : bd γ ξ = ξ)
    (hc : 0 < bCocy γ ξ) : False := by
  have hAb := POBasic.ofProp hA
  have hId := HypIsoData.ofProp hI
  have hbcδ : bCocy δ ξ = 0 := bCocy_parabolic hA hI δ hδpar ξ hξ hδξ
  have hlevδ : ∀ u : E n, lev ξ (δ • u) = lev ξ u := by
    intro u
    rw [gfsh_lev_smul_cocycle hA hI δ hξ hδξ u, hbcδ, Real.exp_zero, mul_one]
  have hβ : busemann ξ (δ • (0 : E n)) = 0 := by
    have h : bCocy δ ξ = busemann ξ (δ • (0 : E n)) := by rw [bCocy, hδξ]
    rw [← h]; exact hbcδ
  obtain ⟨A, v, hvξ, hAξ, hAn, hflat⟩ := stabFlatAction n hA hI ξ hξ δ hδξ hβ
  have hycδ : ∀ u : E n, yc ξ (δ • u) = A (yc ξ u) + v := by
    intro u
    obtain ⟨ρ, hρorth, hρhpt, -, -⟩ := exists_rho_levelIndep hA hI ξ hξ δ hδξ hlevδ
    have hρeq : ∀ y : E n, inner ℝ y ξ = 0 → ρ y = A y + v := by
      intro y hy
      have h1 : yc ξ (δ • hptOf ξ y 1) = ρ y := by
        rw [← hρhpt y hy 1 one_pos]
        exact (hptOf_level ξ hξ 1 one_pos (ρ y) (hρorth y hy)).2
      have h2 : yc ξ (δ • hptOf ξ y 1) = A y + v := (hflat y 1 hy one_pos).2
      rw [h1] at h2
      exact h2
    have h := yc_smul_eq hA hI ξ hξ δ ρ hρhpt hρorth u
    rw [h, hρeq (yc ξ u) (yc_inner_orth hξ)]
  obtain ⟨R, hR0, hR⟩ := gfsh_yc_growth hA hI γ hξ hγξ hc
  set R' : ℝ := Real.arcosh (1 + (2 * R + ‖v‖) ^ 2 / 2) with hR'def
  have hR'nn : 0 ≤ R' := by
    rw [hR'def]
    exact Real.arcosh_nonneg (by nlinarith [sq_nonneg (2 * R + ‖v‖)])
  have hdisp : ∀ k : ℕ, hdist (0 : E n) ((γ ^ k * δ * (γ ^ k)⁻¹) • (0 : E n)) ≤ R' := by
    intro k
    set p : E n := ((γ⁻¹) ^ k) • (0 : E n) with hpdef
    have hlevp : lev ξ p = Real.exp (-(k : ℝ) * bCocy γ ξ) := gfsh_lev_pow_inv_zero hA hI γ hξ hγξ k
    have hδp : (γ ^ k * δ * (γ ^ k)⁻¹) • (0 : E n) = γ ^ k • (δ • p) := by
      rw [hAb.mul_smul, hAb.mul_smul]
      congr 1
      rw [hpdef, inv_pow]
    have hdistk : hdist (0 : E n) ((γ ^ k * δ * (γ ^ k)⁻¹) • (0 : E n)) = hdist p (δ • p) := by
      rw [hδp]
      have h3 := hId.isom_smul (γ ^ k) p (δ • p)
      rw [← h3]
      congr 1
      rw [hpdef, ← hAb.mul_smul, inv_pow, mul_inv_cancel, hAb.one_smul]
    rw [hdistk]
    have hD : (0:ℝ) < Real.exp (-(k : ℝ) * bCocy γ ξ) := Real.exp_pos _
    have hform := hdist_of_lev_eq (ξ := ξ) hξ hD hlevp (by rw [hlevδ]; exact hlevp)
    have hdispδ : ‖yc ξ p - yc ξ (δ • p)‖ ≤ 2 * ‖yc ξ p‖ + ‖v‖ := by
      rw [hycδ p]
      have h1 : yc ξ p - (A (yc ξ p) + v) = (yc ξ p - A (yc ξ p)) - v := by abel
      rw [h1]
      calc ‖(yc ξ p - A (yc ξ p)) - v‖
          ≤ ‖yc ξ p - A (yc ξ p)‖ + ‖v‖ := norm_sub_le _ _
        _ ≤ (‖yc ξ p‖ + ‖A (yc ξ p)‖) + ‖v‖ := by
              linarith [norm_sub_le (yc ξ p) (A (yc ξ p))]
        _ = 2 * ‖yc ξ p‖ + ‖v‖ := by rw [hAn (yc ξ p) (yc_inner_orth hξ)]; ring
    have hexp1 : Real.exp (-(k : ℝ) * bCocy γ ξ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
      nlinarith [hc]
    have hkey : Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ p - yc ξ (δ • p)‖
        ≤ 2 * R + ‖v‖ := by
      have h1 : Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ p - yc ξ (δ • p)‖
          ≤ Real.exp (-(k : ℝ) * bCocy γ ξ) * (2 * ‖yc ξ p‖ + ‖v‖) :=
        mul_le_mul_of_nonneg_left hdispδ (le_of_lt hD)
      have h2 : Real.exp (-(k : ℝ) * bCocy γ ξ) * (2 * ‖yc ξ p‖ + ‖v‖)
          = 2 * (Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ p‖)
            + Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖v‖ := by ring
      rw [h2] at h1
      have h3 : Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ p‖ ≤ R := hR k
      have h4 : Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖v‖ ≤ ‖v‖ := by
        nlinarith [hexp1, norm_nonneg v]
      linarith [h1, h3, h4]
    have hcR : Real.cosh R' = 1 + (2 * R + ‖v‖) ^ 2 / 2 := by
      rw [hR'def, Real.cosh_arcosh (by nlinarith [sq_nonneg (2 * R + ‖v‖)])]
    have hmain : Real.cosh (hdist p (δ • p)) ≤ Real.cosh R' := by
      have hnn : (1 : ℝ) ≤ 1 + (Real.exp (-(k : ℝ) * bCocy γ ξ)
          * ‖yc ξ p - yc ξ (δ • p)‖) ^ 2 / 2 := by
        have := sq_nonneg (Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ p - yc ξ (δ • p)‖)
        linarith
      have h1 : Real.cosh (hdist p (δ • p))
          = 1 + (Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ p - yc ξ (δ • p)‖) ^ 2 / 2 := by
        rw [hform, Real.cosh_arcosh hnn]
      rw [h1, hcR]
      have h2 : 0 ≤ 2 * R + ‖v‖ := by linarith [hR0, norm_nonneg v]
      have he : 0 ≤ Real.exp (-(k : ℝ) * bCocy γ ξ) * ‖yc ξ p - yc ξ (δ • p)‖ := by
        positivity
      nlinarith [hkey, h2, he, mul_self_nonneg (2 * R + ‖v‖ - Real.exp (-(k : ℝ) * bCocy γ ξ)
        * ‖yc ξ p - yc ξ (δ • p)‖)]
    have habs := Real.cosh_le_cosh.mp hmain
    rw [abs_of_nonneg (hId.nonneg p (δ • p)), abs_of_nonneg hR'nn] at habs
    exact habs
  have hmem : ∀ k : ℕ, γ ^ k * δ * (γ ^ k)⁻¹ ∈ Γ := fun k =>
    Γ.mul_mem (Γ.mul_mem (Γ.pow_mem hγΓ k) hδΓ) (Γ.inv_mem (Γ.pow_mem hγΓ k))
  have hinj : Function.Injective (fun k : ℕ => (⟨γ ^ k * δ * (γ ^ k)⁻¹, hmem k⟩ : Γ)) := by
    intro k l hkl
    by_contra hne
    have hcoe : γ ^ k * δ * (γ ^ k)⁻¹ = γ ^ l * δ * (γ ^ l)⁻¹ :=
      congrArg (fun g : Γ => (g : PO n 1)) hkl
    have hcne : bCocy γ ξ ≠ 0 := ne_of_gt hc
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : 0 < l - k := Nat.sub_pos_of_lt hlt
      have h2 : γ ^ l = γ ^ k * γ ^ (l - k) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hlt.le]
        rw [pow_add]
      have hcomm : δ * γ ^ (l - k) = γ ^ (l - k) * δ := by
        have hkey2 : δ = γ ^ (l - k) * δ * (γ ^ (l - k))⁻¹ := by
          have h := hcoe
          rw [h2, mul_inv_rev] at h
          have h5 : (γ ^ k)⁻¹ * (γ ^ k * δ * (γ ^ k)⁻¹) * γ ^ k = δ := gfsh_aux_conj_mul _ _
          have h6 : (γ ^ k)⁻¹ * (γ ^ k * γ ^ (l - k) * δ
              * ((γ ^ (l - k))⁻¹ * (γ ^ k)⁻¹)) * γ ^ k
              = γ ^ (l - k) * δ * (γ ^ (l - k))⁻¹ := gfsh_aux_conj_mul' _ _ _
          calc δ = (γ ^ k)⁻¹ * (γ ^ k * δ * (γ ^ k)⁻¹) * γ ^ k := h5.symm
            _ = (γ ^ k)⁻¹ * (γ ^ k * γ ^ (l - k) * δ
                  * ((γ ^ (l - k))⁻¹ * (γ ^ k)⁻¹)) * γ ^ k := by rw [h]
            _ = γ ^ (l - k) * δ * (γ ^ (l - k))⁻¹ := h6
        calc δ * γ ^ (l - k) = (γ ^ (l - k) * δ * (γ ^ (l - k))⁻¹) * γ ^ (l - k) := by
              conv_lhs => rw [hkey2]
          _ = γ ^ (l - k) * δ := gfsh_aux_conj_mul'' _ _
      exact parabolic_not_commute_levelScaling n hn hA hI δ γ hδpar ξ hξ hδξ hγξ hcne
        (l - k) hm hcomm
    · have hm : 0 < k - l := Nat.sub_pos_of_lt hgt
      have h2 : γ ^ k = γ ^ l * γ ^ (k - l) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hgt.le]
        rw [pow_add]
      have hcomm : δ * γ ^ (k - l) = γ ^ (k - l) * δ := by
        have hkey2 : δ = γ ^ (k - l) * δ * (γ ^ (k - l))⁻¹ := by
          have h := hcoe
          rw [h2, mul_inv_rev] at h
          have h5 : (γ ^ l)⁻¹ * (γ ^ l * δ * (γ ^ l)⁻¹) * γ ^ l = δ := gfsh_aux_conj_mul _ _
          have h6 : (γ ^ l)⁻¹ * (γ ^ l * γ ^ (k - l) * δ
              * ((γ ^ (k - l))⁻¹ * (γ ^ l)⁻¹)) * γ ^ l
              = γ ^ (k - l) * δ * (γ ^ (k - l))⁻¹ := gfsh_aux_conj_mul' _ _ _
          calc δ = (γ ^ l)⁻¹ * (γ ^ l * δ * (γ ^ l)⁻¹) * γ ^ l := h5.symm
            _ = (γ ^ l)⁻¹ * (γ ^ l * γ ^ (k - l) * δ
                  * ((γ ^ (k - l))⁻¹ * (γ ^ l)⁻¹)) * γ ^ l := by rw [h]
            _ = γ ^ (k - l) * δ * (γ ^ (k - l))⁻¹ := h6
        calc δ * γ ^ (k - l) = (γ ^ (k - l) * δ * (γ ^ (k - l))⁻¹) * γ ^ (k - l) := by
              conv_lhs => rw [hkey2]
          _ = γ ^ (k - l) * δ := gfsh_aux_conj_mul'' _ _
      exact parabolic_not_commute_levelScaling n hn hA hI δ γ hδpar ξ hξ hδξ hγξ hcne
        (k - l) hm hcomm
  have hSfin := finite_nearStab hAb hId hdisc R'
  have hinjS : Function.Injective (fun k : ℕ =>
      (⟨⟨γ ^ k * δ * (γ ^ k)⁻¹, hmem k⟩, hdisp k⟩ :
        {g : Γ // hdist (0 : E n) ((g : PO n 1) • (0 : E n)) ≤ R'})) := by
    intro k l hkl
    apply hinj
    have h1 : (⟨γ ^ k * δ * (γ ^ k)⁻¹, hmem k⟩ : Γ) = ⟨γ ^ l * δ * (γ ^ l)⁻¹, hmem l⟩ :=
      congrArg (fun x : {g : Γ // hdist (0 : E n) ((g : PO n 1) • (0 : E n)) ≤ R'} => (x : Γ)) hkl
    simpa using (Subtype.ext_iff.mp h1)
  haveI : Fintype {g : Γ // hdist (0 : E n) ((g : PO n 1) • (0 : E n)) ≤ R'} := hSfin.fintype
  haveI : Fintype ℕ := Fintype.ofInjective _ hinjS
  exact (Set.infinite_univ (α := ℕ)) (Set.finite_univ_iff.mpr (Fintype.finite ‹Fintype ℕ›))

/-! ## The target theorem -/

theorem geomFiniteStabHorosphere (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdis : IsDiscrete (SetLike.coe Γ)) (ξ : E n)
    (hξ : ξ ∈ parFixed Γ) (γ : Γ) (hγ : bd (γ : PO n 1) ξ = ξ) :
    bCocy (γ : PO n 1) ξ = 0 := by
  by_cases hc : 0 < bCocy (γ : PO n 1) ξ
  · obtain ⟨hξS, δ, hδpar, hδξ⟩ := hξ
    exact (gfsh_stab_cocycle_zero hA hI hn Γ hdis (δ : PO n 1) (γ : PO n 1) δ.2 γ.2 hδpar
      ξ hξS hδξ hγ hc).elim
  · have hle : bCocy (γ : PO n 1) ξ ≤ 0 := le_of_not_gt hc
    by_cases h0 : bCocy (γ : PO n 1) ξ = 0
    · exact h0
    · have hlt : bCocy (γ : PO n 1) ξ < 0 := lt_of_le_of_ne hle h0
      have hγinv : bd ((γ : PO n 1)⁻¹) ξ = ξ := gfsh_bd_inv hA hξ.1 hγ
      have hcinv : 0 < bCocy ((γ : PO n 1)⁻¹) ξ := by
        rw [gfsh_bCocy_inv hA hI (γ : PO n 1) hξ.1 hγ]
        linarith
      obtain ⟨hξS, δ, hδpar, hδξ⟩ := hξ
      exact (gfsh_stab_cocycle_zero hA hI hn Γ hdis (δ : PO n 1) ((γ : PO n 1)⁻¹) δ.2
        (Γ.inv_mem γ.2) hδpar ξ hξS hδξ hγinv hcinv).elim

end

end Work.Mostow
