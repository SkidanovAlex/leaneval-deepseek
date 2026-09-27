import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspShimizuDefs
import Submission.Work.Mostow.cuspHoroInterIff
import Submission.Work.Mostow.paraUniqueFixed
import Submission.Work.Mostow.margulisCuspV2
import Submission.Work.Mostow.margulisCusp
import Submission.Work.Mostow.geomFiniteStabHorosphere
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.cuspShimizuHoroballAux
import Submission.Work.Mostow.bieberbach

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- An element fixing `ξ` preserves the horospherical levels as soon as the Busemann cocycle
at `ξ` vanishes. -/
lemma hvd_lev_smul_self (hA : POActionProp n) (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n)
    (g : PO n 1) (u : E n) (hg : bd g ξ = ξ) :
    lev ξ (g • u) = lev ξ u * lev ξ (g • (0 : E n)) := by
  have h := HypIsoData.ofProp hI
  have hbc := h.busemann_cocycle g ξ u hξ
  rw [hg] at hbc
  calc lev ξ (g • u) = Real.exp (busemann ξ (g • u)) := lev_eq_exp hξ (g • u)
    _ = Real.exp (busemann ξ u + busemann ξ (g • (0 : E n))) := by rw [hbc]
    _ = lev ξ u * lev ξ (g • (0 : E n)) := by
          rw [Real.exp_add, ← lev_eq_exp hξ u, ← lev_eq_exp hξ (g • (0 : E n))]

/-! ## The displacement of a flat translation

An element `δ` of the stabiliser of `ξ` which acts on the horospheres at `ξ` by the flat
translation `y ↦ y + v` (and preserves the levels) moves every point `u` by the amount
`arccosh (1 + (lev ξ u)^2 ‖v‖^2 / 2)`, which tends to `0` as `lev ξ u → 0`. -/

lemma hdist_flatTrans {ξ : E n} (hξ : ξ ∈ Sph n) (hI : HypIsometryProp n)
    (δ : PO n 1) (v : E n)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v)
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u) (u : E n) :
    hdist u (δ • u) = Real.arcosh (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) := by
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have h := levYcFormula (ξ := ξ) hξ u (δ • u)
  rw [hlev u, hyc u] at h
  have hycv : yc ξ u - (yc ξ u + v) = -v := by abel
  rw [hycv, norm_neg, div_self (ne_of_gt (lev_pos ξ hξ u)), Real.log_one, Real.cosh_zero] at h
  have harg : (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) = 1 + (lev ξ u * lev ξ u / 2) * ‖v‖ ^ 2 := by
    ring
  rw [harg, ← h]
  exact (Real.arcosh_cosh (hvd.nonneg u (δ • u))).symm

/-- A flat translation has no fixed point (as soon as `v ≠ 0`). -/
lemma flatTrans_ne_self {ξ : E n} (hξ : ξ ∈ Sph n)
    (δ : PO n 1) (v : E n) (hv : v ≠ 0)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v) :
    ∀ u : E n, δ • u ≠ u := by
  intro u hu
  have h := hyc u
  rw [hu] at h
  have h2 : v = 0 := by
    have := congrArg (fun z => z - yc ξ u) h
    rw [add_sub_cancel_left, sub_self] at this
    exact this.symm
  exact hv h2

/-- A flat translation is parabolic. -/
lemma flatTrans_isParabolic {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (δ : PO n 1) (v : E n) (hv : v ≠ 0)
    (hyc : ∀ u : E n, yc ξ (δ • u) = yc ξ u + v)
    (hlev : ∀ u : E n, lev ξ (δ • u) = lev ξ u) :
    IsParabolic δ := by
  have hpb : POBasic n := POBasic.ofProp hA
  refine ⟨flatTrans_ne_self hξ δ v hv hyc, fun ε hε => ?_⟩
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  have hcosh : 1 < Real.cosh ε := Real.one_lt_cosh.mpr (ne_of_gt hε)
  set D : ℝ := Real.sqrt (2 * (Real.cosh ε - 1) / ‖v‖ ^ 2) / 2 with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact div_pos (Real.sqrt_pos.mpr (div_pos (by linarith) hv2)) (by norm_num)
  have hD2 : D ^ 2 = (2 * (Real.cosh ε - 1) / ‖v‖ ^ 2) / 4 := by
    rw [hDdef, div_pow, Real.sq_sqrt (le_of_lt (div_pos (by linarith) hv2))]
    norm_num
  refine ⟨hptOf ξ 0 D, ?_⟩
  have hlevD : lev ξ (hptOf ξ 0 D) = D := (hptOf_level ξ hξ D hDpos 0 (by simp)).1
  rw [hdist_flatTrans hξ hI δ v hyc hlev (hptOf ξ 0 D), hlevD]
  have hkey : 1 + D ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh ε := by
    have hE : D ^ 2 * ‖v‖ ^ 2 / 2 = (Real.cosh ε - 1) / 4 := by
      rw [hD2]; field_simp
    rw [hE]; linarith
  rw [show ε = Real.arcosh (Real.cosh ε) from (Real.arcosh_cosh (le_of_lt hε)).symm,
    Real.arcosh_lt_arcosh (by positivity) (Real.cosh_pos ε)]
  exact hkey

/-! ## The main assembly

From a nontrivial flat translation of the horosphere at `ξ`, Shimizu's lemma follows by the
Margulis lemma: a hypothetical element `γ` moving a deep point `u` to a deep point `γ • u`
conjugates the flat translation `δ` into an element `σ = γ⁻¹ δ γ` moving `u` little; Margulis
then forces `σ` to fix `ξ`, while `σ` is conjugate to `δ` and hence has the single fixed
boundary point `bd γ⁻¹ ξ`. -/

theorem cuspShimizuHoroball_of_flatTrans
    (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (ξ : E n) (hξ : ξ ∈ parFixed Γ)
    (hflat : ∃ (δ : Γ) (v : E n), v ≠ 0 ∧ inner ℝ v ξ = 0 ∧ bd (δ : PO n 1) ξ = ξ ∧
      (∀ u : E n, yc ξ ((δ : PO n 1) • u) = yc ξ u + v) ∧
      (∀ u : E n, lev ξ ((δ : PO n 1) • u) = lev ξ u)) :
    ∃ s : ℝ, 0 < s ∧ ∀ γ : Γ,
      bd (γ : PO n 1) ξ ≠ ξ →
      ∀ u : E n, lev ξ u < s → s ≤ lev ξ ((γ : PO n 1) • u) := by
  obtain ⟨δ, v, hv, hvξ, hδξ, hyc, hlev⟩ := hflat
  have hξS : ξ ∈ Sph n := hξ.1
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  -- the displacement formula and parabolicity of `δ`
  have hdisp : ∀ u : E n, hdist u ((δ : PO n 1) • u)
      = Real.arcosh (1 + (lev ξ u) ^ 2 * ‖v‖ ^ 2 / 2) :=
    fun u => hdist_flatTrans hξS hI (δ : PO n 1) v hyc hlev u
  have hδpar : IsParabolic (δ : PO n 1) :=
    flatTrans_isParabolic hξS hA hI (δ : PO n 1) v hv hyc hlev
  -- the Margulis constant for the bound `R = 1`
  obtain ⟨εM, hεMpos, hmc⟩ := margulisCusp n hn hA hI 1
  -- the level `s`
  set C : ℝ := min (Real.cosh εM) (Real.cosh 1) with hCdef
  have hC1 : 1 < C :=
    lt_min (Real.one_lt_cosh.mpr (ne_of_gt hεMpos)) (Real.one_lt_cosh.mpr one_ne_zero)
  have hv2 : 0 < ‖v‖ ^ 2 := by positivity
  have hvhalf : 0 < ‖v‖ ^ 2 / 2 := by positivity
  set s : ℝ := Real.sqrt (2 * (C - 1) / ‖v‖ ^ 2) / 2 with hsdef
  have hspos : 0 < s := by
    rw [hsdef]
    exact div_pos (Real.sqrt_pos.mpr (div_pos (by linarith) hv2)) (by norm_num)
  have hs2 : s ^ 2 * ‖v‖ ^ 2 / 2 = (C - 1) / 4 := by
    rw [hsdef, div_pow, Real.sq_sqrt (le_of_lt (div_pos (by linarith) hv2))]
    field_simp
    ring
  have hsC : 1 + s ^ 2 * ‖v‖ ^ 2 / 2 < C := by
    rw [hs2]; linarith
  -- the two monotonicity consequences we need
  have hbound : ∀ x : ℝ, 0 ≤ x → x < s →
      Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) < εM ∧
        Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) ≤ 1 := by
    intro x hx0 hx
    have hx2 : x ^ 2 < s ^ 2 := by nlinarith
    have hmul : x ^ 2 * (‖v‖ ^ 2 / 2) < s ^ 2 * (‖v‖ ^ 2 / 2) :=
      mul_lt_mul_of_pos_right hx2 hvhalf
    have hlt : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 < 1 + s ^ 2 * ‖v‖ ^ 2 / 2 := by
      have h1 : x ^ 2 * ‖v‖ ^ 2 / 2 = x ^ 2 * (‖v‖ ^ 2 / 2) := by ring
      have h2 : s ^ 2 * ‖v‖ ^ 2 / 2 = s ^ 2 * (‖v‖ ^ 2 / 2) := by ring
      linarith
    have hxpos : (0:ℝ) < 1 + x ^ 2 * ‖v‖ ^ 2 / 2 := by positivity
    have hltC : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 < C := lt_trans hlt hsC
    constructor
    · have hltε : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 < Real.cosh εM :=
        lt_of_lt_of_le hltC (by rw [hCdef]; exact min_le_left _ _)
      have hmono : Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) < Real.arcosh (Real.cosh εM) :=
        (Real.arcosh_lt_arcosh hxpos (Real.cosh_pos εM)).mpr hltε
      rwa [Real.arcosh_cosh (le_of_lt hεMpos)] at hmono
    · have hlt1 : 1 + x ^ 2 * ‖v‖ ^ 2 / 2 ≤ Real.cosh 1 :=
        le_of_lt (lt_of_lt_of_le hltC (by rw [hCdef]; exact min_le_right _ _))
      have hmono : Real.arcosh (1 + x ^ 2 * ‖v‖ ^ 2 / 2) ≤ Real.arcosh (Real.cosh 1) :=
        (Real.arcosh_le_arcosh hxpos (Real.cosh_pos 1)).mpr hlt1
      rwa [Real.arcosh_cosh (le_of_lt zero_lt_one)] at hmono
  refine ⟨s, hspos, ?_⟩
  intro γ hγ u hu
  by_contra hcon
  push_neg at hcon
  -- `u` is moved little by `δ`
  have h1 : hdist u ((δ : PO n 1) • u) < εM := by
    rw [hdisp u]
    exact (hbound (lev ξ u) (le_of_lt (lev_pos ξ hξS u)) hu).1
  -- the conjugated element `σ = γ⁻¹ δ γ`
  set σ : Γ := ⟨(γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1),
    mul_mem (mul_mem (inv_mem γ.2) δ.2) γ.2⟩ with hσdef
  have hσcoe : (σ : PO n 1) = (γ : PO n 1)⁻¹ * (δ : PO n 1) * (γ : PO n 1) := rfl
  have hσmul : (γ : PO n 1) * (σ : PO n 1) = (δ : PO n 1) * (γ : PO n 1) := by
    rw [hσcoe]; group
  -- `σ` also moves `u` very little
  have h2 : hdist u ((σ : PO n 1) • u) ≤ 1 := by
    have hA1 : hdist u ((σ : PO n 1) • u)
        = hdist ((γ : PO n 1) • u) ((γ : PO n 1) • ((σ : PO n 1) • u)) :=
      (hvd.isom_smul (γ : PO n 1) u ((σ : PO n 1) • u)).symm
    have hA2 : (γ : PO n 1) • ((σ : PO n 1) • u) = (δ : PO n 1) • ((γ : PO n 1) • u) := by
      rw [← hpb.mul_smul (γ : PO n 1) (σ : PO n 1) u, hσmul, hpb.mul_smul (δ : PO n 1)
        (γ : PO n 1) u]
    rw [hA1, hA2, hdisp ((γ : PO n 1) • u)]
    exact (hbound (lev ξ ((γ : PO n 1) • u)) (le_of_lt (lev_pos ξ hξS _)) hcon).2
  -- Margulis forces `σ` to fix `ξ`
  have hσpar : IsParabolic (σ : PO n 1) := by
    have h := isParabolic_conj hA hI ((γ : PO n 1)⁻¹) (δ : PO n 1) hδpar
    rw [hσcoe]
    simpa only [inv_inv] using h
  have hσfix : bd (σ : PO n 1) ξ = ξ :=
    hmc Γ hΓ.1 u ξ δ σ hδpar hξS hδξ h1 h2
  -- the unique fixed boundary point of `σ` is `bd γ⁻¹ ξ`
  have hγinvξS : bd (γ : PO n 1)⁻¹ ξ ∈ Sph n := hpb.bd_mem ((γ : PO n 1)⁻¹) ξ hξS
  have hbd1 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = ξ := by
    rw [← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel, hpb.bd_one ξ hξS]
  have hσfixinv : bd (σ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = bd (γ : PO n 1)⁻¹ ξ := by
    rw [hσcoe,
      hpb.bd_mul ((γ : PO n 1)⁻¹ * (δ : PO n 1)) (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) hγinvξS,
      hbd1,
      hpb.bd_mul ((γ : PO n 1)⁻¹) (δ : PO n 1) ξ hξS,
      hδξ]
  have heq : bd (γ : PO n 1)⁻¹ ξ = ξ :=
    paraUniqueFixed hpb hvd hσpar hξS hσfix hγinvξS hσfixinv
  -- hence `bd γ ξ = ξ`, contradicting `hγ`
  refine hγ ?_
  have h3 : bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) = bd (γ : PO n 1) ξ := by rw [heq]
  rw [← h3, ← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel,
    hpb.bd_one ξ hξS]

/-! ## Shimizu's lemma from the Margulis horoball packing

`Work.Mostow.cuspHoroballsPairwise` provides a `Γ`-equivariant height `ht` on `parFixed Γ` whose
horoballs are pairwise disjoint.  If `bd γ ξ ≠ ξ` and both `u` and `γ • u` are below the level
`ht ξ` at `ξ`, then `u` lies in the horoball at `ξ` and also (by equivariance and the Busemann
cocycle) in the horoball at `bd γ⁻¹ ξ`, contradicting disjointness.  Hence the horoball at level
`exp (ht ξ)` is precisely invariant, which is the statement. -/

theorem cuspShimizuHoroball_of_pairwise
    (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ parFixed Γ → bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (ht : E n → ℝ) (heq : IsEquivHeight Γ (parFixed Γ) ht)
    (hpw : (parFixed Γ).Pairwise
      (fun ξ η => Disjoint (horoball ξ (ht ξ)) (horoball η (ht η))))
    (ξ : E n) (hξ : ξ ∈ parFixed Γ) :
    ∃ s : ℝ, 0 < s ∧ ∀ γ : Γ,
      bd (γ : PO n 1) ξ ≠ ξ →
      ∀ u : E n, lev ξ u < s → s ≤ lev ξ ((γ : PO n 1) • u) := by
  have hpb : POBasic n := POBasic.ofProp hA
  have hvd : HypIsoData n := HypIsoData.ofProp hI
  have hξS : ξ ∈ Sph n := hξ.1
  refine ⟨Real.exp (ht ξ), Real.exp_pos _, ?_⟩
  intro γ hγ u hu
  by_contra hcon
  push_neg at hcon
  have hu' : busemann ξ u < ht ξ := by
    have h := lev_eq_exp hξS u
    rw [h] at hu
    exact (Real.exp_lt_exp).mp hu
  have hγu' : busemann ξ ((γ : PO n 1) • u) < ht ξ := by
    have h := lev_eq_exp hξS ((γ : PO n 1) • u)
    rw [h] at hcon
    exact (Real.exp_lt_exp).mp hcon
  have hξγS : bd (γ : PO n 1)⁻¹ ξ ∈ Sph n := hpb.bd_mem _ _ hξS
  have hξγP : bd (γ : PO n 1)⁻¹ ξ ∈ parFixed Γ := parFixed_invariant hA hI Γ γ⁻¹ hξ
  have hbus : busemann (bd (γ : PO n 1)⁻¹ ξ) u
      = busemann ξ ((γ : PO n 1) • u) + bCocy (γ : PO n 1)⁻¹ ξ := by
    have h := hvd.busemann_cocycle (γ : PO n 1)⁻¹ ξ ((γ : PO n 1) • u) hξS
    have h1 : (γ : PO n 1)⁻¹ • ((γ : PO n 1) • u) = u := by
      rw [← hpb.mul_smul, inv_mul_cancel, hpb.one_smul]
    have hcoc : bCocy (γ : PO n 1)⁻¹ ξ
        = busemann (bd (γ : PO n 1)⁻¹ ξ) ((γ : PO n 1)⁻¹ • (0 : E n)) := rfl
    rw [h1, ← hcoc] at h
    exact h
  have heqγ : ht (bd (γ : PO n 1)⁻¹ ξ) = ht ξ + bCocy (γ : PO n 1)⁻¹ ξ := heq γ⁻¹ ξ hξ
  have hmem1 : u ∈ horoball (bd (γ : PO n 1)⁻¹ ξ) (ht (bd (γ : PO n 1)⁻¹ ξ)) := by
    simp only [horoball, Set.mem_ofPred_eq]
    rw [hbus, heqγ]
    linarith
  have hmem2 : u ∈ horoball ξ (ht ξ) := by
    simp only [horoball, Set.mem_ofPred_eq]
    exact hu'
  have hne : ξ ≠ bd (γ : PO n 1)⁻¹ ξ := by
    intro h
    apply hγ
    have h2 : bd (γ : PO n 1) ξ = bd (γ : PO n 1) (bd (γ : PO n 1)⁻¹ ξ) := by rw [← h]
    rw [h2, ← hpb.bd_mul (γ : PO n 1) ((γ : PO n 1)⁻¹) ξ hξS, mul_inv_cancel, hpb.bd_one ξ hξS]
  exact (Set.disjoint_left.mp (hpw hξ hξγP hne)) hmem2 hmem1

theorem cuspShimizuHoroball (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hΓ : Submission.Mostow.HypLattice Γ)
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    ∃ s : ℝ, 0 < s ∧ ∀ γ : Γ,
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ ≠ ξ →
      ∀ u : Submission.Mostow.E n, Work.Mostow.lev ξ u < s →
        s ≤ Work.Mostow.lev ξ ((γ : LeanEval.Geometry.MostowRigidity.PO n 1) • u) := by
  have hBb : ∀ m, Submission.Mostow.BieberbachProp m := fun m => bieberbach m
  have hξS : ξ ∈ Sph n := hξ.1
  have hpb : POBasic n := POBasic.ofProp hA
  -- the cusp stabiliser is cocompact on the horosphere at `ξ`
  obtain ⟨K, hKc, hK⟩ := horosphereStabCocompactAux n hn hA hI Γ hΓ hvan ξ hξ
  -- hence the cusp stabiliser contains a parabolic flat translation
  obtain ⟨δ, hδpar, hδξ, hδcoc, v, hv, hvξ, hyc⟩ :=
    csha_flatTransOfCocompact n hn hA hI hBb Γ hΓ hvan ξ hξ ⟨K, hKc, hK⟩
  -- the vanishing cocycle gives preservation of the horospherical levels
  have hlev : ∀ u : E n, lev ξ ((δ : PO n 1) • u) = lev ξ u := by
    intro u
    have h := hvd_lev_smul_self hA hI ξ hξS (δ : PO n 1) u hδξ
    have h0 : lev ξ ((δ : PO n 1) • (0 : E n)) = 1 := by
      have h1 : busemann ξ ((δ : PO n 1) • (0 : E n)) = 0 := by
        have h2 : bCocy (δ : PO n 1) ξ = busemann ξ ((δ : PO n 1) • (0 : E n)) := by
          rw [bCocy, hδξ]
        rw [← h2]; exact hδcoc
      rw [lev_eq_exp hξS, h1, Real.exp_zero]
    rw [h, h0, mul_one]
  exact cuspShimizuHoroball_of_flatTrans n hn hA hI Γ hΓ hvan ξ hξ
    ⟨δ, v, hv, hvξ, hδξ, hyc, hlev⟩

end

end Work.Mostow
