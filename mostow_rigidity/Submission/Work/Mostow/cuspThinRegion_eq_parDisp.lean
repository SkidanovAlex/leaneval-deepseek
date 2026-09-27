import Mathlib
import Submission.Work.Mostow.cuspParDispDefs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.cuspHoro.flatActLevelOne
import Submission.Work.Mostow.cuspHoro.flatDispEqLevOne
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.horSpec
import Submission.Work.Mostow.rayStrictHoro

/-!
# The Margulis thin region as a sublevel set of the flat displacement

For a discrete subgroup `Γ ≤ PO(n,1)`, a cusp `ξ ∈ parFixed Γ` at which the Busemann cocycle of
the stabiliser vanishes (`bCocy γ ξ = 0` for all `γ ∈ Γ` fixing `ξ`), and `y ∈ ξ^⊥`, we prove

* `parDisp Γ ξ y > 0`, and
* `u ∈ cuspThinRegion Γ ξ ε ↔ lev ξ u * parDisp Γ ξ (yc ξ u) < cEps ε`.

The two ingredients are the horospherical form of the law of cosines (`levYcFormula`)

`cosh (hdist u (γ • u)) = 1 + (lev ξ u)^2 / 2 * ‖yc ξ u - flatAct ξ γ (yc ξ u)‖^2`

for a level-preserving `γ` fixing `ξ` (note `lev ξ (γ • u) = lev ξ u` because `bCocy γ ξ = 0`),
and the discreteness of `Γ`, which bounds the flat displacements away from `0`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- The set of flat displacements of the parabolic elements of `Γ` fixing `ξ`, whose infimum is
`parDisp Γ ξ y`. -/
def parDispSet (Γ : Subgroup (PO n 1)) (ξ y : E n) : Set ℝ :=
  {r : ℝ | ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
    r = ‖y - flatAct ξ (γ : PO n 1) y‖}

lemma parDisp_eq_sInf (Γ : Subgroup (PO n 1)) (ξ y : E n) :
    parDisp Γ ξ y = sInf (parDispSet Γ ξ y) := rfl

/-- For `a > 0` and a nonempty set `S` bounded below,
`∃ s ∈ S, a * s < c ↔ a * sInf S < c`. -/
lemma exists_mul_lt_iff_mul_sInf_lt {a c : ℝ} (ha : 0 < a) {S : Set ℝ}
    (hne : S.Nonempty) (hbdd : BddBelow S) :
    (∃ s ∈ S, a * s < c) ↔ a * sInf S < c := by
  constructor
  · rintro ⟨s, hs, hlt⟩
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (csInf_le hbdd hs) (le_of_lt ha)) hlt
  · intro h
    by_contra hc
    push_neg at hc
    have hle : c / a ≤ sInf S := by
      refine le_csInf hne ?_
      intro s hs
      exact (div_le_iff₀ ha).mpr (by rw [mul_comm]; exact hc s hs)
    have h2 : a * (c / a) = c := by field_simp
    have := mul_le_mul_of_nonneg_left hle (le_of_lt ha)
    linarith

/-- **Per-element equivalence.**  For an isometry `γ` fixing `ξ` and preserving the horospherical
levels `lev ξ`, the displacement of the point `u` is below `ε` exactly when the product of the
level `lev ξ u` with the flat displacement of `γ` at `yc ξ u` is below `cEps ε`. -/
theorem hdist_lt_iff_lev_mul_flatAct (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {ξ : E n}
    (hξS : ξ ∈ Sph n) (γ : PO n 1)
    (hγ : bd γ ξ = ξ)
    (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u)
    (u : E n) {ε : ℝ} (hε : 0 < ε) :
    hdist u (γ • u) < ε ↔
      lev ξ u * ‖yc ξ u - flatAct ξ γ (yc ξ u)‖ < cEps ε := by
  have hB : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  have h0 : lev ξ (γ • (0 : E n)) = 1 := by
    rw [hlev (0 : E n), Work.Mostow.cuspHoro.lev_zero]
  have hcosh := cosh_hdist_smul_horo hB hId hξS hγ h0 u
  have hL : 0 < lev ξ u := lev_pos ξ hξS u
  have hd : 0 ≤ ‖yc ξ u - flatAct ξ γ (yc ξ u)‖ := norm_nonneg _
  have hEpspos : 0 < 2 * (Real.cosh ε - 1) := by
    have : 1 < Real.cosh ε := Real.one_lt_cosh.mpr (ne_of_gt hε)
    linarith
  have hcEps_sq : (cEps ε) ^ 2 = 2 * (Real.cosh ε - 1) := by
    rw [cEps, Real.sq_sqrt (le_of_lt hEpspos)]
  have hcEps_nn : 0 ≤ cEps ε := Real.sqrt_nonneg _
  have hcosh_eps : Real.cosh ε = 1 + (cEps ε) ^ 2 / 2 := by
    rw [hcEps_sq]; ring
  calc hdist u (γ • u) < ε
      ↔ Real.cosh (hdist u (γ • u)) < Real.cosh ε := by
          rw [Real.cosh_lt_cosh, abs_of_nonneg (hdist_nonneg u (γ • u)),
            abs_of_nonneg (le_of_lt hε)]
    _ ↔ 1 + (lev ξ u) ^ 2 / 2 * ‖yc ξ u - flatAct ξ γ (yc ξ u)‖ ^ 2
          < 1 + (cEps ε) ^ 2 / 2 := by
          rw [hcosh, hcosh_eps]
    _ ↔ (lev ξ u * ‖yc ξ u - flatAct ξ γ (yc ξ u)‖) ^ 2 < (cEps ε) ^ 2 := by
          constructor <;> intro hh <;>
            nlinarith [sq_nonneg (lev ξ u),
              sq_nonneg ‖yc ξ u - flatAct ξ γ (yc ξ u)‖]
    _ ↔ lev ξ u * ‖yc ξ u - flatAct ξ γ (yc ξ u)‖ < cEps ε := by
          rw [sq_lt_sq, abs_of_nonneg (mul_nonneg (le_of_lt hL) hd), abs_of_nonneg hcEps_nn]

/-- **Positivity of the flat displacement.**  For a discrete `Γ`, a cusp `ξ` at which the Busemann
cocycle vanishes, and `y ∈ ξ^⊥`, the infimum of the flat displacements of the parabolic elements
of `Γ` fixing `ξ` at `y` is strictly positive. -/
theorem parDisp_pos_of_discrete (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ)) {ξ : E n}
    (hξS : ξ ∈ Sph n)
    (hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0)
    (hne : ∃ γ : Γ, IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ)
    {y : E n} (hy : inner ℝ y ξ = 0) :
    0 < parDisp Γ ξ y := by
  classical
  rw [parDisp_eq_sInf]
  have hB : POBasic n := POBasic.ofProp hA
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- the point of level `1` with flat coordinate `y`
  set u : E n := hptOf ξ y 1 with hu
  have hlevu : lev ξ u = 1 := by
    rw [hu]; exact (hptOf_level ξ hξS 1 one_pos y hy).1
  have hycu : yc ξ u = y := by
    rw [hu]; exact (hptOf_level ξ hξS 1 one_pos y hy).2
  have hlev_of : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ →
      ∀ v : E n, lev ξ ((γ : PO n 1) • v) = lev ξ v :=
    fun γ hγ v => Work.Mostow.cuspHoro.lev_smul_of_stab hI hξS hstab γ hγ v
  -- the displacement formula at level `1`
  have hdisp : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ →
      Real.cosh (hdist u ((γ : PO n 1) • u))
        = 1 + ‖y - flatAct ξ (γ : PO n 1) y‖ ^ 2 / 2 := by
    intro γ hγ
    have h0 : lev ξ ((γ : PO n 1) • (0 : E n)) = 1 := by
      rw [hlev_of γ hγ (0 : E n), Work.Mostow.cuspHoro.lev_zero]
    have hc := cosh_hdist_smul_horo hB hId hξS hγ h0 u
    rw [hlevu, hycu] at hc
    exact hc.trans (by ring)
  -- the finite near-stabiliser of the base point
  let R : ℝ := 2 * hdist (0 : E n) u + Real.arcosh (3 / 2)
  have hfin : ({γ : Γ | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R}).Finite :=
    finite_nearStab hB hId hdisc R
  have hmem_fin : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ →
      ‖y - flatAct ξ (γ : PO n 1) y‖ ≤ 1 → hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R := by
    intro γ hγ hd
    have hcosh_le : Real.cosh (hdist u ((γ : PO n 1) • u)) ≤ 3 / 2 := by
      rw [hdisp γ hγ]
      have h2 : ‖y - flatAct ξ (γ : PO n 1) y‖ ^ 2 ≤ 1 := by
        have hdnn : 0 ≤ ‖y - flatAct ξ (γ : PO n 1) y‖ := norm_nonneg _
        nlinarith [mul_nonneg hdnn (sub_nonneg.mpr hd)]
      linarith
    have hdist_le : hdist u ((γ : PO n 1) • u) ≤ Real.arcosh (3 / 2) := by
      have h1 : hdist u ((γ : PO n 1) • u)
          = Real.arcosh (Real.cosh (hdist u ((γ : PO n 1) • u))) :=
        (Real.arcosh_cosh (hdist_nonneg u ((γ : PO n 1) • u))).symm
      rw [h1]
      exact (Real.arcosh_le_arcosh (Real.cosh_pos _) (by norm_num)).mpr hcosh_le
    have ht1 := hId.triangle (0 : E n) u ((γ : PO n 1) • (0 : E n))
    have ht2 := hId.triangle u ((γ : PO n 1) • u) ((γ : PO n 1) • (0 : E n))
    have hiso : hdist ((γ : PO n 1) • u) ((γ : PO n 1) • (0 : E n)) = hdist u (0 : E n) :=
      hId.isom_smul (γ : PO n 1) u (0 : E n)
    have hsym : hdist u (0 : E n) = hdist (0 : E n) u := hId.symm u (0 : E n)
    show hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ 2 * hdist (0 : E n) u + Real.arcosh (3 / 2)
    linarith
  -- the finite set of displacements of the small parabolic stabilising elements
  have hFfin : ({γ : Γ | IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
      hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R}).Finite :=
    hfin.subset (fun γ hγ => hγ.2.2)
  have hWfin : ((fun γ : Γ => ‖y - flatAct ξ (γ : PO n 1) y‖) ''
      {γ : Γ | IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
        hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R}).Finite :=
    hFfin.image (fun γ : Γ => ‖y - flatAct ξ (γ : PO n 1) y‖)
  let T : Finset ℝ := insert 1 hWfin.toFinset
  have hTne : T.Nonempty := ⟨1, Finset.mem_insert_self 1 hWfin.toFinset⟩
  obtain ⟨γ₁, hγ₁p, hγ₁f⟩ := hne
  have hneS : (parDispSet Γ ξ y).Nonempty := ⟨_, γ₁, hγ₁p, hγ₁f, rfl⟩
  -- positivity of the minimum over the finite set
  have hminpos : 0 < T.min' hTne := by
    have hm : T.min' hTne ∈ T := Finset.min'_mem T hTne
    rcases Finset.mem_insert.mp hm with h1 | h1
    · rw [h1]; norm_num
    · have h1' : T.min' hTne ∈ ((fun γ : Γ => ‖y - flatAct ξ (γ : PO n 1) y‖) ''
          {γ : Γ | IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
            hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R}) :=
        (Set.Finite.mem_toFinset hWfin).mp h1
      obtain ⟨γ, hγS, hγeq⟩ := (Set.mem_image _ _ _).mp h1'
      have hγpar : IsParabolic (γ : PO n 1) := hγS.1
      have hγfix : bd (γ : PO n 1) ξ = ξ := hγS.2.1
      have hpos : 0 < ‖y - flatAct ξ (γ : PO n 1) y‖ := by
        by_contra hc
        push_neg at hc
        have hd0 : ‖y - flatAct ξ (γ : PO n 1) y‖ = 0 := le_antisymm hc (norm_nonneg _)
        have hfa : flatAct ξ (γ : PO n 1) y = y :=
          (sub_eq_zero.mp (norm_eq_zero.mp hd0)).symm
        have hycγ : yc ξ ((γ : PO n 1) • u) = y := by
          rw [Work.Mostow.cuspHoro.yc_smul_eq_flatAct hA hI ξ hξS (γ : PO n 1) hγfix
            (hlev_of γ hγfix) u, hycu, hfa]
        have hlevγ : lev ξ ((γ : PO n 1) • u) = 1 := by
          rw [hlev_of γ hγfix u, hlevu]
        have hrepr := hptOf_yc ξ hξS (lev ξ ((γ : PO n 1) • u))
          (lev_pos ξ hξS ((γ : PO n 1) • u)) ((γ : PO n 1) • u) rfl
        rw [hlevγ, hycγ] at hrepr
        exact hγpar.1 u (by rw [← hrepr, hu])
      rwa [← hγeq]
  -- the minimum is a lower bound for the whole set
  have hmin_le : T.min' hTne ≤ sInf (parDispSet Γ ξ y) := by
    refine le_csInf hneS ?_
    intro b hb
    simp only [parDispSet] at hb
    obtain ⟨γ, hγpar, hγfix, rfl⟩ := hb
    by_cases hd : ‖y - flatAct ξ (γ : PO n 1) y‖ ≤ 1
    · have hγS : IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
          hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R :=
        ⟨hγpar, hγfix, hmem_fin γ hγfix hd⟩
      have hWmem : ‖y - flatAct ξ (γ : PO n 1) y‖ ∈ ((fun γ : Γ =>
          ‖y - flatAct ξ (γ : PO n 1) y‖) ''
          {γ : Γ | IsParabolic (γ : PO n 1) ∧ bd (γ : PO n 1) ξ = ξ ∧
            hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ R}) :=
        (Set.mem_image _ _ _).mpr ⟨γ, hγS, rfl⟩
      have hmem : ‖y - flatAct ξ (γ : PO n 1) y‖ ∈ hWfin.toFinset :=
        (Set.Finite.mem_toFinset hWfin).mpr hWmem
      exact Finset.min'_le T _ (Finset.mem_insert_of_mem hmem)
    · push_neg at hd
      refine le_trans (Finset.min'_le T 1 (Finset.mem_insert_self 1 hWfin.toFinset)) ?_
      linarith
  linarith

theorem cuspThinRegion_eq_parDisp (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1))
    (hdisc : IsDiscrete (SetLike.coe Γ))
    (hvan : ∀ (γ : Γ) ξ, ξ ∈ Work.Mostow.parFixed Γ →
      Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0)
    {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Work.Mostow.parFixed Γ) :
    (∀ y : Submission.Mostow.E n, inner ℝ y ξ = 0 → 0 < Work.Mostow.parDisp Γ ξ y) ∧
    (∀ ε : ℝ, 0 < ε → ∀ u : Submission.Mostow.E n,
      u ∈ Work.Mostow.cuspThinRegion Γ ξ ε ↔
        Work.Mostow.lev ξ u * Work.Mostow.parDisp Γ ξ (Work.Mostow.yc ξ u) <
          Work.Mostow.cEps ε) := by
  classical
  have hξS : ξ ∈ Sph n := hξ.1
  have hstab : ∀ (γ : Γ), bd (γ : PO n 1) ξ = ξ → bCocy (γ : PO n 1) ξ = 0 :=
    fun γ hγ => hvan γ ξ hξ hγ
  obtain ⟨γ₀, hγ₀par, hγ₀fix⟩ := hξ.2
  refine ⟨?_, ?_⟩
  · intro y hy
    exact parDisp_pos_of_discrete n hA hI Γ hdisc hξS hstab ⟨γ₀, hγ₀par, hγ₀fix⟩ hy
  · intro ε hε u
    have hper : (∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ξ = ξ ∧
          hdist u ((q : PO n 1) • u) < ε) ↔
        (∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ξ = ξ ∧
          lev ξ u * ‖yc ξ u - flatAct ξ (q : PO n 1) (yc ξ u)‖ < cEps ε) := by
      constructor
      · rintro ⟨q, hp, hf, hd⟩
        exact ⟨q, hp, hf, (hdist_lt_iff_lev_mul_flatAct n hA hI hξS (q : PO n 1) hf
          (fun v => Work.Mostow.cuspHoro.lev_smul_of_stab hI hξS hstab q hf v) u hε).mp hd⟩
      · rintro ⟨q, hp, hf, hd⟩
        exact ⟨q, hp, hf, (hdist_lt_iff_lev_mul_flatAct n hA hI hξS (q : PO n 1) hf
          (fun v => Work.Mostow.cuspHoro.lev_smul_of_stab hI hξS hstab q hf v) u hε).mpr hd⟩
    have hSne : (parDispSet Γ ξ (yc ξ u)).Nonempty := ⟨_, γ₀, hγ₀par, hγ₀fix, rfl⟩
    have hSbdd : BddBelow (parDispSet Γ ξ (yc ξ u)) :=
      ⟨0, fun s hs => by
        simp only [parDispSet, Set.mem_setOf_eq] at hs
        obtain ⟨γ, -, -, rfl⟩ := hs
        positivity⟩
    have hconv : (∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ξ = ξ ∧
          lev ξ u * ‖yc ξ u - flatAct ξ (q : PO n 1) (yc ξ u)‖ < cEps ε) ↔
        (∃ s ∈ parDispSet Γ ξ (yc ξ u), lev ξ u * s < cEps ε) := by
      constructor
      · rintro ⟨q, hp, hf, hlt⟩
        exact ⟨_, by simp only [parDispSet, Set.mem_setOf_eq]; exact ⟨q, hp, hf, rfl⟩, hlt⟩
      · rintro ⟨s, hs, hlt⟩
        simp only [parDispSet, Set.mem_setOf_eq] at hs
        obtain ⟨q, hp, hf, rfl⟩ := hs
        exact ⟨q, hp, hf, hlt⟩
    change (∃ q : Γ, IsParabolic (q : PO n 1) ∧ bd (q : PO n 1) ξ = ξ ∧
        hdist u ((q : PO n 1) • u) < ε) ↔
      lev ξ u * parDisp Γ ξ (yc ξ u) < cEps ε
    rw [hper, hconv, exists_mul_lt_iff_mul_sInf_lt (lev_pos ξ hξS u) hSne hSbdd,
      parDisp_eq_sInf]

end Work.Mostow
