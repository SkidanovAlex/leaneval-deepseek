import Mathlib
import Submission.Work.SSGRoute.wordBarDefs
import Submission.Work.SSGRoute.EKerDefs
import Submission.Work.SSGRoute.pSeries_inter_lcs_general
import Submission.Work.SSGRoute.freeLie_regular_odd
import Submission.Work.SSGRoute.diagOdd.basic
import Submission.Work.SSGRoute.FF5.Theta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Port of the transport `E(j,j) ≅ barLie (Fin n × G) j`

Self-contained copy of the transport construction of
`Submission/Work/SSGRoute/diagOdd/psi.lean`; all declarations carry the `ebl_` prefix so that
`E_iso_barLie` does not depend on the (concurrently edited) original file.
-/

noncomputable section

open Work.CohomologicalShrinking
open Work.SSGRoute.prop5

/-!
# The transport `E(j,j) ≅ barLie X j`

`ebl_Tmap g = redZ (θ g)` is the degree-`j` component of `g ∈ γ_j` modulo `2`.  It kills exactly
`γ_j^2 γ_{j+1} = γ_j ⊓ P_{j+1}`, so it factors through the graded piece `E(j,j)`, and it is onto
`barLie X j`.  It is also equivariant for the relabelling action.
-/

noncomputable section

open Work.CohomologicalShrinking
open Work.SSGRoute.prop5

namespace Work.SSGRoute.diagOdd

universe u

variable {G : Type u} [Group G] {n : ℕ}

/-! ## The graded piece is an elementary abelian `2`-group -/

/-! ## The refined term `F(n)^{(j,j)}` -/

theorem ebl_flowTerm_tauSucc_self (j : ℕ) :
    flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2
      = Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
  rw [tauSucc_of_le (le_refl j)]
  exact refinedTerm_one 2 _ (j + 1)

theorem ebl_flowTerm_jj (j : ℕ) :
    flowTerm 2 G n j j
      = (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1) ⊔
        Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
  have h : (Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j - 1) ⊓
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1)) ⊔
      Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j
      = (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1) ⊔
        Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
    rw [inf_eq_right.mpr (Work.ProP.lowerCentralSeries_le_pCentralSeries 2 _ (j - 1))]
  exact h

theorem ebl_mem_ker_iff (j : ℕ) (x : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) :
    (QuotientGroup.mk'
        ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) x
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      ∈ (Work.SSGRoute.flowQuotSucc 2 G n j j).ker
    ↔ (x : Work.Shrinking.freeOperatorGroup G n) ∈ flowTerm 2 G n j j := by
  rw [MonoidHom.mem_ker, flowQuotSucc_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]

theorem ebl_lcs_le_flowTerm_jj (j : ℕ) :
    (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1) ≤
      flowTerm 2 G n j j := by
  rw [ebl_flowTerm_jj]
  exact le_sup_left

/-! ## The `δ`-action on `γ_j` -/

def ebl_PhiG (σ : (Fin n × G) ≃ (Fin n × G)) (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1)) :=
  ⟨FreeGroup.freeGroupCongr σ (g : Work.Shrinking.freeOperatorGroup G n),
    freeGroupCongr_mem (Fin n × G) σ j g.2⟩

theorem ebl_PhiG_apply (σ : (Fin n × G) ≃ (Fin n × G)) (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ((ebl_PhiG σ j g : _) : Work.Shrinking.freeOperatorGroup G n)
      = FreeGroup.freeGroupCongr σ (g : Work.Shrinking.freeOperatorGroup G n) := rfl

theorem ebl_PhiG_basisPerm_apply (δ : G) (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ((ebl_PhiG (basisPerm G n δ) j g : _) : Work.Shrinking.freeOperatorGroup G n)
      = δ • (g : Work.Shrinking.freeOperatorGroup G n) :=
  (smul_eq_freeGroupCongr δ (g : Work.Shrinking.freeOperatorGroup G n)).symm

theorem ebl_PhiG_mul (σ : (Fin n × G) ≃ (Fin n × G)) (j : ℕ)
    (a b : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_PhiG σ j (a * b) = ebl_PhiG σ j a * ebl_PhiG σ j b := by
  refine Subtype.ext ?_
  show FreeGroup.freeGroupCongr σ ((a : Work.Shrinking.freeOperatorGroup G n)
      * (b : Work.Shrinking.freeOperatorGroup G n))
    = ((ebl_PhiG σ j a : _) : Work.Shrinking.freeOperatorGroup G n)
      * ((ebl_PhiG σ j b : _) : Work.Shrinking.freeOperatorGroup G n)
  rw [map_mul, ebl_PhiG_apply, ebl_PhiG_apply]

theorem ebl_PhiG_one (σ : (Fin n × G) ≃ (Fin n × G)) (j : ℕ) :
    ebl_PhiG σ j 1 = 1 := by
  refine Subtype.ext ?_
  show FreeGroup.freeGroupCongr σ (1 : Work.Shrinking.freeOperatorGroup G n) = (1 : _)
  rw [map_one]

theorem ebl_PhiG_inv (σ : (Fin n × G) ≃ (Fin n × G)) (j : ℕ)
    (a : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_PhiG σ j a⁻¹ = (ebl_PhiG σ j a)⁻¹ := by
  have h := ebl_PhiG_mul σ j a a⁻¹
  rw [mul_inv_cancel, ebl_PhiG_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-! ## The projection `γ_j ↠ E(j,j)` -/

noncomputable def ebl_phiGamma (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker) :=
  ⟨QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
      ⟨(g : Work.Shrinking.freeOperatorGroup G n), Subgroup.mem_top _⟩,
    (ebl_mem_ker_iff j ⟨(g : Work.Shrinking.freeOperatorGroup G n), Subgroup.mem_top _⟩).mpr
      (ebl_lcs_le_flowTerm_jj j g.2)⟩

theorem ebl_phiGamma_apply (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ((ebl_phiGamma (G := G) (n := n) j g : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker))
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
          ⟨(g : Work.Shrinking.freeOperatorGroup G n), Subgroup.mem_top _⟩ := rfl

theorem ebl_phiGamma_mul (j : ℕ)
    (a b : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_phiGamma (G := G) (n := n) j (a * b)
      = ebl_phiGamma (G := G) (n := n) j a * ebl_phiGamma (G := G) (n := n) j b := by
  refine Subtype.ext ?_
  show (QuotientGroup.mk' _ ⟨((a : _) * (b : _)), Subgroup.mem_top _⟩ :
      flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
    = QuotientGroup.mk' _ ⟨(a : _), Subgroup.mem_top _⟩
      * QuotientGroup.mk' _ ⟨(b : _), Subgroup.mem_top _⟩
  rw [← map_mul]
  rfl

theorem ebl_phiGamma_one (j : ℕ) :
    ebl_phiGamma (G := G) (n := n) j 1 = 1 := by
  refine Subtype.ext ?_
  show (QuotientGroup.mk' _ (1 : ↥(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) :
      flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = 1
  exact map_one _

theorem ebl_phiGamma_inv (j : ℕ)
    (a : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_phiGamma (G := G) (n := n) j a⁻¹ = (ebl_phiGamma (G := G) (n := n) j a)⁻¹ := by
  refine Subtype.ext ?_
  show (QuotientGroup.mk' _ ⟨((a⁻¹ : ↥((⊤ : Subgroup
        (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
        Work.Shrinking.freeOperatorGroup G n), Subgroup.mem_top _⟩ :
      flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
    = (QuotientGroup.mk' _ ⟨(a : Work.Shrinking.freeOperatorGroup G n),
        Subgroup.mem_top _⟩)⁻¹
  rw [← map_inv]
  rfl

theorem ebl_phiGamma_surj (j : ℕ) (hj : 1 ≤ j) :
    Function.Surjective (ebl_phiGamma (G := G) (n := n) j) := by
  intro k
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
    (k : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
  have hker : (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤) x
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      ∈ (Work.SSGRoute.flowQuotSucc 2 G n j j).ker := by
    rw [hx]; exact k.2
  have hxm : (x : Work.Shrinking.freeOperatorGroup G n) ∈ flowTerm 2 G n j j :=
    (ebl_mem_ker_iff (G := G) (n := n) j x).mp hker
  have hxm' : (x : Work.Shrinking.freeOperatorGroup G n) ∈
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1) ⊔
        Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
    rwa [ebl_flowTerm_jj] at hxm
  obtain ⟨g, hg, t, ht, hgt⟩ := Subgroup.mem_sup_of_normal_right.mp hxm'
  refine ⟨⟨g, hg⟩, ?_⟩
  refine Subtype.ext ?_
  rw [ebl_phiGamma_apply, ← hx]
  have ht1 : (QuotientGroup.mk'
      ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
      ⟨t, Subgroup.mem_top _⟩ : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      ebl_flowTerm_tauSucc_self j]
    exact ht
  have hxeq : x = (⟨g, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup
      (Work.Shrinking.freeOperatorGroup G n))) * ⟨t, Subgroup.mem_top _⟩ := by
    refine Subtype.ext ?_
    show (x : Work.Shrinking.freeOperatorGroup G n) = g * t
    exact hgt.symm
  rw [hxeq, map_mul, ht1, mul_one]

/-! ## The `δ`-action on the graded piece -/

def ebl_PhiK (δ : G) (j : ℕ) (k : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker)) :
    ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker) :=
  ⟨flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ (k : _), by
    rw [MonoidHom.mem_ker,
      show flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ (k : _)
        = δ • (k : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) from rfl,
      Work.SSGRoute.flowQuotSucc_smul, k.2, smul_one]⟩

theorem ebl_PhiK_apply (δ : G) (j : ℕ)
    (k : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker)) :
    ((ebl_PhiK (G := G) (n := n) δ j k : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker))
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2)
      = δ • (k : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) := rfl

theorem ebl_PhiK_phiGamma (δ : G) (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_PhiK (G := G) (n := n) δ j (ebl_phiGamma (G := G) (n := n) j g)
      = ebl_phiGamma (G := G) (n := n) j (ebl_PhiG (basisPerm G n δ) j g) := by
  refine Subtype.ext ?_
  rw [ebl_PhiK_apply, ebl_phiGamma_apply, ebl_phiGamma_apply]
  show flowAction 2 G n (tauSucc j j).1 (tauSucc j j).2 δ
      (QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨(g : Work.Shrinking.freeOperatorGroup G n), Subgroup.mem_top _⟩)
    = QuotientGroup.mk' ((flowTerm 2 G n (tauSucc j j).1 (tauSucc j j).2).subgroupOf ⊤)
        ⟨((ebl_PhiG (basisPerm G n δ) j g : _) : Work.Shrinking.freeOperatorGroup G n),
          Subgroup.mem_top _⟩
  rw [flowAction_mk_top, ebl_PhiG_basisPerm_apply]

/-! ## The mod-`2` Lie part as a quotient of the Lie span -/

theorem ebl_exists_of_mem_barLie (X : Type u) (j : ℕ) {v : WordBar X} (hv : v ∈ barLie X j) :
    ∃ a ∈ lieSpan X j, redZ X a = v := by
  refine Submodule.span_induction (p := fun v _ => ∃ a ∈ lieSpan X j, redZ X a = v) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨c, hc⟩
    exact ⟨brkMon X c.1, Submodule.subset_span ⟨c.1, c.2, rfl⟩, hc⟩
  · exact ⟨0, Submodule.zero_mem _, by rw [map_zero]⟩
  · intro v w _ _ ⟨a, ha, haeq⟩ ⟨b, hb, hbeq⟩
    exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [map_add, haeq, hbeq]⟩
  · intro t v _ ⟨a, ha, haeq⟩
    refine ⟨((t.val : ℤ)) • a, Submodule.smul_mem _ _ ha, ?_⟩
    rw [map_zsmul, haeq]
    show ((t.val : ℤ)) • v = t • v
    rw [show ((t.val : ℤ)) = (((t.val : ℕ) : ℤ)) from rfl,
      ← Int.cast_smul_eq_zsmul (ZMod 2) ((t.val : ℕ) : ℤ) v]
    rw [show ((((t.val : ℕ) : ℤ) : ZMod 2)) = t from by
      rw [Int.cast_natCast]; exact ZMod.natCast_zmod_val t]

/-! ## Reduction mod `2` -/

theorem ebl_redZ_eq_zero_iff (X : Type u) (a : FreeAssoc X) :
    redZ X a = 0 ↔ ∃ b : FreeAssoc X, a = (2 : ℤ) • b := by
  constructor
  · intro h
    have hcoeff : ∀ w : FreeMonoid X, ((a.coeff w : ℤ) : ZMod 2) = 0 := by
      intro w
      have hc := congrArg (fun v : WordBar X => v w) h
      simpa [redZ_apply, MonoidAlgebra.coeff_mapRingHom] using hc
    refine ⟨MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun z : ℤ => z / 2) (by norm_num) a.coeff),
      ?_⟩
    apply MonoidAlgebra.ext
    ext w
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, MonoidAlgebra.coeff_ofCoeff,
      Finsupp.mapRange_apply]
    exact (Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (hcoeff w))).symm
  · rintro ⟨b, rfl⟩
    rw [map_zsmul]
    rw [← Int.cast_smul_eq_zsmul (ZMod 2) (2 : ℤ) (redZ X b)]
    rw [show (((2 : ℤ) : ZMod 2)) = 0 from by decide, zero_smul]

theorem ebl_exists_two_smul_theta_of_mem_powSubgroup {X : Type u} (j : ℕ) (hj : 1 ≤ j)
    (a : FreeGroup X) (h2 : a ∈ Work.Shrinking.powSubgroup 2
      ((⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))) :
    ∃ (h : a ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1))
      (c : FreeAssoc X), theta X j hj a h = (2 : ℤ) • c := by
  rw [Work.Shrinking.powSubgroup] at h2
  induction h2 using Subgroup.closure_induction with
  | mem z hz =>
      rcases hz with ⟨x, hx, rfl⟩
      refine ⟨Subgroup.pow_mem _ hx 2, theta X j hj x hx, ?_⟩
      rw [two_smul]
      simpa only [pow_two] using theta_mul (X := X) j hj x x hx hx
  | one => exact ⟨Subgroup.one_mem _, 0, by rw [theta_one, two_smul, add_zero]⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨ha', ca, hea⟩ := iha
      obtain ⟨hb', cb, heb⟩ := ihb
      refine ⟨Subgroup.mul_mem _ ha' hb', ca + cb, ?_⟩
      rw [theta_mul (X := X) j hj a b ha' hb', hea, heb, two_smul, two_smul, two_smul]
      abel
  | inv a ha iha =>
      obtain ⟨ha', c, he⟩ := iha
      refine ⟨Subgroup.inv_mem _ ha', -c, ?_⟩
      rw [theta_inv (X := X) j hj a ha', he, two_smul, two_smul]
      abel

/-! ## The mod-`2` Magnus component on `γ_j` -/

noncomputable def ebl_Tmap (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ↥(barLie (Fin n × G) j) :=
  ⟨redZ (Fin n × G) (theta (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2),
    Work.SSGRoute.redZ_lieSpan_mem_barLie (X := Fin n × G) (by
      rw [← nestedSpan_eq_lieSpan]
      exact theta_mem (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2)⟩

theorem ebl_Tmap_apply (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ((ebl_Tmap (G := G) (n := n) j hj g : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G))
      = redZ (Fin n × G)
          (theta (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2) := rfl

theorem ebl_Tmap_mul (j : ℕ) (hj : 1 ≤ j)
    (a b : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ((ebl_Tmap (G := G) (n := n) j hj (a * b) : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G))
      = ((ebl_Tmap (G := G) (n := n) j hj a : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G))
        + ((ebl_Tmap (G := G) (n := n) j hj b : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G)) := by
  rw [ebl_Tmap_apply, ebl_Tmap_apply, ebl_Tmap_apply, ← map_add]
  congr 1
  exact theta_mul (Fin n × G) j hj (a : _) (b : _) a.2 b.2

theorem ebl_Tmap_one (j : ℕ) (hj : 1 ≤ j) :
    ((ebl_Tmap (G := G) (n := n) j hj 1 : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G)) = 0 := by
  have hcoe : ((1 : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries
        (j - 1))) : Work.Shrinking.freeOperatorGroup G n) = 1 :=
    map_one ((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries
      (j - 1)).subtype
  rw [ebl_Tmap_apply, theta_congr (X := Fin n × G) j hj hcoe
    (Subgroup.one_mem _) (Subgroup.one_mem _)]
  rw [theta_one (Fin n × G) j hj, map_zero]

theorem ebl_Tmap_inv (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ((ebl_Tmap (G := G) (n := n) j hj g⁻¹ : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G))
      = - ((ebl_Tmap (G := G) (n := n) j hj g : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G)) := by
  have h := ebl_Tmap_mul (G := G) (n := n) j hj g g⁻¹
  rw [mul_inv_cancel] at h
  rw [ebl_Tmap_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem ebl_Tmap_eq_zero_iff (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_Tmap (G := G) (n := n) j hj g = 0 ↔
      (g : Work.Shrinking.freeOperatorGroup G n) ∈
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1) ⊓
          Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
  constructor
  · intro hz
    have hred : redZ (Fin n × G)
        (theta (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2) = 0 := by
      have hc := congrArg (fun x : ↥(barLie (Fin n × G) j) => (x : WordBar (Fin n × G))) hz
      rwa [ebl_Tmap_apply] at hc
    obtain ⟨c, hc⟩ := (ebl_redZ_eq_zero_iff (Fin n × G) _).mp hred
    have hcw : c ∈ wordSpan (X := Fin n × G) j := by
      rw [mem_wordSpan_iff]
      intro w hw
      by_contra hne
      have hth : theta (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2
          ∈ wordSpan (X := Fin n × G) j :=
        theta_mem_wordSpan (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2
      have hcoeff := (mem_wordSpan_iff j _).mp hth w hw
      have hcoeff2 : MonoidAlgebra.coeff (theta (Fin n × G) j hj
            (g : Work.Shrinking.freeOperatorGroup G n) g.2) w = 2 * MonoidAlgebra.coeff c w := by
        rw [hc, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
      rw [hcoeff2] at hcoeff
      exact (mul_ne_zero (by norm_num) hne) hcoeff
    obtain ⟨instLO, -⟩ := exists_wellFoundedLT (Fin n × G)
    letI := instLO
    have hcfil : c ∈ fil (Fin n × G) j := mem_fil_of_mem_wordSpan hcw
    have haeq : magLT (Fin n × G) j (g : Work.Shrinking.freeOperatorGroup G n)
        = (2 : ℤ) • (Ideal.Quotient.mk (fil (Fin n × G) (j + 1)) c) := by
      rw [← theta_mk (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2, hc,
        map_zsmul]
    have hmem2 : Ideal.Quotient.mk (fil (Fin n × G) (j + 1)) c
        ∈ filq (Fin n × G) (j + 1) j := Ideal.mem_map_of_mem _ hcfil
    obtain ⟨w, hw, hwe⟩ := Work.SSGRoute.Up.purity_aux (X := Fin n × G) j hj 2 (by norm_num)
      g.2 hmem2 haeq
    have hwtheta : theta (Fin n × G) j hj w hw = c := by
      have key : (Ideal.Quotient.mk (fil (Fin n × G) (j + 1))) (theta (Fin n × G) j hj w hw)
          = (Ideal.Quotient.mk (fil (Fin n × G) (j + 1))) c :=
        (theta_mk (Fin n × G) j hj w hw).trans hwe
      have h1 : theta (Fin n × G) j hj w hw - c ∈ fil (Fin n × G) (j + 1) := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, key, sub_self]
      have h2 : theta (Fin n × G) j hj w hw - c ∈ wordSpan (X := Fin n × G) j :=
        Submodule.sub_mem _ (theta_mem_wordSpan (Fin n × G) j hj w hw) hcw
      exact sub_eq_zero.mp (Work.SSGRoute.UpCore.eq_zero_of_mem_wordSpan_of_mem_fil h2 h1)
    have hg2 : theta (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2
        = theta (Fin n × G) j hj (w ^ 2) (Subgroup.pow_mem _ hw 2) := by
      rw [theta_congr (X := Fin n × G) j hj (pow_two w) (Subgroup.pow_mem _ hw 2)
        (Subgroup.mul_mem _ hw hw)]
      rw [hc, ← hwtheta, two_smul]
      exact (theta_mul (X := Fin n × G) j hj w w hw hw).symm
    have hmemj : (g : Work.Shrinking.freeOperatorGroup G n) * (w ^ 2)⁻¹
        ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries j := by
      refine (theta_zero_iff (Fin n × G) j hj ((g : Work.Shrinking.freeOperatorGroup G n) * (w ^ 2)⁻¹)
        (Subgroup.mul_mem _ g.2 (Subgroup.inv_mem _ (Subgroup.pow_mem _ hw 2)))).mp ?_
      rw [theta_mul (X := Fin n × G) j hj _ _ g.2 (Subgroup.inv_mem _ (Subgroup.pow_mem _ hw 2)),
        theta_inv (X := Fin n × G) j hj (w ^ 2) (Subgroup.pow_mem _ hw 2), hg2]
      abel
    refine ⟨g.2, ?_⟩
    have hge : (g : Work.Shrinking.freeOperatorGroup G n)
        = ((g : Work.Shrinking.freeOperatorGroup G n) * (w ^ 2)⁻¹) * (w ^ 2) := by group
    rw [hge]
    exact Subgroup.mul_mem _
      (Work.ProP.lowerCentralSeries_le_pCentralSeries 2
        (Work.Shrinking.freeOperatorGroup G n) j hmemj)
      (Work.SSGRoute.prop5.pow_mem_pSeries 2 j 1 hj w hw)
  · intro hm
    obtain ⟨hg, hp⟩ := Subgroup.mem_inf.mp hm
    have h1 : (g : Work.Shrinking.freeOperatorGroup G n) ∈ Work.Shrinking.powSubgroup 2
        ((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1)) ⊔
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries j := by
      rw [← pSeries_inter_lcs_general (X := Fin n × G) j hj]
      exact ⟨hg, hp⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp h1
    obtain ⟨ha', ca, hea⟩ := ebl_exists_two_smul_theta_of_mem_powSubgroup (X := Fin n × G) j hj a ha
    have hb' : b ∈ (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries
        (j - 1) :=
      Subgroup.lowerCentralSeries_antitone _ (show j - 1 ≤ j by omega) hb
    have hb0 : theta (Fin n × G) j hj b hb' = 0 :=
      (theta_zero_iff (Fin n × G) j hj b hb').mpr hb
    refine Subtype.ext ?_
    rw [ebl_Tmap_apply]
    have hsplit : theta (Fin n × G) j hj (g : Work.Shrinking.freeOperatorGroup G n) g.2
        = theta (Fin n × G) j hj a ha' := by
      rw [theta_congr (X := Fin n × G) j hj (hab.symm) g.2 (Subgroup.mul_mem _ ha' hb')]
      rw [theta_mul (X := Fin n × G) j hj a b ha' hb', hea, hb0, add_zero]
    rw [hsplit, hea, map_zsmul]
    rw [← Int.cast_smul_eq_zsmul (ZMod 2) (2 : ℤ) (redZ (Fin n × G) ca)]
    rw [show (((2 : ℤ) : ZMod 2)) = 0 from by decide, zero_smul]
    rfl

theorem ebl_Tmap_surj (j : ℕ) (hj : 1 ≤ j) (v : ↥(barLie (Fin n × G) j)) :
    ∃ g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1)),
      ebl_Tmap (G := G) (n := n) j hj g = v := by
  obtain ⟨a, ha, haeq⟩ := ebl_exists_of_mem_barLie (Fin n × G) j v.2
  have ha' : a ∈ nestedSpan (X := Fin n × G) j := by rwa [← nestedSpan_eq_lieSpan] at ha
  obtain ⟨g, hg, hge⟩ := theta_surj (Fin n × G) j hj ha'
  refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
  rw [ebl_Tmap_apply, hge, haeq]

theorem ebl_Tmap_natural (δ : G) (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ((ebl_Tmap (G := G) (n := n) j hj (ebl_PhiG (basisPerm G n δ) j g)
        : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G))
      = wordBarσ (Fin n × G) (basisPerm G n δ)
          (ebl_Tmap (G := G) (n := n) j hj g : WordBar (Fin n × G)) := by
  rw [ebl_Tmap_apply, ebl_Tmap_apply]
  rw [theta_congr (X := Fin n × G) j hj
    (ebl_PhiG_apply (basisPerm G n δ) j g)
    (ebl_PhiG (basisPerm G n δ) j g).2
    (freeGroupCongr_mem (Fin n × G) (basisPerm G n δ) j g.2)]
  rw [theta_natural (Fin n × G) (basisPerm G n δ) j hj
    (g : Work.Shrinking.freeOperatorGroup G n) g.2]
  exact redZ_freeAssocMap (Fin n × G) (basisPerm G n δ) _


/-! ## Packaging into monoid homomorphisms -/

/-- `ebl_Tmap` packaged as a monoid homomorphism, with target `Multiplicative ↥(barLie X j)`. -/
noncomputable def ebl_TmapHom (j : ℕ) (hj : 1 ≤ j) :
    ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1)) →*
      Multiplicative ↥(barLie (Fin n × G) j) where
  toFun g := Multiplicative.ofAdd (ebl_Tmap (G := G) (n := n) j hj g)
  map_one' := Subtype.ext (ebl_Tmap_one (G := G) (n := n) j hj)
  map_mul' a b := Subtype.ext (ebl_Tmap_mul (G := G) (n := n) j hj a b)

/-- `ebl_phiGamma` packaged as a monoid homomorphism. -/
noncomputable def ebl_phiGammaHom (j : ℕ) :
    ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1)) →*
      ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker) where
  toFun g := ebl_phiGamma (G := G) (n := n) j g
  map_one' := ebl_phiGamma_one (G := G) (n := n) j
  map_mul' a b := ebl_phiGamma_mul (G := G) (n := n) j a b

@[simp] theorem ebl_TmapHom_apply (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_TmapHom (G := G) (n := n) j hj g
      = Multiplicative.ofAdd (ebl_Tmap (G := G) (n := n) j hj g) := rfl

@[simp] theorem ebl_phiGammaHom_apply (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_phiGammaHom (G := G) (n := n) j g = ebl_phiGamma (G := G) (n := n) j g := rfl

theorem ebl_phiGammaHom_surj (j : ℕ) (hj : 1 ≤ j) :
    Function.Surjective (ebl_phiGammaHom (G := G) (n := n) j) :=
  ebl_phiGamma_surj (G := G) (n := n) j hj

theorem ebl_TmapHom_surj (j : ℕ) (hj : 1 ≤ j) :
    Function.Surjective (ebl_TmapHom (G := G) (n := n) j hj) := by
  intro v
  obtain ⟨g, hg⟩ := ebl_Tmap_surj (G := G) (n := n) j hj (Multiplicative.toAdd v)
  refine ⟨g, ?_⟩
  show Multiplicative.ofAdd (ebl_Tmap (G := G) (n := n) j hj g) = v
  rw [hg]
  rfl

/-- The kernel of `ebl_phiGammaHom` is the `j + 1`-st term of the `2`-central series. -/
theorem ebl_phiGammaHom_eq_one_iff (j : ℕ)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_phiGammaHom (G := G) (n := n) j g = 1 ↔
      (g : Work.Shrinking.freeOperatorGroup G n) ∈
        Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j := by
  constructor
  · intro h
    have h2 : ((ebl_phiGamma (G := G) (n := n) j g
          : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker))
        : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = 1 := by
      rw [← ebl_phiGammaHom_apply, h]
      rfl
    rw [ebl_phiGamma_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, ebl_flowTerm_tauSucc_self] at h2
    exact h2
  · intro h
    apply Subtype.ext
    show ((ebl_phiGamma (G := G) (n := n) j g
        : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker))
      : flowQuotient 2 G n (tauSucc j j).1 (tauSucc j j).2) = 1
    rw [ebl_phiGamma_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, ebl_flowTerm_tauSucc_self]
    exact h

/-- Elements of `γ_j` with the same class in `E(j,j)` have the same `ebl_Tmap`. -/
theorem ebl_TmapHom_eq_of_phiGammaHom_eq (j : ℕ) (hj : 1 ≤ j)
    {x y : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))}
    (h : ebl_phiGammaHom (G := G) (n := n) j x = ebl_phiGammaHom (G := G) (n := n) j y) :
    ebl_TmapHom (G := G) (n := n) j hj x = ebl_TmapHom (G := G) (n := n) j hj y := by
  have h1 : ebl_phiGammaHom (G := G) (n := n) j (x⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, h]
    exact inv_mul_cancel (ebl_phiGammaHom (G := G) (n := n) j y)
  have hmem : ((x⁻¹ * y : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries
      (j - 1))) : Work.Shrinking.freeOperatorGroup G n) ∈
      Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) j :=
    (ebl_phiGammaHom_eq_one_iff (G := G) (n := n) j (x⁻¹ * y)).mp h1
  have hz : ebl_Tmap (G := G) (n := n) j hj (x⁻¹ * y) = 0 :=
    (ebl_Tmap_eq_zero_iff (G := G) (n := n) j hj (x⁻¹ * y)).mpr ⟨(x⁻¹ * y).2, hmem⟩
  have hz' : ebl_TmapHom (G := G) (n := n) j hj (x⁻¹ * y) = 1 := by
    rw [ebl_TmapHom_apply, hz]
    rfl
  rw [map_mul, map_inv] at hz'
  exact inv_mul_eq_one.mp hz'

/-- The descended set-theoretic map `E(j,j) → Multiplicative ↥(barLie X j)`. -/
noncomputable def ebl_isoFun (j : ℕ) (hj : 1 ≤ j) :
    ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker) → Multiplicative ↥(barLie (Fin n × G) j) :=
  fun k => ebl_TmapHom (G := G) (n := n) j hj
    (Classical.choose (ebl_phiGammaHom_surj (G := G) (n := n) j hj k))

theorem ebl_isoFun_phiGamma (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_isoFun (G := G) (n := n) j hj (ebl_phiGamma (G := G) (n := n) j g)
      = ebl_TmapHom (G := G) (n := n) j hj g :=
  ebl_TmapHom_eq_of_phiGammaHom_eq (G := G) (n := n) j hj
    (Classical.choose_spec
      (ebl_phiGammaHom_surj (G := G) (n := n) j hj (ebl_phiGamma (G := G) (n := n) j g)))

theorem ebl_isoFun_phiGammaHom (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_isoFun (G := G) (n := n) j hj (ebl_phiGammaHom (G := G) (n := n) j g)
      = ebl_TmapHom (G := G) (n := n) j hj g :=
  ebl_isoFun_phiGamma (G := G) (n := n) j hj g

theorem ebl_isoFun_one (j : ℕ) (hj : 1 ≤ j) :
    ebl_isoFun (G := G) (n := n) j hj 1 = 1 := by
  rw [← map_one (ebl_phiGammaHom (G := G) (n := n) j)]
  exact (ebl_isoFun_phiGammaHom (G := G) (n := n) j hj 1).trans (map_one _)

theorem ebl_isoFun_mul (j : ℕ) (hj : 1 ≤ j)
    (k₁ k₂ : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker)) :
    ebl_isoFun (G := G) (n := n) j hj (k₁ * k₂)
      = ebl_isoFun (G := G) (n := n) j hj k₁ * ebl_isoFun (G := G) (n := n) j hj k₂ := by
  obtain ⟨x₁, hx₁⟩ := ebl_phiGammaHom_surj (G := G) (n := n) j hj k₁
  obtain ⟨x₂, hx₂⟩ := ebl_phiGammaHom_surj (G := G) (n := n) j hj k₂
  have h12 : ebl_phiGammaHom (G := G) (n := n) j (x₁ * x₂) = k₁ * k₂ := by
    rw [map_mul, hx₁, hx₂]
  calc ebl_isoFun (G := G) (n := n) j hj (k₁ * k₂)
      = ebl_isoFun (G := G) (n := n) j hj
          (ebl_phiGammaHom (G := G) (n := n) j (x₁ * x₂)) := by rw [h12]
    _ = ebl_TmapHom (G := G) (n := n) j hj (x₁ * x₂) :=
        ebl_isoFun_phiGammaHom (G := G) (n := n) j hj (x₁ * x₂)
    _ = ebl_TmapHom (G := G) (n := n) j hj x₁ * ebl_TmapHom (G := G) (n := n) j hj x₂ :=
        map_mul _ _ _
    _ = ebl_isoFun (G := G) (n := n) j hj k₁ * ebl_isoFun (G := G) (n := n) j hj k₂ := by
        rw [← ebl_isoFun_phiGammaHom (G := G) (n := n) j hj x₁, hx₁,
          ← ebl_isoFun_phiGammaHom (G := G) (n := n) j hj x₂, hx₂]

theorem ebl_isoFun_injective (j : ℕ) (hj : 1 ≤ j) :
    Function.Injective (ebl_isoFun (G := G) (n := n) j hj) := by
  intro k₁ k₂ h
  obtain ⟨x₁, hx₁⟩ := ebl_phiGammaHom_surj (G := G) (n := n) j hj k₁
  obtain ⟨x₂, hx₂⟩ := ebl_phiGammaHom_surj (G := G) (n := n) j hj k₂
  rw [← hx₁, ← hx₂]
  have hT : ebl_TmapHom (G := G) (n := n) j hj x₁ = ebl_TmapHom (G := G) (n := n) j hj x₂ := by
    rw [← ebl_isoFun_phiGammaHom (G := G) (n := n) j hj x₁,
      ← ebl_isoFun_phiGammaHom (G := G) (n := n) j hj x₂, hx₁, hx₂, h]
  have h1 : ebl_phiGammaHom (G := G) (n := n) j (x₁⁻¹ * x₂) = 1 := by
    refine (ebl_phiGammaHom_eq_one_iff (G := G) (n := n) j (x₁⁻¹ * x₂)).mpr ?_
    have hz : ebl_Tmap (G := G) (n := n) j hj (x₁⁻¹ * x₂) = 0 := by
      have hh : ebl_TmapHom (G := G) (n := n) j hj (x₁⁻¹ * x₂) = 1 := by
        rw [map_mul, map_inv, hT]
        exact inv_mul_cancel (ebl_TmapHom (G := G) (n := n) j hj x₂)
      rw [ebl_TmapHom_apply] at hh
      exact hh
    exact ((ebl_Tmap_eq_zero_iff (G := G) (n := n) j hj (x₁⁻¹ * x₂)).mp hz).2
  rw [map_mul, map_inv] at h1
  exact inv_mul_eq_one.mp h1

theorem ebl_isoFun_surjective (j : ℕ) (hj : 1 ≤ j) :
    Function.Surjective (ebl_isoFun (G := G) (n := n) j hj) := by
  intro v
  obtain ⟨g, hg⟩ := ebl_Tmap_surj (G := G) (n := n) j hj (Multiplicative.toAdd v)
  refine ⟨ebl_phiGammaHom (G := G) (n := n) j g, ?_⟩
  rw [ebl_isoFun_phiGammaHom]
  show Multiplicative.ofAdd (ebl_Tmap (G := G) (n := n) j hj g) = v
  rw [hg]
  rfl

/-- **The transport `E(j,j) ≃* Multiplicative ↥(barLie X j)`.** -/
noncomputable def ebl_iso (j : ℕ) (hj : 1 ≤ j) :
    ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker) ≃*
      Multiplicative ↥(barLie (Fin n × G) j) where
  toFun := ebl_isoFun (G := G) (n := n) j hj
  invFun := fun v => Classical.choose (ebl_isoFun_surjective (G := G) (n := n) j hj v)
  left_inv := fun k => ebl_isoFun_injective (G := G) (n := n) j hj
    (Classical.choose_spec
      (ebl_isoFun_surjective (G := G) (n := n) j hj (ebl_isoFun (G := G) (n := n) j hj k)))
  right_inv := fun v => Classical.choose_spec (ebl_isoFun_surjective (G := G) (n := n) j hj v)
  map_mul' := ebl_isoFun_mul (G := G) (n := n) j hj

theorem ebl_iso_apply_phiGamma (j : ℕ) (hj : 1 ≤ j)
    (g : ↥((⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries (j - 1))) :
    ebl_iso (G := G) (n := n) j hj (ebl_phiGamma (G := G) (n := n) j g)
      = ebl_TmapHom (G := G) (n := n) j hj g :=
  ebl_isoFun_phiGamma (G := G) (n := n) j hj g

/-- `flowKerSmul` is the `PhiK`-action. -/
theorem ebl_flowKerSmul_eq_PhiK (j : ℕ) (δ : G)
    (k : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker)) :
    Work.SSGRoute.flowKerSmul G n j δ k = ebl_PhiK (G := G) (n := n) δ j k := rfl

/-- **Equivariance of the transport under the `δ`-action.** -/
theorem ebl_iso_flowKerSmul (j : ℕ) (hj : 1 ≤ j) (δ : G)
    (c : ↥((Work.SSGRoute.flowQuotSucc 2 G n j j).ker)) :
    ((Multiplicative.toAdd (ebl_iso (G := G) (n := n) j hj
        (Work.SSGRoute.flowKerSmul G n j δ c)) : ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G))
      = wordBarσ (Fin n × G) (basisPerm G n δ)
          ((Multiplicative.toAdd (ebl_iso (G := G) (n := n) j hj c) :
            ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G)) := by
  obtain ⟨g, hg⟩ := ebl_phiGamma_surj (G := G) (n := n) j hj c
  rw [← hg]
  have hsm : Work.SSGRoute.flowKerSmul G n j δ (ebl_phiGamma (G := G) (n := n) j g)
      = ebl_phiGamma (G := G) (n := n) j (ebl_PhiG (basisPerm G n δ) j g) := by
    rw [ebl_flowKerSmul_eq_PhiK, ebl_PhiK_phiGamma]
  rw [hsm]
  simp only [ebl_iso_apply_phiGamma]
  show ((ebl_Tmap (G := G) (n := n) j hj (ebl_PhiG (basisPerm G n δ) j g) :
      ↥(barLie (Fin n × G) j)) : WordBar (Fin n × G))
      = wordBarσ (Fin n × G) (basisPerm G n δ)
          (ebl_Tmap (G := G) (n := n) j hj g : WordBar (Fin n × G))
  exact ebl_Tmap_natural (G := G) (n := n) δ j hj g

end Work.SSGRoute.diagOdd
