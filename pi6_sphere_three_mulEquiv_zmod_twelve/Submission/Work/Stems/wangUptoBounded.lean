import Mathlib
import Submission.Work.Stems.Collar.WangPowFormula
import Submission.Work.Stems.wangOddStepSphere
import Submission.Work.Stems.wangOddStep
import Submission.Work.StemsB.WangE4Rat
import Submission.Work.Stems.wangAllAux
import Submission.Work.Stems.wangSphereUpto

/-!
# The Wang odd step over the sphere, with **both** fibre hypotheses bounded

*(Area STEMS.)*  `Work.Stems.wangUptoBounded` is the form of the all-degrees Wang odd step that a
**range model** of `K(ℤ,b)` can supply: the fibre `ΩX` is only known up to its own top `T`, so both
the vanishing `hfib` and the generator statement `hgen` are restricted to degrees `≤ T` (compare
`Work.Stems.wangSphereUpto`, whose `hgen` is unrestricted and therefore unusable for range models).
The proof is the proof of `Work.Stems.isZero_ratCoh_sphereFibration_all` with the two auxiliary
lemmas `wangTheta_canon_injective`/`wangTheta_canon_surjective` of `Work.Stems.wangAllAux` capped.

**The only mathematical content beyond `wangAllAux`** is that every instance of `hgen` consulted by
the argument lives at degree `≤ t ≤ T`: the argument uses `hgen` at the indices `(b-1)K` with
`(b-1)K = t` (injectivity branch) and `(b-1)K = t - b`, `(b-1)(K+1) = t - 1` (surjectivity branch).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology
open scoped Simplicial

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Stems

noncomputable section

section Pow

variable {E : Type} [TopologicalSpace E]
variable (b : ℕ) (hb : 2 ≤ b) (p : C(E, Work.StemsB.SphModel b))
variable (d_G : ↥(Work.StemsB.sphLoopBig b))
variable (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
variable (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
variable (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty}))

theorem wangTheta_canon_injectiveB (hbodd : Odd b) (hpc : PathConnectedSpace (↥(p ⁻¹' {OnePoint.infty}))) (hlow : Work.StemsB.Rat.wangThetaLow b hb E p d_G hT_G hT_O x ≠ 0)
    (hpow : Work.Stems.Collar.WangPowFormula)
    (T : ℕ) (hgen : ∀ k : ℕ, 1 ≤ k → (b - 1) * k ≤ T → Nonempty
      (Work.Cohomology.singularCohomology ℚ ((b - 1) * k)
        (Work.StemsB.wangCohFsp b p) ≅ ModuleCat.of ℚ ℚ)) (k : ℕ)
    (hk : (b - 1) * (k + 2) ≤ T) :
    Function.Injective (Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)) := by
  obtain ⟨_, hθ⟩ := pow_and_theta b hb p d_G hT_G hT_O x hbodd hpc hlow hpow k
  have hP' : Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1) ≠ 0 :=
    fun h0 => hθ (by rw [h0, transT_zero (Y := ↥(p ⁻¹' {OnePoint.infty})), map_zero])
  have hPg : Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty}) (powArg b k hb)
      (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1)) ≠ 0 :=
    fun h0 => hP' (transT_injective (Y := ↥(p ⁻¹' {OnePoint.infty})) (powArg b k hb)
      (by rw [h0, transT_zero (Y := ↥(p ⁻¹' {OnePoint.infty}))]))
  obtain ⟨e⟩ := hgen (k + 2) (by omega) hk
  have hsrc : (b - 1) * (k + 2) = ((b - 1) * (k + 2) - b) + b := powArg b k hb
  have key : ∀ u : Work.Thom.Coh ℚ (((b - 1) * (k + 2) - b) + b) (↥(p ⁻¹' {OnePoint.infty})),
      (Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)) u = 0 → u = 0 := by
    intro u hu
    obtain ⟨a, ha⟩ := eq_smul_of_iso_rat ((transIso (↥(p ⁻¹' {OnePoint.infty})) hsrc).symm ≪≫ e)
      (g := Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty}) (powArg b k hb)
        (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1))) hPg u
    have h0 : a • ((Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)) (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty}) (powArg b k hb) (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1)))) = 0 := by
      rw [← map_smul, ← ha, hu]
    have haz : a = 0 := (smul_eq_zero.mp h0).resolve_right hθ
    rw [ha, haz, zero_smul]
  intro z w hzw
  have hsub : z - w = 0 := key (z - w) (by rw [map_sub, hzw, sub_self])
  exact sub_eq_zero.mp hsub

/-- **The canonical transgression `θ_{(b-1)(k+2)-b}` is surjective** (a non-zero map between
one-dimensional `ℚ`-vector spaces). -/
theorem wangTheta_canon_surjectiveB (hbodd : Odd b) (hpc : PathConnectedSpace (↥(p ⁻¹' {OnePoint.infty}))) (hlow : Work.StemsB.Rat.wangThetaLow b hb E p d_G hT_G hT_O x ≠ 0)
    (hpow : Work.Stems.Collar.WangPowFormula)
    (T : ℕ) (hgen : ∀ k : ℕ, 1 ≤ k → (b - 1) * k ≤ T → Nonempty
      (Work.Cohomology.singularCohomology ℚ ((b - 1) * k)
        (Work.StemsB.wangCohFsp b p) ≅ ModuleCat.of ℚ ℚ)) (k : ℕ)
    (hk : (b - 1) * (k + 1) ≤ T) :
    Function.Surjective (Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)) := by
  obtain ⟨_, hθ⟩ := pow_and_theta b hb p d_G hT_G hT_O x hbodd hpc hlow hpow k
  obtain ⟨e⟩ := hgen (k + 1) (by omega) hk
  have htgt : ((b - 1) * (k + 2) - b) + 1 = (b - 1) * (k + 1) := powRes b k hb
  have hne : ((transIso (↥(p ⁻¹' {OnePoint.infty})) htgt) ≪≫ e).hom
      ((Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)) (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty}) (powArg b k hb) (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1)))) ≠ 0 :=
    fun h => hθ (Work.StemsB.iso_hom_injective_R ℚ ((transIso (↥(p ⁻¹' {OnePoint.infty})) htgt) ≪≫ e)
      (by rw [h, map_zero]))
  intro u
  refine ⟨(((transIso (↥(p ⁻¹' {OnePoint.infty})) htgt) ≪≫ e).hom u /
      ((transIso (↥(p ⁻¹' {OnePoint.infty})) htgt) ≪≫ e).hom
        ((Work.StemsB.Rat.wangTheta b hb p d_G hT_G hT_O ((b - 1) * (k + 2) - b)) (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty}) (powArg b k hb) (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1))))) •
      (Work.StemsB.Rat.transT ↥(p ⁻¹' {OnePoint.infty}) (powArg b k hb) (Work.Stems.Collar.wangPow b hb E p d_G hT_G hT_O x (k + 1))), ?_⟩
  apply Work.StemsB.iso_hom_injective_R ℚ ((transIso (↥(p ⁻¹' {OnePoint.infty})) htgt) ≪≫ e)
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ _ hne
end Pow

theorem wangUptoBounded (b : ℕ) (hb : 2 ≤ b) (hbodd : Odd b)
    (E : Type) [TopologicalSpace E] (p : C(E, Work.StemsB.SphModel b))
    (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G)
    (x : Work.Thom.Coh ℚ (b - 1) ↥(p ⁻¹' {OnePoint.infty}))
    (hpc : PathConnectedSpace ↥(p ⁻¹' {OnePoint.infty}))
    (hpow : Work.Stems.Collar.WangPowFormula)
    (hlow : Work.StemsB.Rat.wangThetaLow b hb E p d_G hT_G hT_O x ≠ 0)
    (T : ℕ)
    (hfib : ∀ t : ℕ, 0 < t → t ≤ T → (∀ k : ℕ, t ≠ (b - 1) * k) →
      Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p)))
    (hgen : ∀ k : ℕ, 1 ≤ k → (b - 1) * k ≤ T → Nonempty
      (Work.Cohomology.singularCohomology ℚ ((b - 1) * k) (Work.StemsB.wangCohFsp b p) ≅
        ModuleCat.of ℚ ℚ)) :
    ∀ t : ℕ, b + 1 ≤ t → t ≤ T →
      Subsingleton ↥(Work.Cohomology.singularCohomology ℚ t (TopCat.of E)) := by
  intro t ht htT
  have keyT : (t - b - 1) + b + 1 = t := by omega
  rw [← keyT]
  refine isZero_wangTotal_of_zeroMaps (TopCat.of E) (Work.StemsB.Rat.wangA b p)
    (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
    (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) (t - b - 1) ?hβ ?hα
  · by_cases hsrc : Subsingleton
        ↥(Work.Cohomology.singularCohomology ℚ (t - b) (Work.StemsB.wangCohFsp b p))
    · intro c
      haveI : Subsingleton
          ↥(Work.Cohomology.singularCohomology ℚ ((t - b - 1) + 1) (Work.StemsB.wangCohFsp b p)) := by
        rw [show (t - b - 1) + 1 = t - b from by omega]
        exact hsrc
      rw [Subsingleton.elim c 0]
      exact map_zero _
    · obtain ⟨K, hK⟩ : ∃ K, t - b = (b - 1) * K := by
        by_contra h
        push_neg at h
        exact hsrc (hfib (t - b) (by omega) (by omega) h)
      have hK1 : 1 ≤ K := by
        by_contra h
        have h0 : K = 0 := by omega
        rw [h0, Nat.mul_zero] at hK
        omega
      have hidx : t - b - 1 = (b - 1) * ((K - 1) + 2) - b := by
        have h1 : (K - 1) + 2 = K + 1 := by omega
        rw [h1, Nat.mul_succ, ← hK]
        omega
      intro c
      have hsurj := thetaR_surjective_of_index b hb p d_G hT_G hT_O hidx
        (wangTheta_canon_surjectiveB b hb p d_G hT_G hT_O x hbodd hpc hlow hpow T hgen (K - 1)
          (by rw [show (K - 1) + 1 = K from by omega, ← hK]; exact le_trans (Nat.sub_le _ _) htT))
      obtain ⟨v, hv⟩ := hsurj c
      have hEx := Work.StemsB.wangCohShiftExact₃R ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
        (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) (t - b - 1)
      exact (hEx c).mpr ⟨v, hv⟩
  · intro y
    by_cases htgt : Subsingleton
        ↥(Work.Cohomology.singularCohomology ℚ t (Work.StemsB.wangCohFsp b p))
    · haveI : Subsingleton
          ↥(Work.Cohomology.singularCohomology ℚ ((t - b - 1) + b + 1)
            (Work.StemsB.wangCohFsp b p)) := by
        rw [show (t - b - 1) + b + 1 = t from by omega]
        exact htgt
      exact Subsingleton.elim _ _
    · obtain ⟨K, hK⟩ : ∃ K, t = (b - 1) * K := by
        by_contra h
        push_neg at h
        exact htgt (hfib t (by omega) (by omega) h)
      have hK2 : 2 ≤ K := by
        by_contra h
        have h1 : K ≤ 1 := by omega
        interval_cases K
        · rw [Nat.mul_zero] at hK
          omega
        · rw [Nat.mul_one] at hK
          omega
      have hidxθ : (t - b - 1) + 1 = (b - 1) * ((K - 2) + 2) - b := by
        have h1 : (K - 2) + 2 = K := by omega
        rw [h1, ← hK]
        omega
      have hθinj : Function.Injective
          (⇑(Work.StemsB.wangCohShiftθR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) ((t - b - 1) + 1))) :=
        thetaR_injective_of_index b hb p d_G hT_G hT_O hidxθ
          (wangTheta_canon_injectiveB b hb p d_G hT_G hT_O x hbodd hpc hlow hpow T hgen (K - 2)
          (by rw [show (K - 2) + 2 = K from by omega, ← hK]; exact htT))
      have hα1 : ∀ z : ↥(Work.Cohomology.singularCohomology ℚ (((t - b - 1) + 1) + b)
            (TopCat.of E)),
          ((Work.StemsB.wangCohShiftαR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (((t - b - 1) + 1) + b))).hom z = 0 := by
        intro z
        have hEx := Work.StemsB.wangCohShiftExact₂R ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
          (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
          (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) ((t - b - 1) + 1)
        have hz : (⇑(Work.StemsB.wangCohShiftθR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (Work.StemsB.Rat.wangTauS b hb E p hT_O d_G hT_G) ((t - b - 1) + 1)))
            ((⇑(Work.StemsB.wangCohShiftαR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
              (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
              (((t - b - 1) + 1) + b))) z) = 0 :=
          (hEx ((⇑(Work.StemsB.wangCohShiftαR ℚ (TopCat.of E) (Work.StemsB.Rat.wangA b p)
            (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O)
            (((t - b - 1) + 1) + b))) z)).mpr ⟨z, rfl⟩
        exact hθinj (hz.trans (map_zero _).symm)
      have hidxα : (t - b - 1) + b + 1 = ((t - b - 1) + 1) + b := by omega
      have htr := wangCohShiftαR_transport (TopCat.of E) (Work.StemsB.Rat.wangA b p)
        (Work.StemsB.wangCohFsp b p) b (Work.StemsB.Rat.wangGammaExplicit b p hT_O) hidxα y
      have h2 := hα1 ((transIso (TopCat.of E) hidxα).hom y)
      rw [← htr] at h2
      exact Work.StemsB.iso_hom_injective_R ℚ (transIso (Work.StemsB.wangCohFsp b p) hidxα)
        (h2.trans (map_zero _).symm)

end

end Work.Stems
