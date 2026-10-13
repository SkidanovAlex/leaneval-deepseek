/-
  `Work.CoreStep.branchDomainPairDim`: the dimension identity `pPair n m - W.j = n + (m+1) - T.j`
  for a pair stratum of dimension at least `dim T`, and the covering hypothesis of
  `Work.WilE7.DimAPI.openMap_of_equalDim` (used by `Work.CoreStep.branchDomain_open`).
-/
import Mathlib
import Submission.Work.CoreStep.branchDomainPairFacts
import Submission.Work.WilE7.DimAPI.finrank_ker_fderiv_eqMap
import Submission.Work.WilE7.CoreStep.basePrLin_injective_on_ker_jac
import Submission.Work.WilE7.CoreStep.localGraph_on_branch

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
namespace Work.CoreStep

open Work.WilE7 Work.WilE7.CoreStep

/-- The tangent space of an absolute `Good` stratum at one of its points has dimension `N - S.j`. -/
theorem finrank_ker_jac_abs {N : ℕ} (S : Stratum 0 N) (hS : S.Good)
    {z : Fin (0 + N) → ℝ} (hz : z ∈ S.X.set) :
    Module.finrank ℝ (LinearMap.ker (MainDesign.jac S z)) = N - S.j := by
  have h := DimAPI.finrank_ker_fderiv_eqMap S hS hz
  have hker : LinearMap.ker (MainDesign.jac S z) =
      LinearMap.ker ((fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
        eaEval S.X.c (S.h a) w) z).toLinearMap) := by
    rw [DimAPI.jac_eq_fderiv S z]
  rw [hker, h]

/-- The half maps of a `Good` pair stratum are injective on its tangent space: this is the
hypothesis `hinj` of `openMap_of_equalDim` for the second-half projection. -/
theorem hinj_of_pair {n m : ℕ} (T : Stratum 0 (n + (m + 1))) (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, MainDesign.projRank T z = n + (m + 1) - T.j)
    (W : Stratum 0 (pPair n m)) (hW : W.Good) (hWsub : W.X.set ⊆ (absPairSet T).set) :
    ∀ z ∈ W.X.set, ∀ v ∈ LinearMap.ker (MainDesign.jac W z),
      linProjSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v) = 0 → v = 0 := by
  intro z hz v hv hv₂
  set v₁ : Fin (n + (m + 1)) → ℝ := projFirst (n + (m + 1)) (n + (m + 1))
    (MainDesign.absPt v) with hv₁
  set v₂ : Fin (n + (m + 1)) → ℝ := projSnd (n + (m + 1)) (n + (m + 1))
    (MainDesign.absPt v) with hv₂def
  obtain ⟨hf1, -, hf3⟩ := jac_pair_facts T hT W hW hWsub hz v hv
  -- the first half of the base point
  set u₁ : Fin (pDim n m) → ℝ :=
    absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt z)) with hu₁
  have hu₁T : u₁ ∈ T.X.set := ((absPairSet_mem_iff T z).mp (hWsub hz)).1
  -- `absPtUp v₁` lies in the tangent space of `T` at `u₁`
  have hkerT : absPtUp (n := n) (m := m) v₁ ∈ LinearMap.ker (MainDesign.jac T u₁) := by
    rw [LinearMap.mem_ker, hv₁]
    exact hf3
  -- and its base projection vanishes, since the base projections of the halves agree
  have hbase : MainDesign.basePrLin n (m + 1) (absPtUp (n := n) (m := m) v₁) = 0 := by
    have hpf : MainDesign.basePrLin n (m + 1) (absPtUp (n := n) (m := m) v₁) =
        projFirst n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1))
          (MainDesign.absPt v)) := by
      rw [← projFirst_absPt_eq_basePrLin (n := n) (q := m + 1) (absPtUp (n := n) (m := m) v₁)]
      rw [absPtUp_eq_absPtInv, DimAPI.absPt_absPtInv, hv₁]
    have hv₂' : projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v) = 0 := by
      simpa [linProjSnd_apply] using hv₂
    rw [hpf, hf1, hv₂']
    exact (linProjFirst n (m + 1)).map_zero
  have hv₁0 : absPtUp (n := n) (m := m) v₁ = 0 := by
    have hinj := basePrLin_injective_on_ker_jac T hT u₁ hu₁T (hrank u₁ hu₁T)
    have h : (MainDesign.basePrLin n (m + 1) ∘ₗ (LinearMap.ker (MainDesign.jac T u₁)).subtype)
        ⟨absPtUp (n := n) (m := m) v₁, hkerT⟩
        = (MainDesign.basePrLin n (m + 1) ∘ₗ
            (LinearMap.ker (MainDesign.jac T u₁)).subtype) ⟨0, by simp⟩ := by
      show MainDesign.basePrLin n (m + 1) (absPtUp (n := n) (m := m) v₁) =
        MainDesign.basePrLin n (m + 1) 0
      rw [hbase, map_zero]
    exact congrArg Subtype.val (hinj h)
  -- hence `v = 0`
  have hv₁' : v₁ = 0 := by
    have h := congrArg (MainDesign.absPt (N := n + (m + 1))) hv₁0
    rw [absPtUp_eq_absPtInv, DimAPI.absPt_absPtInv, absPt_zero] at h
    exact h
  have hv₂' : v₂ = 0 := hv₂
  have hsum : Fin.append v₁ v₂ = MainDesign.absPt v := by
    rw [hv₁, hv₂def]
    exact append_projFirst_projSnd _
  have hzero : MainDesign.absPt v = 0 := by
    rw [← hsum, hv₁', hv₂']
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ j
    · exact Fin.append_right _ _ j
  exact DimAPI.absPt_injective (pPair n m) (a₁ := v) (a₂ := 0) (by rw [hzero, absPt_zero])

/-- The second-half projection maps `absSet W` into `absSet T`. -/
theorem hmap_of_pair {n m : ℕ} (T : Stratum 0 (n + (m + 1)))
    (W : Stratum 0 (pPair n m)) (hWsub : W.X.set ⊆ (absPairSet T).set) :
    linProjSnd (n + (m + 1)) (n + (m + 1)) '' (MainDesign.absSet W)
      ⊆ MainDesign.absSet T := by
  rintro y ⟨w, hw, rfl⟩
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  have hparts := (absPairSet_mem_iff T w₀).mp (hWsub hw₀)
  refine ⟨absPtUp (n := n) (m := m) (projSnd (n + (m + 1)) (n + (m + 1))
    (MainDesign.absPt w₀)), hparts.2.1, ?_⟩
  rw [absPtUp_eq_absPtInv]
  exact DimAPI.absPt_absPtInv (n + (m + 1)) _

/-- **The dimension identity**: a `Good` stratum of the same-base pair set that contains the pair
point of two points of `T.X.set` over `C` and whose dimension is at least `dim T` has dimension
exactly `dim T`. -/
theorem pair_dim_eq {n m : ℕ} (T : Stratum 0 (n + (m + 1))) (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, MainDesign.projRank T z = n + (m + 1) - T.j)
    (W : Stratum 0 (pPair n m)) (hW : W.Good) (hWsub : W.X.set ⊆ (absPairSet T).set)
    (u u' : Fin (pDim n m) → ℝ) (hu' : u' ∈ T.X.set)
    (hWmem : pairPtUp u u' ∈ W.X.set)
    (hle : n + (m + 1) - T.j ≤ pPair n m - W.j) :
    pPair n m - W.j = n + (m + 1) - T.j := by
  set z : Fin (0 + pPair n m) → ℝ := pairPtUp u u' with hz
  -- the second half map restricted to the tangent space of `W`
  set S : Submodule ℝ (Fin (0 + pPair n m) → ℝ) := LinearMap.ker (MainDesign.jac W z) with hS
  set ψ : ↥S →ₗ[ℝ] (Fin (0 + (n + (m + 1))) → ℝ) :=
    (pairSndLift (n := n) (m := m)).comp S.subtype with hψ
  have hψapply : ∀ a : ↥S, ψ a = absPtUp (projSnd (n + (m + 1)) (n + (m + 1))
      (MainDesign.absPt (a : Fin (0 + pPair n m) → ℝ))) := by
    intro a
    rw [hψ, LinearMap.comp_apply, pairSndLift_apply]
    rfl
  -- the dimension of the tangent space of `W`
  have hdimW : Module.finrank ℝ ↥S = pPair n m - W.j := by
    have h := finrank_ker_jac_abs W hW hWmem
    rw [hS]
    simpa [hz] using h
  -- `ψ` is injective
  have hψinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro a ha
    have ha0 : ψ a = 0 := ha
    have hav : MainDesign.jac W z (a : Fin (0 + pPair n m) → ℝ) = 0 := a.2
    set v₂ : Fin (n + (m + 1)) → ℝ := projSnd (n + (m + 1)) (n + (m + 1))
      (MainDesign.absPt (a : Fin (0 + pPair n m) → ℝ)) with hv₂
    have h₂ : absPtUp (n := n) (m := m) v₂ = 0 := by
      rw [hv₂, ← hψapply a, ha0]
    have hv₂0 : v₂ = 0 := by
      have h := congrArg (MainDesign.absPt (N := n + (m + 1))) h₂
      rw [absPtUp_eq_absPtInv, DimAPI.absPt_absPtInv, absPt_zero] at h
      exact h
    have hmain := hinj_of_pair T hT hrank W hW hWsub z hWmem (a : Fin (0 + pPair n m) → ℝ)
      hav (by simpa [linProjSnd_apply, ← hv₂] using hv₂0)
    exact Subtype.ext hmain
  -- the range of `ψ` lies in the tangent space of `T` at `u'`
  have hrange_sub : LinearMap.range ψ ≤ LinearMap.ker (MainDesign.jac T u') := by
    rintro y ⟨a, rfl⟩
    rw [LinearMap.mem_ker, hψapply a]
    have hf2 := (jac_pair_facts T hT W hW hWsub hWmem (a : Fin (0 + pPair n m) → ℝ) a.2).2.1
    have h₁ : absPtUp (n := n) (m := m) (projSnd (n + (m + 1)) (n + (m + 1))
        (MainDesign.absPt z)) = u' := by
      rw [hz, snd_half_pairPt, absPtUp_absPtInv]
    rw [← h₁]
    exact hf2
  -- rank–nullity for `ψ`
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  have hkerψ : Module.finrank ℝ (LinearMap.ker ψ) = 0 := by
    rw [Submodule.finrank_eq_zero]
    exact LinearMap.ker_eq_bot.mpr hψinj
  have hmono : Module.finrank ℝ (LinearMap.range ψ) ≤
      Module.finrank ℝ (LinearMap.ker (MainDesign.jac T u')) := Submodule.finrank_mono hrange_sub
  have hdimT : Module.finrank ℝ (LinearMap.ker (MainDesign.jac T u')) = n + (m + 1) - T.j :=
    finrank_ker_jac_abs T hT hu'
  omega

end Work.CoreStep
