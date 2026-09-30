import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMM2.finiteType
import Submission.Work.Pi6.EMM2.K2F9Kit
import Submission.Work.Pi6.EMM2.K4Kit
import Submission.Work.Pi6.EMM2.botEdgeInj
import Submission.Work.Pi6.EMM2.dimBounds
import Submission.Work.Pi6.EMM2.sqCore
import Submission.Work.Pi6.K2Z.transfer
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Cohomology.Pullback
import Submission.Work.EMFG.finiteAbelianModelFG
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMM2

noncomputable section

/-! ## Support: the `mpathOf` homotopy equivalence -/

/-! ## The `mpathOf` homotopy equivalence -/

/-- The section `mpathOf p` of the mapping path space is a homotopy equivalence. -/
noncomputable def homotopyEquiv_mpathOf {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : ContinuousMap.HomotopyEquiv E (Work.Serre.mpath p) where
  toFun := Work.Serre.mpathOf p
  invFun := Work.Serre.mpathFst p
  left_inv := by
    have h : (Work.Serre.mpathFst p).comp (Work.Serre.mpathOf p) = ContinuousMap.id E := by
      ext e; rfl
    rw [h]
  right_inv := Work.FGThm.mpathOf_comp_mpathFst_homotopic p

/-! ## The main assembly -/

set_option linter.unusedVariables false in
theorem k2forcing9
    : Work.Pi6.EMM2.K2Facts9Statement := by
  intro hM hKZ hFT hLD h2f h2c hmc hco X _instX x₀ N hN8 hX
  obtain ⟨KZ, tKZ, k₀, r, hrk, hKZmodel, hπ1, hH2surj, hFibre⟩ := hKZ x₀ N hN8 hX
  letI : TopologicalSpace KZ := tKZ
  let p : C(Work.Serre.mpath r, X) := Work.Serre.mpathQ r
  let e₀ : Work.Serre.mpath r := Work.Serre.mpathOf r k₀
  -- 1. the field facts about the K(Z,2) model
  obtain ⟨wKZ, hwKZ_ne, hwKZ_pow, hwKZ_fin, hwKZ_odd⟩ :=
    h2f hM (ZMod 2) k₀ (M := N) (by omega) hKZmodel
  -- 2. the field facts about the fibre (a K(Z,2) model through N - 1)
  obtain ⟨wF, hwF_ne, hwF_pow, hwF_fin, hwF_odd⟩ :=
    h2f hM (ZMod 2) (Work.StemsB.fibrePoint p e₀) (M := N - 1) (by omega) hFibre
  -- 3. the low-degree cohomology of the base
  obtain ⟨hBconn, hB0, hBodd⟩ :=
    hLD (ZMod 2) (by infer_instance) (by norm_num) (by omega) x₀ hX
  have hB1 : IsZero (Coh (ZMod 2) X 1) := hBodd 1 le_rfl (by norm_num)
  -- 4. the values for the fibre
  have hF0 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 0) = 1 := hwF_fin 0 (by norm_num)
  have hF1 : IsZero (Coh (ZMod 2) (Fib p e₀) 1) := by
    haveI : Subsingleton (Coh (ZMod 2) (Fib p e₀) 1) := hwF_odd 0 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hF2 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 2) = 1 := hwF_fin 1 (by norm_num)
  have hF3 : IsZero (Coh (ZMod 2) (Fib p e₀) 3) := by
    haveI : Subsingleton (Coh (ZMod 2) (Fib p e₀) 3) := hwF_odd 1 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  have hF4 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Fib p e₀) 4) = 1 := hwF_fin 2 (by norm_num)
  have hF5 : IsZero (Coh (ZMod 2) (Fib p e₀) 5) := by
    haveI : Subsingleton (Coh (ZMod 2) (Fib p e₀) 5) := hwF_odd 2 (by norm_num)
    exact ModuleCat.isZero_of_subsingleton _
  -- 5. finiteness
  have hFinB : ∀ s : ℕ, s ≤ 6 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) X s) := by
    intro s hs
    have hX7 : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) 7 X x₀ :=
      Work.EMFG.isEMSpaceUpTo_mono hX (by omega)
    exact Work.Pi6.EMM2.finiteType (ZMod 2) (by infer_instance : Module.Finite ℤ (ZMod 2))
      (m := 2) (N := 6) (by norm_num) x₀ hX7 s (by omega)
  have hFinF : ∀ q : ℕ, q ≤ 6 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) (Fib p e₀) q) := by
    intro q hq
    have hF7 : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 7 (Fib p e₀)
        (Work.StemsB.fibrePoint p e₀) := Work.EMFG.isEMSpaceUpTo_mono hFibre (by omega)
    exact Work.Pi6.EMM2.finiteType (ZMod 2) (by infer_instance : Module.Finite ℤ ℤ)
      (m := 2) (N := 6) (by norm_num) (Work.StemsB.fibrePoint p e₀) hF7 q (by omega)
  have hFinB3 : ∀ s : ℕ, s ≤ 3 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) X s) :=
    fun s hs => hFinB s (by omega)
  have hFinF3 : ∀ q : ℕ, q ≤ 3 → FiniteDimensional (ZMod 2) (Coh (ZMod 2) (Fib p e₀) q) :=
    fun q hq => hFinF q (by omega)
  -- 6. the total space is a K(Z,2) model through N (homotopy equivalent to KZ)
  have hE3 : IsZero (Coh (ZMod 2) (Work.Serre.mpath r) 3) := by
    haveI : Subsingleton (Coh (ZMod 2) KZ 3) := hwKZ_odd 1 (by norm_num)
    exact K2F9.isZero_coh_of_homotopyEquiv (homotopyEquiv_mpathOf r) 3
      (ModuleCat.isZero_of_subsingleton _)
  have hE4 : Module.finrank (ZMod 2) (Coh (ZMod 2) (Work.Serre.mpath r) 4) = 1 := by
    rw [(K2F9.finrank_coh_of_homotopyEquiv (𝕜 := ZMod 2) (homotopyEquiv_mpathOf r) 4).symm]
    exact hwKZ_fin 2 (by norm_num)
  have hE5 : IsZero (Coh (ZMod 2) (Work.Serre.mpath r) 5) := by
    haveI : Subsingleton (Coh (ZMod 2) KZ 5) := hwKZ_odd 2 (by norm_num)
    exact K2F9.isZero_coh_of_homotopyEquiv (homotopyEquiv_mpathOf r) 5
      (ModuleCat.isZero_of_subsingleton _)
  -- 7. the two Serre spectral sequences
  have hpc : Work.StemsB.IsSerreFibration p := Work.Serre.mpathQ_isSerreFibration r
  have hconn : Work.PiS.SimplyConn X (p e₀) := by
    show Work.PiS.SimplyConn X (r k₀)
    rw [hrk]
    exact hBconn
  obtain ⟨S, hS⟩ := hM (ZMod 2) (Work.Serre.mpath r) X p e₀ 6 hpc hconn hFinF hFinB
  obtain ⟨S3, hS3⟩ := hM (ZMod 2) (Work.Serre.mpath r) X p e₀ 3 hpc hconn hFinF3 hFinB3
  -- 8. the dimension bounds
  have hdims : Module.finrank (ZMod 2) (Coh (ZMod 2) X 3) ≤ 1 ∧
      Module.finrank (ZMod 2) (Coh (ZMod 2) X 4) ≤ 1 :=
    dimBounds p e₀ S hS hB0 hB1 hF0 hF1 hF2 hF3 hFinB hFinF hE3 hE4
  -- 9. the square of a nonzero class of H²(KZ) is nonzero
  have hwwKZ : Work.Pi6.cup (ZMod 2) KZ 2 2 wKZ wKZ ≠ 0 :=
    K2F9.cup_sq_ne_zero_of_cpow_two hco wKZ (hwKZ_pow 2 (by norm_num))
  have hKZ_sq : ∀ c : Coh (ZMod 2) KZ 2, c ≠ 0 →
      Work.Pi6.cup (ZMod 2) KZ 2 2 c c ≠ 0 := by
    intro c hc
    have hfin1 : Module.finrank (ZMod 2) (Coh (ZMod 2) KZ 2) = 1 := hwKZ_fin 1 (by norm_num)
    obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' wKZ hwKZ_ne).mp hfin1 c
    have hμ0 : μ ≠ 0 := by
      rintro h0
      exact hc (by rw [← hμ, h0, zero_smul])
    rw [← hμ]
    simp only [map_smul, LinearMap.smul_apply]
    rintro h
    rcases smul_eq_zero.mp h with h' | h'
    · exact absurd h' hμ0
    · rcases smul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hμ0
      · exact hwwKZ h''
  -- 10. injectivity of r* on H²
  have hp_inj : Function.Injective (Work.Pi6.cmap (ZMod 2) p 2) :=
    botEdgeInj p e₀ S3 hS3 hF0 hF1 (hFinF 0 (by norm_num)) hco
  have hmof_inj : Function.Injective (Work.Pi6.cmap (ZMod 2) (Work.Serre.mpathOf r) 2) := by
    haveI : CategoryTheory.IsIso (Work.Pi6.cmap (ZMod 2) (Work.Serre.mpathOf r) 2) :=
      K2F9.isIso_cmap_of_homotopyEquiv (homotopyEquiv_mpathOf r) 2
    exact (ConcreteCategory.bijective_of_isIso _).1
  have hcomp_eq : (Work.Serre.mpathQ r).comp (Work.Serre.mpathOf r) = r := by
    ext k; rfl
  have hofhom : TopCat.ofHom (Work.Serre.mpathOf r) ≫ TopCat.ofHom (Work.Serre.mpathQ r) =
      TopCat.ofHom r := by
    rw [← TopCat.ofHom_comp, hcomp_eq]
  have hfactor : Work.Pi6.cmap (ZMod 2) r 2 =
      Work.Pi6.cmap (ZMod 2) p 2 ≫ Work.Pi6.cmap (ZMod 2) (Work.Serre.mpathOf r) 2 := by
    have h := Work.Cohomology.singularCohomologyMap_comp (R := ZMod 2) (X := TopCat.of KZ)
      (Y := TopCat.of (Work.Serre.mpath r)) (Z := TopCat.of X)
      (TopCat.ofHom (Work.Serre.mpathOf r)) (TopCat.ofHom p) 2
    rw [show (TopCat.ofHom (Work.Serre.mpathOf r)) ≫ (TopCat.ofHom p)
        = TopCat.ofHom r from hofhom] at h
    simpa [Work.Pi6.cmap] using h
  have hr_inj : Function.Injective (Work.Pi6.cmap (ZMod 2) r 2) := by
    intro a b hab
    rw [hfactor] at hab
    simp only [ModuleCat.comp_apply] at hab
    exact hp_inj (hmof_inj hab)
  -- 11. the square-nonvanishing for H²(X)
  have ha_sq : ∀ a : Coh (ZMod 2) X 2, a ≠ 0 →
      Work.Pi6.cup (ZMod 2) X 2 2 a a ≠ 0 := by
    intro a ha
    have hra : Work.Pi6.cmap (ZMod 2) r 2 a ≠ 0 := by
      intro h
      exact ha (hr_inj (by rw [h, map_zero]))
    have hnat := Work.Cohomology.cupNaturalH (ZMod 2) (TopCat.ofHom r) 2 2 a a
    intro h
    have h' : Work.Cohomology.cupH' (ZMod 2) (TopCat.toSSet.obj (TopCat.of X)) 2 2 a a = 0 := h
    refine hKZ_sq (Work.Pi6.cmap (ZMod 2) r 2 a) hra ?_
    change Work.Cohomology.cupH' (ZMod 2) (TopCat.toSSet.obj (TopCat.of KZ)) 2 2
      (Work.Pi6.cmap (ZMod 2) r 2 a) (Work.Pi6.cmap (ZMod 2) r 2 a) = 0
    rw [← hnat, h']
    exact map_zero _
  -- 12. the square-nonvanishing for H³(X)
  have hwF_sq : Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) 2 2 wF wF ≠ 0 :=
    K2F9.cup_sq_ne_zero_of_cpow_two hco wF (hwF_pow 2 (by norm_num))
  have hy_sq : ∀ y : Coh (ZMod 2) X 3, y ≠ 0 →
      Work.Pi6.cup (ZMod 2) X 3 3 y y ≠ 0 :=
    fun y hy => K2F9.sq_core p e₀ S hS hB0 hB1 hF0 hF1 hF2 hF3 hF4 hF5
      hFinB hFinF hE3 hE5 hmc hco wF hwF_ne hwF_sq y hy
  exact ⟨hdims.1, hdims.2, ha_sq, hy_sq⟩

end

end Work.Pi6.EMM2

