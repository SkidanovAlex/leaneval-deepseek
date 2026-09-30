import Mathlib
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.SSSR.serreE1CruxDefs
import Submission.Work.SSSR.FirstPage.HomElts
import Submission.Work.SSSR.Filtration
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.Pi6.MSS.boundary_of_homologypi_zero
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Decomposition of the kernel of `jF`

Let `ξ` be the Serre filtration of `C_*(E)` along a continuous map `p : E → B` and let
`F_k = ξ.F.obj k` be its `k`-th term, with graded piece `gr_k = F_k/F_{k-1}`.  The map
`jF ξ k q : H_{k+q}(F_k) → H_{k+q}(gr_k)` of the exact couple is (for `k ≥ 1`) the map on homology
induced by the projection `π : F_k → gr_k`.

The lemma `jF_ker_decomp` computes the kernel of `jF` (`k ≥ 1`; the case `k = 0`, where
`jF ξ 0 q = 𝟙`, is treated separately) **on the chain level**: an element of `ker (jF ξ k q)`
represented by a cycle `v ∈ F_k` admits a decomposition
`ξ.incl k v = ξ.incl (k-1) Y + ξ.incl k (d Z)`.

The proof is the standard one: `jF [v] = 0` says that `[π v] = 0` in `H(gr_k)`, so `π v = d Z'`
for some chain `Z'` of `gr_k`; lifting `Z'` along the surjection `π` and using that
`ker π = im (F_{k-1} → F_k)` (exactness of `0 → F_{k-1} → F_k → gr_k → 0`) gives
`v - dZ ∈ im (F_{k-1} → F_k)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS

noncomputable section

/-- Naturality of `homologyπ` under `homologyMap`, elementwise. -/
theorem jFker_homologyMap_homologyπ {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) (i : ℕ) [K.HasHomology i] [L.HasHomology i] (z : K.cycles i) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyMap φ i)) (K.homologyπ i z)
      = L.homologyπ i (HomologicalComplex.cyclesMap φ i z) := by
  have h := HomologicalComplex.homologyπ_naturality (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.homology i) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The cycle map commutes with `iCycles`. -/
theorem jFker_iCycles_cyclesMap {R : Type} [CommRing R] {K L : ChainComplex (ModuleCat R) ℕ}
    (φ : K ⟶ L) (i : ℕ) [K.HasHomology i] [L.HasHomology i] (z : K.cycles i) :
    (ModuleCat.Hom.hom (L.iCycles i)) (HomologicalComplex.cyclesMap φ i z)
      = (ModuleCat.Hom.hom (φ.f i)) ((ModuleCat.Hom.hom (K.iCycles i)) z) := by
  have h := HomologicalComplex.cyclesMap_i (φ := φ) (i := i)
  have h2 := congrArg (fun (g : K.cycles i ⟶ L.X i) => (ModuleCat.Hom.hom g) z) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- **Descent along a term of the Serre filtration** (`k = k' + 1`): a cycle in `F_{k'+1}` whose
class is killed by `jF ξ (k'+1) q` decomposes in the total complex as a cycle of `F_{k'}` plus a
boundary. -/
theorem jFker_succ (𝕜 : Type) [Field 𝕜] {C : ChainComplex (ModuleCat 𝕜) ℕ}
    (ξ : Work.SSSR.Filtration 𝕜 C) (k' q : ℕ)
    (v : (ξ.F.obj (k'+1)).X ((k'+1)+q))
    (hv : (ModuleCat.Hom.hom ((ξ.F.obj (k'+1)).d ((k'+1)+q)
      ((ComplexShape.down ℕ).next ((k'+1)+q)))) v = 0)
    (hker : (Work.SSSR.jF ξ (k'+1) q)
      ((ξ.F.obj (k'+1)).homologyπ ((k'+1)+q)
        ((ξ.F.obj (k'+1)).cyclesMk v ((ComplexShape.down ℕ).next ((k'+1)+q)) rfl hv)) = 0) :
    ∃ (Y : (ξ.F.obj k').X ((k'+1)+q))
      (Z : (ξ.F.obj (k'+1)).X (((k'+1)+1)+q)),
      ((ξ.incl (k'+1)).f ((k'+1)+q)) v
        = ((ξ.incl k').f ((k'+1)+q)) Y
          + ((ξ.incl (k'+1)).f ((k'+1)+q))
              ((ModuleCat.Hom.hom ((ξ.F.obj (k'+1)).d (((k'+1)+1)+q) ((k'+1)+q))) Z) := by
  set π := cokernel.π (Work.SSSR.incF ξ.F k') with hπ
  set z := (ξ.F.obj (k'+1)).cyclesMk v ((ComplexShape.down ℕ).next ((k'+1)+q)) rfl hv with hz
  have hker1 : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap π ((k'+1)+q)))
      ((ξ.F.obj (k'+1)).homologyπ ((k'+1)+q) z) = 0 := hker
  have hnat := jFker_homologyMap_homologyπ π ((k'+1)+q) z
  have hgr : (cokernel (Work.SSSR.incF ξ.F k')).homologyπ ((k'+1)+q)
      (HomologicalComplex.cyclesMap π ((k'+1)+q) z) = 0 := by
    rw [← hnat]; exact hker1
  have hprev : (ComplexShape.down ℕ).prev ((k'+1)+q) = ((k'+1)+q)+1 :=
    ComplexShape.prev_eq' (c := ComplexShape.down ℕ)
      (ComplexShape.down_mk (((k'+1)+q)+1) ((k'+1)+q) rfl)
  have hj : (ComplexShape.down ℕ).prev ((k'+1)+q) = ((k'+1)+1)+q := by
    rw [hprev]; omega
  haveI : ∀ i, (cokernel (Work.SSSR.incF ξ.F k')).HasHomology i := fun i => inferInstance
  obtain ⟨Z0, hZ0⟩ := boundary_of_homologypi_zero (cokernel (Work.SSSR.incF ξ.F k'))
    ((k'+1)+q) (((k'+1)+1)+q) hj (HomologicalComplex.cyclesMap π ((k'+1)+q) z) hgr
  have hshort : ((Work.SSSR.sesF ξ k').map
      (HomologicalComplex.eval (ModuleCat 𝕜) (ComplexShape.down ℕ) (((k'+1)+1)+q))).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact (Work.SSSR.sesF ξ k')).mp
      (Work.SSSR.sesF_shortExact ξ k') (((k'+1)+1)+q)
  obtain ⟨Z1, hZ1⟩ := ShortComplex.ShortExact.moduleCat_surjective_g hshort Z0
  have hZ1' : (ModuleCat.Hom.hom (π.f (((k'+1)+1)+q))) Z1 = Z0 := hZ1
  have hstep : (ModuleCat.Hom.hom ((cokernel (Work.SSSR.incF ξ.F k')).d (((k'+1)+1)+q)
        ((k'+1)+q)))
      ((ModuleCat.Hom.hom (π.f (((k'+1)+1)+q))) Z1)
    = (ModuleCat.Hom.hom (π.f ((k'+1)+q)))
      ((ModuleCat.Hom.hom ((ξ.F.obj (k'+1)).d (((k'+1)+1)+q) ((k'+1)+q))) Z1) := by
    have h := congrArg (fun (g : (ξ.F.obj (k'+1)).X (((k'+1)+1)+q) ⟶
        (cokernel (Work.SSSR.incF ξ.F k')).X ((k'+1)+q)) => (ModuleCat.Hom.hom g) Z1)
      (π.comm (((k'+1)+1)+q) ((k'+1)+q))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hcyc : (ModuleCat.Hom.hom ((ξ.F.obj (k'+1)).iCycles ((k'+1)+q))) z = v := by
    rw [hz]; exact HomologicalComplex.i_cyclesMk (K := ξ.F.obj (k'+1)) v _ rfl hv
  have hcyc2 : (ModuleCat.Hom.hom ((cokernel (Work.SSSR.incF ξ.F k')).iCycles ((k'+1)+q)))
      (HomologicalComplex.cyclesMap π ((k'+1)+q) z)
        = (ModuleCat.Hom.hom (π.f ((k'+1)+q))) v := by
    rw [jFker_iCycles_cyclesMap π ((k'+1)+q) z, hcyc]
  have hfinal : (ModuleCat.Hom.hom (π.f ((k'+1)+q)))
      ((ModuleCat.Hom.hom ((ξ.F.obj (k'+1)).d (((k'+1)+1)+q) ((k'+1)+q))) Z1)
    = (ModuleCat.Hom.hom (π.f ((k'+1)+q))) v := by
    rw [← hstep, hZ1', hZ0, hcyc2]
  have hkerπ : (ModuleCat.Hom.hom (π.f ((k'+1)+q)))
      (v - (ModuleCat.Hom.hom ((ξ.F.obj (k'+1)).d (((k'+1)+1)+q) ((k'+1)+q))) Z1) = 0 := by
    rw [map_sub, hfinal, sub_self]
  have hrange : LinearMap.ker (ModuleCat.Hom.hom (π.f ((k'+1)+q)))
      = LinearMap.range (ModuleCat.Hom.hom ((Work.SSSR.incF ξ.F k').f ((k'+1)+q))) := by
    have hE := ShortComplex.Exact.moduleCat_range_eq_ker
      (((HomologicalComplex.shortExact_iff_degreewise_shortExact (Work.SSSR.sesF ξ k')).mp
        (Work.SSSR.sesF_shortExact ξ k') ((k'+1)+q)).exact)
    exact hE.symm
  obtain ⟨Y, hY⟩ := LinearMap.mem_range.mp (by rw [← hrange]; exact LinearMap.mem_ker.mpr hkerπ)
  refine ⟨Y, Z1, ?_⟩
  have hvdecomp : v = (ModuleCat.Hom.hom ((Work.SSSR.incF ξ.F k').f ((k'+1)+q))) Y
      + (ModuleCat.Hom.hom ((ξ.F.obj (k'+1)).d (((k'+1)+1)+q) ((k'+1)+q))) Z1 := by
    rw [hY]; abel
  rw [hvdecomp, map_add]
  congr 1
  have hc := congrArg (fun (g : ξ.F.obj k' ⟶ C) => (ModuleCat.Hom.hom (g.f ((k'+1)+q))) Y)
    (ξ.compat (Nat.le_succ k'))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at hc
  exact hc

end

theorem jF_ker_decomp (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (k q : ℕ)
    (v : (Work.Pi6.MSS.Cc 𝕜 p (k+1)).X (k+q))
    (hv : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).d (k+q)
      ((ComplexShape.down ℕ).next (k+q)))) v = 0)
    (hker : (Work.SSSR.jF (Work.SSSR.xiCan (R := 𝕜) p) k q)
      ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).homologyπ (k+q)
        ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).cyclesMk v ((ComplexShape.down ℕ).next (k+q)) rfl hv)) = 0) :
    ∃ (Y : (Work.Pi6.MSS.Cc 𝕜 p k).X (k+q))
      (Z : (Work.Pi6.MSS.Cc 𝕜 p (k+1)).X ((k+1)+q)),
      (Work.Pi6.MSS.inclL 𝕜 p (k+1)).f (k+q) v
        = (Work.Pi6.MSS.inclL 𝕜 p k).f (k+q) Y
          + (Work.Pi6.MSS.inclL 𝕜 p (k+1)).f (k+q)
              ((ModuleCat.Hom.hom ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).d ((k+1)+q) (k+q))) Z) := by
  cases k with
  | zero =>
    have h0 : (ModuleCat.Hom.hom ((Cc 𝕜 p 1).homologyπ (0+q)))
        ((Cc 𝕜 p 1).cyclesMk v ((ComplexShape.down ℕ).next (0+q)) rfl hv) = 0 := hker
    have hj : (ComplexShape.down ℕ).prev (0+q) = ((0+1)+q) := by
      have h1 : (ComplexShape.down ℕ).prev (0+q) = (0+q)+1 :=
        ComplexShape.prev_eq' (c := ComplexShape.down ℕ)
          (ComplexShape.down_mk ((0+q)+1) (0+q) rfl)
      rw [h1]; omega
    haveI : ∀ i, (Cc 𝕜 p 1).HasHomology i := fun i => inferInstance
    obtain ⟨Z0, hZ0⟩ := boundary_of_homologypi_zero (Cc 𝕜 p 1) (0+q) ((0+1)+q) hj
      ((Cc 𝕜 p 1).cyclesMk v ((ComplexShape.down ℕ).next (0+q)) rfl hv) h0
    have hZ0' : (ModuleCat.Hom.hom ((Cc 𝕜 p 1).iCycles (0+q)))
        ((Cc 𝕜 p 1).cyclesMk v ((ComplexShape.down ℕ).next (0+q)) rfl hv) = v :=
      HomologicalComplex.i_cyclesMk (K := Cc 𝕜 p 1) v _ rfl hv
    refine ⟨0, Z0, ?_⟩
    rw [hZ0, hZ0']
    simp only [map_zero, zero_add]
  | succ k' =>
    exact jFker_succ 𝕜 (Work.SSSR.xiCan (R := 𝕜) p) k' q v hv hker

end Work.Pi6.MSS
