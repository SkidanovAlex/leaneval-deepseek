import Mathlib
import Submission.Work.Pi6.MSS.e1CohDualDefs
import Submission.Work.Pi6.MSS.coFiltAnn
import Submission.Work.Pi6.MSS.evSaux
import Submission.Work.Pi6.MSS.e1CohDual.secLift
import Submission.Work.Pi6.MSS.e1CohDual.killCycles
import Submission.Work.Pi6.MSS.e1CohDual.secLiftDMem
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomologicalComplex
open scoped Simplicial

namespace Work.Pi6.MSS.e1CohDual

noncomputable section

variable (𝕜 : Type) [Field 𝕜]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## Two elementary rewritings -/

/-- The transposed differential in applied form, with the cochain displayed as a functional. -/
theorem dPrev_apply' (p : C(E, B)) (m : ℕ) (b : (serreCF 𝕜 E B p).C.X m)
    (v : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (m+1)) :
    (e1cCochFun 𝕜 p (m+1) ((serreCF 𝕜 E B p).dPrev (m+1) b)) v
      = (e1cCochFun 𝕜 p m b)
          (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (m+1) m).hom v) :=
  e1cW_dPrev_apply 𝕜 p m b v

/-- A cochain of `F^s` depends on a chain of `A_{s+1}` only through its class in the graded
piece: `c` evaluates the same on `v` and on the chosen lift of `π v`. -/
lemma secFactor (p : C(E, B)) (s n : ℕ) (c : (serreCF 𝕜 E B p).C.X n)
    (hc : c ∈ (serreCF 𝕜 E B p).F s n) (v : (e1cCc 𝕜 p (s+1)).X n) :
    (e1cCochFun 𝕜 p n c) (((e1cIncl 𝕜 p (s+1)).f n).hom v)
      = (e1cCochFun 𝕜 p n c) (((e1cIncl 𝕜 p (s+1)).f n).hom
          (e1cSec 𝕜 p s n (((e1cKgπ 𝕜 p s).f n).hom v))) := by
  have hsplit : ((e1cKgπ 𝕜 p s).f n).hom
      (v - e1cSec 𝕜 p s n (((e1cKgπ 𝕜 p s).f n).hom v)) = 0 := by
    rw [map_sub, e1cSec_apply, sub_self]
  have hkill : (e1cCochFun 𝕜 p n c)
      (((e1cIncl 𝕜 p (s+1)).f n).hom
        (v - e1cSec 𝕜 p s n (((e1cKgπ 𝕜 p s).f n).hom v))) = 0 :=
    e1cKillKernel' 𝕜 p s n hc hsplit
  have hsum : v = e1cSec 𝕜 p s n (((e1cKgπ 𝕜 p s).f n).hom v)
      + (v - e1cSec 𝕜 p s n (((e1cKgπ 𝕜 p s).f n).hom v)) := by abel
  conv_lhs => rw [hsum]
  rw [map_add, map_add, hkill, add_zero]

/-! ## Injectivity: the kernel of the evaluation is the denominator -/

theorem evZ_ker_le (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) (hx : e1cEvZ 𝕜 p s n x = 0) :
    (x.1 : (serreCF 𝕜 E B p).C.X n) ∈ pDen 𝕜 (serreCF 𝕜 E B p) 1 s n := by
  match n with
  | 0 =>
    have hF : (x.1 : (serreCF 𝕜 E B p).C.X 0) ∈ (serreCF 𝕜 E B p).F (s+1) 0 := by
      refine e1cF_of_kill 𝕜 p (s+1) 0 ?_
      intro w
      show (e1cCochFun 𝕜 p 0 x.1) (((e1cIncl 𝕜 p (s+1)).f 0).hom w) = 0
      rw [secFactor 𝕜 p s 0 x.1 x.2.1 w]
      refine killCycles 𝕜 p s 0 x hx (((e1cKgπ 𝕜 p s).f 0).hom w) ?_
      have h0 : (e1cKg 𝕜 p s).d 0 (0-1) = 0 := by
        rw [show (0:ℕ) - 1 = 0 from rfl]
        exact HomologicalComplex.shape (e1cKg 𝕜 p s) 0 0 (by simp [ComplexShape.down])
      rw [h0, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Work.Pi6.MSS.pDen_one_eq]
    exact Submodule.mem_sup.mpr ⟨x.1, hF, 0, Submodule.zero_mem _, add_zero _⟩
  | k+1 =>
    let φ : (e1cKg 𝕜 p s).X (k+1) →ₗ[𝕜] 𝕜 :=
      ((e1cCochFun 𝕜 p (k+1) x.1).comp ((e1cIncl 𝕜 p (s+1)).f (k+1)).hom).comp
        (e1cSec 𝕜 p s (k+1))
    have hφker : LinearMap.ker (((e1cKg 𝕜 p s).d (k+1) k).hom) ≤ LinearMap.ker φ := by
      intro u hu
      rw [LinearMap.mem_ker] at hu ⊢
      exact killCycles 𝕜 p s (k+1) x hx u hu
    obtain ⟨ψ, hψ⟩ := Work.Pi6.MSS.exists_comp_of_ker_le
      (((e1cKg 𝕜 p s).d (k+1) k).hom) φ hφker
    obtain ⟨y, hyF, hyπ⟩ := secLift 𝕜 p s k ψ
    have hx1 : (x.1 : (serreCF 𝕜 E B p).C.X (k+1))
        - (serreCF 𝕜 E B p).dPrev (k+1) y
        ∈ (serreCF 𝕜 E B p).F (s+1) (k+1) := by
      refine e1cF_of_kill 𝕜 p (s+1) (k+1) ?_
      intro w
      show (e1cCochFun 𝕜 p (k+1) x.1
          - e1cCochFun 𝕜 p (k+1) ((serreCF 𝕜 E B p).dPrev (k+1) y))
        (((e1cIncl 𝕜 p (s+1)).f (k+1)).hom w) = 0
      rw [LinearMap.sub_apply, secFactor 𝕜 p s (k+1) x.1 x.2.1 w]
      have hφv : (e1cCochFun 𝕜 p (k+1) x.1) (((e1cIncl 𝕜 p (s+1)).f (k+1)).hom
            (e1cSec 𝕜 p s (k+1) (((e1cKgπ 𝕜 p s).f (k+1)).hom w)))
          = φ (((e1cKgπ 𝕜 p s).f (k+1)).hom w) := rfl
      have hψv : ψ (((e1cKg 𝕜 p s).d (k+1) k).hom (((e1cKgπ 𝕜 p s).f (k+1)).hom w))
          = φ (((e1cKgπ 𝕜 p s).f (k+1)).hom w) :=
        LinearMap.congr_fun hψ (((e1cKgπ 𝕜 p s).f (k+1)).hom w)
      rw [hφv, ← hψv]
      have hcm : ((e1cKgπ 𝕜 p s).f k).hom (((e1cCc 𝕜 p (s+1)).d (k+1) k).hom w)
          = ((e1cKg 𝕜 p s).d (k+1) k).hom (((e1cKgπ 𝕜 p s).f (k+1)).hom w) := by
        have h := congrArg (fun (g : (e1cCc 𝕜 p (s+1)).X (k+1) ⟶ (e1cKg 𝕜 p s).X k) =>
          g.hom w) (e1cKgπ_comm 𝕜 p s k)
        rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
          LinearMap.comp_apply] at h
        exact h.symm
      rw [dPrev_apply' 𝕜 p k y ((e1cIncl 𝕜 p (s+1)).f (k+1) w),
        e1cIncl_d_apply 𝕜 p (s+1) k w, hyπ (((e1cCc 𝕜 p (s+1)).d (k+1) k).hom w), hcm,
        sub_self]
    have hδy : (serreCF 𝕜 E B p).dPrev (k+1) y
        ∈ ((serreCF 𝕜 E B p).F s ((k+1)-1)).map ((serreCF 𝕜 E B p).dPrev (k+1)) :=
      ⟨y, hyF, rfl⟩
    rw [Work.Pi6.MSS.pDen_one_eq]
    exact Submodule.mem_sup.mpr ⟨_, hx1, _, hδy, by abel⟩

/-! ## Surjectivity of the evaluation -/

theorem evZ_surj (p : C(E, B)) (s n : ℕ) :
    Function.Surjective (e1cEvZ 𝕜 p s n) := by
  intro q
  have hInj : Function.Injective (((e1cKg 𝕜 p s).iCycles n).hom) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  obtain ⟨ψ, hψ⟩ := Work.Pi6.MSS.exists_comp_of_injective
    (((e1cKg 𝕜 p s).iCycles n).hom) hInj
    (q.comp (((e1cKg 𝕜 p s).homologyπ n).hom))
  obtain ⟨y, hyF, hyπ⟩ := secLift 𝕜 p s n ψ
  have hbdry : ∀ v : (e1cKg 𝕜 p s).X (n+1),
      ψ (((e1cKg 𝕜 p s).d (n+1) n).hom v) = 0 := by
    intro v
    have h1 : ((e1cKg 𝕜 p s).iCycles n).hom
        (((e1cKg 𝕜 p s).toCycles (n+1) n).hom v)
        = ((e1cKg 𝕜 p s).d (n+1) n).hom v := by
      have h := congrArg (fun (f : (e1cKg 𝕜 p s).X (n+1) ⟶ (e1cKg 𝕜 p s).X n) =>
        f.hom v) (HomologicalComplex.toCycles_i (e1cKg 𝕜 p s) (n+1) n)
      rwa [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    have h2 : ((e1cKg 𝕜 p s).homologyπ n).hom
        (((e1cKg 𝕜 p s).toCycles (n+1) n).hom v) = 0 := by
      have h := congrArg (fun (g : (e1cKg 𝕜 p s).X (n+1) ⟶ (e1cKg 𝕜 p s).homology n) =>
        g.hom v) (HomologicalComplex.toCycles_comp_homologyπ (e1cKg 𝕜 p s) (n+1) n)
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] at h
      exact h
    have hψv : ψ (((e1cKg 𝕜 p s).iCycles n).hom
          (((e1cKg 𝕜 p s).toCycles (n+1) n).hom v))
        = q (((e1cKg 𝕜 p s).homologyπ n).hom
          (((e1cKg 𝕜 p s).toCycles (n+1) n).hom v)) :=
      LinearMap.congr_fun hψ (((e1cKg 𝕜 p s).toCycles (n+1) n).hom v)
    calc ψ (((e1cKg 𝕜 p s).d (n+1) n).hom v)
        = ψ (((e1cKg 𝕜 p s).iCycles n).hom
            (((e1cKg 𝕜 p s).toCycles (n+1) n).hom v)) := by rw [h1]
      _ = q (((e1cKg 𝕜 p s).homologyπ n).hom
            (((e1cKg 𝕜 p s).toCycles (n+1) n).hom v)) := hψv
      _ = q 0 := by rw [h2]
      _ = 0 := map_zero q
  have hδF : (serreCF 𝕜 E B p).dPrev (n+1) y ∈ (serreCF 𝕜 E B p).F (s+1) (n+1) :=
    secLiftDMem 𝕜 p s n ψ y hyπ hbdry
  have hyZ : y ∈ pZ 𝕜 (serreCF 𝕜 E B p) 1 s n :=
    Submodule.mem_inf.mpr ⟨hyF, hδF⟩
  refine ⟨⟨y, hyZ⟩, ?_⟩
  apply LinearMap.ext
  intro h'
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((e1cKg 𝕜 p s).homologyπ n)).1 inferInstance h'
  have hysec : (e1cCochFun 𝕜 p n y) (((e1cIncl 𝕜 p (s+1)).f n).hom
      (e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).iCycles n).hom z)))
      = ψ (((e1cKg 𝕜 p s).iCycles n).hom z) := by
    rw [hyπ (e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).iCycles n).hom z)), e1cSec_apply]
  have hψz : ψ (((e1cKg 𝕜 p s).iCycles n).hom z)
      = q (((e1cKg 𝕜 p s).homologyπ n).hom z) := LinearMap.congr_fun hψ z
  calc (e1cEvZ 𝕜 p s n ⟨y, hyZ⟩) (((e1cKg 𝕜 p s).homologyπ n).hom z)
      = e1cEv 𝕜 p s n ⟨y, hyZ⟩ (((e1cKg 𝕜 p s).homologyπ n).hom z) := rfl
    _ = e1cEvCyc 𝕜 p s n ⟨y, hyZ⟩ z := e1cEv_π 𝕜 p s n ⟨y, hyZ⟩ z
    _ = (e1cCochFun 𝕜 p n y) (((e1cIncl 𝕜 p (s+1)).f n).hom
          (e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).iCycles n).hom z))) := rfl
    _ = ψ (((e1cKg 𝕜 p s).iCycles n).hom z) := hysec
    _ = q (((e1cKg 𝕜 p s).homologyπ n).hom z) := hψz

/-! ## The comparison map on the page is bijective -/

theorem evBijective (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s n : ℕ) :
    Function.Bijective (Work.Pi6.MSS.e1cEvFrom 𝕜 p s n) := by
  constructor
  · intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
      ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s n).comap (pZ 𝕜 (serreCF 𝕜 E B p) 1 s n).subtype) a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective
      ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s n).comap (pZ 𝕜 (serreCF 𝕜 E B p) 1 s n).subtype) b
    rw [e1cEvFrom_apply, e1cEvFrom_apply] at hab
    have hmem : (x - y).1 ∈ pDen 𝕜 (serreCF 𝕜 E B p) 1 s n := by
      refine evZ_ker_le 𝕜 p s n (x - y) ?_
      have hsub : e1cEvZ 𝕜 p s n (x - y)
          = e1cEvZ 𝕜 p s n x - e1cEvZ 𝕜 p s n y :=
        LinearMap.map_sub (e1cEvZ 𝕜 p s n) x y
      have hxy : e1cEvZ 𝕜 p s n x = e1cEvZ 𝕜 p s n y := hab
      rw [hsub, hxy, sub_self]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.mem_comap.mpr hmem
  · intro q
    obtain ⟨x, hx⟩ := evZ_surj 𝕜 p s n q
    refine ⟨Submodule.mkQ
      ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s n).comap (pZ 𝕜 (serreCF 𝕜 E B p) 1 s n).subtype) x, ?_⟩
    rw [e1cEvFrom_apply]
    exact hx

end

end Work.Pi6.MSS.e1CohDual
