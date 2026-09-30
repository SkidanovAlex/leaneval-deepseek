import Mathlib
import Submission.Work.Pi6.MSS.E1Aux
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.coFiltAnn
import Submission.Work.SSSR.Filtration
import Submission.Work.SSSR.serreE2Defs
import Submission.Work.SSSR.SSetChain
import Submission.Work.SSSR.StemsB.SerreFiltration
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Vocabulary for `e1CohDual`: the Serre cochain `E_1` row as the dual of the chain `E_1` row

For a continuous map `p : E → B` and a field `𝕜` we set up the objects and the comparison map used
to prove that the cohomological `E_1` row of the Serre filtration of `p` (the row complex
`E1Row 𝕜 (serreCF 𝕜 E B p) q`) is the `𝕜`-dual of the chain level `E_1` row
(`dualComplex 𝕜 (E1Complex 𝕜 ξ q)` for `ξ.F = serF 𝕜 (Sing p)`).

## The objects

* `e1cF p` — the map `Sing E ⟶ Sing B`;
* `e1cSub p k` — the `k`-th Serre subcomplex of `Sing E` along `p` (the preimage of the
  `k`-skeleton of `Sing B`, i.e. the simplices whose image has essential dimension `< k`);
* `e1cCc 𝕜 p k` — its singular chains;
* `e1cIncl 𝕜 p k` — the inclusion of those chains into the chains of `E`;
* `e1cKg 𝕜 p s` — the `s`-th graded piece of the Serre filtration, `C(A_{s+1})/C(A_s)`;
* `e1cKgπ 𝕜 p s` — the quotient map `C(A_{s+1}) ⟶ C(A_{s+1})/C(A_s)`;
* `e1cSec 𝕜 p s n` — a linear section of `e1cKgπ 𝕜 p s` in degree `n`;
* `e1cFilt 𝕜 p` — a `Filtration` of `C_*(E;𝕜)` whose `F` is *definitionally* `serF 𝕜 (Sing p)`.

## The comparison map

An element of `pZ 𝕜 W 1 s n` (`W = serreCF 𝕜 E B p`) is a cochain `x` of `E` vanishing on the
chains of `A_s` and whose coboundary `δx` vanishes on the chains of `A_{s+1}`; evaluating `x` on
the chosen lifts (the section `e1cSec`) of the cycles of the graded piece gives a linear functional
`e1cEv 𝕜 p s n x` on `H_n(C(A_{s+1})/C(A_s))`, which factors through the page
`pEraw 𝕜 W 1 s n` (`e1cEvFrom`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomologicalComplex
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

variable (𝕜 : Type) [Field 𝕜]
variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-! ## The Serre subcomplexes and their chains -/

/-- The map of singular simplicial sets induced by `p`. -/
abbrev e1cF (p : C(E, B)) : Work.SSS.sSing E ⟶ Work.SSS.sSing B := Work.SSS.sSingP p

/-- The `k`-th Serre subcomplex of `Sing E` along `p`. -/
abbrev e1cSub (p : C(E, B)) (k : ℕ) : (Work.SSS.sSing E).Subcomplex :=
  Work.StemsB.serreSubcomplex (e1cF p) k

/-- The singular chains of the `k`-th Serre subcomplex. -/
abbrev e1cCc (p : C(E, B)) (k : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.SSSR.sChains 𝕜 (e1cSub p k)

/-- The inclusion of the chains of the `k`-th Serre subcomplex into the chains of `E`. -/
abbrev e1cIncl (p : C(E, B)) (k : ℕ) :
    e1cCc 𝕜 p k ⟶ Work.SSSR.sChains 𝕜 (Work.SSS.sSing E) :=
  Work.SSSR.sChainMap 𝕜 (e1cSub p k).ι

/-- The `s`-th graded piece of the Serre filtration, `C(A_{s+1})/C(A_s)`. -/
abbrev e1cKg (p : C(E, B)) (s : ℕ) : ChainComplex (ModuleCat 𝕜) ℕ :=
  Work.SSSR.grF (Work.SSSR.serF 𝕜 (e1cF p)) s

/-- The quotient map `C(A_{s+1}) ⟶ C(A_{s+1})/C(A_s)` onto the `s`-th graded piece. -/
abbrev e1cKgπ (p : C(E, B)) (s : ℕ) :
    (Work.SSSR.serF 𝕜 (e1cF p)).obj s ⟶ e1cKg 𝕜 p s :=
  Work.SSSR.grFι 𝕜 (e1cF p) s

/-- Membership in the `k`-th Serre subcomplex, in terms of the essential dimension of the image. -/
lemma e1cMemSub (p : C(E, B)) (k : ℕ) {n : ℕ} (τ : (Work.SSS.sSing E) _⦋n⦌) :
    τ ∈ (e1cSub p k).obj (op ⦋n⦌) ↔ ess ((e1cF p).app (op ⦋n⦌) τ) < k :=
  mem_serreSubcomplex_iff_ess (e1cF p) k τ

/-! ## The Serre filtration with `F = serF 𝕜 (Sing p)` -/

/-- **The Serre filtration of `C_*(E;𝕜)` along `p`**, whose `F` is definitionally
`Work.SSSR.serF 𝕜 (Sing p)`. -/
noncomputable def e1cFilt (p : C(E, B)) :
    Work.SSSR.Filtration 𝕜 (Work.Cohomology.singularChains 𝕜 (TopCat.of E)) where
  F := Work.SSSR.serF 𝕜 (e1cF p)
  mono s := Work.SSSR.mono_serreChainFiltration_map 𝕜 (e1cF p)
    (Work.SSSR.natShift.map (homOfLE (Nat.le_succ s)))
  incl s := e1cIncl 𝕜 p (s+1)
  mono_incl s := Work.SSSR.sChainMap_mono 𝕜 (e1cSub p (s+1)).ι inferInstance
  compat {s t} h := by
    show Work.SSSR.sChainMap 𝕜
          ((Work.SSSR.StemsB.serreFiltration (e1cF p)).map
            (Work.SSSR.natShift.map (homOfLE h))) ≫
        Work.SSSR.sChainMap 𝕜 (Subfunctor.ι (e1cSub p (t+1))) =
      Work.SSSR.sChainMap 𝕜 (Subfunctor.ι (e1cSub p (s+1)))
    exact (Work.SSSR.sChainMap_comp 𝕜 _ _).trans
      (congrArg (fun w => Work.SSSR.sChainMap 𝕜 w)
        (Work.SSSR.serreFiltration_map_iota (e1cF p) s t h))
  sat n := Work.SSSR.isIso_f_of_bijective 𝕜 (Subfunctor.ι (e1cSub p (n+1))) n
    (Work.SSSR.bijective_iota_app_of_obj_eq_top (e1cSub p (n+1)) n
      (Work.SSSR.serreSubcomplex_obj_eq_top (e1cF p) n))

@[simp] theorem e1cFilt_F (p : C(E, B)) :
    (e1cFilt 𝕜 p).F = Work.SSSR.serF 𝕜 (Work.SSS.sSingP p) := rfl

/-! ## A linear section of the projection onto the graded piece -/

/-- Over a field, every surjective linear map admits a linear right inverse. -/
noncomputable def e1cLinSection {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (f : M →ₗ[𝕜] N) (hf : Function.Surjective f) : N →ₗ[𝕜] M :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr hf))

theorem e1cLinSection_spec {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (f : M →ₗ[𝕜] N) (hf : Function.Surjective f) :
    f ∘ₗ e1cLinSection 𝕜 f hf = LinearMap.id :=
  Classical.choose_spec
    (LinearMap.exists_rightInverse_of_surjective f (LinearMap.range_eq_top.mpr hf))

theorem e1cLinSection_apply {M N : Type*} [AddCommGroup M] [Module 𝕜 M]
    [AddCommGroup N] [Module 𝕜 N] (f : M →ₗ[𝕜] N) (hf : Function.Surjective f) (y : N) :
    f (e1cLinSection 𝕜 f hf y) = y :=
  LinearMap.congr_fun (e1cLinSection_spec 𝕜 f hf) y

/-- The projection onto the `(k+1)`-st graded piece is surjective in every degree. -/
theorem e1cProj_surj (p : C(E, B)) (k n : ℕ) :
    Function.Surjective
      ((cokernel.π (Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k)).f n).hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

/-- **A linear section of the projection onto the `s`-th graded piece.** -/
noncomputable def e1cSec (p : C(E, B)) (s n : ℕ) :
    (e1cKg 𝕜 p s).X n →ₗ[𝕜] (e1cCc 𝕜 p (s+1)).X n :=
  match s with
  | 0 => LinearMap.id
  | (k+1) =>
    e1cLinSection 𝕜 ((cokernel.π (Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k)).f n).hom
      (e1cProj_surj 𝕜 p k n)

theorem e1cSec_spec (p : C(E, B)) (s n : ℕ) :
    ((e1cKgπ 𝕜 p s).f n).hom ∘ₗ e1cSec 𝕜 p s n = LinearMap.id := by
  match s with
  | 0 => rfl
  | (k+1) => exact e1cLinSection_spec 𝕜 _ (e1cProj_surj 𝕜 p k n)

theorem e1cSec_apply (p : C(E, B)) (s n : ℕ) (z : (e1cKg 𝕜 p s).X n) :
    ((e1cKgπ 𝕜 p s).f n).hom (e1cSec 𝕜 p s n z) = z :=
  LinearMap.congr_fun (e1cSec_spec 𝕜 p s n) z

/-! ## Elementary componentwise formulae -/

/-- `e1cKgπ` is a chain map (componentwise form). -/
theorem e1cKgπ_comm (p : C(E, B)) (s n : ℕ) :
    (e1cKgπ 𝕜 p s).f (n+1) ≫ (e1cKg 𝕜 p s).d (n+1) n =
      (e1cCc 𝕜 p (s+1)).d (n+1) n ≫ (e1cKgπ 𝕜 p s).f n :=
  (e1cKgπ 𝕜 p s).comm (n+1) n

/-- `e1cIncl` is a chain map (componentwise form). -/
theorem e1cIncl_comm (p : C(E, B)) (k n : ℕ) :
    (e1cIncl 𝕜 p k).f (n+1) ≫ (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n =
      (e1cCc 𝕜 p k).d (n+1) n ≫ (e1cIncl 𝕜 p k).f n :=
  (e1cIncl 𝕜 p k).comm (n+1) n

/-- The composite of the structure map `C(A_{s+1}) → C(A_{s+2})` with the inclusion into `C(E)` is
the inclusion of `C(A_{s+1})`. -/
theorem e1cIncl_incF (p : C(E, B)) (s n : ℕ) (w : (e1cCc 𝕜 p (s+1)).X n) :
    (e1cIncl 𝕜 p (s+2)).f n
        ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) s).f n w)
      = (e1cIncl 𝕜 p (s+1)).f n w := by
  have h2 := congrArg (fun (g : (Work.SSSR.serreFiltrationOf (R := 𝕜) p).F.obj s ⟶
      Work.Cohomology.singularChains 𝕜 (TopCat.of E)) => (g.f n).hom w)
    ((Work.SSSR.serreFiltrationOf (R := 𝕜) p).compat (Nat.le_succ s))
  exact h2

/-- A cochain of the Serre filtration, viewed as a linear functional on the chains of `E`. -/
def e1cCochFun (p : C(E, B)) (n : ℕ) (x : (serreCF 𝕜 E B p).C.X n) :
    Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n := x

/-- The differential of the Serre cochain filtration is the transpose of the boundary. -/
theorem e1cW_d_apply (p : C(E, B)) (n : ℕ) (x : (serreCF 𝕜 E B p).C.X n) :
    ((serreCF 𝕜 E B p).d n) x
      = (show Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n from x).comp
          (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n).hom) := by
  show (ModuleCat.Hom.hom ((Work.Cohomology.SSetCochainComplex 𝕜 (Work.SSS.sSing E)).d n
      (n+1))) x = _
  rw [Work.Cohomology.SSetCochainComplex_d]
  rfl

/-- The transposed differential, in applied form. -/
theorem e1cW_d_apply_applied (p : C(E, B)) (n : ℕ) (x : (serreCF 𝕜 E B p).C.X n)
    (z : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (n+1)) :
    e1cCochFun 𝕜 p n x (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n).hom z)
      = e1cCochFun 𝕜 p (n+1) (((serreCF 𝕜 E B p).d n) x) z := by
  rw [e1cW_d_apply 𝕜 p n x]
  rfl

/-! ## The filtration `F^s` is the annihilator of `C(A_s)` -/

/-- A cochain in `F^s` kills the chains of the `s`-th Serre subcomplex. -/
theorem e1cF_kill (p : C(E, B)) (s n : ℕ)
    {c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n}
    (hc : c ∈ (serreCF 𝕜 E B p).F s n) (w : (e1cCc 𝕜 p s).X n) :
    c (((e1cIncl 𝕜 p s).f n).hom w) = 0 := by
  have hc' : c ∈ compAnn 𝕜 (e1cSub p s) n := by
    rw [← coFiltAnn 𝕜 (e1cF p) s n, ← serreCF_F]
    exact hc
  exact hc' w

/-- A cochain which kills the chains of the `s`-th Serre subcomplex lies in `F^s`. -/
theorem e1cF_of_kill (p : C(E, B)) (s n : ℕ)
    {c : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n}
    (h : ∀ w : (e1cCc 𝕜 p s).X n, c (((e1cIncl 𝕜 p s).f n).hom w) = 0) :
    c ∈ (serreCF 𝕜 E B p).F s n := by
  rw [serreCF_F, coFiltAnn 𝕜 (e1cF p) s n]
  exact fun w => h w


/-! ## The kernel of the projection onto the graded piece -/

/-- `e1cKgπ 𝕜 p (k+1)` is the cokernel projection of the structure map. -/
theorem e1cKgπ_succ (p : C(E, B)) (k : ℕ) :
    e1cKgπ 𝕜 p (k+1) = cokernel.π (Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k) :=
  Work.SSSR.grFι_succ (R := 𝕜) (e1cF p) k

/-- The `n`-th component of the graded piece is the cokernel of the `n`-th component of the
inclusion of the chains of `A_k` into those of `A_{k+1}`. -/
noncomputable def e1cGrIso (p : C(E, B)) (k n : ℕ) :
    (e1cKg 𝕜 p (k+1)).X n ≅
      cokernel ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n) :=
  PreservesCokernel.iso (HomologicalComplex.eval (ModuleCat 𝕜) (ComplexShape.down ℕ) n)
    (Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k)

/-- The projection onto the graded piece corresponds to the cokernel projection under `e1cGrIso`. -/
theorem e1cGrIso_π (p : C(E, B)) (k n : ℕ) :
    (e1cKgπ 𝕜 p (k+1)).f n ≫ (e1cGrIso 𝕜 p k n).hom =
      cokernel.π ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n) := by
  have h := PreservesCokernel.π_iso_hom (HomologicalComplex.eval (ModuleCat 𝕜)
    (ComplexShape.down ℕ) n) (Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k)
  rw [e1cKgπ_succ 𝕜 p k]
  exact h

/-- **The kernel of the projection onto the `(k+1)`-st graded piece is the image of the inclusion
`C(A_{k+1}) ⟶ C(A_{k+2})`.** -/
theorem e1cKerπ_range (p : C(E, B)) (k n : ℕ) {w : (e1cCc 𝕜 p (k+2)).X n}
    (hw : ((e1cKgπ 𝕜 p (k+1)).f n).hom w = 0) :
    ∃ v : (e1cCc 𝕜 p (k+1)).X n,
      ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n).hom v = w := by
  have hπw : (cokernel.π ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n)).hom w = 0 := by
    rw [← e1cGrIso_π 𝕜 p k n]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, hw, map_zero]
  have hmk : (Submodule.mkQ (LinearMap.range
      ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n).hom)) w = 0 := by
    have h := ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom
      ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n)
    have h2 : ((cokernel.π ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n)) ≫
        (ModuleCat.cokernelIsoRangeQuotient
          ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n)).hom).hom
        = (ModuleCat.ofHom (LinearMap.range
            ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n).hom).mkQ).hom :=
      congrArg ModuleCat.Hom.hom h
    rw [ModuleCat.hom_comp] at h2
    have h4 := LinearMap.congr_fun h2 w
    rw [LinearMap.comp_apply, ModuleCat.hom_ofHom, hπw, map_zero] at h4
    exact h4.symm
  have hmem : w ∈ LinearMap.range ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n).hom := by
    have h4 : w ∈ LinearMap.ker (Submodule.mkQ (LinearMap.range
        ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (e1cF p)) k).f n).hom)) :=
      LinearMap.mem_ker.mpr hmk
    rwa [Submodule.ker_mkQ] at h4
  exact hmem

/-! ## The evaluation on the cycles of the graded piece -/

/-- The underlying cochain of an element of `Z_1^s`. -/
def e1cPageCoch (p : C(E, B)) (s n : ℕ) (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n := x.1

/-- The underlying cochain of an element of `Z_1^s` lies in `F^s`. -/
theorem e1cPageCoch_mem (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    e1cPageCoch 𝕜 p s n x ∈ (serreCF 𝕜 E B p).F s n := x.2.1

/-- The coboundary of the underlying cochain of an element of `Z_1^s` lies in `F^{s+1}`. -/
theorem e1cPageCoch_d_mem (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    ((serreCF 𝕜 E B p).d n) (x.1 : (serreCF 𝕜 E B p).C.X n)
      ∈ (serreCF 𝕜 E B p).F (s+1) (n+1) := x.2.2

/-- The cycles of the `s`-th graded piece evaluate the cochain `x` through the chosen lifts. -/
def e1cEvCyc (p : C(E, B)) (s n : ℕ) (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    (e1cKg 𝕜 p s).cycles n →ₗ[𝕜] 𝕜 :=
  ((e1cPageCoch 𝕜 p s n x).comp
      (((e1cIncl 𝕜 p (s+1)).f n).hom.comp (e1cSec 𝕜 p s n))).comp
    ((e1cKg 𝕜 p s).iCycles n).hom

theorem e1cEvCyc_apply (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) (z : (e1cKg 𝕜 p s).cycles n) :
    e1cEvCyc 𝕜 p s n x z = e1cPageCoch 𝕜 p s n x
      (((e1cIncl 𝕜 p (s+1)).f n).hom
        (e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).iCycles n).hom z))) := rfl

/-- **A cochain of `F^s` kills the kernel of the projection onto the `s`-th graded piece.** -/
theorem e1cKillKernel' (p : C(E, B)) (s n : ℕ)
    {b : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) n}
    (hb : b ∈ (serreCF 𝕜 E B p).F s n) {w : (e1cCc 𝕜 p (s+1)).X n}
    (hw : ((e1cKgπ 𝕜 p s).f n).hom w = 0) :
    b ((e1cIncl 𝕜 p (s+1)).f n w) = 0 := by
  match s with
  | 0 =>
    have hw0 : w = 0 := hw
    rw [hw0, map_zero, map_zero]
  | (k+1) =>
    obtain ⟨v, hv⟩ := e1cKerπ_range 𝕜 p k n hw
    rw [← hv, e1cIncl_incF 𝕜 p k n v]
    exact e1cF_kill 𝕜 p (k+1) n hb v

/-- A cochain of `F^s` kills the kernel of the projection onto the `s`-th graded piece
(element of the page form). -/
theorem e1cKillKernel (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) {w : (e1cCc 𝕜 p (s+1)).X n}
    (hw : ((e1cKgπ 𝕜 p s).f n).hom w = 0) :
    e1cPageCoch 𝕜 p s n x ((e1cIncl 𝕜 p (s+1)).f n w) = 0 :=
  e1cKillKernel' 𝕜 p s n (e1cPageCoch_mem 𝕜 p s n x) hw


/-! ## The evaluation is well defined on homology -/

/-- The inclusion is a chain map, in applied form. -/
theorem e1cIncl_d_apply (p : C(E, B)) (k n : ℕ) (z : (e1cCc 𝕜 p k).X (n+1)) :
    ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (n+1) n).hom
        (((e1cIncl 𝕜 p k).f (n+1)).hom z)
      = ((e1cIncl 𝕜 p k).f n).hom (((e1cCc 𝕜 p k).d (n+1) n).hom z) := by
  have h := congrArg (fun (g : (e1cCc 𝕜 p k).X (n+1) ⟶
      (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X n) => g.hom z)
    (e1cIncl_comm 𝕜 p k n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
  exact h

/-- The evaluation of `x` on the boundary of a lift vanishes (this is `δx ∈ F^{s+1}`). -/
theorem e1cEvCyc_bdry (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) (y : (e1cKg 𝕜 p s).X (n+1)) :
    e1cPageCoch 𝕜 p s n x ((e1cIncl 𝕜 p (s+1)).f n
      (((e1cCc 𝕜 p (s+1)).d (n+1) n).hom (e1cSec 𝕜 p s (n+1) y))) = 0 := by
  rw [← e1cIncl_d_apply 𝕜 p (s+1) n (e1cSec 𝕜 p s (n+1) y),
    show e1cPageCoch 𝕜 p s n x = e1cCochFun 𝕜 p n x.1 from rfl, e1cW_d_apply_applied 𝕜 p n x.1]
  exact e1cF_kill 𝕜 p (s+1) (n+1) (e1cPageCoch_d_mem 𝕜 p s n x) (e1cSec 𝕜 p s (n+1) y)

/-- The evaluation of `x` on the correction term
`sec (d z) - ∂ (sec z) ∈ ker π` vanishes, because `x ∈ F^s`. -/
theorem e1cEvCyc_corr (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) (y : (e1cKg 𝕜 p s).X (n+1)) :
    e1cPageCoch 𝕜 p s n x ((e1cIncl 𝕜 p (s+1)).f n
      (e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).d (n+1) n).hom y)
        - ((e1cCc 𝕜 p (s+1)).d (n+1) n).hom (e1cSec 𝕜 p s (n+1) y))) = 0 := by
  apply e1cKillKernel 𝕜 p s n x
  rw [map_sub, e1cSec_apply]
  have h := congrArg (fun (g : (e1cCc 𝕜 p (s+1)).X (n+1) ⟶ (e1cKg 𝕜 p s).X n) => g.hom (e1cSec 𝕜 p s (n+1) y))
    (e1cKgπ_comm 𝕜 p s n)
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
  apply sub_eq_zero.mpr
  conv_lhs => rw [← e1cSec_apply 𝕜 p s (n+1) y]
  exact h

/-- The evaluation on the cycles of the graded piece kills the boundaries: this makes the
comparison map well defined on homology. -/
theorem e1cEvCyc_kill (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    (e1cKg 𝕜 p s).toCycles (n+1) n ≫ ModuleCat.ofHom (e1cEvCyc 𝕜 p s n x) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  have hI : ((e1cKg 𝕜 p s).iCycles n).hom (((e1cKg 𝕜 p s).toCycles (n+1) n).hom y)
      = ((e1cKg 𝕜 p s).d (n+1) n).hom y := by
    have h := congrArg (fun (f : (e1cKg 𝕜 p s).X (n+1) ⟶ (e1cKg 𝕜 p s).X n) => f.hom y)
      (HomologicalComplex.toCycles_i (e1cKg 𝕜 p s) (n+1) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  show e1cEvCyc 𝕜 p s n x (((e1cKg 𝕜 p s).toCycles (n+1) n).hom y) = 0
  rw [e1cEvCyc_apply, hI]
  have hsplit : e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).d (n+1) n).hom y)
      = ((e1cCc 𝕜 p (s+1)).d (n+1) n).hom (e1cSec 𝕜 p s (n+1) y)
        + (e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).d (n+1) n).hom y)
          - ((e1cCc 𝕜 p (s+1)).d (n+1) n).hom (e1cSec 𝕜 p s (n+1) y)) := by abel
  rw [hsplit, map_add, map_add]
  rw [e1cEvCyc_bdry 𝕜 p s n x y, e1cEvCyc_corr 𝕜 p s n x y, add_zero]

/-- The predecessor in the chain complex shape: `(ComplexShape.down ℕ).prev n = n + 1`. -/
theorem e1cPrev (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 :=
  (ComplexShape.down ℕ).prev_eq' (show (ComplexShape.down ℕ).Rel (n+1) n from rfl)

/-- **The comparison map** on the cocycles of the cochain page, as a functional on the homology of
the graded piece. -/
noncomputable def e1cEv (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    (e1cKg 𝕜 p s).homology n →ₗ[𝕜] 𝕜 :=
  (Cofork.IsColimit.desc ((e1cKg 𝕜 p s).homologyIsCokernel (n+1) n (e1cPrev n))
    (ModuleCat.ofHom (e1cEvCyc 𝕜 p s n x))
    (by rw [e1cEvCyc_kill 𝕜 p s n x, zero_comp])).hom

/-- The computation rule for the comparison map. -/
theorem e1cEv_π (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) (z : (e1cKg 𝕜 p s).cycles n) :
    e1cEv 𝕜 p s n x (((e1cKg 𝕜 p s).homologyπ n).hom z) = e1cEvCyc 𝕜 p s n x z := by
  have h := Cofork.IsColimit.π_desc
    (t := (CokernelCofork.ofπ (ModuleCat.ofHom (e1cEvCyc 𝕜 p s n x))
      (by rw [e1cEvCyc_kill 𝕜 p s n x]) :
        CokernelCofork ((e1cKg 𝕜 p s).toCycles (n+1) n)))
    ((e1cKg 𝕜 p s).homologyIsCokernel (n+1) n (e1cPrev n))
  have h2 := congrArg (fun (f : (e1cKg 𝕜 p s).cycles n ⟶ ModuleCat.of 𝕜 𝕜) => f.hom z) h
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, CokernelCofork.π_ofπ,
    CokernelCofork.π_ofπ, ModuleCat.hom_ofHom] at h2
  exact h2

/-! ## Linearity of the comparison map in the cochain -/

theorem e1cEvCyc_add (p : C(E, B)) (s n : ℕ)
    (x y : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    e1cEvCyc 𝕜 p s n (x + y) = e1cEvCyc 𝕜 p s n x + e1cEvCyc 𝕜 p s n y := by
  apply LinearMap.ext
  intro z
  simp only [e1cEvCyc_apply, LinearMap.add_apply]
  rw [show e1cPageCoch 𝕜 p s n (x + y) = e1cPageCoch 𝕜 p s n x + e1cPageCoch 𝕜 p s n y from rfl,
    LinearMap.add_apply]

theorem e1cEvCyc_smul (p : C(E, B)) (s n : ℕ) (a : 𝕜)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    e1cEvCyc 𝕜 p s n (a • x) = a • e1cEvCyc 𝕜 p s n x := by
  apply LinearMap.ext
  intro z
  simp only [e1cEvCyc_apply, LinearMap.smul_apply]
  rw [show e1cPageCoch 𝕜 p s n (a • x) = a • e1cPageCoch 𝕜 p s n x from rfl, LinearMap.smul_apply]

theorem e1cEv_add (p : C(E, B)) (s n : ℕ)
    (x y : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    e1cEv 𝕜 p s n (x + y) = e1cEv 𝕜 p s n x + e1cEv 𝕜 p s n y := by
  apply LinearMap.ext
  intro z
  obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective ((e1cKg 𝕜 p s).homologyπ n)).1
    inferInstance z
  rw [e1cEv_π, LinearMap.add_apply, e1cEv_π, e1cEv_π, e1cEvCyc_add, LinearMap.add_apply]

theorem e1cEv_smul (p : C(E, B)) (s n : ℕ) (a : 𝕜)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    e1cEv 𝕜 p s n (a • x) = a • e1cEv 𝕜 p s n x := by
  apply LinearMap.ext
  intro z
  obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective ((e1cKg 𝕜 p s).homologyπ n)).1
    inferInstance z
  rw [e1cEv_π, LinearMap.smul_apply, e1cEv_π, e1cEvCyc_smul, LinearMap.smul_apply]

/-- The comparison map, as a linear map in the cochain. -/
noncomputable def e1cEvZ (p : C(E, B)) (s n : ℕ) :
    ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n) →ₗ[𝕜]
      ((e1cKg 𝕜 p s).homology n →ₗ[𝕜] 𝕜) where
  toFun x := e1cEv 𝕜 p s n x
  map_add' := e1cEv_add 𝕜 p s n
  map_smul' := e1cEv_smul 𝕜 p s n

@[simp] theorem e1cEvZ_apply (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    e1cEvZ 𝕜 p s n x = e1cEv 𝕜 p s n x := rfl

/-! ## The comparison map vanishes on the denominator -/

/-- The comparison map vanishes on `F^{s+1}`. -/
theorem e1cEv_mem_F (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n))
    (hx : e1cPageCoch 𝕜 p s n x ∈ (serreCF 𝕜 E B p).F (s+1) n) :
    e1cEv 𝕜 p s n x = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective ((e1cKg 𝕜 p s).homologyπ n)).1
    inferInstance z
  rw [e1cEv_π, LinearMap.zero_apply, e1cEvCyc_apply]
  exact e1cF_kill 𝕜 p (s+1) n hx (e1cSec 𝕜 p s n (((e1cKg 𝕜 p s).iCycles n).hom z'))

/-- The transposed differential `dPrev`, in applied form. -/
theorem e1cW_dPrev_apply (p : C(E, B)) (m : ℕ) (b : (serreCF 𝕜 E B p).C.X m)
    (v : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (m+1)) :
    (show Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) (m+1)
      from ((serreCF 𝕜 E B p).dPrev (m+1)) b) v
      = (show Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) m from b)
          (((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (m+1) m).hom v) := by
  have h : (serreCF 𝕜 E B p).dPrev (m+1) = (serreCF 𝕜 E B p).d m := rfl
  rw [h]
  exact congrArg (fun (g : (Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).X (m+1) →ₗ[𝕜] 𝕜) => g v)
    (e1cW_d_apply 𝕜 p m b)

/-- The comparison map vanishes on the `pB` part of the denominator (the coboundaries of `F^s`). -/
theorem e1cEv_zero_of_pB (p : C(E, B)) (s m : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s (m+1)))
    (hx : e1cPageCoch 𝕜 p s (m+1) x ∈ pB 𝕜 (serreCF 𝕜 E B p) 1 s (m+1)) :
    e1cEv 𝕜 p s (m+1) x = 0 := by
  obtain ⟨b, hb, hbc⟩ := hx.2
  have hb' : b ∈ (serreCF 𝕜 E B p).F s m := hb
  apply LinearMap.ext
  intro z
  obtain ⟨z', rfl⟩ := (ModuleCat.epi_iff_surjective ((e1cKg 𝕜 p s).homologyπ (m+1))).1
    inferInstance z
  rw [e1cEv_π, LinearMap.zero_apply, e1cEvCyc_apply, ← hbc,
    e1cW_dPrev_apply 𝕜 p m b]
  rw [e1cIncl_d_apply 𝕜 p (s+1) m]
  apply e1cKillKernel' 𝕜 p s m hb'
  have hcomm : ((e1cKgπ 𝕜 p s).f m).hom
      (((e1cCc 𝕜 p (s+1)).d (m+1) m).hom (e1cSec 𝕜 p s (m+1) (((e1cKg 𝕜 p s).iCycles (m+1)).hom z')))
      = ((e1cKg 𝕜 p s).d (m+1) m).hom
        (((e1cKgπ 𝕜 p s).f (m+1)).hom (e1cSec 𝕜 p s (m+1) (((e1cKg 𝕜 p s).iCycles (m+1)).hom z'))) := by
    have h := congrArg (fun (g : (e1cCc 𝕜 p (s+1)).X (m+1) ⟶ (e1cKg 𝕜 p s).X m) => g.hom
      (e1cSec 𝕜 p s (m+1) (((e1cKg 𝕜 p s).iCycles (m+1)).hom z')))
      (e1cKgπ_comm 𝕜 p s m)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
    exact h.symm
  rw [hcomm, e1cSec_apply]
  have hz := congrArg (fun (f : (e1cKg 𝕜 p s).cycles (m+1) ⟶ (e1cKg 𝕜 p s).X m) => f.hom z')
    (HomologicalComplex.iCycles_d (e1cKg 𝕜 p s) (m+1) m)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using hz

/-- The comparison map vanishes on the whole denominator `pDen ∩ pZ`; this is the well-definedness
of the comparison map on the page `E_1^{s,n}`. -/
theorem e1cEvZ_pDen (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n))
    (hx : (x.1 : (serreCF 𝕜 E B p).C.X n) ∈ pDen 𝕜 (serreCF 𝕜 E B p) 1 s n) :
    e1cEvZ 𝕜 p s n x = 0 := by
  obtain ⟨a, ha, c, hc, hsum⟩ := Submodule.mem_sup.mp hx
  have haF : a ∈ (serreCF 𝕜 E B p).F (s+1) n := ha.1
  have haZ : a ∈ pZ 𝕜 (serreCF 𝕜 E B p) 1 s n :=
    Submodule.mem_inf.mpr ⟨(serreCF 𝕜 E B p).F_mono s n haF, ha.2⟩
  have hcZ : c ∈ pZ 𝕜 (serreCF 𝕜 E B p) 1 s n :=
    Submodule.mem_inf.mpr ⟨hc.1, Submodule.mem_comap.mpr (by
      rw [pd_pB_leib 1 s n c hc]
      exact Submodule.zero_mem _)⟩
  have hxeq : x = (⟨a, haZ⟩ : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) + ⟨c, hcZ⟩ := by
    apply Subtype.ext
    show x.1 = a + c
    exact hsum.symm
  have h1 : e1cEvZ 𝕜 p s n (⟨a, haZ⟩ : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) = 0 :=
    e1cEv_mem_F 𝕜 p s n ⟨a, haZ⟩ haF
  have h2 : e1cEvZ 𝕜 p s n (⟨c, hcZ⟩ : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) = 0 := by
    cases n with
    | zero =>
      have hc0 : c = 0 := by
        have h := hc
        rw [pd_pB_zero 1 s] at h
        exact h
      have hz : (⟨c, hcZ⟩ : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s 0)) = 0 := Subtype.ext hc0
      rw [hz, map_zero]
    | succ m => exact e1cEv_zero_of_pB 𝕜 p s m ⟨c, hcZ⟩ hc
  rw [hxeq, map_add, h1, h2, add_zero]

/-- **The comparison map on the page `E_1^{s,n}`**, as a linear map into the dual of the homology of
the graded piece. -/
noncomputable def e1cEvFrom (p : C(E, B)) (s n : ℕ) :
    (pEraw 𝕜 (serreCF 𝕜 E B p) 1 s n) →ₗ[𝕜] ((e1cKg 𝕜 p s).homology n →ₗ[𝕜] 𝕜) :=
  Submodule.liftQ ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s n).comap
      (pZ 𝕜 (serreCF 𝕜 E B p) 1 s n).subtype) (e1cEvZ 𝕜 p s n) (by
    intro x hx
    rw [LinearMap.mem_ker]
    exact e1cEvZ_pDen 𝕜 p s n x (Submodule.mem_comap.mp hx))

/-- The computation rule for the comparison map on the page. -/
theorem e1cEvFrom_apply (p : C(E, B)) (s n : ℕ)
    (x : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s n)) :
    e1cEvFrom 𝕜 p s n (Submodule.mkQ ((pDen 𝕜 (serreCF 𝕜 E B p) 1 s n).comap
        (pZ 𝕜 (serreCF 𝕜 E B p) 1 s n).subtype) x) = e1cEv 𝕜 p s n x :=
  Submodule.liftQ_apply _ _ x


/-! ## Transport of cohomological degrees -/

/-- The transport of an element of the homology of a chain complex along an equality of degrees. -/
def e1cHomCast {K : ChainComplex (ModuleCat 𝕜) ℕ} {a b : ℕ} (h : a = b) :
    K.homology a →ₗ[𝕜] K.homology b :=
  (eqToHom (congrArg (fun n => K.homology n) h)).hom

/-- The transport of an element of `Z_1^s` along an equality of cohomological degrees. -/
noncomputable def e1cPZcast (p : C(E, B)) (s : ℕ) {a b : ℕ} (h : a = b) :
    ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s a) →ₗ[𝕜] ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s b) :=
  LinearMap.codRestrict (pZ 𝕜 (serreCF 𝕜 E B p) 1 s b)
    (((serreCF 𝕜 E B p).xcast h).comp (pZ 𝕜 (serreCF 𝕜 E B p) 1 s a).subtype)
    (fun y => (pd_xcast_mem_pZ_iff (𝕜 := 𝕜) (W := serreCF 𝕜 E B p) (r := 1) (s := s) h y.1).mpr y.2)

@[simp] theorem e1cPZcast_apply (p : C(E, B)) (s : ℕ) {a b : ℕ} (h : a = b)
    (y : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s a)) :
    ((e1cPZcast 𝕜 p s h y : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s b))
        : (serreCF 𝕜 E B p).C.X b)
      = (serreCF 𝕜 E B p).xcast h (y : (serreCF 𝕜 E B p).C.X a) := rfl

/-- The comparison map on the page, in the degree convention of the `E_1` column of the
cohomological filtration (`q + s` for the page, `s + q` for the homology of the graded piece,
matching `E1Complex`). -/
noncomputable def e1cEvShift (p : C(E, B)) (s q : ℕ) :
    (pEraw 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)) →ₗ[𝕜]
      ((e1cKg 𝕜 p s).homology (s+q) →ₗ[𝕜] 𝕜) :=
  (LinearMap.dualMap (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s) (Nat.add_comm s q))).comp
    (e1cEvFrom 𝕜 p s (q+s))

theorem e1cEvShift_apply (p : C(E, B)) (s q : ℕ)
    (y : (pEraw 𝕜 (serreCF 𝕜 E B p) 1 s (q+s)))
    (z : (e1cKg 𝕜 p s).homology (s+q)) :
    e1cEvShift 𝕜 p s q y z
      = e1cEvFrom 𝕜 p s (q+s) y (e1cHomCast 𝕜 (K := e1cKg 𝕜 p s)
          (Nat.add_comm s q) z) := rfl


/-- `pZmap` commutes with the transport of cohomological degrees. -/
theorem e1cPZmapPZcast (p : C(E, B)) (s : ℕ) {a b : ℕ} (h : a = b)
    (y : ↥(pZ 𝕜 (serreCF 𝕜 E B p) 1 s a)) :
    pZmap 𝕜 (serreCF 𝕜 E B p) 1 s b (e1cPZcast 𝕜 p s h y)
      = e1cPZcast 𝕜 p (s+1) (show a+1 = b+1 by omega)
          (pZmap 𝕜 (serreCF 𝕜 E B p) 1 s a y) := by
  apply Subtype.ext
  rw [e1cPZcast_apply, pd_pZmap_apply (𝕜 := 𝕜) (W := serreCF 𝕜 E B p) (r := 1) (s := s)
      (n := b),
    pd_pZmap_apply (𝕜 := 𝕜) (W := serreCF 𝕜 E B p) (r := 1) (s := s) (n := a)]
  exact (pd_xcast_d (𝕜 := 𝕜) (W := serreCF 𝕜 E B p) h
    (show a+1 = b+1 by omega) y.1).symm

end

end Work.Pi6.MSS
