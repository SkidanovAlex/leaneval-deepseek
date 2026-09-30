import Mathlib
import Submission.Work.Pi6.MSS.E2cfkDefs
import Submission.Work.Pi6.MSS.fibre_to_pullback
import Submission.Work.Pi6.MSS.horn_to_fibre
import Submission.Work.Pi6.MSS.vertical_decomp
import Submission.Work.Pi6.MSS.exists_edge
import Submission.Work.Pi6.MSS.pieceHorn_lift
import Submission.Work.Pi6.MSS.transport_chain
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.coFiltAnn
import Submission.Work.Pi6.Interfaces
import Submission.Work.SSSR.pieceHornAcyclic
import Submission.Work.SSSR.pieceContraction
import Submission.Work.SSSR.pieceAlongZero
import Submission.Work.SSSR.singPullbackIso_exists
import Submission.Work.SSSR.sSingP_fibreIncl_comp
import Submission.Work.SSSR.sndToSerre_range
import Submission.Work.SSSR.serreE1Defs
import Submission.Work.SSSR.SSetChain
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The fibre kernel of the column `E_2^{0,q}` of the Serre spectral sequence

`Work.Pi6.MSS.e2Col_fibre_kernel` is the injectivity of the restriction of the column `E_2^{0,q}`
of the Serre spectral sequence of a Serre fibration `p : E → B` over a simply connected base to the
cohomology of the fibre `F = p⁻¹(p e₀)`.

The statement is about the concrete cochain model `Work.Pi6.MSS.serreCF 𝕜 E B p`: its `C` is the
singular cochain complex of `E` with coefficients in the field `𝕜`, its filtration `F s` is the
Serre filtration `Work.Pi6.MSS.coFilt 𝕜 (Sing p) s` (cochains vanishing on the simplices lying over
the `(s-1)`-skeleton of `B`), `Work.Pi6.MSS.pZ 𝕜 W r s n = Z_r^s`, `Work.Pi6.MSS.pDen 𝕜 W r s n =
Z_{r-1}^{s+1} + B_r^s` and `pEraw 𝕜 W r s n = Z_r^s/pDen 𝕜 W r s n` is the page `E_r^s`.  The
conclusion `x ∈ pDen 𝕜 W 2 0 q` therefore says that the class of `x` vanishes in `E_2^{0,q}`.

## The argument

Write `F = p⁻¹(p e₀)` and let `C_*(E;𝕜)`, `C_*(F;𝕜)` be the singular chain complexes with `𝕜`
coefficients.  The proof has three parts.

* **Linear algebra** (`Work.Pi6.MSS.mem_pDen_of_kills_cycles`): over a field, a cochain
  `x ∈ C^q(E;𝕜)` with `δx` vanishing on the chains over the `1`-skeleton of `B` lies in
  `F^1 C^q + im δ` if and only if it vanishes on every *vertical* cycle, i.e. on every cycle of the
  subcomplex `serreSubcomplex (Sing p) 1` of simplices lying over the vertices of `B`
  (`Work.Pi6.MSS.mem_sup_of_kills`).  The "only if" direction is immediate; for the converse one
  factors `x|_V` through the boundary `∂ : V → C_{q-1}(E;𝕜)` (which is possible because `x`
  vanishes on the cycles) and extends the resulting functional to `C_{q-1}(E;𝕜)`, using that over a
  field linear functionals on a subspace extend (`LinearMap.exists_extend`).
* **Restriction to a fibre is a coboundary** (`hv`): the hypothesis `hv` says exactly that
  `x|_{C_*(F;𝕜)}` vanishes on the cycles of `C_*(F;𝕜)`, which over a field means that
  `x|_{C_*(F;𝕜)} = δ w` is a coboundary; equivalently (and this is the form used) that `x` vanishes
  on the cycles of the fibre over `p e₀`.
* **Propagation from the fibre to all vertical cycles**
  (`Work.Pi6.MSS.vertical_transport`, proved from the ω-piece machinery of the library and the
  lemmas `Work.Pi6.MSS.fibre_to_pullback`, `Work.Pi6.MSS.horn_to_fibre`,
  `Work.Pi6.MSS.vertical_decomp`, `Work.Pi6.MSS.exists_edge`, `Work.Pi6.MSS.pieceHorn_lift`):  a
  vertical cycle splits as a finite sum of cycles of the fibres `p⁻¹ b` (`vertical_decomp`); each of
  those is homologous, modulo the chains over the `1`-skeleton of `B` (on which `δx` vanishes by
  `hx`), to a cycle of the fibre over `p e₀`: transporting a cycle of `p⁻¹ b` along an edge
  `σ : Δ[1] ⟶ Sing B` from `b` to `p e₀` (`exists_edge`), the cycle maps into the pullback
  `T_σ = Δ[1] ×_{Sing B} Sing E` (`fibre_to_pullback`), where the horn-acyclicity of
  `Work.SSSR.pieceHornAcyclic` produces a chain over the horn and a boundary (`pieceHorn_lift`), and
  the horn is the fibre over the last vertex of `σ` (`horn_to_fibre`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Pi6.MSS
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

open E2cfk

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
variable (e₀ : E) (q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
variable (hconn : Work.PiS.SimplyConn B (p e₀))

section ResTransparencyOff

set_option backward.isDefEq.respectTransparency false

/-! ## The bottom of the column

The denominator `pDen 2 0 q` of `E_2^{0,q}` is `Z_1^1 + B_2^0`: the first summand is the group of
`1`-cochains vanishing on the chains over the vertices of `B` whose coboundary vanishes on the
chains over the `1`-skeleton, and the second is the image of the incoming differential. -/

/-- `B_2^0` is the range of the incoming differential. -/
theorem pB_eq_range :
    pB 𝕜 (serreCF 𝕜 E B p) 2 0 q = LinearMap.range (dPrevL 𝕜 E B p q) := by
  rw [pB, dPrevL_eq_dPrev]
  have h0 : (serreCF 𝕜 E B p).F 0 q = ⊤ := (serreCF 𝕜 E B p).F_zero q
  have h1 : (serreCF 𝕜 E B p).F (0 + 1 - 2) (q - 1) = ⊤ :=
    (serreCF 𝕜 E B p).F_zero (q - 1)
  rw [h0, h1, top_inf_eq, ← LinearMap.range_eq_map]

/-! ## The criterion -/

/-- **The linear-algebra criterion for `F^1 + B^q`.**  A cochain of `E` which vanishes on every
cycle of the subcomplex of `E` lying over the vertices of `B` lies in `F^1 C^q + im δ`. -/
theorem mem_sup_of_kills (x : Coh 𝕜 E q)
    (h : ∀ v : (Work.SSSR.sChains 𝕜 (sser p 1)).X q,
        (ECC 𝕜 E).d q (q - 1) ((sserInc 𝕜 p 1).f q v) = 0 →
        x ((sserInc 𝕜 p 1).f q v) = 0) :
    x ∈ compAnn 𝕜 (sser p 1) q ⊔ LinearMap.range (dPrevL 𝕜 E B p q) := by
  classical
  rcases q with _ | k
  · -- `q = 0`: the incoming differential is zero, so it suffices to show that `x` vanishes on
    -- the chains over the vertices
    refine Submodule.mem_sup_left ?_
    intro v
    exact h v (by
      have h2 : (ECC 𝕜 E).d 0 (0 - 1) = 0 := by
        refine HomologicalComplex.shape _ _ _ ?_
        simp
      rw [h2]
      simp)
  · -- `q = k + 1`
    set V : Submodule 𝕜 ((ECC 𝕜 E).X (k + 1)) :=
      LinearMap.range ((sserInc 𝕜 p 1).f (k + 1)).hom with hV
    set dV : ↥V →ₗ[𝕜] (ECC 𝕜 E).X k :=
      (((ECC 𝕜 E).d (k + 1) k).hom).comp V.subtype with hdV
    set xV : ↥V →ₗ[𝕜] 𝕜 := x.comp V.subtype with hxV
    -- `x` vanishes on the kernel of the boundary
    have hker : LinearMap.ker dV ≤ LinearMap.ker xV := by
      intro v hv
      have hv0 : ((ECC 𝕜 E).d (k + 1) k) (v : (ECC 𝕜 E).X (k + 1)) = 0 := hv
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp v.2
      have hz0 : (ECC 𝕜 E).d (k + 1) ((k + 1) - 1)
          ((sserInc 𝕜 p 1).f (k + 1) z) = 0 := by
        rw [hz]
        exact hv0
      have hx0 := h z (by simpa using hz0)
      show xV v = 0
      have : xV v = x ((sserInc 𝕜 p 1).f (k + 1) z) := by
        show x (v : (ECC 𝕜 E).X (k + 1)) = _
        rw [hz]
      rw [this, hx0]
    -- the factorisation of `xV` through the range of the boundary
    set ψ : ↥(LinearMap.range dV) →ₗ[𝕜] 𝕜 :=
      (Submodule.liftQ (LinearMap.ker dV) xV hker).comp
        ((LinearMap.quotKerEquivRange dV).symm.toLinearMap) with hψdef
    have hψ : ∀ v : ↥V, ψ ⟨dV v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩ = xV v := by
      intro v
      have hy : (LinearMap.quotKerEquivRange dV) (Submodule.Quotient.mk v)
          = ⟨dV v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩ := by
        refine Subtype.ext ?_
        rw [LinearMap.quotKerEquivRange_apply_mk]
      have h1 : (LinearMap.quotKerEquivRange dV).symm
          ⟨dV v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩ = Submodule.Quotient.mk v :=
        (LinearEquiv.symm_apply_eq (LinearMap.quotKerEquivRange dV)).mpr hy.symm
      have h1 : (LinearMap.quotKerEquivRange dV).symm
          ⟨dV v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩ = Submodule.Quotient.mk v :=
        (LinearEquiv.symm_apply_eq (LinearMap.quotKerEquivRange dV)).mpr hy.symm
      show (Submodule.liftQ (LinearMap.ker dV) xV hker)
        ((LinearMap.quotKerEquivRange dV).symm ⟨dV v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩)
        = xV v
      rw [h1]
      exact Submodule.liftQ_apply _ _ v
    obtain ⟨w, hw⟩ := LinearMap.exists_extend ψ
    -- `w` is a cochain in degree `k` whose coboundary corrects `x` into `F^1`
    refine Submodule.mem_sup.mpr ⟨x - dPrevL 𝕜 E B p (k + 1) w, ?_,
      dPrevL 𝕜 E B p (k + 1) w, ⟨w, rfl⟩, by abel⟩
    intro v
    have hzV : (sserInc 𝕜 p 1).f (k + 1) v ∈ V :=
      (LinearMap.mem_range (f := ((sserInc 𝕜 p 1).f (k + 1)).hom)).mpr ⟨v, rfl⟩
    have hzV' : dV ⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩ ∈ LinearMap.range dV := by
      apply LinearMap.mem_range.mpr
      exact ⟨⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩, rfl⟩
    have hwapply : w (dV ⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩)
        = xV ⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩ := by
      have hcongr := congrArg
        (fun (g : ↥(LinearMap.range dV) →ₗ[𝕜] 𝕜) =>
          g ⟨dV ⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩, hzV'⟩) hw
      simpa using hcongr.trans (hψ ⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩)
    have hxVv : xV ⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩ = x ((sserInc 𝕜 p 1).f (k + 1) v) := rfl
    have hd := dPrevL_apply_succ 𝕜 E B p k w ((sserInc 𝕜 p 1).f (k + 1) v)
    have hdV : dV ⟨(sserInc 𝕜 p 1).f (k + 1) v, hzV⟩
        = ((ECC 𝕜 E).d (k + 1) k) ((sserInc 𝕜 p 1).f (k + 1) v) := rfl
    rw [LinearMap.sub_apply, hd, ← hdV, hwapply, hxVv, sub_self]

/-- **The criterion for membership in `pDen 2 0 q`.**  It is enough to test a cochain with
`δx ∈ F^2 C^{q+1}` against the cycles of the subcomplex of `E` lying over the vertices of `B`. -/
theorem mem_pDen_of_kills_cycles (x : Coh 𝕜 E q)
    (hx : (serreCF 𝕜 E B p).d q x ∈ (serreCF 𝕜 E B p).F 2 (q + 1))
    (h : ∀ v : (Work.SSSR.sChains 𝕜 (sser p 1)).X q,
        (ECC 𝕜 E).d q (q - 1) ((sserInc 𝕜 p 1).f q v) = 0 →
        x ((sserInc 𝕜 p 1).f q v) = 0) :
    x ∈ pDen 𝕜 (serreCF 𝕜 E B p) 2 0 q := by
  have hmain := mem_sup_of_kills 𝕜 E B p q x h
  rw [← pB_eq_range 𝕜 E B p q] at hmain
  obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.mp hmain
  -- `z` also has its coboundary in `F^2`, since `δb = 0`
  have hd0 : (serreCF 𝕜 E B p).d q b = 0 := by
    rw [pB_eq_range 𝕜 E B p q] at hb
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hb
    show (serreCF 𝕜 E B p).d q (dPrevL 𝕜 E B p q w) = 0
    rw [dPrevL_eq_dPrev]
    show ((serreCF 𝕜 E B p).C.d q (q + 1)).hom
      (((serreCF 𝕜 E B p).C.d (q - 1) q).hom w) = 0
    have hcomp : (serreCF 𝕜 E B p).C.d (q - 1) q ≫ (serreCF 𝕜 E B p).C.d q (q + 1) = 0 := by
      rw [HomologicalComplex.d_comp_d]
    have h2 := congrArg (fun (φ : (serreCF 𝕜 E B p).C.X (q - 1) ⟶
        (serreCF 𝕜 E B p).C.X (q + 1)) => φ.hom w) hcomp
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.zero_apply,
      LinearMap.comp_apply] using h2
  have hxF : (serreCF 𝕜 E B p).d q z ∈ (serreCF 𝕜 E B p).F 2 (q + 1) := by
    have hsum : (serreCF 𝕜 E B p).d q x = (serreCF 𝕜 E B p).d q z + (serreCF 𝕜 E B p).d q b := by
      rw [← hzb]
      simp only [map_add]
    rw [hsum, hd0, add_zero] at hx
    exact hx
  have hb' : b ∈ LinearMap.range (dPrevL 𝕜 E B p q) := by
    rw [← pB_eq_range 𝕜 E B p q]
    exact hb
  refine Submodule.mem_sup.mpr ⟨z, ?_, b, ?_, hzb⟩
  · rw [show pZ 𝕜 (serreCF 𝕜 E B p) 1 1 q
        = (serreCF 𝕜 E B p).F 1 q ⊓ ((serreCF 𝕜 E B p).F 2 (q + 1)).comap
            ((serreCF 𝕜 E B p).d q) from rfl]
    rw [F_eq_compAnn 𝕜 E B p 1 q]
    exact Submodule.mem_inf.mpr ⟨hz, hxF⟩
  · rw [pB_eq_range 𝕜 E B p q]
    exact hb'



/-! ## Propagation from the fibre to all vertical cycles -/

/-- **The geometric input of the fibre edge, stated as a hypothesis.**  For every edge `σ` of the
base whose last vertex is the base point `p e₀`, a cycle of the fibre over the first vertex is
homologous, modulo the chains over the `1`-skeleton of `B`, to a cycle of the fibre over `p e₀`.
This is `Work.Pi6.MSS.transport_chain` (proved from the pullback, horn and fibre identifications). -/
def TransportHyp : Prop :=
  ∀ (σ : (SSet.stdSimplex.obj (SimplexCategory.mk 1) : SSet.{0}) ⟶ Work.SSS.sSing B)
    (z : (fibCC 𝕜 p (Work.SSS.sigmaVert σ)).X q),
      (fibCC 𝕜 p (Work.SSS.sigmaVert σ)).d q (q - 1) z = 0 →
    ∃ (w : (fibCC 𝕜 p (lastVert σ)).X q) (c : (ECC 𝕜 E).X (q + 1)),
      (fibCC 𝕜 p (lastVert σ)).d q (q - 1) w = 0 ∧
      (∃ c' : (((sser p 2).toSSet).chainComplex (ModuleCat.of 𝕜 𝕜)).X (q + 1),
        ((sserInc 𝕜 p 2).f (q + 1)).hom c' = c) ∧
      ((fIncl 𝕜 p (Work.SSS.sigmaVert σ)).f q).hom z
        - ((fIncl 𝕜 p (lastVert σ)).f q).hom w = ((ECC 𝕜 E).d (q + 1) q).hom c

/-- **The propagation of the vanishing from the fibre to all vertical cycles.** -/
theorem kills_vertical (hconn : Work.PiS.SimplyConn B (p e₀)) (x : Coh 𝕜 E q)
    (hx : (serreCF 𝕜 E B p).d q x ∈ (serreCF 𝕜 E B p).F 2 (q + 1))
    (hv : ∀ (γ : (fibCC 𝕜 p (p e₀)).X q), (fibCC 𝕜 p (p e₀)).d q (q - 1) γ = 0 →
        x (((fIncl 𝕜 p (p e₀)).f q).hom γ) = 0)
    (htr : TransportHyp 𝕜 E B p q) :
    ∀ v : (Work.SSSR.sChains 𝕜 (sser p 1)).X q,
      (ECC 𝕜 E).d q (q - 1) ((sserInc 𝕜 p 1).f q v) = 0 →
      x ((sserInc 𝕜 p 1).f q v) = 0 := by
  intro v hvcyc
  set γ : (ECC 𝕜 E).X q := (sserInc 𝕜 p 1).f q v with hγ
  have hγmem : γ ∈ LinearMap.range (ModuleCat.Hom.hom ((sserInc 𝕜 p 1).f q)) := by
    rw [hγ, LinearMap.range_eq_map]
    exact Submodule.mem_map.mpr ⟨v, Submodule.mem_top, rfl⟩
  obtain ⟨s, w, hwcyc, hwsupp, hdec⟩ := vertical_decomp 𝕜 p q γ hγmem hvcyc
  -- transport each summand of the decomposition
  have hstep : ∀ b ∈ s, ∃ (w' : (fibCC 𝕜 p (p e₀)).X q) (c : (ECC 𝕜 E).X (q + 1)),
      (fibCC 𝕜 p (p e₀)).d q (q - 1) w' = 0 ∧
      (∃ c' : (((sser p 2).toSSet).chainComplex (ModuleCat.of 𝕜 𝕜)).X (q + 1),
        ((sserInc 𝕜 p 2).f (q + 1)).hom c' = c) ∧
      ((fIncl 𝕜 p b).f q).hom (w b) - ((fIncl 𝕜 p (p e₀)).f q).hom w'
        = ((ECC 𝕜 E).d (q + 1) q).hom c := by
    intro b hb
    obtain ⟨σ, hσ, hσlast⟩ := exists_edge p e₀ hconn b
    cases hσ
    obtain ⟨w', c, hw'cyc, hcin, hrel⟩ := htr σ (w (Work.SSS.sigmaVert σ))
      (hwcyc (Work.SSS.sigmaVert σ))
    exact hσlast ▸ ⟨w', c, hw'cyc, hcin, hrel⟩
  -- each summand of the decomposition vanishes
  have hzero : ∀ b ∈ s, x (((fIncl 𝕜 p b).f q).hom (w b)) = 0 := by
    intro b hb
    obtain ⟨w', c, hw'cyc, hcin, hcrel⟩ := hstep b hb
    have h3 : x (((fIncl 𝕜 p b).f q).hom (w b)
        - ((fIncl 𝕜 p (p e₀)).f q).hom w') = 0 := by
      rw [hcrel]
      rw [← dPrevL_apply_succ 𝕜 E B p q x c]
      obtain ⟨c', hc'⟩ := hcin
      rw [← hc']
      have hmem : (dPrevL 𝕜 E B p (q + 1) x) ∈ compAnn 𝕜 (sser p 2) (q + 1) := by
        rw [← F_eq_compAnn 𝕜 E B p 2 (q + 1), dPrevL_eq_dPrev]
        exact hx
      exact hmem c'
    have hAB : x (((fIncl 𝕜 p b).f q).hom (w b))
        = x (((fIncl 𝕜 p (p e₀)).f q).hom w') := by
      have h4 := map_sub x (((fIncl 𝕜 p b).f q).hom (w b))
        (((fIncl 𝕜 p (p e₀)).f q).hom w')
      rw [h4] at h3
      exact sub_eq_zero.mp h3
    rw [hAB, hv w' hw'cyc]
  calc x ((sserInc 𝕜 p 1).f q v) = x γ := rfl
    _ = ∑ b ∈ s, x (((fIncl 𝕜 p b).f q).hom (w b)) := by
          rw [hdec]
          simp only [map_sum]
    _ = 0 := Finset.sum_eq_zero hzero

/-! ## The target statement -/

theorem e2Col_fibre_kernel (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (q : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (x : Work.Cohomology.Cochain 𝕜 (Work.SSS.sSing E) q)
    (hx : x ∈ Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q)
    (hv : ∀ (γ : ((Work.SSS.sSing (Work.StemsB.fibre p (p e₀))).chainComplex
        (ModuleCat.of 𝕜 𝕜)).X q),
        ((Work.SSS.sSing (Work.StemsB.fibre p (p e₀))).chainComplex (ModuleCat.of 𝕜 𝕜)).d
          q (q - 1) γ = 0 →
        x (((SSet.chainComplexMap (Work.SSS.sSingP (Work.StemsB.fibreIncl p (p e₀)))
          (ModuleCat.of 𝕜 𝕜)).f q).hom γ) = 0) :
    x ∈ Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 q := by
  have htr : TransportHyp 𝕜 E B p q := fun σ z hz => transport_chain 𝕜 p hfib q σ z hz
  have hkill := kills_vertical 𝕜 E B p e₀ q hconn x hx.2 hv htr
  exact mem_pDen_of_kills_cycles 𝕜 E B p q x hx.2 hkill


end ResTransparencyOff

end

end Work.Pi6.MSS
