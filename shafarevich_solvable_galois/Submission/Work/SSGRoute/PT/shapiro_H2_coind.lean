import Mathlib.GroupTheory.Index
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.shapiro_H2_inj
import Submission.Work.SSGRoute.PT.shapiro_H2_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma for `H²` of the coinduced module `Coind_U^G M`

For an *open* subgroup `U ≤ G` of *finite* index and a `U`-module `M` (with `U` acting
continuously for the discrete topology on `M`) we construct the degree-`2` Shapiro isomorphism

  `H²(G, Coind_U^G M) ≃+ H²(U, M)`,

where `Coind_U^G M = {f : G → M // ∀ g u, f (g*u) = u⁻¹ • f g}` with `(g • f) x = f (g⁻¹x)` and
`H²` is continuous (i.e. locally constant cochain) cohomology in degree `2`.

## The construction

* `coindEv : Coind_U^G M →+ M`, `f ↦ f 1`, is the `U`-equivariant evaluation map
  (`coindEv_smul`);
* `phiC : C²(G, Coind_U^G M) →+ C²(U,M)`, `c ↦ ((u,v) ↦ c(u,v)(1))`, the "restriction/evaluation"
  cochain map; it maps locally constant `2`-cocycles of `G` to locally constant `2`-cocycles of `U`
  (`phiC_mem_Z2`) and coboundaries to coboundaries (`phiC_mem_B2`), hence induces
  `phiH2 : H²(G, Coind_U^G M) →+ H²(U,M)`.

The two halves of the isomorphism are proved in the sibling files
`Submission.Work.SSGRoute.PT.shapiro_H2_lift` (every locally constant `2`-cocycle of `U` is the
restriction of one of `G`, via the standard Shapiro formula `a ↦ ((g,h) ↦ a(A(g,x), A(h,g⁻¹•x)))`
with `A(g,x) = s(x)⁻¹ g s(g⁻¹•x) ∈ U` the `U`-coordinate of `g` at the coset `x ∈ G ⧸ U`) and
`Submission.Work.SSGRoute.PT.shapiro_H2_inj` (a `2`-cocycle of `G` whose restriction is a
coboundary is itself a coboundary; the *kernel* half of Shapiro's lemma).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PT

open Classical

section Ev

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : Subgroup G) (M : Type*) [AddCommGroup M] [DistribMulAction U M]

/-- **Evaluation at `1`**: the additive map `Coind_U^G M → M`, `f ↦ f 1`. -/
noncomputable def coindEv : Coind G U M →+ M where
  toFun f := f 1
  map_zero' := rfl
  map_add' f g := rfl

@[simp] theorem coindEv_apply (f : Coind G U M) : coindEv U M f = f 1 := rfl

/-- `coindEv` is `U`-equivariant. -/
theorem coindEv_smul (u : U) (f : Coind G U M) :
    coindEv U M (u • f) = u • coindEv U M f := by
  show (u • f) 1 = u • f 1
  have h1 : (u • f) 1 = f ((u : G)⁻¹ * 1) := rfl
  rw [h1, mul_one]
  have hrel : f ((u : G)⁻¹ * (u : G)) = u⁻¹ • f ((u : G)⁻¹) := f.2 ((u : G)⁻¹) u
  rw [inv_mul_cancel] at hrel
  have h2 := congrArg (fun m => u • m) hrel
  simp only [smul_smul] at h2
  rw [mul_inv_cancel, one_smul] at h2
  exact h2.symm

/-- Evaluation at `1` of the `G`-action on a `U`-element. -/
theorem coindEv_smulG (u : U) (f : Coind G U M) :
    (((u : G) • f) 1) = u • (f 1) := by
  have h : coindEv U M (u • f) = u • coindEv U M f := coindEv_smul U M u f
  have h2 : coindEv U M (u • f) = (((u : G) • f) 1) := rfl
  have h3 : u • coindEv U M f = u • (f 1) := rfl
  rw [h2, h3] at h
  exact h

end Ev

section Phi

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : Subgroup G) (M : Type*) [AddCommGroup M] [DistribMulAction U M]

/-- The evaluation-at-`1` cochain map `C²(G, Coind_U^G M) →+ C²(U,M)`, `c ↦ ((u,v) ↦ c(u,v)(1))`. -/
noncomputable def phiC : (G × G → Coind G U M) →+ (U × U → M) where
  toFun c := fun p => c ((p.1 : G), (p.2 : G)) 1
  map_zero' := rfl
  map_add' c c' := rfl

@[simp] theorem phiC_apply (c : G × G → Coind G U M) (p : U × U) :
    phiC U M c p = c ((p.1 : G), (p.2 : G)) 1 := rfl

/-- `phiC` sends locally constant `2`-cocycles on `G` to locally constant `2`-cocycles on `U`. -/
theorem phiC_mem_Z2 (hUo : IsOpen (U : Set G)) {c : G × G → Coind G U M}
    (hc : c ∈ Work.AbsoluteKummer.Z2 G (Coind G U M)) :
    phiC U M c ∈ Work.AbsoluteKummer.Z2 U M := by
  obtain ⟨hcoc, hlc⟩ := (Work.AbsoluteKummer.mem_Z2_iff c).mp hc
  rw [Work.AbsoluteKummer.mem_Z2_iff]
  refine ⟨?_, ?_⟩
  · intro u v w
    have h := congrArg (fun f : Coind G U M => f 1) (hcoc (u : G) (v : G) (w : G))
    rw [show (((u : G) • c ((v : G), (w : G)) + c ((u : G), (v : G) * (w : G))) 1)
        = (((u : G) • c ((v : G), (w : G))) 1) + (c ((u : G), (v : G) * (w : G)) 1)
        from rfl] at h
    rw [show ((c ((u : G) * (v : G), (w : G)) + c ((u : G), (v : G))) 1)
        = (c ((u : G) * (v : G), (w : G)) 1) + (c ((u : G), (v : G)) 1)
        from rfl] at h
    rw [coindEv_smulG U M u (c ((v : G), (w : G)))] at h
    simpa [phiC_apply, Subgroup.coe_mul] using h
  · intro p
    obtain ⟨W, hW, hpW, hWc⟩ := hlc ((p.1 : G), (p.2 : G))
    refine ⟨{q : U × U | ((q.1 : G), (q.2 : G)) ∈ W}, ?_, hpW, ?_⟩
    · exact hW.preimage ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
    · intro q hq
      simp only [Set.mem_ofPred_eq] at hq
      show c ((q.1 : G), (q.2 : G)) 1 = c ((p.1 : G), (p.2 : G)) 1
      rw [hWc ((q.1 : G), (q.2 : G)) hq]

/-- `phiC` sends `2`-coboundaries on `G` to `2`-coboundaries on `U`. -/
theorem phiC_mem_B2 (hUo : IsOpen (U : Set G)) {c : G × G → Coind G U M}
    (hc : c ∈ Work.AbsoluteKummer.B2 G (Coind G U M)) :
    phiC U M c ∈ Work.AbsoluteKummer.B2 U M := by
  rw [Work.AbsoluteKummer.mem_B2_iff] at hc ⊢
  obtain ⟨B, hB, hBc⟩ := hc
  refine ⟨fun u => B (u : G) 1, ?_, ?_⟩
  · have hBlc : Work.AbsoluteKummer.IsLocallyConstant B :=
      (Work.AbsoluteKummer.mem_C1c_iff B).mp hB
    intro u
    obtain ⟨W, hW, huW, hWc⟩ :=
      (Work.AbsoluteKummer.isLocallyConstantAt_iff).mp (hBlc (u : G))
    refine ⟨{v : U | (v : G) ∈ W}, ?_, huW, ?_⟩
    · exact hW.preimage continuous_subtype_val
    · intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      have h := congrArg (fun f : Coind G U M => f 1) (hWc (v : G) hv)
      simpa using h
  · funext p
    obtain ⟨u, v⟩ := p
    rw [← hBc, phiC_apply]
    rw [Work.GroupCohomology.d1_apply, Work.GroupCohomology.d1_apply]
    rw [show (((u : G) • B (v : G) - B ((u : G) * (v : G)) + B (u : G)) 1)
        = (((u : G) • B (v : G)) 1) - (B ((u : G) * (v : G)) 1) + (B (u : G) 1)
        from rfl]
    rw [coindEv_smulG U M u (B (v : G))]
    simp [Subgroup.coe_mul]

/-- `phiC` on `2`-cocycles, as a map of the cocycle subgroups. -/
noncomputable def phiZ2 (hUo : IsOpen (U : Set G)) :
    Work.AbsoluteKummer.Z2 G (Coind G U M) →+ Work.AbsoluteKummer.Z2 U M :=
  AddMonoidHom.codRestrict
    ((phiC U M).comp (Work.AbsoluteKummer.Z2 G (Coind G U M)).subtype)
    (Work.AbsoluteKummer.Z2 U M) (fun x => phiC_mem_Z2 U M hUo x.2)

/-- The map induced on `H²` by `phiC`. -/
noncomputable def phiH2 (hUo : IsOpen (U : Set G)) :
    Work.AbsoluteKummer.H2 G (Coind G U M) →+ Work.AbsoluteKummer.H2 U M :=
  QuotientAddGroup.lift ((Work.AbsoluteKummer.B2 G (Coind G U M)).comap
      (Work.AbsoluteKummer.Z2 G (Coind G U M)).subtype)
    ((Work.AbsoluteKummer.H2π U M).comp (phiZ2 U M hUo)) (by
    intro x hx
    have hx' : ((x : Work.AbsoluteKummer.Z2 G (Coind G U M)) : G × G → Coind G U M)
        ∈ Work.AbsoluteKummer.B2 G (Coind G U M) := by
      simpa using (AddSubgroup.mem_comap.mp hx)
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.AbsoluteKummer.H2π_eq_zero_iff]
    exact phiC_mem_B2 U M hUo hx')

theorem phiH2_mk
    (hUo : IsOpen (U : Set G)) (c : Work.AbsoluteKummer.Z2 G (Coind G U M)) :
    phiH2 U M hUo (Work.AbsoluteKummer.H2π G (Coind G U M) c) =
      Work.AbsoluteKummer.H2π U M (phiZ2 U M hUo c) :=
  QuotientAddGroup.lift_mk' _ _ c

end Phi

theorem shapiro_H2_coind {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (hM : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Nonempty (Work.AbsoluteKummer.H2 G (Work.SSGRoute.PT.Coind G U M) ≃+
      Work.AbsoluteKummer.H2 U M) := by
  have hbij : Function.Bijective (phiH2 U M hU) := by
    constructor
    · -- injectivity of `Φ`, from the kernel half of Shapiro's lemma
      intro x y hxy
      have h0 : phiH2 U M hU (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
        ((Work.AbsoluteKummer.B2 G (Coind G U M)).comap
          (Work.AbsoluteKummer.Z2 G (Coind G U M)).subtype) (x - y)
      have hc0 : phiH2 U M hU (Work.AbsoluteKummer.H2π G (Coind G U M) c) = 0 :=
        (congrArg (fun z => phiH2 U M hU z) hc).trans h0
      have hker : (phiC U M ((c : Work.AbsoluteKummer.Z2 G (Coind G U M)) :
          G × G → Coind G U M)) ∈ Work.AbsoluteKummer.B2 U M := by
        rw [phiH2_mk] at hc0
        rw [Work.AbsoluteKummer.H2π_eq_zero_iff] at hc0
        exact hc0
      obtain ⟨b, hb, hbc⟩ := (Work.AbsoluteKummer.mem_B2_iff _).mp hker
      obtain ⟨B, hB, hBc⟩ := shapiro_H2_inj U hU
        ((c : Work.AbsoluteKummer.Z2 G (Coind G U M)) : G × G → Coind G U M) c.2
        ⟨b, hb, hbc⟩
      have hzero : Work.AbsoluteKummer.H2π G (Coind G U M) c = 0 :=
        (Work.AbsoluteKummer.H2π_eq_zero_iff c).mpr
          ((Work.AbsoluteKummer.mem_B2_iff c).mpr ⟨B, hB, hBc⟩)
      exact sub_eq_zero.mp (hc.symm.trans hzero)
    · -- surjectivity of `Φ`, from the Shapiro lift of cocycles
      intro y
      obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective
        ((Work.AbsoluteKummer.B2 U M).comap (Work.AbsoluteKummer.Z2 U M).subtype) y
      obtain ⟨c, hc, hcl⟩ := shapiro_H2_lift U hU
        ((a : Work.AbsoluteKummer.Z2 U M) : U × U → M) a.2
      refine ⟨Work.AbsoluteKummer.H2π G (Coind G U M) ⟨c, hc⟩, ?_⟩
      refine (phiH2_mk U M hU ⟨c, hc⟩).trans ?_
      rw [← ha]
      congr 1
      apply Subtype.ext
      funext p
      obtain ⟨u, v⟩ := p
      show phiC U M c (u, v) = (a : U × U → M) (u, v)
      rw [phiC_apply]
      exact hcl u v
  exact ⟨AddEquiv.ofBijective (phiH2 U M hU) hbij⟩

end Work.SSGRoute.PT
