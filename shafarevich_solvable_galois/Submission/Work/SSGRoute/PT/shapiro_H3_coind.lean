import Mathlib.GroupTheory.Index
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.shapiro_H2_coind
import Submission.Work.SSGRoute.PT.shapiro_H3_localconst
import Submission.Work.SSGRoute.PT.shapiro_H3_primitive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma in degree `3` for the coinduced module `Coind_U^G M`

For an open subgroup `U ≤ G` of finite index and a `U`-module `M`, the evaluation at the identity
of a locally constant `3`-cocycle of `G` with values in the coinduced module
`Coind_U^G M = {f : G → M // ∀ g u, f (g*u) = u⁻¹ • f g}`, restricted to `U`, induces an
isomorphism

  `H³(G, Coind_U^G M) ≅ H³(U, M)`

(this is the degree-`3` case of Shapiro's lemma, in the form needed by the dévissage of Milne's
class-formation proof; the degree `2` case is `shapiro_H2_coind`, with the kernel half
`shapiro_H2_inj`).

The two halves are:

* `shapiro_H3_lift` — every locally constant `3`-cocycle of `U` is the restriction of one of `G`
  (given by the Shapiro lift `shapiroLift3`);
* `shapiro_H3_inj` — a locally constant `3`-cocycle of `G` whose restriction to `U` is a
  coboundary is itself a coboundary (given by the primitive `h3Primitive`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (U : Subgroup G)

/-- **Evaluation at the identity** of a `3`-cochain of `G` with values in the coinduced module,
as a `3`-cochain of `U`: `c ↦ ((u,v,w) ↦ c (u,v,w) 1)`. -/
noncomputable def phiC3 (M : Type*) [AddCommGroup M] [DistribMulAction U M] :
    (G × G × G → Coind G U M) →+ (U × U × U → M) where
  toFun c := fun p => c ((p.1 : G), (p.2.1 : G), (p.2.2 : G)) 1
  map_zero' := rfl
  map_add' c c' := rfl

variable {U}

@[simp] theorem phiC3_apply {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (c : G × G × G → Coind G U M) (p : U × U × U) :
    phiC3 U M c p = c ((p.1 : G), (p.2.1 : G), (p.2.2 : G)) 1 := rfl

theorem phiC3_mem_Z3 (hUo : IsOpen (U : Set G)) {M : Type*} [AddCommGroup M]
    [DistribMulAction U M] {c : G × G × G → Coind G U M}
    (hc : c ∈ Work.SSGRoute.Z3 (M := Coind G U M) G) :
    phiC3 U M c ∈ Work.SSGRoute.Z3 (M := M) U := by
  obtain ⟨hcoc, hlc⟩ := (Work.SSGRoute.mem_Z3_iff (G := G) (M := Coind G U M)).mp hc
  rw [Work.SSGRoute.mem_Z3_iff]
  refine ⟨?_, ?_⟩
  · funext p
    obtain ⟨u, v, w, t⟩ := p
    have h := congrArg (fun f : Coind G U M => (f : G → M) 1)
      (congrFun hcoc ((u : G), (v : G), (w : G), (t : G)))
    simpa only [Work.SSGRoute.d3_apply, phiC3, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      AddSubgroup.coe_add, AddSubgroup.coe_sub, AddSubgroup.coe_zero, Pi.add_apply, Pi.sub_apply,
      Pi.zero_apply, coindEv_smulG, Subgroup.coe_mul] using h
  · intro p
    obtain ⟨W, hW, hpW, hWc⟩ := hlc ((p.1 : G), (p.2.1 : G), (p.2.2 : G))
    refine ⟨{q : U × U × U | ((q.1 : G), (q.2.1 : G), (q.2.2 : G)) ∈ W}, ?_, hpW, ?_⟩
    · exact hW.preimage ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_subtype_val.comp continuous_snd.fst).prodMk
          (continuous_subtype_val.comp continuous_snd.snd)))
    · intro q hq
      simp only [Set.mem_ofPred_eq] at hq
      rw [phiC3_apply, phiC3_apply]
      exact congrArg (fun f : Coind G U M => (f : G → M) 1)
        (hWc ((q.1 : G), (q.2.1 : G), (q.2.2 : G)) hq)

theorem phiC3_mem_B3 (hUo : IsOpen (U : Set G)) {M : Type*} [AddCommGroup M]
    [DistribMulAction U M] {c : G × G × G → Coind G U M}
    (hc : c ∈ Work.SSGRoute.B3 (M := Coind G U M) G) :
    phiC3 U M c ∈ Work.SSGRoute.B3 (M := M) U := by
  rw [Work.SSGRoute.mem_B3_iff] at hc ⊢
  obtain ⟨B, hB, hBc⟩ := hc
  refine ⟨fun p : U × U => (B ((p.1 : G), (p.2 : G)) : G → M) 1, ?_, ?_⟩
  · have hBlc : Work.AbsoluteKummer.IsLocallyConstant B :=
      (Work.AbsoluteKummer.mem_C2c_iff B).mp hB
    intro u
    obtain ⟨W, hW, huW, hWc⟩ := (Work.AbsoluteKummer.isLocallyConstantAt_iff).mp
      (hBlc (u.1, u.2.1))
    refine ⟨{v : U × U | ((v.1 : G), (v.2 : G)) ∈ W}, ?_, huW, ?_⟩
    · exact hW.preimage ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
    · intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      have h := congrArg (fun (f : Coind G U M) => (f : G → M) 1) (hWc ((v.1 : G), (v.2 : G)) hv)
      simpa using h
  · funext p
    obtain ⟨u, v, w⟩ := p
    rw [← hBc, phiC3_apply]
    rw [Work.GroupCohomology.d2_apply, Work.GroupCohomology.d2_apply]
    rw [show (((u : G) • B ((v : G), (w : G)) - B ((u : G) * (v : G), (w : G))
          + B ((u : G), (v : G) * (w : G)) - B ((u : G), (v : G))) 1)
        = (((u : G) • B ((v : G), (w : G))) 1) - (B ((u : G) * (v : G), (w : G)) 1)
          + (B ((u : G), (v : G) * (w : G)) 1) - (B ((u : G), (v : G)) 1)
        from rfl]
    rw [coindEv_smulG U M u (B ((v : G), (w : G)))]
    simp [Subgroup.coe_mul]

/-- The map on `3`-cocycles induced by `phiC3`. -/
noncomputable def phiZ3 (hUo : IsOpen (U : Set G)) {M : Type*} [AddCommGroup M]
    [DistribMulAction U M] :
    Work.SSGRoute.Z3 (M := Coind G U M) G →+ Work.SSGRoute.Z3 (M := M) U :=
  AddMonoidHom.codRestrict
    ((phiC3 U M).comp (Work.SSGRoute.Z3 (M := Coind G U M) G).subtype)
    (Work.SSGRoute.Z3 (M := M) U) (fun x => phiC3_mem_Z3 hUo x.2)

/-- The map induced on `H³` by `phiC3`. -/
noncomputable def phiH3 (hUo : IsOpen (U : Set G)) {M : Type*} [AddCommGroup M]
    [DistribMulAction U M] :
    Work.SSGRoute.H3 (M := Coind G U M) G →+ Work.SSGRoute.H3 (M := M) U :=
  QuotientAddGroup.lift
    ((Work.SSGRoute.B3 (M := Coind G U M) G).comap
      (Work.SSGRoute.Z3 (M := Coind G U M) G).subtype)
    ((Work.SSGRoute.H3π (M := M) U).comp (phiZ3 hUo)) (by
    intro x hx
    have hx' : ((x : Work.SSGRoute.Z3 (M := Coind G U M) G) : G × G × G → Coind G U M)
        ∈ Work.SSGRoute.B3 (M := Coind G U M) G := by
      simpa using (AddSubgroup.mem_comap.mp hx)
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
      Work.SSGRoute.H3π_eq_zero_iff (M := M) U]
    exact phiC3_mem_B3 hUo hx')

theorem phiH3_mk (hUo : IsOpen (U : Set G)) {M : Type*} [AddCommGroup M]
    [DistribMulAction U M] (c : Work.SSGRoute.Z3 (M := Coind G U M) G) :
    phiH3 hUo (Work.SSGRoute.H3π (M := Coind G U M) G c)
      = Work.SSGRoute.H3π (M := M) U (phiZ3 hUo c) :=
  QuotientAddGroup.lift_mk' _ _ c

/-- **Every locally constant `3`-cocycle of `U` extends to one of `G`** (the surjectivity half of
Shapiro's lemma in degree `3`): the extension is the Shapiro lift `shapiroLift3 U a`. -/
theorem shapiro_H3_lift (hU : IsOpen (U : Set G)) [U.FiniteIndex] {M : Type*}
    [AddCommGroup M] [DistribMulAction U M]
    (a : U × U × U → M) (ha : a ∈ Work.SSGRoute.Z3 (M := M) U) :
    ∃ c ∈ Work.SSGRoute.Z3 (M := Coind G U M) G,
      ∀ u v w : U, c ((u : G), (v : G), (w : G)) 1 = a (u, v, w) := by
  obtain ⟨hcoc, hlc⟩ := (Work.SSGRoute.mem_Z3_iff (G := U) (M := M)).mp ha
  refine ⟨shapiroLift3 U a, ?_, fun u v w => shapiroLift3_apply_one U a u v w⟩
  rw [Work.SSGRoute.mem_Z3_iff]
  refine ⟨?_, isLocallyConstant_shapiroLift3 U hU a hlc⟩
  funext p
  obtain ⟨g, h, k, l⟩ := p
  apply Subtype.ext
  funext x
  rw [shapiroLift3_d3 U a g h k l x]
  have hzero := congrFun hcoc (Shapiro.A 0 G U g (x : G ⧸ U),
    Shapiro.A 0 G U h (g⁻¹ • (x : G ⧸ U)), Shapiro.A 0 G U k ((g * h)⁻¹ • (x : G ⧸ U)),
    Shapiro.A 0 G U l ((g * h * k)⁻¹ • (x : G ⧸ U)))
  rw [hzero, Pi.zero_apply, smul_zero]
  simp

/-- **Shapiro's lemma in degree `3`, kernel half**: a locally constant `3`-cocycle of `G` with
values in `Coind U G M` whose restriction to `U` is the coboundary of a locally constant
`2`-cochain of `U` is itself a coboundary of a locally constant `2`-cochain of `G`. -/
theorem shapiro_H3_inj (hU : IsOpen (U : Set G)) [U.FiniteIndex] {M : Type*}
    [AddCommGroup M] [DistribMulAction U M]
    (c : G × G × G → Coind G U M) (hc : c ∈ Work.SSGRoute.Z3 (M := Coind G U M) G)
    (hb : ∃ b ∈ Work.AbsoluteKummer.C2c U M,
        Work.GroupCohomology.d2 U M b
          = fun p : U × U × U => (c ((p.1 : G), (p.2.1 : G), (p.2.2 : G)) : G → M) 1) :
    ∃ B ∈ Work.AbsoluteKummer.C2c G (Coind G U M),
      Work.GroupCohomology.d2 G (Coind G U M) B = c := by
  obtain ⟨b, hbC, hbeq⟩ := hb
  have hblc : Work.AbsoluteKummer.IsLocallyConstant b :=
    (Work.AbsoluteKummer.mem_C2c_iff b).mp hbC
  refine ⟨h3Primitive U b c, isLocallyConstant_h3Primitive U hU hblc hc, ?_⟩
  refine h3Primitive_d2 U hc ?_
  intro u v w
  have h := congrFun hbeq (u, v, w)
  simpa using h

/-- **Shapiro's lemma for `H³` of the coinduced module.**  For a topological group `G`, an open
subgroup `U ≤ G` of finite index and a discrete `U`-module `M`, the evaluation at the identity of
a `3`-cocycle of `G` with values in the coinduced module `Coind G U M`, restricted to `U`, is an
isomorphism on cohomology. -/
theorem shapiro_H3_coind {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    (hM : Work.AbsoluteKummer.IsDiscreteModule U M) :
    Nonempty (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.Coind G U M) G ≃+
      Work.SSGRoute.H3 (M := M) U) := by
  have hbij : Function.Bijective (phiH3 (M := M) hU) := by
    constructor
    · intro x y hxy
      have h0 : phiH3 (M := M) hU (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
        ((Work.SSGRoute.B3 (M := Coind G U M) G).comap
          (Work.SSGRoute.Z3 (M := Coind G U M) G).subtype) (x - y)
      have hc0 : phiH3 (M := M) hU (Work.SSGRoute.H3π (M := Coind G U M) G c) = 0 :=
        (congrArg (fun z => phiH3 (M := M) hU z) hc).trans h0
      have hker : (phiC3 U M ((c : Work.SSGRoute.Z3 (M := Coind G U M) G) :
          G × G × G → Coind G U M)) ∈ Work.SSGRoute.B3 (M := M) U := by
        rw [phiH3_mk] at hc0
        rw [Work.SSGRoute.H3π_eq_zero_iff] at hc0
        exact hc0
      obtain ⟨b, hb, hbc⟩ := (Work.SSGRoute.mem_B3_iff _).mp hker
      obtain ⟨B, hB, hBc⟩ := shapiro_H3_inj hU
        ((c : Work.SSGRoute.Z3 (M := Coind G U M) G) : G × G × G → Coind G U M) c.2
        ⟨b, hb, hbc⟩
      have hzero : Work.SSGRoute.H3π (M := Coind G U M) G c = 0 :=
        (Work.SSGRoute.H3π_eq_zero_iff (M := Coind G U M) G c).mpr
          ((Work.SSGRoute.mem_B3_iff _).mpr ⟨B, hB, hBc⟩)
      exact sub_eq_zero.mp (hc.symm.trans hzero)
    · intro y
      obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective
        ((Work.SSGRoute.B3 (M := M) U).comap (Work.SSGRoute.Z3 (M := M) U).subtype) y
      obtain ⟨c, hc, hcl⟩ := shapiro_H3_lift hU
        ((a : Work.SSGRoute.Z3 (M := M) U) : U × U × U → M) a.2
      refine ⟨Work.SSGRoute.H3π (M := Coind G U M) G ⟨c, hc⟩, ?_⟩
      refine (phiH3_mk hU ⟨c, hc⟩).trans ?_
      rw [← ha]
      congr 1
      apply Subtype.ext
      funext p
      obtain ⟨u, v, w⟩ := p
      show phiC3 U M c (u, v, w) = (a : U × U × U → M) (u, v, w)
      rw [phiC3_apply]
      exact hcl u v w
  exact ⟨AddEquiv.ofBijective (phiH3 (M := M) hU) hbij⟩

end

end Work.SSGRoute.PT
